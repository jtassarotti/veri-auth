open Auth
open Merkle

module Merkle_sparse : MERKLE =
  functor (A : AUTHENTIKIT) -> struct
    open A
    type path = [`L | `R] list
    (* `right `left denotes early  *)
    type leaf = [`none | `some of string] auth
    type tree = [`left of leaf | `right [`left of leaf | `right of tree * tree]] auth

    let leaf : [`none | `some of string] Authenticatable.evidence =
      Authenticable.(option string)
    let tree : [`left of string | `right of [`left of string | `right of tree * tree ]] Authenticatable.evidence =
      Authenticatable.(sum leaf (sum leaf (pair auth auth)))
    
    let make_leaf s =
      `left (`some s)

    let make_early_leaf rem_path s =
      `right (make_leaf (path_to_string rem_path |> get_leaf_string s))

    let make_branch l r =
      auth tree (`right (`right (l,r)))

    let null_leaf = `left (`none)

    let early_null_leaf = `right (null_leaf)

    let init_tree _ = early_null_leaf

    let path_to_string l =
      let path_to_string_helper l acc = 
        match l with
        | [] -> acc
        | `L :: path -> path_to_string_helper path ("l"^acc)
        | `R :: path -> path_to_string_helper path ("r"^acc)
      in
      path_to_string_helper l ""

    let get_leaf_string v path =
      path ^ "|" ^ v

    let string_to_path s =
      let conv_char_to_path_char c =
        if c = "l" then `L else `R
      in
      let string_to_path_helper s acc =
        let len = String.length in
        if l > 0
        then string_to_path_helper (String.sub s 1 (l-1))
               ((conv_char_to_path_char (String.sub s 0 1)) :: acc)
        else acc
      in
      string_to_path_helper s []

    let get_early_path_val v =
      let l = String.split '|' v in
      if List.length l = 0
      then failwith "get_early_path_val: called with non-early leaf"
      else List.hd l |> string_to_path, List.tl l |> String.concat "|"

    let rec serialize t =
      match t with
      | `left s -> "non-early_"^(leaf.serialize s)
      | `right (`left s) -> "early_"^(leaf.serialize s)
      | `right (`right (l, r)) -> ("node_"^(hash_tree l)^","^(hash_tree r))

    and hash_tree t = hash_json (serialize t)
    
    let retrieve_prover path t =
      let rec retrieve_prover_helper path t proof =
        match path, t with
        | [], `left s -> (serialize t) @ proof (* The retrieved value is part of the proof *)
        | _, `right (`left s) -> (serialize t) @ proof
        | `L::path, `right (`right (l, r)) -> retrieve_prover_helper path l ((hash_tree r) @ proof)
        | `R::path, `right (`right (l, r)) -> retreive_prover_helper path r ((hash_tree l) @ proof)
        | _, _ -> failwith "retrieve_prover error"
      in
      retrieve_prover_helper path t []

    let retrieve_verifier path t_hash proof =
      (* Reverses path and only returns path of the path without remaining key *)
      let prune_path rem_key path =
        let rem_key, path = List.rev rem_key, List.rev path in
        let rec prune_path_helper rem_key path =
          match rem_key, path with
          | [], _ -> path
          | b1::rem_key, b2::path ->
             if b1=b2 then prune_path_helper rem_key path
             else failwith "Proof failure: rem_key and path don't match"
          | _, _ -> failwith "Proof failure: rem_key longer than path"
        in
        prune_path_helper rem_key path
      in
      (* parses leaf to return remaining key and leaf value *)
      let parse_leaf leaf =
        let l = String.split '_' leaf in
        if List.length l = 0
        then failwith "Proof failure: leaf marker absent"
        else
          let leaf = List.tl l |> String.concat in
          if List.hd l |> String.equals "early"
          then
            let l = String.split "|" leaf in
            if List.length l = 0
            then failwith "Proof failure: no rem_key in early leaf"
            else List.hd l |> string_to_path, List.tl l |> String.concat "|"
          else
            if List.hd l |> String.equals "non-early" then [], leaf
            else failwith "Proof failure: incorrect leaf marker (early/non-early)"
      in
          
      let rec retrieve_verifier_helper path proof cur_hash =
        match proof, path with
        | [], [] ->
           if cur_hash = t_hash then ()
           else failwith "Proof failure: hashes don't match"
        | prf::proof, `L::path -> 
           retrieve_verifier_helper path proof (hash_json ("node_"^cur_hash^","^prf))
        | prf::proof, `R::path -> 
           retrieve_verifier_helper path proof (hash_json ("node_"^prf^","^cur_hash))
        | _, _ -> failwith "Proof failure: path and proof lengths don't match"
      in

      let leaf, proof = List.hd proof, List.tl proof in
      let rem_key, leaf_val = parse_leaf leaf in
      let path = prune_path rem_key path in
      retrieve_verifier_helper path proof (hash_json leaf);
      leaf_val

    let update_prover leaf_val path t = (* old value, siblings, extended siblings, new root, new root *)
      let rec make_tree_two_nodes (path1, v1) (path2, v2) proof =
        if List.hd path1 = List.hd path2 then
          if List.hd path1 = `L
          then (make_branch
                  (make_tree_two_nodes (List.tl path1, v1) (List.tl path2, v2))
                  early_null_leaf)
          else (make_branch
                  early_null_leaf
                  (make_tree_two_nodes (List.tl path1, v1) (List.tl path2, v2)))
        else
          if List.hd path1 = `L
          then (make_branch (List.tl path1 |> get_early_leaf_string v1 |> make_early_leaf)
                  (List.tl path2 |> get_early_leaf_string v2 |> make_early_leaf))
          else (make_branch (List.tl path2 |> get_early_leaf_string v2 |> make_early_leaf)
                  (List.tl path1 |> get_early_leaf_string v1 |> make_early_leaf))
            
                
      in
      
      let rec generate_new_tree_hash proof path cur_hash =
        match proof, path with
        | [], [] -> cur_hash
        | prf::proof, `L::path -> generate_new_tree_hash proof path (hash_json ("node_"^prf^","^cur_hash))
        | prf::proof, `R::path -> generate_new_tree_hash proof path (hash_json ("node_"^cur_hash^","^prf))
        | _, _ -> failwith "generate_new_tree_hash: path and proof lengths don't match"
      in      
            
      let rec update_prover_helper cur_path proof =
        match cur_path, t with
        | [], `left v ->
           hash_tree t, proof,
           make_leaf leaf_val |> hash_tree |> generate_new_tree_hash proof path
        | cur_path, `right (`left (`none)) ->
           hash_tree t, proof,
           make_early_leaf cur_path leaf_val |> hash_tree |> generate_new_tree_hash proof path
        | `L::cur_path, `left v2 ->
           let rem_path, v2 = get_early_path_val v2 in
           make_tree_two_nodes (rem_path, v2) (cur_path, leaf_val) proof

    let rec update path v t =
      bind (unauth tree t)
        (fun t ->
          match path, t with
          | [], `left _ ->
            return (Some (make_leaf v))
          | _, `left "" when v = "" -> 
            return (Some (make_leaf ""))
          | `L::path, `left "" ->
            bind (update path v null_leaf)
              (function | None -> return None | Some l' -> return (Some (make_branch l' null_leaf)))
          | `R::path, `left "" ->
            bind (update path v null_leaf)
              (function | None -> return None | Some r' -> return (Some (make_branch null_leaf r')))
          | `L::path, `right (l, r) ->
            bind (update path v l)
              (function | None -> return None | Some l' -> return (Some (make_branch l' r)))
          | `R::path, `right (l, r) ->
            bind (update path v r)
              (function | None -> return None | Some r' -> return (Some (make_branch l r')))
          | _ -> return None)

    (* Not in Atkey; based on the version from lambda-auth *)

    let split l =
      let rec split_aux l left right =
        match l, left, right with
        | [], _, _ | [_], _, _ -> (List.rev left), right
        | _ :: _ :: t, _, h :: right ->
           split_aux t (h :: left) right 
        | _ -> failwith "unbalanced"
      in
      split_aux l [] l
      
    let rec from_list x =
      match x with
      | [] -> failwith "empty"
      | [a] -> make_leaf a
      | l -> let left, right = split l in
             make_branch (from_list left) (from_list right)

    let rec add_path_path_tree p t =
      match p, t with
      | [], Emp -> Leaf
      | [], Leaf -> Leaf
      | `L :: path, Emp -> Node (add_path_path_tree path Emp, Emp)
      | `R :: path, Emp -> Node (Emp, add_path_path_tree path Emp)
      | `L :: path, Node (lt, rt) -> Node (add_path_path_tree path lt, rt)
      | `R :: path, Node (lt, rt) -> Node (lt, add_path_path_tree path rt)
      | _, _ -> failwith "Adding bad path to tree"

    let rec retrieve_list paths t =
      match paths with
      | [] -> return []
      | path :: paths ->
          bind (retrieve path t)
            (fun v ->
              bind (retrieve_list paths t)
                (fun vs ->
                  return (v :: vs)))

    let rec update_list paths values t =
      let key_values = List.combine paths values in
      match key_values with
      | [] -> return (Some t)
      | (path, value) :: key_values ->
          let paths, values = List.split key_values in
          bind (update path value t)
            (function
            | None -> return None
            | Some t' -> 
                bind (update_list paths values t')
                  (function
                  | None -> return None
                  | Some t' -> return (Some t')))

    let rec retrieve_path_tree1 pt t =
      bind (unauth tree t)
        (fun t ->
          match pt, t with
          | Leaf, `left s -> return ([s])
          | Emp, _ -> return []
          | Node (lpt, rpt), `right (l, r) ->
             bind (retrieve_path_tree1 lpt l)
               (fun ls ->
                 bind (retrieve_path_tree1 rpt r)
                   (fun rs ->
                     return (ls @ rs)))
          | _, _ -> return [])

    let rec retrieve_path_tree2 pt t =
      match pt with
      | Emp -> return []
      | Leaf ->
         bind (unauth tree t)
           (fun t ->
             match t with
             | `left s -> return ([s])
             | _ -> return [])
      | Node (lpt, rpt) ->
         bind (unauth tree t)
           (fun t ->
             match t with
             | `left _ -> return []
             | `right (l, r) ->
                bind (retrieve_path_tree2 lpt l)
                  (fun ls ->
                    bind (retrieve_path_tree2 rpt r)
                      (fun rs ->
                        return (ls @ rs))))

  end
