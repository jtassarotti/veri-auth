open Auth
open Merkle

module Merkle_sparse : MERKLE =
  functor (A : AUTHENTIKIT) -> struct
    open A
    type path = [`L | `R] list
    type tree = [`left of string | `right of tree * tree ] auth

    let tree : [`left of string |`right of tree * tree] Authenticatable.evidence =
      Authenticatable.(sum string (pair auth auth))

    let make_leaf s =
      auth tree (`left s)

    let make_branch l r =
      auth tree (`right (l,r))

    let null_leaf = make_leaf ""

    let init_tree _ = null_leaf

    let rec retrieve path t =
      bind (unauth tree t)
        (fun t ->
          match path, t with
          | [], `left s -> return (Some s)
          | _, `left "" -> return (Some "")
          | `L::path, `right (l, r) -> retrieve path l
          | `R::path, `right (l, r) -> retrieve path r
          | _, _ -> return None)

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

(* module Merkle_sparse : MERKLE =
  functor (A : AUTHENTIKIT) -> struct
    open A
    type path = [`L | `R] list
    type tree = [`left of string | `right of tree * tree ] auth

    let tree : [`left of string |`right of tree * tree] Authenticatable.evidence =
      Authenticatable.(sum string (pair auth auth))

    let null_leaf = auth1 Authenticatable.string ""

    let path_to_string l =
      let path_to_string_helper l acc = 
        match l with
        | [] -> acc
        | `L :: path -> path_to_string_helper path ("l"^acc)
        | `R :: path -> path_to_string_helper path ("r"^acc)
      in
      path_to_string_helper l ""

    let get_leaf_string v path =
      path ^ "_" ^ v

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

    let get_path_val v =
      let l = String.split '_' v in
      if List.length l = 0 
        then ([], "")
        else List.hd l |> string_to_path, List.tl l |> String.concat "_"

    let make_leaf s =
      auth1 tree (`left s)

    let make_branch l r =
      auth tree (`right (l,r))

    let rec retrieve path t =
      bind (unauth tree t)
        (fun t ->
          match path, t with
          | [], `left v -> let rem_path, s = get_path_val v in return (Some s)
          | `L::path, `right (l, r) -> retrieve path l
          | `R::path, `right (l, r) -> retrieve path r
          | _, _ -> return None)

    let rec make_tree_two_nodes (path1, v1) (path2, v2) =
      if List.hd path1 = List.hd path2
      then 
        if List.hd path1 = `L
          then (make_branch 
                  (make_tree_two_nodes (List.tl path1, v1) (List.tl path2, v2)) null_leaf)
          else (make_branch 
                  (make_tree_two_nodes null_leaf (List.tl path1, v1) (List.tl path2, v2)))
      else
        if List.hd path1 = `L
          then (make_branch (List.tl path1 |> get_leaf_string v1 |> make_leaf) 
                            (List.tl path2 |> get_leaf_string v2 |> make_leaf))
          else (make_branch (List.tl path2 |> get_leaf_string v2 |> make_leaf) 
                            (List.tl path1 |> get_leaf_string v1 |> make_leaf))

    let rec update path v t =
      bind (unauth tree t)
        (fun t ->
          match path, t with
          | [], `left _ ->
              return (Some (make_leaf v))
          | path, `left "" ->
              return (Some (path_to_string path |> get_leaf_string v |> make_leaf))
          | `L::path, `left v2 ->
              let rem_path, v2 = get_path_val v in
              (Some (make_branch (make_tree_two_nodes (rem_path, v2) (path, v)) null_leaf))
          | `R::path, `left v2 ->
              let rem_path, v2 = get_path_val v in
              (Some (make_branch null_leaf (make_tree_two_nodes (rem_path, v2) (path, v))))
          | `L::path, `right (l, r) ->
              bind (update path v l)
                (function | None -> return None | Some l' -> return (Some (make_branch l' r)))
          | `R::path, `right (l, r) ->
              bind (update path v r)
                (function | None -> return None | Some r' -> return (Some (make_branch l r')))
          | _ -> return None)

    (* Not in Atkey; based on the version from lambda-auth *)
      
    let rec from_list x =
      match x with
      | [] -> failwith "empty"
      | [a] -> make_leaf a
      | l -> 
  end *)
