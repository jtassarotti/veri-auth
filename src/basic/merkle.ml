(** Merkle tree functor, incl. hand-optimized merkle retrieve operations. *)
open Auth
open Utils

module Path = struct
  type path_member = Lp | Rp
  type path = path_member list
  let path_empty = []
  let path_left path = Lp :: path
  let path_right path = Rp :: path
  let path_pop path =
    match path with
    | [] -> None
    | h::t -> Some (h, t)
end

module type MERKLE_RETRIEVE =
  functor (K: AUTHENTIKIT) -> sig
    open K
    open Path

    type tree_auth

    val retrieve_magic : 
      path -> tree_auth -> string option authenticated_computation
  end 

module Merkle_retrieve_ideal : MERKLE_RETRIEVE =
  functor (K: AUTHENTIKIT) -> struct
    open K
    open Path

    type tree = [`left of string | `right of tree auth * tree auth]
    type tree_auth = tree auth
    let tree = Authenticatable.(sum string (pair auth auth))

    let rec retrieve_magic_ideal path t =
      let t = Obj.magic (t) in
      let popped_path_opt = path_pop path in
      match t with
      | `left s ->
        begin match popped_path_opt with
        | None -> Some s
        | Some _ -> None
        end
      | `right children ->
        match popped_path_opt with
        | None -> None
        | Some popped_path ->
          let path_head, path_tail = popped_path in
          match path_head with
          | Lp -> retrieve_magic_ideal path (fst children)
          | Rp -> retrieve_magic_ideal path (snd children)

    let retrieve_magic =
      Obj.magic (fun path t _ ->
        retrieve_magic_ideal path t
      )
  end
  
module Merkle_retrieve_prover : MERKLE_RETRIEVE =
  functor (K: AUTHENTIKIT) -> struct
    open K
    open Path
    open Authenticatable_base.Prover

    type tree = [`left of string | `right of tree auth * tree auth]
    type tree_auth = tree auth
    let tree = sum string (pair string string)

    type list_elem = [`left of string | `right of [`left of string | `right of string * string]]
    type list_first = [`left of list_elem | `right of list_elem * string]
    let list_elem: list_elem evidence = sum string (sum string (pair string string))
    let list_first: list_first evidence = sum list_elem (pair list_elem string)
    
    let make_retrieve_proof ser s proof =
      match proof with
        None -> ser (`left s)
      | Some proof -> ser (`right (s, proof))

    let rec retrieve_magic_prover_aux path t_auth r_proof =
      let popped_path_opt = path_pop path in
      let t, t_hash = t_auth in
      match t with
      | `left leaf -> 
        begin match popped_path_opt with
          None -> make_retrieve_proof list_first (`left leaf) r_proof, Some leaf
        | Some _ -> make_retrieve_proof list_first (`right (`left leaf)) r_proof, None
        end
      | `right children ->
        let left_auth, right_auth = children in
        let _, left_hash = left_auth in
        let _, right_hash = right_auth in
        match popped_path_opt with
          None ->
            make_retrieve_proof list_first (`right (`right (left_hash, right_hash))) r_proof, None
        | Some popped_path ->
          let path_head, path_tail = popped_path in
          match path_head with
            Lp -> retrieve_magic_prover_aux path_tail left_auth 
              (Some (make_retrieve_proof tree right_hash r_proof))
          | Rp -> retrieve_magic_prover_aux path_tail right_auth
              (Some (make_retrieve_proof tree left_hash r_proof))

    let retrieve_magic =
      Obj.magic (fun path t proof ->
        let retrieve_proof, retrieve_result = retrieve_magic_prover_aux path t None in
        (push_proof (Obj.magic retrieve_proof) proof, retrieve_result))
  end

module Merkle_retrieve_verifier : MERKLE_RETRIEVE =
  functor (K: AUTHENTIKIT) -> struct
    open K
    open Path
    open Authenticatable_base.Verifier
    open Hash

    type tree = [`left of string | `right of tree auth * tree auth]
    type tree_auth = tree auth
    let tree = sum string (pair string string)
    
    type list_elem = [`left of string | `right of [`left of string | `right of string * string]]
    type list_first = [`left of list_elem | `right of list_elem * string]
    let list_elem: list_elem evidence = sum string (sum string (pair string string))
    let list_first: list_first evidence = sum list_elem (pair list_elem string)
    
    let parse_retreive_proof ser retrieve_proof_ser =
      match ser.deserialize retrieve_proof_ser with
      | None -> None
      | Some v ->
        match v with
        | `left tip -> Some (tip, None)
        | `right list ->
          let v1, v2 = list in
          Some (v1, Some v2)

    let hash_retrieve_proof v = hash (tree.serialize v)

    let rec retrieve_magic_verifier_aux path retrieve_proof cur_hash =
      let popped_path_opt = path_pop path in
      match list_head retrieve_proof with
        None ->
          begin match popped_path_opt with
            None -> Some cur_hash
          | Some _ -> None
          end
      | Some proof_head ->
        let proof_tail = list_tail retrieve_proof in
        match popped_path_opt with
          None -> None
        | Some popped_path ->
          let path_head, path_tail = popped_path in
          let node_hash = retrieve_magic_verifier_aux path_tail proof_tail cur_hash in
          match node_hash with
            None -> None
          | Some node_hash ->
            match path_head with
              Lp -> Some (hash_retrieve_proof (`right (node_hash, proof_head)))
            | Rp -> Some (hash_retrieve_proof (`right (proof_head, node_hash)))

    let rec deserialize_list_proof proof acc =
      match proof with
      | None -> Some acc
      | Some proof -> 
        match parse_retreive_proof tree proof with
          None -> None
        | Some parsed_retrieve_proof ->
          let proof_head, proof_tail = parsed_retrieve_proof in
          deserialize_list_proof proof_tail (proof_head :: acc)

    let retrieve_magic =
      Obj.magic (fun path t_hash proof ->
        match pop_proof proof with
          None -> None
        | Some (retrieve_proof_ser, proof_tail) ->
          match parse_retreive_proof list_first (Obj.magic retrieve_proof_ser) with
            None -> None
          | Some r_proof ->
            let first_element, retrieve_proof = r_proof in
            let proof_list = deserialize_list_proof retrieve_proof [] in
            match proof_list with
              None -> None
            | Some proof_list ->
              let result, start_hash, path, imm_return =
                match first_element with
                | `left tip -> 
                    Some tip, hash_retrieve_proof (`left tip), path, false
                | `right v ->
                  match v with
                    `left last_leaf -> 
                    let trunc_path = list_sub (list_length proof_list) path in
                    (None, hash_retrieve_proof (`left last_leaf), trunc_path,
                      list_length path <= list_length trunc_path)
                  | `right last_val ->
                    None, hash_retrieve_proof (`right last_val), path, false
              in
              if imm_return then None else
              match retrieve_magic_verifier_aux path proof_list start_hash with
              | None -> None
              | Some node_hash ->
                if node_hash = t_hash 
                then Some (proof_tail, result)
                else None ) 
  end

module type MERKLE =
  functor (K : AUTHENTIKIT) -> functor (R: MERKLE_RETRIEVE)-> sig
    open K
    open Path

    type tree = [`left of string | `right of tree auth * tree auth ]
    type tree_auth = tree auth

    val make_leaf : string -> tree_auth
    val make_branch : tree_auth -> tree_auth -> tree_auth
    val init_tree : int -> tree_auth
    val retrieve :
      path -> tree_auth -> string option authenticated_computation
    val retrieve_magic :
      path -> tree_auth -> string option authenticated_computation
    val update :
      path -> string -> tree_auth -> tree_auth option authenticated_computation
    val from_list : string list -> tree_auth
    val retrieve_list : path list -> tree_auth -> (string option list) authenticated_computation 
    val retrieve_list_magic : path list -> tree_auth -> (string option list) authenticated_computation
    val compare : tree_auth -> tree_auth -> bool authenticated_computation
    val contains : string -> tree_auth -> bool authenticated_computation
    val update_list : path list -> string list -> tree_auth -> tree_auth option authenticated_computation 
  end


module Merkle : MERKLE =
  functor (K : AUTHENTIKIT) -> functor (R: MERKLE_RETRIEVE) -> struct
    open K
    module Temp = R (K)
    open Temp
    open Path

    type tree = [`left of string | `right of tree auth * tree auth ]
    type tree_auth = tree auth
    let tree : tree Authenticatable.evidence = 
      Authenticatable.(sum string (pair auth auth))

    let make_leaf s =
      auth tree (`left s)

    let make_branch l r =
      auth tree (`right (l, r))

    let null_leaf = make_leaf ""

    let rec init_tree depth =
      if depth = 0 then null_leaf
      else make_branch (init_tree (depth-1)) (init_tree (depth-1))

    let rec retrieve path t =
      bind (unauth tree t)
        (fun t ->
          match path, t with
          | [], `left s -> return (Some s)
          | Lp::path, `right (l, r) -> retrieve path l
          | Rp::path, `right (l, r) -> retrieve path r
          | _, _ -> return None)

    let rec update path v t =
      bind (unauth tree t)
        (fun t ->
          match path, t with
          | [], `left _ ->
             return (Some (make_leaf v))
          | Lp::path, `right (l, r) ->
             bind (update path v l)
               (function | None -> return None | Some l' -> return (Some (make_branch l' r)))
          | Rp::path, `right (l, r) ->
             bind (update path v r)
               (function | None -> return None | Some r' -> return (Some (make_branch l r')))
          | _ -> return None)

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

    let retrieve_magic path t = (Obj.magic : _ -> _ -> _) retrieve_magic path t

    (* Retrieve a list of paths just by repeatedly calling retrieve *)
    let rec retrieve_list paths t =
      match paths with
      | [] -> return []
      | p :: paths ->
         bind (retrieve p t)
           (fun v ->
             bind (retrieve_list paths t)
               (fun vs ->
                return (v :: vs)))
    
    let rec retrieve_list_magic paths t =
      match paths with
      | [] -> return []
      | p :: paths ->
         bind (retrieve_magic p t)
           (fun v ->
             bind (retrieve_list_magic paths t)
               (fun vs ->
                return (v :: vs)))

    let rec compare t1 t2 =
      bind (unauth tree t1)
        (fun t1 ->
          bind (unauth tree t2)
            (fun t2 ->
              match t1, t2 with
              | `left s1, `left s2 -> return (s1 = s2)
              | `right (l1, r1), `right (l2, r2) ->
                bind (compare l1 l2)
                  (fun b1 -> 
                    if b1
                      then compare r1 r2
                      else return b1
                    )
              | _ -> return false
              )
          )

    let rec contains s t =
      bind (unauth tree t) (
        function
          `left s' -> return (s = s')
        | `right (l, r) ->
          bind (contains s l) (
            function
              true -> return true
            | false -> contains s r
          )
        )

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
  end
