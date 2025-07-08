open Auth
open Utils

module type HISTORY =
  functor (K : AUTHENTIKIT2) -> sig
    open K
    (* open Path *)
  
    
    (* minimum and maximum possible indices. 
      Required for retrieval at the moment. When retrieval is made 
      using lexographic orders, can avoid indices. *)
    type leaf = [`left of string]
    (* String is always null *)
    type empty_tree = [`left of string]
    type tree_node = [leaf | `right of [empty_tree | `right of bool * (int * int) * tree_node auth * tree_node auth]]
    type tree = [empty_tree | `right of bool * (int * int) * tree_node auth * tree_node auth]
    type tree_auth = tree auth
    type tree_node_auth = tree_node auth

    val init_tree : unit -> tree_auth
    val retrieve :
      int -> tree_auth -> string option authenticated_computation
    val append :
      string -> tree_auth -> (tree_auth * int) authenticated_computation
    val is_extension : (* is t1 an extension of t2? *)
      tree_auth -> tree_auth -> bool authenticated_computation
    val is_extension_naive : (* is t1 an extension of t2? *)
      tree_auth -> tree_auth -> bool authenticated_computation
    val inorder :
      tree_auth -> string authenticated_computation

    (* val update :
      path -> string -> tree_auth -> tree_auth option authenticated_computation *)
    (* val from_list : string list -> tree_auth
    val retrieve_list : path list -> tree_auth -> (string option list) authenticated_computation 
    val compare : tree_auth -> tree_auth -> bool authenticated_computation
    val contains : string -> tree_auth -> bool authenticated_computation
    val update_list : path list -> string list -> tree_auth -> tree_auth option authenticated_computation  *)
  end


module History : HISTORY =
  functor (K : AUTHENTIKIT2) -> struct
    open K

    type leaf = [`left of string]
    (* String is always null *)
    type empty_tree = [`left of string]
    type tree_node = [leaf | `right of [empty_tree | `right of bool * (int * int) * tree_node auth * tree_node auth]]
    type tree = [empty_tree | `right of bool * (int * int) * tree_node auth * tree_node auth]
    type tree_auth = tree auth
    type tree_node_auth = tree_node auth

    let tree_evi : tree Authenticatable.evidence = 
      Authenticatable.(sum string (quad bool (pair int int) auth auth))
    let tree_node_evi : tree_node Authenticatable.evidence =
      Authenticatable.(sum string tree_evi)

    let empty_tree = `left ""
    let empty_tree_auth = auth tree_evi (`left "")

    let empty_tree_node = `right empty_tree
    let empty_tree_node_auth = auth tree_node_evi empty_tree_node

    let init_tree () = empty_tree_auth

    let make_tree b i1 i2 l r = `right (b, (i1, i2), l, r)
    let make_leaf s = `left s
    let make_node b i1 i2 l r = `right (`right (b, (i1, i2), l, r))

    let auth_node n = auth tree_node_evi n
    let auth_tree n = auth tree_evi n

    let rec retrieve i t =
      let rec retrieve_aux t =
        match t with
        | `left s -> Some s |> return
        | `right (`left _) -> return None
        | `right (`right (_, (i1, i2), l, r)) -> 
          let num_nodes = exp 2 i2 in
          if i < i1 || i >= i1 + num_nodes then return None
          else if i < i1 + (num_nodes/2) then
            let* l = unauth tree_node_evi l in
            retrieve_aux l
          else
            let* r = unauth tree_node_evi r in
            retrieve_aux r
      in
      let* t = unauth tree_evi t in
      match t with
      | `left _ -> return None
      | `right _ -> retrieve_aux (`right t)


    let append v t =
      let leaf = make_leaf v in
      let rec app n i1 i2 =
        match n with
        | `left s -> failwith "append at a leaf"
        | `right (`left _) -> 
          if i2 = 0 then return (leaf, i1)
          else
            let* (l, i) = app empty_tree_node i1 (i2-1) in
            return (make_node false i1 i2 (auth_node l) empty_tree_node_auth, i)
        | `right (`right (b, (i1, i2), l, r)) ->
          let num_nodes = exp 2 i2 in
          if b then failwith "Node full" else
            let* lu = unauth tree_node_evi l in
            match lu with
            | `left _
            | `right (`right (true, _, _, _)) ->
              let* ru = unauth tree_node_evi r in
              let* (r, i) = app ru (i1 + (num_nodes/2)) (i2-1) in
              return (make_node (i+1 = i1+num_nodes) i1 i2 l (auth_node r), i)
            | _ ->
              let* (l, i) = app lu i1 (i2-1) in
              return (make_node false i1 i2 (auth_node l) r, i)
      in
      let* un_t = unauth tree_evi t in
      match un_t with
      | `left _ -> 
        return (auth_tree (make_tree false 0 1 (auth_node leaf) empty_tree_node_auth), 0)
      | `right (b, (0, i2), l, r) ->
        if b then
          let num_nodes = exp 2 i2 in
          let* (r, i) = app empty_tree_node num_nodes i2 in
          let tree = make_tree (i+1 = (num_nodes*2)) 0 (i2+1) (auth_node (`right un_t)) (auth_node r) in
          return (auth_tree tree, i)
        else 
          let* (tn, i) = app (`right un_t) 0 i2 in
          begin match tn with
          | `right t -> return (auth_tree t, i)
          | _ -> failwith "app returned a leaf or failed"
          end
      | _ -> failwith "invalid root node"


    let is_extension t1 t2 =
      let rec get_matching_n1 n i =
        match n with
        | `left _ | `right (`left _) -> failwith "get_matching_t1: given invalid node"
        | `right (`right (_, (_, i2), l, _)) ->
          if i = i2 then return n
          else
            let* l = unauth tree_node_evi l in get_matching_n1 l i
      in

      let rec is_extension_aux n1 n2 =
        match n1, n2 with
        | _, `right (`left _) -> return true
        | `left s1, `left s2 when s1 = s2 -> return true
        | `right (`right (_, _, l1, r1)), `right (`right (_, _, l2, r2)) ->
          let* b = eqauth tree_node_evi l1 l2 in
          if b then
            let* b = eqauth tree_node_evi r1 r2 in
            if b then return b
            else
              let* r1 = unauth tree_node_evi r1 in
              let* r2 = unauth tree_node_evi r2 in
              is_extension_aux r1 r2
          else
            let* b = eqauth tree_node_evi r2 empty_tree_node_auth in
            if b then 
              let* l1 = unauth tree_node_evi l1 in
              let* l2 = unauth tree_node_evi l2 in
              is_extension_aux l1 l2
            else return false
        | _ -> return false
      in
      
      let* b = eqauth tree_evi t1 t2 in
      if b then return b
      else
        let* b = eqauth tree_evi t2 empty_tree_auth in
        if b then return true
        else
          let* t1 = unauth tree_evi t1 in
          let* t2 = unauth tree_evi t2 in
          match t1, t2 with
          | `left _, _ -> return false
          | _, `left _ -> return true
          | `right (_, _, l1, r1), `right (_, (_, i22), l2, r2) ->
            let n1 = `right t1 in
            let n2 = `right t2 in
            let* n1 = get_matching_n1 n1 i22 in
            is_extension_aux n1 n2


    let is_extension_naive t1 t2 =
      let rec get_matching_n1 n i =
        match n with
        | `left _ | `right (`left _) -> failwith "get_matching_t1: given invalid node"
        | `right (`right (_, (_, i2), l, _)) ->
          if i = i2 then return n
          else
            let* l = unauth tree_node_evi l in get_matching_n1 l i
      in

      let rec is_extension_aux n1 n2 =
        match n1, n2 with
        | _, `right (`left _) -> return true
        | `right (`left _), _ -> return false
        | `left s1, `left s2 when s1 = s2 -> return true
        | `left _, _ -> return false
        | `right (`right (_, _, l1, r1)), `right(`right (_, (_, i22), l2, r2)) ->
          begin match n1 with
          | `right (`right (_, _, l1, r1)) -> 
            let* l1 = unauth tree_node_evi l1 in
            let* l2 = unauth tree_node_evi l2 in
            let* b = is_extension_aux l1 l2 in
            if b then 
              let* r1 = unauth tree_node_evi r1 in
              let* r2 = unauth tree_node_evi r2 in
              is_extension_aux r1 r2
            else return false
          | _ -> failwith "non-node t1"
          end
        | _ -> return false
      in
      
      if t2 = empty_tree_auth then return true
      else
        let* t1 = unauth tree_evi t1 in
        let* t2 = unauth tree_evi t2 in
        match t1, t2 with
        | `left _, _ -> return false
        | _, `left _ -> return true
        | `right (_, _, l1, r1), `right (_, (_, i22), l2, r2) ->
          let n1 = `right t1 in
          let n2 = `right t2 in
          let* n1 = get_matching_n1 n1 i22 in
          is_extension_aux n1 n2

    let inorder tree =
      let rec inorder_node tree_node =
        let* t = unauth tree_node_evi tree_node in
        match t with
        | `left s -> return s
        | `right (`left _) -> return ""
        | `right (`right (_, _, l, r)) ->
          let* sl = inorder_node l in
          let* sr = inorder_node r in
          return (sl^" "^sr)
      in

      let* t = unauth tree_evi tree in
      match t with
      | `left _ -> return "Empty tree"
      | `right (_, _, l, r) ->
        let* sl = inorder_node l in
        let* sr = inorder_node r in
        return (sl^" "^sr)

  end
