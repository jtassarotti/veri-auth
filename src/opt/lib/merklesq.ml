open Auth

module type MERKLESQ =
  functor (K : AUTHENTIKIT2) -> sig
    open K
  
    type key = string
    type priv_key = random
    type value = string
    type data = priv_key * value
    type pos = int
    type pos_range = pos * pos

    type pr_tree = [`left of data evi_option | `right of pr_tree auth * pr_tree auth ]
    type pr_auth = pr_tree auth

    type cr_tree = [`left of pos_range * data | `right of pos_range * pr_auth * cr_tree auth * cr_tree auth ]
    type cr_auth = cr_tree auth
    type forest = cr_auth list * pos
    type forest_auth = forest auth

    val init_forest : unit -> forest_auth
    val retrieve : key -> forest_auth -> value option authenticated_computation
    (* Also return the position where the value is appended *)
    val append : key -> value -> forest_auth -> (forest_auth * pos) option authenticated_computation
    val print_key_vals : forest_auth -> unit authenticated_computation
    (* Check if forest2 is an extension of forest1 *)
    val is_extension : key -> value -> pos -> forest_auth -> forest_auth -> bool authenticated_computation
  end


module MerkleSq : MERKLESQ =
  functor (K : AUTHENTIKIT2) -> struct
    open K
    
    type 'a evi_option = [`left | `right of 'a]

    type key = string
    type priv_key = random
    type value = string
    type data = priv_key * value
    type pos = int
    type pos_range = pos * pos

    type pr_tree = [`left of data evi_option | `right of pr_tree auth * pr_tree auth ]
    type pr_auth = pr_tree auth

    type cr_tree = [`left of pos_range * data | `right of pos_range * pr_auth * cr_tree auth * cr_tree auth ]
    type cr_auth = cr_tree auth
    type forest = cr_auth list * pos
    type forest_auth = forest auth

    let key_evi : key Authenticatable.evidence =
      Authenticatable.string
    let data_evi : data Authenticatable.evidence = 
      Authenticatable.(pair random string)
    let pos_evi : pos_range Authenticatable.evidence =
      Authenticatable.(pair int int)
    let pr_tree_evi : pr_tree Authenticatable.evidence =
      Authenticatable.(sum (option data_evi) (pair auth auth))
    let cr_tree_evi : cr_tree Authenticatable.evidence =
      Authenticatable.(sum (pair pos_evi data_evi) (quad pos_evi auth auth auth))
    let forest_evi : forest Authenticatable.evidence =
      Authenticatable.(pair (list auth) int)
    

    let init_forest () = auth forest_evi ([], 0)

    let cr_tree_leaf i1 i2 key value = `left ((i1, i2), (key, value))
    let cr_tree_node i1 i2 pr_tree left right = `right ((i1, i2), pr_tree, left, right)

    let pr_tree_empty = `left `left
    let pr_tree_empty_auth = auth pr_tree_evi pr_tree_empty
    let pr_tree_leaf kv = `left (`right kv)
    let pr_tree_node left right = `right (left, right)

    let last_cr_tree_size (forest_size as n) = (n land (-n))

    let retrieve_prtree key tree =
      let rec retrieve_prtree_aux key tree depth =
        let* tree = unauth pr_tree_evi tree in
        match tree with
        | `left `left -> return None
        | `left (`right (k, v)) -> 
          (* print_endline (Int64.to_string key); *)
          if Int64.equal key k then return (Some v)
          else return None
        | `right (left, right) ->
          if depth >= 64 then failwith "Exceeded max depth";
          (* print_endline (Int64.to_string key); *)
          let new_key = Int64.shift_right key 1 in
          let i = Int64.sub key (Int64.shift_left new_key 1) in
          if Int64.equal i 0L then retrieve_prtree_aux new_key left (depth+1)
          else retrieve_prtree_aux new_key right (depth+1)
      in retrieve_prtree_aux key tree 0

    let rec retrieve_aux key trees =
      match trees with
      | [] -> return None
      | tree::tail ->
        let* tree = unauth cr_tree_evi tree in
        match tree with
        | `left (_, (k, v)) ->
          (* print_endline k; *)
          if k = key then return (Some v) else retrieve_aux key tail
        | `right (_, pr, _, _) ->
          let* res = retrieve_prtree key pr in
          match res with
          | None -> retrieve_aux key tail
          | Some _ -> return res
    
    let retrieve key forest =
      let* (trees, n) = unauth forest_evi forest in
      let* key = randomize key_evi key in
      retrieve_aux key trees

    let print_data (key, v) =
      print_endline ("key:"^(Int64.to_string key))

    let print_key_vals_prtree pr_tree =
      let rec aux pr_tree key_cur depth =
        let* pr_tree = unauth pr_tree_evi pr_tree in
        match pr_tree with
        | `left `left -> return ()
        | `left (`right (key, v)) -> 
          print_data (key, v); return ()
        | `right (left, right) ->
          let* _ = aux left key_cur (depth+1) in
          aux right (Int64.add (Int64.shift_left 1L depth) key_cur) (depth+1)
      in
      aux pr_tree 0L 0

    let print_key_vals_crtree cr_tree =
      let* cr_tree = unauth cr_tree_evi cr_tree in
      match cr_tree with
      | `left (_, data) -> print_data data; return ()
      | `right (_, pr_tree, _, _) ->
        print_key_vals_prtree pr_tree

    let print_key_vals forest =
      let rec aux trees =
        match trees with
        | [] -> return ()
        | tree :: trees ->
          print_endline "tree:";
          let* _ = print_key_vals_crtree tree in
          aux trees
      in
      print_endline "forest:";
      let* (trees, n) = unauth forest_evi forest in
      aux trees


    (* let rec inorder tree =
      match tree with
      | `left `left -> return []
      | `left (`right kv) -> return [kv]
      | `right (kv, left, right) ->
        let* left = unauth pr_tree_evi left in
        let* right = unauth pr_tree_evi right in
        let* left_tree = inorder left in
        let* right_tree = inorder right in
        return (left_tree @ (kv :: right_tree))
    
    let rec merge_sorted l1 l2 =
      match l1, l2 with
      | [], l | l, [] -> l
      | h1 :: t1, h2 :: t2 ->
        if h1 <= h2 then h1 :: merge_sorted t1 l2
        else h2 :: merge_sorted l1 t2

    let split l =
      let rec split_aux l left right =
        match l, left, right with
        | [], _, _ | [_], _, _ -> (List.rev left), right
        | _ :: _ :: t, _, h :: right ->
            split_aux t (h :: left) right 
        | _ -> failwith "unbalanced"
      in
      split_aux l [] l

    let rec from_list l = match l with
      | [] -> pr_tree_empty_auth
      | [kv] -> auth pr_tree_evi (pr_tree_leaf kv)
      | l ->
        let left, right = split l in
        let kv, right = match right with
          | [] -> failwith "unreachable case in from_list"
          | h::t -> h, t
        in
        auth pr_tree_evi (pr_tree_node kv (from_list left) (from_list right)) *)

    let rec merge_prefix_leafs (k1, v1) (k2, v2) depth =
      if depth >= 64 then failwith "Exceeded max depth";
      let new_k1 = Int64.shift_right k1 1 in
      let i1 = Int64.sub k1 (Int64.shift_left new_k1 1) in
      let new_k2 = Int64.shift_right k2 1 in
      let i2 = Int64.sub k2 (Int64.shift_left new_k2 1) in
      if Int64.equal i1 i2 then
        if Int64.equal i1 0L then
          let left_tree = merge_prefix_leafs (new_k1, v1) (new_k2, v2) (depth+1) |> auth pr_tree_evi in
          `right (left_tree, pr_tree_empty_auth)
        else
          let right_tree = merge_prefix_leafs (new_k1, v1) (new_k2, v2) (depth+1) |> auth pr_tree_evi in
          `right (pr_tree_empty_auth, right_tree)
      else
        if Int64.equal i1 0L then
          `right (pr_tree_leaf (new_k1, v1) |> auth pr_tree_evi, 
            pr_tree_leaf (new_k2, v2) |> auth pr_tree_evi)
        else
          `right (pr_tree_leaf (new_k2, v2) |> auth pr_tree_evi, 
            pr_tree_leaf (new_k1, v1) |> auth pr_tree_evi)

    let rec insert_kv_prtree (k, v) tree depth =
      match tree with
      | `left `left -> `left (`right (k, v)) |> return
      | `left (`right (k2, v2)) -> 
        if Int64.equal k k2 then failwith "key collision";
        merge_prefix_leafs (k, v) (k2, v2) depth |> return
      | `right (left, right) ->
        if depth >= 64 then failwith "Exceeded max depth";
        let new_k1 = Int64.shift_right k 1 in
        let i1 = Int64.sub k (Int64.shift_left new_k1 1) in
        if Int64.equal i1 0L then
          let* left_un = unauth pr_tree_evi left in
          let* left = insert_kv_prtree (new_k1, v) left_un (depth+1) in
          `right (auth pr_tree_evi left, right) |> return
        else
          let* right_un = unauth pr_tree_evi right in
          let* right = insert_kv_prtree (new_k1, v) right_un (depth+1) in
          `right (left, auth pr_tree_evi right) |> return

    let merge_prefix_trees tree1 tree2 = 
      let rec merge_prefix_trees_aux tree1 tree2 depth =
        match tree1, tree2 with
        | `left `left, `left `left -> `left `left |> return
        | `left `left, `left (`right (k, v))
        | `left (`right (k, v)), `left `left -> 
          `left (`right (k, v)) |> return
        | `left (`right (k1, v1)), `left (`right (k2, v2)) ->
          if Int64.equal k1 k2 then failwith "key collision";
          merge_prefix_leafs (k1, v1) (k2, v2) depth |> return
        | `left `left, `right (left, right)
        | `right (left, right), `left `left -> 
          `right (left, right) |> return
        | `left (`right (k, v)), `right (left, right)
        | `right (left, right), `left (`right (k, v)) ->
          insert_kv_prtree (k, v) (`right (left, right)) depth
        | `right (left1, right1), `right (left2, right2) ->
          let* left1 = unauth pr_tree_evi left1 in
          let* left2 = unauth pr_tree_evi left2 in
          let* right1 = unauth pr_tree_evi right1 in
          let* right2 = unauth pr_tree_evi right2 in
          let* left = merge_prefix_trees_aux left1 left2 (depth+1) in
          let* right = merge_prefix_trees_aux right1 right2 (depth+1) in
          `right (left |> auth pr_tree_evi, right |> auth pr_tree_evi) |> return
      in merge_prefix_trees_aux tree1 tree2 0

    let rec merge_cr_tree tree trees =
      let tree_auth = auth cr_tree_evi tree in
      let* ((i1, i2), pr1) = match tree with
        | `left (pos, kv) -> return (pos, pr_tree_leaf kv)
        | `right (pos, pr_tree, _, _) -> 
          let* pr_tree = unauth pr_tree_evi pr_tree in
          return (pos, pr_tree)
      in
      match trees with
      | [] -> return [tree_auth]
      | head::tail ->
        let* ht = unauth cr_tree_evi head in
        let* ((j1, j2), pr2) = match ht with
          | `left (pos, kv) -> return (pos, pr_tree_leaf kv)
          | `right (pos, pr_tree, _, _) -> 
            let* pr_tree = unauth pr_tree_evi pr_tree in
            return (pos, pr_tree)
        in
        let n1, n2 = i2-i1, j2-j1 in
        if n1 < n2 then return (tree_auth :: trees)
        else if n1 > n2 then failwith "right tree is smaller"
        else
          let* new_pr_tree = merge_prefix_trees pr1 pr2 in
          let new_cr_tree = cr_tree_node j1 i2 (auth pr_tree_evi new_pr_tree) head tree_auth in
          merge_cr_tree new_cr_tree tail

    let append key value forest =
      (* let* _ = print_key_vals forest in *)
      let* (trees, n) = unauth forest_evi forest in
      let* key = randomize key_evi key in
      (* print_endline ("rand:"^(Int64.to_string key)); *)
      let* key_exists = retrieve_aux key trees in
      match key_exists with
      | None ->
        let new_cr_tree = cr_tree_leaf n (n+1) key value in
        let* trees = merge_cr_tree new_cr_tree trees in
        let new_forest = auth forest_evi (trees, n+1) in
        (* let* _ = print_key_vals new_forest in *)
        return (Some (new_forest, n))
      | Some _ -> print_endline "key already exists"; return None


    let rec is_extension_tree key value n trees1 tree2 =
      match trees1 with
      | [] -> return true
      | tree1 :: tail1 ->
        let* tree2 = unauth cr_tree_evi tree2 in
        match tree2 with
        | `left x ->
          let* tree1 = unauth cr_tree_evi tree1 in
          begin match tree1 with
          | `left y -> return (x = y && List.length tail1 = 0)
          | `right _ -> (print_string "insufficient tree2\n"; return false)
          end
        | `right ((i1, i2), pr_tree, left, right) ->
          let* retrieve_res =
            if i1 <= n && n < i2 then
              let* ret_res = retrieve_prtree key pr_tree in
              match ret_res with
              | None -> print_string "retrieve failed\n"; return false
              | Some v -> 
                if value = v then return true
                else (print_string "value mismatch\n"; return false)
            else return true
          in
          if retrieve_res then
            let* b = eqauth tree1 left in
            if b then is_extension_tree key value n tail1 right
            else is_extension_tree key value n trees1 left
          else return false

    let is_extension key value n forest1 forest2 =
      let rec is_extension_aux key trees1 trees2 =
        match trees1, trees2 with
        | tree1::tail1, tree2::tail2 ->
          let* b = eqauth tree1 tree2 in
          if b then is_extension_aux key tail1 tail2
          else is_extension_tree key value n trees1 tree2
        | [], _ -> return true
        | _, [] -> print_string "empty forest1\n"; return false
      in

      let* trees1, n1 = unauth forest_evi forest1 in
      let* trees2, n2 = unauth forest_evi forest2 in

      let trees1 = List.rev trees1 in
      let trees2 = List.rev trees2 in
      let* key = randomize key_evi key in
      is_extension_aux key trees1 trees2

  end
