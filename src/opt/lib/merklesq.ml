open Auth

module type MERKLESQ =
  functor (K : AUTHENTIKIT2) -> sig
    open K
  
    type 'a evi_option = [`left | `right of 'a]
  
    type key = int
    type value = string
    type data = key * value
    type pos = int
    type pos_range = pos * pos

    type pr_tree = [`left of data evi_option | `right of data * pr_tree auth * pr_tree auth ]
    type pr_auth = pr_tree auth

    type cr_tree = [`left of pos_range * data | `right of pos_range * pr_auth * cr_tree auth * cr_tree auth ]
    type cr_auth = cr_tree auth
    type forest = cr_auth list * pos
    type forest_auth = forest auth

    val init_forest : unit -> forest_auth
    val retrieve : key -> forest_auth -> value option authenticated_computation
    (* Also return the position where the value is appended *)
    val append : key -> value -> forest_auth -> (forest_auth * pos) option authenticated_computation
    (* Check if forest2 is an extension of forest1 *)
    val is_extension : key -> value -> pos -> forest_auth -> forest_auth -> bool authenticated_computation
  end


module MerkleSq : MERKLESQ =
  functor (K : AUTHENTIKIT2) -> struct
    open K
    
    type 'a evi_option = [`left | `right of 'a]

    type key = int
    type value = string
    type data = key * value
    type pos = int
    type pos_range = pos * pos

    type pr_tree = [`left of data evi_option | `right of data * pr_tree auth * pr_tree auth ]
    type pr_auth = pr_tree auth

    type cr_tree = [`left of pos_range * data | `right of pos_range * pr_auth * cr_tree auth * cr_tree auth ]
    type cr_auth = cr_tree auth
    type forest = cr_auth list * pos
    type forest_auth = forest auth

    let data_evi : data Authenticatable.evidence = 
      Authenticatable.(pair int string)
    let pos_evi : pos_range Authenticatable.evidence =
      Authenticatable.(pair int int)
    let pr_tree_evi : pr_tree Authenticatable.evidence =
      Authenticatable.(sum (option data_evi) (trio data_evi auth auth))
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
    let pr_tree_node kv left right = `right (kv, left, right)

    let last_cr_tree_size (forest_size as n) = (n land (-n))

    let rec retrieve_prtree key tree =
      let* tree = unauth pr_tree_evi tree in
      match tree with
      | `left `left -> return None
      | `left (`right (k, v)) -> 
        if key = k then return (Some v)
        else return None
      | `right ((k, v), left, right) ->
        if key < k then retrieve_prtree key left
        else if key = k then return (Some v)
        else retrieve_prtree key right

    let rec retrieve_aux key trees =
      match trees with
      | [] -> return None
      | tree::tail ->
        let* tree = unauth cr_tree_evi tree in
        match tree with
        | `left (_, (k, v)) ->
          if k = key then return (Some v) else retrieve_aux key tail
        | `right (_, pr, _, _) ->
          let* res = retrieve_prtree key pr in
          match res with
          | None -> retrieve_aux key tail
          | Some _ -> return res
    
    let retrieve key forest =
      let* (trees, n) = unauth forest_evi forest in
      retrieve_aux key trees


    let rec inorder tree =
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
        auth pr_tree_evi (pr_tree_node kv (from_list left) (from_list right))

    let merge_prefix_trees tree1 tree2 = 
      let* l1 = inorder tree1 in
      let* l2 = inorder tree2 in
      let l = merge_sorted l1 l2 in
      return (from_list l)

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
          let new_cr_tree = cr_tree_node j1 i2 new_pr_tree head tree_auth in
          merge_cr_tree new_cr_tree tail
    
    let append key value forest =
      let* (trees, n) = unauth forest_evi forest in
      let* key_exists = retrieve_aux key trees in
      match key_exists with
      | None ->
        let new_cr_tree = cr_tree_leaf n (n+1) key value in
        let* trees = merge_cr_tree new_cr_tree trees in
        return (Some ((auth forest_evi (trees, n+1)), n))
      | Some _ -> return None


    let rec is_extension_tree key value n trees1 tree2 =
      match trees1 with
      | [] -> return true
      | tree1 :: tail1 ->
        let* tree2 = unauth cr_tree_evi tree2 in
        match tree2 with
        | `left x ->
          let* tree1 = unauth cr_tree_evi tree1 in
          begin match tree1 with
          | `left y -> return (x = y)
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
            let* b = eqauth cr_tree_evi tree1 left in
            if b then is_extension_tree key value n tail1 right
            else is_extension_tree key value n trees1 left
          else return false

    let is_extension key value n forest1 forest2 =
      let rec is_extension_aux trees1 trees2 =
        match trees1, trees2 with
        | tree1::tail1, tree2::tail2 ->
          let* b = eqauth cr_tree_evi tree1 tree2 in
          if b then is_extension_aux tail1 tail2
          else is_extension_tree key value n trees1 tree2
        | [], _ -> return true
        | _, [] -> print_string "empty forest1\n"; return false
      in

      let* trees1, n1 = unauth forest_evi forest1 in
      let* trees2, n2 = unauth forest_evi forest2 in

      let trees1 = List.rev trees1 in
      let trees2 = List.rev trees2 in
      is_extension_aux trees1 trees2

  end
