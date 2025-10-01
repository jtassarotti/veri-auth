open Auth

module type OPTIKS =
  functor (K : AUTHENTIKIT2) -> sig
    open K

    type 'a evi_option = [`left | `right of 'a]

    type key = string
    type version = int
    type label = key * version
    type priv_label = random
    type value = string
    type data = priv_label * value
    

    (* merkle sparse/patricia trie *)
    type ozks = [`left of data evi_option | `right of ozks auth * ozks auth ]
    type ozks_auth = ozks auth
    
    type epoch = int
    (* epoch, ozks *)
    type state = ozks_auth * int
    type state_auth = state auth

    val init_state : unit -> state_auth
    val retrieve : key -> state_auth -> value option authenticated_computation
    val append : key -> value -> state_auth -> state_auth authenticated_computation
    val history : key -> state_auth -> value list authenticated_computation
  end

module Optiks : OPTIKS =
  functor (K : AUTHENTIKIT2) -> struct
    open K

    type 'a evi_option = [`left | `right of 'a]

    type key = string
    type version = int
    type label = key * version
    type priv_label = random
    type value = string
    type data = priv_label * value
    

    (* merkle sparse/patricia trie *)
    type ozks = [`left of data evi_option | `right of ozks auth * ozks auth ]
    type ozks_auth = ozks auth
    
    type epoch = int
    (* epoch, ozks *)
    type state = ozks_auth * epoch
    type state_auth = state auth

    let label_evi : label Authenticatable.evidence =
      Authenticatable.(pair string int)
    let data_evi : data Authenticatable.evidence = 
      Authenticatable.(pair random string)
    let ozks_evi : ozks Authenticatable.evidence =
      Authenticatable.(sum (option data_evi) (pair auth auth))
    let state_evi : state Authenticatable.evidence =
      Authenticatable.(pair auth int)

    let init_ozks () = auth ozks_evi (`left `left)
    let init_state () = auth state_evi (init_ozks (), 0)

    let ozks_empty = `left `left
    let ozks_empty_auth = auth ozks_evi ozks_empty
    let ozks_leaf kv = `left (`right kv)
    let ozks_node left right = `right (left, right)

    let retrieve_ozks label ozks =
      let rec retrieve_ozks_aux label ozks depth =
        match ozks with
        | `left `left -> return None
        | `left (`right (k, v)) -> 
          (* print_endline (Int64.to_string label); *)
          if Int64.equal label k then return (Some v)
          else return None
        | `right (left, right) ->
          if depth >= 64 then failwith "Exceeded max depth";
          (* print_endline (Int64.to_string label); *)
          let new_label = Int64.shift_right label 1 in
          let i = Int64.sub label (Int64.shift_left new_label 1) in
          if Int64.equal i 0L then 
            let* left = unauth ozks_evi left in
            retrieve_ozks_aux new_label left (depth+1)
          else 
            let* right = unauth ozks_evi right in
            retrieve_ozks_aux new_label right (depth+1)
      in retrieve_ozks_aux label ozks 0

    let retrieve_key key ozks =
      (* print_endline "retrieve"; *)
      let rec retrieve_aux version last_value =
        (* print_endline (string_of_int version); *)
        let label = (key, version) in
        let* priv_label = randomize label_evi label in
        let* res = retrieve_ozks priv_label ozks in
        match res with
        | None -> return (last_value, version-1)
        | Some value -> 
          (* print_endline value; *)
          retrieve_aux (version+1) (Some value)
      in
      retrieve_aux 1 None

    let retrieve key state =
      let* (ozks_auth, epoch) = unauth state_evi state in
      let* ozks = unauth ozks_evi ozks_auth in
      let* (value, version) = retrieve_key key ozks in
      return value

    
    let append_ozks key value ozks =
      let rec merge_prefix_leafs (k1, v1) (k2, v2) depth =
        if depth >= 64 then failwith "Exceeded max depth";
        let new_k1 = Int64.shift_right k1 1 in
        let i1 = Int64.sub k1 (Int64.shift_left new_k1 1) in
        let new_k2 = Int64.shift_right k2 1 in
        let i2 = Int64.sub k2 (Int64.shift_left new_k2 1) in
        if Int64.equal i1 i2 then
          if Int64.equal i1 0L then
            let left_tree = merge_prefix_leafs (new_k1, v1) (new_k2, v2) (depth+1) |> auth ozks_evi in
            `right (left_tree, ozks_empty_auth)
          else
            let right_tree = merge_prefix_leafs (new_k1, v1) (new_k2, v2) (depth+1) |> auth ozks_evi in
            `right (ozks_empty_auth, right_tree)
        else
          if Int64.equal i1 0L then
            `right (ozks_leaf (new_k1, v1) |> auth ozks_evi, 
              ozks_leaf (new_k2, v2) |> auth ozks_evi)
          else
            `right (ozks_leaf (new_k2, v2) |> auth ozks_evi, 
              ozks_leaf (new_k1, v1) |> auth ozks_evi)
      in
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
            let* left_un = unauth ozks_evi left in
            let* left = insert_kv_prtree (new_k1, v) left_un (depth+1) in
            `right (auth ozks_evi left, right) |> return
          else
            let* right_un = unauth ozks_evi right in
            let* right = insert_kv_prtree (new_k1, v) right_un (depth+1) in
            `right (left, auth ozks_evi right) |> return
      in
      insert_kv_prtree (key, value) ozks 0

    let append key value state =
      let* (ozks_auth, epoch) = unauth state_evi state in
      let* ozks = unauth ozks_evi ozks_auth in
      let* res = retrieve_key key ozks in
      let* ozks_upd = match res with
        | None, _ ->
          (* print_endline "key not found"; *)
          let label = (key, 1) in
          let* priv_label = randomize label_evi label in
          append_ozks priv_label value ozks
        | Some _, version ->
          (* print_endline ("key found "^(string_of_int version)); *)
          let label = (key, version+1) in
          let* priv_label = randomize label_evi label in
          append_ozks priv_label value ozks
      in
      let ozks_auth = auth ozks_evi ozks_upd in
      return (auth state_evi (ozks_auth, epoch+1))


    let history key state =
      let* (ozks_auth, epoch) = unauth state_evi state in
      let* ozks = unauth ozks_evi ozks_auth in
      let rec aux version acc =
        let label = (key, version) in
        let* priv_label = randomize label_evi label in
        let* res = retrieve_ozks priv_label ozks in
        match res with
        | None -> return acc
        | Some value -> aux (version+1) (value::acc)
      in
      let* vals = aux 1 [] in
      return (List.rev vals)

  end

