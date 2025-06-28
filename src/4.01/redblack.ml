open Auth

module type REDBLACK =
  functor (K : AUTHENTIKIT) -> sig
    open K

    (* we always choose "" as the string in option_t and color *)
    type 'a option_t = [`left of string | `right of 'a]
    type color = [`left of string | `right of string] (* left is red, right is black *)
    type value_option = string option_t
    type tree = (color * tree auth * (int * value_option) * tree auth) option_t
    type tree_auth = tree auth

    val empty_tree : unit -> tree_auth
    val retrieve : int -> tree_auth -> string option authenticated_computation
    val update : int -> string -> tree_auth -> tree_auth authenticated_computation
    val insert : int -> string -> tree_auth -> tree_auth authenticated_computation
    val delete : int -> tree_auth -> tree_auth authenticated_computation
    val retrieve_list : int list -> tree_auth -> (string option list) authenticated_computation
    val update_list : int list -> string list -> tree_auth -> tree_auth authenticated_computation
    val insert_list : int list -> string list -> tree_auth -> tree_auth authenticated_computation
    val delete_list : int list -> tree_auth -> tree_auth authenticated_computation

  end

module RedBlack : REDBLACK =
  functor (K : AUTHENTIKIT) -> struct
    open K

    (* we always choose "" as the string in option_t and color *)
    type 'a option_t = [`left of string | `right of 'a]
    type color = string option_t (* left is red, right is black *)
    type value_option = string option_t
    type tree = (color * tree auth * (int * value_option) * tree auth) option_t
    type tree_auth = tree auth

    let option_evi (a_evi : 'a Authenticatable.evidence) :'a option_t Authenticatable.evidence =
      Authenticatable.(sum string a_evi)
    let value_evi : value_option Authenticatable.evidence = option_evi Authenticatable.string
    let tree_evi : tree Authenticatable.evidence =
      option_evi Authenticatable.(quad value_evi auth (pair int value_evi) auth)

    let empty_tree () = auth tree_evi (`left "")
    let make_node c l kv r = auth tree_evi (`right (c, l, kv, r))
    let auth t = auth tree_evi t
    let red = `left ""
    let black = `right ""
    let none_v = `left ""
    let some_v v = `right v

    let rec retrieve x t =
      bind (unauth tree_evi t)
        (fun t ->
          match t with
          | `left _ -> return None
          | `right (_, _, (y, `right v), _) -> 
            if y = x then return (Some v) else return None
          | `right (_, l, (y, `left _), r) -> 
            if x <= y then retrieve x l else retrieve x r)

    let rec update k v t =
      bind (unauth tree_evi t)
        (fun un_t ->
          match un_t with
          | `left _ -> return t
          | `right (c, l, (y, _), r) when k = y -> 
            return (make_node c l (y, some_v v) r)
          | `right (c, l, (y, v'), r) when k < y -> 
            bind (update k v l)
              (fun l -> return (make_node c l (y, v') r))
          | `right (c, l, (y, v'), r) -> 
            bind (update k v r)
              (fun r -> return (make_node c l (y, v') r)))

    let blacken t =
      bind (unauth tree_evi t)
        (fun un_t ->
          match un_t with
          | `left _ -> return t
          | `right (_, l, x, r) -> make_node black l x r |> return)

    let redden t =
      bind (unauth tree_evi t)
        (fun un_t ->
          match un_t with
          | `left _ -> failwith "false"
          | `right (_, l, x, r) -> make_node red l x r |> return)
    
    let balanceL t =
      bind (unauth tree_evi t)
        (fun un_t ->
          match un_t with
          | `right (`right _, l, a, r) ->
            bind (unauth tree_evi l)
              (fun un_l ->
                match un_l with
                | `right (`left _, l1, a1, r1) ->
                  bind (unauth tree_evi l1)
                    (fun un_l1 ->
                      match un_l1 with
                      | `right (`left _, l2, a2, r2) ->
                        make_node red (make_node black l2 a2 r2) a1 (make_node black r1 a r) |> return
                      | _ ->
                        bind (unauth tree_evi r1)
                          (fun un_r1 ->
                            match un_r1 with
                            | `right (`left _, l2, a2, r2) ->
                              make_node red (make_node black l1 a1 l2) a2 (make_node black r2 a r) |> return
                            | _ -> return t
                            )
                      )
                | _ -> return t
                )
          | _ -> return t
          )

    let balanceR t =
      bind (unauth tree_evi t)
        (fun un_t ->
          match un_t with
          | `right (`right _, l, a, r) ->
            bind (unauth tree_evi r)
              (fun un_r ->
                match un_r with
                | `right (`left _, l1, a1, r1) ->
                  bind (unauth tree_evi l1)
                    (fun un_l1 ->
                      match un_l1 with
                      | `right (`left _, l2, a2, r2) ->
                        make_node red (make_node black l a l2) a2 (make_node black r2 a1 r1) |> return
                      | _ ->
                        bind (unauth tree_evi r1)
                          (fun un_r1 ->
                            match un_r1 with
                            | `right (`left _, l2, a2, r2) ->
                              make_node red (make_node black l a l1) a1 (make_node black l2 a2 r2) |> return
                            | _ -> return t
                            )
                      )
                | _ -> return t
                )
          | _ -> return t
          )
    
    let insert x v t =
      let leaf = make_node black (empty_tree ()) (x, some_v v) (empty_tree ()) in
      let rec ins t =
        bind (unauth tree_evi t)
          (fun un_t -> match un_t with
            | `left _ -> return leaf
            | `right (c, l, (y, `right _), r) ->
              if x = y then return t
              else if x < y then make_node red leaf (x, none_v) t |> return 
              else if x > y then make_node red t (y, none_v) leaf |> return
              else failwith "false"
            | `right (c, l, (y, `left _), r) ->
              if x = y then return t
              else if x < y then
                bind (ins l) (fun l_ins -> make_node c l_ins (y, none_v) r |> balanceL)
              else if x > y then
                bind (ins r) (fun r_ins -> make_node c l (y, none_v) r_ins |> balanceR)
              else failwith "false"
          )
      in
      bind (ins t) blacken
    
    let unbalancedL t =
      match t with
      | `right (c, l, a, r) ->
        bind (unauth tree_evi l)
          (fun un_l ->
            match un_l with
            | `right (`right _, l1, a1, r1) ->
              bind (make_node black (make_node red l1 a1 r1) a r |> balanceL)
                (fun res -> return (res, c=black))
            | `right (`left _, l1, a1, r1) ->
              bind (redden r1)
                (fun red_r1 ->
                  bind (make_node black red_r1 a r |> balanceL)
                    (fun bal_t ->
                      return (make_node black l1 a1 bal_t, false)
                      )
                  )
            | _ -> failwith "false"
            )
      | _ -> failwith "false"

    let unbalancedR t =
      match t with
      | `right (c, l, a, r) ->
        bind (unauth tree_evi r)
          (fun un_r ->
            match un_r with
            | `right (`right _, l1, a1, r1) ->
              bind (make_node black l a (make_node red l1 a1 r1) |> balanceR)
                (fun res -> return (res, c=black))
            | `right (`left _, l1, a1, r1) ->
              bind (redden l1)
                (fun red_l1 ->
                  bind (make_node black l a red_l1 |> balanceL)
                    (fun bal_t ->
                      return (make_node black bal_t a1 r1, false)
                      )
                  )
            | _ -> failwith "false"
            )
      | _ -> failwith "false"

    let delete x t =
      let rec del t =
        bind (unauth tree_evi t)
          (fun un_t ->
            match un_t with
            | `left _ -> failwith "delete called on empty tree"
            | `right (_, _, (y, `right _), _) ->
              if x = y then return ((empty_tree (), true), None)
              else failwith ("delete: "^(string_of_int x)^" not found")
            | `right (c, l, (y, `left _), r) ->
              if x <= y then
                bind (del l)
                  (fun ((l, d), m) ->
                    bind (unauth tree_evi l)
                      (fun un_l ->
                        match un_l with
                        | `left _ -> return ((r, c=black), None)
                        | `right _ ->
                          let k = 
                            if x=y then 
                              match m with Some m -> m, none_v | _ -> failwith "false"
                            else y, none_v
                          in
                          let t = `right (c, l, k, r) in
                          if d then
                            bind (unbalancedR t)
                              (fun unb_t -> return (unb_t, None))
                          else return ((auth t, false), None)
                        )
                    )
              else
                bind (del r)
                  (fun ((r, d), m) ->
                    bind (unauth tree_evi r)
                      (fun un_r ->
                        match un_r with
                        | `left _ -> return ((l, c=black), Some y)
                        | `right _ ->
                          let k = y, none_v in
                          let t = `right (c, l, k, r) in
                          if d then
                            bind (unbalancedL t)
                              (fun unb_t -> return (unb_t, m))
                          else return ((auth t, false), m)
                        )
                    )
            )
      in
      bind (del t)
        (fun ((t, _), _) -> blacken t)

    let rec retrieve_list keys t =
      match keys with
      | [] -> return []
      | p :: keys ->
          bind (retrieve p t)
            (fun v ->
              bind (retrieve_list keys t)
                (fun vs ->
                return (v :: vs)))

    let rec update_list keys values t =
      let key_values = List.combine keys values in
      match key_values with
      | [] -> return t
      | (key, value) :: key_values ->
          let keys, values = List.split key_values in
          bind (update key value t)
            (fun up_t -> 
                bind (update_list keys values up_t)
                  (fun up_t -> return up_t))

    let rec insert_list keys values t =
      let key_values = List.combine keys values in
      match key_values with
      | [] -> return t
      | (key, value) :: key_values ->
          let keys, values = List.split key_values in
          bind (insert key value t)
            (fun up_t -> 
                bind (insert_list keys values up_t)
                  (fun up_t -> return up_t))

    let rec delete_list keys t =
      match keys with
      | [] -> return t
      | key :: keys ->
          bind (delete key t)
            (fun del_t -> 
                bind (delete_list keys del_t)
                  (fun del_t -> return del_t))


  end
