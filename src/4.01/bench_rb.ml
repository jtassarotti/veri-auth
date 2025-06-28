open Auth
open Merkle
open Redblack
open Prover_rev
open Verifier
open Prover_marshal
open Verifier_marshal
open Prover_io
open Verifier_io
open Ideal
open Test_utils
open Utils
open Hash

let data_folder = "../data"
let proof_folder = Printf.sprintf "%s/%s" data_folder (Sys.ocaml_version)

let n_configs = 5
let n_sizes = 18
let treesize_args = list_init n_sizes (fun i -> i + 4)
let n_reps = 10
let config_array = list_init n_reps (fun i -> List.map (fun s -> ((s, i))) treesize_args) |> List.concat

let num_rb_inserts = 100000

let read_keys n chn = 
  let rec aux n keys =
    if n = 0 then List.rev keys
    else
      let line = input_line chn in
      let key = int_of_string line in
      aux (n - 1) (key :: keys)
  in
  aux n []

let job_queue = ref []

module DirRedblackIdeal = struct
  type color = Red | Black
  type value_option = Non | Som of string
  type tree = Tip | Bin of (color * tree * (int * value_option) * tree)

  let empty_tree () = Tip
  let make_node c l kv r = Bin (c, l, kv, r)

  let blacken t =
    match t with
    | Tip -> t
    | Bin (_, l, x, r) -> make_node Black l x r

  let balanceL (t : tree) : tree = match t with
  | Bin (Black, l, a, r) -> begin match l with
    | Bin (Red, l1, a1, r1) -> begin match l1 with
      | Bin (Red, l2, a2, r2) -> (Bin(Red,(Bin(Black,l2,a2,r2)),a1,(Bin(Black,r1,a,r))))
      | _ -> begin match  r1 with
        | Bin (Red, l2, a2, r2) -> (Bin(Red,(Bin(Black,l1,a1,l2)),a2,(Bin(Black,r2,a,r))))
        | _ -> t
      end
    end
    | _ -> t
  end
  | _ -> t

  let balanceR (t : tree) : tree = match  t with
  | Bin (Black, l, a, r) -> begin match  r with
    | Bin (Red, l1, a1, r1) -> begin match  l1 with
      | Bin (Red, l2, a2, r2) -> (Bin(Red,(Bin(Black,l,a,l2)),a2,(Bin(Black,r2,a1,r1))))
      | _ -> begin match  r1 with
        | Bin (Red, l2, a2, r2) -> (Bin(Red,(Bin(Black,l,a,l1)),a1,(Bin(Black,l2,a2,r2))))
        | _ -> t
      end
    end
    | _ -> t
  end
  | _ -> t

  let insert x v t =
    let leaf = make_node Black (empty_tree ()) (x, Som v) (empty_tree ()) in
    let rec ins t =
      match t with
      | Tip -> leaf
      | Bin (c, l, (y, Som _), r) ->
        if x = y then t
        else if x < y then make_node Red leaf (x, Non) t
        else if x > y then make_node Red t (y, Non) leaf
        else failwith "false"
      | Bin (c, l, (y, Non), r) ->
        if x = y then t
        else if x < y then make_node c (ins l) (y, Non) r |> balanceL
        else if x > y then make_node c l (y, Non) (ins r) |> balanceR
        else failwith "false"
    in
    ins t |> blacken
end

module RedBlackDirIdeal = struct
  type 'a option_t = [`left of string | `right of 'a]
  type color = string option_t (* left is red, right is black *)
  type value_option = string option_t
  type tree = (color * tree Ideal.auth * (int * value_option) * tree Ideal.auth) option_t
  type tree_auth = tree Ideal.auth

  let option_evi (a_evi : 'a Ideal.Authenticatable.evidence) :'a option_t Ideal.Authenticatable.evidence =
    Ideal.Authenticatable.(sum string a_evi)
  let value_evi : value_option Ideal.Authenticatable.evidence = option_evi Ideal.Authenticatable.string
  let tree_evi : tree Ideal.Authenticatable.evidence =
    option_evi Ideal.Authenticatable.(quad value_evi auth (pair int value_evi) auth)

  let empty_tree () = Ideal.auth tree_evi (`left "")
  let make_node c l kv r = Ideal.auth tree_evi (`right (c, l, kv, r))
  let auth t = Ideal.auth tree_evi t
  let red = `left ""
  let black = `right ""
  let none_v = `left ""
  let some_v v = `right v

  let blacken t =
    Ideal.bind (Ideal.unauth tree_evi t)
      (fun un_t ->
        match un_t with
        | `left _ -> Ideal.return t
        | `right (_, l, x, r) -> make_node black l x r |> Ideal.return)

  let balanceL t =
      Ideal.bind (Ideal.unauth tree_evi t)
        (fun un_t ->
          match un_t with
          | `right (`right _, l, a, r) ->
            Ideal.bind (Ideal.unauth tree_evi l)
              (fun un_l ->
                match un_l with
                | `right (`left _, l1, a1, r1) ->
                  Ideal.bind (Ideal.unauth tree_evi l1)
                    (fun un_l1 ->
                      match un_l1 with
                      | `right (`left _, l2, a2, r2) ->
                        make_node red (make_node black l2 a2 r2) a1 (make_node black r1 a r) |> Ideal.return
                      | _ ->
                        Ideal.bind (Ideal.unauth tree_evi r1)
                          (fun un_r1 ->
                            match un_r1 with
                            | `right (`left _, l2, a2, r2) ->
                              make_node red (make_node black l1 a1 l2) a2 (make_node black r2 a r) |> Ideal.return
                            | _ -> Ideal.return t
                            )
                      )
                | _ -> Ideal.return t
                )
          | _ -> Ideal.return t
          )

  let balanceR t =
    Ideal.bind (Ideal.unauth tree_evi t)
      (fun un_t ->
        match un_t with
        | `right (`right _, l, a, r) ->
          Ideal.bind (Ideal.unauth tree_evi r)
            (fun un_r ->
              match un_r with
              | `right (`left _, l1, a1, r1) ->
                Ideal.bind (Ideal.unauth tree_evi l1)
                  (fun un_l1 ->
                    match un_l1 with
                    | `right (`left _, l2, a2, r2) ->
                      make_node red (make_node black l a l2) a2 (make_node black r2 a1 r1) |> Ideal.return
                    | _ ->
                      Ideal.bind (Ideal.unauth tree_evi r1)
                        (fun un_r1 ->
                          match un_r1 with
                          | `right (`left _, l2, a2, r2) ->
                            make_node red (make_node black l a l1) a1 (make_node black l2 a2 r2) |> Ideal.return
                          | _ -> Ideal.return t
                          )
                    )
              | _ -> Ideal.return t
              )
        | _ -> Ideal.return t
        )
  
  let insert x v t =
    let leaf = make_node black (empty_tree ()) (x, some_v v) (empty_tree ()) in
    let rec ins t =
      Ideal.bind (Ideal.unauth tree_evi t)
        (fun un_t ->
          match un_t with
          | `left _ -> Ideal.return leaf
          | `right (c, l, (y, `right _), r) ->
            if x = y then Ideal.return t
            else if x < y then make_node red leaf (x, none_v) t |> Ideal.return 
            else if x > y then make_node red t (y, none_v) leaf |> Ideal.return
            else failwith "false"
          | `right (c, l, (y, `left _), r) ->
            if x = y then Ideal.return t
            else if x < y then
              Ideal.bind (ins l)
                (fun l_ins -> make_node c l_ins (y, none_v) r |> balanceL)
            else if x > y then
              Ideal.bind (ins r)
                (fun r_ins -> make_node c l (y, none_v) r_ins |> balanceR)
            else failwith "false"
          )
    in
    Ideal.bind (ins t)
      (fun ins_t -> blacken ins_t)
end

module DirRedblackProver = struct
  type 'a auth = 'a * string
  type color = Red | Black
  type value_option = Non | Som of string
  type tree = Tip | Bin of (color * tree auth * (int * value_option) * tree auth)
  type tree_hash = Tipp | Binp of (color * string * (int * value_option) * string)
  type tree_auth = tree auth

  let ser o = 
    (* tree_evi.serialize o *)
    match o with
    | Tip -> Marshal.to_string Tipp marshal_flags
    | Bin (c, (l, ls), kv, (r, rs)) -> Marshal.to_string (Binp (c, ls, kv, rs)) marshal_flags
  let auth o = o, ser o |> hash
  let unauth (t, ts) p = ser t :: p, t
  let red = Red
  let black = Black
  let none_v = Non
  let some_v v = Som v

  let empty_tree () = auth (Tip)
  let make_node c l kv r = auth (Bin (c, l, kv, r))

  let blacken t_auth p =
    match unauth t_auth p with
    | p, Tip -> p, empty_tree ()
    | p, Bin (_, l, x, r) -> p, make_node black l x r

  let balanceL t_auth p = match unauth t_auth p with
  | p, Bin (Black, l_auth, a, r_auth) -> begin match unauth l_auth p with
    | p, Bin (Red, l1_auth, a1, r1_auth) -> begin match unauth l1_auth p with
      | p, Bin (Red, l2_auth, a2, r2_auth) -> 
        p, make_node red (make_node black l2_auth a2 r2_auth) a1 (make_node black r1_auth a r_auth)
      | p, _ -> begin match unauth r1_auth p with
        | p, Bin (Red, l2_auth, a2, r2_auth) -> 
          p, make_node red (make_node black l1_auth a1 l2_auth) a2 (make_node black r2_auth a r_auth)
        | p, sr1 -> p, t_auth
      end
    end
    | p, _ -> p, t_auth
  end
  | p, _ -> p, t_auth

  let balanceR t_auth p = match unauth t_auth p with
  | p, Bin (Black, l_auth, a, r_auth) -> begin match unauth r_auth p with
    | p, Bin (Red, l1_auth, a1, r1_auth) -> begin match unauth l1_auth p with
      | p, Bin (Red, l2_auth, a2, r2_auth) -> 
        p, make_node red (make_node black l_auth a l2_auth) a2 (make_node black r2_auth a1 r1_auth)
      | p, _ -> begin match unauth r1_auth p with
        | p, Bin (Red, l2_auth, a2, r2_auth) -> 
          p, make_node red (make_node black l_auth a l1_auth) a1 (make_node black l2_auth a2 r2_auth)
        | p, sr1 -> p, t_auth
      end
    end
    | p, _ -> p, t_auth
  end
  | p, t -> p, t_auth

  let insert x v t_auth p =
    let leaf_auth = make_node black (empty_tree ()) (x, Som v) (empty_tree ()) in
    let rec ins t_auth p =
      match unauth t_auth p with
      | p, Tip -> p, leaf_auth
      | p, Bin (c, l_auth, (y, Som _), r_auth) ->
        if x = y then p, t_auth
        else if x < y then p, make_node red leaf_auth (x, Non) t_auth
        else if x > y then p, make_node red t_auth (y, Non) leaf_auth
        else failwith "false"
      | p, Bin (c, l_auth, (y, Non), r_auth) ->
        if x = y then p, t_auth
        else if x < y then let p, l_ins = ins l_auth p in
          balanceL (make_node c l_ins (y, Non) r_auth) p
        else if x > y then let p, r_ins = ins r_auth p in
          balanceR (make_node c l_auth (y, Non) r_ins) p
        else failwith "false"
    in
    let p, t_ins = ins t_auth p in
    blacken t_ins p

  let run c = 
    let p, res = c [] in
    List.rev p, res
end

module DirRedblackProverIo = struct
  type 'a auth = 'a * string
  type color = Red | Black
  type value_option = Non | Som of string
  type tree = Tip | Bin of (color * tree auth * (int * value_option) * tree auth)
  type tree_hash = Tipp | Binp of (color * string * (int * value_option) * string)
  type tree_auth = tree auth

  let output = ref (open_out_bin "/dev/null")

  let set_output s = 
    close_out !output; output := open_out_bin s
  let close_output () = close_out !output; output := open_out_bin "/dev/null"

  let prepare_unauth o = match o with
    | Tip -> Tipp
    | Bin (c, (l, ls), kv, (r, rs)) -> Binp (c, ls, kv, rs)
  let ser o = Marshal.to_string (prepare_unauth o) marshal_flags
  let auth o = o, ser o |> hash
  let unauth (t, ts) = Marshal.to_channel !output (prepare_unauth t) marshal_flags; t
  let red = Red
  let black = Black
  let none_v = Non
  let some_v v = Som v

  let empty_tree () = auth (Tip)
  let make_node c l kv r = auth (Bin (c, l, kv, r))

  let blacken t_auth =
    match unauth t_auth with
    | Tip -> empty_tree ()
    | Bin (_, l, x, r) -> make_node black l x r

  let balanceL t_auth = match unauth t_auth with
  | Bin (Black, l_auth, a, r_auth) -> begin match unauth l_auth with
    | Bin (Red, l1_auth, a1, r1_auth) -> begin match unauth l1_auth with
      | Bin (Red, l2_auth, a2, r2_auth) -> 
        make_node red (make_node black l2_auth a2 r2_auth) a1 (make_node black r1_auth a r_auth)
      | _ -> begin match unauth r1_auth with
        | Bin (Red, l2_auth, a2, r2_auth) -> 
          make_node red (make_node black l1_auth a1 l2_auth) a2 (make_node black r2_auth a r_auth)
        | sr1 -> t_auth
      end
    end
    | _ -> t_auth
  end
  | _ -> t_auth

  let balanceR t_auth = match unauth t_auth with
  | Bin (Black, l_auth, a, r_auth) -> begin match unauth r_auth with
    | Bin (Red, l1_auth, a1, r1_auth) -> begin match unauth l1_auth with
      | Bin (Red, l2_auth, a2, r2_auth) -> 
        make_node red (make_node black l_auth a l2_auth) a2 (make_node black r2_auth a1 r1_auth)
      | _ -> begin match unauth r1_auth with
        | Bin (Red, l2_auth, a2, r2_auth) -> 
          make_node red (make_node black l_auth a l1_auth) a1 (make_node black l2_auth a2 r2_auth)
        | sr1 -> t_auth
      end
    end
    | _ -> t_auth
  end
  | t -> t_auth

  let insert x v t_auth =
    let leaf_auth = make_node black (empty_tree ()) (x, Som v) (empty_tree ()) in
    let rec ins t_auth =
      match unauth t_auth with
      | Tip -> leaf_auth
      | Bin (c, l_auth, (y, Som _), r_auth) ->
        if x = y then t_auth
        else if x < y then make_node red leaf_auth (x, Non) t_auth
        else if x > y then make_node red t_auth (y, Non) leaf_auth
        else failwith "false"
      | Bin (c, l_auth, (y, Non), r_auth) ->
        if x = y then t_auth
        else if x < y then let l_ins = ins l_auth in
          balanceL (make_node c l_ins (y, Non) r_auth)
        else if x > y then let r_ins = ins r_auth in
          balanceR (make_node c l_auth (y, Non) r_ins)
        else failwith "false"
    in
    let t_ins = ins t_auth in
    blacken t_ins

  let run c = c
end

module DirRedblackProverPoly = struct
  type 'a auth = 'a * string
  type 'a option_t = [`left of string | `right of 'a]
  type color = string option_t (* left is red, right is black *)
  type value_option = string option_t
  type tree = (color * tree auth * (int * value_option) * tree auth) option_t
  type tree_auth = tree auth

  let ser o =
    match o with
    | `left _ -> Marshal.to_string (`left "") marshal_flags
    | `right (c, (l, ls), kv, (r, rs)) -> Marshal.to_string (`right (c, ls, kv, rs)) marshal_flags
  let auth o = o, ser o |> hash
  let unauth (t, ts) p = ser t :: p, t
  let red = `left ""
  let black = `right ""
  let none_v = `left ""
  let some_v v = `right v

  let empty_tree () = auth (`left "")
  let make_node c l kv r = auth (`right (c, l, kv, r))

  let blacken t_auth p =
    match unauth t_auth p with
    | p, `left _ -> p, empty_tree ()
    | p, `right (_, l, x, r) -> p, make_node black l x r

  let balanceL t_auth p = match unauth t_auth p with
  | p, `right (`right _, l_auth, a, r_auth) -> begin match unauth l_auth p with
    | p, `right (`left _, l1_auth, a1, r1_auth) -> begin match unauth l1_auth p with
      | p, `right (`left _, l2_auth, a2, r2_auth) -> 
        p, make_node red (make_node black l2_auth a2 r2_auth) a1 (make_node black r1_auth a r_auth)
      | p, _ -> begin match unauth r1_auth p with
        | p, `right (`left _, l2_auth, a2, r2_auth) -> 
          p, make_node red (make_node black l1_auth a1 l2_auth) a2 (make_node black r2_auth a r_auth)
        | p, sr1 -> p, t_auth
      end
    end
    | p, _ -> p, t_auth
  end
  | p, _ -> p, t_auth

  let balanceR t_auth p = match unauth t_auth p with
  | p, `right (`right _, l_auth, a, r_auth) -> begin match unauth r_auth p with
    | p, `right (`left _, l1_auth, a1, r1_auth) -> begin match unauth l1_auth p with
      | p, `right (`left _, l2_auth, a2, r2_auth) -> 
        p, make_node red (make_node black l_auth a l2_auth) a2 (make_node black r2_auth a1 r1_auth)
      | p, _ -> begin match unauth r1_auth p with
        | p, `right (`left _, l2_auth, a2, r2_auth) -> 
          p, make_node red (make_node black l_auth a l1_auth) a1 (make_node black l2_auth a2 r2_auth)
        | p, sr1 -> p, t_auth
      end
    end
    | p, _ -> p, t_auth
  end
  | p, t -> p, t_auth

  let insert x v t_auth p =
    let leaf_auth = make_node black (empty_tree ()) (x, `right v) (empty_tree ()) in
    let rec ins t_auth p =
      match unauth t_auth p with
      | p, `left _ -> p, leaf_auth
      | p, `right (c, l_auth, (y, `right _), r_auth) ->
        if x = y then p, t_auth
        else if x < y then p, make_node red leaf_auth (x, `left "") t_auth
        else if x > y then p, make_node red t_auth (y, `left "") leaf_auth
        else failwith "false"
      | p, `right (c, l_auth, (y, `left _), r_auth) ->
        if x = y then p, t_auth
        else if x < y then let p, l_ins = ins l_auth p in
          balanceL (make_node c l_ins (y, `left "") r_auth) p
        else if x > y then let p, r_ins = ins r_auth p in
          balanceR (make_node c l_auth (y, `left "") r_ins) p
        else failwith "false"
    in
    let p, t_ins = ins t_auth p in
    blacken t_ins p

  let run c = c []
end

module DirRedblackProverPolyIo = struct
  type 'a auth = 'a * string
  type 'a option_t = [`left of string | `right of 'a]
  type color = string option_t (* left is red, right is black *)
  type value_option = string option_t
  type tree = (color * tree auth * (int * value_option) * tree auth) option_t
  type tree_auth = tree auth

  let output = ref (open_out_bin "/dev/null")

  let set_output s = 
    close_out !output; output := open_out_bin s
  let close_output () = close_out !output; output := open_out_bin "/dev/null"

  let prepare_unauth o = match o with
    | `left _ -> `left ""
    | `right (c, (l, ls), kv, (r, rs)) -> `right (c, ls, kv, rs)
  let ser o = Marshal.to_string (prepare_unauth o) marshal_flags
  let auth o = o, ser o |> hash
  let unauth (t, ts) = Marshal.to_channel !output (prepare_unauth t) marshal_flags; t
  let red = `left ""
  let black = `right ""
  let none_v = `left ""
  let some_v v = `right v

  let empty_tree () = auth (`left "")
  let make_node c l kv r = auth (`right (c, l, kv, r))

  let blacken t_auth =
    match unauth t_auth with
    | `left _ -> empty_tree ()
    | `right (_, l, x, r) -> make_node black l x r

  let balanceL t_auth = match unauth t_auth with
  | `right (`right _, l_auth, a, r_auth) -> begin match unauth l_auth with
    | `right (`left _, l1_auth, a1, r1_auth) -> begin match unauth l1_auth with
      | `right (`left _, l2_auth, a2, r2_auth) -> 
        make_node red (make_node black l2_auth a2 r2_auth) a1 (make_node black r1_auth a r_auth)
      | _ -> begin match unauth r1_auth with
        | `right (`left _, l2_auth, a2, r2_auth) -> 
          make_node red (make_node black l1_auth a1 l2_auth) a2 (make_node black r2_auth a r_auth)
        | sr1 -> t_auth
      end
    end
    | _ -> t_auth
  end
  | _ -> t_auth

  let balanceR t_auth = match unauth t_auth with
  | `right (`right _, l_auth, a, r_auth) -> begin match unauth r_auth with
    | `right (`left _, l1_auth, a1, r1_auth) -> begin match unauth l1_auth with
      | `right (`left _, l2_auth, a2, r2_auth) -> 
        make_node red (make_node black l_auth a l2_auth) a2 (make_node black r2_auth a1 r1_auth)
      | _ -> begin match unauth r1_auth with
        | `right (`left _, l2_auth, a2, r2_auth) -> 
          make_node red (make_node black l_auth a l1_auth) a1 (make_node black l2_auth a2 r2_auth)
        | sr1 -> t_auth
      end
    end
    | _ -> t_auth
  end
  | t -> t_auth

  let insert x v t_auth =
    let leaf_auth = make_node black (empty_tree ()) (x, `right v) (empty_tree ()) in
    let rec ins t_auth =
      match unauth t_auth with
      | `left _ -> leaf_auth
      | `right (c, l_auth, (y, `right _), r_auth) ->
        if x = y then t_auth
        else if x < y then make_node red leaf_auth (x, `left "") t_auth
        else if x > y then make_node red t_auth (y, `left "") leaf_auth
        else failwith "false"
      | `right (c, l_auth, (y, `left _), r_auth) ->
        if x = y then t_auth
        else if x < y then let l_ins = ins l_auth in
          balanceL (make_node c l_ins (y, `left "") r_auth)
        else if x > y then let r_ins = ins r_auth in
          balanceR (make_node c l_auth (y, `left "") r_ins)
        else failwith "false"
    in
    let t_ins = ins t_auth in
    blacken t_ins

  let run c = c
end

module DirRedblackProverPolyBaseSer = struct
  type 'a auth = 'a * string
  type 'a option_t = [`left of string | `right of 'a]
  type color = string option_t (* left is red, right is black *)
  type value_option = string option_t
  type tree = (color * tree auth * (int * value_option) * tree auth) option_t
  type tree_auth = tree auth

  module Authenticatable = struct
    include Authenticatable_base.Prover
    let auth (a, h) = h
  end
  open Authenticatable

  let option_evi (a_evi : 'a evidence) :'a option_t evidence =
    (sum string a_evi)
  let value_evi : value_option evidence = option_evi string
  let tree_evi : tree evidence =
    option_evi (quad value_evi auth (pair int value_evi) auth)

  let ser o = tree_evi o
  let auth o = o, ser o |> hash
  let unauth (t, ts) p = ser t :: p, t
  let red = `left ""
  let black = `right ""
  let none_v = `left ""
  let some_v v = `right v

  let empty_tree () = auth (`left "")
  let make_node c l kv r = auth (`right (c, l, kv, r))

  let blacken t_auth p =
    match unauth t_auth p with
    | p, `left _ -> p, empty_tree ()
    | p, `right (_, l, x, r) -> p, make_node black l x r

  let balanceL t_auth p = match unauth t_auth p with
  | p, `right (`right _, l_auth, a, r_auth) -> begin match unauth l_auth p with
    | p, `right (`left _, l1_auth, a1, r1_auth) -> begin match unauth l1_auth p with
      | p, `right (`left _, l2_auth, a2, r2_auth) -> 
        p, make_node red (make_node black l2_auth a2 r2_auth) a1 (make_node black r1_auth a r_auth)
      | p, _ -> begin match unauth r1_auth p with
        | p, `right (`left _, l2_auth, a2, r2_auth) -> 
          p, make_node red (make_node black l1_auth a1 l2_auth) a2 (make_node black r2_auth a r_auth)
        | p, sr1 -> p, t_auth
      end
    end
    | p, _ -> p, t_auth
  end
  | p, _ -> p, t_auth

  let balanceR t_auth p = match unauth t_auth p with
  | p, `right (`right _, l_auth, a, r_auth) -> begin match unauth r_auth p with
    | p, `right (`left _, l1_auth, a1, r1_auth) -> begin match unauth l1_auth p with
      | p, `right (`left _, l2_auth, a2, r2_auth) -> 
        p, make_node red (make_node black l_auth a l2_auth) a2 (make_node black r2_auth a1 r1_auth)
      | p, _ -> begin match unauth r1_auth p with
        | p, `right (`left _, l2_auth, a2, r2_auth) -> 
          p, make_node red (make_node black l_auth a l1_auth) a1 (make_node black l2_auth a2 r2_auth)
        | p, sr1 -> p, t_auth
      end
    end
    | p, _ -> p, t_auth
  end
  | p, t -> p, t_auth

  let insert x v t_auth p =
    let leaf_auth = make_node black (empty_tree ()) (x, `right v) (empty_tree ()) in
    let rec ins t_auth p =
      match unauth t_auth p with
      | p, `left _ -> p, leaf_auth
      | p, `right (c, l_auth, (y, `right _), r_auth) ->
        if x = y then p, t_auth
        else if x < y then p, make_node red leaf_auth (x, `left "") t_auth
        else if x > y then p, make_node red t_auth (y, `left "") leaf_auth
        else failwith "false"
      | p, `right (c, l_auth, (y, `left _), r_auth) ->
        if x = y then p, t_auth
        else if x < y then let p, l_ins = ins l_auth p in
          balanceL (make_node c l_ins (y, `left "") r_auth) p
        else if x > y then let p, r_ins = ins r_auth p in
          balanceR (make_node c l_auth (y, `left "") r_ins) p
        else failwith "false"
    in
    let p, t_ins = ins t_auth p in
    blacken t_ins p

  let run c = c []
end

module DirRedblackProverPolyMarSer = struct
  type 'a auth = 'a * string
  type 'a option_t = [`left of string | `right of 'a]
  type color = string option_t (* left is red, right is black *)
  type value_option = string option_t
  type tree = (color * tree auth * (int * value_option) * tree auth) option_t
  type tree_auth = tree auth

  module Authenticatable = struct
    include Authenticatable_marshal.Prover
    let auth =
      let prepare (a, h) = h 
      and serialize y = Marshal.to_string y marshal_flags
      in
      T {prepare; serialize }
      
  end
  open Authenticatable

  let option_evi (a_evi : 'a evidence) :'a option_t evidence =
    (sum string a_evi)
  let value_evi : value_option evidence = option_evi string
  let tree_evi : tree evidence =
    option_evi (quad value_evi auth (pair int value_evi) auth)

  let ser o = 
    match tree_evi with
    | T evi -> evi.serialize (evi.prepare o)
  let auth o = o, ser o |> hash
  let unauth (t, ts) p = ser t :: p, t
  let red = `left ""
  let black = `right ""
  let none_v = `left ""
  let some_v v = `right v

  let empty_tree () = auth (`left "")
  let make_node c l kv r = auth (`right (c, l, kv, r))

  let blacken t_auth p =
    match unauth t_auth p with
    | p, `left _ -> p, empty_tree ()
    | p, `right (_, l, x, r) -> p, make_node black l x r

  let balanceL t_auth p = match unauth t_auth p with
  | p, `right (`right _, l_auth, a, r_auth) -> begin match unauth l_auth p with
    | p, `right (`left _, l1_auth, a1, r1_auth) -> begin match unauth l1_auth p with
      | p, `right (`left _, l2_auth, a2, r2_auth) -> 
        p, make_node red (make_node black l2_auth a2 r2_auth) a1 (make_node black r1_auth a r_auth)
      | p, _ -> begin match unauth r1_auth p with
        | p, `right (`left _, l2_auth, a2, r2_auth) -> 
          p, make_node red (make_node black l1_auth a1 l2_auth) a2 (make_node black r2_auth a r_auth)
        | p, sr1 -> p, t_auth
      end
    end
    | p, _ -> p, t_auth
  end
  | p, _ -> p, t_auth

  let balanceR t_auth p = match unauth t_auth p with
  | p, `right (`right _, l_auth, a, r_auth) -> begin match unauth r_auth p with
    | p, `right (`left _, l1_auth, a1, r1_auth) -> begin match unauth l1_auth p with
      | p, `right (`left _, l2_auth, a2, r2_auth) -> 
        p, make_node red (make_node black l_auth a l2_auth) a2 (make_node black r2_auth a1 r1_auth)
      | p, _ -> begin match unauth r1_auth p with
        | p, `right (`left _, l2_auth, a2, r2_auth) -> 
          p, make_node red (make_node black l_auth a l1_auth) a1 (make_node black l2_auth a2 r2_auth)
        | p, sr1 -> p, t_auth
      end
    end
    | p, _ -> p, t_auth
  end
  | p, t -> p, t_auth

  let insert x v t_auth p =
    let leaf_auth = make_node black (empty_tree ()) (x, `right v) (empty_tree ()) in
    let rec ins t_auth p =
      match unauth t_auth p with
      | p, `left _ -> p, leaf_auth
      | p, `right (c, l_auth, (y, `right _), r_auth) ->
        if x = y then p, t_auth
        else if x < y then p, make_node red leaf_auth (x, `left "") t_auth
        else if x > y then p, make_node red t_auth (y, `left "") leaf_auth
        else failwith "false"
      | p, `right (c, l_auth, (y, `left _), r_auth) ->
        if x = y then p, t_auth
        else if x < y then let p, l_ins = ins l_auth p in
          balanceL (make_node c l_ins (y, `left "") r_auth) p
        else if x > y then let p, r_ins = ins r_auth p in
          balanceR (make_node c l_auth (y, `left "") r_ins) p
        else failwith "false"
    in
    let p, t_ins = ins t_auth p in
    blacken t_ins p

  let run c = c []
end

module DirRedblackProverPolyMarSerIo = struct
  type 'a auth = 'a * string
  type 'a option_t = [`left of string | `right of 'a]
  type color = string option_t (* left is red, right is black *)
  type value_option = string option_t
  type tree = (color * tree auth * (int * value_option) * tree auth) option_t
  type tree_auth = tree auth

  let output = ref (open_out_bin "/dev/null")

  let set_output s = 
    close_out !output; output := open_out_bin s
  let close_output () = close_out !output; output := open_out_bin "/dev/null"

  module Authenticatable = struct
    include Authenticatable_marshal.Prover
    let auth =
      let prepare (a, h) = h 
      and serialize y = Marshal.to_string y marshal_flags
      in
      T {prepare; serialize }
      
  end
  open Authenticatable

  let option_evi (a_evi : 'a evidence) :'a option_t evidence =
    (sum string a_evi)
  let value_evi : value_option evidence = option_evi string
  let tree_evi : tree evidence =
    option_evi (quad value_evi auth (pair int value_evi) auth)

  let auth o = 
    match tree_evi with
    | T evi -> (o, hash (evi.serialize (evi.prepare o)))
  let unauth (t, ts) =
    match tree_evi with
    | T evi -> 
      Marshal.to_channel !output (evi.prepare t) marshal_flags; t
  let red = `left ""
  let black = `right ""
  let none_v = `left ""
  let some_v v = `right v

  let empty_tree () = auth (`left "")
  let make_node c l kv r = auth (`right (c, l, kv, r))

  let blacken t_auth =
    match unauth t_auth with
    | `left _ -> empty_tree ()
    | `right (_, l, x, r) -> make_node black l x r

  let balanceL t_auth = match unauth t_auth with
  | `right (`right _, l_auth, a, r_auth) -> begin match unauth l_auth with
    | `right (`left _, l1_auth, a1, r1_auth) -> begin match unauth l1_auth with
      | `right (`left _, l2_auth, a2, r2_auth) -> 
        make_node red (make_node black l2_auth a2 r2_auth) a1 (make_node black r1_auth a r_auth)
      | _ -> begin match unauth r1_auth with
        | `right (`left _, l2_auth, a2, r2_auth) -> 
          make_node red (make_node black l1_auth a1 l2_auth) a2 (make_node black r2_auth a r_auth)
        | sr1 -> t_auth
      end
    end
    | _ -> t_auth
  end
  | _ -> t_auth

  let balanceR t_auth = match unauth t_auth with
  | `right (`right _, l_auth, a, r_auth) -> begin match unauth r_auth with
    | `right (`left _, l1_auth, a1, r1_auth) -> begin match unauth l1_auth with
      | `right (`left _, l2_auth, a2, r2_auth) -> 
        make_node red (make_node black l_auth a l2_auth) a2 (make_node black r2_auth a1 r1_auth)
      | _ -> begin match unauth r1_auth with
        | `right (`left _, l2_auth, a2, r2_auth) -> 
          make_node red (make_node black l_auth a l1_auth) a1 (make_node black l2_auth a2 r2_auth)
        | sr1 -> t_auth
      end
    end
    | _ -> t_auth
  end
  | t -> t_auth

  let insert x v t_auth =
    let leaf_auth = make_node black (empty_tree ()) (x, `right v) (empty_tree ()) in
    let rec ins t_auth =
      match unauth t_auth with
      | `left _ -> leaf_auth
      | `right (c, l_auth, (y, `right _), r_auth) ->
        if x = y then t_auth
        else if x < y then make_node red leaf_auth (x, `left "") t_auth
        else if x > y then make_node red t_auth (y, `left "") leaf_auth
        else failwith "false"
      | `right (c, l_auth, (y, `left _), r_auth) ->
        if x = y then t_auth
        else if x < y then let l_ins = ins l_auth in
          balanceL (make_node c l_ins (y, `left "") r_auth)
        else if x > y then let r_ins = ins r_auth in
          balanceR (make_node c l_auth (y, `left "") r_ins)
        else failwith "false"
    in
    let t_ins = ins t_auth in
    blacken t_ins
end

module NonfunRedblackProverMar = struct
  type 'a option_t = [`left of string | `right of 'a]
  type color = string option_t (* left is red, right is black *)
  type value_option = string option_t
  type tree = (color * tree Prover_marshal.auth * (int * value_option) * tree Prover_marshal.auth) option_t
  type tree_auth = tree Prover_marshal.auth

  let option_evi (a_evi : 'a Prover_marshal.Authenticatable.evidence) :'a option_t Prover_marshal.Authenticatable.evidence =
    Prover_marshal.Authenticatable.(sum string a_evi)
  let value_evi : value_option Prover_marshal.Authenticatable.evidence = option_evi Prover_marshal.Authenticatable.string
  let tree_evi : tree Prover_marshal.Authenticatable.evidence =
    option_evi Prover_marshal.Authenticatable.(quad value_evi auth (pair int value_evi) auth)

  let empty_tree () = Prover_marshal.auth tree_evi (`left "")
  let make_node c l kv r = Prover_marshal.auth tree_evi (`right (c, l, kv, r))
  let auth t = Prover_marshal.auth tree_evi t
  let red = `left ""
  let black = `right ""
  let none_v = `left ""
  let some_v v = `right v

  let blacken t =
    Prover_marshal.bind (Prover_marshal.unauth tree_evi t)
      (fun un_t ->
        match un_t with
        | `left _ -> Prover_marshal.return t
        | `right (_, l, x, r) -> make_node black l x r |> Prover_marshal.return)

  let balanceL t =
    Prover_marshal.bind (Prover_marshal.unauth tree_evi t)
      (fun un_t ->
        match un_t with
        | `right (`right _, l, a, r) ->
          Prover_marshal.bind (Prover_marshal.unauth tree_evi l)
            (fun un_l ->
              match un_l with
              | `right (`left _, l1, a1, r1) ->
                Prover_marshal.bind (Prover_marshal.unauth tree_evi l1)
                  (fun un_l1 ->
                    match un_l1 with
                    | `right (`left _, l2, a2, r2) ->
                      make_node red (make_node black l2 a2 r2) a1 (make_node black r1 a r) |> Prover_marshal.return
                    | _ ->
                      Prover_marshal.bind (Prover_marshal.unauth tree_evi r1)
                        (fun un_r1 ->
                          match un_r1 with
                          | `right (`left _, l2, a2, r2) ->
                            make_node red (make_node black l1 a1 l2) a2 (make_node black r2 a r) |> Prover_marshal.return
                          | _ -> Prover_marshal.return t
                          )
                    )
              | _ -> Prover_marshal.return t
              )
        | _ -> Prover_marshal.return t
        )

  let balanceR t =
    Prover_marshal.bind (Prover_marshal.unauth tree_evi t)
      (fun un_t ->
        match un_t with
        | `right (`right _, l, a, r) ->
          Prover_marshal.bind (Prover_marshal.unauth tree_evi r)
            (fun un_r ->
              match un_r with
              | `right (`left _, l1, a1, r1) ->
                Prover_marshal.bind (Prover_marshal.unauth tree_evi l1)
                  (fun un_l1 ->
                    match un_l1 with
                    | `right (`left _, l2, a2, r2) ->
                      make_node red (make_node black l a l2) a2 (make_node black r2 a1 r1) |> Prover_marshal.return
                    | _ ->
                      Prover_marshal.bind (Prover_marshal.unauth tree_evi r1)
                        (fun un_r1 ->
                          match un_r1 with
                          | `right (`left _, l2, a2, r2) ->
                            make_node red (make_node black l a l1) a1 (make_node black l2 a2 r2) |> Prover_marshal.return
                          | _ -> Prover_marshal.return t
                          )
                    )
              | _ -> Prover_marshal.return t
              )
        | _ -> Prover_marshal.return t
        )
  
  let insert x v t =
    let leaf = make_node black (empty_tree ()) (x, some_v v) (empty_tree ()) in
    let rec ins t =
      Prover_marshal.bind (Prover_marshal.unauth tree_evi t)
        (fun un_t ->
          match un_t with
          | `left _ -> Prover_marshal.return leaf
          | `right (c, l, (y, `right _), r) ->
            if x = y then Prover_marshal.return t
            else if x < y then make_node red leaf (x, none_v) t |> Prover_marshal.return 
            else if x > y then make_node red t (y, none_v) leaf |> Prover_marshal.return
            else failwith "false"
          | `right (c, l, (y, `left _), r) ->
            if x = y then Prover_marshal.return t
            else if x < y then
              Prover_marshal.bind (ins l)
                (fun l_ins -> make_node c l_ins (y, none_v) r |> balanceL)
            else if x > y then
              Prover_marshal.bind (ins r)
                (fun r_ins -> make_node c l (y, none_v) r_ins |> balanceR)
            else failwith "false"
          )
    in
    Prover_marshal.bind (ins t) blacken
end

module NonfunRedblackProverIo = struct
  type 'a option_t = [`left of string | `right of 'a]
  type color = string option_t (* left is red, right is black *)
  type value_option = string option_t
  type tree = (color * tree Prover_io.auth * (int * value_option) * tree Prover_io.auth) option_t
  type tree_auth = tree Prover_io.auth

  let option_evi (a_evi : 'a Prover_io.Authenticatable.evidence) :'a option_t Prover_io.Authenticatable.evidence =
    Prover_io.Authenticatable.(sum string a_evi)
  let value_evi : value_option Prover_io.Authenticatable.evidence = option_evi Prover_io.Authenticatable.string
  let tree_evi : tree Prover_io.Authenticatable.evidence =
    option_evi Prover_io.Authenticatable.(quad value_evi auth (pair int value_evi) auth)

  let empty_tree () = Prover_io.auth tree_evi (`left "")
  let make_node c l kv r = Prover_io.auth tree_evi (`right (c, l, kv, r))
  let auth t = Prover_io.auth tree_evi t
  let red = `left ""
  let black = `right ""
  let none_v = `left ""
  let some_v v = `right v

  let blacken t =
    Prover_io.bind (Prover_io.unauth tree_evi t)
      (fun un_t ->
        match un_t with
        | `left _ -> Prover_io.return t
        | `right (_, l, x, r) -> make_node black l x r |> Prover_io.return)

  let balanceL t =
      Prover_io.bind (Prover_io.unauth tree_evi t)
        (fun un_t ->
          match un_t with
          | `right (`right _, l, a, r) ->
            Prover_io.bind (Prover_io.unauth tree_evi l)
              (fun un_l ->
                match un_l with
                | `right (`left _, l1, a1, r1) ->
                  Prover_io.bind (Prover_io.unauth tree_evi l1)
                    (fun un_l1 ->
                      match un_l1 with
                      | `right (`left _, l2, a2, r2) ->
                        make_node red (make_node black l2 a2 r2) a1 (make_node black r1 a r) |> Prover_io.return
                      | _ ->
                        Prover_io.bind (Prover_io.unauth tree_evi r1)
                          (fun un_r1 ->
                            match un_r1 with
                            | `right (`left _, l2, a2, r2) ->
                              make_node red (make_node black l1 a1 l2) a2 (make_node black r2 a r) |> Prover_io.return
                            | _ -> Prover_io.return t
                            )
                      )
                | _ -> Prover_io.return t
                )
          | _ -> Prover_io.return t
          )

  let balanceR t =
    Prover_io.bind (Prover_io.unauth tree_evi t)
      (fun un_t ->
        match un_t with
        | `right (`right _, l, a, r) ->
          Prover_io.bind (Prover_io.unauth tree_evi r)
            (fun un_r ->
              match un_r with
              | `right (`left _, l1, a1, r1) ->
                Prover_io.bind (Prover_io.unauth tree_evi l1)
                  (fun un_l1 ->
                    match un_l1 with
                    | `right (`left _, l2, a2, r2) ->
                      make_node red (make_node black l a l2) a2 (make_node black r2 a1 r1) |> Prover_io.return
                    | _ ->
                      Prover_io.bind (Prover_io.unauth tree_evi r1)
                        (fun un_r1 ->
                          match un_r1 with
                          | `right (`left _, l2, a2, r2) ->
                            make_node red (make_node black l a l1) a1 (make_node black l2 a2 r2) |> Prover_io.return
                          | _ -> Prover_io.return t
                          )
                    )
              | _ -> Prover_io.return t
              )
        | _ -> Prover_io.return t
        )
  
  let insert x v t =
    let leaf = make_node black (empty_tree ()) (x, some_v v) (empty_tree ()) in
    let rec ins t =
      Prover_io.bind (Prover_io.unauth tree_evi t)
        (fun un_t ->
          match un_t with
          | `left _ -> Prover_io.return leaf
          | `right (c, l, (y, `right _), r) ->
            if x = y then Prover_io.return t
            else if x < y then make_node red leaf (x, none_v) t |> Prover_io.return 
            else if x > y then make_node red t (y, none_v) leaf |> Prover_io.return
            else failwith "false"
          | `right (c, l, (y, `left _), r) ->
            if x = y then Prover_io.return t
            else if x < y then
              Prover_io.bind (ins l)
                (fun l_ins -> make_node c l_ins (y, none_v) r |> balanceL)
            else if x > y then
              Prover_io.bind (ins r)
                (fun r_ins -> make_node c l (y, none_v) r_ins |> balanceR)
            else failwith "false"
          )
    in
    Prover_io.bind (ins t) blacken
end

module DirRedblackVerifier = struct
  type 'a auth = string
  type color = Red | Black
  type value_option = Non | Som of string
  type tree = Tip | Bin of (color * tree auth * (int * value_option) * tree auth)
  type tree_hash = Tipp | Binp of (color * string * (int * value_option) * string)
  type tree_auth = tree auth

  let ser o = 
    (* tree_evi.serialize o *)
    Marshal.to_string o marshal_flags
  let deser s = 
    (* match tree_evi.deserialize s with
    | None -> failwith "proof failure3"
    | Some a -> a *)
    match Marshal.from_string s 0 with
    | Tipp -> Tip
    | Binp (_ as b) -> Bin b
  let auth o = ser o |> hash
  let unauth h ps = match ps with
    | [] -> failwith "proof failure1"
    | p::ps when hash p = h -> ps, deser p
    | _ -> failwith "proof failure2"
  let red = Red
  let black = Black
  let none_v = Non
  let some_v v = Som v

  let empty_tree () = auth (Tip)
  let make_node c l kv r = auth (Bin (c, l, kv, r))

  let blacken t_auth p =
    match unauth t_auth p with
    | p, Tip -> p, empty_tree ()
    | p, Bin (_, l, x, r) -> p, make_node black l x r

  let balanceL t_auth p = match unauth t_auth p with
  | p, Bin (Black, l_auth, a, r_auth) -> begin match unauth l_auth p with
    | p, Bin (Red, l1_auth, a1, r1_auth) -> begin match unauth l1_auth p with
      | p, Bin (Red, l2_auth, a2, r2_auth) -> 
        p, make_node red (make_node black l2_auth a2 r2_auth) a1 (make_node black r1_auth a r_auth)
      | p, _ -> begin match unauth r1_auth p with
        | p, Bin (Red, l2_auth, a2, r2_auth) -> 
          p, make_node red (make_node black l1_auth a1 l2_auth) a2 (make_node black r2_auth a r_auth)
        | p, sr1 -> p, t_auth
      end
    end
    | p, _ -> p, t_auth
  end
  | p, _ -> p, t_auth

  let balanceR t_auth p = match unauth t_auth p with
  | p, Bin (Black, l_auth, a, r_auth) -> begin match unauth r_auth p with
    | p, Bin (Red, l1_auth, a1, r1_auth) -> begin match unauth l1_auth p with
      | p, Bin (Red, l2_auth, a2, r2_auth) -> 
        p, make_node red (make_node black l_auth a l2_auth) a2 (make_node black r2_auth a1 r1_auth)
      | p, _ -> begin match unauth r1_auth p with
        | p, Bin (Red, l2_auth, a2, r2_auth) -> 
          p, make_node red (make_node black l_auth a l1_auth) a1 (make_node black l2_auth a2 r2_auth)
        | p, sr1 -> p, t_auth
      end
    end
    | p, _ -> p, t_auth
  end
  | p, t -> p, t_auth

  let insert x v t_auth p =
    let leaf_auth = make_node black (empty_tree ()) (x, Som v) (empty_tree ()) in
    let rec ins t_auth p =
      match unauth t_auth p with
      | p, Tip -> p, leaf_auth
      | p, Bin (c, l_auth, (y, Som _), r_auth) ->
        if x = y then p, t_auth
        else if x < y then p, make_node red leaf_auth (x, Non) t_auth
        else if x > y then p, make_node red t_auth (y, Non) leaf_auth
        else failwith "false"
      | p, Bin (c, l_auth, (y, Non ), r_auth) ->
        if x = y then p, t_auth
        else if x < y then let p, l_ins = ins l_auth p in
          balanceL (make_node c l_ins (y, Non) r_auth) p
        else if x > y then let p, r_ins = ins r_auth p in
          balanceR (make_node c l_auth (y, Non) r_ins) p
        else failwith "false"
    in
    let p, t_ins = ins t_auth p in
    blacken t_ins p
end

module DirRedblackVerifierIo = struct
  type 'a auth = string
  type color = Red | Black
  type value_option = Non | Som of string
  type tree = Tip | Bin of (color * tree auth * (int * value_option) * tree auth)
  type tree_hash = Tipp | Binp of (color * string * (int * value_option) * string)
  type tree_auth = tree auth

  let input = ref (open_in_bin "/dev/null")

  let set_input s = 
    close_in !input; input := open_in_bin s
  let close_input () = close_in !input; input := open_in_bin "/dev/null"

  let ser o = 
    Marshal.to_string o marshal_flags
  let deser s = 
    match Marshal.from_string s 0 with
    | Tipp -> Tip
    | Binp (_ as b) -> Bin b
  let auth o = ser o |> hash
  let unauth h = 
    let p = from_channel_with_string !input in
    if hash p = h then deser p
    else failwith "Proof failure"

  let red = Red
  let black = Black
  let none_v = Non
  let some_v v = Som v

  let empty_tree () = auth (Tip)
  let make_node c l kv r = auth (Bin (c, l, kv, r))

  let blacken t_auth =
    match unauth t_auth with
    | Tip -> empty_tree ()
    | Bin (_, l, x, r) -> make_node black l x r

  let balanceL t_auth = match unauth t_auth with
  | Bin (Black, l_auth, a, r_auth) -> begin match unauth l_auth with
    | Bin (Red, l1_auth, a1, r1_auth) -> begin match unauth l1_auth with
      | Bin (Red, l2_auth, a2, r2_auth) -> 
        make_node red (make_node black l2_auth a2 r2_auth) a1 (make_node black r1_auth a r_auth)
      | _ -> begin match unauth r1_auth with
        | Bin (Red, l2_auth, a2, r2_auth) -> 
          make_node red (make_node black l1_auth a1 l2_auth) a2 (make_node black r2_auth a r_auth)
        | sr1 -> t_auth
      end
    end
    | _ -> t_auth
  end
  | _ -> t_auth

  let balanceR t_auth = match unauth t_auth with
  | Bin (Black, l_auth, a, r_auth) -> begin match unauth r_auth with
    | Bin (Red, l1_auth, a1, r1_auth) -> begin match unauth l1_auth with
      | Bin (Red, l2_auth, a2, r2_auth) -> 
        make_node red (make_node black l_auth a l2_auth) a2 (make_node black r2_auth a1 r1_auth)
      | _ -> begin match unauth r1_auth with
        | Bin (Red, l2_auth, a2, r2_auth) -> 
          make_node red (make_node black l_auth a l1_auth) a1 (make_node black l2_auth a2 r2_auth)
        | sr1 -> t_auth
      end
    end
    | _ -> t_auth
  end
  | t -> t_auth

  let insert x v t_auth =
    let leaf_auth = make_node black (empty_tree ()) (x, Som v) (empty_tree ()) in
    let rec ins t_auth =
      match unauth t_auth with
      | Tip -> leaf_auth
      | Bin (c, l_auth, (y, Som _), r_auth) ->
        if x = y then t_auth
        else if x < y then make_node red leaf_auth (x, Non) t_auth
        else if x > y then make_node red t_auth (y, Non) leaf_auth
        else failwith "false"
      | Bin (c, l_auth, (y, Non ), r_auth) ->
        if x = y then t_auth
        else if x < y then let l_ins = ins l_auth in
          balanceL (make_node c l_ins (y, Non) r_auth)
        else if x > y then let r_ins = ins r_auth in
          balanceR (make_node c l_auth (y, Non) r_ins)
        else failwith "false"
    in
    let t_ins = ins t_auth in
    blacken t_ins
end

module DirRedblackVerifierPoly = struct
  type 'a auth = string
  type 'a option_t = [`left of string | `right of 'a]
  type color = string option_t (* left is red, right is black *)
  type value_option = string option_t
  type tree = (color * tree auth * (int * value_option) * tree auth) option_t
  type tree_auth = tree auth

  let ser o = Marshal.to_string o marshal_flags
  let deser s = Marshal.from_string s 0
  let auth o = ser o |> hash
  let unauth h ps = match ps with
    | [] -> failwith "proof failure1"
    | p::ps when hash p = h -> ps, deser p
    | _ -> failwith "proof failure2"
  let red = `left ""
  let black = `right ""
  let none_v = `left ""
  let some_v v = `right v

  let empty_tree () = auth (`left "")
  let make_node c l kv r = auth (`right (c, l, kv, r))

  let blacken t_auth p =
    match unauth t_auth p with
    | p, `left _ -> p, empty_tree ()
    | p, `right (_, l, x, r) -> p, make_node black l x r

  let balanceL t_auth p = match unauth t_auth p with
  | p, `right (`right _, l_auth, a, r_auth) -> begin match unauth l_auth p with
    | p, `right (`left _, l1_auth, a1, r1_auth) -> begin match unauth l1_auth p with
      | p, `right (`left _, l2_auth, a2, r2_auth) -> 
        p, make_node red (make_node black l2_auth a2 r2_auth) a1 (make_node black r1_auth a r_auth)
      | p, _ -> begin match unauth r1_auth p with
        | p, `right (`left _, l2_auth, a2, r2_auth) -> 
          p, make_node red (make_node black l1_auth a1 l2_auth) a2 (make_node black r2_auth a r_auth)
        | p, sr1 -> p, t_auth
      end
    end
    | p, _ -> p, t_auth
  end
  | p, _ -> p, t_auth

  let balanceR t_auth p = match unauth t_auth p with
  | p, `right (`right _, l_auth, a, r_auth) -> begin match unauth r_auth p with
    | p, `right (`left _, l1_auth, a1, r1_auth) -> begin match unauth l1_auth p with
      | p, `right (`left _, l2_auth, a2, r2_auth) -> 
        p, make_node red (make_node black l_auth a l2_auth) a2 (make_node black r2_auth a1 r1_auth)
      | p, _ -> begin match unauth r1_auth p with
        | p, `right (`left _, l2_auth, a2, r2_auth) -> 
          p, make_node red (make_node black l_auth a l1_auth) a1 (make_node black l2_auth a2 r2_auth)
        | p, sr1 -> p, t_auth
      end
    end
    | p, _ -> p, t_auth
  end
  | p, t -> p, t_auth

  let insert x v t_auth p =
    let leaf_auth = make_node black (empty_tree ()) (x, `right v) (empty_tree ()) in
    let rec ins t_auth p =
      match unauth t_auth p with
      | p, `left _ -> p, leaf_auth
      | p, `right (c, l_auth, (y, `right _), r_auth) ->
        if x = y then p, t_auth
        else if x < y then p, make_node red leaf_auth (x, `left "") t_auth
        else if x > y then p, make_node red t_auth (y, `left "") leaf_auth
        else failwith "false"
      | p, `right (c, l_auth, (y, `left _), r_auth) ->
        if x = y then p, t_auth
        else if x < y then let p, l_ins = ins l_auth p in
          balanceL (make_node c l_ins (y, `left "") r_auth) p
        else if x > y then let p, r_ins = ins r_auth p in
          balanceR (make_node c l_auth (y, `left "") r_ins) p
        else failwith "false"
    in
    let p, t_ins = ins t_auth p in
    blacken t_ins p
end

module DirRedblackVerifierPolyIo = struct
  type 'a auth = string
  type 'a option_t = [`left of string | `right of 'a]
  type color = string option_t (* left is red, right is black *)
  type value_option = string option_t
  type tree = (color * tree auth * (int * value_option) * tree auth) option_t
  type tree_auth = tree auth

  let input = ref (open_in_bin "/dev/null")

  let set_input s = 
    close_in !input; input := open_in_bin s
  let close_input () = close_in !input; input := open_in_bin "/dev/null"

  let ser o = Marshal.to_string o marshal_flags
  let deser s = Marshal.from_string s 0
  let auth o = ser o |> hash
  let unauth h = 
    let p = from_channel_with_string !input in
    if hash p = h then deser p
    else failwith "Proof failure"

  let red = `left ""
  let black = `right ""
  let none_v = `left ""
  let some_v v = `right v

  let empty_tree () = auth (`left "")
  let make_node c l kv r = auth (`right (c, l, kv, r))

  let blacken t_auth =
    match unauth t_auth with
    | `left _ -> empty_tree ()
    | `right (_, l, x, r) -> make_node black l x r

  let balanceL t_auth = match unauth t_auth with
  | `right (`right _, l_auth, a, r_auth) -> begin match unauth l_auth with
    | `right (`left _, l1_auth, a1, r1_auth) -> begin match unauth l1_auth with
      | `right (`left _, l2_auth, a2, r2_auth) -> 
        make_node red (make_node black l2_auth a2 r2_auth) a1 (make_node black r1_auth a r_auth)
      | _ -> begin match unauth r1_auth with
        | `right (`left _, l2_auth, a2, r2_auth) -> 
          make_node red (make_node black l1_auth a1 l2_auth) a2 (make_node black r2_auth a r_auth)
        | sr1 -> t_auth
      end
    end
    | _ -> t_auth
  end
  | _ -> t_auth

  let balanceR t_auth = match unauth t_auth with
  | `right (`right _, l_auth, a, r_auth) -> begin match unauth r_auth with
    | `right (`left _, l1_auth, a1, r1_auth) -> begin match unauth l1_auth with
      | `right (`left _, l2_auth, a2, r2_auth) -> 
        make_node red (make_node black l_auth a l2_auth) a2 (make_node black r2_auth a1 r1_auth)
      | _ -> begin match unauth r1_auth with
        | `right (`left _, l2_auth, a2, r2_auth) -> 
          make_node red (make_node black l_auth a l1_auth) a1 (make_node black l2_auth a2 r2_auth)
        | sr1 -> t_auth
      end
    end
    | _ -> t_auth
  end
  | t -> t_auth

  let insert x v t_auth =
    let leaf_auth = make_node black (empty_tree ()) (x, `right v) (empty_tree ()) in
    let rec ins t_auth =
      match unauth t_auth with
      | `left _ -> leaf_auth
      | `right (c, l_auth, (y, `right _), r_auth) ->
        if x = y then t_auth
        else if x < y then make_node red leaf_auth (x, `left "") t_auth
        else if x > y then make_node red t_auth (y, `left "") leaf_auth
        else failwith "false"
      | `right (c, l_auth, (y, `left _), r_auth) ->
        if x = y then t_auth
        else if x < y then let l_ins = ins l_auth in
          balanceL (make_node c l_ins (y, `left "") r_auth)
        else if x > y then let r_ins = ins r_auth in
          balanceR (make_node c l_auth (y, `left "") r_ins)
        else failwith "false"
    in
    let t_ins = ins t_auth in
    blacken t_ins
end

module DirRedblackVerifierPolyBaseSer = struct
  type 'a auth = string
  type 'a option_t = [`left of string | `right of 'a]
  type color = string option_t (* left is red, right is black *)
  type value_option = string option_t
  type tree = (color * tree auth * (int * value_option) * tree auth) option_t
  type tree_auth = tree auth

  module Authenticatable = struct
    include Authenticatable_base.Verifier
    let auth = string
  end
  open Authenticatable

  let option_evi (a_evi : 'a evidence) :'a option_t evidence =
    (sum string a_evi)
  let value_evi : value_option evidence = option_evi string
  let tree_evi : tree evidence =
    option_evi (quad value_evi auth (pair int value_evi) auth)

  let ser o = tree_evi.serialize o
  let deser s = match tree_evi.deserialize s with Some s -> s | None -> raise (Invalid_argument "deser")
  let auth o = ser o |> hash
  let unauth h ps = match ps with
    | [] -> failwith "proof failure1"
    | p::ps when hash p = h -> ps, deser p
    | _ -> failwith "proof failure2"
  let red = `left ""
  let black = `right ""
  let none_v = `left ""
  let some_v v = `right v

  let empty_tree () = auth (`left "")
  let make_node c l kv r = auth (`right (c, l, kv, r))

  let blacken t_auth p =
    match unauth t_auth p with
    | p, `left _ -> p, empty_tree ()
    | p, `right (_, l, x, r) -> p, make_node black l x r

  let balanceL t_auth p = match unauth t_auth p with
  | p, `right (`right _, l_auth, a, r_auth) -> begin match unauth l_auth p with
    | p, `right (`left _, l1_auth, a1, r1_auth) -> begin match unauth l1_auth p with
      | p, `right (`left _, l2_auth, a2, r2_auth) -> 
        p, make_node red (make_node black l2_auth a2 r2_auth) a1 (make_node black r1_auth a r_auth)
      | p, _ -> begin match unauth r1_auth p with
        | p, `right (`left _, l2_auth, a2, r2_auth) -> 
          p, make_node red (make_node black l1_auth a1 l2_auth) a2 (make_node black r2_auth a r_auth)
        | p, sr1 -> p, t_auth
      end
    end
    | p, _ -> p, t_auth
  end
  | p, _ -> p, t_auth

  let balanceR t_auth p = match unauth t_auth p with
  | p, `right (`right _, l_auth, a, r_auth) -> begin match unauth r_auth p with
    | p, `right (`left _, l1_auth, a1, r1_auth) -> begin match unauth l1_auth p with
      | p, `right (`left _, l2_auth, a2, r2_auth) -> 
        p, make_node red (make_node black l_auth a l2_auth) a2 (make_node black r2_auth a1 r1_auth)
      | p, _ -> begin match unauth r1_auth p with
        | p, `right (`left _, l2_auth, a2, r2_auth) -> 
          p, make_node red (make_node black l_auth a l1_auth) a1 (make_node black l2_auth a2 r2_auth)
        | p, sr1 -> p, t_auth
      end
    end
    | p, _ -> p, t_auth
  end
  | p, t -> p, t_auth

  let insert x v t_auth p =
    let leaf_auth = make_node black (empty_tree ()) (x, `right v) (empty_tree ()) in
    let rec ins t_auth p =
      match unauth t_auth p with
      | p, `left _ -> p, leaf_auth
      | p, `right (c, l_auth, (y, `right _), r_auth) ->
        if x = y then p, t_auth
        else if x < y then p, make_node red leaf_auth (x, `left "") t_auth
        else if x > y then p, make_node red t_auth (y, `left "") leaf_auth
        else failwith "false"
      | p, `right (c, l_auth, (y, `left _), r_auth) ->
        if x = y then p, t_auth
        else if x < y then let p, l_ins = ins l_auth p in
          balanceL (make_node c l_ins (y, `left "") r_auth) p
        else if x > y then let p, r_ins = ins r_auth p in
          balanceR (make_node c l_auth (y, `left "") r_ins) p
        else failwith "false"
    in
    let p, t_ins = ins t_auth p in
    blacken t_ins p
end

module DirRedblackVerifierPolyMarSer = struct
  type 'a auth = string
  type 'a option_t = [`left of string | `right of 'a]
  type color = string option_t (* left is red, right is black *)
  type value_option = string option_t
  type tree = (color * tree auth * (int * value_option) * tree auth) option_t
  type tree_auth = tree auth

  module Authenticatable = struct
    include Authenticatable_marshal.Verifier
    let auth =
      let serialize x = Marshal.to_string x marshal_flags in
      let deserialize s = Some (Marshal.from_string s 0) in
      { serialize; deserialize }

  end
  open Authenticatable

  let option_evi (a_evi : 'a evidence) :'a option_t evidence =
    (sum string a_evi)
  let value_evi : value_option evidence = option_evi string
  let tree_evi : tree evidence =
    option_evi (quad value_evi auth (pair int value_evi) auth)

  let ser o = tree_evi.serialize o
  let deser s = match tree_evi.deserialize s with Some s -> s | None -> raise (Invalid_argument "deser")
  let auth o = ser o |> hash
  let unauth h ps = match ps with
    | [] -> failwith "proof failure1"
    | p::ps when hash p = h -> ps, deser p
    | _ -> failwith "proof failure2"
  let red = `left ""
  let black = `right ""
  let none_v = `left ""
  let some_v v = `right v

  let empty_tree () = auth (`left "")
  let make_node c l kv r = auth (`right (c, l, kv, r))

  let blacken t_auth p =
    match unauth t_auth p with
    | p, `left _ -> p, empty_tree ()
    | p, `right (_, l, x, r) -> p, make_node black l x r

  let balanceL t_auth p = match unauth t_auth p with
  | p, `right (`right _, l_auth, a, r_auth) -> begin match unauth l_auth p with
    | p, `right (`left _, l1_auth, a1, r1_auth) -> begin match unauth l1_auth p with
      | p, `right (`left _, l2_auth, a2, r2_auth) -> 
        p, make_node red (make_node black l2_auth a2 r2_auth) a1 (make_node black r1_auth a r_auth)
      | p, _ -> begin match unauth r1_auth p with
        | p, `right (`left _, l2_auth, a2, r2_auth) -> 
          p, make_node red (make_node black l1_auth a1 l2_auth) a2 (make_node black r2_auth a r_auth)
        | p, sr1 -> p, t_auth
      end
    end
    | p, _ -> p, t_auth
  end
  | p, _ -> p, t_auth

  let balanceR t_auth p = match unauth t_auth p with
  | p, `right (`right _, l_auth, a, r_auth) -> begin match unauth r_auth p with
    | p, `right (`left _, l1_auth, a1, r1_auth) -> begin match unauth l1_auth p with
      | p, `right (`left _, l2_auth, a2, r2_auth) -> 
        p, make_node red (make_node black l_auth a l2_auth) a2 (make_node black r2_auth a1 r1_auth)
      | p, _ -> begin match unauth r1_auth p with
        | p, `right (`left _, l2_auth, a2, r2_auth) -> 
          p, make_node red (make_node black l_auth a l1_auth) a1 (make_node black l2_auth a2 r2_auth)
        | p, sr1 -> p, t_auth
      end
    end
    | p, _ -> p, t_auth
  end
  | p, t -> p, t_auth

  let insert x v t_auth p =
    let leaf_auth = make_node black (empty_tree ()) (x, `right v) (empty_tree ()) in
    let rec ins t_auth p =
      match unauth t_auth p with
      | p, `left _ -> p, leaf_auth
      | p, `right (c, l_auth, (y, `right _), r_auth) ->
        if x = y then p, t_auth
        else if x < y then p, make_node red leaf_auth (x, `left "") t_auth
        else if x > y then p, make_node red t_auth (y, `left "") leaf_auth
        else failwith "false"
      | p, `right (c, l_auth, (y, `left _), r_auth) ->
        if x = y then p, t_auth
        else if x < y then let p, l_ins = ins l_auth p in
          balanceL (make_node c l_ins (y, `left "") r_auth) p
        else if x > y then let p, r_ins = ins r_auth p in
          balanceR (make_node c l_auth (y, `left "") r_ins) p
        else failwith "false"
    in
    let p, t_ins = ins t_auth p in
    blacken t_ins p
end

module DirRedblackVerifierPolyMarSerIo = struct
  type 'a auth = string
  type 'a option_t = [`left of string | `right of 'a]
  type color = string option_t (* left is red, right is black *)
  type value_option = string option_t
  type tree = (color * tree auth * (int * value_option) * tree auth) option_t
  type tree_auth = tree auth

  let input = ref (open_in_bin "/dev/null")

  let set_input s = 
    close_in !input; input := open_in_bin s
  let close_input () = close_in !input; input := open_in_bin "/dev/null"

  module Authenticatable = struct
    include Authenticatable_marshal.Verifier
    let auth =
      let serialize x = Marshal.to_string x marshal_flags in
      let deserialize s = Some (Marshal.from_string s 0) in
      { serialize; deserialize }

  end
  open Authenticatable

  let option_evi (a_evi : 'a evidence) :'a option_t evidence =
    (sum string a_evi)
  let value_evi : value_option evidence = option_evi string
  let tree_evi : tree evidence =
    option_evi (quad value_evi auth (pair int value_evi) auth)

  let ser o = tree_evi.serialize o
  let deser s = match tree_evi.deserialize s with Some s -> s | None -> raise (Invalid_argument "deser")
  let auth o = ser o |> hash
  let unauth h = 
    let p = from_channel_with_string !input in
    if hash p = h then deser p
    else failwith "Proof failure"
  let red = `left ""
  let black = `right ""
  let none_v = `left ""
  let some_v v = `right v

  let empty_tree () = auth (`left "")
  let make_node c l kv r = auth (`right (c, l, kv, r))

  let blacken t_auth =
    match unauth t_auth with
    | `left _ -> empty_tree ()
    | `right (_, l, x, r) -> make_node black l x r

  let balanceL t_auth = match unauth t_auth with
  | `right (`right _, l_auth, a, r_auth) -> begin match unauth l_auth with
    | `right (`left _, l1_auth, a1, r1_auth) -> begin match unauth l1_auth with
      | `right (`left _, l2_auth, a2, r2_auth) -> 
        make_node red (make_node black l2_auth a2 r2_auth) a1 (make_node black r1_auth a r_auth)
      | _ -> begin match unauth r1_auth with
        | `right (`left _, l2_auth, a2, r2_auth) -> 
          make_node red (make_node black l1_auth a1 l2_auth) a2 (make_node black r2_auth a r_auth)
        | sr1 -> t_auth
      end
    end
    | _ -> t_auth
  end
  | _ -> t_auth

  let balanceR t_auth = match unauth t_auth with
  | `right (`right _, l_auth, a, r_auth) -> begin match unauth r_auth with
    | `right (`left _, l1_auth, a1, r1_auth) -> begin match unauth l1_auth with
      | `right (`left _, l2_auth, a2, r2_auth) -> 
        make_node red (make_node black l_auth a l2_auth) a2 (make_node black r2_auth a1 r1_auth)
      | _ -> begin match unauth r1_auth with
        | `right (`left _, l2_auth, a2, r2_auth) -> 
          make_node red (make_node black l_auth a l1_auth) a1 (make_node black l2_auth a2 r2_auth)
        | sr1 -> t_auth
      end
    end
    | _ -> t_auth
  end
  | t -> t_auth

  let insert x v t_auth =
    let leaf_auth = make_node black (empty_tree ()) (x, `right v) (empty_tree ()) in
    let rec ins t_auth =
      match unauth t_auth with
      | `left _ -> leaf_auth
      | `right (c, l_auth, (y, `right _), r_auth) ->
        if x = y then t_auth
        else if x < y then make_node red leaf_auth (x, `left "") t_auth
        else if x > y then make_node red t_auth (y, `left "") leaf_auth
        else failwith "false"
      | `right (c, l_auth, (y, `left _), r_auth) ->
        if x = y then t_auth
        else if x < y then let l_ins = ins l_auth in
          balanceL (make_node c l_ins (y, `left "") r_auth)
        else if x > y then let r_ins = ins r_auth in
          balanceR (make_node c l_auth (y, `left "") r_ins)
        else failwith "false"
    in
    let t_ins = ins t_auth in
    blacken t_ins
end

module NonfunRedblackVerifierMar = struct
  type 'a option_t = [`left of string | `right of 'a]
  type color = string option_t (* left is red, right is black *)
  type value_option = string option_t
  type tree = (color * tree Verifier_marshal.auth * (int * value_option) * tree Verifier_marshal.auth) option_t
  type tree_auth = tree Verifier_marshal.auth

  let option_evi (a_evi : 'a Verifier_marshal.Authenticatable.evidence) :'a option_t Verifier_marshal.Authenticatable.evidence =
    Verifier_marshal.Authenticatable.(sum string a_evi)
  let value_evi : value_option Verifier_marshal.Authenticatable.evidence = option_evi Verifier_marshal.Authenticatable.string
  let tree_evi : tree Verifier_marshal.Authenticatable.evidence =
    option_evi Verifier_marshal.Authenticatable.(quad value_evi auth (pair int value_evi) auth)

  let empty_tree () = Verifier_marshal.auth tree_evi (`left "")
  let make_node c l kv r = Verifier_marshal.auth tree_evi (`right (c, l, kv, r))
  let auth t = Verifier_marshal.auth tree_evi t
  let red = `left ""
  let black = `right ""
  let none_v = `left ""
  let some_v v = `right v

  let blacken t =
    Verifier_marshal.bind (Verifier_marshal.unauth tree_evi t)
      (fun un_t ->
        match un_t with
        | `left _ -> Verifier_marshal.return t
        | `right (_, l, x, r) -> make_node black l x r |> Verifier_marshal.return)

  let balanceL t =
      Verifier_marshal.bind (Verifier_marshal.unauth tree_evi t)
        (fun un_t ->
          match un_t with
          | `right (`right _, l, a, r) ->
            Verifier_marshal.bind (Verifier_marshal.unauth tree_evi l)
              (fun un_l ->
                match un_l with
                | `right (`left _, l1, a1, r1) ->
                  Verifier_marshal.bind (Verifier_marshal.unauth tree_evi l1)
                    (fun un_l1 ->
                      match un_l1 with
                      | `right (`left _, l2, a2, r2) ->
                        make_node red (make_node black l2 a2 r2) a1 (make_node black r1 a r) |> Verifier_marshal.return
                      | _ ->
                        Verifier_marshal.bind (Verifier_marshal.unauth tree_evi r1)
                          (fun un_r1 ->
                            match un_r1 with
                            | `right (`left _, l2, a2, r2) ->
                              make_node red (make_node black l1 a1 l2) a2 (make_node black r2 a r) |> Verifier_marshal.return
                            | _ -> Verifier_marshal.return t
                            )
                      )
                | _ -> Verifier_marshal.return t
                )
          | _ -> Verifier_marshal.return t
          )

  let balanceR t =
    Verifier_marshal.bind (Verifier_marshal.unauth tree_evi t)
      (fun un_t ->
        match un_t with
        | `right (`right _, l, a, r) ->
          Verifier_marshal.bind (Verifier_marshal.unauth tree_evi r)
            (fun un_r ->
              match un_r with
              | `right (`left _, l1, a1, r1) ->
                Verifier_marshal.bind (Verifier_marshal.unauth tree_evi l1)
                  (fun un_l1 ->
                    match un_l1 with
                    | `right (`left _, l2, a2, r2) ->
                      make_node red (make_node black l a l2) a2 (make_node black r2 a1 r1) |> Verifier_marshal.return
                    | _ ->
                      Verifier_marshal.bind (Verifier_marshal.unauth tree_evi r1)
                        (fun un_r1 ->
                          match un_r1 with
                          | `right (`left _, l2, a2, r2) ->
                            make_node red (make_node black l a l1) a1 (make_node black l2 a2 r2) |> Verifier_marshal.return
                          | _ -> Verifier_marshal.return t
                          )
                    )
              | _ -> Verifier_marshal.return t
              )
        | _ -> Verifier_marshal.return t
        )
  
  let insert x v t =
    let leaf = make_node black (empty_tree ()) (x, some_v v) (empty_tree ()) in
    let rec ins t =
      Verifier_marshal.bind (Verifier_marshal.unauth tree_evi t)
        (fun un_t ->
          match un_t with
          | `left _ -> Verifier_marshal.return leaf
          | `right (c, l, (y, `right _), r) ->
            if x = y then Verifier_marshal.return t
            else if x < y then make_node red leaf (x, none_v) t |> Verifier_marshal.return 
            else if x > y then make_node red t (y, none_v) leaf |> Verifier_marshal.return
            else failwith "false"
          | `right (c, l, (y, `left _), r) ->
            if x = y then Verifier_marshal.return t
            else if x < y then
              Verifier_marshal.bind (ins l)
                (fun l_ins -> make_node c l_ins (y, none_v) r |> balanceL)
            else if x > y then
              Verifier_marshal.bind (ins r)
                (fun r_ins -> make_node c l (y, none_v) r_ins |> balanceR)
            else failwith "false"
          )
    in
    Verifier_marshal.bind (ins t)
      (fun ins_t -> blacken ins_t)
end

module NonfunRedblackVerifierIo = struct
  type 'a option_t = [`left of string | `right of 'a]
  type color = string option_t (* left is red, right is black *)
  type value_option = string option_t
  type tree = (color * tree Verifier_io.auth * (int * value_option) * tree Verifier_io.auth) option_t
  type tree_auth = tree Verifier_io.auth

  let option_evi (a_evi : 'a Verifier_io.Authenticatable.evidence) :'a option_t Verifier_io.Authenticatable.evidence =
    Verifier_io.Authenticatable.(sum string a_evi)
  let value_evi : value_option Verifier_io.Authenticatable.evidence = option_evi Verifier_io.Authenticatable.string
  let tree_evi : tree Verifier_io.Authenticatable.evidence =
    option_evi Verifier_io.Authenticatable.(quad value_evi auth (pair int value_evi) auth)

  let empty_tree () = Verifier_io.auth tree_evi (`left "")
  let make_node c l kv r = Verifier_io.auth tree_evi (`right (c, l, kv, r))
  let auth t = Verifier_io.auth tree_evi t
  let red = `left ""
  let black = `right ""
  let none_v = `left ""
  let some_v v = `right v

  let blacken t =
    Verifier_io.bind (Verifier_io.unauth tree_evi t)
      (fun un_t ->
        match un_t with
        | `left _ -> Verifier_io.return t
        | `right (_, l, x, r) -> make_node black l x r |> Verifier_io.return)

  let balanceL t =
      Verifier_io.bind (Verifier_io.unauth tree_evi t)
        (fun un_t ->
          match un_t with
          | `right (`right _, l, a, r) ->
            Verifier_io.bind (Verifier_io.unauth tree_evi l)
              (fun un_l ->
                match un_l with
                | `right (`left _, l1, a1, r1) ->
                  Verifier_io.bind (Verifier_io.unauth tree_evi l1)
                    (fun un_l1 ->
                      match un_l1 with
                      | `right (`left _, l2, a2, r2) ->
                        make_node red (make_node black l2 a2 r2) a1 (make_node black r1 a r) |> Verifier_io.return
                      | _ ->
                        Verifier_io.bind (Verifier_io.unauth tree_evi r1)
                          (fun un_r1 ->
                            match un_r1 with
                            | `right (`left _, l2, a2, r2) ->
                              make_node red (make_node black l1 a1 l2) a2 (make_node black r2 a r) |> Verifier_io.return
                            | _ -> Verifier_io.return t
                            )
                      )
                | _ -> Verifier_io.return t
                )
          | _ -> Verifier_io.return t
          )

  let balanceR t =
    Verifier_io.bind (Verifier_io.unauth tree_evi t)
      (fun un_t ->
        match un_t with
        | `right (`right _, l, a, r) ->
          Verifier_io.bind (Verifier_io.unauth tree_evi r)
            (fun un_r ->
              match un_r with
              | `right (`left _, l1, a1, r1) ->
                Verifier_io.bind (Verifier_io.unauth tree_evi l1)
                  (fun un_l1 ->
                    match un_l1 with
                    | `right (`left _, l2, a2, r2) ->
                      make_node red (make_node black l a l2) a2 (make_node black r2 a1 r1) |> Verifier_io.return
                    | _ ->
                      Verifier_io.bind (Verifier_io.unauth tree_evi r1)
                        (fun un_r1 ->
                          match un_r1 with
                          | `right (`left _, l2, a2, r2) ->
                            make_node red (make_node black l a l1) a1 (make_node black l2 a2 r2) |> Verifier_io.return
                          | _ -> Verifier_io.return t
                          )
                    )
              | _ -> Verifier_io.return t
              )
        | _ -> Verifier_io.return t
        )
  
  let insert x v t =
    let leaf = make_node black (empty_tree ()) (x, some_v v) (empty_tree ()) in
    let rec ins t =
      Verifier_io.bind (Verifier_io.unauth tree_evi t)
        (fun un_t ->
          match un_t with
          | `left _ -> Verifier_io.return leaf
          | `right (c, l, (y, `right _), r) ->
            if x = y then Verifier_io.return t
            else if x < y then make_node red leaf (x, none_v) t |> Verifier_io.return 
            else if x > y then make_node red t (y, none_v) leaf |> Verifier_io.return
            else failwith "false"
          | `right (c, l, (y, `left _), r) ->
            if x = y then Verifier_io.return t
            else if x < y then
              Verifier_io.bind (ins l)
                (fun l_ins -> make_node c l_ins (y, none_v) r |> balanceL)
            else if x > y then
              Verifier_io.bind (ins r)
                (fun r_ins -> make_node c l (y, none_v) r_ins |> balanceR)
            else failwith "false"
          )
    in
    Verifier_io.bind (ins t)
      (fun ins_t -> blacken ins_t)
end

let auth_io_hash = Hashtbl.create 18
let read_prover_io_rb_tree s =
  let rec prover_tree keys t =
    match keys with
    | [] -> t
    | k::keys ->
      let t = Prover_io.run (RedBlack_Prover_io.insert k (string_of_int k) t) in
      prover_tree keys t
  in
  let n = exp 2 s in
  let chn = Printf.sprintf "%s/rdb1_%d.dat" data_folder s |> open_in_bin in
  let keys = read_keys n chn in
  close_in chn;
  let t = RedBlack_Prover_io.empty_tree () in
  prover_tree keys t

let read_dir_prover_rb_tree s =
  let rec prover_tree keys t =
    match keys with
    | [] -> t
    | k::keys ->
      let _, t = DirRedblackProver.insert k (string_of_int k) t [] in
      prover_tree keys t
  in
  let n = exp 2 s in
  let chn = Printf.sprintf "%s/rdb1_%d.dat" data_folder s |> open_in_bin in
  let keys = read_keys n chn in
  close_in chn;
  let t = DirRedblackProver.empty_tree () in
  prover_tree keys t

let dir_io_hash = Hashtbl.create 18
let read_dir_prover_rb_io_tree s =
  let rec prover_tree keys t =
    match keys with
    | [] -> t
    | k::keys ->
      let t = DirRedblackProverIo.insert k (string_of_int k) t in
      prover_tree keys t
  in
  let n = exp 2 s in
  let chn = Printf.sprintf "%s/rdb1_%d.dat" data_folder s |> open_in_bin in
  let keys = read_keys n chn in
  close_in chn;
  let t = DirRedblackProverIo.empty_tree () in
  prover_tree keys t

let dir_poly_io_hash = Hashtbl.create 18
let read_dir_prover_rb_poly_io_tree s =
  let rec prover_tree keys t =
    match keys with
    | [] -> t
    | k::keys ->
      let t = DirRedblackProverPolyIo.insert k (string_of_int k) t in
      prover_tree keys t
  in
  let n = exp 2 s in
  let chn = Printf.sprintf "%s/rdb1_%d.dat" data_folder s |> open_in_bin in
  let keys = read_keys n chn in
  close_in chn;
  let t = DirRedblackProverPolyIo.empty_tree () in
  prover_tree keys t

let dir_poly_mar_ser_io_hash = Hashtbl.create 18
let read_dir_prover_rb_poly_mar_ser_io_tree s =
  let rec prover_tree keys t =
    match keys with
    | [] -> t
    | k::keys ->
      let t = DirRedblackProverPolyMarSerIo.insert k (string_of_int k) t in
      prover_tree keys t
  in
  let n = exp 2 s in
  let chn = Printf.sprintf "%s/rdb1_%d.dat" data_folder s |> open_in_bin in
  let keys = read_keys n chn in
  close_in chn;
  let t = DirRedblackProverPolyMarSerIo.empty_tree () in
  prover_tree keys t

let read_io_tree s =
  let chn = Printf.sprintf "%s/mtree_%d.dat" data_folder s |> open_in_bin in
  let l = from_channel_with_string chn in
  close_in chn;
  Merkle_Prover_io.from_list (Marshal.from_string l 0)

let rec dirprover_redblack_insertions t keys =
  match keys with
  | [] -> ()
  | k::keys -> 
    let _ = DirRedblackProver.run (DirRedblackProver.insert k (string_of_int k) t) in
    dirprover_redblack_insertions t keys
let rec dirprover_redblack_poly_insertions t keys =
  match keys with
  | [] -> ()
  | k::keys -> 
    let _ = DirRedblackProverPoly.insert k (string_of_int k) t [] in
    dirprover_redblack_poly_insertions t keys
let rec dirprover_redblack_poly_base_ser_insertions t keys =
  match keys with
  | [] -> ()
  | k::keys -> 
    let _ = DirRedblackProverPolyBaseSer.insert k (string_of_int k) t [] in
    dirprover_redblack_poly_base_ser_insertions t keys
let rec dirprover_redblack_poly_mar_ser_insertions t keys =
  match keys with
  | [] -> ()
  | k::keys -> 
    let _ = DirRedblackProverPolyMarSer.insert k (string_of_int k) t [] in
    dirprover_redblack_poly_mar_ser_insertions t keys
let rec prover_mar_redblack_dir_insertions t keys =
  match keys with
  | [] -> ()
  | k::keys -> 
    let _ = NonfunRedblackProverMar.insert k (string_of_int k) t [] in
    prover_mar_redblack_dir_insertions t keys
let rec prover_redblack_insertions t keys =
  match keys with
  | [] -> ()
  | k::keys -> 
    let _ = Prover_rev.run (RedBlack_Prover_rev.insert k (string_of_int k) t) in
    prover_redblack_insertions t keys
let rec prover_mar_redblack_insertions t keys =
  match keys with
  | [] -> ()
  | k::keys -> 
    let _ = Prover_marshal.run (RedBlack_Prover_marshal.insert k (string_of_int k) t) in
    prover_mar_redblack_insertions t keys

let rec dirprover_redblack_insertions_keep t keys proofs =
  match keys with
  | [] -> List.rev proofs
  | k::keys -> 
    let proof, _ = DirRedblackProver.run (DirRedblackProver.insert k (string_of_int k) t) in
    dirprover_redblack_insertions_keep t keys (proof :: proofs)
let rec dirprover_redblack_poly_insertions_keep t keys proofs =
  match keys with
  | [] -> List.rev proofs
  | k::keys -> 
    let proof, _ = DirRedblackProverPoly.run (DirRedblackProverPoly.insert k (string_of_int k) t) in
    dirprover_redblack_poly_insertions_keep t keys (proof :: proofs)
let rec dirprover_redblack_poly_base_ser_insertions_keep t keys proofs =
  match keys with
  | [] -> List.rev proofs
  | k::keys -> 
    let proof, _ = DirRedblackProverPolyBaseSer.run (DirRedblackProverPolyBaseSer.insert k (string_of_int k) t) in
    dirprover_redblack_poly_base_ser_insertions_keep t keys (proof :: proofs)
let rec dirprover_redblack_poly_mar_ser_insertions_keep t keys proofs =
  match keys with
  | [] -> List.rev proofs
  | k::keys -> 
    let proof, _ = DirRedblackProverPolyMarSer.run (DirRedblackProverPolyMarSer.insert k (string_of_int k) t) in
    dirprover_redblack_poly_mar_ser_insertions_keep t keys (proof :: proofs)
let rec prover_mar_redblack_dir_insertions_keep t keys proofs =
  match keys with
  | [] -> List.rev proofs
  | k::keys -> 
    let proof, _ = Prover_marshal.run (NonfunRedblackProverMar.insert k (string_of_int k) t) in
    prover_mar_redblack_dir_insertions_keep t keys (proof :: proofs)
let rec prover_redblack_insertions_keep t keys proofs =
  match keys with
  | [] -> List.rev proofs
  | k::keys -> 
    let proof, _ = Prover_rev.run (RedBlack_Prover_rev.insert k (string_of_int k) t) in
    prover_redblack_insertions_keep t keys (proof :: proofs)
let rec prover_mar_redblack_insertions_keep t keys proofs =
  match keys with
  | [] -> List.rev proofs
  | k::keys -> 
    let proof, _ = Prover_marshal.run (RedBlack_Prover_marshal.insert k (string_of_int k) t) in
    prover_mar_redblack_insertions_keep t keys (proof :: proofs)

let dirprover_redblack_poly_mar_ser_io_insertions file t keys =
  DirRedblackProverPolyMarSerIo.set_output file;
  let rec real_dirprover_redblack_poly_mar_ser_io_insertions keys =
    match keys with
    | [] -> DirRedblackProverPolyMarSerIo.close_output ()
    | k::keys -> 
      let _ = DirRedblackProverPolyMarSerIo.insert k (string_of_int k) t in
      real_dirprover_redblack_poly_mar_ser_io_insertions keys
  in
  real_dirprover_redblack_poly_mar_ser_io_insertions keys
let dirprover_redblack_io_insertions file t keys =
  DirRedblackProverIo.set_output file;
  let rec real_dirprover_redblack_io_insertions keys =
    match keys with
    | [] -> DirRedblackProverIo.close_output ()
    | k::keys -> 
      let _ = DirRedblackProverIo.insert k (string_of_int k) t in
      real_dirprover_redblack_io_insertions keys
  in
  real_dirprover_redblack_io_insertions keys
let dirprover_redblack_poly_io_insertions file t keys =
  DirRedblackProverPolyIo.set_output file;
  let rec real_dirprover_redblack_poly_io_insertions keys =
    match keys with
    | [] -> DirRedblackProverPolyIo.close_output ()
    | k::keys -> 
      let _ = DirRedblackProverPolyIo.insert k (string_of_int k) t in
      real_dirprover_redblack_poly_io_insertions keys
  in
  real_dirprover_redblack_poly_io_insertions keys
let rec prover_io_redblack_dir_insertions file t keys =
  Prover_io.set_output file;
  let rec real_prover_io_redblack_dir_insertions t keys =
    match keys with
    | [] -> Prover_io.close_output ()
    | k::keys -> 
      let _ = NonfunRedblackProverIo.insert k (string_of_int k) t [] in
      real_prover_io_redblack_dir_insertions t keys
  in
  real_prover_io_redblack_dir_insertions t keys
let prover_io_redblack_insertions file t keys =
  Prover_io.set_output file;
  let rec real_prover_io_redblack_insertions t keys =
    match keys with
    | [] -> Prover_io.close_output ()
    | k::keys -> 
      let _ = Prover_io.run (RedBlack_Prover_io.insert k (string_of_int k) t) in
      real_prover_io_redblack_insertions t keys
  in
  real_prover_io_redblack_insertions t keys

let rec dirverifier_redblack_insertions ht keys proofs =
  (* let _ = print_string ("verifier"^(string_of_int (List.length values))); print_newline () in *)
  match keys, proofs with
  | [], [] -> ()
  | k::keys, proof::proofs ->
    let v = string_of_int k in
    let _ = DirRedblackVerifier.insert k v ht proof in
    dirverifier_redblack_insertions ht keys proofs
  | _ -> failwith "keys and proofs must match in length"

let rec dirverifier_redblack_poly_insertions ht keys proofs =
  (* let _ = print_string ("verifier"^(string_of_int (List.length values))); print_newline () in *)
  match keys, proofs with
  | [], [] -> ()
  | k::keys, proof::proofs ->
    let v = string_of_int k in
    let _ = DirRedblackVerifierPoly.insert k v ht proof in
    dirverifier_redblack_poly_insertions ht keys proofs
  | _ -> failwith "keys and proofs must match in length"

let rec dirverifier_redblack_poly_base_ser_insertions ht keys proofs =
  (* let _ = print_string ("verifier"^(string_of_int (List.length values))); print_newline () in *)
  match keys, proofs with
  | [], [] -> ()
  | k::keys, proof::proofs ->
    let v = string_of_int k in
    let _ = DirRedblackVerifierPolyBaseSer.insert k v ht proof in
    dirverifier_redblack_poly_base_ser_insertions ht keys proofs
  | _ -> failwith "keys and proofs must match in length"

let rec dirverifier_redblack_poly_mar_ser_insertions ht keys proofs =
  (* let _ = print_string ("verifier"^(string_of_int (List.length values))); print_newline () in *)
  match keys, proofs with
  | [], [] -> ()
  | k::keys, proof::proofs ->
    let v = string_of_int k in
    let _ = DirRedblackVerifierPolyMarSer.insert k v ht proof in
    dirverifier_redblack_poly_mar_ser_insertions ht keys proofs
  | _ -> failwith "keys and proofs must match in length"

let dirverifier_redblack_io_insertions file ht keys =
  DirRedblackVerifierIo.set_input file;
  let rec real_dirverifier_redblack_insertions keys =
    match keys with
    | [] -> DirRedblackVerifierIo.close_input ()
    | k::keys ->
      let v = string_of_int k in
      let _ = DirRedblackVerifierIo.insert k v ht in
      real_dirverifier_redblack_insertions keys
  in
  real_dirverifier_redblack_insertions keys

let dirverifier_redblack_poly_io_insertions file ht keys =
  DirRedblackVerifierPolyIo.set_input file;
  let rec real_dirverifier_redblack_poly_insertions keys =
    match keys with
    | [] -> DirRedblackVerifierPolyIo.close_input ()
    | k::keys ->
      let v = string_of_int k in
      let _ = DirRedblackVerifierPolyIo.insert k v ht in
      real_dirverifier_redblack_poly_insertions keys
  in
  real_dirverifier_redblack_poly_insertions keys

let dirverifier_redblack_poly_mar_ser_io_insertions file ht keys =
  DirRedblackVerifierPolyMarSerIo.set_input file;
  let rec real_dirverifier_redblack_poly_mar_ser_insertions keys =
    match keys with
    | [] -> DirRedblackVerifierPolyMarSerIo.close_input ()
    | k::keys ->
      let v = string_of_int k in
      let _ = DirRedblackVerifierPolyMarSerIo.insert k v ht in
      real_dirverifier_redblack_poly_mar_ser_insertions keys
  in
  real_dirverifier_redblack_poly_mar_ser_insertions keys

let rec verifier_mar_dir_redblack_insertions ht keys proofs =
  (* let _ = print_string ("verifier"^(string_of_int (List.length values))); print_newline () in *)
  match keys, proofs with
  | [], [] -> ()
  | k::keys, proof::proofs ->
    let v = string_of_int k in
    let _ = NonfunRedblackVerifierMar.insert k v ht proof in
    verifier_mar_dir_redblack_insertions ht keys proofs
  | _ -> failwith "keys and proofs must match in length"

let verifier_io_dir_redblack_insertions file ht keys =
  Verifier_io.set_input file;
  let rec real_verifier_io_dir_redblack_insertions ht keys =
    (* let _ = print_string ("verifier"^(string_of_int (List.length values))); print_newline () in *)
    match keys with
    | [] -> Verifier_io.close_input ()
    | k::keys ->
      let v = string_of_int k in
      let _ = NonfunRedblackVerifierIo.insert k v ht [] in
      real_verifier_io_dir_redblack_insertions ht keys
  in
  real_verifier_io_dir_redblack_insertions ht keys

let rec verifier_redblack_insertions ht keys proofs =
  (* let _ = print_string ("verifier"^(string_of_int (List.length values))); print_newline () in *)
  match keys, proofs with
  | [], [] -> ()
  | k::keys, proof::proofs ->
    let v = string_of_int k in
    let _ = Verifier.run (RedBlack_Verifier.insert k v ht) proof in
    verifier_redblack_insertions ht keys proofs
  | _ -> failwith "keys and proofs must match in length"

let rec verifier_marshal_redblack_insertions ht keys proofs =
  (* let _ = print_string ("verifier"^(string_of_int (List.length values))); print_newline () in *)
  match keys, proofs with
  | [], [] -> ()
  | k::keys, proof::proofs ->
    let v = string_of_int k in
    let _ = Verifier_marshal.run (RedBlack_Verifier_marshal.insert k v ht) proof in
    verifier_marshal_redblack_insertions ht keys proofs
  | _ -> failwith "keys and proofs must match in length"

let verifier_io_redblack_insertions file ht keys =
  Verifier_io.set_input file;
  let rec real_verifier_io_redblack_insertions ht keys =
    (* let _ = print_string ("verifier"^(string_of_int (List.length values))); print_newline () in *)
    match keys with
    | [] -> Verifier_io.close_input ()
    | k::keys ->
      let v = string_of_int k in
      let _ = Verifier_io.run (RedBlack_Verifier_io.insert k v ht) in
      real_verifier_io_redblack_insertions ht keys
  in
  real_verifier_io_redblack_insertions ht keys

let rec ideal_redblack_insertions t keys =
  (* let _ = print_string ("ideal"^(string_of_int (List.length values))); print_newline () in *)
  match keys with
  | [] -> ()
  | k::keys ->
    let v = string_of_int k in
    let _ = RedBlack_Ideal.insert k v t in
    ideal_redblack_insertions t keys

let rec ideal_rbredblack_insertions t keys =
  (* let _ = print_string ("ideal"^(string_of_int (List.length values))); print_newline () in *)
  match keys with
  | [] -> ()
  | k::keys ->
    let _ = DirRedblackIdeal.insert k (string_of_int k) t in
    ideal_rbredblack_insertions t keys

let rec ideal_rbredblackid_insertions t keys =
  (* let _ = print_string ("ideal"^(string_of_int (List.length values))); print_newline () in *)
  match keys with
  | [] -> ()
  | k::keys ->
    let _ = RedBlackDirIdeal.insert k (string_of_int k) t in
    ideal_rbredblackid_insertions t keys

(* let rec prover_redblack_retrieves keys t proofs =
  match keys with
  | [] -> proofs
  | key::keys ->
    let proof, _ = Prover_rev.run (RedBlack_Prover_rev.retrieve key t) in
    prover_redblack_retrieves keys t (proof::proofs) *)

(* let rec verifier_redblack_retrieves keys ht proofs =
  match keys, proofs with
  | [], [] -> ()
  | key::keys, proof::proofs ->
    let _ = Verifier.run (RedBlack_Verifier.retrieve key ht) proof in
    verifier_redblack_retrieves keys ht proofs
  | _ -> failwith "paths and proofs length differ";; *)

let rec prover_merkle_retrieves_keep t h paths proofs =
  match paths with
  | [] -> proofs
  | path::paths ->
    let proof, _ = Prover_rev.run (Merkle_Prover_rev.retrieve path t) in
    prover_merkle_retrieves_keep t h paths (proof::proofs)

let rec verifier_merkle_retrieves ht h paths proofs =
  match paths,proofs with
  | [], [] -> ()
  | path::paths, proof::proofs ->
    let _ = Verifier.run (Merkle_Verifier.retrieve path ht) proof in
    verifier_merkle_retrieves ht h paths proofs
  | _ -> failwith "paths and proofs length differ"

let rec prover_merkle_magic_retrieves_keep t h paths proofs =
  match paths with
  | [] -> proofs
  | path::paths ->
    let proof, _ = Prover_rev.run (Merkle_Prover_rev.retrieve_magic path t) in
    prover_merkle_magic_retrieves_keep t h paths (proof::proofs)

let rec verifier_merkle_magic_retrieves ht h paths proofs =
  match paths, proofs with
  | [],[] -> ()
  | path::paths, proof::proofs ->
    let _ = Verifier.run (Merkle_Verifier.retrieve_magic path ht) proof in
    verifier_merkle_magic_retrieves ht h paths proofs
  | _ -> failwith "paths and proofs length differ"

let rec prover_marshal_merkle_retrieves_keep t h paths proofs =
  match paths with
  | [] -> proofs
  | path::paths ->
    let proof, _ = Prover_marshal.run (Merkle_Prover_marshal.retrieve path t) in
    prover_marshal_merkle_retrieves_keep t h paths (proof::proofs)

let rec verifier_marshal_merkle_retrieves ht h paths proofs =
  match paths, proofs with
  | [],[] -> ()
  | path::paths, proof::proofs ->
    let _ = Verifier_marshal.run (Merkle_Verifier_marshal.retrieve path ht) proof in
    verifier_marshal_merkle_retrieves ht h paths proofs
  | _ -> failwith "paths and proofs length differ"

let rec prover_marshal_merkle_magic_retrieves_keep t h paths proofs =
  match paths with
  | [] -> proofs
  | path::paths ->
    let proof, _ = Prover_marshal.run (Merkle_Prover_marshal.retrieve_magic path t) in
    prover_marshal_merkle_magic_retrieves_keep t h paths (proof::proofs)

let rec verifier_marshal_merkle_magic_retrieves ht h paths proofs =
  match paths, proofs with
  | [],[] -> ()
  | path::paths, proof::proofs ->
    let _ = Verifier_marshal.run (Merkle_Verifier_marshal.retrieve_magic path ht) proof in
    verifier_marshal_merkle_magic_retrieves ht h paths proofs
  | _ -> failwith "paths and proofs length differ"

let prover_io_merkle_retrieves_keep file t h paths =
  Prover_io.set_output file;
  let rec real_prover_io_merkle_retrieves_keep t h paths =
    match paths with
    | [] -> Prover_io.close_output ()
    | path::paths ->
      let _ = Prover_io.run (Merkle_Prover_io.retrieve path t) in
      real_prover_io_merkle_retrieves_keep t h paths
  in
  real_prover_io_merkle_retrieves_keep t h paths

let verifier_io_merkle_retrieves file ht h paths =
  Verifier_io.set_input file;
  let rec real_verifier_io_merkle_retrieves ht h paths =
    match paths with
    | [] -> Verifier_io.close_input ()
    | path::paths ->
      let _ = Verifier_io.run (Merkle_Verifier_io.retrieve path ht) in
      real_verifier_io_merkle_retrieves ht h paths
  in
  real_verifier_io_merkle_retrieves ht h paths

let prover_io_merkle_magic_retrieves_keep file t h paths =
  Prover_io.set_output file;
  let rec real_prover_io_merkle_magic_retrieves_keep t h paths =
    match paths with
    | [] -> Prover_io.close_output ()
    | path::paths ->
      let _ = Prover_io.run (Merkle_Prover_io.retrieve_magic path t) in
      real_prover_io_merkle_magic_retrieves_keep t h paths
  in
  real_prover_io_merkle_magic_retrieves_keep t h paths

let verifier_io_merkle_magic_retrieves file ht h paths =
  Verifier_io.set_input file;
  let rec real_verifier_io_merkle_magic_retrieves ht h paths =
    match paths with
    | [] -> Verifier_io.close_input ()
    | path::paths ->
      let _ = Verifier_io.run (Merkle_Verifier_io.retrieve_magic path ht) in
      real_verifier_io_merkle_magic_retrieves ht h paths
  in
  real_verifier_io_merkle_magic_retrieves ht h paths;;

let read_rdb_ins s =
  let chn = Printf.sprintf "%s/rdb_ins1_%d.dat" data_folder s |> open_in_bin in
  let keys = read_keys num_rb_inserts chn in
  close_in chn;
  keys;;

job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i), fun () ->
    Printf.printf "%d %d direct_prover_redblack_insertions" i s;
    let t = read_dir_prover_rb_tree s in
    let keys = read_rdb_ins s in
    gc_collect ();
    measure_call ("direct_prover_redblack_insertions "^(string_of_int s)) (dirprover_redblack_insertions t) keys)
config_array;

job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i), fun () ->
    Printf.printf "%d %d dirprover_redblack_io_insertions" i s;
    let t = read_dir_prover_rb_io_tree s in
    Hashtbl.add dir_io_hash s (snd t);
    let keys = read_rdb_ins s in
    gc_collect ();
    let file = Printf.sprintf "%s/proof_rb_ins_d_%03d.dat" proof_folder s in
    measure_call ("dirprover_redblack_io_insertions "^(string_of_int s)) (dirprover_redblack_io_insertions file t) keys)
config_array;

job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i), fun () ->
    Printf.printf "%d %d dirprover_redblack_poly_io_insertions" i s;
    let t = read_dir_prover_rb_poly_io_tree s in
    Hashtbl.add dir_poly_io_hash s (snd t);
    let keys = read_rdb_ins s in
    gc_collect ();
    let file = Printf.sprintf "%s/proof_rb_ins_dp_%03d.dat" proof_folder s in
    measure_call ("dirprover_redblack_poly_io_insertions "^(string_of_int s)) (dirprover_redblack_poly_io_insertions file t) keys)
config_array;

job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i), fun () ->
    Printf.printf "%d %d dirprover_redblack_poly_mar_ser_io_insertions" i s;
    let t = read_dir_prover_rb_poly_mar_ser_io_tree s in
    Hashtbl.add dir_poly_mar_ser_io_hash s (snd t);
    let keys = read_rdb_ins s in
    gc_collect ();
    let file = Printf.sprintf "%s/proof_rb_ins_dpm_%03d.dat" proof_folder s in
    measure_call ("dirprover_redblack_poly_mar_ser_io_insertions "^(string_of_int s)) (dirprover_redblack_poly_mar_ser_io_insertions file t) keys)
config_array;

job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i), fun () ->
    Printf.printf "%d %d prover_io_redblack_insertions" i s;
    let t = read_prover_io_rb_tree s in
    Hashtbl.add auth_io_hash s (Prover_io.get_hash t);
    let keys = read_rdb_ins s in
    gc_collect ();
    let file = Printf.sprintf "%s/proof_rb_ins_dpma_%03d.dat" proof_folder s in
    measure_call ("prover_io_redblack_insertions "^(string_of_int s)) (prover_io_redblack_insertions file t) keys)
config_array;

job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i) + (2*n_configs), fun () ->
    Printf.printf "%d %d dirverifier_redblack_insertions" i s;
    let t = read_dir_prover_rb_tree s in
    let keys = read_rdb_ins s in
    let ht = snd t in
    let proofs = dirprover_redblack_insertions_keep t keys [] in
    gc_collect ();
    measure_call ("dirverifier_redblack_insertions "^(string_of_int s)) (dirverifier_redblack_insertions ht keys) proofs)
config_array;

job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i) + (2*n_configs), fun () ->
    Printf.printf "%d %d dirverifier_redblack_io_insertions" i s;
    let file = Printf.sprintf "%s/proof_rb_ins_d_%03d.dat" proof_folder s in
    let ht = Hashtbl.find dir_io_hash s in
    let keys = read_rdb_ins s in
    gc_collect ();
    measure_call ("dirverifier_redblack_io_insertions "^(string_of_int s)) (dirverifier_redblack_io_insertions file ht) keys)
config_array;

job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i) + (2*n_configs), fun () ->
    Printf.printf "%d %d dirverifier_redblack_poly_io_insertions" i s;
    let file = Printf.sprintf "%s/proof_rb_ins_dp_%03d.dat" proof_folder s in
    let ht = Hashtbl.find dir_poly_io_hash s in
    let keys = read_rdb_ins s in
    gc_collect ();
    measure_call ("dirverifier_redblack_poly_io_insertions "^(string_of_int s)) (dirverifier_redblack_poly_io_insertions file ht) keys)
config_array;

job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i) + (2*n_configs), fun () ->
    Printf.printf "%d %d dirverifier_redblack_poly_mar_ser_io_insertions" i s;
    let file = Printf.sprintf "%s/proof_rb_ins_dpm_%03d.dat" proof_folder s in
    let ht = Hashtbl.find dir_poly_mar_ser_io_hash s in
    let keys = read_rdb_ins s in
    gc_collect ();
    measure_call ("dirverifier_redblack_poly_mar_ser_io_insertions "^(string_of_int s)) (dirverifier_redblack_poly_mar_ser_io_insertions file ht) keys)
config_array;

job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i) + (2*n_configs), fun () ->
    Printf.printf "%d %d verifier_io_redblack_insertions" i s;
    let file = Printf.sprintf "%s/proof_rb_ins_dpma_%03d.dat" proof_folder s in
    let ht = Hashtbl.find auth_io_hash s in
    let keys = read_rdb_ins s in
    gc_collect ();
    measure_call ("verifier_io_redblack_insertions "^(string_of_int s)) (verifier_io_redblack_insertions file ht) keys)
config_array;

job_queue := List.sort (fun (i1, _) (i2, _) -> compare i1 i2) !job_queue;

let rec run_jobs = function
  | [] -> ()
  | (_, job)::rest ->
    job ();
    print_endline "";
    gc_collect ();
    run_jobs rest
in

run_jobs !job_queue;
print_measures ();
