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

let num_rb_retrieves = 100000

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

  let rec retrieve x t =
    match unauth t with
    | Tip -> None
    | Bin (_, _, (y, Som v), _) -> 
      if y = x then (Some v) else None
    | Bin (_, l, (y, Non), r) -> 
      if x <= y then retrieve x l else retrieve x r

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

  let rec retrieve x t =
    match unauth t with
    | `left _ -> None
    | `right (_, _, (y, `right v), _) -> 
      if y = x then (Some v) else None
    | `right (_, l, (y, `left _), r) -> 
      if x <= y then retrieve x l else retrieve x r

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

  let rec retrieve x t =
    match unauth t with
    | `left _ -> None
    | `right (_, _, (y, `right v), _) -> 
      if y = x then (Some v) else None
    | `right (_, l, (y, `left _), r) -> 
      if x <= y then retrieve x l else retrieve x r

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

  let rec retrieve x t =
    match unauth t with
    | Tip -> None
    | Bin (_, _, (y, Som v), _) -> 
      if y = x then (Some v) else None
    | Bin (_, l, (y, Non), r) -> 
      if x <= y then retrieve x l else retrieve x r

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

  let rec retrieve x t =
    match unauth t with
    | `left _ -> None
    | `right (_, _, (y, `right v), _) -> 
      if y = x then (Some v) else None
    | `right (_, l, (y, `left _), r) -> 
      if x <= y then retrieve x l else retrieve x r

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

  let rec retrieve x t =
    match unauth t with
    | `left _ -> None
    | `right (_, _, (y, `right v), _) -> 
      if y = x then (Some v) else None
    | `right (_, l, (y, `left _), r) -> 
      if x <= y then retrieve x l else retrieve x r

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


let dirprover_redblack_poly_mar_ser_io_retrieves file t keys =
  DirRedblackProverPolyMarSerIo.set_output file;
  let rec real_dirprover_redblack_poly_mar_ser_io_retrieves keys =
    match keys with
    | [] -> DirRedblackProverPolyMarSerIo.close_output ()
    | k::keys -> 
      let _ = DirRedblackProverPolyMarSerIo.retrieve k t in
      real_dirprover_redblack_poly_mar_ser_io_retrieves keys
  in
  real_dirprover_redblack_poly_mar_ser_io_retrieves keys
let dirprover_redblack_io_retrieves file t keys =
  DirRedblackProverIo.set_output file;
  let rec real_dirprover_redblack_io_retrieves keys =
    match keys with
    | [] -> DirRedblackProverIo.close_output ()
    | k::keys -> 
      let _ = DirRedblackProverIo.retrieve k t in
      real_dirprover_redblack_io_retrieves keys
  in
  real_dirprover_redblack_io_retrieves keys
let dirprover_redblack_poly_io_retrieves file t keys =
  DirRedblackProverPolyIo.set_output file;
  let rec real_dirprover_redblack_poly_io_retrieves keys =
    match keys with
    | [] -> DirRedblackProverPolyIo.close_output ()
    | k::keys -> 
      let _ = DirRedblackProverPolyIo.retrieve k t in
      real_dirprover_redblack_poly_io_retrieves keys
  in
  real_dirprover_redblack_poly_io_retrieves keys

let prover_io_redblack_retrieves file t keys =
  Prover_io.set_output file;
  let rec real_prover_io_redblack_retrieves t keys =
    match keys with
    | [] -> Prover_io.close_output ()
    | k::keys -> 
      let _ = Prover_io.run (RedBlack_Prover_io.retrieve k t) in
      real_prover_io_redblack_retrieves t keys
  in
  real_prover_io_redblack_retrieves t keys

let dirverifier_redblack_io_retrieves file ht keys =
  DirRedblackVerifierIo.set_input file;
  let rec real_dirverifier_redblack_retrieves keys =
    match keys with
    | [] -> DirRedblackVerifierIo.close_input ()
    | k::keys ->
      let _ = DirRedblackVerifierIo.retrieve k ht in
      real_dirverifier_redblack_retrieves keys
  in
  real_dirverifier_redblack_retrieves keys

let dirverifier_redblack_poly_io_retrieves file ht keys =
  DirRedblackVerifierPolyIo.set_input file;
  let rec real_dirverifier_redblack_poly_retrieves keys =
    match keys with
    | [] -> DirRedblackVerifierPolyIo.close_input ()
    | k::keys ->
      let _ = DirRedblackVerifierPolyIo.retrieve k ht in
      real_dirverifier_redblack_poly_retrieves keys
  in
  real_dirverifier_redblack_poly_retrieves keys

let dirverifier_redblack_poly_mar_ser_io_retrieves file ht keys =
  DirRedblackVerifierPolyMarSerIo.set_input file;
  let rec real_dirverifier_redblack_poly_mar_ser_retrieves keys =
    match keys with
    | [] -> DirRedblackVerifierPolyMarSerIo.close_input ()
    | k::keys ->
      let _ = DirRedblackVerifierPolyMarSerIo.retrieve k ht in
      real_dirverifier_redblack_poly_mar_ser_retrieves keys
  in
  real_dirverifier_redblack_poly_mar_ser_retrieves keys

let rec verifier_redblack_retrieves ht keys proofs =
  (* let _ = print_string ("verifier"^(string_of_int (List.length values))); print_newline () in *)
  match keys, proofs with
  | [], [] -> ()
  | k::keys, proof::proofs ->
    let _ = Verifier.run (RedBlack_Verifier.retrieve k ht) proof in
    verifier_redblack_retrieves ht keys proofs
  | _ -> failwith "keys and proofs must match in length"

let rec verifier_marshal_redblack_retrieves ht keys proofs =
  (* let _ = print_string ("verifier"^(string_of_int (List.length values))); print_newline () in *)
  match keys, proofs with
  | [], [] -> ()
  | k::keys, proof::proofs ->
    let _ = Verifier_marshal.run (RedBlack_Verifier_marshal.retrieve k ht) proof in
    verifier_marshal_redblack_retrieves ht keys proofs
  | _ -> failwith "keys and proofs must match in length"

let verifier_io_redblack_retrieves file ht keys =
  Verifier_io.set_input file;
  let rec real_verifier_io_redblack_retrieves ht keys =
    (* let _ = print_string ("verifier"^(string_of_int (List.length values))); print_newline () in *)
    match keys with
    | [] -> Verifier_io.close_input ()
    | k::keys ->
      let _ = Verifier_io.run (RedBlack_Verifier_io.retrieve k ht) in
      real_verifier_io_redblack_retrieves ht keys
  in
  real_verifier_io_redblack_retrieves ht keys

let read_rdb_ins s =
  let chn = Printf.sprintf "%s/rdb_look1_%d.dat" data_folder s |> open_in_bin in
  let keys = read_keys num_rb_retrieves chn in
  close_in chn;
  keys;;

(* job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i), fun () ->
    Printf.printf "%d %d direct_prover_redblack_retrieves" i s;
    let t = read_dir_prover_rb_tree s in
    let keys = read_rdb_ins s in
    gc_collect ();
    measure_call ("direct_prover_redblack_retrieves "^(string_of_int s)) (dirprover_redblack_retrieves t) keys)
config_array; *)

job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i), fun () ->
    Printf.printf "%d %d dirprover_redblack_io_retrieves" i s;
    let t = read_dir_prover_rb_io_tree s in
    Hashtbl.add dir_io_hash s (snd t);
    let keys = read_rdb_ins s in
    gc_collect ();
    let file = Printf.sprintf "%s/proof_rb_look_d_%03d.dat" proof_folder s in
    measure_call ("dirprover_redblack_io_retrieves "^(string_of_int s)) (dirprover_redblack_io_retrieves file t) keys)
config_array;

job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i), fun () ->
    Printf.printf "%d %d dirprover_redblack_poly_io_retrieves" i s;
    let t = read_dir_prover_rb_poly_io_tree s in
    Hashtbl.add dir_poly_io_hash s (snd t);
    let keys = read_rdb_ins s in
    gc_collect ();
    let file = Printf.sprintf "%s/proof_rb_look_dp_%03d.dat" proof_folder s in
    measure_call ("dirprover_redblack_poly_io_retrieves "^(string_of_int s)) (dirprover_redblack_poly_io_retrieves file t) keys)
config_array;

job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i), fun () ->
    Printf.printf "%d %d dirprover_redblack_poly_mar_ser_io_retrieves" i s;
    let t = read_dir_prover_rb_poly_mar_ser_io_tree s in
    Hashtbl.add dir_poly_mar_ser_io_hash s (snd t);
    let keys = read_rdb_ins s in
    gc_collect ();
    let file = Printf.sprintf "%s/proof_rb_look_dpm_%03d.dat" proof_folder s in
    measure_call ("dirprover_redblack_poly_mar_ser_io_retrieves "^(string_of_int s)) (dirprover_redblack_poly_mar_ser_io_retrieves file t) keys)
config_array;

job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i), fun () ->
    Printf.printf "%d %d prover_io_redblack_retrieves" i s;
    let t = read_prover_io_rb_tree s in
    Hashtbl.add auth_io_hash s (Prover_io.get_hash t);
    let keys = read_rdb_ins s in
    gc_collect ();
    let file = Printf.sprintf "%s/proof_rb_look_dpma_%03d.dat" proof_folder s in
    measure_call ("prover_io_redblack_retrieves "^(string_of_int s)) (prover_io_redblack_retrieves file t) keys)
config_array;

(* job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i) + (2*n_configs), fun () ->
    Printf.printf "%d %d dirverifier_redblack_retrieves" i s;
    let t = read_dir_prover_rb_tree s in
    let keys = read_rdb_ins s in
    let ht = snd t in
    let proofs = dirprover_redblack_retrieves_keep t keys [] in
    gc_collect ();
    measure_call ("dirverifier_redblack_retrieves "^(string_of_int s)) (dirverifier_redblack_retrieves ht keys) proofs)
config_array; *)

job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i) + (2*n_configs), fun () ->
    Printf.printf "%d %d dirverifier_redblack_io_retrieves" i s;
    let file = Printf.sprintf "%s/proof_rb_look_d_%03d.dat" proof_folder s in
    let ht = Hashtbl.find dir_io_hash s in
    let keys = read_rdb_ins s in
    gc_collect ();
    measure_call ("dirverifier_redblack_io_retrieves "^(string_of_int s)) (dirverifier_redblack_io_retrieves file ht) keys)
config_array;

job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i) + (2*n_configs), fun () ->
    Printf.printf "%d %d dirverifier_redblack_poly_io_retrieves" i s;
    let file = Printf.sprintf "%s/proof_rb_look_dp_%03d.dat" proof_folder s in
    let ht = Hashtbl.find dir_poly_io_hash s in
    let keys = read_rdb_ins s in
    gc_collect ();
    measure_call ("dirverifier_redblack_poly_io_retrieves "^(string_of_int s)) (dirverifier_redblack_poly_io_retrieves file ht) keys)
config_array;

job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i) + (2*n_configs), fun () ->
    Printf.printf "%d %d dirverifier_redblack_poly_mar_ser_io_retrieves" i s;
    let file = Printf.sprintf "%s/proof_rb_look_dpm_%03d.dat" proof_folder s in
    let ht = Hashtbl.find dir_poly_mar_ser_io_hash s in
    let keys = read_rdb_ins s in
    gc_collect ();
    measure_call ("dirverifier_redblack_poly_mar_ser_io_retrieves "^(string_of_int s)) (dirverifier_redblack_poly_mar_ser_io_retrieves file ht) keys)
config_array;

job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i) + (2*n_configs), fun () ->
    Printf.printf "%d %d verifier_io_redblack_retrieves" i s;
    let file = Printf.sprintf "%s/proof_rb_look_dpma_%03d.dat" proof_folder s in
    let ht = Hashtbl.find auth_io_hash s in
    let keys = read_rdb_ins s in
    gc_collect ();
    measure_call ("verifier_io_redblack_retrieves "^(string_of_int s)) (verifier_io_redblack_retrieves file ht) keys)
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
