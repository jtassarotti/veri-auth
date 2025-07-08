(* Alternative authenticatable functions that use the OCaml Marshal serialization
   library. *)

open Utils
    
module Prover = struct
  type ('x, 'y) raw_evidence =
    { prepare : 'x -> 'y;
      serialize : 'y -> string; }

  type 'x evidence = T : ('x, 'y) raw_evidence -> 'x evidence

  let[@inline] raw_pair (a_s : ('ax, 'ay) raw_evidence) (b_s : ('bx, 'by) raw_evidence) :
    ('ax * 'bx, 'ay * 'by) raw_evidence =
    let[@inline] serialize x = Marshal.to_string x marshal_flags
    and[@inline] prepare (a, b) =
      let a' = a_s.prepare a in
      let b' = b_s.prepare b in
      (a', b')
    in { prepare; serialize }

  let[@inline] pair (a_s : 'a evidence) (b_s : 'b evidence) : ('a * 'b) evidence =
    match a_s, b_s with
    | T a_s', T b_s' ->
      T (raw_pair a_s' b_s')

  let[@inline] raw_trio a_s b_s c_s =
    let[@inline] serialize y = Marshal.to_string y marshal_flags
    and[@inline] prepare (a, b, c) =
      (a_s.prepare a, b_s.prepare b, c_s.prepare c)
    in { prepare; serialize }

  let[@inline] trio a_s b_s c_s =
    match a_s, b_s, c_s with
    | T a_s', T b_s', T c_s' ->
      T (raw_trio a_s' b_s' c_s')

  let[@inline] raw_quad a_s b_s c_s d_s =
    let[@inline] serialize y = Marshal.to_string y marshal_flags
    and[@inline] prepare (a, b, c, d) =
      (a_s.prepare a, b_s.prepare b, c_s.prepare c, d_s.prepare d)
    in { prepare; serialize }

  let[@inline] quad a_s b_s c_s d_s =
    match a_s, b_s, c_s, d_s with
    | T a_s', T b_s', T c_s', T d_s' ->
      T (raw_quad a_s' b_s' c_s' d_s')

  let[@inline] raw_list (a_s : ('ax, 'ay) raw_evidence) =
    let[@inline] serialize x = Marshal.to_string x marshal_flags
    and[@inline] prepare l = 
      let rec aux l l_ret = match l with
        | [] -> List.rev l_ret
        | h::t -> aux t ((a_s.prepare h) :: l_ret)
      in 
      aux l []
    in { prepare; serialize }

  let[@inline] list (a_s : 'a evidence) : ('a list) evidence =
    match a_s with
    | T a_s' ->
      T (raw_list a_s')

  let[@inline] raw_sum (a_s : ('ax, 'ay) raw_evidence) (b_s : ('bx, 'by) raw_evidence) =
    let[@inline] serialize y = Marshal.to_string y marshal_flags
    and[@inline] prepare x =
      match x with
      | `left a -> `left (a_s.prepare a)
      | `right b -> `right (b_s.prepare b)
    in { prepare; serialize }
      
  let[@inline] sum (a_s : 'a evidence) (b_s : 'b evidence) : [> `left of 'a | `right of 'b] evidence =
    match a_s, b_s with
    | T a_s', T b_s' ->
      T (raw_sum a_s' b_s')

  let[@inline] raw_option (a_s : ('ax, 'ay) raw_evidence) =
    let[@inline] serialize y = Marshal.to_string y marshal_flags
    and[@inline] prepare x =
      match x with
      | `left -> `left
      | `right a -> `right (a_s.prepare a)
    in { prepare; serialize }
      
  let[@inline] option (a_s : 'a evidence) : [> `left | `right of 'a] evidence =
    match a_s with
    | T a_s' ->
      T (raw_option a_s')

  let[@inline] bool : 'bool evidence =
    let[@inline] serialize y = Marshal.to_string y marshal_flags
    and[@inline] prepare x = x
    in T { prepare; serialize }

  let[@inline] string : 'string evidence =
    let[@inline] serialize y = Marshal.to_string y marshal_flags
    and[@inline] prepare x = x
    in T { prepare; serialize }

  let[@inline] int : 'int evidence =
    let[@inline] serialize y = Marshal.to_string y marshal_flags
    and[@inline] prepare x = x
    in T { prepare; serialize }
end

module Verifier = struct
  type 'x evidence =
  { serialize : 'x -> string;
    deserialize : string -> 'x option }

let[@inline] pair _ _ : ('a * 'b) evidence =
  let[@inline] serialize x = Marshal.to_string x marshal_flags in
  let[@inline] deserialize s = Some (Marshal.from_string s 0) in
  { serialize; deserialize }

let[@inline] trio _ _ _ : ('a * 'b * 'c) evidence =
  let[@inline] serialize x = Marshal.to_string x marshal_flags in
  let[@inline] deserialize s = Some (Marshal.from_string s 0) in
  { serialize; deserialize }

let[@inline] quad _ _ _ _ : ('a * 'b * 'c * 'd) evidence =
  let[@inline] serialize x = Marshal.to_string x marshal_flags in
  let[@inline] deserialize s = Some (Marshal.from_string s 0) in
  { serialize; deserialize }

let[@inline] list _ : ('a list) evidence =
  let[@inline] serialize x = Marshal.to_string x marshal_flags in
  let[@inline] deserialize s = Some (Marshal.from_string s 0) in
  { serialize; deserialize }

let[@inline] sum _ _ : [> `left of 'a | `right of 'b] evidence =
  let[@inline] serialize x = Marshal.to_string x marshal_flags in
  let[@inline] deserialize s = Some (Marshal.from_string s 0) in
  { serialize; deserialize }

let[@inline] option _ : [> `left | `right of 'a] evidence =
  let[@inline] serialize x = Marshal.to_string x marshal_flags in
  let[@inline] deserialize s = Some (Marshal.from_string s 0) in
  { serialize; deserialize }

let[@inline] bool : 'bool evidence =
  let[@inline] serialize x = Marshal.to_string x marshal_flags in
  let[@inline] deserialize s = Some (Marshal.from_string s 0) in
  { serialize; deserialize }

let[@inline] string : 'string evidence =
  let[@inline] serialize x = Marshal.to_string x marshal_flags in
  let[@inline] deserialize s = Some (Marshal.from_string s 0) in
  { serialize; deserialize }

let[@inline] int : 'int evidence =
  let[@inline] serialize x = Marshal.to_string x marshal_flags in
  let[@inline] deserialize s = Some (Marshal.from_string s 0) in
  { serialize; deserialize }
end