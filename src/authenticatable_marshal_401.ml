open Utils
    
module Prover = struct
  type ('x, 'y) raw_evidence =
    { prepare : 'x -> 'y;
      serialize : 'y -> string; }

  type 'x evidence = T : ('x, 'y) raw_evidence -> 'x evidence

  let raw_pair (a_s : ('ax, 'ay) raw_evidence) (b_s : ('bx, 'by) raw_evidence) :
    ('ax * 'bx, 'ay * 'by) raw_evidence =
    let serialize x = Marshal.to_string x marshal_flags
    and prepare (a, b) =
      let a' = a_s.prepare a in
      let b' = b_s.prepare b in
      (a', b')
    in { prepare; serialize }

  let pair (a_s : 'a evidence) (b_s : 'b evidence) : ('a * 'b) evidence =
    match a_s, b_s with
    | T a_s', T b_s' ->
      T (raw_pair a_s' b_s')

  let raw_sum (a_s : ('ax, 'ay) raw_evidence) (b_s : ('bx, 'by) raw_evidence) =
    let serialize y = Marshal.to_string y marshal_flags
    and prepare x =
      match x with
      | `left a -> `left (a_s.prepare a)
      | `right b -> `right (b_s.prepare b)
    in { prepare; serialize }
      
  let sum (a_s : 'a evidence) (b_s : 'b evidence) : [> `left of 'a | `right of 'b] evidence =
    match a_s, b_s with
    | T a_s', T b_s' ->
      T (raw_sum a_s' b_s')

  let raw_quad a_s b_s c_s d_s =
    let serialize y = Marshal.to_string y marshal_flags
    and prepare (a, b, c, d) =
      (a_s.prepare a, b_s.prepare b, c_s.prepare c, d_s.prepare d)
    in { prepare; serialize }

  let quad a_s b_s c_s d_s =
    match a_s, b_s, c_s, d_s with
    | T a_s', T b_s', T c_s', T d_s' ->
      T (raw_quad a_s' b_s' c_s' d_s')

  let string : 'string evidence =
    let serialize y = Marshal.to_string y marshal_flags
    and prepare x = x
    in T { prepare; serialize }

  let int : 'int evidence =
    let serialize y = Marshal.to_string y marshal_flags
    and prepare x = x
    in T { prepare; serialize }
end

module Verifier = struct
  type 'x evidence =
  { serialize : 'x -> string;
    deserialize : string -> 'x option }

let pair _ _ : ('a * 'b) evidence =
  let serialize x = Marshal.to_string x marshal_flags in
  let deserialize s = Some (Marshal.from_string s 0) in
  { serialize; deserialize }

let sum _ _ : [> `left of 'a | `right of 'b] evidence =
  let serialize x = Marshal.to_string x marshal_flags in
  let deserialize s = Some (Marshal.from_string s 0) in
  { serialize; deserialize }

let quad _ _ _ _ : ('a * 'b * 'c * 'd) evidence =
  let serialize x = Marshal.to_string x marshal_flags in
  let deserialize s = Some (Marshal.from_string s 0) in
  { serialize; deserialize }

let string : 'string evidence =
  let serialize x = Marshal.to_string x marshal_flags in
  let deserialize s = Some (Marshal.from_string s 0) in
  { serialize; deserialize }

let int : 'int evidence =
  let serialize x = Marshal.to_string x marshal_flags in
  let deserialize s = Some (Marshal.from_string s 0) in
  { serialize; deserialize }
end