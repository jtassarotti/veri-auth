open Utils

module type EVIDENCE = sig
  type t_in
  type t_out
  val prepare: t_in -> t_out
  val serialize: t_out -> string
  val deserialize: string -> t_out option
end

type 'a evidence = (module EVIDENCE with type t_in = 'a)

module Pair (A: EVIDENCE) (B: EVIDENCE): (EVIDENCE with type t_in = A.t_in * B.t_in) = struct
  type t_in = A.t_in * B.t_in
  type t_out = A.t_out * B.t_out

  let prepare (a, b) =
    A.prepare a, B.prepare b
  
  let serialize (a, b) = Marshal.to_string (a, b) marshal_flags

  let deserialize s = Some (Marshal.from_string s 0)
end

module Quad (A: EVIDENCE) (B: EVIDENCE) (C: EVIDENCE) (D: EVIDENCE): (EVIDENCE with type t_in = A.t_in * B.t_in * C.t_in * D.t_in) = struct
  type t_in = A.t_in * B.t_in * C.t_in * D.t_in
  type t_out = A.t_out * B.t_out * C.t_out * D.t_out

  let prepare (a, b, c, d) =
    A.prepare a, B.prepare b, C.prepare c, D.prepare d
  
  let serialize o = Marshal.to_string o marshal_flags

  let deserialize s = Some (Marshal.from_string s 0)
end

module Sum (A: EVIDENCE) (B:EVIDENCE): (EVIDENCE with type t_in = [`left of A.t_in | `right of B.t_in]) = struct
  type t_in = [`left of A.t_in | `right of B.t_in]
  type t_out = [`left of A.t_out | `right of B.t_out]

  let prepare = function
    | `left a -> `left (A.prepare a)
    | `right b -> `right (B.prepare b)

  let serialize o = Marshal.to_string o marshal_flags

  let deserialize s = Some (Marshal.from_string s 0)
end

module String: (EVIDENCE with type t_in = string) = struct
  type t_in = string
  type t_out = string

  let prepare x = x
  
  let serialize o = Marshal.to_string o marshal_flags

  let deserialize s = Some (Marshal.from_string s 0)
end

module Int: (EVIDENCE with type t_in = int) = struct
  type t_in = int
  type t_out = int

  let prepare x = x
  
  let serialize o = Marshal.to_string o marshal_flags

  let deserialize s = Some (Marshal.from_string s 0)
end

let pair (type a) (type b) (module A : EVIDENCE with type t_in = a) 
  (module B : EVIDENCE with type t_in = b) 
  : (module EVIDENCE with type t_in = a * b) = 
    (module Pair(A)(B))

let quad (type a) (type b) (type c) (type d) 
  (module A : EVIDENCE with type t_in = a) (module B : EVIDENCE with type t_in = b) 
  (module C : EVIDENCE with type t_in = c) (module D : EVIDENCE with type t_in = d) 
  : (module EVIDENCE with type t_in = a * b * c * d) = 
    (module Quad(A)(B)(C)(D))
let sum (type a) (type b) (module A : EVIDENCE with type t_in = a) 
  (module B : EVIDENCE with type t_in = b)
  : (module EVIDENCE with type t_in = [`left of a | `right of b]) = 
    (module Sum(A)(B))
let string: (module EVIDENCE with type t_in = string) = (module String)
let int: (module EVIDENCE with type t_in = int) = (module Int)
