(* Ideal authentikit type module. *)

open Auth

module Ideal : sig
  include AUTHENTIKIT with
    type 'a authenticated_computation = 'a
end = struct
  type proof_val = unit
  type proof_state = unit
  type 'a auth = 'a
  type 'a authenticated_computation = 'a

  let return a = a
  let bind a f = f a

  module Authenticatable = struct
    type 'a evidence = 'a -> unit
    let auth a = ()
    let pair a b (a, b) = ()
    let trio a b c (a, b, c) = ()
    let quad a b c d (a, b, c, d) = ()
    let sum a_serializer b_serializer x = ()
    let bool b = ()
    let string s = ()
    let int i = ()
  end

  let push_proof a b = b
  let pop_proof a = Some ((), a)
  let auth e a = a
  let unauth e a = a
end
