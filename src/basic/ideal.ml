(** The "no-op" Authentikit *)
open Auth

module Ideal : sig
  include AUTHENTIKIT
  val run : 'a authenticated_computation -> 'a
end = struct
  type proof_state = unit
  type 'a auth = 'a
  type 'a authenticated_computation = unit -> 'a

  let return a _ = a
  let bind a f _ = f (a ()) ()

  module Authenticatable = struct
    type 'a evidence = 'a -> unit
    let auth a = ()
    let pair a b (a, b) = ()
    let sum a_serializer b_serializer x = ()
    let bool b = ()
    let string s = ()
    let int i = ()
  end

  let auth _ a = a
  let unauth _ a _ = a

  let run m = m ()

  type proof_val = unit
  
  let push_proof a b = b
  let pop_proof a = Some ((), a)  
end
