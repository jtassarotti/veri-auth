(** The naive prover implementation as it appears in Bob Atkey's blog. *)
open Auth
open Hash
open Utils

module Prover : sig
  include AUTHENTIKIT with
  type 'a authenticated_computation = unit -> (proof_stream * 'a)
  val get_hash : 'a auth -> string
  val run : 'a authenticated_computation -> (string list * 'a)
end = struct
  type proof_state = proof_stream
  type 'a auth = 'a * string
  type 'a authenticated_computation = unit -> (proof_state * 'a)

  let get_hash (a, h) = h
  let return a _ = ([], a)
  let bind c f _ =
    let (prf, a) = c () in
    let (prf', b) = f a () in
    (prf @ prf', b)

  module Authenticatable = struct
    include Authenticatable_base.Prover
  end
  open Authenticatable

  let auth serializer a =
    (a, hash (serializer a))

  let unauth serializer ah buf =
    let a, h = ah in
    let s = serializer a in
    ([s], a)

  let run c = 
    let r = c () in
    r

  type proof_val = proof_value

  let push_proof prf prf_state = prf_state @ [prf]  
  let pop_proof prf_state = (* unused for prover *)
    match list_head prf_state with
    | None -> None
    | Some h -> Some (h, list_tail prf_state)  
    
end
                          
