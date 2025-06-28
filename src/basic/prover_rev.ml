(* This implements the Proof Accumulator optimization for the prover as 
   specified in Section 6 of the paper. *)

open Auth
open Hash
open Utils

module Prover_rev : sig
  include AUTHENTIKIT with
  type 'a authenticated_computation = proof_stream -> (proof_stream * 'a)
  val get_hash : 'a auth -> string
  val run : 'a authenticated_computation -> (string list * 'a)
end = struct
  type proof_val = proof_value
  type proof_state = proof_stream
  type 'a auth = 'a * string
  type 'a authenticated_computation = proof_stream -> (proof_stream * 'a)

  let get_hash (a, h) = h
  let return a buf = buf, a

  let bind c f buf =
    let (buf', a) = c buf in
    f a buf'

  module Authenticatable = struct
    include Authenticatable_base.Prover 
  end
  open Authenticatable

  let push_proof prf prf_state = prf :: prf_state
  
  let pop_proof prf_state = 
    match list_head prf_state with
    | None -> None
    | Some h -> Some (h, list_tail prf_state)

  let auth serializer a =
    (a, hash (serializer a))

  let unauth serializer ah buf =
    let a, h = ah in
    let s = serializer a in
    (s :: buf, a)

  let run c =
    let pf, res = c [] in
    (list_rev pf, res)
end
