(* This implements the Reuse Buffering optimization for the prover as 
   specified in Section 6 of the paper. *)

open Auth
open Hash
open Utils

module Prover_buf : sig
  include AUTHENTIKIT
  val get_hash : 'a auth -> string
  val run : 'a authenticated_computation -> (string list * 'a)
end = struct
  type proof_val = proof_value
  type proof_state = { prf : proof_stream; cache : SSet.t }
  type 'a auth = 'a * string
  type 'a authenticated_computation = proof_state -> (proof_state * 'a)

  let get_hash (a, h) = h
  let return a buf = (buf, a)
  let bind c f buf =
    let (buf', a) = c buf in
    f a buf'

  module Authenticatable = struct
    include Authenticatable_base.Prover
  end
  open Authenticatable

  let push_proof prf prf_state =
    { prf_state with prf = prf :: prf_state.prf }

  let pop_proof prf_state = 
    match list_head prf_state.prf with
    | None -> None
    | Some h -> Some (h, { prf_state with prf = list_tail prf_state.prf })

  let auth serializer a =
    (a, hash (serializer a))

  let add_obj evi ah pf =
    let a, h = ah in
    let prf, cache = pf.prf, pf.cache in
    let prf' = evi a :: prf in
    let cache' = set_add h cache in
    { prf = prf'; cache = cache'}

  let unauth evi ah pf =
    let a, h = ah in
    let prf, cache = pf.prf, pf.cache in
    if set_mem h cache then
      (pf, a)
    else
      (add_obj evi ah pf, a)

  let run c =
    let init_state = { prf = []; cache = set_empty () }  in
    let fin_state, res = c init_state in
    let prf, cache = fin_state.prf, fin_state.cache in
    (list_rev prf, res)

end
                          
