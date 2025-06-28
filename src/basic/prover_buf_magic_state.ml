(* This implements the Stateful Buffering/Heterogenous Reuse Buffering 
   optimization for the prover as specified in Section 6 of the paper. *)

open Auth
open Hash
open Utils

module Prover_buf_magic_state : sig
  include AUTHENTIKIT
  val get_hash : 'a auth -> string
  val run : 'a authenticated_computation -> (string list * 'a)
end = struct
  let cache: SSet.t ref = ref SSet.empty
  type proof_val = proof_value
  type proof_state = proof_stream
  type 'a auth = 'a * string
  type 'a authenticated_computation = proof_state -> (proof_state * 'a)
  let get_hash a = snd a

  let return a buf = (buf, a)
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

  let add_obj evi ah prf =
    let a, h = ah in
    let s = evi a in
    cache := set_add h (!cache);
    let prf' = s :: prf in
    prf'

  let unauth evi ah prf =
    let a, h = ah in
    if set_mem h !cache then
      (prf, a)
    else
      (add_obj evi ah prf, a)

  let run c =
    cache := set_empty ();
    let prf, res = c [] in
    (list_rev prf, res)

end
                          
