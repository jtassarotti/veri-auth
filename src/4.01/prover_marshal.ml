(* This implements a prover that uses the authenticatable_marshal functions.
   This does not appear in the paper, or in our proofs, and is only used for 
   experiments. *)

open Auth
open Hash
open Utils

module Prover_marshal : sig
  include AUTHENTIKIT with
  type 'a authenticated_computation = proof_stream -> (proof_stream * 'a)
  val get_hash : 'a auth -> string
  val run : 'a authenticated_computation -> (string * 'a)
end = struct
  type proof_val = proof_value
  type proof_state = proof_stream
  type 'a auth = 'a * string
  type 'a authenticated_computation = proof_state -> (proof_state * 'a)
  let get_hash (a, h) = h
  let return a buf_state = (buf_state, a)
  let bind ma f =
    fun buf_state ->
      let (buf_state', a) = ma buf_state in
      f a buf_state'

  module Authenticatable = struct
    include Authenticatable_marshal.Prover
    let auth =
      let prepare (a, h) = h 
      and serialize y = Marshal.to_string y marshal_flags
      in
      T {prepare; serialize }
      
  end
  open Authenticatable

  let push_proof prf prf_state = prf :: prf_state
  
  let pop_proof prf_state = 
    match try Some (List.nth prf_state 0) with Failure _ -> None with
    | None -> None
    | Some h -> Some (h, List.tl prf_state)

  let auth (evi: 'a evidence) (a: 'a) =
    match evi with
    | T evi -> (a, hash (evi.serialize (evi.prepare a)))

  let unauth (evi: 'a evidence) (a, h) buf =
    match evi with
    | T evi -> ((evi.serialize (evi.prepare a)) :: buf, a)

  let run m =
    let pf, res = m [] in
    let pf_s = Marshal.to_string (List.rev pf) marshal_flags in
    (pf_s, res)
end
                          
