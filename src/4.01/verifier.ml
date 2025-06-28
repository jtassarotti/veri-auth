(* This implements the default prover implementation as it appears in
   Bob Atkey's blog. It also serves as the implementation for the 
   Proof Accumulator optimization as specified in Section 6 of the paper. *)

open Auth
open Hash
open Utils

module Verifier : sig
  include AUTHENTIKIT with
  type 'a authenticated_computation = proof_stream -> (proof_stream * 'a)
  and type 'a auth = string
  val run : 'a authenticated_computation -> string -> 'a
end = struct
  type proof_val = proof_value
  type proof_state = proof_stream
  type 'a authenticated_computation = proof_stream -> (proof_stream * 'a)
  type 'a auth = string

  let return a = fun pf -> pf, a

  let bind c f =
    fun prf_state ->
      let prf_state', a = c prf_state in
      f a prf_state'

  module Authenticatable = struct
    include Authenticatable_base.Verifier

    let auth = string

  end
  open Authenticatable

  let push_proof prf prf_state = prf :: prf_state

  let pop_proof prf_state = 
    match try Some (List.nth prf_state 0) with Failure _ -> None with
    | None -> None
    | Some h -> Some (h, List.tl prf_state)

  let auth evi a =
    hash (evi.serialize a)

  let unauth evi h proof =
    match proof with
    | [] -> failwith "Expected proof object"
    | p :: ps when hash p = h ->
      begin match evi.deserialize p with
        | None -> failwith "Deserialization failure"
        | Some a -> (ps, a)
      end
    | _ -> failwith "hash check failed"

  let run c pf_s =
    let pf = Marshal.from_string pf_s 0 in
    let _, a = c pf in
    a

end
