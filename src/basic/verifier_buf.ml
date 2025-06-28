(* This implements the Reuse Buffering optimization for the verifier as mentioned in 
   Section 6 of the paper. *)

open Auth
open Hash
open Utils

module Verifier_buf : sig
  include AUTHENTIKIT with
  type 'a auth = string
  val run : 'a authenticated_computation -> proof_stream -> 'a option
end = struct
  type proof_val = proof_value
  type proof_state = { prf : proof_stream; cache : string SMap.t }
  type 'a auth = string
  type 'a authenticated_computation = proof_state -> (proof_state * 'a) option

  let return a buf = Some (buf, a)

  let bind c f pf =
    match c pf with
    | None -> None
    | Some x ->
      let (pf', a) = x in 
      f a pf'

  module Authenticatable = struct
    include Authenticatable_base.Verifier

    let auth = string

  end
  open Authenticatable

  let push_proof a prf_state =
    let prf' = a :: prf_state.prf in
    { prf = prf'; cache = prf_state.cache }

  let pop_proof prf_state = 
    match list_head prf_state.prf with
    | None -> None
    | Some h -> 
      let prf' = list_tail prf_state.prf in
      let pf_state' = { prf = prf'; cache = prf_state.cache } in
      Some (h, pf_state')

  let auth evi a =
    hash (evi.serialize a)

  let unauth evi h pf =
    let serialize, deserialize = evi.serialize, evi.deserialize in
    let prf, cache = pf.prf, pf.cache in
    match map_lookup h cache with
    | None ->
      begin match list_head prf with
      | None -> None
      | Some p ->
        if hash p = h then
          match deserialize p with
          | None -> None
          | Some a ->
            let pf' = {prf = list_tail prf; cache = map_insert h p cache} in
            Some (pf', a)
        else None
      end
    | Some p ->
      match deserialize p with
      | None -> None
      | Some a -> Some (pf, a)

  let run c prf =
    let init_state = { prf = prf; cache = map_empty () }  in
    match (c init_state) with
    | Some v -> Some (snd v)
    | None -> None

end
