(** The naive verifier implementation as it appears in Bob Atkey's blog. *)
open Auth
open Hash
open Utils

module Verifier : sig
  include AUTHENTIKIT with
  type 'a auth = string
  val run : 'a authenticated_computation -> proof_stream -> 'a option
end = struct
  type proof_state = proof_stream
  type 'a authenticated_computation = proof_stream -> (proof_stream * 'a) option
  type 'a auth = string

  let return a proof = Some (proof, a)

  let bind c f prfs =
    match c prfs with
    | None -> None
    | Some x ->
      let prfs', a = x in
      f a prfs'

  module Authenticatable = struct
    include Authenticatable_base.Verifier
  end
  open Authenticatable

  let auth evi a =
    hash (evi.serialize a)

  let unauth a_scheme h proof =
    let serialize, deserialize = a_scheme.serialize, a_scheme.deserialize in
    match list_head proof with
    | None -> None
    | Some p ->
      if hash p = h then
        match deserialize p with
          | None -> None
          | Some a -> Some (list_tail proof, a)
      else None

  let run c prf =
    match c prf with
    | None -> None
    | Some v -> Some (snd v)

  type proof_val = proof_value
  
  let push_proof prf prf_state = prf :: prf_state
  let pop_proof prf_state = 
    match list_head prf_state with
    | None -> None
    | Some h -> Some (h, list_tail prf_state)  
end
