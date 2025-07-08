open Auth
open Hash
open Utils
open Vrf

module Verifier : sig
  include AUTHENTIKIT2 with
  type 'a auth = string
  val make_auth : string -> 'a auth
  val run : 'a authenticated_computation -> string -> string -> 'a
end = struct
  type proof_val = proof_value
  type proof_state = { pf_stream: proof_stream; vrf_key: int array }
  type 'a authenticated_computation = proof_state -> (proof_state * 'a)
  type 'a auth = string

  let make_auth s = s
  let[@inline] return a = fun pf -> pf, a

  let[@inline] bind c f =
    fun prf_state ->
      let prf_state', a = (c[@inlined]) prf_state in
      ((f[@inlined]) a) prf_state'

  let ( let* ) = bind

  module Authenticatable = struct
    include Authenticatable_base.Verifier

    let auth = string

  end
  open Authenticatable

  let push_proof prf prf_state = { prf_state with pf_stream = prf :: prf_state.pf_stream }
  
  let pop_proof prf_state = 
    match try Some (List.nth prf_state.pf_stream 0) with Failure _ -> None with
    | None -> None
    | Some h -> Some (h, { prf_state with pf_stream = List.tl prf_state.pf_stream })

  let[@inline] auth evi a =
    hash (evi.serialize a)

  let[@inline] unauth evi h prf_state =
    match prf_state.pf_stream with
    | [] -> failwith "Proof failure"
    | p :: ps when hash p = h ->
      (match evi.deserialize p with
        | None -> failwith "Proof failure"
        | Some a -> ({ prf_state with pf_stream = ps }, a))
    | _ -> failwith "Proof failure"

  let eqauth _ h1 h2 prf_state = (prf_state, h1=h2)

  let randomize str prf_state =
    match prf_state.pf_stream with
    | [] -> failwith "Vrf proof failure"
    | random_s :: proof_s :: ps ->
      let proof = Marshal.from_string proof_s 0 in
      if verify_proof prf_state.vrf_key str proof then
        ({ prf_state with pf_stream = ps }, random_s)
      else
        failwith "Vrf proof failure"
    | _ -> failwith "Vrf proof failure"

  let run c pf_s pub_key_s =
    let pub_key = Marshal.from_string pub_key_s 0 in
    let pf = Marshal.from_string pf_s 0 in
    (* print_string "verifier run"; print_newline (); *)
    let _, a = c { pf_stream = pf; vrf_key = pub_key } in
    a

end
