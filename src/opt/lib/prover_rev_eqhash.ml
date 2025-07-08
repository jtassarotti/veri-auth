open Auth
open Hash
open Utils
open Vrf

module Prover_rev : sig
  include AUTHENTIKIT2
  val get_hash : 'a auth -> string
  val run : 'a authenticated_computation -> (string * string * 'a)
end = struct
  type proof_val = proof_value
  type proof_state = { pf_stream: proof_stream; vrf_key: int array }
  type 'a auth = 'a * string
  type 'a authenticated_computation = proof_state -> (proof_state * 'a)
  let get_hash (a, h) = h
  let[@inline] return a = fun buf_state -> (buf_state, a)

  let[@inline] bind ma f =
    fun buf_state ->
      let (buf_state', a) = (ma[@inlined]) buf_state in
      ((f[@inlined]) a) buf_state'

  let ( let* ) = bind

  module Authenticatable = struct
    include Authenticatable_base.Prover
    
    let auth (a, h) = string h
      
  end
  open Authenticatable

  let push_proof prf prf_state = { prf_state with pf_stream = prf :: prf_state.pf_stream }
  
  let pop_proof prf_state = 
    match try Some (List.nth prf_state.pf_stream 0) with Failure _ -> None with
    | None -> None
    | Some h -> Some (h, { prf_state with pf_stream = List.tl prf_state.pf_stream })

  let[@inline] auth evi a =
    (a, hash (evi a))

  let[@inline] unauth evi (a, h) prf_state =
    ({ prf_state with pf_stream = evi a :: prf_state.pf_stream }, a)

  let eqauth evi (a1, h1) (a2, h2) prf_state =
    (prf_state, h1=h2)

  let randomize str prf_state =
    let key = prf_state.vrf_key in
    let random_s, proof = randomize_string key str in
    let proof_s = Marshal.to_string proof marshal_flags in
    ({ prf_state with pf_stream = random_s :: proof_s :: prf_state.pf_stream }, random_s)

  let[@inline] run m =
    (* print_string "prover run"; print_newline (); *)
    let pr_key, pub_key = get_keys () in
    let pf, res = m { pf_stream = []; vrf_key = pr_key } in
    let pf_s = Marshal.to_string (List.rev pf.pf_stream) marshal_flags in
    (* print_string "prover run done"; print_newline (); *)
    let pub_key_s = Marshal.to_string pub_key marshal_flags in
    (pf_s, pub_key_s, res)
end
