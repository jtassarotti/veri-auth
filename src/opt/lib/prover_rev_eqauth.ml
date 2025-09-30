open Auth
open Hash
open Utils
open Vrf

module Prover_rev : sig
  include AUTHENTIKIT2
  val get_hash : 'a auth -> string
  val init : int array -> unit
  val run : 'a authenticated_computation -> (string * 'a)
end = struct
  type proof_val = proof_value
  type proof_state = proof_stream
  type 'a auth = 'a * string
  type 'a authenticated_computation = proof_state -> (proof_state * 'a)
  
  type random = int64

  let vrf_key: int array ref = ref [||]

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

  let push_proof prf pf_stream = prf :: pf_stream
  
  let pop_proof pf_stream = 
    match try Some (List.nth pf_stream 0) with Failure _ -> None with
    | None -> None
    | Some h -> Some (h, List.tl pf_stream)

  let[@inline] auth evi a =
    (a, hash (evi a))

  let[@inline] unauth evi (a, h) pf_stream =
    (evi a :: pf_stream, a)

  let eqauth (a1, h1) (a2, h2) pf_stream =
    (pf_stream, h1=h2)

  let randomize evi obj pf_stream =
    let str = evi obj in
    let random, proof = randomize_string !vrf_key str in
    let random_s = Bytes.to_string random in
    let rand_int = Bytes.get_int64_le random 0 in
    let proof_s = Marshal.to_string proof marshal_flags in
    let prf_val = Authenticatable.(pair string string) (random_s, proof_s) in
    (prf_val :: pf_stream, rand_int)

  let init key = vrf_key := key

  let[@inline] run m =
    let pf, res = m [] in
    let pf_s = Marshal.to_string (List.rev pf) marshal_flags in
    (pf_s, res)
end
