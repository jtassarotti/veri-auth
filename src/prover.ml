open Auth
open Proof
open Utils

module Prover : sig
  include AUTHENTIKIT with
  type 'a authenticated_computation = proof_stream -> (proof_stream * 'a)
  val get_hash : 'a auth -> string
  val run : 'a authenticated_computation -> (string * 'a)
end = struct
  type proof_val = proof_value
  type proof_state = proof_stream
  type 'a auth = 'a * string
  type 'a authenticated_computation = proof_stream -> (proof_stream * 'a)
  let get_hash (a, h) = h
  let[@inline] return a = fun buf_state -> (buf_state, a)

  let[@inline] bind ma f =
    fun buf_state ->
      let (buf_state', a) = (ma[@inlined]) buf_state in
      ((f[@inlined]) a) buf_state'

  module Authenticatable = struct
    include Authenticatable_base
    let auth =
      let serialize (a, h) = h 
      and deserialize _ = None
      in
      {serialize; deserialize }
      
  end
  open Authenticatable

  let push_proof prf prf_state = prf :: prf_state
  
  let pop_proof prf_state = 
    match try Some (List.nth prf_state 0) with Failure _ -> None with
    | None -> None
    | Some h -> Some (h, List.tl prf_state)

  let[@inline] auth evi a =
    (a, hash_json (evi.serialize a))

  let[@inline] unauth evi (a, h) =
    fun buf -> ((evi.serialize a) :: buf, a)

  let[@inline] run m =
    (* print_string "prover run"; print_newline (); *)
    let pf, res = m [] in
    let pf_s = Marshal.to_string (List.rev pf) marshal_flags in
    (* print_string "prover run done"; print_newline (); *)
    (pf_s, res)
end
