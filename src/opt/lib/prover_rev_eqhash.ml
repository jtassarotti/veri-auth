open Auth
open Hash
open Utils

module Prover_rev : sig
  include AUTHENTIKIT2
  val get_hash : 'a auth -> string
  val run : 'a authenticated_computation -> (string * 'a)
end = struct
  type proof_val = proof_value
  type proof_state = proof_stream
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

  let push_proof prf pf_stream = prf :: pf_stream
  
  let pop_proof pf_stream = 
    match try Some (List.nth pf_stream 0) with Failure _ -> None with
    | None -> None
    | Some h -> Some (h, List.tl pf_stream)

  let[@inline] auth evi a =
    (a, hash (evi a))

  let[@inline] unauth evi (a, h) =
    fun pf -> (evi a :: pf, a)

  let eqauth evi (a1, h1) (a2, h2) =
    fun buf -> (buf, h1=h2)

  let[@inline] run m =
    (* print_string "prover run"; print_newline (); *)
    let pf, res = m [] in
    let pf_s = Marshal.to_string (List.rev pf) marshal_flags in
    (* print_string "prover run done"; print_newline (); *)
    (pf_s, res)
end
