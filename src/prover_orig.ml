open Auth
open Proof
open Utils

module Prover_orig : sig
  include AUTHENTIKIT with
  type 'a authenticated_computation = unit -> (proof_stream * 'a)
  val get_hash : 'a auth -> string
  val run : 'a authenticated_computation -> (string * 'a)
end = struct
  type proof_val = proof_value
  type proof_state = proof_stream
  type 'a auth = 'a * string
  type 'a authenticated_computation = unit -> (proof_state * 'a)
  let get_hash (a, h) = h
  let return a () = ([], a)
  let bind ma f =
    fun _ ->
    let (buf_state, a) = ma () in
    let (buf_state', b) = f a () in
    (buf_state @ buf_state', b)

  module Authenticatable = struct
    include Authenticatable_base
    let auth =
      let serialize (a, h) = h 
      and deserialize _ = None
      in
      {serialize; deserialize }
      
  end
  open Authenticatable

  let push_proof prf prf_state = prf_state @ [prf]
  
  let pop_proof prf_state = (* unused for prover *)
    match List.nth_opt prf_state 0 with
    | None -> None
    | Some h -> Some (h, List.tl prf_state)

  let auth evi a =
    (a, hash_json (evi.serialize a))

  let unauth evi (a, h) buf =
    ([evi.serialize a], a)

  let run m =
    (* print_string "prover run"; print_newline (); *)
    let pf, a = m () in
    (Marshal.to_string pf marshal_flags, a)
    (* print_string "prover run done"; print_newline (); *)
end
                          
