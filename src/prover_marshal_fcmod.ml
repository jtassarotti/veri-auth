open Auth
open Proof
open Utils
open Authenticatable_marshal

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
  let[@inline] bind ma f =
    fun buf_state ->
    let (buf_state', a) = (ma[@inlined]) buf_state in
    (f[@inlined]) a buf_state'

  module Authenticatable = struct
    include Authenticatable_marshal
    let auth (type a) =
      let module Auth: (EVIDENCE with type t_in = a * string) = (struct
        type t_in = a * string
        type t_out = string
      
        let prepare (a, h) = h
        
        let serialize o = Marshal.to_string o marshal_flags
      
        let deserialize s = Some (Marshal.from_string s 0)
      end) in
      (module Auth: EVIDENCE with type t_in = a * string)
      
  end
  open Authenticatable

  (* let ser evi = evi.serialize *)
  (* let hash_json = hash_json *)

  let push_proof prf prf_state = prf :: prf_state
  
  let pop_proof prf_state = 
    match List.nth_opt prf_state 0 with
    | None -> None
    | Some h -> Some (h, List.tl prf_state)

  let[@inline] auth (type a') (evi: a' evidence) (a: a') =
    let module Evi = (val evi) in
    (a, hash_json (Evi.serialize (Evi.prepare a)))

  let[@inline] unauth (type a') (evi: a' evidence) (a, h) buf =
    let module Evi = (val evi) in
    ((Evi.serialize (Evi.prepare a)) :: buf, a)

  (* let unauth a b = unauth a b *)

  let run m =
    (* print_string "prover run"; print_newline (); *)
    let pf, res = m [] in
    let pf_s = Marshal.to_string (List.rev pf) marshal_flags in
    (* print_string "prover run done"; print_newline (); *)
    (pf_s, res)
end
                          
