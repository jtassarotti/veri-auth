open Auth
open Proof
open Utils

module Verifier_marshal : sig
  include AUTHENTIKIT with
  type 'a authenticated_computation = proof_stream -> proof_stream * 'a
  and type 'a auth = string
  val run : 'a authenticated_computation -> string -> 'a
end = struct
  type proof_val = proof_value
  type proof_state = proof_stream
  type 'a authenticated_computation = proof_state -> proof_state * 'a
  type 'a auth = string

  let return a =
    fun pf -> pf, a

  let[@inline] bind c f prf_state =
    let prf_state', a = c prf_state in
    ((f[@inlined]) a) prf_state'

  (* let bind a = bind a *)

  module Authenticatable = struct
    include Authenticatable_marshal
    let auth =
      let module Auth: (EVIDENCE with type t_in = string) = (struct
        type t_in = string
        type t_out = string
      
        let prepare h = h
        
        let serialize o = Marshal.to_string o marshal_flags
      
        let deserialize s = Some (Marshal.from_string s 0)
      end) in
      (module Auth: EVIDENCE with type t_in = string)

  end
  open Authenticatable

  (* let deser evi = evi.deserialize *)
  (* let hash_json = hash_json *)

  let push_proof prf prf_state = prf :: prf_state

  let pop_proof prf_state = 
    match List.nth_opt prf_state 0 with
    | None -> None
    | Some h -> Some (h, List.tl prf_state)

  let[@inline] auth (type a') (evi: a' evidence) (a: a') =
    let module Evi = (val evi) in
    hash_json (Evi.serialize (Evi.prepare a))

  let[@inline] unauth (type a') (evi: a' evidence) h proof: proof_state * a' =
    match proof with
    | [] -> failwith "Proof failure"
    | p :: ps when hash_json p = h ->
       (let module Evi = (val evi) in
        match Evi.deserialize p with
        | None -> failwith "Proof failure"
        | Some a -> (ps, (Obj.magic a)))
    | _ -> failwith "Proof failure"

  (* let unauth a b = unauth a b *)

  let run c pf_s =
    let pf = Marshal.from_string pf_s 0 in
    (* print_string "verifier run"; print_newline (); *)
    let _, a = c pf in
    a

end
