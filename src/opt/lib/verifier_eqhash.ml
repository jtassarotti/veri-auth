open Auth
open Hash
open Utils

module Verifier : sig
  include AUTHENTIKIT2 with
  type 'a auth = string
  val make_auth : string -> 'a auth
  val run : 'a authenticated_computation -> string -> 'a
end = struct
  type proof_val = proof_value
  type proof_state = proof_stream
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

  let push_proof prf pf_stream = prf :: pf_stream
  
  let pop_proof pf_stream = 
    match try Some (List.nth pf_stream 0) with Failure _ -> None with
    | None -> None
    | Some h -> Some (h, List.tl pf_stream)

  let[@inline] auth evi a =
    hash (evi.serialize a)

  let[@inline] unauth evi h proof =
    match proof with
    | [] -> failwith "Proof failure"
    | p :: ps when hash p = h ->
      (match evi.deserialize p with
        | None -> failwith "Proof failure"
        | Some a -> (ps, a))
    | _ -> failwith "Proof failure"

  let eqauth _ h1 h2 proof = (proof, h1=h2)

  let run c pf_s =
    let pf = Marshal.from_string pf_s 0 in
    (* print_string "verifier run"; print_newline (); *)
    let _, a = c pf in
    a

end
