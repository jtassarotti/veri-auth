open Auth
open Proof
open Utils

module Verifier : sig
  include AUTHENTIKIT with
  type 'a authenticated_computation = proof_stream -> (proof_stream * 'a)
  and type 'a auth = string
  val run : 'a authenticated_computation -> string -> 'a
end = struct
  type proof_val = proof_value
  type proof_state = proof_stream
  type 'a authenticated_computation = proof_stream -> (proof_stream * 'a)
  type 'a auth = string

  let return a = fun pf -> pf, a

  let bind c f =
    fun prf_state ->
      let prf_state', a = c prf_state in
      f a prf_state'

  module Authenticatable = struct
    include Authenticatable_base

    let auth =
      let serialize h = h
      and deserialize s = Some s
      in
      { serialize; deserialize }

  end
  open Authenticatable

  let push_proof prf prf_state = prf :: prf_state

  let pop_proof prf_state = 
    match try Some(List.nth prf_state 0) with Failure _ -> None with
    | None -> None
    | Some h -> Some (h, List.tl prf_state)

  let auth evi a =
    hash_json (evi.serialize a)

  let unauth evi h proof =
    match proof with
    | [] -> failwith "Proof failure"
    | p :: ps when hash_json p = h ->
      (match evi.deserialize p with
        | None -> failwith "Proof failure"
        | Some a -> (ps, a))
    | _ -> failwith "Proof failure"

  let run c pf_s =
    let pf = Marshal.from_string pf_s 0 in
    (* print_string "verifier run"; print_newline (); *)
    let _, a = c pf in
    a

end
