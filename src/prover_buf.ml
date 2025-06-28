open Auth
open Proof
open Utils

module SSet = Set.Make(struct type t = string let compare : string -> string -> int = compare end)

module Prover_buf : sig
  include AUTHENTIKIT
  val get_hash : 'a auth -> string
  val run : 'a authenticated_computation -> (string * 'a)
end = struct
  type proof_val = proof_value
  type proof_state = { pf_stream : proof_stream; cache : SSet.t }
  type 'a auth = 'a * string
  type 'a authenticated_computation = proof_state -> (proof_state * 'a)
  let get_hash (a, h) = h
  let return a buf = (buf, a)
  let bind ma f =
    fun buf ->
    let (buf', a) = ma buf in
    f a buf'

  module Authenticatable = struct
    include Authenticatable_base
    let auth =
      let serialize (a, h) = h 
      and deserialize _ = None
      in
      {serialize; deserialize }
      
  end
  open Authenticatable

  let push_proof a prf_state =
    let pf_stream' = a :: prf_state.pf_stream in
    { pf_stream = pf_stream'; cache = prf_state.cache }

  let pop_proof prf_state = 
    match List.nth_opt prf_state.pf_stream 0 with
    | None -> None
    | Some h -> 
      let pf_stream' = List.tl prf_state.pf_stream in
      let pf_state' = { pf_stream = pf_stream'; cache = prf_state.cache } in
      Some (h, pf_state')

  let auth evi a =
    (a, hash_json (evi.serialize a))

  let add_obj evi (a, h) buf =
    let pf_stream' = evi.serialize a :: buf.pf_stream in
    let cache' = SSet.add h buf.cache in
    { pf_stream = pf_stream'; cache = cache'}

  let unauth evi (a, h) buf =
    if SSet.mem h buf.cache then
      (buf, a)
    else
      (add_obj evi (a, h) buf, a)

  let run m =
    let init_state = { pf_stream = []; cache = SSet.empty }  in
    let fin_state, res = m init_state in
    let pf_s = Marshal.to_string (List.rev fin_state.pf_stream) marshal_flags in
    (* print_string "prover run done"; print_newline (); *)
    (pf_s, res)

end
                          
