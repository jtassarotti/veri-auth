open Auth
open Proof

module SMap = Map.Make(struct type t = string let compare : string -> string -> int = compare end)

module Verifier_buf : sig
  include AUTHENTIKIT with
      (*  with type 'a authenticated_computation = proof -> [`Ok of proof * 'a | `ProofFailure ] *)
            type 'a auth = string
  val run : 'a authenticated_computation -> string -> 'a
end = struct
  type proof_val = proof_value
  type proof_state = { pf_stream : proof_stream; cache : string SMap.t }
  type 'a auth = string
  type 'a authenticated_computation = proof_state -> [`Ok of proof_state * 'a | `ProofFailure]

  let return a =
    fun pf -> `Ok (pf, a)

  let bind c f =
    fun prfs ->
    match c prfs with
    | `ProofFailure -> `ProofFailure
    | `Ok (prfs', a) -> f a prfs'

  module Authenticatable = struct
    include Authenticatable_base

    let auth =
      let serialize h = h
      and deserialize s = Some s
      in
      { serialize; deserialize }

  end
  open Authenticatable

  (* TODO: Not changing cache here *)
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
    hash_json (evi.serialize a)

  let unauth evi h pf =
    match SMap.find_opt h pf.cache with
    | None ->
       (match pf.pf_stream with
       | [] -> `ProofFailure
       | p :: ps when hash_json p = h ->
          (match evi.deserialize p with
          | None -> `ProofFailure
          | Some a -> `Ok ({pf_stream = ps; cache = SMap.add h p pf.cache}, a))
       | _ -> `ProofFailure)
    | Some p ->
       match evi.deserialize p with
       | None -> `ProofFailure
       | Some a -> `Ok (pf, a)

  let run c pf_s =
    let pf = Marshal.from_string pf_s 0 in
    let init_state = { pf_stream = pf; cache = SMap.empty }  in
    match (c init_state) with
    | `Ok (_, a) -> a
    | _ -> failwith "Proof failure"

end
