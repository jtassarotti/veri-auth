open Auth
open Proof

module SMap = Map.Make(struct type t = string let compare : string -> string -> int = compare end)
let cache: string SMap.t ref = ref SMap.empty

module Verifier_buf_magic_state : sig
  include AUTHENTIKIT with
      (*  with type 'a authenticated_computation = proof -> [`Ok of proof * 'a | `ProofFailure ] *)
            type 'a auth = string
  val run : 'a authenticated_computation -> string -> 'a
end = struct
  type proof_val = proof_value
  type proof_state = proof_stream
  type 'a auth = string
  type 'a authenticated_computation = proof_state -> [`Ok of proof_state * 'a | ` ProofFailure]

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

  let push_proof prf prf_state = prf :: prf_state

  let pop_proof prf_state = 
    match List.nth_opt prf_state 0 with
    | None -> None
    | Some h -> Some (h, List.tl prf_state)

  let auth evi a =
    hash_json (evi.serialize a)

  let unauth evi h pf =
    match Obj.magic (SMap.find_opt h (!cache)) with
    | None ->
       (match pf with
       | [] -> `ProofFailure
       | p :: ps when hash_json p = h ->
          (match evi.deserialize p with
          | None -> `ProofFailure
          | Some a -> 
            cache := SMap.add h (Obj.magic a) (!cache);
            `Ok (ps, a))
       | _ -> `ProofFailure)
    | Some a -> `Ok (pf, a)

  let run c pf_s =
    let pf = Marshal.from_string pf_s 0 in
    cache := SMap.empty;
    match (c pf) with
    | `Ok (_, a) -> a
    | _ -> failwith "Proof failure"

end
