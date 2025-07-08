open Auth
open Hash
open Utils
open Vrf

module Prover_susp : sig
  include AUTHENTIKIT2
  (* type 'a authenticated_computation = proof_stream -> (proof_stream * 'a) *)
  val get_hash : 'a auth -> string
  val run : 'a authenticated_computation -> (string * string * 'a)
end = struct
  type proof_val = proof_value
  type proof_state = 
  { pf_stream : proof_stream; buffer : (unit -> proof_value) list; vrf_key : int array }
  (* Only composite objects can be of variant Merkle. 
     Any thing that the client may have will be of variant MerkleSusp. *)
  type 'a auth = | Merkle of 'a * string | MerkleSusp of bool ref * 'a * string
  type 'a authenticated_computation = proof_state -> (proof_state * 'a)

  (* let initial_id = Int.max_int
  let counter: int ref = ref 0
  let increment_counter () =
    let a = !counter in
    counter := !counter + 1;
    a *)

  let get_hash = function
    | Merkle (_, h) | MerkleSusp (_, _, h) -> h
  let return a buf_state = buf_state, a
  let bind ma f =
    fun buf_state ->
    let (buf_state', a) = ma buf_state in
    f a buf_state'

  let ( let* ) = bind

  module Authenticatable = struct
    include Authenticatable_base.Prover_susp

    let auth =
      let serialize = function
        | MerkleSusp (b, a, h) -> 
          if !b then "A_" else ("A_"^h)
        | Merkle (a, h) -> ("A_"^h)
      and suspend = function
        | Merkle (a, h) -> MerkleSusp (ref false, a, h)
        | MerkleSusp (b, a, h) -> failwith "Suspending suspended value"
      and unsuspend = function
        | MerkleSusp (_, a, h) -> Merkle (a, h)
        | Merkle _ -> failwith "auth called with Merkle variant type"
      in
      { serialize; suspend; unsuspend }

  end
  open Authenticatable

  let push_proof a prf_state = 
    { prf_state with pf_stream = a :: prf_state.pf_stream }
  
  let pop_proof prf_state = 
    match List.nth_opt prf_state.pf_stream 0 with
    | None -> None
    | Some h ->
      let pf_stream' = List.tl prf_state.pf_stream in
      let pf_state' = { prf_state with pf_stream = pf_stream' } in
      Some (h, pf_state')

  let auth evi a =
    let unsusp_a = evi.unsuspend a in
    MerkleSusp (ref true, unsusp_a, hash (evi.serialize unsusp_a))

  let unauth evi a prf_state =
    let un_a = match a with
      | MerkleSusp (b, a, _) ->
        b := true; a
      | Merkle (a, _) -> a
    in
    let susp_un_a = evi.suspend un_a in
    let finish () = evi.serialize susp_un_a in
    let prf_state = { prf_state with buffer = finish :: prf_state.buffer } in
    (prf_state, susp_un_a)

  let eqauth evi a1 a2 prf_state =
    let res = (get_hash a1) = (get_hash a2) in
    let finish () = (Authenticatable.bool).serialize res in
    { prf_state with buffer = finish :: prf_state.buffer }, res

  let randomize str prf_state =
    let key = prf_state.vrf_key in
    let random_s, proof = randomize_string key str in
    let proof_s = Marshal.to_string proof marshal_flags in
    let finish_s () = random_s in
    let finish_p () = proof_s in
    ({ prf_state with buffer = finish_p :: finish_s :: prf_state.buffer }, random_s)

  let rec flush_buf_stream buffer pf_stream =
    match buffer with
    | [] -> pf_stream
    | f::buffer -> flush_buf_stream buffer (f () :: pf_stream)

  let run m =
    let pr_key, pub_key = get_keys () in
    let init_state = { pf_stream = []; buffer = []; vrf_key = pr_key }  in
    let fin_state, res = m init_state in
    let pf_stream' = flush_buf_stream fin_state.buffer [] in
    let pf_s = Marshal.to_string ((List.rev fin_state.pf_stream) @ pf_stream') marshal_flags in
    let pub_key_s = Marshal.to_string pub_key marshal_flags in
    (pf_s, pub_key_s, res)
end
