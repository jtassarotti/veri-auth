open Auth
open Hash
open Utils

module ISet = Set.Make(struct type t = int let compare : int -> int -> int = compare end)

module Prover_susp : sig
  include AUTHENTIKIT
  (* type 'a authenticated_computation = proof_stream -> (proof_stream * 'a) *)
  val get_hash : 'a auth -> string
  val run : 'a authenticated_computation -> (string * 'a)
end = struct
  type proof_val = proof_value
  type proof_state = { pf_stream : proof_stream; buffer : (unit -> proof_value) list }
  (* Only composite objects can be of variant Merkle. 
     Any thing that the client may have will be of variant MerkleSusp. *)
  type 'a auth = | Merkle of 'a * string | MerkleSusp of bool ref * bool ref * 'a * string
  type 'a authenticated_computation = proof_state -> (proof_state * 'a)

  let get_hash = function
    | Merkle (_, h) | MerkleSusp (_, _, _, h) -> h
  let return a buf_state = buf_state, a
  let bind ma f =
    fun buf_state ->
    let (buf_state', a) = ma buf_state in
    f a buf_state'

  module Authenticatable = struct
    include Authenticatable_base.Prover_susp

    let auth =
      let serialize = function
        | MerkleSusp (b, _, a, h) -> 
          if !b then "A_" else ("A_"^h)
        | Merkle (a, h) -> ("A_"^h)
      and suspend = function
        | Merkle (a, h) -> MerkleSusp (ref false, ref false, a, h)
        | MerkleSusp (b, _, a, h) -> failwith "Suspending suspended value"
      and unsuspend = function
        | MerkleSusp (b, r, a, h) -> r := true; Merkle (a, h)
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
    MerkleSusp (ref false, ref false, unsusp_a, hash (evi.serialize unsusp_a))

  let unauth evi a prf_state =
    let un_a = match a with
      | MerkleSusp (b, r, a, _) ->
        if !r then failwith "This value has been serialized earlier. It should not be suspended.";
        b := true; a
      | Merkle (a, _) -> a (* Never reached *)
    in
    let susp_un_a = evi.suspend un_a in
    let finish () = evi.serialize susp_un_a in
    let prf_state = { prf_state with buffer = finish :: prf_state.buffer } in
    (prf_state, susp_un_a)

  let rec flush_buf_stream buffer pf_stream =
    match buffer with
    | [] -> pf_stream
    | f::buffer -> flush_buf_stream buffer (f () :: pf_stream)

  let run m =
    let init_state = { pf_stream = []; buffer = [] }  in
    let fin_state, res = m init_state in
    let pf_stream' = flush_buf_stream fin_state.buffer [] in
    let pf_stream = (List.rev fin_state.pf_stream) @ pf_stream' in
    let pf_s = Marshal.to_string pf_stream marshal_flags in
    (pf_s, res)
end
