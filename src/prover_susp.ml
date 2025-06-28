open Auth
open Proof
open Utils

module ISet = Set.Make(struct type t = int let compare : int -> int -> int = compare end)

module Prover_susp : sig
  include AUTHENTIKIT
  (* type 'a authenticated_computation = proof_stream -> (proof_stream * 'a) *)
  val get_hash : 'a auth -> string
  val run : 'a authenticated_computation -> (string * 'a)
end = struct
  type proof_val = proof_value
  type buf_value = (int -> proof_value)
  type proof_state = { pf_stream : proof_stream; buffer : (unit -> proof_value) list }
  (* Only composite objects can be of variant Merkle. 
     Any thing that the client may have will be of variant MerkleSusp. *)
  type 'a auth = | Merkle of 'a * string | MerkleSusp of bool ref * 'a * string
  type 'a authenticated_computation = proof_state -> (proof_state * 'a)

  let get_hash = function
    | Merkle (_, h) | MerkleSusp (_, _, h) -> h
  let return a buf_state = buf_state, a
  let bind ma f =
    fun buf_state ->
    let (buf_state', a) = ma buf_state in
    f a buf_state'

  module Authenticatable = struct
    open Authenticatable_base
    type 'a evidence = 
      { serialize : 'a -> proof_value;
        suspend : 'a -> 'a;
        unsuspend : 'a -> 'a }

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

    let pair f_a f_b =
      let serialize = pair_serialize f_a.serialize f_b.serialize
      and suspend = function
        | (a, b) -> (f_a.suspend a, f_b.suspend b)
      and unsuspend = function
        | (a, b) -> (f_a.unsuspend a, f_b.unsuspend b)
      in
      { serialize; suspend; unsuspend }

    let trio f_a f_b f_c =
      let serialize = trio_serialize f_a.serialize f_b.serialize f_c.serialize
      and suspend = function
        | (a, b, c) -> (f_a.suspend a, f_b.suspend b, f_c.suspend c)
      and unsuspend = function
        | (a, b, c) -> (f_a.unsuspend a, f_b.unsuspend b, f_c.unsuspend c)
      in
      { serialize; suspend; unsuspend }

    let quad f_a f_b f_c f_d =
      let serialize = quad_serialize f_a.serialize f_b.serialize f_c.serialize f_d.serialize
      and suspend = function
        | (a, b, c, d) -> (f_a.suspend a, f_b.suspend b, f_c.suspend c, f_d.suspend d)
      and unsuspend = function
        | (a, b, c, d) -> (f_a.unsuspend a, f_b.unsuspend b, f_c.unsuspend c, f_d.unsuspend d)
      in
      { serialize; suspend; unsuspend }

    let sum f_a f_b =
      let serialize = sum_serialize f_a.serialize f_b.serialize
      and suspend = function
        | `left a -> `left (f_a.suspend a)
        | `right b -> `right (f_b.suspend b)
      and unsuspend = function
        | `left a -> `left (f_a.unsuspend a)
        | `right b -> `right (f_b.unsuspend b)
      in
      { serialize; suspend; unsuspend }

    let string =
      let serialize = string.serialize
      and suspend a = a
      and unsuspend a = a in
      { serialize; suspend; unsuspend }

    let int =
      let serialize = int.serialize
      and suspend a = a
      and unsuspend a = a in
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
    MerkleSusp (ref true, unsusp_a, hash_json (evi.serialize unsusp_a))

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

  let rec flush_buf_stream buffer pf_stream =
    match buffer with
    | [] -> pf_stream
    | f::buffer -> flush_buf_stream buffer (f () :: pf_stream)

  let run m =
    let init_state = { pf_stream = []; buffer = [] }  in
    let fin_state, res = m init_state in
    let pf_stream' = flush_buf_stream fin_state.buffer [] in
    let pf_stream = Marshal.to_string ((List.rev fin_state.pf_stream) @ pf_stream') marshal_flags in
    (pf_stream, res)
end
