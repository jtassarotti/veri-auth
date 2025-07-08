open Auth
open Hash

module IMap = Map.Make(struct type t = int let compare : int -> int -> int = compare end)
module SMap = Map.Make(struct type t = string let compare : string -> string -> int = compare end)

module Verifier_susp : sig
  include AUTHENTIKIT2
  val make_auth : string -> 'a auth
  val run : 'a authenticated_computation -> string -> 'a
end = struct
  type proof_val = proof_value
  type final_check_fn = unit -> bool
  type proof_state = 
    { pf_stream: proof_stream; checks: final_check_fn list }
  type 'a authenticated_computation =
    proof_state -> proof_state * 'a
  type suspension = | Tag of int | Hash of string
  type 'a auth = | Shallow of string | Suspension of suspension ref

  let counter: int ref = ref 0
  type finish_t = unit -> unit
  let susp_table: (int * finish_t) IMap.t ref = ref IMap.empty

  let increment_counter () =
    let a = !counter in
    counter := !counter + 1;
    a

  let make_auth s = Shallow s
  let return a = fun pf -> pf, a

  let bind c f =
    fun prf_state ->
    match c prf_state with
    | prf_state', a -> f a prf_state'

  let ( let* ) = bind

  let get_hash = function
    | Shallow h -> Some h
    | Suspension susp ->
      begin match !susp with
      | Hash h -> Some h
      | _ -> None
      end

  module Authenticatable = struct
    include Authenticatable_base.Verifier_susp

    let auth =
      let serialize = function
        | Shallow h -> ("A_"^h)
        | Suspension susp ->
          match !susp with
          | Tag _ -> failwith ("Serialization called on suspended value")
          | Hash h -> ("A_"^h)
      and deserialize pid count s = 
        if String.length s < 2 then None
        else 
          let tag = String.sub s 0 2 in
          if tag = "A_" then
            if String.length s == 2 then 
              Some (Suspension (ref (Tag pid)), count + 1)
            else 
              let s = String.sub s 2 ((String.length s)-2) in
              Some (Shallow s, count)
          else None
      and to_string () = "Auth"
      in { serialize; deserialize; to_string }

  end
  open Authenticatable

  let push_proof prf prf_state = {prf_state with pf_stream = prf :: prf_state.pf_stream}
  
  let pop_proof prf_state = 
    match try Some (List.nth prf_state.pf_stream 0) with Failure _ -> None with
    | None -> None
    | Some h -> Some (h, {prf_state with pf_stream = List.tl prf_state.pf_stream})

  let auth evi a = 
    Shallow (hash (evi.serialize a))

  let unauth evi a proof =
    let id = increment_counter () in
    match proof.pf_stream with
    | [] -> failwith "Expected a proof object"
    | p :: ps ->
      match evi.deserialize id 0 p with
      | None -> failwith "Deserialization failure"
      | Some (x, count) ->
        let finish () =
          let y = evi.serialize x in
          match a with
          | Shallow h -> 
            if h = hash y then ()
            else failwith "Hashes don't match"
          | Suspension susp ->
            match !susp with
            | Hash h ->
              if h = hash y then ()
              else failwith "Hashes don't match"
            | Tag pid ->
              let ctr, finish = IMap.find pid !susp_table in
              if ctr = 1 then begin
                susp_table := IMap.remove pid !susp_table;
                susp := Hash (hash y);
                finish ()
              end
              else begin
                susp := Hash (hash y);
                susp_table := IMap.add pid (ctr-1, finish) !susp_table
              end
        in
        if count = 0 then
          finish ()
        else
          susp_table := IMap.add id (count, finish) !susp_table;
        { proof with pf_stream = ps }, x

  let eqauth _ a1 a2 prf_state =
    match prf_state.pf_stream with
    | [] -> failwith "eqauth: Expected a prf_state object"
    | p :: ps ->
      match (Authenticatable.bool).deserialize 0 0 p with
      | None -> failwith "eqauth: Deserialization failure"
      | Some (res, _) ->
        let eq_check () = 
          match get_hash a1, get_hash a2 with
          | None, _ | _, None -> failwith "Unresolved hashes"
          | Some h1, Some h2 -> (h1 = h2) = res
        in
        { pf_stream = ps; checks = eq_check :: prf_state.checks }, res

  let rec eqauth_checks checks =
    match checks with
    | [] -> ()
    | check :: checks ->
      if check () then eqauth_checks checks else failwith "check failed"

  let run c pf_s =
    susp_table := IMap.empty;
    let pf = Marshal.from_string pf_s 0 in
    let init_state = { pf_stream = pf; checks = [] } in
    match c init_state with
    | proof_state, a ->
      eqauth_checks proof_state.checks; a

end
