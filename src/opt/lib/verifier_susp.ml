open Auth
open Hash

module IMap = Map.Make(struct type t = int let compare : int -> int -> int = compare end)

module Verifier_susp : sig
  include AUTHENTIKIT
  val make_auth : string -> 'a auth
  val run : 'a authenticated_computation -> string -> 'a
end = struct
  type proof_val = proof_value
  type type_finish = unit -> unit
  type proof_state = { pf_stream: proof_stream; counter: int }
  type 'a authenticated_computation =
    proof_state -> proof_state * 'a
  type suspension = | Tag of int | Hash of string
  type 'a auth = | Shallow of string | Suspension of suspension ref

  let susp_table: (int * type_finish) IMap.t ref = ref IMap.empty

  let make_auth s = Shallow s
  let return a = fun pf -> pf, a

  let bind c f =
    fun prf_state ->
    match c prf_state with
    | prf_state', a -> f a prf_state'

  module Authenticatable = struct
    include Authenticatable_base.Verifier_susp

    let auth =
      let serialize = function
        | Shallow h -> ("A_"^h)
        | Suspension susp ->
          match !susp with
          | Tag _ -> failwith ("Serialization called on suspended value")
          | Hash h -> ("A_"^h)
      and deserialize pid s = 
        if String.length s < 2 then None
        else 
          let tag = String.sub s 0 2 in
          if tag = "A_" then
            if String.length s == 2 then 
              Some (Suspension (ref (Tag pid)), 1)
            else 
              let s = String.sub s 2 ((String.length s)-2) in
              Some (Shallow s, 0)
          else None
      and to_string () = "Auth"
      in { serialize; deserialize; to_string }

  end
  open Authenticatable

  let push_proof a pf_state = { pf_state with pf_stream = a :: pf_state.pf_stream }
  
  let pop_proof pf_state = 
    match pf_state.pf_stream with
    | [] -> None
    | h::pf_stream -> Some (h, { pf_state with pf_stream = pf_stream })

  let auth evi a = 
    (* TODO: create a suspended auth here? see which cases might call auth on a suspended value. *)
    Shallow (hash (evi.serialize a))

  let unauth evi a proof =
    match proof.pf_stream with
    | [] -> failwith "Expected a proof object"
    | p :: ps ->
      let id = proof.counter in
      match evi.deserialize id p with
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
        { pf_stream = ps; counter = id + 1}, x

  let run c pf_s =
    let pf = Marshal.from_string pf_s 0 in
    let init_state = { pf_stream = pf; counter = 0} in
    match c init_state with
    | _, a -> a

end
