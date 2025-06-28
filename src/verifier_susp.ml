open Auth
open Proof

module IMap = Map.Make(struct type t = int let compare : int -> int -> int = compare end)

module Verifier_susp : sig
  include AUTHENTIKIT
  val make_auth : string -> 'a auth
  val run : 'a authenticated_computation -> string -> 'a
end = struct
  type proof_val = proof_value
  type type_finish = unit -> unit
  type proof_state = proof_stream
  type 'a authenticated_computation =
    proof_state -> proof_state * 'a
  type suspension = | Tag of int | Hash of string
  type 'a auth = | Shallow of string | Suspension of suspension ref

  let counter: int ref = ref 0
  let susp_table: (int * type_finish) IMap.t ref = ref IMap.empty

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

  module Authenticatable = struct
    open Authenticatable_base
    type 'a evidence = 
      { serialize : 'a -> string;
        deserialize : int -> int -> proof_value -> ('a * int) option }

    let auth =
      let serialize = function
        | Shallow h -> ("A_"^h)
        | Suspension susp ->
          match !susp with
          | Tag _ -> failwith ("Serialization called on suspended value")
          | Hash h -> ("A_"^h)
      and deserialize pid count s = 
        if String.length s < 2 then None
        else let tag = String.sub s 0 2 in
        if tag = "A_" then
          if String.length s == 2 then Some (Suspension (ref (Tag pid)), count + 1)
          else let s = String.sub s 2 ((String.length s)-2) in
          Some (Shallow s, count)
        else None
      in { serialize; deserialize }

    let pair f_a f_b =
      let serialize = pair_serialize f_a.serialize f_b.serialize
      and deserialize pid count s = 
        match try Some (String.index_from s 0 '_') with Invalid_argument _ -> None with
        | None -> None
        | Some i ->
          let tag, s = String.sub s 0 i, String.sub s (i+1) ((String.length s) - (i+1)) in
          match try Some (int_of_string tag) with Failure _ -> None with
          | None -> None
          | Some i ->
            if i < 0 then None
            else if i > String.length s then None
            else
              let sa = String.sub s 0 i in
              let sb = String.sub s i ((String.length s) - i) in
              match f_a.deserialize pid count sa with
              | Some (a, count) -> begin match f_b.deserialize pid count sb with
                | Some (b, count) -> Some ((a, b), count)
                | None -> None
                end
              | None -> None
      in { serialize; deserialize }

    let trio f_a f_b f_c =
      let evi = pair f_a (pair f_b f_c) in
      let serialize (a, b, c) = evi.serialize (a, (b, c))
      and deserialize pid count s = match evi.deserialize pid count s with
        | None -> None
        | Some ((a, (b, c)), count) -> Some ((a, b, c), count)
      in { serialize; deserialize }

    let quad f_a f_b f_c f_d =
      let evi = pair f_a (pair f_b (pair f_c f_d)) in
      let serialize (a, b, c, d) = evi.serialize (a, (b, (c, d)))
      and deserialize pid count s = match evi.deserialize pid count s with
        | None -> None
        | Some ((a, (b, (c, d))), count) -> Some ((a, b, c, d), count)
      in { serialize; deserialize }

    let sum f_a f_b =
      let serialize = sum_serialize f_a.serialize f_b.serialize
      and deserialize pid count s = 
        match sum_deserialize (f_a.deserialize pid count) (f_b.deserialize pid count) s with
        | Some (`left (a, count)) -> Some (`left a, count)
        | Some (`right (a, count)) -> Some (`right a, count)
        | _ -> None
      in { serialize; deserialize }

    let string =
      let serialize = string.serialize
      and deserialize _ count s = 
        match string.deserialize s with
        | Some s -> Some (s, count)
        | None -> None
      in { serialize; deserialize }

    let int =
      let serialize = int.serialize
      and deserialize _ count s = 
        match int.deserialize s with
        | Some i -> Some (i, count)
        | None -> None
      in { serialize; deserialize }

  end
  open Authenticatable

  let push_proof a pf_stream = a :: pf_stream
  
  let pop_proof pf_stream = 
    match pf_stream with
    | [] -> None
    | h::pf_stream -> Some (h, pf_stream)

  let auth evi a = 
    Shallow (hash_json (evi.serialize a))

  let unauth evi a proof =
    let id = increment_counter () in
    match proof with
    | [] -> failwith "Expected a proof object"
    | p :: ps ->
      match evi.deserialize id 0 p with
      | None -> failwith "Deserialization failure"
      | Some (x, count) ->
        let finish () =
          let y = evi.serialize x in
          match a with
          | Shallow h -> 
            if h = hash_json y then ()
            else failwith "Hashes don't match"
          | Suspension susp ->
            match !susp with
            | Hash h ->
              if h = hash_json y then ()
              else failwith "Hashes don't match"
            | Tag pid ->
              let ctr, finish = IMap.find pid !susp_table in
              if ctr = 1 then begin
                susp_table := IMap.remove pid !susp_table;
                susp := Hash (hash_json y);
                finish ()
              end
              else begin
                susp := Hash (hash_json y);
                susp_table := IMap.add pid (ctr-1, finish) !susp_table
              end
        in
        if count = 0 then
          finish ()
        else
          susp_table := IMap.add id (count, finish) !susp_table;
        ps, x

  let run c pf_s =
    let init_state = Marshal.from_string pf_s 0 in
    match c init_state with
    | proof_state, a ->
      assert (IMap.is_empty !susp_table); a

end
