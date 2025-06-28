(* Basic functions for instantiating an authenticatable module for an
   Authentikit module type. The auth evidence type is instantiated by
   individual modules. *)

let pair_serialize ser_a ser_b v =
  let s1 = ser_a (fst v) in
  let s2 = ser_b (snd v) in
  (string_of_int (String.length s1))^"_"^s1^s2

(* This doesn't do the "string_of_int alen <> alen_str" check *)            
let pair_deserialize deser_a deser_b s =
  match try Some (String.index_from s 0 '_') with Invalid_argument _ -> None with
  | None -> None
  | Some i ->
    let alen_str = String.sub s 0 i in
    let is_alen = try Some (int_of_string alen_str) with Failure _ -> None in
    match is_alen with
    | None -> None
    | Some alen ->
      if alen < 0 then None 
      else
        let slen = String.length s in
        if slen - i - 1 < alen then None 
        else
          let s1 = String.sub s (i + 1) alen in
          let s2 = String.sub s (i + 1 + alen) (slen - (i + 1 + alen)) in
          let is_v1 = deser_a s1 in
          match is_v1 with
          | None -> None
          | Some v1 ->
            let is_v2 = deser_b s2 in
            match is_v2 with
            | Some v2 -> Some (v1, v2)
            | None -> None


let trio_serialize ser_a ser_b ser_c (a, b, c) =
  pair_serialize ser_a (pair_serialize ser_b ser_c) (a, (b, c))

let trio_deserialize deser_a deser_b deser_c s =
  match pair_deserialize deser_a (pair_deserialize deser_b deser_c) s with
  | None -> None
  | Some (a, (b, c)) -> Some (a, b, c)


let quad_serialize ser_a ser_b ser_c ser_d (a, b, c, d) =
  trio_serialize ser_a ser_b (pair_serialize ser_c ser_d) (a, b, (c, d))

let quad_deserialize deser_a deser_b deser_c deser_d s =
  match trio_deserialize deser_a deser_b (pair_deserialize deser_c deser_d) s with
  | None -> None
  | Some (a, b, (c, d)) -> Some (a, b, c, d) 


let sum_serialize ser_a ser_b v = match v with
  | `left a -> "L_"^(ser_a a)
  | `right b -> "R_"^(ser_b b)

let sum_deserialize deser_a deser_b s =
  if String.length s < 2 then None
  else 
    let tag = String.sub s 0 2 in
    let rest = String.sub s 2 ((String.length s)-2) in
    if tag = "L_" then
      let mA = deser_a rest in
      match mA with
      | None -> None
      | Some a -> Some (`left a)
    else if tag = "R_" then
      let mB = deser_b rest in
      match mB with
      | None -> None
      | Some b -> Some (`right b)
    else None


let bool_serialize b = if b then "b_1" else "b_0"

let bool_deserialize s =
  if "b_1" = s then Some true
  else if "b_0" = s then Some false
  else None


let string_serialize s = "s_"^s

let string_deserialize s = 
  if String.length s < 2 then None
  else 
    let tag = String.sub s 0 2 in
    let rest = String.sub s 2 ((String.length s)-2) in
    if tag = "s_" then Some (rest)
    else None


let int_serialize s = "i_"^(string_of_int s)

(* This doesn't do the "string_of_int z = rest" check *)
let int_deserialize s = 
  if String.length s < 3 then None
  else let tag = String.sub s 0 2 in
  if tag = "i_" then
    try Some (int_of_string (String.sub s 2 ((String.length s)-2))) with Failure _ -> None
  else None


module Prover = struct
  type 'a evidence = 'a -> string

  let pair = pair_serialize
  let trio = trio_serialize
  let quad = quad_serialize
  let sum = sum_serialize
  let bool = bool_serialize
  let string = string_serialize
  let int = int_serialize
end

module Verifier = struct
  type 'a evidence =
  { serialize : 'a -> string;
    deserialize : string -> 'a option }

  let pair a_s b_s = 
    let serialize = pair_serialize a_s.serialize b_s.serialize
    and deserialize = pair_deserialize a_s.deserialize b_s.deserialize
    in
    { serialize; deserialize }

  let trio a_s b_s c_s =
    let serialize = trio_serialize a_s.serialize b_s.serialize c_s.serialize
    and deserialize = trio_deserialize a_s.deserialize b_s.deserialize c_s.deserialize
    in { serialize; deserialize }

  let quad a_s b_s c_s d_s =
    let serialize = quad_serialize a_s.serialize b_s.serialize c_s.serialize d_s.serialize
    and deserialize = quad_deserialize a_s.deserialize b_s.deserialize c_s.deserialize d_s.deserialize
    in { serialize; deserialize }

  let sum a_s b_s =
    let serialize = sum_serialize a_s.serialize b_s.serialize
    and deserialize = sum_deserialize a_s.deserialize b_s.deserialize
    in { serialize; deserialize }

  let bool = { serialize=bool_serialize; deserialize=bool_deserialize }

  let int = { serialize=int_serialize; deserialize=int_deserialize }

  let string = { serialize=string_serialize; deserialize=string_deserialize }

end
