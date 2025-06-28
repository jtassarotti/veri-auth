type 'a evidence =
  { serialize : 'a -> string;
    deserialize : string -> 'a option }


let pair_serialize ser_a ser_b (a, b) =
  let s1 = ser_a a in
  let s2 = ser_b b in
  (string_of_int (String.length s1))^"_"^s1^s2

let pair_deserialize deser_a deser_b s =
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
        match deser_a sa, deser_b sb with
        | Some a, Some b -> Some (a, b)
        | _, _ -> None


let pair a_s b_s = 
  let serialize = pair_serialize a_s.serialize b_s.serialize
  and deserialize = pair_deserialize a_s.deserialize b_s.deserialize
  in
  { serialize; deserialize }


let trio_serialize ser_a ser_b ser_c (a, b, c) =
  pair_serialize ser_a (pair_serialize ser_b ser_c) (a, (b, c))

let trio_deserialize deser_a deser_b deser_c s =
  match pair_deserialize deser_a (pair_deserialize deser_b deser_c) s with
  | None -> None
  | Some (a, (b, c)) -> Some (a, b, c)

let trio a_s b_s c_s =
  let serialize = trio_serialize a_s.serialize b_s.serialize c_s.serialize
  and deserialize = trio_deserialize a_s.deserialize b_s.deserialize c_s.deserialize
  in { serialize; deserialize }


let quad_serialize ser_a ser_b ser_c ser_d (a, b, c, d) =
  trio_serialize ser_a ser_b (pair_serialize ser_c ser_d) (a, b, (c, d))

let quad_deserialize deser_a deser_b deser_c deser_d s =
  match trio_deserialize deser_a deser_b (pair_deserialize deser_c deser_d) s with
  | None -> None
  | Some (a, b, (c, d)) -> Some (a, b, c, d)

let quad a_s b_s c_s d_s =
  let serialize = quad_serialize a_s.serialize b_s.serialize c_s.serialize d_s.serialize
  and deserialize = quad_deserialize a_s.deserialize b_s.deserialize c_s.deserialize d_s.deserialize
  in { serialize; deserialize }


let sum_serialize ser_a ser_b = function
  | `left a -> "L_"^(ser_a a)
  | `right b -> "R_"^(ser_b b)

let sum_deserialize deser_a deser_b s =
  if String.length s < 2 then None
  else let tag = String.sub s 0 2 in
  if tag = "L_" then
    match deser_a (String.sub s 2 ((String.length s)-2)) with
    | None -> None
    | Some a -> Some (`left a)
  else if tag = "R_" then
    match deser_b (String.sub s 2 ((String.length s)-2)) with
    | None -> None
    | Some b -> Some (`right b)
  else None

let sum a_s b_s =
  let serialize = sum_serialize a_s.serialize b_s.serialize
  and deserialize = sum_deserialize a_s.deserialize b_s.deserialize
  in { serialize; deserialize }


let string =
  let serialize s = "s_"^s
  and deserialize s = 
    if String.length s < 2 then None
    else let tag = String.sub s 0 2 in
    if tag = "s_" then
      Some (String.sub s 2 ((String.length s)-2))
    else None
  in { serialize; deserialize }

  
let int =
  let serialize s = "i_"^(string_of_int s)
  and deserialize s = 
    if String.length s < 3 then None
    else let tag = String.sub s 0 2 in
    if tag = "i_" then
      try Some (int_of_string (String.sub s 2 ((String.length s)-2))) with Failure _ -> None
    else None
  in { serialize; deserialize }
