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


let rec list_serialize ser_a l = match l with
  | [] -> "Li"
  | h :: t -> 
    let s_h = ser_a h in
    let len_h = String.length s_h in
    "Li" ^ (string_of_int len_h) ^ "_" ^ (ser_a h) ^ (list_serialize ser_a t)

let rec list_deserialize deser_a s =
  if String.length s < 2 then None
  else if String.length s = 2 && s = "Li" then Some []
  else
    let tag, s = String.sub s 0 2, String.sub s 2 ((String.length s) - 2) in
    if tag = "Li" then
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
            match deser_a sa, list_deserialize deser_a sb with
            | Some a, Some b -> Some (a::b)
            | _, _ -> None
    else None


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


let option_serialize ser_a = function
  | `left -> "N_"
  | `right a -> "S_"^(ser_a a)

let option_deserialize deser_a s =
  if String.length s < 2 then None
  else let tag = String.sub s 0 2 in
  if tag = "N_" && String.length s = 2 then
    Some `left
  else if tag = "S_" then
    match deser_a (String.sub s 2 ((String.length s)-2)) with
    | None -> None
    | Some a -> Some (`right a)
  else None


let bool_serialize b = if b then "b_1" else "b_0"

let bool_deserialize s =
  if String.equal "b_1" s then Some true
  else if String.equal "b_0" s then Some false
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
  let list = list_serialize
  let sum = sum_serialize
  let option = option_serialize
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
    
  let list a_s =
    let serialize = list_serialize a_s.serialize
    and deserialize = list_deserialize a_s.deserialize
    in { serialize; deserialize }

  let sum a_s b_s =
    let serialize = sum_serialize a_s.serialize b_s.serialize
    and deserialize = sum_deserialize a_s.deserialize b_s.deserialize
    in { serialize; deserialize }

  let option a_s =
    let serialize = option_serialize a_s.serialize
    and deserialize = option_deserialize a_s.deserialize
    in { serialize; deserialize }

  let bool = { serialize=bool_serialize; deserialize=bool_deserialize }

  let int = { serialize=int_serialize; deserialize=int_deserialize }

  let string = { serialize=string_serialize; deserialize=string_deserialize }

end

module Prover_susp = struct
  type 'a evidence = 
    { serialize : 'a -> string;
      suspend : 'a -> 'a;
      unsuspend : 'a -> 'a }

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

  let list f_a =
    let serialize = list_serialize f_a.serialize in
    let rec suspend = function
      | [] -> []
      | h :: t -> f_a.suspend h :: suspend t
    in
    let rec unsuspend = function
      | [] -> []
      | h :: t -> f_a.unsuspend h :: unsuspend t
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

  let option f_a =
    let serialize = option_serialize f_a.serialize
    and suspend = function
      | `left -> `left
      | `right a -> `right (f_a.suspend a)
    and unsuspend = function
      | `left -> `left
      | `right a -> `right (f_a.unsuspend a)
    in
    { serialize; suspend; unsuspend }

  let bool =
    let serialize = bool_serialize
    and suspend a = a
    and unsuspend a = a in
    { serialize; suspend; unsuspend }

  let string =
    let serialize = string_serialize
    and suspend a = a
    and unsuspend a = a in
    { serialize; suspend; unsuspend }

  let int =
    let serialize = int_serialize
    and suspend a = a
    and unsuspend a = a in
    { serialize; suspend; unsuspend }
end

module Verifier_susp = struct
  type 'a evidence = 
    { serialize : 'a -> string;
      deserialize : int -> int -> string -> ('a * int) option;
      to_string : unit -> string }
  
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
    and to_string () = 
      "Pair(" ^ f_a.to_string () ^ ", " ^ f_b.to_string () ^ ")"
    in { serialize; deserialize; to_string }

  let trio f_a f_b f_c =
    let evi = pair f_a (pair f_b f_c) in
    let serialize (a, b, c) = evi.serialize (a, (b, c))
    and deserialize pid count s = match evi.deserialize pid count s with
      | None -> None
      | Some ((a, (b, c)), count) -> Some ((a, b, c), count)
    and to_string () =
      "Trio(" ^ f_a.to_string () ^ ", " ^ f_b.to_string () ^ ", " ^ f_c.to_string () ^ ")"
    in { serialize; deserialize; to_string }

  let quad f_a f_b f_c f_d =
    let evi = pair f_a (pair f_b (pair f_c f_d)) in
    let serialize (a, b, c, d) = evi.serialize (a, (b, (c, d)))
    and deserialize pid count s = match evi.deserialize pid count s with
      | None -> None
      | Some ((a, (b, (c, d))), count) -> Some ((a, b, c, d), count)
    and to_string () =
      "Quad(" ^ f_a.to_string () ^ ", " ^ f_b.to_string () ^ ", " ^ f_c.to_string () ^ ", " ^ f_d.to_string () ^ ")"
    in { serialize; deserialize; to_string }

  let list f_a =
    let serialize = list_serialize f_a.serialize in
    let rec deserialize pid count s = 
      if String.length s < 2 then None
      else if String.length s = 2 && s = "Li" then Some ([], 0)
      else
        let tag, s = String.sub s 0 2, String.sub s 2 ((String.length s) - 2) in
        if tag = "Li" then
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
                match f_a.deserialize pid count sa, deserialize pid count sb with
                | Some (h, hcount), Some (t, tcount) -> Some ((h::t), hcount + tcount)
                | _, _ -> None
        else None
    and to_string () =
      "List(" ^ f_a.to_string () ^ ")"
    in { serialize; deserialize; to_string }

  let sum f_a f_b =
    let serialize = sum_serialize f_a.serialize f_b.serialize
    and deserialize pid count s = 
      match sum_deserialize (f_a.deserialize pid count) (f_b.deserialize pid count) s with
      | Some (`left (a, count)) -> Some (`left a, count)
      | Some (`right (b, count)) -> Some (`right b, count)
      | _ -> None
    and to_string () =
      "Sum(" ^ f_a.to_string () ^ ", " ^ f_b.to_string () ^ ")"
    in { serialize; deserialize; to_string }

  let option f_a =
    let serialize = option_serialize f_a.serialize
    and deserialize pid count s = 
      match option_deserialize (f_a.deserialize pid count) s with
      | Some `left -> Some (`left, 0)
      | Some (`right (a, count)) -> Some (`right a, count)
      | _ -> None
    and to_string () =
      "Option(" ^ f_a.to_string () ^ ")"
    in { serialize; deserialize; to_string }

  let bool =
    let serialize = bool_serialize
    and deserialize _ count s = 
      match bool_deserialize s with
      | Some s -> Some (s, count)
      | None -> None
    and to_string () = "Bool"
    in { serialize; deserialize; to_string }

  let string =
    let serialize = string_serialize
    and deserialize _ count s = 
      match string_deserialize s with
      | Some s -> Some (s, count)
      | None -> None
    and to_string () = "String"
    in { serialize; deserialize; to_string }

  let int =
    let serialize = int_serialize
    and deserialize _ count s = 
      match int_deserialize s with
      | Some i -> Some (i, count)
      | None -> None
    and to_string () = "Int"
    in { serialize; deserialize; to_string }
  
end