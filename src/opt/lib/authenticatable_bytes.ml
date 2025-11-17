let uscore_chr = Char.chr 95 (* _ *)
let list_chr = Char.chr 108 (* l *)
let sing_chr = Char.chr 103 (* g *)
let left_chr = Char.chr 76 (* L *)
let right_chr = Char.chr 82 (* R *)
let str_chr = Char.chr 83 (* S *)
let int_chr = Char.chr 73 (* I *)
let int64_chr = Char.chr 105 (* i *)
let bytes_chr = Char.chr 98 (* b *)
let none_chr = Char.chr 78 (* N *)
let some_chr = Char.chr 83 (* S *)
let true_char = Char.chr 84 (* T *)
let false_char = Char.chr 70 (* F *)

(* TODO: 
  1. Everyting can be optimized even more if we reduce calls to Bytes.sub, Bytes.cat
  2. Check if string conversion operations can be replaced by unsafe versions *)

let pair_serialize ser_a ser_b v =
  let b1 = ser_a (fst v) in
  let b2 = ser_b (snd v) in
  let b = Bytes.create 2 in
  Bytes.set_uint16_le b (Bytes.length b1) 0;
  Bytes.cat b1 b2 |> Bytes.cat b

let pair_deserialize deser_a deser_b b =
  let blen = Bytes.length b in
  if blen < 2 then None else
  let alen = Bytes.get_uint16_le b 0 in
  if blen - 2 < alen then None 
  else
    let b1 = Bytes.sub b 2 alen in
    let b2 = Bytes.sub b (2 + alen) (blen - (2 + alen)) in
    let v1_opt = deser_a b1 in
    match v1_opt with
    | None -> None
    | Some v1 ->
      let v2_opt = deser_b b2 in
      match v2_opt with
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

(* Can be optimized using some tricks *)
let list_serialize ser_a l = 
  let rec aux l = match l with
    | [] -> Bytes.empty
    | h :: [] -> Bytes.cat (Bytes.make 1 sing_chr) (ser_a h)
    | h :: t ->
      let b_h = ser_a h in
      let len_h = Bytes.length b_h in
      let b = Bytes.create 2 in
      Bytes.set_uint16_le b (Bytes.length b_h) 0;
      Bytes.cat b (aux t)
  in
  let b = Bytes.make 1 list_chr in
  Bytes.cat b (aux l)

let list_deserialize deser_a b =
  let blen = Bytes.length b in
  if blen = 0 || not (Bytes.get b 0 |> Char.equal list_chr) then None
  else
    let rec aux i =
      if blen = i then Some []
      else 
        if Bytes.get b i |> Char.equal sing_chr then
          let bh = (Bytes.sub b (i+1) (blen - (i+1))) in
          match deser_a bh with
          | None -> None
          | Some a -> Some [a]
        else
          let hlen = Bytes.get_uint16_le b i in
          if (blen - i - 2) < hlen then None
          else
            let bh = Bytes.sub b (i+2) hlen in
            match deser_a bh with
            | None -> None
            | Some h ->
              match aux (i+2+hlen) with
              | None -> None
              | Some t -> Some (h::t)
    in
    aux 1


let sum_serialize ser_a ser_b v = match v with
  | `left a -> Bytes.cat (Bytes.make 1 left_chr) (ser_a a)
  | `right b -> Bytes.cat (Bytes.make 1 right_chr) (ser_a b)

let sum_deserialize deser_a deser_b b =
  let blen = Bytes.length b in
  if blen < 2 then None
  else
    let tag = Bytes.get b 0 in
    let rest = Bytes.sub b 1 (blen-1) in
    if Char.equal tag left_chr then
      match deser_a rest with
      | None -> None
      | Some a -> Some (`left a)
    else if Char.equal tag right_chr then
      match deser_b rest with
      | None -> None
      | Some b -> Some (`right b)
    else None


let option_serialize ser_a = function
  | `left -> Bytes.make 1 none_chr
  | `right a -> Bytes.cat (Bytes.make 1 some_chr) (ser_a a)

let option_deserialize deser_a b =
  let blen = Bytes.length b in
  if blen < 1 then None
  else 
    if Bytes.get b 0 |> Char.equal none_chr then Some `left
    else if Bytes.get b 0 |> Char.equal some_chr then
      match deser_a (Bytes.sub b 1 (blen - 1)) with
      | None -> None
      | Some a -> Some (`right a)
    else None

    
let bool_serialize b = 
  if b then Bytes.make 1 true_char else Bytes.make 1 false_char

let bool_deserialize b =
  if Bytes.equal (Bytes.make 1 true_char) b then Some true
  else if Bytes.equal (Bytes.make 1 false_char) b then Some false
  else None


let string_serialize s = 
  Bytes.cat (Bytes.make 1 str_chr) (Bytes.of_string s)

let string_deserialize b =
  let blen = Bytes.length b in
  if blen < 1 then None
  else
    let tag = Bytes.get b 0 in
    let rest = Bytes.sub b 1 (blen-1) |> Bytes.to_string in
    if Char.equal tag str_chr then Some (rest) else None


let int_serialize i =
  let b = Bytes.make 3 int_chr in
  Bytes.set_uint16_le b 1 i; b

(* This doesn't do the "string_of_int z = rest" check *)
let int_deserialize b =
  if Bytes.length b <> 3 then None
  else
    if not (Bytes.get b 0 |> Char.equal int_chr) then None
    else
      Some (Bytes.get_uint16_le b 1)


let bytes_serialize b = Bytes.cat (Bytes.make 1 bytes_chr) b

let bytes_deserialize b =
  let blen = Bytes.length b in
  if not (Bytes.get b 1 |> Char.equal bytes_chr) then None
  else
    Some (Bytes.sub b 1 (blen-1))


let int64_serialize i = 
  let b = Bytes.make 9 int64_chr in
  Bytes.set_int64_le b 0 i; b

let int64_deserialize b =
  if Bytes.length b <> 9 then None
  else 
    if not (Bytes.get b 0 |> Char.equal int64_chr) then None
    else
      Some (Bytes.get_int64_le b 1)


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
  let int64 = int64_serialize
  let bytes = bytes_serialize
  let random = int64
end

module Verifier = struct
  type 'a evidence =
    { serialize : 'a -> bytes;
      deserialize : bytes -> 'a option }

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

  let int64 = { serialize=int64_serialize; deserialize=int64_deserialize }

  let string = { serialize=string_serialize; deserialize=string_deserialize }

  let bytes = { serialize=bytes_serialize; deserialize=bytes_deserialize }

  let random = int64

end

(* module Prover_susp = struct
  type 'a evidence = 
    { serialize : 'a -> bytes;
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

  let int64 =
    let serialize = int64_serialize
    and suspend a = a
    and unsuspend a = a in
    { serialize; suspend; unsuspend }

  let bytes =
    let serialize = bytes_serialize
    and suspend a = a
    and unsuspend a = a in
    { serialize; suspend; unsuspend }

  let random = int64

end

module Verifier_susp = struct
  type 'a evidence = 
    { serialize : 'a -> bytes;
      deserialize : int -> bytes -> ('a * int) option;
      to_string : unit -> bytes }
  
  let pair f_a f_b =
    let serialize = pair_serialize f_a.serialize f_b.serialize
    and deserialize pid s = 
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
            match f_a.deserialize pid sa with
            | Some (a, count_a) -> begin match f_b.deserialize pid sb with
              | Some (b, count_b) -> Some ((a, b), count_a + count_b)
              | None -> None
              end
            | None -> None
    and to_string () = 
      "Pair(" ^ f_a.to_string () ^ ", " ^ f_b.to_string () ^ ")"
    in { serialize; deserialize; to_string }

  let trio f_a f_b f_c =
    let evi = pair f_a (pair f_b f_c) in
    let serialize (a, b, c) = evi.serialize (a, (b, c))
    and deserialize pid s = match evi.deserialize pid s with
      | None -> None
      | Some ((a, (b, c)), count) -> Some ((a, b, c), count)
    and to_string () =
      "Trio(" ^ f_a.to_string () ^ ", " ^ f_b.to_string () ^ ", " ^ f_c.to_string () ^ ")"
    in { serialize; deserialize; to_string }

  let quad f_a f_b f_c f_d =
    let evi = pair f_a (pair f_b (pair f_c f_d)) in
    let serialize (a, b, c, d) = evi.serialize (a, (b, (c, d)))
    and deserialize pid s = match evi.deserialize pid s with
      | None -> None
      | Some ((a, (b, (c, d))), count) -> Some ((a, b, c, d), count)
    and to_string () =
      "Quad(" ^ f_a.to_string () ^ ", " ^ f_b.to_string () ^ ", " ^ f_c.to_string () ^ ", " ^ f_d.to_string () ^ ")"
    in { serialize; deserialize; to_string }

  let list f_a =
    let serialize = list_serialize f_a.serialize in
    let rec deserialize pid s = 
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
                match f_a.deserialize pid sa, deserialize pid sb with
                | Some (h, hcount), Some (t, tcount) -> Some ((h::t), hcount + tcount)
                | _, _ -> None
        else None
    and to_string () =
      "List(" ^ f_a.to_string () ^ ")"
    in { serialize; deserialize; to_string }

  let sum f_a f_b =
    let serialize = sum_serialize f_a.serialize f_b.serialize
    and deserialize pid s = 
      match sum_deserialize (f_a.deserialize pid) (f_b.deserialize pid) s with
      | Some (`left (a, count)) -> Some (`left a, count)
      | Some (`right (b, count)) -> Some (`right b, count)
      | _ -> None
    and to_string () =
      "Sum(" ^ f_a.to_string () ^ ", " ^ f_b.to_string () ^ ")"
    in { serialize; deserialize; to_string }

  let option f_a =
    let serialize = option_serialize f_a.serialize
    and deserialize pid s = 
      match option_deserialize (f_a.deserialize pid) s with
      | Some `left -> Some (`left, 0)
      | Some (`right (a, count)) -> Some (`right a, count)
      | _ -> None
    and to_string () =
      "Option(" ^ f_a.to_string () ^ ")"
    in { serialize; deserialize; to_string }

  let bool =
    let serialize = bool_serialize
    and deserialize _ s = 
      match bool_deserialize s with
      | Some s -> Some (s, 0)
      | None -> None
    and to_string () = "Bool"
    in { serialize; deserialize; to_string }

  let string =
    let serialize = string_serialize
    and deserialize _ s = 
      match string_deserialize s with
      | Some s -> Some (s, 0)
      | None -> None
    and to_string () = "String"
    in { serialize; deserialize; to_string }

  let int =
    let serialize = int_serialize
    and deserialize _ s = 
      match int_deserialize s with
      | Some i -> Some (i, 0)
      | None -> None
    and to_string () = "Int"
    in { serialize; deserialize; to_string }

  let int64 =
    let serialize = int64_serialize
    and deserialize _ s = 
      match int64_deserialize s with
      | Some i -> Some (i, 0)
      | None -> None
    and to_string () = "Int64"
    in { serialize; deserialize; to_string }

  let bytes =
    let serialize = bytes_serialize
    and deserialize _ s = 
      match bytes_deserialize s with
      | Some i -> Some (i, 0)
      | None -> None
    and to_string () = "Bytes"
    in { serialize; deserialize; to_string }

  let random = int64
  
end *)