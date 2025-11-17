type slice1D = int * bytes

let empty_slice: slice1D = 0, Bytes.empty
let get_slice (b: bytes): slice1D = Bytes.length b, b
let get_slice_len ((l, b): slice1D) = l
let get_slice_byt ((l, b): slice1D) = b

let write_st conv write =
  fun b st -> conv st |> write b
let read_st conv read =
  fun b -> read b |> Option.map (fun (t, b) -> conv t, b)

let int_to_bytes (i: int): bytes =
  let b = Bytes.create 2 in
  Bytes.set_uint16_le b 0 i; b

let int64_to_bytes (i: int64): bytes =
  let b = Bytes.create 8 in
  Bytes.set_int64_le b 0 i; b

type 'a evidence =
  { write: bytes -> 'a -> bytes; 
    read: bytes -> ('a * bytes) option }

let read_int (b : bytes): (int * bytes) option =
  if Bytes.length b < 2 then None else
  let i = Bytes.get_int16_le b 0 in
  let rem = Bytes.sub b 2 ((Bytes.length b)-2) in
  Some (i, rem)

let write_int (b : bytes) (i : int): bytes =
  let l = Bytes.length b in
  let b = Bytes.extend b 0 2 in
  Bytes.set_int16_le b l i; b

let int_evi: int evidence = 
  { write = write_int; read = read_int }

let read_int64 (b: bytes): (int64 * bytes) option =
  if Bytes.length b < 8 then None else
  let i = Bytes.get_int64_le b 0 in
  let rem = Bytes.sub b 8 ((Bytes.length b)-8) in
  Some (i, rem)

let write_int64 (b: bytes) (i: int64): bytes =
  let l = Bytes.length b in
  let b = Bytes.extend b 0 8 in
  Bytes.set_int64_le b l i; b

let int64_evi: int64 evidence = 
  { write = write_int64; read = read_int64 }


let read_bool (b: bytes): (bool * bytes) option =
  if Bytes.length b < 1 then None else
  let i = Bytes.get_int8 b 0 in
  let rem = Bytes.sub b 1 ((Bytes.length b)-1) in
  if i = 0 then Some (false, rem)
  else if i = 1 then Some (true, rem)
  else None

let write_bool (by: bytes) (bo: bool): bytes =
  let l = Bytes.length by in
  let by = Bytes.extend by 0 1 in
  begin if bo then Bytes.set_int8 by l 1
  else Bytes.set_int8 by l 0 end; by

let bool_evi: bool evidence =
  { write = write_bool; read = read_bool }


let read_bytes (i: int) (b: bytes): (bytes * bytes) option =
  let l = Bytes.length b in
  if l < i then None else Some (Bytes.sub b 0 i, Bytes.sub b i (l-i))

let write_bytes (b : bytes) (b1 : bytes): bytes =
  Bytes.cat b b1

let byte_evi: bytes evidence =
  { write = write_bytes; read = read_bytes 1 }


let read_sum (evi1: 'a evidence) (evi2: 'b evidence) (b: bytes)
  : ([ `left of 'a | `right of 'b ] * bytes) option =
  let deser1, deser2 = evi1.read, evi2.read in
  match read_bool b with
  | None -> None
  | Some (bo, rem) ->
    if bo then
      match deser1 rem with
      | None -> None
      | Some (a, rem) -> Some (`left a, rem)
    else
      match deser2 rem with
      | None -> None
      | Some (b, rem) -> Some (`right b, rem)

let write_sum (evi1: 'a evidence) (evi2: 'b evidence) (b: bytes) 
  (v: [ `left of 'a | `right of 'b ]): bytes =
  match v with
  | `left a -> 
    let b = write_bool b true in
    evi1.write b a
  | `right a -> 
    let b = write_bool b true in
    evi2.write b a

let sum_evi (evi1: 'a evidence) (evi2: 'b evidence): ([ `left of 'a | `right of 'b ]) evidence =
  { write = write_sum evi1 evi2; read = read_sum evi1 evi2 }


let read_pair (evi1: 'a evidence) (evi2: 'b evidence) (b: bytes)
  : (('a * 'b) * bytes) option =
  let deser1, deser2 = evi1.read, evi2.read in
  match deser1 b with
  | None -> None
  | Some (a1, rem) ->
    match deser2 rem with
    | None -> None
    | Some (a2, rem) -> Some ((a1, a2), rem)

let write_pair (evi1: 'a evidence) (evi2: 'b evidence) (b: bytes) ((a1, a2): ('a * 'b)): bytes =
  let ser1, ser2 = evi1.write, evi2.write in

  let b1 = ser1 b a1 in
  ser2 b1 a2

let pair_evi (evi1: 'a evidence) (evi2: 'b evidence): ('a * 'b) evidence = 
  let write = write_pair evi1 evi2 in
  let read = read_pair evi1 evi2 in
  { write = write; read = read }


let read_trio (evi1: 'a evidence) (evi2: 'b evidence) (evi3: 'c evidence) (b: bytes)
  : (('a * 'b * 'c) * bytes) option =
  let deser1, deser2, deser3 = evi1.read, evi2.read, evi3.read in
  match deser1 b with
  | None -> None
  | Some (a1, rem) ->
    match deser2 rem with
    | None -> None
    | Some (a2, rem) -> 
      match deser3 rem with
      | None -> None
      | Some (a3, rem) -> Some ((a1, a2, a3), rem)

let write_trio (evi1: 'a evidence) (evi2: 'b evidence) (evi3: 'c evidence) (b: bytes) 
  ((a1, a2, a3): ('a * 'b * 'c)): bytes =
  let ser1, ser2, ser3 = evi1.write, evi2.write, evi3.write in

  let b1 = ser1 b a1 in
  let b2 = ser2 b1 a2 in
  ser3 b2 a3

let trio_evi (evi1: 'a evidence) (evi2: 'b evidence) (evi3: 'c evidence)
  : ('a * 'b * 'c) evidence = 
  let write = write_trio evi1 evi2 evi3 in
  let read = read_trio evi1 evi2 evi3 in
  { write = write; read = read }


let read_quad (evi1: 'a evidence) (evi2: 'b evidence) (evi3: 'c evidence) (evi4: 'd evidence) (b: bytes)
  : (('a * 'b * 'c * 'd) * bytes) option =
  let deser1, deser2, deser3, deser4 = evi1.read, evi2.read, evi3.read, evi4.read in
  match deser1 b with
  | None -> None
  | Some (a1, rem) ->
    match deser2 rem with
    | None -> None
    | Some (a2, rem) -> 
      match deser3 rem with
      | None -> None
      | Some (a3, rem) -> 
        match deser4 rem with
        | None -> None
        | Some (a4, rem) -> Some ((a1, a2, a3, a4), rem)

let write_quad (evi1: 'a evidence) (evi2: 'b evidence) (evi3: 'c evidence) (evi4: 'd evidence) (b: bytes) 
  ((a1, a2, a3, a4): ('a * 'b * 'c * 'd)): bytes =
  let ser1, ser2, ser3, ser4 = evi1.write, evi2.write, evi3.write, evi4.write in

  let b1 = ser1 b a1 in
  let b2 = ser2 b1 a2 in
  let b3 = ser3 b2 a3 in
  ser4 b3 a4

let quad_evi (evi1: 'a evidence) (evi2: 'b evidence) (evi3: 'c evidence) (evi4: 'd evidence)
  : ('a * 'b * 'c * 'd) evidence = 
  let write = write_quad evi1 evi2 evi3 evi4 in
  let read = read_quad evi1 evi2 evi3 evi4 in
  { write = write; read = read }


let read_pent (evi1: 'a evidence) (evi2: 'b evidence) (evi3: 'c evidence) (evi4: 'd evidence) (evi5: 'e evidence) (b: bytes)
  : (('a * 'b * 'c * 'd * 'e) * bytes) option =
  let deser1, deser2, deser3, deser4, deser5 = evi1.read, evi2.read, evi3.read, evi4.read, evi5.read in
  match deser1 b with
  | None -> None
  | Some (a1, rem) ->
    match deser2 rem with
    | None -> None
    | Some (a2, rem) -> 
      match deser3 rem with
      | None -> None
      | Some (a3, rem) -> 
        match deser4 rem with
        | None -> None
        | Some (a4, rem) -> 
          match deser5 rem with
          | None -> None
          | Some (a5, rem) -> Some ((a1, a2, a3, a4, a5), rem)

let write_pent (evi1: 'a evidence) (evi2: 'b evidence) (evi3: 'c evidence) (evi4: 'd evidence) (evi5: 'e evidence) (b: bytes) 
  ((a1, a2, a3, a4, a5): ('a * 'b * 'c * 'd * 'e)): bytes =
  let ser1, ser2, ser3, ser4, ser5 = evi1.write, evi2.write, evi3.write, evi4.write, evi5.write in

  let b1 = ser1 b a1 in
  let b2 = ser2 b1 a2 in
  let b3 = ser3 b2 a3 in
  let b4 = ser4 b3 a4 in
  ser5 b4 a5

let pent_evi (evi1: 'a evidence) (evi2: 'b evidence) (evi3: 'c evidence) (evi4: 'd evidence) (evi5: 'e evidence)
  : ('a * 'b * 'c * 'd * 'e) evidence = 
  let write = write_pent evi1 evi2 evi3 evi4 evi5 in
  let read = read_pent evi1 evi2 evi3 evi4 evi5 in
  { write = write; read = read }


let read_hex (evi1: 'a evidence) (evi2: 'b evidence) (evi3: 'c evidence) (evi4: 'd evidence) (evi5: 'e evidence) (evi6: 'f evidence) (b: bytes)
  : (('a * 'b * 'c * 'd * 'e * 'f) * bytes) option =
  let deser1, deser2, deser3, deser4, deser5, deser6 = evi1.read, evi2.read, evi3.read, evi4.read, evi5.read, evi6.read in
  match deser1 b with
  | None -> None
  | Some (a1, rem) ->
    match deser2 rem with
    | None -> None
    | Some (a2, rem) -> 
      match deser3 rem with
      | None -> None
      | Some (a3, rem) -> 
        match deser4 rem with
        | None -> None
        | Some (a4, rem) -> 
          match deser5 rem with
          | None -> None
          | Some (a5, rem) -> 
            match deser6 rem with
            | None -> None
            | Some (a6, rem) -> Some ((a1, a2, a3, a4, a5, a6), rem)

let write_hex (evi1: 'a evidence) (evi2: 'b evidence) (evi3: 'c evidence) (evi4: 'd evidence) (evi5: 'e evidence) (evi6: 'f evidence) (b: bytes) 
  ((a1, a2, a3, a4, a5, a6): ('a * 'b * 'c * 'd * 'e * 'f)): bytes =
  let ser1, ser2, ser3, ser4, ser5, ser6 = evi1.write, evi2.write, evi3.write, evi4.write, evi5.write, evi6.write in

  let b1 = ser1 b a1 in
  let b2 = ser2 b1 a2 in
  let b3 = ser3 b2 a3 in
  let b4 = ser4 b3 a4 in
  let b5 = ser5 b4 a5 in
  ser6 b5 a6

let hex_evi (evi1: 'a evidence) (evi2: 'b evidence) (evi3: 'c evidence) (evi4: 'd evidence) (evi5: 'e evidence) (evi6: 'f evidence)
  : ('a * 'b * 'c * 'd * 'e * 'f) evidence = 
  let write = write_hex evi1 evi2 evi3 evi4 evi5 evi6 in
  let read = read_hex evi1 evi2 evi3 evi4 evi5 evi6 in
  { write = write; read = read }


let read_slice1D (b: bytes): (slice1D * bytes) option =
  match read_int b with
  | None -> None
  | Some (i, rem) ->
    match read_bytes i rem with
    | None -> None
    | Some (b, rem) -> Some ((i, b), rem)

let write_slice1D (b: bytes) ((i, b1): slice1D): bytes =
  let b = write_int b i in
  write_bytes b b1

let slice1D_evi: slice1D evidence =
  { write = write_slice1D; read = read_slice1D }


let read_list (evi: 'a evidence) (b: bytes): ('a list * bytes) option =
  match read_int b with
  | None -> None
  | Some (i, rem) ->
    let rec aux i acc b =
      if i = 0 then Some (List.rev acc, b) else
        match evi.read b with
        | None -> None
        | Some (e, rem) -> aux (i-1) (e::acc) rem
    in
    aux i [] rem

let write_list (evi: 'a evidence) (b: bytes) (l: 'a list): bytes =
  let b = write_int b (List.length l) in
  List.fold_left (fun b e -> evi.write b e) b l

let list_evi (evi: 'a evidence): 'a list evidence =
  let write = write_list evi in
  let read = read_list evi in
  { write = write; read = read }


let read_queue (evi: 'a evidence) (b: bytes): ('a Queue.t * bytes) option =
  let q = Queue.create () in
  match read_int b with
  | None -> None
  | Some (i, rem) ->
    let rec aux i b =
      if i = 0 then Some (q, b) else
        match evi.read b with
        | None -> None
        | Some (e, rem) -> 
          Queue.push e q; aux (i-1) rem
    in
    aux i rem

let write_queue (evi: 'a evidence) (b: bytes) (q: 'a Queue.t): bytes =
  let b = write_int b (Queue.length q) in
  Queue.fold (fun b e -> evi.write b e) b q

let queue_evi (evi: 'a evidence): 'a Queue.t evidence =
  let write = write_queue evi in
  let read = read_queue evi in
  { write = write; read = read }


let read_array (evi: 'a evidence) (b: bytes): ('a Array.t * bytes) option =
  match read_int b with
  | None -> None
  | Some (i, rem) ->
    match evi.read b with
    | None -> None
    | Some (e, rem) ->
      let arr = Array.make i e in
      let b_opt = Array.fold_left (fun b_opt _ ->
        match b_opt with
        | None -> None
        | Some (b, i) ->
          match evi.read b with
          | None -> None
          | Some (e, rem) -> 
            Array.set arr i e; Some (rem, (i + 1))
        ) (Some (rem, 1)) arr
      in
      match b_opt with
      | None -> None
      | Some (b, _) -> Some (arr, b)

let write_array (evi: 'a evidence) (b: bytes) (arr: 'a Array.t): bytes =
  let b = write_int b (Array.length arr) in
  Array.fold_left (fun b e -> evi.write b e) b arr

let array_evi (evi: 'a evidence): 'a Array.t evidence =
  let write = write_array evi in
  let read = read_array evi in
  { write = write; read = read }
