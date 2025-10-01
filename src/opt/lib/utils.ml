Sys.catch_break true;;

(** Reading from a file **)
let from_channel_with_string chan =
  let s = Bytes.create Marshal.header_size in
  really_input chan s 0 Marshal.header_size;
  let d = Marshal.data_size s 0 in
  let str = Bytes.create (Marshal.header_size + d) in
  Bytes.blit s 0 str 0 Marshal.header_size;
  really_input chan str Marshal.header_size d;
  Bytes.to_string str

(** String functions *)
let string_to_bits (s : string) : string =
  let len = String.length s in
  let out = Bytes.create (len * 8) in
  for i = 0 to len - 1 do
    let code = Char.code s.[i] in
    for j = 0 to 7 do
      let bit = (code lsr (7 - j)) land 1 in
      Bytes.set out (i * 8 + j) (if bit = 1 then '1' else '0')
    done
  done;
  Bytes.unsafe_to_string out

(** List functions *)
let rec list_sub n path =
  if n = 0 then []
  else 
    match path with
    | [] -> []
    | h::t -> h::list_sub (n-1) t

let list_length = List.length

let list_head = function
    [] -> None
  | h::t -> Some h

let list_tail = function
    [] -> []
  | h::t -> t

let list_rev = List.rev

let list_init i f =
  let rec list_init i l =
    if i = 0 then l
    else list_init (i-1) (f (i-1) :: l)
  in
  list_init i []

let list_split l =
  let rec split_aux l left right =
    match l, left, right with
    | [], _, _ | [_], _, _ -> (List.rev left), right
    | _ :: _ :: t, _, h :: right ->
        split_aux t (h :: left) right 
    | _ -> failwith "unbalanced"
  in
  split_aux l [] l

(** Serialization **)
let marshal_flags = [Marshal.No_sharing]

(** Measurement **)
let measured_time = ref 0.
let measured_calls = ref 0

(** Random generation **)
let set_default_seed () =
  Random.set_state (Random.State.make ([|1|]))

let random_int64 () =
  Random.int64(Int64.max_int)

let random_int64s num =
  let rec random_int64s_aux num acc =
    if num = 0 then acc
    else
      random_int64s_aux (num-1) (random_int64 ()::acc)
  in random_int64s_aux num []

let random_even () =
  Random.int(50000000) * 2

let random_odd () =
  Random.int(50000000) * 2 + 1

let random_alpha_char () =
  Char.chr (97 + Random.int 26)

let random_string len =
  String.concat "" (list_init len (fun _ -> String.make 1 (BatRandom.char())))

let random_key length =
  let charset = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789" in
  let len = String.length charset in
  let result = Bytes.create length in
  for i = 0 to length - 1 do
    let index = Random.int len in
    Bytes.set result i charset.[index]
  done;
  Bytes.to_string result

let random_bytes length =
  let charset = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789" in
  let len = String.length charset in
  let result = Bytes.create length in
  for i = 0 to length - 1 do
    let index = Random.int len in
    Bytes.set result i charset.[index]
  done;
  result

let random_leaves num len =
  let rec go num acc =
    match num with
    | 0 -> acc
    | _ ->
      let s = random_string len in
      go (num - 1) (s :: acc)
  in
  go num []
;;

let random_key_vals num len =
  let rec go num acc =
    match num with
    | 0 -> acc
    | _ -> go (num-1) ((random_key len, random_string len) :: acc)
  in
  go num []
;;

let random_key_vals_rep num len =
  let keys = Array.make num "" in
  let rec go num acc i =
    match num with
    | 0 -> acc
    | _ -> 
      let key, i =
        if (Random.bool ()) && (i>0) then
          let ind = Random.int i in
          keys.(ind), i
        else
          let key = random_key len in
          keys.(i) <- key;
          key, i+1
      in
      go (num-1) ((key, random_string len) :: acc) i
  in
  go num [] 0
;;

let random_odd_key_vals num =
  let rec go num acc1 acc2 =
    match num with
    | 0 -> (acc1, acc2)
    | _ -> 
      let a = random_odd () in
      go (num - 1) (a::acc1) (string_of_int a::acc2)
  in
  go num [] []
;;

let random_even_key_vals num =
  let rec go num acc1 acc2 =
    match num with
    | 0 -> (acc1, acc2)
    | _ -> 
      let a = random_even () in
      go (num-1) (a::acc1) (string_of_int a::acc2)
  in
  go num [] []
;;

let random_keys num =
  let rec go num acc =
    match num with
    | 0 -> acc
    | _ -> 
      let n = random_odd () in
      go (num-1) (n :: acc)
  in
  go num []

(** Integer Exponentiation *)
let exp i1 i2 =
  int_of_float (( ** ) (float_of_int i1) (float_of_int i2))

(** Set functions *)
module SSet = Set.Make(struct type t = string let compare : string -> string -> int = compare end)
let set_add = SSet.add
let set_mem = SSet.mem
let set_empty () = SSet.empty

(** Map functions *)
module SMap = Map.Make(struct type t = string let compare : string -> string -> int = compare end)
let map_lookup = SMap.find_opt
let map_insert = SMap.add
let map_empty () = SMap.empty

(** Memory stuff **)
let curr_total_memory : float ref = ref 0.

let set_heap_params () = 
  let gc_params = { (Gc.get()) with Gc.minor_heap_size = 32000; Gc.major_heap_increment = 124000; Gc.space_overhead = 80; Gc.stack_limit = 256000 } in
  Gc.set gc_params

let gc_collect () = Gc.full_major (); Gc.full_major ()

let total_memory () = 
  (Gc.stat ()).live_words * 8

let print_total_memory () =
  total_memory () |> string_of_int

(** Measurement **)
let measured_time = ref 0.
let measured_calls = ref 0

(** measure accumulated execution time and number of calls to a particular function *)
let measures = Hashtbl.create 20

let measure_call (id: string) fn arg =
  let get_time () = Sys.time ()
  in
  let calls, times, total_time =
    if Hashtbl.mem measures id
    then Hashtbl.find measures id
    else 0.0, "", 0.0
  in
  let start_time = get_time () in
  let res = fn arg in
  let end_time = get_time () in
  let time_taken = end_time -. start_time in
  Hashtbl.replace measures id 
    (calls +. 1., Printf.sprintf "%f_%s" time_taken times, time_taken +. total_time);
  res

let print_measures () =
  if Hashtbl.length measures > 0 then print_endline "Profiling:";
  let l = Hashtbl.fold (fun id _ (l:string list) -> id :: l) measures [] |> List.sort String.compare in
  List.iter
    (fun id ->
      let calls, times, time_taken = Hashtbl.find measures id in
      Printf.printf "%s. %f s/call. times: %s" id (time_taken /. calls) times;
      print_newline ();
    ) l

let reset_measures () =
  Hashtbl.clear measures;;
