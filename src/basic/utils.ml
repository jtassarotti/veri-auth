Sys.catch_break true;;

(** Serialization **)
let marshal_flags = [Marshal.No_sharing]

(** Measurement **)
let measured_time = ref 0.
let measured_calls = ref 0

(** Integer Exponentiation *)
let exp i1 i2 =
  int_of_float (( ** ) (float_of_int i1) (float_of_int i2))

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
let measure fn arg =
  let start_time = Sys.time ()
  in
  try
    let res = fn arg in
    let end_time = Sys.time ()
    in
    measured_time := !measured_time +. (end_time -. start_time);
    incr measured_calls;
    res
  with e ->
    let end_time = Sys.time ()
    in
    measured_time := !measured_time +. (end_time -. start_time);
    incr measured_calls;
    raise e

let measures = Hashtbl.create 10
let steps = Hashtbl.create 10

let measure_call (id: string) fn arg =
  let get_time () = Sys.time ()
  in
  let (calls, time) =
    if Hashtbl.mem measures id
    then Hashtbl.find measures id
    else (0, 0.)
  in
  let start_time = get_time () in
  try
    let res = fn arg in
    let end_time = get_time () in
    Hashtbl.replace measures id (calls + 1, time +. end_time -. start_time);
    (if String.compare id "step" = 0 then Hashtbl.replace steps calls (end_time -. start_time));
    res
  with e ->
    let end_time = get_time () in
    Hashtbl.replace measures id (calls + 1, time +. end_time -. start_time);
    raise e

(* let measure_call _ f arg = f arg *)

let get_measure (id: string) =
  Hashtbl.find measures id

let rec print_steps n_steps step = 
  if step = n_steps then ()
  else 
    let time = Hashtbl.find steps step in
    print_endline ((string_of_int step) ^ ": " ^ (string_of_float time) ^ " s");
    print_steps n_steps (step+1)

let print_measures () =
  if Hashtbl.length measures > 0 then print_endline "Profiling:";
  let l = Hashtbl.fold (fun id _ (l:string list) -> id :: l) measures [] |> List.sort String.compare in
  List.iter
    (fun id ->
      let calls, time = Hashtbl.find measures id in
      print_endline ("  " ^ id ^ ": " ^ (string_of_int calls) ^ " call(s), " ^ (string_of_float time) ^ " s. " ^
      (string_of_float (time /. (float calls))) ^ " s/call")
    ) l;
  let n_steps = Hashtbl.length steps in
  print_steps n_steps 0

let reset_measures () =
  Hashtbl.clear measures;
  Hashtbl.clear steps

let measure_bytes () =
  (Gc.stat()).minor_words +. (Gc.stat()).major_words -. (Gc.stat()).promoted_words
