Sys.catch_break true;;

(** Serialization **)
let marshal_flags = [Marshal.No_sharing]

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
