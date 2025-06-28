let exp i1 i2 =
  int_of_float (( ** ) (float_of_int i1) (float_of_int i2))

let list_init i f =
  let rec list_init i l =
    if i = 0 then l
    else list_init (i-1) (f (i-1) :: l)
  in
  list_init i []

let random_even () =
  Random.int(50000000) * 2

let random_odd () =
  Random.int(50000000) * 2 + 1

let random_string len =
  String.concat "" (list_init len (fun _ -> String.make 1 (char_of_int (20 + (Random.int 236)))))

let output = ref (open_out_bin "/dev/null")

let num_rb_inserts = 100000
let rb_sizes = list_init 18 (fun i -> i + 4)

let leaf_size = 1024
let num_mtree_retrieves = 100000
let mtree_sizes = list_init 16 (fun i -> i + 4)

let write_rdb_tree s =
  let rec aux x l =
    match x with
    | 0 -> l
    | _ -> aux (x-1) ((string_of_int (random_odd ())^"\n") :: l)
  in
  let _ = output := open_out_bin (Printf.sprintf "data/rdb1_%d.dat" s) in
  let l =  aux (exp 2 s) [] in
  let _ = List.iter (output_string !output) l in
  let _ = close_out !output in
  output := open_out_bin "/dev/null"

let write_mrk_tree s =
  let rec aux x l =
    match x with
    | 0 -> l
    | _ -> aux (x-1) (((random_string leaf_size)^"\n") :: l)
  in
  let _ = output := open_out_bin (Printf.sprintf "data/mtree1_%d.dat" s) in
  let l =  aux (exp 2 s) [] in
  let _ = List.iter (output_string !output) l in
  let _ = close_out !output in
  output := open_out_bin "/dev/null"
  
let write_rdb_queries s =
  let rec aux x l =
    match x with
    | 0 -> l
    | _ -> aux (x-1) ((string_of_int (random_even ())^"\n") :: l)
  in
  let _ = output := open_out_bin (Printf.sprintf "data/rdb_ins1_%d.dat" s) in
  let l = aux num_rb_inserts [] in
  let _ = List.iter (output_string !output) l in
  let _ = close_out !output in
  output := open_out_bin "/dev/null"

let write_mtree_queries s =
  let n = exp 2 s in
  let rec aux x l =
    match x with
    | 0 -> l
    | _ -> aux (x-1) ((string_of_int (Random.int n)^"\n") :: l)
  in
  let _ = output := open_out_bin (Printf.sprintf "data/mtree_look1_%d.dat" s) in
  let l = aux num_mtree_retrieves [] in
  let _ = List.iter (output_string !output) l in
  let _ = close_out !output in
  output := open_out_bin "/dev/null";;


List.iter (fun s -> write_rdb_tree s) rb_sizes;
List.iter (fun s -> write_mrk_tree s) mtree_sizes;
List.iter (fun s -> write_rdb_queries s) rb_sizes;
List.iter (fun s -> write_mtree_queries s) mtree_sizes;
