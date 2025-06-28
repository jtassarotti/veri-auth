open Merkle
open Redblack
open Prover
open Verifier
open Prover_marshal
open Verifier_marshal
open Prover_io
open Verifier_io
open Prover_io_batch
open Verifier_io_batch
open Prover_susp
open Verifier_susp
(* open Prover_buf
open Verifier_buf
open Prover_orig
open Verifier_buf_magic
open Prover_buf_magic_state
open Verifier_buf_magic_state *)
open Ideal

module ISet = Set.Make(struct type t = int let compare : int -> int -> int = compare end)
let curr_total_memory : float ref = ref 0.

let set_heap_params () = 
  let gc_params = { (Gc.get()) with Gc.minor_heap_size = 32000; Gc.major_heap_increment = 124000; Gc.space_overhead = 80; Gc.stack_limit = 256000 } in
  Gc.set gc_params

let gc_collect () = Gc.full_major (); Gc.full_major ()

let total_memory () = 
  (Gc.stat ()).live_words * 8
  (* ((Gc.stat()).minor_words +. (Gc.stat()).major_words -. (Gc.stat()).promoted_words) *. 8.0 *)

let print_total_memory () =
  total_memory () |> string_of_int
  (* total_memory () |> string_of_float *)

(* let record_total_memory () = curr_total_memory := total_memory ()

let print_memory_diff () = 
  let mem = !curr_total_memory in
  let _ = curr_total_memory := 0. in
  total_memory () -. mem |> string_of_float *)

let set_default_seed () =
  Random.set_state (Random.State.make ([|1|]))

let random_even () =
  Random.int(50000000) * 2

let random_odd () =
  Random.int(50000000) * 2 + 1

let print_opt_string r =
  match r with
  | None -> print_string "None"
  | Some s -> print_string ("Some " ^ s)

let print_prover_res s =
  print_string "Result: "; print_opt_string s

let print_verifier_res s =
  print_string "Verifier Result: "; print_opt_string s

let equal_res pres vres =
  match vres with
  | `Ok (_, v) -> pres = v
  | _ -> false

let print_proof_size proof =
  print_string (proof^"\n"); Printf.printf "(pf size: %d)" (String.length proof)
;;

(* Test similar to in Lambda auth paper *)
let random_alpha_char () =
  Char.chr (97 + Random.int 26)

let random_string len =
  let s = BytesLabels.create len in
  for i = 0 to len -1 do BytesLabels.set s i (random_alpha_char ()) done;
  BytesLabels.to_string s;;

let random_leaves num len =
  let rec go num acc =
    match num with
    | 0.0 -> acc
    | _ -> go (num -. 1.0) (random_string len :: acc)
  in
  go num []
;;

let random_key_vals num len =
  let rec go num acc =
    match num with
    | 0 -> acc
    | _ -> go (num-1) ((num, random_string len) :: acc)
  in
  go num [] 
  |> List.sort (fun (_, a) (_, b) -> String.compare a b)
;;

let random_odd_key_vals num =
  let rec go num acc1 acc2 =
    match num with
    | 0.0 -> (acc1, acc2)
    | _ -> 
      let a = random_odd () in
      go (num -. 1.0) (a::acc1) (string_of_int a::acc2)
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

let rec random_unique_int max cache =
  let n = Random.int max |> (+) 1 in
  match try Some (ISet.find n cache) with Not_found -> None with
  | None -> n
  | Some _ -> random_unique_int max cache

let random_keys num =
  let rec go num acc =
    match num with
    | 0 -> acc
    | _ -> 
      let n = random_odd () in
      go (num-1) (n :: acc)
  in
  go num []

module Merkle_Ideal = ((Merkle [@inlined]) (Ideal) [@inlined]) (Merkle_retrieve_ideal);;
module Merkle_Prover = ((Merkle [@inlined]) (Prover) [@inlined]) (Merkle_retrieve_prover);;
module Merkle_Verifier = ((Merkle [@inlined]) (Verifier) [@inlined]) (Merkle_retrieve_verifier);;
module Merkle_Prover_susp = ((Merkle [@inlined]) (Prover_susp) [@inlined]) (Merkle_retrieve_prover);;
module Merkle_Verifier_susp = ((Merkle [@inlined]) (Verifier_susp) [@inlined]) (Merkle_retrieve_verifier);;
module Merkle_Prover_marshal = ((Merkle [@inlined]) (Prover_marshal) [@inlined]) (Merkle_retrieve_prover);;
module Merkle_Verifier_marshal = ((Merkle [@inlined]) (Verifier_marshal) [@inlined]) (Merkle_retrieve_verifier);;
module Merkle_Prover_io = ((Merkle [@inlined]) (Prover_io) [@inlined]) (Merkle_retrieve_prover);;
module Merkle_Verifier_io = ((Merkle [@inlined]) (Verifier_io) [@inlined]) (Merkle_retrieve_verifier);;
(* module Merkle_Prover_buf = (Merkle (Prover_buf) [@inlined]) (Merkle_retrieve_prover);;
module Merkle_Verifier_buf = (Merkle (Verifier_buf) [@inlined]) (Merkle_retrieve_verifier);;
module Merkle_Prover_orig = (Merkle (Prover_orig) [@inlined]) (Merkle_retrieve_prover);;
module Merkle_Verifier_buf_magic = (Merkle (Verifier_buf_magic) [@inlined]) (Merkle_retrieve_verifier);;
module Merkle_Prover_buf_magic_state = (Merkle (Prover_buf_magic_state) [@inlined]) (Merkle_retrieve_prover);;
module Merkle_Verifier_buf_magic_state = (Merkle (Verifier_buf_magic_state) [@inlined]) (Merkle_retrieve_verifier);; *)


let rec random_path height =
  match height with
  | 0.0 -> Path.path_empty
  | _  ->
    random_path (height -. 1.)
    |>
      if Random.bool () then
        Path.path_left
      else
        Path.path_right
;;

let rec random_paths num height =
  let rec go num acc =
    match num with
    | 0 -> acc
    | _ -> go (num - 1) (random_path height :: acc)
  in
  go num []
;;

let random_ideal_tree height leaf_len =
  let l = random_leaves (( ** ) 2.0 height) leaf_len in
  Merkle_Ideal.from_list l
;;

let random_tree height leaf_len =
  let l = random_leaves (( ** ) 2.0 height) leaf_len in
  Merkle_Prover.from_list l
;;

let random_susp_tree height leaf_len =
  let l = random_leaves (( ** ) 2.0 height) leaf_len in
  Merkle_Prover_susp.from_list l
;;

let random_tree_marshal height leaf_len =
  let l = random_leaves (( ** ) 2.0 height) leaf_len in
  Merkle_Prover_marshal.from_list l
;;

let random_tree_io height leaf_len =
  let l = random_leaves (( ** ) 2.0 height) leaf_len in
  Merkle_Prover_io.from_list l
;;

(* let random_orig_tree height leaf_len =
  let l = random_leaves (( ** ) 2.0 height) leaf_len in
  Merkle_Prover_orig.from_list l
;;

let random_buf_tree height leaf_len =
  let l = random_leaves (( ** ) 2.0 height) leaf_len in
  Merkle_Prover_buf.from_list l
;;

let random_buf_magic_state_tree height leaf_len =
  let l = random_leaves (( ** ) 2.0 height) leaf_len in
  Merkle_Prover_buf_magic_state.from_list l
;; *)

module RedBlack_Ideal = RedBlack[@inlined] (Ideal);;
module RedBlack_Prover = RedBlack[@inlined] (Prover);;
module RedBlack_Verifier = RedBlack[@inlined] (Verifier);;
module RedBlack_Prover_marshal = RedBlack[@inlined] (Prover_marshal);;
module RedBlack_Verifier_marshal = RedBlack[@inlined] (Verifier_marshal);;
module RedBlack_Prover_io = RedBlack[@inlined] (Prover_io);;
module RedBlack_Verifier_io = RedBlack[@inlined] (Verifier_io);;
module RedBlack_Prover_io_batch = RedBlack[@inlined] (Prover_io_batch);;
module RedBlack_Verifier_io_batch = RedBlack[@inlined] (Verifier_io_batch);;
(* module RedBlack_Prover_buf = RedBlack[@inlined] (Prover_buf);;
module RedBlack_Verifier_buf = RedBlack[@inlined] (Verifier_buf);;
module RedBlack_Prover_orig = RedBlack[@inlined] (Prover_orig);;
module RedBlack_Verifier_buf_magic = RedBlack[@inlined] (Verifier_buf_magic);;
module RedBlack_Prover_buf_magic_state = RedBlack[@inlined] (Prover_buf_magic_state);;
module RedBlack_Verifier_buf_magic_state = RedBlack[@inlined] (Verifier_buf_magic_state);; *)

(* let random_normal_sparse_tree height num_leafs leaf_len =
  let leaves = random_leaves num_leafs leaf_len in
  let paths = random_paths num_leafs height in
  let t = Merkle_Prover.init_tree height in
  Prover.run (Merkle_Prover.update_list paths leaves t)
;; *)

(* let random_normal_sparse_buf_tree height num_leafs leaf_len =
  let leaves = random_leaves num_leafs leaf_len in
  let paths = random_paths num_leafs height in
  let t = Merkle_Prover_buf.init_tree height in
  Prover_buf.run (Merkle_Prover_buf.update_list paths leaves t)
;; *)

(* let random_sparse_tree height num_leafs leaf_len =
  let leaves = random_leaves num_leafs leaf_len in
  let paths = random_paths num_leafs height in
  let t = Merkle_Sparse_Prover.init_tree height in
  Prover.run (Merkle_Sparse_Prover.update_list paths leaves t)
;;

let random_sparse_buf_tree height num_leafs leaf_len =
  let leaves = random_leaves num_leafs leaf_len in
  let paths = random_paths num_leafs height in
  let t = Merkle_Sparse_Prover_buf.init_tree height in
  Prover_buf.run (Merkle_Sparse_Prover_buf.update_list paths leaves t)
;; *)

(* let random_ideal_tree height leaf_len =
  let l = random_leaves (Core.Int.pow 2 height) leaf_len in
  Merkle_Ideal.from_list l
;; *)
