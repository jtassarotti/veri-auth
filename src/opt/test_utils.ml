open Merkle
open Redblack
open Prover_rev
open Verifier
open Prover_marshal
open Verifier_marshal
open Prover_io
open Verifier_io
open Ideal
open Utils

let set_default_seed () =
  Random.set_state (Random.State.make ([|1|]))

let random_even () =
  Random.int(50000000) * 2

let random_odd () =
  Random.int(50000000) * 2 + 1

let print_string_opt r =
  match r with
  | None -> print_string "None"
  | Some s -> print_string ("Some " ^ s)

let print_prover_res s =
  print_string "Result: "; print_string_opt s

let print_verifier_res s =
  print_string "Verifier Result: "; print_string_opt s

let equal_res pres vres =
  match vres with
  | `Ok (_, v) -> pres = v
  | _ -> false

let print_proof_size proof =
  print_string (proof^"\n"); Printf.printf "(pf size: %d)" (String.length proof)
;;

let print_proof_list_size proof =
  proof
  |> List.map (fun s -> print_string (s^"\n"); String.length s)
  |> List.fold_left (+) 0
  |> Printf.printf "(pf size: %d)"
;;

let random_alpha_char () =
  Char.chr (97 + Random.int 26)

let list_init i f =
  let rec list_init i l =
    if i = 0 then l
    else list_init (i-1) (f (i-1) :: l)
  in
  list_init i []

let random_string len =
  String.concat "" (list_init len (fun _ -> String.make 1 (BatRandom.char())))

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
    | _ -> go (num-1) ((num, random_string len) :: acc)
  in
  go num [] 
  |> List.sort (fun (_, a) (_, b) -> String.compare a b)
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

module Merkle_Ideal = ((Merkle [@inlined]) (Ideal) [@inlined]) (Merkle_retrieve_ideal);;
module Merkle_Prover_rev = ((Merkle [@inlined]) (Prover_rev) [@inlined]) (Merkle_retrieve_prover);;
module Merkle_Verifier = ((Merkle [@inlined]) (Verifier) [@inlined]) (Merkle_retrieve_verifier);;
module Merkle_Prover_marshal = ((Merkle [@inlined]) (Prover_marshal) [@inlined]) (Merkle_retrieve_prover);;
module Merkle_Verifier_marshal = ((Merkle [@inlined]) (Verifier_marshal) [@inlined]) (Merkle_retrieve_verifier);;
module Merkle_Prover_io = ((Merkle [@inlined]) (Prover_io) [@inlined]) (Merkle_retrieve_prover);;
module Merkle_Verifier_io = ((Merkle [@inlined]) (Verifier_io) [@inlined]) (Merkle_retrieve_verifier);;

let rec random_path height =
  match height with
  | 0 -> Path.path_empty
  | _  ->
    random_path (height - 1)
    |>
      if Random.bool () then
        Path.path_left
      else
        Path.path_right
;;

let rec print_path path =
  match Path.path_pop path with
  | None -> print_newline ()
  | Some (Path.Lp, path) -> print_string "l "; print_path path
  | Some (Path.Rp, path) -> print_string "r "; print_path path
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
  let l = random_leaves (exp 2 height) leaf_len in
  Merkle_Ideal.from_list l
;;

let random_rev_tree height leaf_len =
  let l = random_leaves (exp 2 height) leaf_len in
  Merkle_Prover_rev.from_list l
;;

let random_tree_marshal height leaf_len =
  let l = random_leaves (exp 2 height) leaf_len in
  Merkle_Prover_marshal.from_list l
;;

let random_tree_io height leaf_len =
  let l = random_leaves (exp 2 height) leaf_len in
  Merkle_Prover_io.from_list l
;;

module RedBlack_Ideal = ((RedBlack [@inlined]) (Ideal) [@inlined]);;
module RedBlack_Prover_rev = ((RedBlack [@inlined]) (Prover_rev) [@inlined]);;
module RedBlack_Verifier = ((RedBlack [@inlined]) (Verifier) [@inlined]);;
module RedBlack_Prover_marshal = ((RedBlack [@inlined]) (Prover_marshal) [@inlined]);;
module RedBlack_Verifier_marshal = ((RedBlack [@inlined]) (Verifier_marshal) [@inlined]);;
module RedBlack_Prover_io = ((RedBlack [@inlined]) (Prover_io) [@inlined]);;
module RedBlack_Verifier_io = ((RedBlack [@inlined]) (Verifier_io) [@inlined]);;

