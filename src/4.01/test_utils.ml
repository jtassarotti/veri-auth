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

let list_init i f =
  let rec list_init i l =
    if i = 0 then l
    else list_init (i-1) (f (i-1) :: l)
  in
  list_init i []

module Merkle_Ideal = Merkle (Ideal) (Merkle_retrieve_ideal);;
module Merkle_Prover_rev = Merkle (Prover_rev) (Merkle_retrieve_prover);;
module Merkle_Verifier = Merkle (Verifier) (Merkle_retrieve_verifier);;
module Merkle_Prover_marshal = Merkle (Prover_marshal) (Merkle_retrieve_prover);;
module Merkle_Verifier_marshal = Merkle (Verifier_marshal) (Merkle_retrieve_verifier);;
module Merkle_Prover_io = Merkle (Prover_io) (Merkle_retrieve_prover);;
module Merkle_Verifier_io = Merkle (Verifier_io) (Merkle_retrieve_verifier);;

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

module RedBlack_Ideal = RedBlack (Ideal);;
module RedBlack_Prover_rev = RedBlack (Prover_rev);;
module RedBlack_Verifier = RedBlack (Verifier);;
module RedBlack_Prover_marshal = RedBlack (Prover_marshal);;
module RedBlack_Verifier_marshal = RedBlack (Verifier_marshal);;
module RedBlack_Prover_io = RedBlack (Prover_io);;
module RedBlack_Verifier_io = RedBlack (Verifier_io);;

