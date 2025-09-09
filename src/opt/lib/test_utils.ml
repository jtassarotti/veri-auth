open Merkle
open Redblack
open Prover_rev
open Verifier
open Prover_marshal
open Verifier_marshal
open Prover_io
open Verifier_io
open Prover_susp
open Verifier_susp
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

module Merkle_Ideal = ((Merkle [@inlined]) (Ideal) [@inlined]) (Merkle_retrieve_ideal);;
module Merkle_Prover_rev = ((Merkle [@inlined]) (Prover_rev) [@inlined]) (Merkle_retrieve_prover);;
module Merkle_Verifier = ((Merkle [@inlined]) (Verifier) [@inlined]) (Merkle_retrieve_verifier);;
module Merkle_Prover_marshal = ((Merkle [@inlined]) (Prover_marshal) [@inlined]) (Merkle_retrieve_prover);;
module Merkle_Verifier_marshal = ((Merkle [@inlined]) (Verifier_marshal) [@inlined]) (Merkle_retrieve_verifier);;
module Merkle_Prover_io = ((Merkle [@inlined]) (Prover_io) [@inlined]) (Merkle_retrieve_prover);;
module Merkle_Verifier_io = ((Merkle [@inlined]) (Verifier_io) [@inlined]) (Merkle_retrieve_verifier);;
module Merkle_Prover_susp = ((Merkle [@inlined]) (Prover_susp) [@inlined]) (Merkle_retrieve_prover);;
module Merkle_Verifier_susp = ((Merkle [@inlined]) (Verifier_susp) [@inlined]) (Merkle_retrieve_verifier);;

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

let random_susp_tree height leaf_len =
  let l = random_leaves (exp 2 height) leaf_len in
  Merkle_Prover_susp.from_list l
;;

module RedBlack_Ideal = ((RedBlack [@inlined]) (Ideal) [@inlined]);;
module RedBlack_Prover_rev = ((RedBlack [@inlined]) (Prover_rev) [@inlined]);;
module RedBlack_Verifier = ((RedBlack [@inlined]) (Verifier) [@inlined]);;
module RedBlack_Prover_marshal = ((RedBlack [@inlined]) (Prover_marshal) [@inlined]);;
module RedBlack_Verifier_marshal = ((RedBlack [@inlined]) (Verifier_marshal) [@inlined]);;
module RedBlack_Prover_io = ((RedBlack [@inlined]) (Prover_io) [@inlined]);;
module RedBlack_Verifier_io = ((RedBlack [@inlined]) (Verifier_io) [@inlined]);;

