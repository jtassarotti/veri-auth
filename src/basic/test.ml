open Auth
open Merkle
open Prover_rev
open Verifier
open Prover_buf
open Verifier_buf
open Prover
open Verifier_buf_magic
open Prover_buf_magic_state
open Verifier_buf_magic_state
open Test_utils
open Utils

let k = 3;;
let leaf_size = 20;;
let num_leafs = 100;;
let n_retrieve_paths = 50;;
set_default_seed ();

(* We show usage of different Authentikit versions below. The steps for using a given Authentikit module can be summarized as follows:
  1. Initialize the prover and the verifier modules.
  2. Call a function using Prover.run to generate a proof.
  3. Make the same call using Verifier.run and pass the proof as an argument. If the proof is not accepted, the program will terminate
with an error. *)

(* Merkle module initialization. The second argument specifies the optimized retrieve function module. *)
module Merkle_Prover_rev = Merkle (Prover_rev) (Merkle_retrieve_prover);;
module Merkle_Verifier = Merkle (Verifier) (Merkle_retrieve_verifier);;
module Merkle_Prover_buf = Merkle (Prover_buf) (Merkle_retrieve_prover);;
module Merkle_Verifier_buf = Merkle (Verifier_buf) (Merkle_retrieve_verifier);;
module Merkle_Prover = Merkle (Prover) (Merkle_retrieve_prover);;
module Merkle_Verifier_buf_magic = Merkle (Verifier_buf_magic) (Merkle_retrieve_verifier);;
module Merkle_Prover_buf_magic_state = Merkle (Prover_buf_magic_state) (Merkle_retrieve_prover);;
module Merkle_Verifier_buf_magic_state = Merkle (Verifier_buf_magic_state) (Merkle_retrieve_verifier);;


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

let rec random_paths num height =
  let rec go num acc =
    match num with
    | 0 -> acc
    | _ -> go (num - 1) (random_path height :: acc)
  in
  go num []
;;

let random_rev_tree height leaf_len =
  let l = random_leaves (exp 2 height) leaf_len in
  Merkle_Prover_rev.from_list l
;;

let random_tree height leaf_len =
  let l = random_leaves (exp 2 height) leaf_len in
  Merkle_Prover.from_list l
;;

let random_buf_tree height leaf_len =
  let l = random_leaves (exp 2 height) leaf_len in
  Merkle_Prover_buf.from_list l
;;

let random_buf_magic_state_tree height leaf_len =
  let l = random_leaves (exp 2 height) leaf_len in
  Merkle_Prover_buf_magic_state.from_list l
;;

Printf.printf "****** Original ******\n";;
Printf.printf "\n* Retrieve *\n";;
let t = random_tree k leaf_size;;
let ht = Prover.get_hash t;;
let p = random_path k;;
(* Calling Prover.run for the retrieve function. Note that Prover.run should only be called with Merkle_Prover functions. *)
(* This returns the proof and result of the call. *)
let proof, pres = Prover.run (Merkle_Prover.retrieve p t);;
(* Same for Verifier.run. Here we also pass the proof as an argument. *)
let vres = Verifier.run (Merkle_Verifier.retrieve p ht) proof;;

print_prover_res pres;
print_newline ();
print_verifier_res vres;;
print_newline ();
print_proof_size proof;
print_newline ();
assert (pres = (Option.get vres));;

(* Here we use the optimized retrieve function *)
Printf.printf "\n* Retrieve magic *\n";;
let proof, pres = Prover.run (Merkle_Prover.retrieve_magic p t);;

print_prover_res pres;
print_newline ();;
print_proof_size proof;
print_newline ();;

let vres = Verifier.run (Merkle_Verifier.retrieve_magic p ht) proof;; 
print_verifier_res vres;;
print_newline ();
assert (pres = (Option.get vres));;

Printf.printf "\n* Retrieve list *\n";;
let ps = List.init 10 (fun _ -> random_path k);;
let proof, pres = Prover.run (Merkle_Prover.retrieve_list ps t);;
List.iter (fun res -> print_prover_res res; print_newline ()) pres;;

let vres = Verifier.run (Merkle_Verifier.retrieve_list ps ht) proof;; 
print_proof_size proof;
print_newline ();;

Printf.printf "\n* Retrieve list magic *\n";;
let proof, pres = Prover.run (Merkle_Prover.retrieve_list_magic ps t);;
List.iter (fun res -> print_prover_res res; print_newline ()) pres;;

let vres = Verifier.run (Merkle_Verifier.retrieve_list_magic ps ht) proof;; 
print_proof_size proof;
print_newline ();;

Printf.printf "\n\n\n****** Reverse Optimization ******\n";;
Printf.printf "\n* Retrieve *\n";;
let t = random_rev_tree k leaf_size;;
let ht = Prover_rev.get_hash t;;
let p = random_path k;;
let proof, pres = Prover_rev.run (Merkle_Prover_rev.retrieve p t);;
let vres = Verifier.run (Merkle_Verifier.retrieve p ht) proof;;
       
print_prover_res pres;
print_newline ();
print_verifier_res vres;;
print_newline ();
print_proof_size proof;
print_newline ();
assert (pres = (Option.get vres));;

Printf.printf "\n* Contains *\n";;
match vres with
| Some (Some s) -> (
  let proof, pres = Prover_rev.run (Merkle_Prover_rev.contains s t) in
  print_proof_size proof;
  print_newline ();
  let vres = Verifier.run (Merkle_Verifier.contains s ht) proof in
  assert (pres = (Option.get vres)) )
| _ -> ()

let proof, pres = Prover_rev.run (Merkle_Prover_rev.contains "" t);;
print_proof_size proof;;
print_newline ();;
let vres = Verifier.run (Merkle_Verifier.contains "" ht) proof;;
assert (pres = (Option.get vres));;

Printf.printf "\n* Retrieve magic *\n";;
let proof, pres = Prover_rev.run (Merkle_Prover_rev.retrieve_magic p t);;

print_prover_res pres;
print_newline ();;
print_proof_size proof;
print_newline ();;

let vres = Verifier.run (Merkle_Verifier.retrieve_magic p ht) proof;; 
print_verifier_res vres;;
print_newline ();
assert (pres = (Option.get vres));;

Printf.printf "\n* Retrieve list *\n";;
let ps = List.init 10 (fun _ -> random_path k);;
let proof, pres = Prover_rev.run (Merkle_Prover_rev.retrieve_list ps t);;
List.iter (fun res -> print_prover_res res; print_newline ()) pres;;

let vres = Verifier.run (Merkle_Verifier.retrieve_list ps ht) proof;; 
print_proof_size proof;
print_newline ();;

Printf.printf "\n* Retrieve list magic *\n";;
let proof, pres = Prover_rev.run (Merkle_Prover_rev.retrieve_list_magic ps t);;
List.iter (fun res -> print_prover_res res; print_newline ()) pres;;

let vres = Verifier.run (Merkle_Verifier.retrieve_list_magic ps ht) proof;; 
print_proof_size proof;
print_newline ();;

(* let t2 = random_tree k leaf_size;;
let ht2 = Prover_rev.get_hash t2;;
let proof, pres = Prover_rev.run (Merkle_Prover_rev.compare t t2);;
print_proof_size proof;;
print_newline ();;
let vres = Verifier.run (Merkle_Verifier.compare ht ht2) proof;;
assert (pres = (Option.get vres));;

let proof, pres = Prover_rev.run (Merkle_Prover_rev.compare t t);;
print_proof_size proof;;
print_newline ();;
let vres = Verifier.run (Merkle_Verifier.compare ht ht) proof;;
assert (pres = (Option.get vres));; *)

Printf.printf "\n\n\n****** Buffer Optimization ******\n";;
Printf.printf "\n* Retrieve *\n";;
let t = random_buf_tree k leaf_size;;
let ht = Prover_buf.get_hash t;;
let p = random_path k;;
let proof, pres = Prover_buf.run (Merkle_Prover_buf.retrieve p t);;
let vres = Verifier_buf.run (Merkle_Verifier_buf.retrieve p ht) proof;; 

print_prover_res pres;
print_newline ();
print_verifier_res vres;;
print_newline ();
print_proof_size proof;
print_newline ();
assert (pres = (Option.get vres));;

Printf.printf "\n* Retrieve magic *\n";;
let proof, pres = Prover_buf.run (Merkle_Prover_buf.retrieve_magic p t);;
let vres = Verifier_buf.run (Merkle_Verifier_buf.retrieve_magic p ht) proof;; 

print_prover_res pres;
print_newline ();
print_verifier_res vres;;
print_newline ();
print_proof_size proof;
print_newline ();
assert (pres = (Option.get vres));;

Printf.printf "\n* Retrieve list *\n";;
let ps = List.init 10 (fun _ -> random_path k);;
let proof, pres = Prover_buf.run (Merkle_Prover_buf.retrieve_list ps t);;
List.iter (fun res -> print_prover_res res; print_newline ()) pres;;

let vres = Verifier_buf.run (Merkle_Verifier_buf.retrieve_list ps ht) proof;; 
print_proof_size proof;
print_newline ();
assert (pres = (Option.get vres));;

Printf.printf "\n* Retrieve list magic *\n";;
let proof, pres = Prover_buf.run (Merkle_Prover_buf.retrieve_list_magic ps t);;
List.iter (fun res -> print_prover_res res; print_newline ()) pres;;

let vres = Verifier_buf.run (Merkle_Verifier_buf.retrieve_list_magic ps ht) proof;; 
print_proof_size proof;
print_newline ();
assert (pres = (Option.get vres));;

Printf.printf "\n\n\n****** Buffer Magic Optimization ******\n";;
Printf.printf "\n* Retrieve *\n";;
let t = random_buf_tree k leaf_size;;
let ht = Prover_buf.get_hash t;;
let p = random_path (k-1);;
let proof, pres = Prover_buf.run (Merkle_Prover_buf.retrieve p t);;
let vres = Verifier_buf_magic.run (Merkle_Verifier_buf_magic.retrieve p ht) proof;; 

print_prover_res pres;
print_newline ();
print_verifier_res vres;;
print_newline ();
print_proof_size proof;
print_newline ();
assert (pres = (Option.get vres));;

Printf.printf "\n* Retrieve magic *\n";;
let proof, pres = Prover_buf.run (Merkle_Prover_buf.retrieve_magic p t);;
let vres = Verifier_buf_magic.run (Merkle_Verifier_buf_magic.retrieve_magic p ht) proof;; 

print_prover_res pres;
print_newline ();
print_verifier_res vres;;
print_newline ();
print_proof_size proof;
print_newline ();
assert (pres = (Option.get vres));;

Printf.printf "\n* Retrieve list *\n";;
let ps = List.init 10 (fun _ -> random_path k);;
let proof, pres = Prover_buf.run (Merkle_Prover_buf.retrieve_list ps t);;
List.iter (fun res -> print_prover_res res; print_newline ()) pres;;

let vres = Verifier_buf_magic.run (Merkle_Verifier_buf_magic.retrieve_list ps ht) proof;; 
print_proof_size proof;
print_newline ();;

Printf.printf "\n* Retrieve list magic*\n"
let proof, pres = Prover_buf.run (Merkle_Prover_buf.retrieve_list_magic ps t);;
List.iter (fun res -> print_prover_res res; print_newline ()) pres;;

let vres = Verifier_buf_magic.run (Merkle_Verifier_buf_magic.retrieve_list_magic ps ht) proof;; 
print_proof_size proof;
print_newline ();;

Printf.printf "\n\n\n****** Buffer Magic State Optimization ******\n";;
Printf.printf "\n* Retrieve *\n";;
let t = random_buf_magic_state_tree k leaf_size;;
let ht = Prover_buf_magic_state.get_hash t;;
let p = random_path (k-1);;
let proof, pres = Prover_buf_magic_state.run (Merkle_Prover_buf_magic_state.retrieve p t);;
let vres = Verifier_buf_magic_state.run (Merkle_Verifier_buf_magic_state.retrieve p ht) proof;; 

print_prover_res pres;
print_newline ();
print_verifier_res vres;;
print_newline ();
print_proof_size proof;
print_newline ();
assert (pres = (Option.get vres));;

Printf.printf "\n* Retrieve magic *\n";;
let proof, pres = Prover_buf_magic_state.run (Merkle_Prover_buf_magic_state.retrieve_magic p t);;
let vres = Verifier_buf_magic_state.run (Merkle_Verifier_buf_magic_state.retrieve_magic p ht) proof;; 

print_prover_res pres;
print_newline ();
print_verifier_res vres;;
print_newline ();
print_proof_size proof;
print_newline ();
assert (pres = (Option.get vres));;

Printf.printf "\n* Retrieve list *\n";;
let ps = List.init 10 (fun _ -> random_path k);;
let proof, pres = Prover_buf_magic_state.run (Merkle_Prover_buf_magic_state.retrieve_list ps t);;
List.iter (fun res -> print_prover_res res; print_newline ()) pres;;

let vres = Verifier_buf_magic_state.run (Merkle_Verifier_buf_magic_state.retrieve_list ps ht) proof;; 
print_proof_size proof;
print_newline ();;

Printf.printf "\n* Retrieve list magic *\n";;
let proof, pres = Prover_buf_magic_state.run (Merkle_Prover_buf_magic_state.retrieve_list_magic ps t);;
List.iter (fun res -> print_prover_res res; print_newline ()) pres;;

let vres = Verifier_buf_magic_state.run (Merkle_Verifier_buf_magic_state.retrieve_list_magic ps ht) proof;; 
print_proof_size proof;
print_newline ();;
