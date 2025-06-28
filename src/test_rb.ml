open Auth
open Redblack
open Proof
open Prover
open Verifier
open Prover_buf
open Verifier_buf
open Prover_orig
open Verifier_buf_magic
open Prover_buf_magic_state
open Verifier_buf_magic_state
open Ideal
open Test_utils

let leaf_size = 20;;
let num_values = 50;;
let num_dels = 5;;

Printf.printf "****** Reverse Optimization ******\n";;
let t = RedBlack_Prover.empty_tree ();;
let ht = Prover.get_hash t;;
let key_vals = random_key_vals num_values leaf_size;;
let (k, v), key_vals = List.hd key_vals, List.tl key_vals;;
let keys, values = List.split key_vals;;

Printf.printf "* Insert to empty *\n";;
let proof, t = Prover.run (RedBlack_Prover.insert k v t);;
let ht' = Prover.get_hash t;;
print_proof_size proof;;
print_newline ();;
let ht = Verifier.run (RedBlack_Verifier.insert k v ht) proof;;
assert (ht' = ht);;

Printf.printf "* Find in one success *\n";;
let proof, pv = Prover.run (RedBlack_Prover.retrieve k t);;
print_proof_size proof;;
print_newline ();;
let vv = Verifier.run (RedBlack_Verifier.retrieve k ht) proof;;
assert (pv = vv);;

Printf.printf "* Find in one failure *\n";;
let proof, pv = Prover.run (RedBlack_Prover.retrieve (k+1) t);;
print_proof_size proof;;
print_newline ();;
let vv = Verifier.run (RedBlack_Verifier.retrieve (k+1) ht) proof;;
assert (pv = vv);;

Printf.printf "* Delete in one *\n";;
let proof, t = Prover.run (RedBlack_Prover.delete k t);;
let ht' = Prover.get_hash t;;
print_proof_size proof;;
print_newline ();;
let ht = Verifier.run (RedBlack_Verifier.delete k ht) proof;;
assert (ht = ht');;

Printf.printf "* Find in empty *\n";;
let proof, pv = Prover.run (RedBlack_Prover.retrieve k t);;
print_proof_size proof;;
print_newline ();;
let vv = Verifier.run (RedBlack_Verifier.retrieve k ht) proof;;
assert (pv = vv);;

Printf.printf "* Insert again *\n";;
let proof, t = Prover.run (RedBlack_Prover.insert k v t);;
let ht' = Prover.get_hash t;;
print_proof_size proof;;
print_newline ();;
let ht = Verifier.run (RedBlack_Verifier.insert k v ht) proof;;
assert (ht' = ht);;

Printf.printf "* Insert list *\n";;
let proof, t = Prover.run (RedBlack_Prover.insert_list keys values t);;
let ht' = Prover.get_hash t;;
print_proof_size proof;;
print_newline ();;
let ht = Verifier.run (RedBlack_Verifier.insert_list keys values ht) proof;;
assert (ht' = ht);;

Printf.printf "* Retrieve list *\n";;
let keys = random_keys num_dels;;
let proof, pres = Prover.run (RedBlack_Prover.retrieve_list keys t);;
print_proof_size proof;;
print_newline ();;
let vres = Verifier.run (RedBlack_Verifier.retrieve_list keys ht) proof;;
assert (pres = vres);;

Printf.printf "* Update list *\n";;
let key_vals = random_key_vals num_values leaf_size;;
let keys, values = List.split key_vals;;
let proof, t = Prover.run (RedBlack_Prover.insert_list keys values t);;
let ht' = Prover.get_hash t;;
print_proof_size proof;;
print_newline ();;
let ht = Verifier.run (RedBlack_Verifier.insert_list keys values ht) proof;;
assert (ht' = ht);;

(* Printf.printf "* Delete list *\n";;
let keys = random_keys num_dels;;
let proof, t = Prover.run (RedBlack_Prover.delete_list keys t);;
let ht' = Prover.get_hash t;;
print_proof_size proof;;
print_newline ();;
let ht = Verifier.run (RedBlack_Verifier.delete_list keys ht) proof;; *)
