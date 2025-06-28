open Auth
open Prover_rev
open Verifier
open Test_utils

let k = 3;;
let leaf_size = 20;;
let num_leafs = 100;;
let n_retrieve_paths = 50;;
set_default_seed ();

Printf.printf "****** Reverse Optimization ******\n";;
Printf.printf "* Retrieve *\n";;
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
assert (pres = vres);;

Printf.printf "* Contains *\n";;
match vres with
| None -> ()
| Some s -> (
  let proof, pres = Prover_rev.run (Merkle_Prover_rev.contains s t) in
  print_proof_size proof;
  print_newline ();
  let vres = Verifier.run (Merkle_Verifier.contains s ht) proof in
  assert (pres = vres) )

let proof, pres = Prover_rev.run (Merkle_Prover_rev.contains "" t);;
print_proof_size proof;;
print_newline ();;
let vres = Verifier.run (Merkle_Verifier.contains "" ht) proof;;
assert (pres = vres);;

Printf.printf "* Retrieve magic *\n";;
let proof, pres = Prover_rev.run (Merkle_Prover_rev.retrieve_magic p t);;

print_prover_res pres;
print_newline ();;
print_proof_size proof;
print_newline ();;

let vres = Verifier.run (Merkle_Verifier.retrieve_magic p ht) proof;; 
print_verifier_res vres;;
print_newline ();
assert (pres = vres);;

Printf.printf "* Retrieve list *\n";;
let ps = List.init 10 (fun _ -> let p = random_path k in print_path p; p);;
let proof, pres = Prover_rev.run (Merkle_Prover_rev.retrieve_list ps t);;
List.iter (fun res -> print_prover_res res; print_newline ()) pres;;

let vres = Verifier.run (Merkle_Verifier.retrieve_list ps ht) proof;; 
print_proof_size proof;
print_newline ();;

Printf.printf "* Retrieve list magic *\n";;
let proof, pres = Prover_rev.run (Merkle_Prover_rev.retrieve_list_magic ps t);;
List.iter (fun res -> print_prover_res res; print_newline ()) pres;;

let vres = Verifier.run (Merkle_Verifier.retrieve_list_magic ps ht) proof;; 
print_proof_size proof;
print_newline ();;
