open Authentikit.Prover_rev
open Authentikit.Verifier
open Authentikit.Prover_susp
open Authentikit.Verifier_susp
open Authentikit.Test_utils

let k = 3;;
let leaf_size = 20;;
set_default_seed ();

Printf.printf "****** Suspended optimization ******\n";;
let t = random_susp_tree k leaf_size;;
let ht = Prover_susp.get_hash t |> Verifier_susp.make_auth;;
let p = random_path k;;

Printf.printf "* Retrieve *\n";;
let proof, pres = Prover_susp.run (Merkle_Prover_susp.retrieve p t);;
print_proof_size proof;
print_newline ();;
let vres = Verifier_susp.run (Merkle_Verifier_susp.retrieve p ht) proof;;
assert (pres = vres);;

Printf.printf "* Contains x2 *\n";;
match vres with
| None -> ()
| Some s -> (
  let proof, pres = Prover_susp.run (Merkle_Prover_susp.contains s t) in
  print_proof_size proof;
  print_newline ();
  let vres = Verifier_susp.run (Merkle_Verifier_susp.contains s ht) proof in
  assert (pres = vres) )

let proof, pres = Prover_susp.run (Merkle_Prover_susp.contains "" t);;
print_proof_size proof;;
print_newline ();;
let vres = Verifier_susp.run (Merkle_Verifier_susp.contains "" ht) proof;;
assert (pres = vres);;

Printf.printf "* Compare x2 *\n";;
let t2 = random_susp_tree k leaf_size;;
let ht2 = Prover_susp.get_hash t2 |> Verifier_susp.make_auth;;
let proof, pres = Prover_susp.run (Merkle_Prover_susp.compare t t2);;
print_proof_size proof;;
print_newline ();;
let vres = Verifier_susp.run (Merkle_Verifier_susp.compare ht ht2) proof;;
assert (pres = vres);;

let proof, pres = Prover_susp.run (Merkle_Prover_susp.compare t t);;
print_proof_size proof;;
print_newline ();;
let vres = Verifier_susp.run (Merkle_Verifier_susp.compare ht ht) proof;;
assert (pres = vres);;

Printf.printf "* Retrieve list *\n";;
let ps = List.init 10 (fun _ -> random_path k);;
let proof, pres = Prover_susp.run (Merkle_Prover_susp.retrieve_list ps t);;
print_proof_size proof;
print_newline ();;

let vres = Verifier_susp.run (Merkle_Verifier_susp.retrieve_list ps ht) proof;; 
assert (pres = vres);;

Printf.printf "* Update *\n";;
let t = random_susp_tree k leaf_size;;
let ht = Prover_susp.get_hash t |> Verifier_susp.make_auth;;
let p = random_path k;;
let leaf = random_string leaf_size;;
let proof, _ = Prover_susp.run (Merkle_Prover_susp.update p leaf t);;
let _ = Verifier_susp.run (Merkle_Verifier_susp.update p leaf ht) proof;;

print_proof_size proof;
print_newline ();

Printf.printf "* Update list *\n";;
let ps = List.init 10 (fun _ -> random_path k);;
let leaves = random_leaves 10 leaf_size;;
let proof, _ = Prover_susp.run (Merkle_Prover_susp.update_list ps leaves t);;
print_proof_size proof;
print_newline ();;

let _ = Verifier_susp.run (Merkle_Verifier_susp.update_list ps leaves ht) proof;; 

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

let _ = Verifier.run (Merkle_Verifier.retrieve_list ps ht) proof;; 
print_proof_size proof;
print_newline ();;

Printf.printf "* Retrieve list magic *\n";;
let proof, pres = Prover_rev.run (Merkle_Prover_rev.retrieve_list_magic ps t);;
List.iter (fun res -> print_prover_res res; print_newline ()) pres;;

let _ = Verifier.run (Merkle_Verifier.retrieve_list_magic ps ht) proof;; 
print_proof_size proof;
print_newline ();;
