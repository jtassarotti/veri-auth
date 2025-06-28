open Auth
open Merkle
(* open Merkle_sparse *)
open Prover
open Verifier
(* open Prover_buf
open Verifier_buf
open Prover_orig
open Verifier_buf_magic
open Prover_buf_magic_state
open Verifier_buf_magic_state *)
open Prover_susp
open Verifier_susp
(* open Prover_susp_buf
open Verifier_susp_buf *)
open Ideal
open Test_utils

let k = 3.;;
let leaf_size = 20;;
let num_leafs = 100;;
let n_retrieve_paths = 50;;
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
let proof, pres = Prover_susp.run (Merkle_Prover_susp.update p leaf t);;
let vres = Verifier_susp.run (Merkle_Verifier_susp.update p leaf ht) proof;;

(* print_prover_res proof pres;
print_newline ();
print_verifier_res vres;;
print_newline (); *)
print_proof_size proof;
print_newline ();
(* assert (pres = vres);; *)

Printf.printf "* Update list *\n";;
let ps = List.init 10 (fun _ -> random_path k);;
let leaves = random_leaves 10. leaf_size;;
let proof, pres = Prover_susp.run (Merkle_Prover_susp.update_list ps leaves t);;
(* List.iter (fun res -> print_prover_res proof res; print_newline ()) pres;; *)
print_proof_size proof;
print_newline ();;

let vres = Verifier_susp.run (Merkle_Verifier_susp.update_list ps leaves ht) proof;; 
(* assert (pres = vres);; *)

(* Printf.printf "****** Suspended buffer optimization ******\n";;
let t = random_susp_buf_tree k leaf_size;;
let ht = Prover_susp_buf.get_hash t |> Verifier_susp_buf.make_auth;;
let p = random_path k;;
let prov_path = path_prover_susp_buf p;;
let ver_path = path_verifier_susp_buf p;;
let proof, pres = Prover_susp_buf.run (Merkle_Prover_susp_buf.retrieve prov_path t);;
Printf.printf "* Retrieve *\n";;
print_proof_size proof;
print_newline ();;

let vres = Verifier_susp_buf.run (Merkle_Verifier_susp_buf.retrieve ver_path ht) proof;;
print_verifier_res vres;
print_newline ();
assert (pres = vres);;

Printf.printf "* Contains x2 *\n";;
match vres with
| None -> ()
| Some s -> (
  let proof, pres = Prover_susp_buf.run (Merkle_Prover_susp_buf.contains s t) in
  print_proof_size proof;
  print_newline ();
  let vres = Verifier_susp_buf.run (Merkle_Verifier_susp_buf.contains s ht) proof in
  assert (pres = vres) )

let proof, pres = Prover_susp_buf.run (Merkle_Prover_susp_buf.contains "" t);;
print_proof_size proof;;
print_newline ();;
let vres = Verifier_susp_buf.run (Merkle_Verifier_susp_buf.contains "" ht) proof;;
assert (pres = vres);;

Printf.printf "* Compare x2 *\n";;
let t2 = random_susp_buf_tree k leaf_size;;
let ht2 = Prover_susp_buf.get_hash t2 |> Verifier_susp_buf.make_auth;;
let proof, pres = Prover_susp_buf.run (Merkle_Prover_susp_buf.compare t t2);;
print_proof_size proof;;
print_newline ();;
let vres = Verifier_susp_buf.run (Merkle_Verifier_susp_buf.compare ht ht2) proof;;
assert (pres = vres);;

let proof, pres = Prover_susp_buf.run (Merkle_Prover_susp_buf.compare t t);;
print_proof_size proof;;
print_newline ();;
let vres = Verifier_susp_buf.run (Merkle_Verifier_susp_buf.compare ht ht) proof;;
assert (pres = vres);;

Printf.printf "* Retrieve list *\n";;
let ps = List.init 10 (fun _ -> random_path k);;
let prover_ps = List.map path_prover_susp_buf ps;;
let verifier_ps = List.map path_verifier_susp_buf ps;;
let proof, pres = Prover_susp_buf.run (Merkle_Prover_susp_buf.retrieve_list prover_ps t);;
List.iter (fun res -> print_prover_res proof res; print_newline ()) pres;;
print_proof_size proof;
print_newline ();;

let vres = Verifier_susp_buf.run (Merkle_Verifier_susp_buf.retrieve_list verifier_ps ht) proof;; 
assert (pres = vres);;

Printf.printf "* Update *\n";;
let t = random_susp_buf_tree k leaf_size;;
let ht = Prover_susp_buf.get_hash t |> Verifier_susp_buf.make_auth;;
let p = random_path k;;
let prov_path = path_prover_susp_buf p;;
let ver_path = path_verifier_susp_buf p;;
let leaf = random_string leaf_size;;
let proof, pres = Prover_susp_buf.run (Merkle_Prover_susp_buf.update prov_path leaf t);;
let vres = Verifier_susp_buf.run (Merkle_Verifier_susp_buf.update ver_path leaf ht) proof;;

(* print_prover_res proof pres;
print_newline ();
print_verifier_res vres;;
print_newline (); *)
print_proof_size proof;
print_newline ();
(* assert (pres = vres);; *)

Printf.printf "* Update list *\n";;
let ps = List.init 10 (fun _ -> random_path k);;
let prover_ps = List.map path_prover_susp_buf ps;;
let verifier_ps = List.map path_verifier_susp_buf ps;;
let leaves = random_leaves 10 leaf_size;;
let proof, pres = Prover_susp_buf.run (Merkle_Prover_susp_buf.update_list prover_ps leaves t);;
(* List.iter (fun res -> print_prover_res proof res; print_newline ()) pres;; *)
print_proof_size proof;
print_newline ();;

let vres = Verifier_susp_buf.run (Merkle_Verifier_susp_buf.update_list verifier_ps leaves ht) proof;;  *)
(* assert (pres = vres);; *)

(* Printf.printf "****** Reverse Optimization ******\n";;
let t = random_tree k leaf_size;;
let ht = Prover.get_hash t;;
let p = random_path k;;
let prov_path = path_prover p;;
let ver_path = path_verifier p;;
let proof, pres = Prover.run (Merkle_Prover.retrieve prov_path t);;
let vres = Verifier.run (Merkle_Verifier.retrieve ver_path ht) proof;;
       
print_prover_res proof pres;
print_newline ();
print_verifier_res vres;;
print_newline ();
print_proof_size proof;
print_newline ();
assert (pres = vres);;

match vres with
| None -> ()
| Some s -> (
  let proof, pres = Prover.run (Merkle_Prover.contains s t) in
  print_proof_size proof;
  print_newline ();
  let vres = Verifier.run (Merkle_Verifier.contains s ht) proof in
  assert (pres = vres) )

let proof, pres = Prover.run (Merkle_Prover.contains "" t);;
print_proof_size proof;;
print_newline ();;
let vres = Verifier.run (Merkle_Verifier.contains "" ht) proof;;
assert (pres = vres);;

let proof, pres = Prover.run (Merkle_Prover.retrieve_magic prov_path t);;

print_prover_res proof pres;
print_newline ();;
print_proof_size proof;
print_newline ();;

let vres = Verifier.run (Merkle_Verifier.retrieve_magic ver_path ht) proof;; 
print_verifier_res vres;;
print_newline ();
assert (pres = vres);;

let ps = List.init 10 (fun _ -> random_path k);;
let prover_ps = List.map path_prover ps;;
let verifier_ps = List.map path_verifier ps;;
let proof, pres = Prover.run (Merkle_Prover.retrieve_list prover_ps t);;
List.iter (fun res -> print_prover_res proof res; print_newline ()) pres;;

let vres = Merkle_Verifier.retrieve_list verifier_ps ht proof;; 
print_proof_size proof;
print_newline ();
assert (equal_res pres vres);;

let proof, pres = Prover.run (Merkle_Prover.retrieve_list_magic prover_ps t);;
List.iter (fun res -> print_prover_res proof res; print_newline ()) pres;;

let vres = Merkle_Verifier.retrieve_list_magic verifier_ps ht proof;; 
print_proof_size proof;
print_newline ();
assert (equal_res pres vres);; *)

(* let t2 = random_tree k leaf_size;;
let ht2 = Prover.get_hash t2;;
let proof, pres = Prover.run (Merkle_Prover.compare t t2);;
print_proof_size proof;;
print_newline ();;
let vres = Verifier.run (Merkle_Verifier.compare ht ht2) proof;;
assert (pres = vres);;

let proof, pres = Prover.run (Merkle_Prover.compare t t);;
print_proof_size proof;;
print_newline ();;
let vres = Verifier.run (Merkle_Verifier.compare ht ht) proof;;
assert (pres = vres);; *)

(* Printf.printf "****** Original ******\n"
let t = random_orig_tree k leaf_size;;
let ht = Prover_orig.get_hash t;;
let p = random_path (k+1);;
let prov_path = path_prover_orig p;;
let ver_path = path_verifier p;;
let proof, pres = Prover_orig.run (Merkle_Prover_orig.retrieve prov_path t);;
let vres = Verifier.run (Merkle_Verifier.retrieve ver_path ht) proof;;

print_prover_res proof pres;
print_newline ();
print_verifier_res vres;;
print_newline ();
print_proof_size proof;
print_newline ();
assert (pres = vres);;

let proof, pres = Prover_orig.run (Merkle_Prover_orig.retrieve_magic prov_path t);;

print_prover_res proof pres;
print_newline ();;
print_proof_size proof;
print_newline ();;

let vres = Verifier.run (Merkle_Verifier.retrieve_magic ver_path ht) proof;; 
print_verifier_res vres;;
print_newline ();
assert (pres = vres);;

let ps = List.init 10 (fun _ -> random_path k);;
let prover_ps = List.map path_prover_orig ps;;
let verifier_ps = List.map path_verifier ps;;
let proof, pres = Prover_orig.run (Merkle_Prover_orig.retrieve_list prover_ps t);;
List.iter (fun res -> print_prover_res proof res; print_newline ()) pres;;

let vres = Merkle_Verifier.retrieve_list verifier_ps ht proof;; 
print_proof_size proof;
print_newline ();
assert (equal_res pres vres);;

let proof, pres = Prover_orig.run (Merkle_Prover_orig.retrieve_list_magic prover_ps t);;
List.iter (fun res -> print_prover_res proof res; print_newline ()) pres;;

let vres = Merkle_Verifier.retrieve_list_magic verifier_ps ht proof;; 
print_proof_size proof;
print_newline ();
assert (equal_res pres vres);; *)

(* Printf.printf "****** Buffer Optimization ******\n"
let t = random_buf_tree k leaf_size;;
let ht = Prover_buf.get_hash t;;
let p = random_path k;;
let prover_path = path_prover_buf p;;
let verifier_path = path_verifier_buf p;;
let proof, pres = Prover_buf.run (Merkle_Prover_buf.retrieve prover_path t);;
let vres = Verifier_buf.run (Merkle_Verifier_buf.retrieve verifier_path ht) proof;; 

print_prover_res proof pres;
print_newline ();
print_verifier_res vres;;
print_newline ();
print_proof_size proof;
print_newline ();
assert (pres = vres);;

let proof, pres = Prover_buf.run (Merkle_Prover_buf.retrieve_magic prover_path t);;
let vres = Verifier_buf.run (Merkle_Verifier_buf.retrieve_magic verifier_path ht) proof;; 

print_prover_res proof pres;
print_newline ();
print_verifier_res vres;;
print_newline ();
print_proof_size proof;
print_newline ();
assert (pres = vres);;

let ps = List.init 10 (fun _ -> random_path k);;
let prover_ps = List.map path_prover_buf ps;;
let verifier_ps = List.map path_verifier_buf ps;;
let proof, pres = Prover_buf.run (Merkle_Prover_buf.retrieve_list prover_ps t);;
List.iter (fun res -> print_prover_res proof res; print_newline ()) pres;;

let vres = Verifier_buf.run (Merkle_Verifier_buf.retrieve_list verifier_ps ht) proof;; 
print_proof_size proof;
print_newline ();
assert (pres = vres);;

let proof, pres = Prover_buf.run (Merkle_Prover_buf.retrieve_list_magic prover_ps t);;
List.iter (fun res -> print_prover_res proof res; print_newline ()) pres;;

let vres = Verifier_buf.run (Merkle_Verifier_buf.retrieve_list_magic verifier_ps ht) proof;; 
print_proof_size proof;
print_newline ();
assert (pres = vres);; *)

(* Printf.printf "****** Buffer Magic Optimization ******\n"
let t = random_buf_tree k leaf_size;;
let ht = Prover_buf.get_hash t;;
let p = random_path (k-1);;
let prover_path = path_prover_buf p;;
let verifier_path = path_verifier_buf_magic p;;
let proof, pres = Prover_buf.run (Merkle_Prover_buf.retrieve prover_path t);;
let vres = Verifier_buf_magic.run (Merkle_Verifier_buf_magic.retrieve verifier_path ht) proof;; 

print_prover_res proof pres;
print_newline ();
print_verifier_res vres;;
print_newline ();
print_proof_size proof;
print_newline ();
assert (pres = vres);;

let proof, pres = Prover_buf.run (Merkle_Prover_buf.retrieve_magic prover_path t);;
let vres = Verifier_buf_magic.run (Merkle_Verifier_buf_magic.retrieve_magic verifier_path ht) proof;; 

print_prover_res proof pres;
print_newline ();
print_verifier_res vres;;
print_newline ();
print_proof_size proof;
print_newline ();
assert (pres = vres);;

let ps = List.init 10 (fun _ -> random_path k);;
let prover_ps = List.map path_prover_buf ps;;
let verifier_ps = List.map path_verifier_buf_magic ps;;
let proof, pres = Prover_buf.run (Merkle_Prover_buf.retrieve_list prover_ps t);;
List.iter (fun res -> print_prover_res proof res; print_newline ()) pres;;

let vres = Verifier_buf_magic.run (Merkle_Verifier_buf_magic.retrieve_list verifier_ps ht) proof;; 
print_proof_size proof;
print_newline ();
assert (pres = vres);;

let proof, pres = Prover_buf.run (Merkle_Prover_buf.retrieve_list_magic prover_ps t);;
List.iter (fun res -> print_prover_res proof res; print_newline ()) pres;;

let vres = Verifier_buf_magic.run (Merkle_Verifier_buf_magic.retrieve_list_magic verifier_ps ht) proof;; 
print_proof_size proof;
print_newline ();
assert (pres = vres);;

Printf.printf "****** Buffer Magic State Optimization ******\n"
let t = random_buf_magic_state_tree k leaf_size;;
let ht = Prover_buf_magic_state.get_hash t;;
let p = random_path (k-1);;
let prover_path = path_prover_buf_magic_state p;;
let verifier_path = path_verifier_buf_magic_state p;;
let proof, pres = Prover_buf_magic_state.run (Merkle_Prover_buf_magic_state.retrieve prover_path t);;
let vres = Verifier_buf_magic_state.run (Merkle_Verifier_buf_magic_state.retrieve verifier_path ht) proof;; 

print_prover_res proof pres;
print_newline ();
print_verifier_res vres;;
print_newline ();
print_proof_size proof;
print_newline ();
assert (pres = vres);;

let proof, pres = Prover_buf_magic_state.run (Merkle_Prover_buf_magic_state.retrieve_magic prover_path t);;
let vres = Verifier_buf_magic_state.run (Merkle_Verifier_buf_magic_state.retrieve_magic verifier_path ht) proof;; 

print_prover_res proof pres;
print_newline ();
print_verifier_res vres;;
print_newline ();
print_proof_size proof;
print_newline ();
assert (pres = vres);;

let ps = List.init 10 (fun _ -> random_path k);;
let prover_ps = List.map path_prover_buf_magic_state ps;;
let verifier_ps = List.map path_verifier_buf_magic_state ps;;
let proof, pres = Prover_buf_magic_state.run (Merkle_Prover_buf_magic_state.retrieve_list prover_ps t);;
List.iter (fun res -> print_prover_res proof res; print_newline ()) pres;;

let vres = Verifier_buf_magic_state.run (Merkle_Verifier_buf_magic_state.retrieve_list verifier_ps ht) proof;; 
print_proof_size proof;
print_newline ();
assert (pres = vres);;

let proof, pres = Prover_buf_magic_state.run (Merkle_Prover_buf_magic_state.retrieve_list_magic prover_ps t);;
List.iter (fun res -> print_prover_res proof res; print_newline ()) pres;;

let vres = Verifier_buf_magic_state.run (Merkle_Verifier_buf_magic_state.retrieve_list_magic verifier_ps ht) proof;; 
print_proof_size proof;
print_newline ();
assert (pres = vres);; *)

(* let pt = List.fold_left (fun pt p -> Merkle_Prover.add_path_path_tree p pt) Emp ps;;

let proof1, pres1 = Prover.run (Merkle_Prover.retrieve_path_tree1 pt t);;
let proof2, pres2 = Prover.run (Merkle_Prover.retrieve_path_tree2 pt t);;

Printf.printf "\nPTree1: %d\nPTree2: %d\n" (List.length proof1) (List.length proof2);; *)

(* module Merkle_Prover_buf = Merkle (Prover_buf);;
module Merkle_Verifier_buf = Merkle (Verifier_buf);;

 let random_tree height leaf_len =
  let l = random_leaves (Core.Int.pow 2 height) leaf_len in
  Merkle_Prover_buf.from_list l
;;

let t = random_tree k leaf_size;;
let ht = Prover_buf.get_hash t;;

let proof, pres = Prover_buf.run (Merkle_Prover_buf.retrieve_list ps t);;

List.iter (fun res -> print_prover_res proof res; print_newline ()) pres;;

let vres = Verifier_buf.run (Merkle_Verifier_buf.retrieve_list ps ht) proof;; 
assert (pres = vres);;

module Merkle_Sparse_Prover_buf = Merkle_sparse (Prover_buf);;
module Merkle_Sparse_Verifier_buf = Merkle_sparse (Verifier_buf);;

let leaves = random_leaves num_leafs leaf_size ;;
let paths = random_paths num_leafs k ;;
let paths2 = random_paths n_retrieve_paths k ;;

let n_proof, n_pres = 
  let t = Merkle_Prover.init_tree k in 
  Prover.run (Merkle_Prover.update_list paths leaves t) ;;

let s_proof, s_pres = 
  let t = Merkle_Sparse_Prover.init_tree k in
  Prover.run (Merkle_Sparse_Prover.update_list paths leaves t) ;;

let n_tree, s_tree = Option.get n_pres, Option.get s_pres ;;

Printf.printf "\nNormal Tree Update Proof: %d\nSparse Tree Update Proof: %d\n" (List.length n_proof) (List.length s_proof);;

let n_ht, s_ht = Prover.get_hash n_tree, Prover.get_hash s_tree ;;

let n_proof, n_pres = Prover.run (Merkle_Prover.retrieve_list paths2 n_tree) ;;
let s_proof, s_pres = Prover.run (Merkle_Sparse_Prover.retrieve_list paths2 s_tree) ;;

List.combine n_pres s_pres |> List.iter (fun (n_pre, s_pre) -> print_opt_string n_pre; print_opt_string s_pre; Printf.printf "\n");;

Printf.printf "\nNormal Tree Retrieve Proof: %d\nSparse Tree Retrieve Proof: %d\n" (List.length n_proof) (List.length s_proof);;

let n_vres = Verifier.run (Merkle_Verifier.retrieve_list paths2 n_ht) n_proof;;
assert (n_pres = n_vres);;
Printf.printf "Normal merkle correct\n"

let s_vres = Verifier.run (Merkle_Sparse_Verifier.retrieve_list paths2 s_ht) s_proof;;
assert (s_pres = s_vres);;
Printf.printf "Sparse merkle correct\n"

let n_proof, n_pres = 
  let t = Merkle_Prover_buf.init_tree k in 
  Prover_buf.run (Merkle_Prover_buf.update_list paths leaves t) ;;

let s_proof, s_pres = 
  let t = Merkle_Sparse_Prover_buf.init_tree k in
  Prover_buf.run (Merkle_Sparse_Prover_buf.update_list paths leaves t) ;;

let n_tree, s_tree = Option.get n_pres, Option.get s_pres ;;

Printf.printf "\nNormal Reuse Update Tree Proof: %d\nSparse Reuse Update Tree Proof: %d\n" (List.length n_proof) (List.length s_proof);;

let n_ht, s_ht = Prover_buf.get_hash n_tree, Prover_buf.get_hash s_tree ;;

let n_proof, n_pres = Prover_buf.run (Merkle_Prover_buf.retrieve_list paths2 n_tree) ;;
let s_proof, s_pres = Prover_buf.run (Merkle_Sparse_Prover_buf.retrieve_list paths2 s_tree) ;;

List.combine n_pres s_pres |> List.iter (fun (n_pre, s_pre) -> print_opt_string n_pre; print_opt_string s_pre; Printf.printf "\n");;

Printf.printf "\nNormal Reuse Retrieve Tree Proof: %d\nSparse Reuse Retrieve Tree Proof: %d\n" (List.length n_proof) (List.length s_proof);;

let n_vres = Verifier_buf.run (Merkle_Verifier_buf.retrieve_list paths2 n_ht) n_proof;;
assert (n_pres = n_vres);;
Printf.printf "Normal Reuse merkle correct\n"

let s_vres = Verifier_buf.run (Merkle_Sparse_Verifier_buf.retrieve_list paths2 s_ht) s_proof;;
assert (s_pres = s_vres);;
Printf.printf "Sparse Reuse merkle correct\n" *)