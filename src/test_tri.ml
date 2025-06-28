open Auth
open Trimerkle
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

module TriMerkle_Prover = TriMerkle (Prover);;
module TriMerkle_Verifier = TriMerkle (Verifier);;
module TriMerkle_Prover_buf = TriMerkle (Prover_buf);;
module TriMerkle_Verifier_buf = TriMerkle (Verifier_buf);;
module TriMerkle_Prover_orig = TriMerkle (Prover_orig);;
module TriMerkle_Verifier_buf_magic = TriMerkle (Verifier_buf_magic);;
module TriMerkle_Prover_buf_magic_state = TriMerkle (Prover_buf_magic_state);;
module TriMerkle_Verifier_buf_magic_state = TriMerkle (Verifier_buf_magic_state);;

let k = 3;;
let leaf_size = 20;;
let num_leafs = 100;;
let n_retrieve_tripaths = 50;;

let rec random_tripath height =
  match height with
  | 0 -> []
  | _  ->
    let n = Core.Random.int 3 in
    let next =
      if n=0 then
        `L
      else if n=1 then
        `M
      else
        `R
    in
    next :: random_tripath (height-1)
;;

let rec tripath_prover path =
  match path with
  | [] -> TriMerkle_Prover.path_empty
  | `L :: t ->
    tripath_prover t |> TriMerkle_Prover.path_left
  | `M :: t ->
    tripath_prover t |> TriMerkle_Prover.path_middle
  | `R :: t ->
    tripath_prover t |> TriMerkle_Prover.path_right

let rec tripath_verifier path =
  match path with
  | [] -> TriMerkle_Verifier.path_empty
  | `L :: t ->
    tripath_verifier t |> TriMerkle_Verifier.path_left
  | `M :: t ->
    tripath_verifier t |> TriMerkle_Verifier.path_middle
  | `R :: t ->
    tripath_verifier t |> TriMerkle_Verifier.path_right

let rec tripath_prover_orig path =
  match path with
  | [] -> TriMerkle_Prover_orig.path_empty
  | `L :: t ->
    tripath_prover_orig t |> TriMerkle_Prover_orig.path_left
  | `M :: t ->
    tripath_prover_orig t |> TriMerkle_Prover_orig.path_middle
  | `R :: t ->
    tripath_prover_orig t |> TriMerkle_Prover_orig.path_right

let rec tripath_prover_buf path =
  match path with
  | [] -> TriMerkle_Prover_buf.path_empty
  | `L :: t ->
    tripath_prover_buf t |> TriMerkle_Prover_buf.path_left
  | `M :: t ->
    tripath_prover_buf t |> TriMerkle_Prover_buf.path_middle
  | `R :: t ->
    tripath_prover_buf t |> TriMerkle_Prover_buf.path_right

let rec tripath_verifier_buf path =
  match path with
  | [] -> TriMerkle_Verifier_buf.path_empty
  | `L :: t ->
    tripath_verifier_buf t |> TriMerkle_Verifier_buf.path_left
  | `M :: t ->
    tripath_verifier_buf t |> TriMerkle_Verifier_buf.path_middle
  | `R :: t ->
    tripath_verifier_buf t |> TriMerkle_Verifier_buf.path_right

let rec tripath_verifier_buf_magic path =
  match path with
  | [] -> TriMerkle_Verifier_buf_magic.path_empty
  | `L :: t ->
    tripath_verifier_buf_magic t |> TriMerkle_Verifier_buf_magic.path_left
  | `M :: t ->
    tripath_verifier_buf_magic t |> TriMerkle_Verifier_buf_magic.path_middle
  | `R :: t ->
    tripath_verifier_buf_magic t |> TriMerkle_Verifier_buf_magic.path_right

let rec tripath_prover_buf_magic_state path =
  match path with
  | [] -> TriMerkle_Prover_buf_magic_state.path_empty
  | `L :: t ->
    tripath_prover_buf_magic_state t |> TriMerkle_Prover_buf_magic_state.path_left
  | `M :: t ->
    tripath_prover_buf_magic_state t |> TriMerkle_Prover_buf_magic_state.path_middle
  | `R :: t ->
    tripath_prover_buf_magic_state t |> TriMerkle_Prover_buf_magic_state.path_right

let rec tripath_verifier_buf_magic_state path =
  match path with
  | [] -> TriMerkle_Verifier_buf_magic_state.path_empty
  | `L :: t ->
    tripath_verifier_buf_magic_state t |> TriMerkle_Verifier_buf_magic_state.path_left
  | `M :: t ->
    tripath_verifier_buf_magic_state t |> TriMerkle_Verifier_buf_magic_state.path_middle
  | `R :: t ->
    tripath_verifier_buf_magic_state t |> TriMerkle_Verifier_buf_magic_state.path_right

let rec random_tripaths num height =
  let rec go num acc =
    match num with
    | 0 -> acc
    | _ -> go (num - 1) ((random_tripath height |> tripath_prover) :: acc)
  in
  go num []
;;

let random_tritree height leaf_len =
  let l = random_leaves (((Core.Int.pow 3 (height+1))-1)/2) leaf_len in
  TriMerkle_Prover.from_list l
;;

let random_orig_tritree height leaf_len =
  let l = random_leaves (((Core.Int.pow 3 (height+1))-1)/2) leaf_len in
  TriMerkle_Prover_orig.from_list l
;;

let random_buf_tritree height leaf_len =
  let l = random_leaves (((Core.Int.pow 3 (height+1))-1)/2) leaf_len in
  TriMerkle_Prover_buf.from_list l
;;

let random_buf_magic_state_tritree height leaf_len =
  let l = random_leaves (((Core.Int.pow 3 (height+1))-1)/2) leaf_len in
  TriMerkle_Prover_buf_magic_state.from_list l
;;

Printf.printf "****** Reverse Optimization ******\n";;
let t = random_tritree k leaf_size;;
let ht = Prover.get_hash t;;
let p = random_tripath k;;
let prov_tripath = tripath_prover p;;
let ver_tripath = tripath_verifier p;;
let proof, pres = Prover.run (TriMerkle_Prover.retrieve prov_tripath t);;
let vres = Verifier.run (TriMerkle_Verifier.retrieve ver_tripath ht) proof;;
       
print_prover_res pres;
print_newline ();
print_verifier_res vres;;
print_newline ();
print_proof_size proof;
print_newline ();
assert (pres = vres);;

match vres with
| None -> ()
| Some s -> (
  let proof, pres = Prover.run (TriMerkle_Prover.contains s t) in
  print_proof_size proof;
  print_newline ();
  let vres = Verifier.run (TriMerkle_Verifier.contains s ht) proof in
  assert (pres = vres) )

let proof, pres = Prover.run (TriMerkle_Prover.contains "" t);;
print_proof_size proof;;
print_newline ();;
let vres = Verifier.run (TriMerkle_Verifier.contains "" ht) proof;;
assert (pres = vres);;

let ps = List.init 10 (fun _ -> random_tripath k);;
let prover_ps = List.map tripath_prover ps;;
let verifier_ps = List.map tripath_verifier ps;;
let proof, pres = Prover.run (TriMerkle_Prover.retrieve_list prover_ps t);;
List.iter (fun res -> print_prover_res res; print_newline ()) pres;;

let vres = Verifier.run (TriMerkle_Verifier.retrieve_list verifier_ps ht) proof;; 
print_proof_size proof;
print_newline ();;
(* assert (equal_res pres vres);; *)

let t2 = random_tritree k leaf_size;;
let ht2 = Prover.get_hash t2;;
let proof, pres = Prover.run (TriMerkle_Prover.compare t t2);;
print_proof_size proof;;
print_newline ();;
let vres = Verifier.run (TriMerkle_Verifier.compare ht ht2) proof;;
assert (pres = vres);;

let proof, pres = Prover.run (TriMerkle_Prover.compare t t);;
print_proof_size proof;;
print_newline ();;
let vres = Verifier.run (TriMerkle_Verifier.compare ht ht) proof;;
assert (pres = vres);;

(* Printf.printf "****** Original ******\n"
let t = random_orig_tritree k leaf_size;;
let ht = Prover_orig.get_hash t;;
let p = random_tripath (k+1);;
let prov_tripath = path_prover_orig p;;
let ver_tripath = path_verifier p;;
let proof, pres = Prover_orig.run (TriMerkle_Prover_orig.retrieve prov_tripath t);;
let vres = Verifier.run (TriMerkle_Verifier.retrieve ver_tripath ht) proof;;

print_prover_res proof pres;
print_newline ();
print_verifier_res vres;;
print_newline ();
print_proof_size proof;
print_newline ();
assert (pres = vres);;

let proof, pres = Prover_orig.run (TriMerkle_Prover_orig.retrieve_magic prov_tripath t);;

print_prover_res proof pres;
print_newline ();;
print_proof_size proof;
print_newline ();;

let vres = Verifier.run (TriMerkle_Verifier.retrieve_magic ver_tripath ht) proof;; 
print_verifier_res vres;;
print_newline ();
assert (pres = vres);;

let ps = List.init 10 (fun _ -> random_tripath k);;
let prover_ps = List.map path_prover_orig ps;;
let verifier_ps = List.map path_verifier ps;;
let proof, pres = Prover_orig.run (TriMerkle_Prover_orig.retrieve_list prover_ps t);;
List.iter (fun res -> print_prover_res proof res; print_newline ()) pres;;

let vres = TriMerkle_Verifier.retrieve_list verifier_ps ht proof;; 
print_proof_size proof;
print_newline ();
assert (equal_res pres vres);;

let proof, pres = Prover_orig.run (TriMerkle_Prover_orig.retrieve_list_magic prover_ps t);;
List.iter (fun res -> print_prover_res proof res; print_newline ()) pres;;

let vres = TriMerkle_Verifier.retrieve_list_magic verifier_ps ht proof;; 
print_proof_size proof;
print_newline ();
assert (equal_res pres vres);; *)

Printf.printf "****** Buffer Optimization ******\n"
let t = random_buf_tritree k leaf_size;;
let ht = Prover_buf.get_hash t;;
let p = random_tripath k;;
let prover_tripath = tripath_prover_buf p;;
let verifier_tripath = tripath_verifier_buf p;;
let proof, pres = Prover_buf.run (TriMerkle_Prover_buf.retrieve prover_tripath t);;
let vres = Verifier_buf.run (TriMerkle_Verifier_buf.retrieve verifier_tripath ht) proof;; 

print_prover_res pres;
print_newline ();
print_verifier_res vres;;
print_newline ();
print_proof_size proof;
print_newline ();
assert (pres = vres);;

let ps = List.init 10 (fun _ -> random_tripath k);;
let prover_ps = List.map tripath_prover_buf ps;;
let verifier_ps = List.map tripath_verifier_buf ps;;
let proof, pres = Prover_buf.run (TriMerkle_Prover_buf.retrieve_list prover_ps t);;
List.iter (fun res -> print_prover_res res; print_newline ()) pres;;

let vres = Verifier_buf.run (TriMerkle_Verifier_buf.retrieve_list verifier_ps ht) proof;; 
print_proof_size proof;
print_newline ();
assert (pres = vres);;

(* Printf.printf "****** Buffer Magic Optimization ******\n"
let t = random_buf_tritree k leaf_size;;
let ht = Prover_buf.get_hash t;;
let p = random_tripath (k-1);;
let prover_tripath = path_prover_buf p;;
let verifier_tripath = path_verifier_buf_magic p;;
let proof, pres = Prover_buf.run (TriMerkle_Prover_buf.retrieve prover_tripath t);;
let vres = Verifier_buf_magic.run (TriMerkle_Verifier_buf_magic.retrieve verifier_tripath ht) proof;; 

print_prover_res proof pres;
print_newline ();
print_verifier_res vres;;
print_newline ();
print_proof_size proof;
print_newline ();
assert (pres = vres);;

let proof, pres = Prover_buf.run (TriMerkle_Prover_buf.retrieve_magic prover_tripath t);;
let vres = Verifier_buf_magic.run (TriMerkle_Verifier_buf_magic.retrieve_magic verifier_tripath ht) proof;; 

print_prover_res proof pres;
print_newline ();
print_verifier_res vres;;
print_newline ();
print_proof_size proof;
print_newline ();
assert (pres = vres);;

let ps = List.init 10 (fun _ -> random_tripath k);;
let prover_ps = List.map path_prover_buf ps;;
let verifier_ps = List.map path_verifier_buf_magic ps;;
let proof, pres = Prover_buf.run (TriMerkle_Prover_buf.retrieve_list prover_ps t);;
List.iter (fun res -> print_prover_res proof res; print_newline ()) pres;;

let vres = Verifier_buf_magic.run (TriMerkle_Verifier_buf_magic.retrieve_list verifier_ps ht) proof;; 
print_proof_size proof;
print_newline ();
assert (pres = vres);;

let proof, pres = Prover_buf.run (TriMerkle_Prover_buf.retrieve_list_magic prover_ps t);;
List.iter (fun res -> print_prover_res proof res; print_newline ()) pres;;

let vres = Verifier_buf_magic.run (TriMerkle_Verifier_buf_magic.retrieve_list_magic verifier_ps ht) proof;; 
print_proof_size proof;
print_newline ();
assert (pres = vres);;

Printf.printf "****** Buffer Magic State Optimization ******\n"
let t = random_buf_magic_state_tritree k leaf_size;;
let ht = Prover_buf_magic_state.get_hash t;;
let p = random_tripath (k-1);;
let prover_tripath = path_prover_buf_magic_state p;;
let verifier_tripath = path_verifier_buf_magic_state p;;
let proof, pres = Prover_buf_magic_state.run (TriMerkle_Prover_buf_magic_state.retrieve prover_tripath t);;
let vres = Verifier_buf_magic_state.run (TriMerkle_Verifier_buf_magic_state.retrieve verifier_tripath ht) proof;; 

print_prover_res proof pres;
print_newline ();
print_verifier_res vres;;
print_newline ();
print_proof_size proof;
print_newline ();
assert (pres = vres);;

let proof, pres = Prover_buf_magic_state.run (TriMerkle_Prover_buf_magic_state.retrieve_magic prover_tripath t);;
let vres = Verifier_buf_magic_state.run (TriMerkle_Verifier_buf_magic_state.retrieve_magic verifier_tripath ht) proof;; 

print_prover_res proof pres;
print_newline ();
print_verifier_res vres;;
print_newline ();
print_proof_size proof;
print_newline ();
assert (pres = vres);;

let ps = List.init 10 (fun _ -> random_tripath k);;
let prover_ps = List.map path_prover_buf_magic_state ps;;
let verifier_ps = List.map path_verifier_buf_magic_state ps;;
let proof, pres = Prover_buf_magic_state.run (TriMerkle_Prover_buf_magic_state.retrieve_list prover_ps t);;
List.iter (fun res -> print_prover_res proof res; print_newline ()) pres;;

let vres = Verifier_buf_magic_state.run (TriMerkle_Verifier_buf_magic_state.retrieve_list verifier_ps ht) proof;; 
print_proof_size proof;
print_newline ();
assert (pres = vres);;

let proof, pres = Prover_buf_magic_state.run (TriMerkle_Prover_buf_magic_state.retrieve_list_magic prover_ps t);;
List.iter (fun res -> print_prover_res proof res; print_newline ()) pres;;

let vres = Verifier_buf_magic_state.run (TriMerkle_Verifier_buf_magic_state.retrieve_list_magic verifier_ps ht) proof;; 
print_proof_size proof;
print_newline ();
assert (pres = vres);; *)

(* let pt = List.fold_left (fun pt p -> TriMerkle_Prover.add_tripath_tripath_tritree p pt) Emp ps;;

let proof1, pres1 = Prover.run (TriMerkle_Prover.retrieve_tripath_tritree1 pt t);;
let proof2, pres2 = Prover.run (TriMerkle_Prover.retrieve_tripath_tritree2 pt t);;

Printf.printf "\nPTree1: %d\nPTree2: %d\n" (List.length proof1) (List.length proof2);; *)

(* module TriMerkle_Prover_buf = TriMerkle (Prover_buf);;
module TriMerkle_Verifier_buf = TriMerkle (Verifier_buf);;

 let random_tritree height leaf_len =
  let l = random_leaves (Core.Int.pow 2 height) leaf_len in
  TriMerkle_Prover_buf.from_list l
;;

let t = random_tritree k leaf_size;;
let ht = Prover_buf.get_hash t;;

let proof, pres = Prover_buf.run (TriMerkle_Prover_buf.retrieve_list ps t);;

List.iter (fun res -> print_prover_res proof res; print_newline ()) pres;;

let vres = Verifier_buf.run (TriMerkle_Verifier_buf.retrieve_list ps ht) proof;; 
assert (pres = vres);;

module TriMerkle_Sparse_Prover_buf = TriMerkle_sparse (Prover_buf);;
module TriMerkle_Sparse_Verifier_buf = TriMerkle_sparse (Verifier_buf);;

let leaves = random_leaves num_leafs leaf_size ;;
let paths = random_tripaths num_leafs k ;;
let paths2 = random_tripaths n_retrieve_tripaths k ;;

let n_proof, n_pres = 
  let t = TriMerkle_Prover.init_tritree k in 
  Prover.run (TriMerkle_Prover.update_list paths leaves t) ;;

let s_proof, s_pres = 
  let t = TriMerkle_Sparse_Prover.init_tritree k in
  Prover.run (TriMerkle_Sparse_Prover.update_list paths leaves t) ;;

let n_tritree, s_tritree = Option.get n_pres, Option.get s_pres ;;

Printf.printf "\nNormal Tree Update Proof: %d\nSparse Tree Update Proof: %d\n" (List.length n_proof) (List.length s_proof);;

let n_ht, s_ht = Prover.get_hash n_tritree, Prover.get_hash s_tritree ;;

let n_proof, n_pres = Prover.run (TriMerkle_Prover.retrieve_list paths2 n_tritree) ;;
let s_proof, s_pres = Prover.run (TriMerkle_Sparse_Prover.retrieve_list paths2 s_tritree) ;;

List.combine n_pres s_pres |> List.iter (fun (n_pre, s_pre) -> print_opt_string n_pre; print_opt_string s_pre; Printf.printf "\n");;

Printf.printf "\nNormal Tree Retrieve Proof: %d\nSparse Tree Retrieve Proof: %d\n" (List.length n_proof) (List.length s_proof);;

let n_vres = Verifier.run (TriMerkle_Verifier.retrieve_list paths2 n_ht) n_proof;;
assert (n_pres = n_vres);;
Printf.printf "Normal merkle correct\n"

let s_vres = Verifier.run (TriMerkle_Sparse_Verifier.retrieve_list paths2 s_ht) s_proof;;
assert (s_pres = s_vres);;
Printf.printf "Sparse merkle correct\n"

let n_proof, n_pres = 
  let t = TriMerkle_Prover_buf.init_tritree k in 
  Prover_buf.run (TriMerkle_Prover_buf.update_list paths leaves t) ;;

let s_proof, s_pres = 
  let t = TriMerkle_Sparse_Prover_buf.init_tritree k in
  Prover_buf.run (TriMerkle_Sparse_Prover_buf.update_list paths leaves t) ;;

let n_tritree, s_tritree = Option.get n_pres, Option.get s_pres ;;

Printf.printf "\nNormal Reuse Update Tree Proof: %d\nSparse Reuse Update Tree Proof: %d\n" (List.length n_proof) (List.length s_proof);;

let n_ht, s_ht = Prover_buf.get_hash n_tritree, Prover_buf.get_hash s_tritree ;;

let n_proof, n_pres = Prover_buf.run (TriMerkle_Prover_buf.retrieve_list paths2 n_tritree) ;;
let s_proof, s_pres = Prover_buf.run (TriMerkle_Sparse_Prover_buf.retrieve_list paths2 s_tritree) ;;

List.combine n_pres s_pres |> List.iter (fun (n_pre, s_pre) -> print_opt_string n_pre; print_opt_string s_pre; Printf.printf "\n");;

Printf.printf "\nNormal Reuse Retrieve Tree Proof: %d\nSparse Reuse Retrieve Tree Proof: %d\n" (List.length n_proof) (List.length s_proof);;

let n_vres = Verifier_buf.run (TriMerkle_Verifier_buf.retrieve_list paths2 n_ht) n_proof;;
assert (n_pres = n_vres);;
Printf.printf "Normal Reuse merkle correct\n"

let s_vres = Verifier_buf.run (TriMerkle_Sparse_Verifier_buf.retrieve_list paths2 s_ht) s_proof;;
assert (s_pres = s_vres);;
Printf.printf "Sparse Reuse merkle correct\n" *)