open Auth
open Merkle
open Merkle_sparse
open Prover
open Verifier
open Prover_buf
open Verifier_buf
open Ideal
open Test_utils

module Merkle_Prover = Merkle (Prover);;
module Merkle_Verifier = Merkle (Verifier);;
module Merkle_Ideal = Merkle (Ideal);;

module Merkle_Sparse_Prover = Merkle_sparse (Prover);;
module Merkle_Sparse_Verifier = Merkle_sparse (Verifier);;
module Merkle_Sparse_Ideal = Merkle_sparse (Ideal);;

let k = 16;;
let leaf_size = 20;;
let num_leafs = 50;;

let t = Merkle_Sparse_Prover.init_tree k ;;
let ht = Prover.get_hash t;;

let leaves = random_leaves num_leafs leaf_size;;
let paths = List.init num_leafs (fun _ -> random_path k);;

let proof, pres = Prover.run (Merkle_Sparse_Prover.update_list paths leaves t);;
let t_new = Option.get pres ;;
let ht_new = Prover.get_hash t_new ;;
let vres = Verifier.run (Merkle_Sparse_Verifier.update_list paths leaves ht) proof 
           |> Option.get;;

assert (ht_new = vres);;
Printf.printf "Update correct\n"

let paths = List.init num_leafs (fun _ -> random_path k);;

let proof, pres = Prover.run (Merkle_Sparse_Prover.retrieve_list paths t_new);;

let vres = Verifier.run (Merkle_Sparse_Verifier.retrieve_list paths ht_new) proof;; 
assert (pres = vres);;
Printf.printf "Retrieve correct\n"
