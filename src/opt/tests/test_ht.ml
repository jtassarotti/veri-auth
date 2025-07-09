open Authentikit
open History
open Test_utils
open Prover_rev_eqhash
open Verifier_eqhash
open Prover_susp_eqhash
open Verifier_susp_eqhash
open Utils

module Prover = Prover_rev;;
module Verifier = Verifier;;

let pr_key, pb_key = Vrf.get_keys () in
Prover.init pr_key; Verifier.init pb_key;

module History_Prover = History (Prover);;
module History_Verifier = History (Verifier);;

let leaf_size = 20
let tree_sizes = 
  [8; 16; 32; 64; 128; 256; 512; 1024; 2048; 4096; 8192;
  16384; 32768; 65536; 131072; 262144; 524288; 1048576]
let random_i_percs = [0.1; 0.2; 0.35; 0.5; 0.6; 0.8; 0.99]

let exp num_leafs random_i =
  let random_cmtree_with_proofs leaves =
    let t = History_Prover.init_tree () in
    List.fold_left (fun (_, ts) leaf -> 
      let _, (t, i) = Prover.run (History_Prover.append leaf (List.hd ts)) in
      (i+1, (t::ts))) (0, [t]) leaves
  in

  let leaves = random_leaves num_leafs leaf_size in 
  let _, ts = random_cmtree_with_proofs leaves in
  let last_t = List.hd ts in
  let last_ht = Prover.get_hash last_t |> Verifier.make_auth in
  let ts = List.rev ts in
  let ts = List.filteri (fun i _ -> i > random_i) ts in
  let first_t = List.hd ts in
  let first_ht = Prover.get_hash first_t |> Verifier.make_auth in
  (* let hts = List.map (fun t -> Prover.get_hash t) ts in *)

  (* let ret_proofs = 
    List.mapi 
      (fun i t -> Prover.run (History_Prover.retrieve random_i t) (i+random_i) |> fst) ts in
  (* let _ = List.iter (fun s -> print_string s; print_newline ()) ret_proofs in *)
  let proof_lengths = List.fold_left (fun acc s -> acc + String.length s) 0 ret_proofs in
  let _ = print_string ("Generated proofs, length: "^(string_of_int proof_lengths)); print_newline () in
  let _ = 
    List.iteri 
      (fun i (pf, ht) -> Verifier.run (History_Verifier.retrieve random_i ht) pf i; ()) 
      (List.combine ret_proofs hts) in
  let _ = print_string "Verified proofs"; print_newline () in *)

  let pruned_proof, b = Prover.run (History_Prover.is_extension last_t first_t) in
  (* let _, s = Prover.run (History_Prover.inorder first_t) 100 in
  print_string s; print_newline ();
  let _, s = Prover.run (History_Prover.inorder last_t) 100 in
  print_string s; print_newline (); *)
  (* let _ = print_string ("Generated pruned proof, length: "^(string_of_int (String.length pruned_proof))); print_newline () in *)
  let _ = assert b in
  let _ = Verifier.run (History_Verifier.is_extension last_ht first_ht) pruned_proof in
  (* let _ = print_string "Verified pruned proof"; print_newline () in *)

  let naive_pruned_proof, b = Prover.run (History_Prover.is_extension_naive last_t first_t) in
  (* let _ = print_string ("Generated naive pruned proof, length: "^(string_of_int (String.length naive_pruned_proof))); print_newline () in *)
  let _ = assert b in
  let _ = Verifier.run (History_Verifier.is_extension_naive last_ht first_ht) naive_pruned_proof in
  (* print_string "Verified pruned proof"; print_newline () *)
  String.length pruned_proof, String.length naive_pruned_proof;;


List.iter 
  (fun random_i_perc -> 
    let random_leaf = int_of_float (random_i_perc *. (float_of_int 150)) in
    let pruned_size, naive_size = exp 150 random_leaf in
    print_string 
      ("Tree size: "^(string_of_int 150)^"; Chosen leaf: "^(string_of_float random_i_perc)
      ^"; Results (eqauth): "^(string_of_int pruned_size)
      ^"; Results (naive): "^(string_of_int naive_size));
    print_newline ();
    ()) random_i_percs



