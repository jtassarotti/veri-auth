open Authentikit
open Auth
open Merklesq
open Test_utils
open Prover_rev_eqhash
open Verifier_eqhash
open Prover_susp_eqhash
open Verifier_susp_eqhash
open Utils

module StrKey = struct
  type t = string
  
  let equal a b = String.compare a b = 0
  
  let hash a = Hashtbl.hash a
end

module SHash = Hashtbl.Make(StrKey);;

let pr_key, pb_key = Vrf.get_keys () in
Prover_rev.init pr_key; Verifier.init pb_key;
Prover_susp.init pr_key; Verifier_susp.init pb_key;
  
module Msq_prover = MerkleSq (Prover_rev);;
module Msq_verifier = MerkleSq (Verifier);;
module Msq_prover_susp = MerkleSq (Prover_susp);;
module Msq_verifier_susp = MerkleSq (Verifier_susp);;

let key_pos_hash = SHash.create 1048576 in

let leaf_size = 20 in
let tree_sizes = 
  [10; 16; 25; 78; 169; 243; 485; 1302; 3245; 4096; 12673;
  22391; 55372; 89372; 131072; 237191; 724288; 1048576]
in
let random_i_percs = [0.1; 0.2; 0.35; 0.5; 0.6; 0.8; 0.99] in
let n_repetitions = 1 in

let take n lst =
  let rec aux i acc = function
    | _ when i = 0 -> List.rev acc
    | [] -> List.rev acc
    | x :: xs -> aux (i - 1) (x :: acc) xs
  in
  aux n [] lst
in

let random_element lst =
  let idx = Random.int (List.length lst) in
  List.nth lst idx
in


let exp n random_i key_vals =
  let random_forest_with_proofs key_vals =
    let f = Msq_prover.init_forest () in
    List.fold_left (fun (i, fs) (k, v) ->
      let _, res = Prover_rev.run (Msq_prover.append k v (List.hd fs)) in
      let f, pos = match res with
        | None -> failwith "append failed"
        | Some r -> r
      in
      SHash.add key_pos_hash k pos;
      (i+1, (f::fs))) (0, [f]) key_vals
  in

  let _, forests = random_forest_with_proofs key_vals in
  let last_forest = List.hd forests in
  let last_forest_hash = Prover_rev.get_hash last_forest |> Verifier.make_auth in
  let forests = List.rev forests in
  let forests = List.filteri (fun i _ -> i > random_i) forests in
  let first_forest = List.hd forests in
  let first_forest_hash = Prover_rev.get_hash first_forest |> Verifier.make_auth in


  let total_pruned_proof = ref 0 in
  let total_naive_proof = ref 0 in

  for _ = 1 to n_repetitions do
    let k, v = take random_i key_vals |> random_element in
    let n = SHash.find key_pos_hash k in

    (* let ret_proof_length = 
      List.fold_left (fun total_length forest ->
        let ret_proof, key, res = Prover_rev.run (Msq_prover.retrieve k forest) in
        let _ = match res with
          | None -> assert false
          | Some va -> assert (va = v)
        in
        let forest_hash = Prover_rev.get_hash forest in
        let res = Verifier.run (Msq_verifier.retrieve k forest_hash) ret_proof key in
        let _ = match res with
          | None -> assert false
          | Some va -> assert (va = v)
        in
        (String.length ret_proof) + total_length
      ) 0 forests
    in
    total_naive_proof := !total_naive_proof + ret_proof_length; *)

    let pruned_proof, b = Prover_rev.run (Msq_prover.is_extension k v n first_forest last_forest) in
    (* print_endline (String.concat "\n" (Marshal.from_string pruned_proof 0)); print_newline (); *)
    let _ = assert b in
    let _ = Verifier.run (Msq_verifier.is_extension k v n first_forest_hash last_forest_hash) pruned_proof in
    total_pruned_proof := !total_pruned_proof + (String.length pruned_proof);
  done;
  
  (float_of_int !total_pruned_proof) /. (float_of_int n_repetitions), 
  (float_of_int !total_naive_proof) /. (float_of_int n_repetitions)
in

let exp_susp n random_i key_vals =
  let random_forest_with_proofs key_vals =
    let f = Msq_prover_susp.init_forest () in
    List.fold_left (fun (i, fs) (k, v) ->
      let _, res = Prover_susp.run (Msq_prover_susp.append k v (List.hd fs)) in
      let f, pos = match res with
        | None -> failwith "append failed"
        | Some r -> r
      in
      SHash.add key_pos_hash k pos;
      (i+1, (f::fs))) (0, [f]) key_vals
  in

  let _, forests = random_forest_with_proofs key_vals in
  let last_forest = List.hd forests in
  let last_forest_hash = Prover_susp.get_hash last_forest |> Verifier_susp.make_auth in
  let forests = List.rev forests in
  let forests = List.filteri (fun i _ -> i > random_i) forests in
  let first_forest = List.hd forests in
  let first_forest_hash = Prover_susp.get_hash first_forest |> Verifier_susp.make_auth in


  let total_pruned_proof = ref 0 in
  let total_naive_proof = ref 0 in

  for _ = 1 to n_repetitions do
    let k, v = take random_i key_vals |> random_element in
    let n = SHash.find key_pos_hash k in

    (* let ret_proof_length = 
      List.fold_left (fun total_length forest ->
        let ret_proof, res = Prover_susp.run (Msq_prover_susp.retrieve k forest) in
        let _ = match res with
          | None -> assert false
          | Some va -> assert (va = v)
        in
        let forest_hash = Prover_susp.get_hash forest in
        let res = Verifier_susp.run (Msq_verifier_susp.retrieve k forest_hash) ret_proof in
        let _ = match res with
          | None -> assert false
          | Some va -> assert (va = v)
        in
        (String.length ret_proof) + total_length
      ) 0 forests
    in
    total_naive_proof := !total_naive_proof + ret_proof_length; *)

    let pruned_proof, b = Prover_susp.run (Msq_prover_susp.is_extension k v n first_forest last_forest) in
    (* print_endline (String.concat "\n" (Marshal.from_string pruned_proof 0)); print_newline (); *)
    let _ = assert b in
    let _ = Verifier_susp.run (Msq_verifier_susp.is_extension k v n first_forest_hash last_forest_hash) pruned_proof in
    total_pruned_proof := !total_pruned_proof + (String.length pruned_proof);
  done;
  
  (float_of_int !total_pruned_proof) /. (float_of_int n_repetitions), 
  (float_of_int !total_naive_proof) /. (float_of_int n_repetitions)
in
let tree_size = 200 in

let key_vals = random_key_vals tree_size leaf_size in 
List.iter 
  (fun random_i_perc -> 
    let random_leaf = random_i_perc *. (float_of_int tree_size) |> Float.trunc |> int_of_float in
    let pruned_size, _ = exp tree_size random_leaf key_vals in
    print_endline "rev done";
    let pruned_size_susp, _ = exp_susp tree_size random_leaf key_vals in
    print_endline "susp done";
    print_string 
      ("Tree size: "^(string_of_int tree_size)^"; Chosen leaf: "^(string_of_float random_i_perc)
      ^"; Results (eqauth): "^(string_of_float pruned_size)
      ^"; Results (eqauth_susp): "^(string_of_float pruned_size_susp));
    print_newline (); 
    ()) random_i_percs

