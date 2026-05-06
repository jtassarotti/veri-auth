open Authentikit
open Auth
open Optiks
open Test_utils
open Prover_rev_eqauth
open Verifier_eqauth
open Prover_susp_eqauth
open Verifier_susp_eqauth
open Utils

module StrKey = struct
  type t = string
  
  let equal a b = String.compare a b = 0
  
  let hash a = Hashtbl.hash a
end

module IntKey = struct
  type t = int
  
  let equal a b = a = b
  let hash a = Hashtbl.hash a
end

module SHash = Hashtbl.Make(StrKey);;
module IHash = Hashtbl.Make(IntKey);;

let pr_key, pb_key = Vrf.get_keys () in
Prover_rev.init pr_key; Verifier.init pb_key;
Prover_susp.init pr_key; Verifier_susp.init pb_key;
  
module Otks_prover = Optiks (Prover_rev);;
module Otks_verifier = Optiks (Verifier);;
module Otks_prover_susp = Optiks (Prover_susp);;
module Otks_verifier_susp = Optiks (Verifier_susp);;

let key_vals_hash = SHash.create 1048576 in

let leaf_size = 20 in
let tree_sizes = 
  [10; 16; 25; 78; 169; 243; 485; 1302; 3245; 4096; 12673;
  22391; 55372; 89372; 131072; 237191; 724288; 1048576]
in
let random_i_percs = [0.1; 0.2; 0.35; 0.5; 0.6; 0.8; 0.99] in
let n_repetitions = 5 in

let take n lst =
  let rec aux i acc = function
    | _ when i = 0 -> List.rev acc
    | [] -> List.rev acc
    | x :: xs -> aux (i - 1) (x :: acc) xs
  in
  aux n [] lst
in

let random_element_lst lst =
  let idx = Random.int (List.length lst) in
  List.nth lst idx
in

let random_element_arr arr =
  let idx = Random.int (Array.length arr) in
  arr.(idx)
in

let exp n random_i key_vals =
  let append_key_vals key_vals =
    let state = Otks_prover.init_state () in
    List.fold_left (fun (i, state) (k, v) ->
      if not (SHash.mem key_vals_hash k) then
        SHash.add key_vals_hash k [v]
      else
        SHash.replace key_vals_hash k (v :: SHash.find key_vals_hash k);
      (* print_endline (string_of_int i); *)
      (* print_string k; print_string " "; *)
      (* print_endline v; *)
      let _, state = Prover_rev.run (Otks_prover.append k v state) in
      (* print_endline (Prover_rev.get_hash state); *)
      let proof, res = Prover_rev.run (Otks_prover.retrieve k state) in
      (* let _ = print_endline (String.concat "\n" (Marshal.from_string proof 0)); print_newline () in *)
      match res with
      | None -> failwith "retrieve after append failed"
      | Some v1 -> ((* print_endline v1 ;*) assert (v = v1));
      (i+1, state)) (0, state) key_vals
  in

  let _, state = append_key_vals key_vals in
  (* print_endline (Prover_rev.get_hash state); *)
  let state_hash = Verifier.make_auth (Prover_rev.get_hash state) in
  let key_vals_arr = SHash.to_seq key_vals_hash |> Array.of_seq in

  let total_retrieve_proof = ref 0 in
  let total_history_proof = ref 0 in

  for _ = 1 to n_repetitions do
    let k, vals = random_element_arr key_vals_arr in
    (* print_endline k; *)

    let proof, value = Prover_rev.run (Otks_prover.retrieve k state) in
    (* let _ = print_endline (String.concat "\n" (Marshal.from_string proof 0)); print_newline () in *)
    let _ = match value with
      | None -> failwith "Value not found"
      | Some value -> assert (String.equal value (List.hd vals))
    in
    let _ = Verifier.run (Otks_verifier.retrieve k state_hash) proof in
    total_retrieve_proof := !total_retrieve_proof + (String.length proof);

    let proof, values = Prover_rev.run (Otks_prover.history k state) in
    let _ = match values with
      | [] -> failwith "No values found"
      | vals -> assert (List.equal String.equal vals values)
    in
    let _ = Verifier.run (Otks_verifier.history k state_hash) proof in
    total_history_proof := !total_history_proof + (String.length proof);
  done;
  
  (float_of_int !total_retrieve_proof) /. (float_of_int n_repetitions), 
  (float_of_int !total_history_proof) /. (float_of_int n_repetitions)
in

let exp_susp n random_i key_vals =
  let random_state_with_proofs key_vals =
    let state = Otks_prover_susp.init_state () in
    List.fold_left (fun (i, state) (k, v) ->
      if not (SHash.mem key_vals_hash k) then
        SHash.add key_vals_hash k [v]
      else
        SHash.replace key_vals_hash k (v :: SHash.find key_vals_hash k);
      (* print_endline (string_of_int i); *)
      let _, state = Prover_susp.run (Otks_prover_susp.append k v state) in
      let _, res = Prover_susp.run (Otks_prover_susp.retrieve k state) in
      match res with
      | None -> failwith "retrieve after append failed"
      | Some v1 -> assert (v = v1);
      (i+1, state)) (0, state) key_vals
  in

  let _, state = random_state_with_proofs key_vals in
  let state_hash = Verifier_susp.make_auth (Prover_susp.get_hash state) in
  let key_vals_arr = SHash.to_seq key_vals_hash |> Array.of_seq in

  let total_retrieve_proof = ref 0 in
  let total_history_proof = ref 0 in

  for _ = 1 to n_repetitions do
    let k, vals = random_element_arr key_vals_arr in

    let proof, value = Prover_susp.run (Otks_prover_susp.retrieve k state) in
    (* let _ = print_endline (String.concat "\n" (Marshal.from_string proof 0)); print_newline () in *)
    let _ = match value with
      | None -> failwith "Value not found"
      | Some value -> assert (String.equal value (List.hd vals))
    in
    let _ = Verifier_susp.run (Otks_verifier_susp.retrieve k state_hash) proof in
    total_retrieve_proof := !total_retrieve_proof + (String.length proof);

    let proof, value = Prover_susp.run (Otks_prover_susp.history k state) in
    let _ = match value with
      | [] -> failwith "Value not found"
      | vals -> assert (List.equal String.equal vals value)
    in
    let _ = Verifier_susp.run (Otks_verifier_susp.history k state_hash) proof in
    total_history_proof := !total_history_proof + (String.length proof);
  done;
  
  (float_of_int !total_retrieve_proof) /. (float_of_int n_repetitions), 
  (float_of_int !total_history_proof) /. (float_of_int n_repetitions)
in
let tree_size = 200 in

let key_vals = random_key_vals_rep tree_size leaf_size in 
List.iter 
  (fun random_i_perc -> 
    let random_leaf = random_i_perc *. (float_of_int tree_size) |> Float.trunc |> int_of_float in
    let retrieve_size, history_size = exp tree_size random_leaf key_vals in
    print_endline "rev done";
    let retrieve_size_susp, history_size_susp = exp_susp tree_size random_leaf key_vals in
    print_endline "susp done";
    print_string 
      ("Tree size: "^(string_of_int tree_size)^"; Chosen leaf: "^(string_of_float random_i_perc)
      ^"; Results (retrieve): "^(string_of_float retrieve_size)
      ^"; Results (retrieve susp): "^(string_of_float retrieve_size_susp)
      ^"; Results (history): "^(string_of_float history_size)
      ^"; Results (history susp): "^(string_of_float history_size_susp););
    print_newline (); 
    ()) random_i_percs

