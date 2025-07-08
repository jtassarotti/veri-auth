open Authentikit.Merklesq
open Authentikit.Test_utils
(* open Authentikit.Prover_rev_eqhash *)
(* open Authentikit.Verifier_eqhash *)
open Authentikit.Prover_susp_eqhash
open Authentikit.Verifier_susp_eqhash

module Prover = Prover_susp;;
module Verifier = Verifier_susp;;

module Msq_prover = MerkleSq (Prover);;
module Msq_verifier = MerkleSq (Verifier);;

module IntKey = struct
  type t = int
  
  let equal a b = a = b
  
  let hash a = Hashtbl.hash a
end

module IHash = Hashtbl.Make(IntKey)

(* let print_kv k v =
  Printf.printf "%d, %s\n" k v *)

let key_pos_hash = IHash.create 1048576;;

let leaf_size = 20
let tree_sizes = 
  [10; 16; 25; 78; 169; 243; 485; 1302; 3245; 4096; 12673;
  22391; 55372; 89372; 131072; 237191; 724288; 1048576]
let random_i_percs = [0.1; 0.2; 0.35; 0.5; 0.6; 0.8; 0.99]
let n_repetitions = 10

let take n lst =
  let rec aux i acc = function
    | _ when i = 0 -> List.rev acc
    | [] -> List.rev acc
    | x :: xs -> aux (i - 1) (x :: acc) xs
  in
  aux n [] lst

let random_element lst =
  let idx = Random.int (List.length lst) in
  List.nth lst idx

let exp num_leafs random_i =
  let random_forest_with_proofs key_vals =
    let f = Msq_prover.init_forest () in
    List.fold_left (fun (i, fs) (k, v) ->
      let _, res = Prover.run (Msq_prover.append k v (List.hd fs)) in
      let f, pos = match res with
        | None -> failwith "append failed"
        | Some r -> r
      in
      IHash.add key_pos_hash k pos;
      (i+1, (f::fs))) (0, [f]) key_vals
  in

  let key_vals = random_key_vals num_leafs leaf_size in 
  let _, forests = random_forest_with_proofs key_vals in
  let last_forest = List.hd forests in
  let last_forest_hash = Prover.get_hash last_forest |> Verifier.make_auth in
  let forests = List.rev forests in
  let forests = List.filteri (fun i _ -> i > random_i) forests in
  let first_forest = List.hd forests in
  let first_forest_hash = Prover.get_hash first_forest |> Verifier.make_auth in


  let total_pruned_proof = ref 0 in
  let total_naive_proof = ref 0 in

  for _ = 1 to n_repetitions do
    let k, v = take random_i key_vals |> random_element in
    let n = IHash.find key_pos_hash k in

    (* let ret_proof_length = 
      List.fold_left (fun total_length forest ->
        let ret_proof, res = Prover.run (Msq_prover.retrieve k forest) in
        let _ = match res with
          | None -> assert false
          | Some va -> assert (va = v)
        in
        let forest_hash = Prover.get_hash forest in
        let res = Verifier.run (Msq_verifier.retrieve k forest_hash) ret_proof in
        let _ = match res with
          | None -> assert false
          | Some va -> assert (va = v)
        in
        (String.length ret_proof) + total_length
      ) 0 forests
    in
    total_naive_proof := !total_naive_proof + ret_proof_length; *)

    let pruned_proof, b = Prover.run (Msq_prover.is_extension k v n first_forest last_forest) in
    (* print_endline (String.concat "\n" (Marshal.from_string pruned_proof 0)); print_newline (); *)
    let _ = assert b in
    let _ = Verifier.run (Msq_verifier.is_extension k v n first_forest_hash last_forest_hash) pruned_proof in
    total_pruned_proof := !total_pruned_proof + (String.length pruned_proof);
  done;
  
  (float_of_int !total_pruned_proof) /. (float_of_int n_repetitions), 
  (float_of_int !total_naive_proof) /. (float_of_int n_repetitions);;


List.iter 
  (fun random_i_perc -> 
    List.iter 
    (fun num_leafs ->
      let random_leaf = random_i_perc *. (float_of_int num_leafs) |> Float.trunc |> int_of_float in
      let pruned_size, naive_size = exp num_leafs random_leaf in
      print_string 
        ("Tree size: "^(string_of_int num_leafs)^"; Chosen leaf: "^(string_of_float random_i_perc)
        ^"; Results (eqauth): "^(string_of_float pruned_size)
        ^"; Results (naive): "^(string_of_float naive_size));
        print_newline ();) tree_sizes) random_i_percs



