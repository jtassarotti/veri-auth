open Auth
open Merkle
open Prover_rev
open Verifier
open Prover_marshal
open Verifier_marshal
open Prover_io
open Verifier_io
open Ideal
open Test_utils
open Utils
open Hash

open Path

let data_folder = "../data"
let proof_folder = Printf.sprintf "%s/%s" data_folder (Sys.ocaml_version)

let n_configs = 7
let n_sizes = 16
let treesize_args = list_init n_sizes (fun i -> i + 4)
let n_reps = 10
let config_array = list_init n_reps (fun i -> List.map (fun s -> ((s, i))) treesize_args) |> List.concat

let num_updates = 100000

let read_vals n chn = 
  let rec aux n paths =
    if n = 0 then List.rev paths
    else
      let v = input_line chn in
      aux (n - 1) (v :: paths)
  in
  aux n []

let rec from_int n x = 
  (* Bit string representing a number, from LSB to MSB *)
  let of_bit = function | 0 -> Lp | 1 -> Rp | _ -> assert false in
  match n with
  | 1 -> []
  | _ -> of_bit (x mod 2) :: from_int (n/2) (x/2)

let read_mrk_queries s =
  let chn = Printf.sprintf "%s/mtree_upd1_%d.dat" data_folder s |> open_in_bin in
  let l = read_vals num_updates chn in
  let n = exp 2 s in
  close_in chn;
  List.map (fun s -> 
    match try Some (String.index_from s 0 '_') with Invalid_argument _ -> None with
    | None -> failwith "Error"
    | Some i ->
      let path, s = String.sub s 0 i, String.sub s (i+1) ((String.length s) - (i+1)) in
      from_int n (int_of_string path), s) l

let job_queue = ref []

module DirMerkleProverIo = struct
  type 'a auth = 'a * string
  type tree = Leaf of string | Node of tree auth * tree auth 
  type tree_hash = Leafp of string | Nodep of string * string
  type tree_auth = tree auth

  let output = ref (open_out_bin "/dev/null")

  let set_output s = 
    close_out !output; output := open_out_bin s
  let close_output () = close_out !output; output := open_out_bin "/dev/null"

  let prepare_unauth o = match o with
    | Leaf s -> Leafp s
    | Node ((l, ls), (r, rs)) -> Nodep (ls, rs)
  let ser o = Marshal.to_string (prepare_unauth o) marshal_flags
  let auth o = o, ser o |> hash
  let unauth (t, ts) = Marshal.to_channel !output (prepare_unauth t) marshal_flags; t

  let make_leaf s = auth (Leaf s)
  let make_branch l r = auth (Node (l, r))

  let rec update path v t =
    match path, unauth t with
    | [], Leaf _ -> Some (make_leaf v)
    | Lp::path, Node (l, r) ->
      begin match update path v l with
      | None -> None
      | Some l' -> Some (make_branch l' r)
      end
    | Rp::path, Node (l, r) ->
      begin match update path v r with
      | None -> None
      | Some r' -> Some (make_branch l r')
      end
    | _ -> None
    
  let rec from_list x =
    match x with
    | [] -> failwith "empty"
    | [a] -> make_leaf a
    | l -> 
      let left, right = list_split l in
      make_branch (from_list left) (from_list right)
end

module DirMerkleProverPolyIo = struct
  type 'a auth = 'a * string
  type tree = [`left of string | `right of tree auth * tree auth ]
  type tree_auth = tree auth

  let output = ref (open_out_bin "/dev/null")

  let set_output s = 
    close_out !output; output := open_out_bin s
  let close_output () = close_out !output; output := open_out_bin "/dev/null"

  let prepare_unauth o = match o with
    | `left s -> `left s
    | `right ((l, ls), (r, rs)) -> `right (ls, rs)
  let ser o = Marshal.to_string (prepare_unauth o) marshal_flags
  let auth o = o, ser o |> hash
  let unauth (t, ts) = Marshal.to_channel !output (prepare_unauth t) marshal_flags; t

  let make_leaf s = auth (`left s)
  let make_branch l r = auth (`right (l, r))

  let rec update path v t =
    match path, unauth t with
    | [], `left _ -> Some (make_leaf v)
    | Lp::path, `right (l, r) ->
      begin match update path v l with
      | None -> None
      | Some l' -> Some (make_branch l' r)
      end
    | Rp::path, `right (l, r) ->
      begin match update path v r with
      | None -> None
      | Some r' -> Some (make_branch l r')
      end
    | _ -> None
    
  let rec from_list x =
    match x with
    | [] -> failwith "empty"
    | [a] -> make_leaf a
    | l -> 
      let left, right = list_split l in
      make_branch (from_list left) (from_list right)
end

module DirMerkleProverPolyMarSerIo = struct
  type 'a auth = 'a * string
  type tree = [`left of string | `right of tree auth * tree auth ]
  type tree_auth = tree auth

  let output = ref (open_out_bin "/dev/null")

  let set_output s = 
    close_out !output; output := open_out_bin s
  let close_output () = close_out !output; output := open_out_bin "/dev/null"

  module Authenticatable = struct
    include Authenticatable_marshal.Prover
    let auth =
      let prepare (a, h) = h 
      and serialize y = Marshal.to_string y marshal_flags
      in
      T {prepare; serialize }
      
  end
  open Authenticatable

  let tree_evi : tree evidence = (sum string (pair auth auth))

  let auth o =
    match tree_evi with
    | T evi -> (o, hash (evi.serialize (evi.prepare o)))
  let unauth (t, ts) =
    match tree_evi with
    | T evi -> 
      Marshal.to_channel !output (evi.prepare t) marshal_flags; t

  let make_leaf s = auth (`left s)
  let make_branch l r = auth (`right (l, r))

  let rec update path v t =
    match path, unauth t with
    | [], `left _ -> Some (make_leaf v)
    | Lp::path, `right (l, r) ->
      begin match update path v l with
      | None -> None
      | Some l' -> Some (make_branch l' r)
      end
    | Rp::path, `right (l, r) ->
      begin match update path v r with
      | None -> None
      | Some r' -> Some (make_branch l r')
      end
    | _ -> None
    
  let rec from_list x =
    match x with
    | [] -> failwith "empty"
    | [a] -> make_leaf a
    | l -> 
      let left, right = list_split l in
      make_branch (from_list left) (from_list right)
end

module DirMerkleVerifierIo = struct
  type 'a auth = string
  type tree = Leaf of string | Node of tree auth * tree auth 
  type tree_hash = Leafp of string | Nodep of string * string
  type tree_auth = tree auth

  let input = ref (open_in_bin "/dev/null")

  let set_input s = 
    close_in !input; input := open_in_bin s
  let close_input () = close_in !input; input := open_in_bin "/dev/null"

  let ser o = 
    Marshal.to_string o marshal_flags
  let deser s = 
    match Marshal.from_string s 0 with
    | Leafp s -> Leaf s
    | Nodep (ls, rs) -> Node (ls, rs)
  let auth o = ser o |> hash
  let unauth h =
    let p = from_channel_with_string !input in
    if hash p = h then deser p
    else failwith "Proof failure"

  let make_leaf s = auth (Leaf s)
  let make_branch l r = auth (Node (l, r))

  let rec update path v t =
    match path, unauth t with
    | [], Leaf _ -> Some (make_leaf v)
    | Lp::path, Node (l, r) ->
      begin match update path v l with
      | None -> None
      | Some l' -> Some (make_branch l' r)
      end
    | Rp::path, Node (l, r) ->
      begin match update path v r with
      | None -> None
      | Some r' -> Some (make_branch l r')
      end
    | _ -> None
end

module DirMerkleVerifierPolyIo = struct
  type 'a auth = string
  type tree = [`left of string | `right of tree auth * tree auth ]
  type tree_auth = tree auth

  let input = ref (open_in_bin "/dev/null")

  let set_input s = 
    close_in !input; input := open_in_bin s
  let close_input () = close_in !input; input := open_in_bin "/dev/null"

  let ser o = Marshal.to_string o marshal_flags
  let deser s = Marshal.from_string s 0
  let auth o = ser o |> hash
  let unauth h =
    let p = from_channel_with_string !input in
    if hash p = h then deser p
    else failwith "Proof failure"

  let make_leaf s = auth (`left s)
  let make_branch l r = auth (`right (l, r))

  let rec update path v t =
    match path, unauth t with
    | [], `left _ -> Some (make_leaf v)
    | Lp::path, `right (l, r) ->
      begin match update path v l with
      | None -> None
      | Some l' -> Some (make_branch l' r)
      end
    | Rp::path, `right (l, r) ->
      begin match update path v r with
      | None -> None
      | Some r' -> Some (make_branch l r')
      end
    | _ -> None
end

module DirMerkleVerifierPolyMarSerIo = struct
  type 'a auth = string
  type tree = [`left of string | `right of tree auth * tree auth ]
  type tree_auth = tree auth

  let input = ref (open_in_bin "/dev/null")

  let set_input s = 
    close_in !input; input := open_in_bin s
  let close_input () = close_in !input; input := open_in_bin "/dev/null"

  module Authenticatable = struct
    include Authenticatable_marshal.Verifier
    let auth =
      let serialize x = Marshal.to_string x marshal_flags in
      let deserialize s = Some (Marshal.from_string s 0) in
      { serialize; deserialize }

  end
  open Authenticatable
     
  let tree_evi : tree evidence = (sum string (pair auth auth))

  let ser o = tree_evi.serialize o
  let deser s = match tree_evi.deserialize s with Some s -> s | None -> raise (Invalid_argument "deser")
  let auth o = ser o |> hash
  let unauth h =
    let p = from_channel_with_string !input in
    if hash p = h then deser p
    else failwith "Proof failure"

  let make_leaf s = auth (`left s)
  let make_branch l r = auth (`right (l, r))

  let rec update path v t =
    match path, unauth t with
    | [], `left _ -> Some (make_leaf v)
    | Lp::path, `right (l, r) ->
      begin match update path v l with
      | None -> None
      | Some l' -> Some (make_branch l' r)
      end
    | Rp::path, `right (l, r) ->
      begin match update path v r with
      | None -> None
      | Some r' -> Some (make_branch l r')
      end
    | _ -> None
end

let dir_io_hash = Hashtbl.create 18
let read_dir_prover_io_tree s =
  let n = exp 2 s in
  let chn = Printf.sprintf "%s/mtree1_%d.dat" data_folder s |> open_in_bin in
  let l = read_vals n chn in
  close_in chn;
  DirMerkleProverIo.from_list l

let dir_poly_io_hash = Hashtbl.create 18  
let read_dir_prover_poly_io_tree s =
  let n = exp 2 s in
  let chn = Printf.sprintf "%s/mtree1_%d.dat" data_folder s |> open_in_bin in
  let l = read_vals n chn in
  close_in chn;
  DirMerkleProverPolyIo.from_list l

let dir_poly_mar_ser_io_hash = Hashtbl.create 18
let read_dir_prover_poly_mar_ser_io_tree s =
  let n = exp 2 s in
  let chn = Printf.sprintf "%s/mtree1_%d.dat" data_folder s |> open_in_bin in
  let l = read_vals n chn in
  close_in chn;
  DirMerkleProverPolyMarSerIo.from_list l

let auth_io_hash = Hashtbl.create 18
let read_io_tree s =
  let n = exp 2 s in
  let chn = Printf.sprintf "%s/mtree1_%d.dat" data_folder s |> open_in_bin in
  let l = read_vals n chn in
  close_in chn;
  Merkle_Prover_io.from_list l

let dirprover_merkle_io_updates file t paths =
  DirMerkleProverIo.set_output file;
  let rec aux paths =
    match paths with
    | [] -> DirMerkleProverIo.close_output ()
    | (path, leaf)::paths ->
      DirMerkleProverIo.update path leaf t;
      aux paths
  in
  aux paths

let dirprover_merkle_poly_io_updates file t paths =
  DirMerkleProverPolyIo.set_output file;
  let rec aux paths =
    match paths with
    | [] -> DirMerkleProverPolyIo.close_output ()
    | (path, leaf)::paths ->
      DirMerkleProverPolyIo.update path leaf t;
      aux paths
  in
  aux paths

let dirprover_merkle_poly_mar_ser_io_updates file t paths =
  DirMerkleProverPolyMarSerIo.set_output file;
  let rec aux paths =
    match paths with
    | [] -> DirMerkleProverPolyMarSerIo.close_output ()
    | (path, leaf)::paths ->
      DirMerkleProverPolyMarSerIo.update path leaf t;
      aux paths
  in
  aux paths

let prover_io_merkle_updates file t paths =
  Prover_io.set_output file;
  let rec aux paths =
    match paths with
    | [] -> Prover_io.close_output ()
    | (path, leaf)::paths ->
      let _ = Prover_io.run (Merkle_Prover_io.update path leaf t) in
      aux paths
  in
  aux paths

let dirverifier_merkle_io_updates file ht paths =
  DirMerkleVerifierIo.set_input file;
  let rec aux paths =
    match paths with
    | [] -> DirMerkleVerifierIo.close_input ()
    | (path, leaf)::paths ->
      let _ = DirMerkleVerifierIo.update path leaf ht in
      aux paths
  in
  aux paths

let dirverifier_merkle_poly_io_updates file ht paths =
  DirMerkleVerifierPolyIo.set_input file;
  let rec aux paths =
    match paths with
    | [] -> DirMerkleVerifierPolyIo.close_input ()
    | (path, leaf)::paths ->
      let _ = DirMerkleVerifierPolyIo.update path leaf ht in
      aux paths
  in
  aux paths

let dirverifier_merkle_poly_mar_ser_io_updates file ht paths =
  DirMerkleVerifierPolyMarSerIo.set_input file;
  let rec aux paths =
    match paths with
    | [] -> DirMerkleVerifierPolyMarSerIo.close_input ()
    | (path, leaf)::paths ->
      let _ = DirMerkleVerifierPolyMarSerIo.update path leaf ht in
      aux paths
  in
  aux paths

let verifier_io_merkle_updates file t paths =
  Verifier_io.set_input file;
  let rec aux paths =
    match paths with
    | [] -> Verifier_io.close_input ()
    | (path, leaf)::paths ->
      let _ = Verifier_io.run (Merkle_Verifier_io.update path leaf t) in
      aux paths
  in
  aux paths;;

(* job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i),
  fun () ->
    Printf.printf "%d %d dirprover_hash_merkle_magic_updates" i s;
    let t = read_dir_prover_hash_magic_tree s in
    let paths = read_mrk_queries s in
    gc_collect ();
    measure_call ("dirprover_hash_merkle_magic_updates "^(string_of_int s)) (dirprover_hash_merkle_magic_updates t) paths)
config_array;

job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i),
  fun () ->
    Printf.printf "%d %d dirprover_hash_merkle_updates" i s;
    let t = read_dir_prover_hash_tree s in
    let paths = read_mrk_queries s in
    gc_collect ();
    measure_call ("dirprover_hash_merkle_updates "^(string_of_int s)) (dirprover_hash_merkle_updates t) paths)
config_array;

job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i),
  fun () ->
    Printf.printf "%d %d dirprover_merkle_updates" i s;
    let t = read_dir_prover_tree s in
    let paths = read_mrk_queries s in
    gc_collect ();
    measure_call ("dirprover_merkle_updates "^(string_of_int s)) (dirprover_merkle_updates t) paths)
config_array; *)

job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i),
  fun () ->
    Printf.printf "%d %d dirprover_merkle_io_updates" i s;
    let t = read_dir_prover_io_tree s in
    Hashtbl.add dir_io_hash s (snd t);
    let paths = read_mrk_queries s in
    gc_collect ();
    let file = Printf.sprintf "%s/proof_mtree_upd_d_%03d.dat" proof_folder s in
    measure_call ("dirprover_merkle_io_updates "^(string_of_int s)) (dirprover_merkle_io_updates file t) paths)
config_array;

job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i),
  fun () ->
    Printf.printf "%d %d dirprover_merkle_poly_io_updates" i s;
    let t = read_dir_prover_poly_io_tree s in
    Hashtbl.add dir_poly_io_hash s (snd t);
    let paths = read_mrk_queries s in
    gc_collect ();
    let file = Printf.sprintf "%s/proof_mtree_upd_dp_%03d.dat" proof_folder s in
    measure_call ("dirprover_merkle_poly_io_updates "^(string_of_int s)) (dirprover_merkle_poly_io_updates file t) paths)
config_array;

job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i),
  fun () ->
    Printf.printf "%d %d dirprover_merkle_poly_mar_ser_io_updates" i s;
    let t = read_dir_prover_poly_mar_ser_io_tree s in
    Hashtbl.add dir_poly_mar_ser_io_hash s (snd t);
    let paths = read_mrk_queries s in
    gc_collect ();
    let file = Printf.sprintf "%s/proof_mtree_upd_dpm_%03d.dat" proof_folder s in
    measure_call ("dirprover_merkle_poly_mar_ser_io_updates "^(string_of_int s)) (dirprover_merkle_poly_mar_ser_io_updates file t) paths)
config_array;

job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i),
  fun () ->
    Printf.printf "%d %d prover_io_merkle_updates" i s;
    let t = read_io_tree s in
    Hashtbl.add auth_io_hash s (Prover_io.get_hash t);
    let paths = read_mrk_queries s in
    gc_collect ();
    let file = Printf.sprintf "%s/proof_mtree_upd_dpma_%03d.dat" proof_folder s in
    measure_call ("prover_io_merkle_updates "^(string_of_int s)) (prover_io_merkle_updates file t) paths)
config_array;

(* job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i),
  fun () ->
    Printf.printf "%d %d prover_io_merkle_magic_updates" i s;
    let t = read_io_tree s in
    Hashtbl.add auth_io_hash s (Prover_io.get_hash t);
    let paths = read_mrk_queries s in
    gc_collect ();
    let file = Printf.sprintf "%s/proof_mtree_upd_dpmam_%03d.dat" proof_folder s in
    measure_call ("prover_io_merkle_magic_updates "^(string_of_int s)) (prover_io_merkle_magic_updates file t) paths)
config_array; *)

(* job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i) + (2*n_configs),
  fun () ->
    Printf.printf "%d %d dirverifier_hash_merkle_magic_updates" i s;
    let t = read_dir_prover_hash_magic_tree s in
    let ht = snd t in
    let paths = read_mrk_queries s in
    let proofs = dirprover_hash_merkle_magic_updates_keep t paths in
    gc_collect ();
    measure_call ("dirverifier_hash_merkle_magic_updates "^(string_of_int s)) (dirverifier_hash_merkle_magic_updates ht paths) proofs)
config_array;

job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i) + (2*n_configs),
  fun () ->
    Printf.printf "%d %d dirverifier_hash_merkle_updates" i s;
    let t = read_dir_prover_hash_tree s in
    let ht = snd t in
    let paths = read_mrk_queries s in
    let proofs = dirprover_hash_merkle_updates_keep t paths in
    gc_collect ();
    measure_call ("dirverifier_hash_merkle_updates "^(string_of_int s)) (dirverifier_hash_merkle_updates ht paths) proofs)
config_array; *)

(* job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i) + (2*n_configs),
  fun () ->
    Printf.printf "%d %d dirverifier_merkle_updates" i s;
    let t = read_dir_prover_tree s in
    let ht = snd t in
    let paths = read_mrk_queries s in
    let proofs = dirprover_merkle_updates_keep t paths in
    gc_collect ();
    measure_call ("dirverifier_merkle_updates "^(string_of_int s)) (dirverifier_merkle_updates ht paths) proofs)
config_array; *)

job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i) + (2*n_configs),
  fun () ->
    Printf.printf "%d %d dirverifier_merkle_io_updates" i s;
    let paths = read_mrk_queries s in
    let file = Printf.sprintf "%s/proof_mtree_upd_d_%03d.dat" proof_folder s in
    let ht = Hashtbl.find dir_io_hash s in
    gc_collect ();
    measure_call ("dirverifier_merkle_io_updates "^(string_of_int s)) (dirverifier_merkle_io_updates file ht) paths)
config_array;

job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i) + (2*n_configs),
  fun () ->
    Printf.printf "%d %d dirverifier_merkle_poly_io_updates" i s;
    let paths = read_mrk_queries s in
    let file = Printf.sprintf "%s/proof_mtree_upd_dp_%03d.dat" proof_folder s in
    let ht = Hashtbl.find dir_poly_io_hash s in
    gc_collect ();
    measure_call ("dirverifier_merkle_poly_io_updates "^(string_of_int s)) (dirverifier_merkle_poly_io_updates file ht) paths)
config_array;

job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i) + (2*n_configs),
  fun () ->
    Printf.printf "%d %d dirverifier_merkle_poly_mar_ser_io_updates" i s;
    let paths = read_mrk_queries s in
    let file = Printf.sprintf "%s/proof_mtree_upd_dpm_%03d.dat" proof_folder s in
    let ht = Hashtbl.find dir_poly_mar_ser_io_hash s in
    gc_collect ();
    measure_call ("dirverifier_merkle_poly_mar_ser_io_updates "^(string_of_int s)) (dirverifier_merkle_poly_mar_ser_io_updates file ht) paths)
config_array;

job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i) + (2*n_configs),
  fun () ->
    Printf.printf "%d %d verifier_io_merkle_updates" i s;
    let paths = read_mrk_queries s in
    let file = Printf.sprintf "%s/proof_mtree_upd_dpma_%03d.dat" proof_folder s in
    let ht = Hashtbl.find auth_io_hash s in
    gc_collect ();
    measure_call ("verifier_io_merkle_updates "^(string_of_int s)) (verifier_io_merkle_updates file ht) paths)
config_array;

(* job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i) + (2*n_configs),
  fun () ->
    Printf.printf "%d %d verifier_io_merkle_magic_updates" i s;
    let paths = read_mrk_queries s in
    let file = Printf.sprintf "%s/proof_mtree_upd_dpmam_%03d.dat" proof_folder s in
    let ht = Hashtbl.find auth_io_hash s in
    gc_collect ();
    measure_call ("verifier_io_merkle_magic_updates "^(string_of_int s)) (verifier_io_merkle_magic_updates file ht) paths)
config_array; *)

job_queue := List.sort (fun (i1, _) (i2, _) -> compare i1 i2) !job_queue;

let rec run_jobs = function
  | [] -> ()
  | (_, job)::rest ->
    job ();
    print_endline "";
    gc_collect ();
    run_jobs rest
in

run_jobs !job_queue;
print_measures ();
