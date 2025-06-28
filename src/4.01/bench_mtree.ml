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

let num_retrieves = 100000

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
  let chn = Printf.sprintf "%s/mtree_look1_%d.dat" data_folder s |> open_in_bin in
  let l = read_vals num_retrieves chn in
  let n = exp 2 s in
  close_in chn;
  List.map (fun i -> from_int n (int_of_string i)) l

let job_queue = ref []

module DirMerkleProverDirHashMagic = struct
  type 'a auth = 'a * string
  type tree = Leaf of string | Node of tree auth * tree auth 
  type tree_auth = tree auth

  let ser o = 
    match o with
    | Leaf s -> s
    | Node ((l, ls), (r, rs)) -> ls^rs
  let auth o = o, ser o |> hash

  let make_leaf s = auth (Leaf s)
  let make_branch l r = auth (Node (l, r))

  let rec retrieve path t p =
    match path, t with
    | [], (Leaf s, _) -> s :: p, Some s
    | Lp::path, (Node (l, (_, rh)), _) -> retrieve path l (rh :: p)
    | Rp::path, (Node ((_, lh), r), _) -> retrieve path r (lh :: p)
    | _, _ -> p, None
    
  let rec from_list x =
    match x with
    | [] -> failwith "empty"
    | [a] -> make_leaf a
    | l -> 
      let left, right = list_split l in
      make_branch (from_list left) (from_list right)

  let run c = c []
end

module DirMerkleProverDirHash = struct
  type 'a auth = 'a * string
  type tree = Leaf of string | Node of tree auth * tree auth 
  type tree_auth = tree auth

  let ser o = 
    match o with
    | Leaf s -> s
    | Node ((l, ls), (r, rs)) -> ls^rs
  let auth o = o, ser o |> hash
  let unauth (t, ts) p = 
    match t with
    | Leaf s -> s :: p, t
    | Node ((l, ls), (r, rs)) -> ls :: rs :: p, t

  let make_leaf s = auth (Leaf s)
  let make_branch l r = auth (Node (l, r))

  let rec retrieve path t p =
    match path, unauth t p with
    | [], (p, Leaf s) -> p, Some s
    | Lp::path, (p, Node (l, r)) -> retrieve path l p
    | Rp::path, (p, Node (l, r)) -> retrieve path r p
    | _, _ -> p, None
    
  let rec from_list x =
    match x with
    | [] -> failwith "empty"
    | [a] -> make_leaf a
    | l -> 
      let left, right = list_split l in
      make_branch (from_list left) (from_list right)

  let run c = 
    let p, res = c [] in
    List.rev p, res
end

module DirMerkleProver = struct
  type 'a auth = 'a * string
  type tree = Leaf of string | Node of tree auth * tree auth
  type tree_hash = Leafp of string | Nodep of string * string
  type tree_auth = tree auth

  let ser o = 
    (* tree_evi.serialize o *)
    match o with
    | Leaf s -> Marshal.to_string (Leafp s) marshal_flags
    | Node ((l, ls), (r, rs)) -> Marshal.to_string (Nodep (ls, rs)) marshal_flags
  let auth o = o, ser o |> hash
  let unauth (t, ts) p = ser t :: p, t

  let make_leaf s = auth (Leaf s)
  let make_branch l r = auth (Node (l, r))

  let rec retrieve path t p =
    match path, unauth t p with
    | [], (p, Leaf s) -> p, Some s
    | Lp::path, (p, Node (l, r)) -> retrieve path l p
    | Rp::path, (p, Node (l, r)) -> retrieve path r p
    | _, _ -> p, None
    
  let rec from_list x =
    match x with
    | [] -> failwith "empty"
    | [a] -> make_leaf a
    | l -> 
      let left, right = list_split l in
      make_branch (from_list left) (from_list right)

  let run c = 
    let p, res = c [] in
    List.rev p, res
end

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

  let rec retrieve path t =
    match path, unauth t with
    | [], Leaf s -> Some s
    | Lp::path, Node (l, r) -> retrieve path l
    | Rp::path, Node (l, r) -> retrieve path r
    | _, _ -> None
    
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

  let rec retrieve path t =
    match path, unauth t with
    | [], `left s -> Some s
    | Lp::path, `right (l, r) -> retrieve path l
    | Rp::path, `right (l, r) -> retrieve path r
    | _, _ -> None
    
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

  let rec retrieve path t =
    match path, unauth t with
    | [], `left s -> Some s
    | Lp::path, `right (l, r) -> retrieve path l
    | Rp::path, `right (l, r) -> retrieve path r
    | _, _ -> None
    
  let rec from_list x =
    match x with
    | [] -> failwith "empty"
    | [a] -> make_leaf a
    | l -> 
      let left, right = list_split l in
      make_branch (from_list left) (from_list right)
end

module DirMerkleVerifierDirHashMagic = struct
  type 'a auth = string
  type tree = Leaf of string | Node of tree auth * tree auth 
  type tree_auth = tree auth

  let rec retrieve path root p =
    let rec _validate path child p = 
      match p,path with
      | [],[] -> child
      | sibling::p, Lp::path -> 
          _validate path (hash (child ^ sibling)) p;
      | sibling::p, Rp::path -> 
          _validate path (hash (sibling ^ child)) p
      | _ -> assert false
    in
    match p with
    | leaf::p -> assert (_validate (List.rev path) (hash leaf) p = root)
    | [] -> failwith "empty proof"
end

module DirMerkleVerifierDirHash = struct
  type 'a auth = string
  type tree = Leaf of string | Node of tree auth * tree auth 
  type tree_auth = tree auth

  let unauth h ps = match ps with
    | [] -> failwith "proof failure1"
    | p::ps ->
      if String.length p <> hash_size then
        if hash p = h then
          ps, Leaf p
        else failwith "proof failure2"
      else
        match ps with
        | [] -> failwith "proof failure3"
        | l::ps ->
          if hash (l^p) = h then
            ps, Node (l, p)
          else failwith "proof failure4"

  let rec retrieve path t p =
    match path, unauth t p with
    | [], (p, Leaf s) -> p, Some s
    | Lp::path, (p, Node (l, r)) -> retrieve path l p
    | Rp::path, (p, Node (l, r)) -> retrieve path r p
    | _, _ -> p, None
end

module DirMerkleVerifier = struct
  type 'a auth = string
  type tree = Leaf of string | Node of tree auth * tree auth
  type tree_hash = Leafp of string | Nodep of string * string
  type tree_auth = tree auth

  let deser s = 
    match Marshal.from_string s 0 with
    | Leafp s -> Leaf s
    | Nodep (ls, rs) -> Node (ls, rs)
  let unauth h ps = match ps with
    | [] -> failwith "proof failure1"
    | p::ps when hash p = h -> ps, deser p
    | _ -> failwith "proof failure2"

  let rec retrieve path t p =
    match path, unauth t p with
    | [], (p, Leaf s) -> p, Some s
    | Lp::path, (p, Node (l, r)) -> retrieve path l p
    | Rp::path, (p, Node (l, r)) -> retrieve path r p
    | _, _ -> p, None
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

  let deser s = 
    match Marshal.from_string s 0 with
    | Leafp s -> Leaf s
    | Nodep (ls, rs) -> Node (ls, rs)
  let unauth h =
    let p = from_channel_with_string !input in
    if hash p = h then deser p
    else failwith "Proof failure"

  let rec retrieve path t =
    match path, unauth t with
    | [], Leaf s -> Some s
    | Lp::path, Node (l, r) -> retrieve path l
    | Rp::path, Node (l, r) -> retrieve path r
    | _, _ -> None
end

module DirMerkleVerifierPolyIo = struct
  type 'a auth = string
  type tree = [`left of string | `right of tree auth * tree auth ]
  type tree_auth = tree auth

  let input = ref (open_in_bin "/dev/null")

  let set_input s = 
    close_in !input; input := open_in_bin s
  let close_input () = close_in !input; input := open_in_bin "/dev/null"

  let deser s = Marshal.from_string s 0
  let unauth h =
    let p = from_channel_with_string !input in
    if hash p = h then deser p
    else failwith "Proof failure"

  let rec retrieve path t =
    match path, unauth t with
    | [], `left s -> Some s
    | Lp::path, `right (l, r) -> retrieve path l
    | Rp::path, `right (l, r) -> retrieve path r
    | _, _ -> None
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

  let deser s = match tree_evi.deserialize s with Some s -> s | None -> raise (Invalid_argument "deser")
  let unauth h =
    let p = from_channel_with_string !input in
    if hash p = h then deser p
    else failwith "Proof failure"

  let rec retrieve path t =
    match path, unauth t with
    | [], `left s -> Some s
    | Lp::path, `right (l, r) -> retrieve path l
    | Rp::path, `right (l, r) -> retrieve path r
    | _, _ -> None
end

let read_dir_prover_hash_magic_tree s =
  let n = exp 2 s in
  let chn = Printf.sprintf "%s/mtree1_%d.dat" data_folder s |> open_in_bin in
  let l = read_vals n chn in
  close_in chn;
  DirMerkleProverDirHashMagic.from_list l

let read_dir_prover_hash_tree s =
  let n = exp 2 s in
  let chn = Printf.sprintf "%s/mtree1_%d.dat" data_folder s |> open_in_bin in
  let l = read_vals n chn in
  close_in chn;
  DirMerkleProverDirHash.from_list l

let read_dir_prover_tree s =
  let n = exp 2 s in
  let chn = Printf.sprintf "%s/mtree1_%d.dat" data_folder s |> open_in_bin in
  let l = read_vals n chn in
  close_in chn;
  DirMerkleProver.from_list l

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

let rec dirprover_hash_merkle_magic_retrieves t paths =
  match paths with
  | [] -> ()
  | path::paths -> 
    let _ = DirMerkleProverDirHashMagic.run (DirMerkleProverDirHashMagic.retrieve path t) in
    dirprover_hash_merkle_magic_retrieves t paths

let rec dirprover_hash_merkle_retrieves t paths =
  match paths with
  | [] -> ()
  | path::paths -> 
    let _ = DirMerkleProverDirHash.run (DirMerkleProverDirHash.retrieve path t) in
    dirprover_hash_merkle_retrieves t paths

let rec dirprover_merkle_retrieves t paths =
  match paths with
  | [] -> ()
  | path::paths -> 
    let _ = DirMerkleProver.run (DirMerkleProver.retrieve path t) in
    dirprover_merkle_retrieves t paths

let dirprover_merkle_io_retrieves file t paths =
  DirMerkleProverIo.set_output file;
  let rec aux paths =
    match paths with
    | [] -> DirMerkleProverIo.close_output ()
    | path::paths ->
      DirMerkleProverIo.retrieve path t;
      aux paths
  in
  aux paths

let dirprover_merkle_poly_io_retrieves file t paths =
  DirMerkleProverPolyIo.set_output file;
  let rec aux paths =
    match paths with
    | [] -> DirMerkleProverPolyIo.close_output ()
    | path::paths ->
      DirMerkleProverPolyIo.retrieve path t;
      aux paths
  in
  aux paths

let dirprover_merkle_poly_mar_ser_io_retrieves file t paths =
  DirMerkleProverPolyMarSerIo.set_output file;
  let rec aux paths =
    match paths with
    | [] -> DirMerkleProverPolyMarSerIo.close_output ()
    | path::paths ->
      DirMerkleProverPolyMarSerIo.retrieve path t;
      aux paths
  in
  aux paths

let prover_io_merkle_retrieves file t paths =
  Prover_io.set_output file;
  let rec aux paths =
    match paths with
    | [] -> Prover_io.close_output ()
    | path::paths ->
      let _ = Prover_io.run (Merkle_Prover_io.retrieve path t) in
      aux paths
  in
  aux paths

let prover_io_merkle_magic_retrieves file t paths =
  Prover_io.set_output file;
  let rec aux paths =
    match paths with
    | [] -> Prover_io.close_output ()
    | path::paths ->
      let _ = Prover_io.run (Merkle_Prover_io.retrieve_magic path t) in
      aux paths
  in
  aux paths

let dirprover_hash_merkle_magic_retrieves_keep t paths =
  let rec aux paths proofs =
    match paths with
    | [] -> List.rev proofs
    | path::paths -> 
      let proof, _ = DirMerkleProverDirHashMagic.run (DirMerkleProverDirHashMagic.retrieve path t) in
      aux paths (proof::proofs)
  in
  aux paths []

let dirprover_hash_merkle_retrieves_keep t paths =
  let rec aux paths proofs =
    match paths with
    | [] -> List.rev proofs
    | path::paths -> 
      let proof, _ = DirMerkleProverDirHash.run (DirMerkleProverDirHash.retrieve path t) in
      aux paths (proof::proofs)
  in
  aux paths []

let dirprover_merkle_retrieves_keep t paths =
  let rec aux paths proofs =
    match paths with
    | [] -> List.rev proofs
    | path::paths -> 
      let proof, _ = DirMerkleProver.run (DirMerkleProver.retrieve path t) in
      aux paths (proof::proofs)
  in
  aux paths []

let rec dirverifier_hash_merkle_magic_retrieves ht paths proofs =
  match paths, proofs with
  | [], [] -> ()
  | path::paths, proof::proofs ->
    let _ = DirMerkleVerifierDirHashMagic.retrieve path ht proof in
    dirverifier_hash_merkle_magic_retrieves ht paths proofs
  | _ -> failwith "paths and proofs must match in length"

let rec dirverifier_hash_merkle_retrieves ht paths proofs =
  match paths, proofs with
  | [], [] -> ()
  | path::paths, proof::proofs ->
    let _ = DirMerkleVerifierDirHash.retrieve path ht proof in
    dirverifier_hash_merkle_retrieves ht paths proofs
  | _ -> failwith "paths and proofs must match in length"

let rec dirverifier_merkle_retrieves ht paths proofs =
  match paths, proofs with
  | [], [] -> ()
  | path::paths, proof::proofs ->
    let _ = DirMerkleVerifier.retrieve path ht proof in
    dirverifier_merkle_retrieves ht paths proofs
  | _ -> failwith "paths and proofs must match in length"

let dirverifier_merkle_io_retrieves file ht paths =
  DirMerkleVerifierIo.set_input file;
  let rec aux paths =
    match paths with
    | [] -> DirMerkleVerifierIo.close_input ()
    | path::paths ->
      let _ = DirMerkleVerifierIo.retrieve path ht in
      aux paths
  in
  aux paths

let dirverifier_merkle_poly_io_retrieves file ht paths =
  DirMerkleVerifierPolyIo.set_input file;
  let rec aux paths =
    match paths with
    | [] -> DirMerkleVerifierPolyIo.close_input ()
    | path::paths ->
      let _ = DirMerkleVerifierPolyIo.retrieve path ht in
      aux paths
  in
  aux paths

let dirverifier_merkle_poly_mar_ser_io_retrieves file ht paths =
  DirMerkleVerifierPolyMarSerIo.set_input file;
  let rec aux paths =
    match paths with
    | [] -> DirMerkleVerifierPolyMarSerIo.close_input ()
    | path::paths ->
      let _ = DirMerkleVerifierPolyMarSerIo.retrieve path ht in
      aux paths
  in
  aux paths

let verifier_io_merkle_retrieves file t paths =
  Verifier_io.set_input file;
  let rec aux paths =
    match paths with
    | [] -> Verifier_io.close_input ()
    | path::paths ->
      let _ = Verifier_io.run (Merkle_Verifier_io.retrieve path t) in
      aux paths
  in
  aux paths

let verifier_io_merkle_magic_retrieves file t paths =
  Verifier_io.set_input file;
  let rec aux paths =
    match paths with
    | [] -> Verifier_io.close_input ()
    | path::paths ->
      let _ = Verifier_io.run (Merkle_Verifier_io.retrieve_magic path t) in
      aux paths
  in
  aux paths;;

job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i),
  fun () ->
    Printf.printf "%d %d dirprover_hash_merkle_magic_retrieves" i s;
    let t = read_dir_prover_hash_magic_tree s in
    let paths = read_mrk_queries s in
    gc_collect ();
    measure_call ("dirprover_hash_merkle_magic_retrieves "^(string_of_int s)) (dirprover_hash_merkle_magic_retrieves t) paths)
config_array;

job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i),
  fun () ->
    Printf.printf "%d %d dirprover_hash_merkle_retrieves" i s;
    let t = read_dir_prover_hash_tree s in
    let paths = read_mrk_queries s in
    gc_collect ();
    measure_call ("dirprover_hash_merkle_retrieves "^(string_of_int s)) (dirprover_hash_merkle_retrieves t) paths)
config_array;

job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i),
  fun () ->
    Printf.printf "%d %d dirprover_merkle_retrieves" i s;
    let t = read_dir_prover_tree s in
    let paths = read_mrk_queries s in
    gc_collect ();
    measure_call ("dirprover_merkle_retrieves "^(string_of_int s)) (dirprover_merkle_retrieves t) paths)
config_array;

job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i),
  fun () ->
    Printf.printf "%d %d dirprover_merkle_io_retrieves" i s;
    let t = read_dir_prover_io_tree s in
    Hashtbl.add dir_io_hash s (snd t);
    let paths = read_mrk_queries s in
    gc_collect ();
    let file = Printf.sprintf "%s/proof_mtree_look_d_%03d.dat" proof_folder s in
    measure_call ("dirprover_merkle_io_retrieves "^(string_of_int s)) (dirprover_merkle_io_retrieves file t) paths)
config_array;

job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i),
  fun () ->
    Printf.printf "%d %d dirprover_merkle_poly_io_retrieves" i s;
    let t = read_dir_prover_poly_io_tree s in
    Hashtbl.add dir_poly_io_hash s (snd t);
    let paths = read_mrk_queries s in
    gc_collect ();
    let file = Printf.sprintf "%s/proof_mtree_look_dp_%03d.dat" proof_folder s in
    measure_call ("dirprover_merkle_poly_io_retrieves "^(string_of_int s)) (dirprover_merkle_poly_io_retrieves file t) paths)
config_array;

job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i),
  fun () ->
    Printf.printf "%d %d dirprover_merkle_poly_mar_ser_io_retrieves" i s;
    let t = read_dir_prover_poly_mar_ser_io_tree s in
    Hashtbl.add dir_poly_mar_ser_io_hash s (snd t);
    let paths = read_mrk_queries s in
    gc_collect ();
    let file = Printf.sprintf "%s/proof_mtree_look_dpm_%03d.dat" proof_folder s in
    measure_call ("dirprover_merkle_poly_mar_ser_io_retrieves "^(string_of_int s)) (dirprover_merkle_poly_mar_ser_io_retrieves file t) paths)
config_array;

job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i),
  fun () ->
    Printf.printf "%d %d prover_io_merkle_retrieves" i s;
    let t = read_io_tree s in
    Hashtbl.add auth_io_hash s (Prover_io.get_hash t);
    let paths = read_mrk_queries s in
    gc_collect ();
    let file = Printf.sprintf "%s/proof_mtree_look_dpma_%03d.dat" proof_folder s in
    measure_call ("prover_io_merkle_retrieves "^(string_of_int s)) (prover_io_merkle_retrieves file t) paths)
config_array;

job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i),
  fun () ->
    Printf.printf "%d %d prover_io_merkle_magic_retrieves" i s;
    let t = read_io_tree s in
    Hashtbl.add auth_io_hash s (Prover_io.get_hash t);
    let paths = read_mrk_queries s in
    gc_collect ();
    let file = Printf.sprintf "%s/proof_mtree_look_dpmam_%03d.dat" proof_folder s in
    measure_call ("prover_io_merkle_magic_retrieves "^(string_of_int s)) (prover_io_merkle_magic_retrieves file t) paths)
config_array;

job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i) + (2*n_configs),
  fun () ->
    Printf.printf "%d %d dirverifier_hash_merkle_magic_retrieves" i s;
    let t = read_dir_prover_hash_magic_tree s in
    let ht = snd t in
    let paths = read_mrk_queries s in
    let proofs = dirprover_hash_merkle_magic_retrieves_keep t paths in
    gc_collect ();
    measure_call ("dirverifier_hash_merkle_magic_retrieves "^(string_of_int s)) (dirverifier_hash_merkle_magic_retrieves ht paths) proofs)
config_array;

job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i) + (2*n_configs),
  fun () ->
    Printf.printf "%d %d dirverifier_hash_merkle_retrieves" i s;
    let t = read_dir_prover_hash_tree s in
    let ht = snd t in
    let paths = read_mrk_queries s in
    let proofs = dirprover_hash_merkle_retrieves_keep t paths in
    gc_collect ();
    measure_call ("dirverifier_hash_merkle_retrieves "^(string_of_int s)) (dirverifier_hash_merkle_retrieves ht paths) proofs)
config_array;

job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i) + (2*n_configs),
  fun () ->
    Printf.printf "%d %d dirverifier_merkle_retrieves" i s;
    let t = read_dir_prover_tree s in
    let ht = snd t in
    let paths = read_mrk_queries s in
    let proofs = dirprover_merkle_retrieves_keep t paths in
    gc_collect ();
    measure_call ("dirverifier_merkle_retrieves "^(string_of_int s)) (dirverifier_merkle_retrieves ht paths) proofs)
config_array;

job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i) + (2*n_configs),
  fun () ->
    Printf.printf "%d %d dirverifier_merkle_io_retrieves" i s;
    let paths = read_mrk_queries s in
    let file = Printf.sprintf "%s/proof_mtree_look_d_%03d.dat" proof_folder s in
    let ht = Hashtbl.find dir_io_hash s in
    gc_collect ();
    measure_call ("dirverifier_merkle_io_retrieves "^(string_of_int s)) (dirverifier_merkle_io_retrieves file ht) paths)
config_array;

job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i) + (2*n_configs),
  fun () ->
    Printf.printf "%d %d dirverifier_merkle_poly_io_retrieves" i s;
    let paths = read_mrk_queries s in
    let file = Printf.sprintf "%s/proof_mtree_look_dp_%03d.dat" proof_folder s in
    let ht = Hashtbl.find dir_poly_io_hash s in
    gc_collect ();
    measure_call ("dirverifier_merkle_poly_io_retrieves "^(string_of_int s)) (dirverifier_merkle_poly_io_retrieves file ht) paths)
config_array;

job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i) + (2*n_configs),
  fun () ->
    Printf.printf "%d %d dirverifier_merkle_poly_mar_ser_io_retrieves" i s;
    let paths = read_mrk_queries s in
    let file = Printf.sprintf "%s/proof_mtree_look_dpm_%03d.dat" proof_folder s in
    let ht = Hashtbl.find dir_poly_mar_ser_io_hash s in
    gc_collect ();
    measure_call ("dirverifier_merkle_poly_mar_ser_io_retrieves "^(string_of_int s)) (dirverifier_merkle_poly_mar_ser_io_retrieves file ht) paths)
config_array;

job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i) + (2*n_configs),
  fun () ->
    Printf.printf "%d %d verifier_io_merkle_retrieves" i s;
    let paths = read_mrk_queries s in
    let file = Printf.sprintf "%s/proof_mtree_look_dpma_%03d.dat" proof_folder s in
    let ht = Hashtbl.find auth_io_hash s in
    gc_collect ();
    measure_call ("verifier_io_merkle_retrieves "^(string_of_int s)) (verifier_io_merkle_retrieves file ht) paths)
config_array;

job_queue := !job_queue @ List.map (fun (s, i) ->
  (Random.int (2*n_configs)) + ((4*n_configs)*i) + (2*n_configs),
  fun () ->
    Printf.printf "%d %d verifier_io_merkle_magic_retrieves" i s;
    let paths = read_mrk_queries s in
    let file = Printf.sprintf "%s/proof_mtree_look_dpmam_%03d.dat" proof_folder s in
    let ht = Hashtbl.find auth_io_hash s in
    gc_collect ();
    measure_call ("verifier_io_merkle_magic_retrieves "^(string_of_int s)) (verifier_io_merkle_magic_retrieves file ht) paths)
config_array;

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
