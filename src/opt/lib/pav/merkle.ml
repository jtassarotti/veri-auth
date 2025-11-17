open Cryptoffi
open Byte_parser

type node_ty = Cut | Leaf | Node

type node = { 
  node_ty: node_ty;
  hash: bytes;
  child0: child ref;
  child1: child ref;
  label: bytes;
  value: bytes
}
and child = node option
type map = { root: child ref }

type merkle_proof = { 
  siblings: bytes;
  is_other_leaf: bool;
  leaf_label: bytes;
  leaf_val: bytes
}
type update_proof = {
  old_val: bytes;
  old_proof: bytes;
  new_proof: bytes
}

let merkle_proof_evi: merkle_proof evidence =
  let conv_to (st: merkle_proof) = 
    get_slice st.siblings, st.is_other_leaf, get_slice st.leaf_label, get_slice st.leaf_val in
  let conv_from (siblings, is_other_leaf, leaf_label, leaf_val) = 
    { siblings = get_slice_byt siblings; is_other_leaf = is_other_leaf; 
      leaf_label = get_slice_byt leaf_label; leaf_val = get_slice_byt leaf_val }
  in
  let base_evi = quad_evi slice1D_evi bool_evi slice1D_evi slice1D_evi in
  { write = write_st conv_to base_evi.write; 
    read = read_st conv_from base_evi.read }

let update_proof_evi: update_proof evidence =
  let conv_to (st: update_proof) = 
    get_slice st.old_val, get_slice st.old_proof, get_slice st.new_proof in
  let conv_from (old_val, old_proof, new_proof) = 
    { old_val = get_slice_byt old_val; old_proof = get_slice_byt old_proof; new_proof = get_slice_byt new_proof }
  in
  let base_evi = trio_evi slice1D_evi slice1D_evi slice1D_evi in
  { write = write_st conv_to base_evi.write; 
    read = read_st conv_from base_evi.read }

let empty_node_tag =
  let b = Bytes.create 2 in
  Bytes.set_uint16_le b 0 0; b

let leaf_node_tag = 
  let b = Bytes.create 2 in
  Bytes.set_uint16_le b 0 1; b

let inner_node_tag =
  let b = Bytes.create 2 in
  Bytes.set_uint16_le b 0 2; b

let max_depth = 8 * Cryptoffi.hash_len


let get_bit b n: bool = (* false on left, true on right *)
  let slot = n / 8 in
  if slot >= Bytes.length b then failwith "n too big" else
  let byte = Bytes.get b slot in
  let off = n mod 8 in
  let num = Char.code byte in
  (Int.shift_left 1 off |> (land) num) <> 0


let comp_empty_hash () =
  hash_bytes empty_node_tag

let comp_leaf_hash (label: bytes) (value: bytes): bytes =
  let b = write_bytes leaf_node_tag label in
  let b' = write_bytes b value in
  hash_bytes b'

let comp_inner_hash child0_hash child1_hash =
  let ctx = write inner_node_tag in
  let ctx' = sum ctx child0_hash in
  let ctx'' = sum ctx' child1_hash in
  encode_ctx ctx''

let empty_hash = comp_empty_hash ()

let get_child_hash child = match child with
  | None -> empty_hash
  | Some node -> node.hash

let get_map_hash (m: map) = get_child_hash !(m.root)

let create_cut hash =
  { node_ty = Cut; hash = hash; child0 = ref None; child1 = ref None;
    label = Bytes.empty; value = Bytes.empty }

let create_leaf label value =
  { node_ty = Leaf; hash = comp_leaf_hash label value; 
    child0 = ref None; child1 = ref None; label = label; value = value }

let create_node child0 child1 =
  let child0_hash, child1_hash = get_child_hash child0, get_child_hash child1 in
  { node_ty = Node; hash = comp_inner_hash child0_hash child1_hash;
    child0 = ref child0; child1 = ref child1; label = Bytes.empty; value = Bytes.empty }

let create_temp_node () =
  { node_ty = Node; hash = empty_hash; child0 = ref None; child1 = ref None;
    label = Bytes.empty; value = Bytes.empty }

let get_child (n: node) label (depth: int): (child ref * child ref) =
  if get_bit label depth then
    n.child0, n.child1
  else
    n.child1, n.child0

let empty_map () = { root = ref None }

let print_child child =
  let rec aux i child =
    print_int i;
    match child with
    | None -> print_endline "|"
    | Some node ->
      match node.node_ty with
      | Cut -> failwith "Tree with cut node"
      | Leaf -> 
        print_string ". Leaf "; print_bytes node.hash; print_endline ("//")
      | Node ->
        print_string ". Node "; print_bytes node.hash; print_string "[";
        aux (i+1) !(node.child0); aux (i+1) !(node.child1); print_string ("]")
  in
  aux 0 child
  


let recompute_hash (n: node): node =
  let child0_hash, child1_hash = get_child_hash !(n.child0), get_child_hash !(n.child1) in
  let new_hash = comp_inner_hash child0_hash child1_hash in
  { n with hash = new_hash }


let find (n: child) (label: bytes) (get_proof: bool): ((bytes * bytes) option * bytes) =
  let rec find_aux n (depth: int) (proof: bytes) = 
    match n with
    | None -> None, 
        if get_proof then proof else Bytes.empty
    | Some node ->
      match node.node_ty with
      | Cut -> failwith "find into cut node"
      | Leaf -> Some (node.label, node.value), 
          if get_proof then proof else Bytes.empty
      | Node ->
        let child, sib = get_child node label depth in
        let new_proof = Bytes.cat (get_child_hash !sib) proof in
        find_aux (!child) (depth+1) new_proof
  in
  find_aux n 0 Bytes.empty

let prove_aux (n: child) (label: bytes) (get_proof: bool): (bytes option * bytes) =
  let opt_found, proof = find n label get_proof in
  match opt_found with
  | None ->
    if not get_proof then None, Bytes.empty else
      let merkle_proof = { 
        siblings = proof;
        is_other_leaf = false;
        leaf_label = Bytes.empty;
        leaf_val = Bytes.empty
        }
      in
      None, merkle_proof_evi.write Bytes.empty merkle_proof
  | Some (found_label, found_value) ->
    if Bytes.equal found_label label then
      if not get_proof then Some found_value, Bytes.empty else
        let merkle_proof = { 
          siblings = proof;
          is_other_leaf = false;
          leaf_label = Bytes.empty;
          leaf_val = Bytes.empty
          }
        in
        Some found_value,
          merkle_proof_evi.write Bytes.empty merkle_proof
    else
      if not get_proof then None, Bytes.empty else
        let merkle_proof = { 
          siblings = proof;
          is_other_leaf = true;
          leaf_label = found_label;
          leaf_val = found_value
          }
        in
        None, merkle_proof_evi.write Bytes.empty merkle_proof

let prove (m: map) (label: bytes): (bytes option * bytes) =
  prove_aux !(m.root) label true

(* TODO: probably shouldn't return new_proof and instead repurpose compute_new_hash to use old_proof *)
let rec put_aux (n0: child ref) (depth: int) (label: bytes) (value: bytes): bool =
  assert (depth <= max_depth);

  match !n0 with
  | None ->
    let leaf = create_leaf label value in
    n0 := Some leaf; false
  | Some node ->
    match node.node_ty with
    | Cut -> true
    | Leaf ->
      if Bytes.equal node.label label then begin
        let leaf = create_leaf label value in
        n0 := Some leaf; false
      end else begin
        let inner = create_temp_node () in
        let old_child, _ = get_child inner node.label depth in
        old_child := Some node;
        let new_child, _ = get_child inner label depth in
        assert (not (put_aux new_child (depth+1) label value));
        n0 := Some (recompute_hash inner); false
      end
    | Node ->
      let c, sib = get_child node label depth in
      assert (not (put_aux c (depth+1) label value));
      n0 := Some (recompute_hash node); false

let put (m: map) (label: bytes) (value: bytes): bytes =
  assert (Bytes.length label = Cryptoffi.hash_len);
  let value_opt, old_proof = prove m label in
  assert (not (put_aux m.root 0 label value));
  let _, new_proof = prove m label in
  match value_opt with
  | None -> 
    update_proof_evi.write Bytes.empty 
      { old_val = Bytes.empty; old_proof = old_proof; new_proof = new_proof }
  | Some value ->
    update_proof_evi.write Bytes.empty 
      { old_val = value; old_proof = old_proof; new_proof = new_proof }


(* let new_shell (depth: int) (label: bytes) (sibs: bytes): child =
  let sibs_len = get_slice_len siblings in
  if sibs_len = 0 then None else
  let split = sibs_len - Cryptoffi.hash_len in
  let sibs0 = Bytes.sub sibs 0 split in
  let hash = Bytes.sub sibs split Cryptoffi.hash_len in
  let cut = create_cut hash in
  let inner = create_temp_node () in
  let child, sib = get_child inner label depth in
  sib := Some cut;
  child := new_shell (depth+1) label sibs0;
  Some (recompute_hash inner)


let proof_to_tree (label: bytes) (proof: bytes): node option =
  if Bytes.length label <> Cryptoffi.hash_len then None else
  match merkle_proof_evi.read proof with
  | None -> None
  | Some (merkle_proof, _) ->
    let sibs_len = get_slice_len merkle_proof.siblings in
    if sibs_len mod Cryptoffi.hash_len <> 0 then None
    else
      let sibs_depth = sibs_len / Cryptoffi.hash_len in
      if sibs_depth > max_depth then None else
      let tr = create_cut *)

let rec compute_proof_hash (cur_hash: bytes) (label: bytes) (depth: int) (sibs: bytes) (sibs_i: int): bytes =
  if depth = -1 then cur_hash else
  let next_sib = Bytes.sub sibs (sibs_i * hash_len) hash_len in
  (* print_endline "compute_proof_hash";
  print_bytes cur_hash; print_newline ();
  print_bytes next_sib; print_newline (); *)
  let new_hash =
    if get_bit label depth then
      comp_inner_hash cur_hash next_sib
    else
      comp_inner_hash next_sib cur_hash
  in
  compute_proof_hash new_hash label (depth-1) sibs (sibs_i+1)


let verify_memb (label: bytes) (value: bytes) (proof: bytes): bytes option =
  match merkle_proof_evi.read proof with
  | None -> (print_string "here3"; None)
  | Some (merkle_proof, _) ->
    let sibs = merkle_proof.siblings in
    let sibs_len = Bytes.length merkle_proof.siblings in
    if sibs_len mod Cryptoffi.hash_len <> 0 then (print_string "here4"; None)
    else
      let sibs_depth = sibs_len / hash_len in
      let val_hash = comp_leaf_hash label value in
      Some (compute_proof_hash val_hash label (sibs_depth-1) sibs 0)

let verify_nonmemb (label: bytes) (proof: bytes): bytes option =
  match merkle_proof_evi.read proof with
  | None -> None
  | Some (merkle_proof, _) ->
    let sibs = merkle_proof.siblings in
    let sibs_len = Bytes.length merkle_proof.siblings in
    if sibs_len mod Cryptoffi.hash_len <> 0 then None
    else
      let sibs_depth = sibs_len / hash_len in
      (* let _ = print_string "depth: "; print_int sibs_depth; print_newline () in *)
      let cur_hash =
        if merkle_proof.is_other_leaf then
          let leaf_label = merkle_proof.leaf_label in
          let leaf_val = merkle_proof.leaf_val in
          comp_leaf_hash leaf_label leaf_val
        else
          empty_hash
      in
      Some (compute_proof_hash cur_hash label (sibs_depth-1) sibs 0)

let verify_update (label: bytes) (value: bytes) (proof: bytes): (bytes * bytes) option =
  match update_proof_evi.read proof with
  | None -> (print_string "here"; None)
  | Some (update_proof, _) ->
    let old_proof = update_proof.old_proof in
    let new_proof = update_proof.new_proof in
    let old_hash_opt = 
      if Bytes.length update_proof.old_val = 0 then
        verify_nonmemb label old_proof
      else
        let value = update_proof.old_val in
        verify_memb label value old_proof
    in
    match old_hash_opt with
    | None -> (print_string "here1"; None)
    | Some old_hash ->
      match verify_memb label value new_proof with
      | None -> (print_string "here2"; None)
      | Some new_hash -> Some (old_hash, new_hash)
