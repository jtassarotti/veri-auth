open Cryptoffi
open Byte_parser

type blame = int

let blame_none       : blame = 0
let blame_serv_sig   : blame = 1
let blame_serv_full  : blame = 2
let blame_adtr_sig   : blame = 4
let blame_adtr_full  : blame = 8
let blame_clients    : blame = 16
let blame_unknown    : blame = 32

type 'a blame_ret = [ `left of blame | `right of 'a ]

let vrf_sig_tag: bytes =
  let b = Bytes.create 8 in
  Bytes.set_int64_le b 0 (Int64.zero); b

let link_sig_tag: bytes =
  let b = Bytes.create 8 in
  Bytes.set_int64_le b 0 (Int64.one); b

type vrf_sig = { sig_tag: bytes; vrf_pk: bytes }
type link_sig = { sig_tag: bytes; epoch: int; link: bytes }
type map_label = { uid: int; ver: int }
type commit_open = { value: bytes; rand: bytes }
type memb = { label_proof: bytes; pk_open: commit_open; merkle_proof: bytes }
type non_memb = { label_proof: bytes; merkle_proof: bytes }
type update_proof = { map_label: bytes; map_val: bytes; update_proof: bytes }
type audit_proof = { updates: update_proof list; link_sig: bytes }

let blame_ret_evi (evi: 'a evidence): 'a blame_ret evidence = 
  sum_evi int_evi evi
let blame_ret_conv_to conv_to a = match a with
  | `left a -> `left a
  | `right st -> `right (conv_to st)
let blame_ret_conv_from conv_from a = match a with
  | `left a -> `left a
  | `right tup -> `right (conv_from tup)

let vrf_sig_evi: vrf_sig evidence =
  let conv_to (st: vrf_sig) = st.sig_tag, get_slice st.vrf_pk in
  let conv_from (sig_tag, vrf_pk) = { sig_tag = sig_tag; vrf_pk = get_slice_byt vrf_pk } in
  let base_evi = pair_evi byte_evi slice1D_evi in
  { write = write_st conv_to base_evi.write; 
    read = read_st conv_from base_evi.read }

let link_sig_evi: link_sig evidence =
  let conv_to st = st.sig_tag, st.epoch, get_slice st.link in
  let conv_from (sig_tag, epoch, link) = 
    { sig_tag = sig_tag; epoch = epoch; link = get_slice_byt link } in
  let base_evi = trio_evi byte_evi int_evi slice1D_evi in
  { write = write_st conv_to base_evi.write; 
    read = read_st conv_from base_evi.read }

let map_label_evi: map_label evidence =
  let conv_to st = st.uid, st.ver in
  let conv_from (uid, ver) = { uid = uid; ver = ver } in
  let base_evi = pair_evi int_evi int_evi in
  { write = write_st conv_to base_evi.write; 
    read = read_st conv_from base_evi.read }

let commit_open_evi: commit_open evidence =
  let conv_to st = get_slice st.value, get_slice st.rand in
  let conv_from (value, rand) = 
    { value = get_slice_byt value; rand = get_slice_byt rand } in
  let base_evi = pair_evi slice1D_evi slice1D_evi in
  { write = write_st conv_to base_evi.write; 
    read = read_st conv_from base_evi.read }

let memb_evi: memb evidence =
  let conv_to (st: memb) = get_slice st.label_proof, st.pk_open, get_slice st.merkle_proof in
  let conv_from (label_proof, pk_open, merkle_proof) = 
    { label_proof = get_slice_byt label_proof; pk_open = pk_open; 
      merkle_proof = get_slice_byt merkle_proof } in
  let base_evi = trio_evi slice1D_evi commit_open_evi slice1D_evi in
  { write = write_st conv_to base_evi.write; 
    read = read_st conv_from base_evi.read }

let non_memb_evi: non_memb evidence =
  let conv_to st = get_slice st.label_proof, get_slice st.merkle_proof in
  let conv_from (label_proof, merkle_proof) = 
    { label_proof = get_slice_byt label_proof; merkle_proof = get_slice_byt merkle_proof } in
  let base_evi = pair_evi slice1D_evi slice1D_evi in
  { write = write_st conv_to base_evi.write; 
    read = read_st conv_from base_evi.read }

let update_proof_evi: update_proof evidence =
  let conv_to st = get_slice st.map_label, get_slice st.map_val, get_slice st.update_proof in
  let conv_from (map_label, map_val, update_proof) = 
    { map_label = get_slice_byt map_label; map_val = get_slice_byt map_val; 
      update_proof = get_slice_byt update_proof } in
  let base_evi = trio_evi slice1D_evi slice1D_evi slice1D_evi in
  { write = write_st conv_to base_evi.write; 
    read = read_st conv_from base_evi.read }

let audit_proof_evi: audit_proof evidence =
  let conv_to st = st.updates, get_slice st.link_sig in
  let conv_from (updates, link_sig) = 
    { updates = updates; link_sig = get_slice_byt link_sig } in
  let base_evi = pair_evi (list_evi update_proof_evi) slice1D_evi in
  { write = write_st conv_to base_evi.write; 
    read = read_st conv_from base_evi.read }
    

let check_blame (b: blame) (allowed: blame list): bool =
  let acc = List.fold_left (fun acc bi -> bi lor acc) blame_none allowed in
  b land (lnot acc) <> 0

let sign_vrf (sig_sk: priv_sig_key) (vrf_pk: bytes): bytes =
  let b = Bytes.empty in
  let b = vrf_sig_evi.write b { sig_tag = vrf_sig_tag; vrf_pk = vrf_pk } in
  sign sig_sk b

let verify_vrf_sig (sig_pk: pub_sig_key) (vrf_pk: bytes) (sigs: bytes): bool =
  let b = Bytes.empty in
  let b = vrf_sig_evi.write b { sig_tag = vrf_sig_tag; vrf_pk = vrf_pk } in
  sig_verify sig_pk b sigs

let sign_link (sig_sk: priv_sig_key) (epoch: int) (link: bytes): bytes =
  let b = Bytes.empty in
  let b = link_sig_evi.write b { sig_tag = link_sig_tag; epoch = epoch; link = link } in
  sign sig_sk b

let verify_link_sig (sig_pk: pub_sig_key) (epoch: int) (link: bytes) (sigs: bytes): bool =
  let b = Bytes.empty in
  let b = link_sig_evi.write b { sig_tag = link_sig_tag; epoch = epoch; link = link } in
  sig_verify sig_pk b sigs

let prove_map_label (uid: int) (ver: int) (sk: vrf_sk): bytes * bytes =
  let b = Bytes.empty in
  let b = map_label_evi.write b { uid = uid; ver = ver } in
  vrf_prove sk b

let eval_map_label (uid: int) (ver: int) (sk: vrf_sk): bytes =
  let b = Bytes.empty in
  let b = map_label_evi.write b { uid = uid; ver = ver } in
  vrf_evaluate sk b

let check_map_label (pk: vrf_pk) (uid: int) (ver: int) (proof: bytes): bytes option =
  let b = Bytes.empty in
  let b = map_label_evi.write b { uid = uid; ver = ver } in
  vrf_verify pk b proof

let get_map_val (pk_open: commit_open): bytes =
  let b = Bytes.empty in
  let b = commit_open_evi.write b pk_open in
  hash_bytes b

let get_commit_rand (commit_secret: bytes) (label: bytes): bytes =
  let hr = write commit_secret in
  let hr = sum hr label in
  encode_ctx hr
