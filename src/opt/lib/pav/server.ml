open Cryptoffi
open Hashchain
open Ktcore
open Merkle
open Workq
open Byte_parser
open Utils


type start_reply = {
  prev_epoch_len: int;
	prev_link: bytes;
	chain_proof: bytes;
	link_sig: bytes;
	vrf_pk: bytes;
	vrf_sig: bytes
}

type put_arg = {
  uid: int;
  pk: bytes;
  ver: int
}

type history_arg = {
  uid: int;
  prev_epoch: int;
  prev_ver_len: int
}

type history_reply_true = {
  chain_proof: bytes;
  link_sig: bytes;
  hist: memb array;
  bound: non_memb
}
type history_reply = history_reply_true blame_ret

type audit_arg = {
  prev_epoch_len: int
}

type audit_reply_true = {
  p: audit_proof array
}
type audit_reply = audit_reply_true blame_ret


let start_reply_evi: start_reply evidence =
  let conv_to (st: start_reply) = 
    st.prev_epoch_len, get_slice st.prev_link, get_slice st.chain_proof, 
    get_slice st.link_sig, get_slice st.vrf_pk, get_slice st.vrf_sig
  in
  let conv_from (prev_epoch_len, prev_link, chain_proof, link_sig, vrf_pk, vrf_sig) = 
    { prev_epoch_len = prev_epoch_len; prev_link = get_slice_byt prev_link;
      chain_proof = get_slice_byt chain_proof; link_sig = get_slice_byt link_sig;
      vrf_pk = get_slice_byt vrf_pk; vrf_sig = get_slice_byt vrf_sig }
  in
  let base_evi = hex_evi int_evi slice1D_evi slice1D_evi slice1D_evi slice1D_evi slice1D_evi in
  { write = write_st conv_to base_evi.write; 
    read = read_st conv_from base_evi.read }

let put_arg_evi: put_arg evidence =
  let conv_to (st: put_arg) = 
    st.uid, get_slice st.pk, st.ver
  in
  let conv_from (uid, pk, ver) = 
    { uid = uid; pk = get_slice_byt pk; ver = ver }
  in
  let base_evi = trio_evi int_evi slice1D_evi int_evi in
  { write = write_st conv_to base_evi.write; 
    read = read_st conv_from base_evi.read }

let history_arg_evi: history_arg evidence =
  let conv_to (st: history_arg) = 
    st.uid, st.prev_epoch, st.prev_ver_len
  in
  let conv_from (uid, prev_epoch, prev_ver_len) = 
    { uid = uid; prev_epoch = prev_epoch; prev_ver_len = prev_ver_len }
  in
  let base_evi = trio_evi int_evi int_evi int_evi in
  { write = write_st conv_to base_evi.write; 
    read = read_st conv_from base_evi.read }

let history_reply_evi: history_reply evidence =
  let conv_to (st: history_reply) = match st with
    | `left b -> `left b
    | `right st ->
      `right (get_slice st.chain_proof, get_slice st.link_sig, 
        st.hist, st.bound)
  in
  let conv_from s = match s with
    | `left b -> `left b
    | `right (chain_proof, link_sig, hist, bound) ->
      `right { chain_proof = get_slice_byt chain_proof; link_sig = get_slice_byt link_sig;
        hist = hist; bound = bound }
  in
  let base_evi = blame_ret_evi (quad_evi slice1D_evi slice1D_evi (array_evi memb_evi) non_memb_evi) in
  { write = write_st conv_to base_evi.write; 
    read = read_st conv_from base_evi.read }

let audit_arg_evi: audit_arg evidence =
  let conv_to (st: audit_arg) = st.prev_epoch_len in
  let conv_from prev_epoch_len = { prev_epoch_len = prev_epoch_len } in
  let base_evi = int_evi in
  { write = write_st conv_to base_evi.write; 
    read = read_st conv_from base_evi.read }

let audit_reply_evi: audit_reply evidence =
  let conv_to (st: audit_reply) = match st with
    | `left b -> `left b
    | `right st -> `right st.p
  in
  let conv_from s = match s with
    | `left b -> `left b
    | `right p -> `right { p = p }
  in
  let base_evi = blame_ret_evi (array_evi audit_proof_evi) in
  { write = write_st conv_to base_evi.write; 
    read = read_st conv_from base_evi.read }


type secrets = {
  sig_key: priv_sig_key;
  vrf_key: vrf_sk;
  commit: bytes
}

type key_store = {
  hidden: Merkle.map;
  mutable plain: bytes array IMap.t
}

type history = {
  chain: hashchain;
  mutable audits: audit_proof array;
  vrf_pk_sig: bytes
}

type server = {
  mu: RWMutex.t;
  secs: secrets;
  keys: key_store;
  hist: history;
  workq: workq
}

let empty_memb = 
  { label_proof = emp_bytes; 
    pk_open = { value = emp_bytes; rand = emp_bytes }; 
    merkle_proof = emp_bytes }


let get_hist: server -> int -> int -> memb array =
  fun s uid prefix_len ->
    let pks = IMap.find uid s.keys.plain in
    let num_vers = Array.length pks in
    let hist = Array.make (num_vers-prefix_len) empty_memb in
    let rec aux ver =
      if ver = num_vers then ()
      else
        let label, label_proof = prove_map_label uid ver s.secs.vrf_key in
        let res, map_proof = Merkle.prove s.keys.hidden label in
        assert (Option.is_some res);
        let rand = get_commit_rand s.secs.commit label in
        let ope = { value = Array.get pks uid; rand = rand } in
        let memb = { label_proof = label_proof; pk_open = ope; merkle_proof = map_proof } in
        Array.set hist (ver - prefix_len) memb;
        aux (ver + 1)
    in
    aux prefix_len; hist

let get_bound: server -> int -> int -> non_memb =
  fun s uid num_vers ->
    let label, label_proof = prove_map_label uid num_vers s.secs.vrf_key in
    let res, map_proof = Merkle.prove s.keys.hidden label in
    assert (Option.is_none res);
    { label_proof = label_proof; merkle_proof = map_proof }


let start (s: server): start_reply =
  RWMutex.with_r_lock s.mu (fun () ->
    let pred_len = (Array.length s.hist.audits) - 1 in
    let pred_link, proof = bootstrap s.hist.chain in
    let last_sig = (Array.get s.hist.audits pred_len).link_sig in
    let pk = s.secs.vrf_key.pk in
    let start_reply = 
      { prev_epoch_len = pred_len; prev_link = pred_link; chain_proof = proof;
        link_sig = last_sig; vrf_pk = pk; vrf_sig = s.hist.vrf_pk_sig }
    in
    start_reply
  )

let put (s: server) (uid: int) (pk: bytes) (ver: int) =
  let req: wq_req = { uid = uid; pk = pk; ver = ver } in
  do_q s.workq req

let history: server -> int -> int -> int -> 
  (bytes * bytes * memb array * non_memb) blame_ret =
  fun s uid prev_epoch prev_ver_len ->
    RWMutex.with_r_lock s.mu (fun () ->
      let num_eps = Array.length s.hist.audits in
      if prev_epoch >= num_eps then
        `left blame_unknown
      else
        let num_vers = IMap.find uid s.keys.plain |> Array.length in
        if prev_ver_len > num_vers then
          `left blame_unknown
        else
          let chain_proof = Hashchain.prove s.hist.chain (prev_epoch+1) in
          let link_sig = (Array.get s.hist.audits (Array.length s.hist.audits - 1)).link_sig in
          let hist = get_hist s uid prev_ver_len in
          let bound = get_bound s uid num_vers in
          let link_sig = if prev_epoch + 1 = num_eps then Bytes.empty else link_sig in
          `right (chain_proof, link_sig, hist, bound)
    )

let audit: server -> int -> audit_proof array blame_ret =
  fun s prev_epoch_len ->
    RWMutex.with_r_lock s.mu (fun () ->
      let num_eps = Array.length s.hist.audits in
      if prev_epoch_len >= num_eps then
        `left blame_unknown
      else
        let arr = Array.init (num_eps - prev_epoch_len) 
          (fun ep -> Array.get s.hist.audits (ep+prev_epoch_len))
        in `right arr
    )


type map_entry = {
  mutable label: bytes;
  mutable value: bytes
}


let check_requests (s: server) (work: work Queue.t) =
  let uid_set = IMap.empty in
  let _ = Queue.fold (fun uid_set w ->
    let uid = w.req.uid in
    let next_ver = IMap.find uid s.keys.plain |> Array.length in
    if w.req.ver <> next_ver then (w.resp <- err_resp; uid_set)
    else
      match IMap.find_opt uid uid_set with
      | None -> IMap.add uid false uid_set
      | Some ok ->
        if ok then (w.resp <- err_resp; uid_set)
        else IMap.add uid false uid_set
    ) uid_set work
  in ()

let make_entry (s: server) (win: wq_req): map_entry =
  let num_vers = IMap.find win.uid s.keys.plain |> Array.length in
  let map_label = eval_map_label win.uid num_vers s.secs.vrf_key in
  let rand = get_commit_rand s.secs.commit map_label in
  let ope = { value = win.pk; rand = rand } in
  let map_val = get_map_val ope in
  { label = map_label; value = map_val }

let make_entries (s: server) (work: work Queue.t): map_entry option array =
  let ents = Array.make (Queue.length work) None in
  let wg = Wait_group.create () in
  let _ = Queue.fold (fun i w ->
    let resp = w.resp in
    if resp.err then i+1
    else
      let req = w.req in
      Wait_group.add wg 1;
      let _ = Thread.create (fun i ->
        Some (make_entry s req) |> Array.set ents i;
        Wait_group.done_ wg;
        ) i
      in
      i+1
    )
  in
  Wait_group.wait wg;
  ents

let add_entries (s: server) (work: work Queue.t) (ents: map_entry option array) =
  let _, upd = Queue.fold (fun (i, l) w ->
    let resp = w.resp in
    if resp.err then i+1, l
    else
      let req = w.req in
      let out0 = Array.get ents i |> Option.get in
      let label = out0.label in

      let proof = Merkle.put s.keys.hidden label out0.value in
      
      let keys_plain = IMap.find req.uid s.keys.plain in
      let keys_plain' = Array.append keys_plain [|req.pk|] in
      s.keys.plain <- IMap.add req.uid keys_plain' s.keys.plain;

      let info = { map_label = label; map_val = out0.value; update_proof = proof } in
      i+1, info::l
    ) (0, []) work
  in
  let upd = List.rev upd in

  let dig = get_map_hash s.keys.hidden in
  let link = append s.hist.chain dig in
  let epoch = Array.length s.hist.audits in
  let link_sig = sign_link s.secs.sig_key epoch link in
  s.hist.audits <- Array.append s.hist.audits [|{ updates = upd; link_sig = link_sig }|]

let worker (s: server) =
  let work = Workq.get s.workq in
  check_requests s work;

  let ents = make_entries s work in
  RWMutex.with_w_lock s.mu (fun () ->
    add_entries s work ents
    );

  Queue.iter finish work

let new_server (): (server * pub_sig_key) =
  let mu = RWMutex.create () in
  let sig_sk, sig_pk = sig_gen_keys () in
  let vrf_sk = vrf_gen_key () in
  let vrf_sig = sign_vrf sig_sk vrf_sk.pk in
  let commit_sec = secure_random_bytes hash_len in
  let secs = { sig_key = sig_sk; vrf_key = vrf_sk; commit = commit_sec } in
  let hidden = empty_map () in
  let plain = IMap.empty in
  let keys = { hidden = hidden; plain = plain } in
  let chain = new_hashchain () in
  let hist = { chain = chain; audits = [||]; vrf_pk_sig = vrf_sig } in
  let wq = new_workq () in
  let s = { mu = mu; secs = secs; keys = keys; hist = hist; workq = wq } in

  let dig = get_map_hash keys.hidden in
  let link = Hashchain.append chain dig in
  let link_sig = sign_link s.secs.sig_key 0 link in
  s.hist.audits <- [|{ updates = []; link_sig = link_sig }|];

  let _ = Thread.create (fun () ->
    let rec aux () =
      worker s; aux ()
    in
    aux ()
    ) ()
  in
  s, sig_pk
