open Advrpc
open Cryptoffi
open Hashchain
open Ktcore
open Merkle
open Server
open Server_rpc
open Utils
open Byte_parser


type update_reply = {
  err: blame
}

type get_arg = {
  epoch: int
}

type get_reply_true = {
  link: bytes;
  serv_link_sig: bytes;
  adtr_link_sig: bytes;
  vrf_pk: bytes;
  serv_vrf_sig: bytes;
  adtr_vrf_sig: bytes
}
type get_reply = get_reply_true blame_ret


let update_reply_evi: update_reply evidence =
  let conv_to (st: update_reply) = st.err in
  let conv_from err = { err = err } in
  let base_evi = int_evi in
  { write = write_st conv_to base_evi.write;
    read = read_st conv_from base_evi.read }

let get_arg_evi: get_arg evidence =
  let conv_to (st: get_arg) = st.epoch in
  let conv_from epoch = { epoch = epoch } in
  let base_evi = int_evi in
  { write = write_st conv_to base_evi.write;
    read = read_st conv_from base_evi.read }

let get_reply_evi: get_reply evidence =
  let conv_to (st: get_reply_true) =
    get_slice st.link, get_slice st.serv_link_sig, get_slice st.adtr_link_sig, 
    get_slice st.vrf_pk, get_slice st.serv_vrf_sig, get_slice st.adtr_link_sig
  in
  let conv_from (link, serv_link_sig, adtr_link_sig, vrf_pk, 
    serv_vrf_sig, adtr_vrf_sig) =
    { link = get_slice_byt link; serv_link_sig = get_slice_byt serv_link_sig; 
      adtr_link_sig = get_slice_byt adtr_link_sig; vrf_pk = get_slice_byt vrf_pk; 
      serv_vrf_sig = get_slice_byt serv_vrf_sig; adtr_vrf_sig = get_slice_byt adtr_vrf_sig }
  in
  let base_evi = hex_evi slice1D_evi slice1D_evi slice1D_evi slice1D_evi slice1D_evi slice1D_evi |> blame_ret_evi in
  { write = write_st (blame_ret_conv_to conv_to) base_evi.write;
    read = read_st (blame_ret_conv_from conv_from) base_evi.read }


type history = {
  link: bytes;
  serv_sig: bytes;
  adtr_sig: bytes
}

type serv = {
  cli: client;
  sig_pk: pub_sig_key;
  vrf_pk: vrf_pk;
  serv_vrf_sig: bytes;
  adtr_vrf_sig: bytes
}

type auditor = {
  mu: RWMutex.t;
  sk: priv_sig_key;
  mutable last_dig: bytes;
  start_ep: int;
  mutable hist: history array;
  serv: serv
}


let get_next_dig (prev_dig: bytes) (updates: Ktcore.update_proof list): bytes option =
  let _, dig_opt = List.fold_left (fun (early_term, dig_opt) u ->
    if early_term then true, None else
    match verify_update u.map_label u.map_val u.update_proof with
    | None -> true, dig_opt
    | Some (prev, next) ->
      if Option.get dig_opt |> Bytes.equal prev then
        false, Some next
      else
        true, None
    ) (false, None) updates
  in
  dig_opt

let get_next_link (sig_pk: pub_sig_key) (prev_ep: int) (prev_dig: bytes) (prev_link: bytes) (p: audit_proof):
  (int * bytes * bytes) option =
  if check_overflow prev_ep 1 then None
  else
    let ep = prev_ep + 1 in
    match get_next_dig prev_dig p.updates with
    | None -> None
    | Some dig ->
      let link = get_next_link prev_link dig in
      if verify_link_sig sig_pk ep link p.link_sig then Some (ep, dig, link)
      else None

(* let upd_once (a: auditor) (p: audit_proof): blame =
  if check_overflow a.start_ep (Array.length a.hist) then blame_serv_full else
  let hist_len = Array.length a.hist in
  let next_ep = a.start_ep + hist_len in
  let last_link = (Array.get a.hist (hist_len - 1)).link in
  
  match get_next_dig a.last_dig p.updates with
  | None -> blame_serv_full
  | Some next_dig ->
    let next_link = get_next_link last_link next_dig in
    if verify_link_sig a.serv.sig_pk next_ep next_link p.link_sig then
      let sign = sign_link a.sk next_ep next_link in
      a.last_dig <- next_dig;
      let info = { link = next_link; serv_sig = p.link_sig; adtr_sig = sign } in
      a.hist <- Array.append a.hist [|info|];
      blame_unknown
    else blame_serv_full *)

let update (a: auditor): blame =
  let hist_len = Array.length a.hist in
  RWMutex.with_w_lock a.mu (fun () -> 
    let num_eps = a.start_ep + hist_len in
    let upd_br = call_audit a.serv.cli num_eps in
    match upd_br with
    | `left b -> b
    | `right upd ->
      Array.fold_left (fun b p ->
        if b > 0 then b else 
        let sig_pk = a.serv.sig_pk in
        let prev_ep = a.start_ep + hist_len - 1 in
        let prev_link = (Array.get a.hist (hist_len - 1)).link in
        match get_next_link sig_pk prev_ep a.last_dig prev_link p with
        | None -> blame_serv_full
        | Some (ep, dig, link) ->
          let sign = sign_link a.sk ep link in
          a.last_dig <- dig;
          let info = { link = link; serv_sig = p.link_sig; adtr_sig = sign } in
          a.hist <- Array.append a.hist [|info|];
          blame_unknown
        ) 0 upd.p
    )

let get (a: auditor) (epoch: int): get_reply =
  RWMutex.with_r_lock a.mu (fun () ->
    let num_epochs = a.start_ep + (Array.length a.hist) in
    print_endline ((string_of_int (num_epochs))^" "^(string_of_int epoch));
    if epoch < a.start_ep then `left blame_unknown
    else if epoch >= num_epochs then `left blame_unknown
    else
      let x = Array.get a.hist (epoch - a.start_ep) in
      let gr = { link = x.link; serv_link_sig = x.serv_sig; adtr_link_sig = x.adtr_sig;
        vrf_pk = a.serv.vrf_pk; serv_vrf_sig = a.serv.serv_vrf_sig;
        adtr_vrf_sig = a.serv.adtr_vrf_sig }
      in `right gr
    )

let check_start (serv_pk: pub_sig_key) (reply: start_reply): (int * bytes * bytes * vrf_pk) option =
  if Bytes.length reply.prev_link <> hash_len then None
  else
    match Hashchain.verify reply.prev_link reply.chain_proof with
    | None -> None
    | Some (ext_len, dig, link) ->
      print_endline (string_of_int ext_len);
      if ext_len = 0 then None
      else
        if check_overflow reply.prev_epoch_len (ext_len-1) then None
        else
          let ep = reply.prev_epoch_len + (ext_len-1) in
          if (verify_link_sig serv_pk ep link reply.link_sig) && 
            (verify_vrf_sig serv_pk reply.vrf_pk reply.vrf_sig) then
              Some (ep, dig, link, reply.vrf_pk)
          else None


let new_auditor (serv_addr: int64) (serv_pk: pub_sig_key): (auditor * pub_sig_key) blame_ret =
  let cli = dial serv_addr in
  match call_start cli with
  | `left b -> `left b
  | `right reply ->
    match check_start serv_pk reply with
    | None -> `left blame_serv_full
    | Some (start_ep, start_dig, start_link, _) ->
      let mu = RWMutex.create () in
      let sk, sig_pk = sig_gen_keys () in
      let link_sig = sign_link sk start_ep start_link in
      let h = { link = start_link; serv_sig = reply.link_sig; adtr_sig = link_sig } in
      let vrf_sig = sign_vrf sk reply.vrf_pk in
      let serv = { cli = cli; sig_pk = serv_pk; vrf_pk = reply.vrf_pk; 
        serv_vrf_sig = reply.vrf_sig; adtr_vrf_sig = vrf_sig }
      in
      let a = { mu = mu; sk = sk; last_dig = start_dig; start_ep = start_ep;
        hist = [||]; serv = serv }
      in
      `right (a, sig_pk)
