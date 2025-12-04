open Advrpc
open Auditor
open Cryptoffi
open Hashchain
open Ktcore
open Merkle
open Server
open Utils


type evid_vrf = {
  vrf_pk0: bytes;
  sig0: bytes;
  vrf_pk1: bytes;
  sig1: bytes
}

type evid_link = {
  epoch: int;
  link0: bytes;
  sig0: bytes;
  link1: bytes;
  sig1: bytes
}

type evid =
  | Noevid
  | Vrf of evid_vrf
  | Link of evid_link


let check_evid_vrf (e: evid_vrf) (pk: pub_sig_key): bool =
  not (verify_vrf_sig pk e.vrf_pk0 e.sig0) ||
    not (verify_vrf_sig pk e.vrf_pk1 e.sig1) ||
    Bytes.equal e.vrf_pk0 e.vrf_pk1

let check_evid_link (e: evid_link) (pk: pub_sig_key): bool =
  not (verify_link_sig pk e.epoch e.link0 e.sig0) ||
    not (verify_link_sig pk e.epoch e.link1 e.sig1) ||
    Bytes.equal e.link0 e.link1

let check_evid (e: evid) (pk: pub_sig_key): bool =
  match e with
  | Noevid -> true
  | Vrf evid_vrf -> check_evid_vrf evid_vrf pk
  | Link evid_link -> check_evid_link evid_link pk


type next_ver = {
  ver: int;
  is_pending: bool;
  pending_pk: bytes
}

type epoch = {
  epoch: int;
  dig: bytes;
  link: bytes;
  sign: bytes
}

type serv = {
  cli: Advrpc.client;
  sig_pk: pub_sig_key;
  vrf_pk: vrf_pk;
  vrf_sig: bytes
}

type client = {
  uid: int;
  mutable pend: next_ver;
  mutable last: epoch;
  serv: serv
}


let get_next_ep (prev: epoch) (sig_pk: pub_sig_key) (chain_proof: bytes) (sign: bytes): epoch option =
  match Hashchain.verify prev.link chain_proof with
  | None -> None
  | Some (ext_len, new_dig, new_link) ->
    if ext_len = 0 then Some prev
    else
      if check_overflow prev.epoch ext_len then None
      else
        let new_ep = prev.epoch + ext_len in
        if verify_link_sig sig_pk new_ep new_link sign then 
          Some { epoch = new_ep; dig = new_dig; link = new_link; sign = sign }
        else None

let check_memb (vrf_pk: vrf_pk) (uid: int) (ver: int) (dig: bytes) (memb: memb): bool =
  match check_map_label vrf_pk uid ver memb.label_proof with
  | None -> true
  | Some label ->
    let map_val = get_map_val memb.pk_open in
    match verify_memb label map_val memb.merkle_proof with
    | None -> true
    | Some dig0 -> not (Bytes.equal dig0 dig)

let check_hist (vrf_pk: vrf_pk) (uid: int) (prefix_len: int) (dig: bytes) (hist: memb array): bool =
  let _, b = Array.fold_left (fun (ver, b) memb ->
    ver+1, 
      if b then b
      else check_memb vrf_pk uid (prefix_len + ver) dig memb
    ) (0, false) hist
  in b

let check_nonmemb (vrf_pk: vrf_pk) (uid: int) (ver: int) (dig: bytes) (non_memb: non_memb): bool =
  match check_map_label vrf_pk uid ver non_memb.label_proof with
  | None -> true
  | Some label ->
    match verify_nonmemb label non_memb.merkle_proof with
    | None -> true
    | Some dig0 -> not (Bytes.equal dig0 dig)

let check_audit (serv_pk: pub_sig_key) (adtr_pk: pub_sig_key) (ep: int) (reply: get_reply_true): bool =
  verify_vrf_sig adtr_pk reply.vrf_pk reply.adtr_vrf_sig ||
    verify_vrf_sig serv_pk reply.vrf_pk reply.serv_vrf_sig ||
    verify_link_sig adtr_pk ep reply.link reply.adtr_link_sig ||
    verify_link_sig serv_pk ep reply.link reply.serv_link_sig


let put (c: client) (pk: bytes) =
  if c.pend.is_pending then
    assert (Bytes.equal c.pend.pending_pk pk)
  else
    let cur_pend = c.pend in
    c.pend <- { ver = cur_pend.ver; is_pending = true; pending_pk = pk };
  
  Server_rpc.call_put c.serv.cli c.uid pk c.pend.ver

let get (c: client) (uid: int): (int * bool * bytes) blame_ret =
  match Server_rpc.call_history c.serv.cli uid c.last.epoch 0 with
  | `left b -> `left b
  | `right hreply ->
    match get_next_ep c.last c.serv.sig_pk hreply.chain_proof hreply.link_sig with
    | None -> `left blame_serv_full
    | Some next ->
      if check_hist c.serv.vrf_pk uid 0 next.dig hreply.hist then `left blame_serv_full
      else
        let bound_ver = Array.length hreply.hist in
        if check_nonmemb c.serv.vrf_pk uid bound_ver next.dig hreply.bound then `left blame_serv_full
        else begin
          c.last <- next;
          if bound_ver = 0 then
            `right (next.epoch, false, emp_bytes)
          else
            let last_key = Array.get hreply.hist (bound_ver - 1) in
            `right (next.epoch, true, last_key.pk_open.value)
        end

let self_mon (c: client): (int * bool) blame_ret =
  match Server_rpc.call_history c.serv.cli c.uid c.last.epoch c.pend.ver with
  | `left b -> `left b
  | `right hreply ->
    let chain_proof, sign, hist, bound = 
      hreply.chain_proof, hreply.link_sig, hreply.hist, hreply.bound
    in
    match get_next_ep c.last c.serv.sig_pk chain_proof sign with
    | None -> `left blame_serv_full
    | Some next ->
      if check_hist c.serv.vrf_pk c.uid c.pend.ver next.dig hist then
        `left blame_serv_full
      else
        let hist_len = Array.length hist in
        let bound_ver = c.pend.ver + hist_len in
        if check_nonmemb c.serv.vrf_pk c.uid bound_ver next.dig bound then
          `left blame_serv_full
        else
          if not c.pend.is_pending then
            if hist_len <> 0 then
              `left (blame_serv_full lor blame_clients)
            else begin
              c.last <- next;
              `right (next.epoch, false)
            end
          else
            if hist_len > 1 then
              `left (blame_serv_full lor blame_clients)
            else
              if hist_len = 0 then begin
                c.last <- next;
                `right (next.epoch, false)
              end else
                let new_key = Array.get hist 0 in
                if Bytes.equal new_key.pk_open.value c.pend.pending_pk then begin
                  c.last <- next;
                  c.pend <- { is_pending = false; pending_pk = emp_bytes; ver = c.pend.ver + 1 };
                  `right (next.epoch, true)
                end else
                  `left (blame_serv_full lor blame_clients)

let audit (c: client) (adtr_addr: int64) (adtr_pk: pub_sig_key): (evid option * blame) =
  let cli = dial adtr_addr in
  let last = c.last in
  print_endline "Calling get on auditor";
  match Auditor_rpc.call_get cli last.epoch with
  | `left b -> None, b
  | `right reply ->
    print_endline "Checking audit";
    if check_audit c.serv.sig_pk adtr_pk last.epoch reply then
      None, blame_adtr_full
    else
      if not (Bytes.equal c.serv.vrf_pk reply.vrf_pk) then
        let evid = Vrf { vrf_pk0 = c.serv.vrf_pk; sig0 = c.serv.vrf_sig; 
          vrf_pk1 = reply.vrf_pk; sig1 = reply.serv_vrf_sig }
        in
        Some evid, blame_serv_sig
      else if not (Bytes.equal last.link reply.link) then
        let evid = Link { epoch = last.epoch; link0 = last.link;
          sig0 = last.sign; link1 = reply.link; sig1 = reply.serv_link_sig }
        in
        Some evid, blame_serv_sig
      else None, blame_none
        
let new_client (uid: int) (serv_addr: int64) (serv_pk: pub_sig_key): client blame_ret =
  let cli = dial serv_addr in
  match Server_rpc.call_start cli with
  | `left b -> `left b
  | `right reply ->
    match check_start serv_pk reply with
    | None -> `left blame_serv_full
    | Some (start_ep, start_dig, start_link, vrf_pk) ->
      let pending_put = { ver = 0; is_pending = false; pending_pk = emp_bytes } in
      let last = { epoch = start_ep; dig = start_dig; link = start_link; sign = reply.link_sig } in
      let serv = { cli = cli; sig_pk = serv_pk; vrf_pk = vrf_pk; vrf_sig = reply.vrf_sig } in
      `right { uid = uid; pend = pending_put; last = last; serv = serv }
