open Advrpc
open Ktcore
open Server
open Utils

let start_rpc = 0
let put_rpc = 1
let history_rpc = 2
let audit_rpc = 3

let new_rpc_server (s: Server.server): Advrpc.server =
  let h = IMap.empty in
  let start_fun (arg: bytes): bytes option =
    let r = start s in
    Some (start_reply_evi.write Bytes.empty r)
  in
  let h = IMap.add start_rpc start_fun h in
  let put_fun (arg: bytes): bytes option =
    match put_arg_evi.read arg with
    | None -> None
    | Some (a, _) ->
      let _ = put s a.uid a.pk a.ver in
      None
  in
  let h = IMap.add put_rpc put_fun h in
  let history_fun (arg: bytes): bytes option =
    match history_arg_evi.read arg with
    | None ->
      let r = `left blame_unknown in
      Some (history_reply_evi.write Bytes.empty r)
    | Some (a, _) ->
      let history_reply = 
        match history s a.uid a.prev_epoch a.prev_ver_len with
        | `left b -> `left b
        | `right (r0, r1, r2, r3) ->
          `right { chain_proof = r0; link_sig = r1; hist = r2; bound = r3 }
      in
      Some (history_reply_evi.write Bytes.empty history_reply)
  in
  let h = IMap.add history_rpc history_fun h in
  let audit_fun (arg: bytes): bytes option =
    match audit_arg_evi.read arg with
    | None ->
      let r = `left blame_unknown in
      Some (audit_reply_evi.write Bytes.empty r)
    | Some (a, _) ->
      let audit_reply =
        match audit s a.prev_epoch_len with
        | `left b -> `left b
        | `right r0 -> `right { p = r0 }
      in
      Some (audit_reply_evi.write Bytes.empty audit_reply)
  in
  let h = IMap.add audit_rpc audit_fun h in
  Advrpc.new_server h

let call_start (c: client): start_reply blame_ret =
  let call_ret = call c start_rpc emp_bytes in
  match call_ret with
  | None -> `left blame_unknown
  | Some rb ->
    match start_reply_evi.read rb with
    | None -> `left blame_serv_full
    | Some (r, _) -> `right r

let call_put (c: client) (uid: int) (pk: bytes) (ver: int): unit =
  let a = { uid = uid; pk = pk; ver = ver } in
  let ab = put_arg_evi.write emp_bytes a in
  let _ = call c put_rpc ab in ()

let call_history (c: client) (uid: int) (prev_epoch: int) (prev_ver_len: int): history_reply =
  let a = { uid = uid; prev_epoch = prev_epoch; prev_ver_len = prev_ver_len } in
  let ab = history_arg_evi.write emp_bytes a in
  let call_ret = call c history_rpc ab in
  match call_ret with
  | None -> `left blame_unknown
  | Some rb ->
    match history_reply_evi.read rb with
    | None -> `left blame_serv_full
    | Some (r, _) ->
      match r with
      | `left b -> `left blame_serv_full
      | `right r -> `right r

let call_audit (c: client) (prev_epoch_len: int): audit_reply =
  let a = { prev_epoch_len = prev_epoch_len } in
  let ab = audit_arg_evi.write emp_bytes a in
  let call_ret = call c audit_rpc ab in
  match call_ret with
  | None -> `left blame_unknown
  | Some rb ->
    match audit_reply_evi.read rb with
    | None -> `left blame_serv_full
    | Some (r, _) ->
      match r with
      | `left b -> `left blame_serv_full
      | `right r -> `right r
