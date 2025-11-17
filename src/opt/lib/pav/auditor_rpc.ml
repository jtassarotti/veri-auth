open Advrpc
open Ktcore
open Auditor
open Utils

let update_rpc = 0
let get_rpc = 1

let new_rpc_auditor (adtr: auditor): Advrpc.server =
  let h = IMap.empty in
  let update_fun (arg: bytes): bytes option =
    let r0 = Auditor.update adtr in
    let reply_obj = { err = r0 } in
    Some (update_reply_evi.write emp_bytes reply_obj)
  in
  let h = IMap.add update_rpc update_fun h in
  let get_fun (arg: bytes): bytes option =
    match get_arg_evi.read arg with
    | None ->
      let r = `left blame_unknown in
      Some (get_reply_evi.write emp_bytes r)
    | Some (a, _) ->
      let r = Auditor.get adtr a.epoch in
      Some (get_reply_evi.write emp_bytes r)
  in
  let h = IMap.add get_rpc get_fun h in
  new_server h

let call_update (c: client): blame =
  match call c update_rpc emp_bytes with
  | None -> blame_unknown
  | Some rb ->
    match update_reply_evi.read rb with
    | None -> blame_adtr_full
    | Some (r, _) ->
      if check_blame r.err [blame_serv_full; blame_unknown] then blame_adtr_full
      else blame_none

let call_get (c: client) (epoch: int): get_reply =
  let a = { epoch = epoch } in
  let ab = get_arg_evi.write emp_bytes a in
  match call c get_rpc ab with
  | None -> `left blame_unknown
  | Some rb ->
    match get_reply_evi.read rb with
    | None -> `left blame_adtr_full
    | Some (r, _) ->
      match r with
      | `left b ->
        if check_blame b [blame_unknown] then `left blame_adtr_full
        else `left b
      | `right r -> `right r
