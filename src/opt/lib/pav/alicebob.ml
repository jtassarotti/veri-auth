open Advrpc
open Auditor
open Auditor_rpc
open Client
open Cryptoffi
open Ktcore
open Server
open Server_rpc
open Utils


type hist_entry = {
  is_reg: bool;
  pk: bytes
}


let alice_uid = 0
let bob_uid = 1

let rec loop_pending (cli: Client.client) (ep: int): blame =
  match self_mon cli with
  | `left b -> b
  | `right (ep0, don) ->
    if don then begin assert (ep0 = ep); blame_none end
    else loop_pending cli ep

let run_alice (cli: Client.client): hist_entry list blame_ret =
  match self_mon cli with
  | `left b -> `left b
  | `right (ep, is_insert) ->
    assert (not is_insert);
    assert (ep = 0);
    let hist = [{ is_reg = false; pk = emp_bytes }] in

    let rec aux i hist =
      if i = 20 then `right (List.rev hist)
      else
        let pk = secure_random_bytes 32 in
        Client.put cli pk;
        
        let err = loop_pending cli (List.length hist) in
        if err <> blame_none then `left err
        else
          let hist = { is_reg = true; pk = pk } :: hist in
          aux (i+1) hist
    in
    aux 0 hist

let run_bob (cli: Client.client): (int * hist_entry) blame_ret =
  Unix.sleepf (0.12);
  match Client.get cli alice_uid with
  | `left b -> `left b
  | `right (ep, is_reg, pk) -> `right (ep, { is_reg = is_reg; pk = pk })

let equal_hist (o0: hist_entry) (o1: hist_entry): bool =
  if o0.is_reg <> o1.is_reg then false
  else if o0.is_reg then Bytes.equal o0.pk o1.pk
  else true

let test_alice_bob (serv_addr: int64) (adtr_addr: int64): evid option blame_ret =
  print_endline "Creating new server";
  let serv, serv_sig_pk = Server.new_server () in
  let serv_rpc = new_rpc_server serv in
  serve serv_rpc serv_addr;
  Unix.sleepf (0.001);

  print_endline "Creating new auditor";
  match new_auditor serv_addr serv_sig_pk with
  | `left b -> `left b
  | `right (adtr, adtr_pk) ->
    let adtr_rpc = new_rpc_auditor adtr in
    Advrpc.serve adtr_rpc adtr_addr;
    Unix.sleepf (0.001);

    print_endline "Creating client alice";
    match new_client alice_uid serv_addr serv_sig_pk with
    | `left b -> `left b
    | `right alice ->

      print_endline "Creating client bob";
      match new_client bob_uid serv_addr serv_sig_pk with
      | `left b -> `left b
      | `right bob ->

        print_endline "Alice audit";
        let evid, b = Client.audit alice adtr_addr adtr_pk in
        if b <> blame_none then `left b else begin
          print_endline "Bob audit";
          let evid, b = Client.audit bob adtr_addr adtr_pk in
          if b <> blame_none then `left b else

            let alice_hist_br: hist_entry list blame_ret option ref = ref None in
            let bob_ret_br: (int * hist_entry) blame_ret option ref = ref None in

            let t1 = Thread.create (fun () ->
              alice_hist_br := Some (run_alice alice);
              ) ()
            in
            let t2 = Thread.create (fun () ->
              bob_ret_br := Some (run_bob bob);
              ) ()
            in

            Thread.join t1; Thread.join t2;
      
            match !alice_hist_br with
            | None -> failwith "alice thread returned without result"
            | Some `left b -> `left b
            | Some `right alice_hist ->
              match !bob_ret_br with
              | None -> failwith "alice thread returned without result"
              | Some `left b -> `left b
              | Some `right (bob_ep, bob_alice_pk) ->
                let adtr_cli = dial adtr_addr in
                let b = Auditor_rpc.call_update adtr_cli in
                if b <> blame_none then `left b else
                let evid, b = Client.audit alice adtr_addr adtr_pk in
                if b <> blame_none then `left b else
                let evid, b = Client.audit bob adtr_addr adtr_pk in
                if b <> blame_none then `left b else begin
                  assert (bob_ep < List.length alice_hist);
                  let alice_pk = List.nth alice_hist bob_ep in
                  if equal_hist alice_pk bob_alice_pk then
                    `right evid
                  else
                    `left blame_adtr_sig
                end
          end
