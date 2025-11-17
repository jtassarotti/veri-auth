open Netffi
open Lwt.Infix
open Lwt.Syntax
open Byte_parser
open Utils

type server = {
  handlers : (bytes -> bytes option) IMap.t
}

let handle (s : server) (c : conn) (rpcId : int) (data : bytes) =
  let f_opt = IMap.find_opt rpcId s.handlers in
  match f_opt with
  | None -> Lwt.return_unit
  | Some f ->
    let resp = 
      match f data with
      | None -> Bytes.empty
      | Some resp -> resp
    in
    let* b = conn_send c resp in
    Lwt.return_unit

let read (s : server) (c : conn) =
  let rec aux (s : server) (c : conn) =
    let* req_opt = conn_receive c in
    match req_opt with
    | None -> Lwt.return_unit
    | Some req ->
      match read_int req with
      | None -> aux s c
      | Some (rpcId, data) ->
        let _ = Lwt.async (fun () -> handle s c rpcId data) in
        aux s c
  in
  aux s c

let serve (s : server) (addr : int64) =
  Lwt_main.run begin
    let+ l = listen addr in
    let rec aux (l : listener) =
      let* c = accept l in
      let _ = Lwt.async (fun () -> read s c) in
      aux l
    in
    Lwt.async (fun () -> aux l)
  end

let new_server handlers : server = { handlers }


type client = {
  conn : conn
}

let dial (addr : int64) =
  Lwt_main.run begin
    let+ c = dial addr in { conn = c }
  end

let call (c : client) (rpcId : int) (args : bytes): bytes option =
  Lwt_main.run begin
    let req0 = Bytes.create (0) in
    let req1 = write_int req0 rpcId in
    let req2 = write_bytes req1 args in
    let* err0 = conn_send c.conn req2 in
    if err0 then Lwt.return None else
    conn_receive c.conn
  end
