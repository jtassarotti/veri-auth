open Lwt.Infix
open Lwt.Syntax

let make_unique_addr () : int64 =
  let port = Int64.of_int (Random.int(4000) + 6000) in
  Int64.shift_left port 32

(* Address conversion (same bit layout as the Go code) *)
let addr_to_string (addr : int64) : string =
  let open Int64 in
  let a0 = to_int (logand addr 0xffL) in
  let addr = shift_right addr 8 in
  let a1 = to_int (logand addr 0xffL) in
  let addr = shift_right addr 8 in
  let a2 = to_int (logand addr 0xffL) in
  let addr = shift_right addr 8 in
  let a3 = to_int (logand addr 0xffL) in
  let addr = shift_right addr 8 in
  let port = to_int (logand addr 0xffffL) in
  Printf.sprintf "%d.%d.%d.%d:%d" a0 a1 a2 a3 port

(* Encoding helpers *)

let put_uint64_be n =
  let b = Bytes.create 8 in
  for i = 0 to 7 do
    let shift = 8 * (7 - i) in
    let v = Int64.(to_int (logand (shift_right_logical n shift) 0xffL)) in
    Bytes.set b i (Char.chr v)
  done;
  b

let get_uint64_be b =
  let acc = ref Int64.zero in
  for i = 0 to 7 do
    let v = Int64.of_int (Char.code (Bytes.get b i)) in
    acc := Int64.(logor (shift_left !acc 8) v)
  done;
  !acc

(* Low-level I/O *)

let rec lwt_write_all fd buf off len =
  if len = 0 then Lwt.return_unit
  else
    let* written = Lwt_unix.write fd buf off len in
    if written = 0 then Lwt.fail End_of_file
    else lwt_write_all fd buf (off + written) (len - written)

let rec lwt_read_exact fd buf off len =
  if len = 0 then Lwt.return_unit
  else
    let* got = Lwt_unix.read fd buf off len in
    if got = 0 then Lwt.fail End_of_file
    else lwt_read_exact fd buf (off + got) (len - got)

(* --- Conn --- *)

type conn = {
  fd : Lwt_unix.file_descr;
  send_mu : Lwt_mutex.t;
  recv_mu : Lwt_mutex.t;
}

let new_conn fd =
  { fd; send_mu = Lwt_mutex.create (); recv_mu = Lwt_mutex.create () }

let dial (addr : int64) : conn Lwt.t =
  let addr_str = addr_to_string addr in
  try%lwt
    let colon = String.index addr_str ':' in
    let host = String.sub addr_str 0 colon in
    let port = int_of_string (String.sub addr_str (colon + 1) (String.length addr_str - colon - 1)) in
    let* he = Lwt_unix.gethostbyname host in
    let sockaddr = Unix.ADDR_INET (he.Unix.h_addr_list.(0), port) in
    let fd = Lwt_unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
    let+ _ = Lwt_unix.connect fd sockaddr in
    new_conn fd
  with _ ->
    Lwt.fail_with "netffi: Dial err"

let conn_send (c : conn) (data : bytes) : bool Lwt.t =
  Lwt_mutex.with_lock c.send_mu (fun () ->
    let len = Int64.of_int (Bytes.length data) in
    let hdr = put_uint64_be len in
    try%lwt
      let* _ = lwt_write_all c.fd hdr 0 8 in
      let+ _ = lwt_write_all c.fd data 0 (Bytes.length data) in
      false
    with _ ->
      let+ _ = 
        try%lwt Lwt_unix.close c.fd
        with _ -> Lwt.return_unit
      in true)

let conn_receive (c : conn) : (bytes option) Lwt.t =
  Lwt_mutex.with_lock c.recv_mu (fun () ->
    let header = Bytes.create 8 in
    try%lwt
      lwt_read_exact c.fd header 0 8 >>= fun () ->
      let data_len = Int64.to_int (get_uint64_be header) in
      let data = Bytes.create data_len in
      lwt_read_exact c.fd data 0 data_len >|= fun () ->
      Some data
    with _ ->
      let+ _ = 
        try%lwt Lwt_unix.close c.fd
        with _ -> Lwt.return_unit
      in None)

(* --- Listener --- *)

type listener = { lfd : Lwt_unix.file_descr }

let listen (addr : int64) : listener Lwt.t =
  let addr_str = addr_to_string addr in
  try%lwt
    let colon = String.index addr_str ':' in
    let host = String.sub addr_str 0 colon in
    let port = int_of_string (String.sub addr_str (colon + 1) (String.length addr_str - colon - 1)) in
    let+ he = Lwt_unix.gethostbyname host in
    let sockaddr = Unix.ADDR_INET (he.Unix.h_addr_list.(0), port) in
    let lfd = Lwt_unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
    Lwt_unix.setsockopt lfd Unix.SO_REUSEADDR true;
    let _ = Lwt_unix.bind lfd sockaddr in
    Lwt_unix.listen lfd 10;
    { lfd }
  with _ ->
    Lwt.fail_with "netffi: Listen err"

let accept (l : listener) : conn Lwt.t =
  try%lwt
    let+ (fd, _) = Lwt_unix.accept l.lfd in
    new_conn fd
  with _ ->
    Lwt.fail_with "netffi: Accept err"
