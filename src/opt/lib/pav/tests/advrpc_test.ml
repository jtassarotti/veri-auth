open Lwt.Infix
open Lwt.Syntax
open Pav
open Advrpc
open Byte_parser
open Utils

type args = {
  a : int64;
  b : int64
}

let multiply (args : args) : int64 =
  Int64.mul args.a args.b

let enc_args (args : args) : bytes =
  let b1 = write_int64 (Bytes.create 0) args.a in
  let b2 = write_int64 b1 args.b in
  b2

let dec_args (args : bytes) : args option =
  match read_int64 args with
  | None -> None
  | Some (a, args0) ->
    match read_int64 args0 with
    | None -> None
    | Some (b, args1) -> Some ({ a; b })

let enc_reply (reply : int64) : bytes =
  write_int64 (Bytes.create 0) reply

let dec_reply (reply : bytes) : int64 option = 
  match read_int64 reply with
  | None -> None
  | Some (out, reply0) ->
    if Bytes.length reply0 != 0 then None else
    Some out

let servStub (args : bytes) : bytes option =
  match dec_args args with
  | None -> None
  | Some args -> Some (enc_reply (multiply args))

let () =
  print_endline "running advrpc test";
  let h = IMap.singleton 2 servStub in
  let f_opt = IMap.find_opt 2 h in
  let s = new_server h in
  let addr = Netffi.make_unique_addr () in
  let _ = serve s addr in

  let c = dial addr in
  let args0 = { a = 7L; b = 8L } in
  let args1 = enc_args args0 in
  match call c 2 args1 with
  | None -> failwith "Error at call"
  | Some reply0 ->
    match dec_reply reply0 with
    | None -> failwith "Bad reply"
    | Some reply1 -> assert (reply1 = (Int64.mul 7L 8L))
  