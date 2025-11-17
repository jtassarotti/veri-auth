open Lwt.Infix
open Lwt.Syntax
open Pav.Netffi

let () =
  print_endline "running netffi test";
  Lwt_main.run begin
    let addr = make_unique_addr () in
    let* l = listen addr in

    let d0 = Char.chr 1 |> Bytes.make 2 in
    Char.chr 2 |> Bytes.set d0 1;
    let* c0 = dial addr in
    let* err0 = conn_send c0 d0 in
    assert (not err0);

    let* c1 = accept l in
    let+ d1_opt = conn_receive c1 in
    match d1_opt with
    | None -> failwith ("error in receive")
    | Some d1 -> assert (Bytes.equal d0 d1)
  end