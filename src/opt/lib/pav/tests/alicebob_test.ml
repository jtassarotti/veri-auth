open Pav
open Alicebob
open Ktcore
open Netffi

let test_alicebob () =
  match test_alice_bob (make_unique_addr ()) (make_unique_addr ()) with
  | `left b -> print_int b; failwith "Error"
  | _ -> ()

let () =
  test_alicebob ()