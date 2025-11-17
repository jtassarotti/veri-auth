open Vrf

let () =
  let (keys, pk) = get_keys () in
  print_endline "generated eys";
  let message = "aljs" |> Bytes.of_string in
  let hash, proof = prove keys message in
  print_endline ("got hash "^(Bytes.unsafe_to_string hash));
  assert (verify_proof pk message proof hash);
  print_endline "verified"

