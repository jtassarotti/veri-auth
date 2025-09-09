open Vrf

let () =
  let (keys, pk) = get_keys () in
  print_endline "generated eys";
  let message = "aljs" in
  let hash, proof = randomize_string keys message in
  print_endline ("got hash "^hash);
  assert (verify_proof pk message proof);
  print_endline "verified"

