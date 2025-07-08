open Vrf

let () =
  let (keys, pk) = getKeys () in
  print_endline "generated eys";
  let message = "aljs" in
  let hash, proof = getProof keys message in
  print_endline ("got hash "^hash);
  assert (verifyProof pk message proof);
  print_endline "verified"

