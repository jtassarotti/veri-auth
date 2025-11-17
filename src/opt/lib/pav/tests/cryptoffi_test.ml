open Pav
open Cryptoffi

let fuzz_bytes b =
  Bytes.map (fun chr -> let i = Char.code chr in Char.chr (255-i)) b


let test_hash () =
  print_endline "testing hashing";
  let d1 = Bytes.of_string "d1" in
  let hc1 = write d1 in
  let h1 = get_hash hc1 in
  let hb1 = encode_ctx hc1 in
  let hc2 = write d1 in
  let h2 = get_hash hc2 in
  assert (equal_hash h1 h2);
  assert (Bytes.length hb1 = hash_len);

  let d2 = Bytes.of_string "d2" in
  let hc3 = write d2 in
  let h3 = get_hash hc3 in
  assert (equal_hash h1 h3 = false)

let test_sig () =
  print_endline "testing signatures";
  let d = Bytes.of_string "d" in
  let sk, pk = sig_gen_keys () in
  let sigs = sign sk d in
  assert (sig_verify pk d sigs);

  let d1 = Bytes.of_string "d1" in
  assert (sig_verify pk d1 sigs = false);

  let _, pk2 = sig_gen_keys () in
  assert (sig_verify pk2 d sigs = false);

  let sigs2 = fuzz_bytes sigs in
  assert (sig_verify pk d sigs2 = false)

let test_vrf () =
  print_endline "testing vrf";
  let sk0 = vrf_gen_key () in
  let pk0 = sk0.pk in
  let d0 = Bytes.of_string "d0" in
  let o0, p = vrf_prove sk0 d0 in
  assert (Bytes.length o0 = vrf_hash_len);
  let o0_v_opt = vrf_verify pk0 d0 p in
  match o0_v_opt with 
  | None -> failwith "verification failed"
  | Some o0_v ->
    assert (Bytes.equal o0 o0_v);

    let o1, _ = vrf_prove sk0 d0 in
    assert (Bytes.equal o0 o1);

    let d1 = Bytes.of_string "d1" in
    let o2, _ = vrf_prove sk0 d1 in
    assert (Bytes.equal o0 o2 = false);

    let sk1 = vrf_gen_key () in
    let pk1 = sk1.pk in
    let o2_v_opt = vrf_verify pk1 d0 p in
    match o2_v_opt with
    | Some _ -> failwith "shouldn't have verified, bad key"
    | None -> ()


let () =
  test_hash (); 
  test_sig ();
  test_vrf ()



