open Pav
open Hashchain

let () =
  print_endline "Testing hashchain";
  let chain = new_hashchain () in
  let links: bytes array = Array.make 1001 Bytes.empty in
  Array.set links 0 (get_empty_link ());

  let p = prove chain 0 in
  let chain_head = Array.get links 0 in
  let verify_opt = verify chain_head p in
  match verify_opt with
  | None -> failwith "Null verification failed"
  | Some (new_len, new_val, new_link) ->
    assert (new_len = 0);
    assert (Bytes.length new_val = 0);
    assert (Bytes.equal chain_head new_link);

    let rec aux new_len =
      if new_len = 1000 then () else
      let new_val = Cryptoffi.secure_random_bytes Cryptoffi.hash_len in
      let new_link = append chain new_val in
      Array.set links new_len new_link;

      let prev_len = Cryptoffi.secure_random_int (new_len+1) in
      let proof0 = prove chain prev_len in
      let verify_opt = verify (Array.get links prev_len) proof0 in
      match verify_opt with
      | None -> failwith ("Verification1 failed at index "^(string_of_int new_len))
      | Some (ext_len0, new_val0, new_link0) ->
        assert (ext_len0 = new_len - prev_len);
        assert (ext_len0 != 0 || (Bytes.equal new_val0 Bytes.empty));
        assert (ext_len0 = 0 || (Bytes.equal new_val new_val0));
        assert (Bytes.equal new_link new_link0);

        let start_link, start_val = bootstrap chain in
        let verify_opt = verify start_link start_val in
        match verify_opt with
        | None -> failwith ("Verification2 failed at index "^(string_of_int new_len))
        | Some (ext_len1, new_val1, new_link1) ->
          assert (ext_len1 = 1);
          assert (Bytes.equal new_val new_val1);
          assert (Bytes.equal new_link new_link1);
          aux (new_len+1)
    in

    aux 1
