open Cryptoffi

type hashchain = {
  mutable pred_last_link: bytes;
  mutable last_link: bytes;
  mutable vals: bytes
}

let get_next_link (prev_link: bytes) (next_val: bytes): bytes =
  let hr = write prev_link in
  let hr = sum hr next_val in
  encode_ctx hr

let append (c: hashchain) (v: bytes): bytes =
  assert (Bytes.length v = hash_len);
  c.pred_last_link <- c.last_link;
  c.last_link <- get_next_link c.last_link v;
  c.vals <- Bytes.cat c.vals v;
  c.last_link

let prove (c: hashchain) (prev_len: int): bytes =
  let start = prev_len * hash_len in
  Bytes.sub c.vals start ((Bytes.length c.vals) - start)
  |> Bytes.copy

let bootstrap (c: hashchain): bytes * bytes =
  let start = Bytes.length (c.vals) - hash_len in
  c.pred_last_link, Bytes.sub c.vals start hash_len |> Bytes.copy

let verify (prev_link: bytes) (proof: bytes): (int * bytes * bytes) option =
  let proof_len = Bytes.length proof in
  if proof_len mod hash_len != 0 then None else
  let ext_len = proof_len / hash_len in

  let rec aux i new_val new_link =
    if i = ext_len then (new_val, new_link) else
    let start = i * hash_len in
    let new_val = Bytes.sub proof start hash_len in
    let new_link = get_next_link new_link new_val in
    aux (i+1) new_val new_link
  in

  let new_val, new_link = aux 0 Bytes.empty prev_link in
  Some (ext_len, new_val, new_link)

let get_empty_link (): bytes = hash_bytes Bytes.empty

let new_hashchain (): hashchain = { 
    pred_last_link = Bytes.empty;
    last_link = get_empty_link ();
    vals = Bytes.empty
  }

