open Vrf
open Digestif
open Mirage_crypto_ec


type hash_ctx = SHA256.ctx
type hash_t = SHA256.t

let hash_len = SHA256.digest_size

let new_hasher (): hash_ctx =
  SHA256.init ()

let write (msg: bytes): hash_ctx =
  SHA256.feed_bytes (new_hasher ()) msg

let sum (ctx: hash_ctx) (msg: bytes): hash_ctx =
  SHA256.feed_bytes ctx msg

let encode_ctx (ctx: hash_ctx): bytes =
  let out = Bytes.create hash_len in
  SHA256.get_into_bytes ctx out; out

let get_hash (ctx: hash_ctx): hash_t =
  SHA256.get ctx

let hash_bytes (msg: bytes): bytes =
  write msg |> encode_ctx

let decode_hash (msg: bytes): hash_t option =
  Bytes.to_string msg |> SHA256.of_raw_string_opt

let equal_hash (hash1: hash_t) (hash2: hash_t): bool =
  SHA256.equal hash1 hash2


type sig_key = bytes

type priv_sig_key = Ed25519.priv
type pub_sig_key = Ed25519.pub

let sig_gen_keys (): priv_sig_key * pub_sig_key =
  Ed25519.generate ()

let sign (key: priv_sig_key) (m: bytes): bytes =
  Bytes.to_string m |> Ed25519.sign ~key:key |> Bytes.of_string

let sig_verify (key: pub_sig_key) (m: bytes) (sigs: bytes): bool =
  let m_s = Bytes.to_string m in
  let sigs_s = Bytes.to_string sigs in
  Ed25519.verify ~key:key sigs_s ~msg:m_s


type vrf_pk = bytes
type vrf_sk = {
  sk: bytes;
  pk: vrf_pk
}
type vrf_keys = {
  sk: vrf_sk;
  pk: vrf_pk
}

let vrf_hash_len = 64

let vrf_gen_key (): vrf_sk =
  let sk, pk = Vrf.get_keys() in
  { sk = sk; pk = pk }

let vrf_prove (sk: vrf_sk) (data: bytes): (bytes * bytes) =
  Vrf.prove sk.sk data

let vrf_evaluate (sk: vrf_sk) (data: bytes): bytes =
  Vrf.evaluate sk.sk data

let vrf_verify (pk: vrf_pk) (data: bytes) (proof: bytes) : bytes option =
  let ok, out = Vrf.verify_proof2 pk data proof in
  if ok then Some out else None


let secure_random_bytes size =
  let b = Bytes.create size in
  Mirage_crypto_rng.generate_into b size;
  b

let secure_random_int64 bound =
  let b = secure_random_bytes 8 in
  let n = Bytes.get_int64_le b 0 in
  Int64.rem n bound

let secure_random_int bound =
  let b = secure_random_bytes 2 in
  let n = Bytes.get_uint16_le b 0 in
  n mod bound


let () = Mirage_crypto_rng_unix.use_default ()
