(* Here, we call the library that implements cryptographic operations. *)

type proof_value = string
type proof_stream = string list

let hash_size = 32

let hash =
  let hash_algo s = Sha256.to_bin (Sha256.string s) in
  fun json_value -> hash_algo json_value;;

hash ("")
