type proof_value = string
type proof_stream = string list

let hash =
  let hash_algo s = Sha256.to_bin (Sha256.string s) in
  fun json_value -> hash_algo json_value;;
