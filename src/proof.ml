(* open Sha1 *)

type proof_value = string
type proof_stream = string list

(* let get_digest_string s = Ezjsonm.to_string (`A [s]) *)

let hash_json =
  let hash_algo s = Sha256.to_bin (Sha256.string s) in
  fun json_value ->
    let h = hash_algo json_value in
    (* print_string ("Hashing: " ^ json_value ^ "\n\n");
    print_string ("Hash:");
    print_string (h^"\n");
    print_string ("Hash:" ^ h^"\n"); *)
    h;;

hash_json ("")
