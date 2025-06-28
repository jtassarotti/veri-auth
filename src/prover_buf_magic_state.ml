open Auth
open Proof
open Utils

module SSet = Set.Make(struct type t = string let compare : string -> string -> int = compare end)

module Prover_buf_magic_state : sig
  include AUTHENTIKIT
  val get_hash : 'a auth -> string
  val run : 'a authenticated_computation -> (string * 'a)
end = struct
  let cache: SSet.t ref = ref SSet.empty
  type proof_val = proof_value
  type proof_state = proof_stream
  type 'a auth = 'a * string
  type 'a authenticated_computation = proof_state -> (proof_state * 'a)
  let get_hash (a, h) = h
  let return a buf = (buf, a)
  let bind ma f =
    fun buf ->
    let (buf', a) = ma buf in
    f a buf'

  module Authenticatable = struct
    include Authenticatable_base
    let auth =
      let serialize (a, h) = h 
      and deserialize _ = None
      in
      {serialize; deserialize }
      
  end
  open Authenticatable

  let push_proof prf prf_state = prf :: prf_state
  
  let pop_proof prf_state = 
    match List.nth_opt prf_state 0 with
    | None -> None
    | Some h -> Some (h, List.tl prf_state)

  let auth evi a =
    (a, hash_json (evi.serialize a))

  let add_obj evi (a, h) buf =
    cache := SSet.add h (!cache);
    evi.serialize a :: buf

  let unauth evi (a, h) buf =
    if SSet.mem h !cache then
      (buf, a)
    else
      (add_obj evi (a, h) buf, a)

  let run m =
    cache := SSet.empty;
    let pf, res = m [] in
    let pf_s = Marshal.to_string (List.rev pf) marshal_flags in
    (* print_string "prover run done"; print_newline (); *)
    (pf_s, res)

end
                          
