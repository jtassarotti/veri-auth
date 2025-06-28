(* This implements the Stateful Buffering optimization for the verifier as specified in 
   Section 6 of the paper. *)

open Auth
open Hash
open Utils

module Verifier_buf_magic_state : sig
  include AUTHENTIKIT with
  type 'a auth = string
  val run : 'a authenticated_computation -> proof_stream -> 'a option
end = struct
  type proof_val = proof_value
  type proof_state = proof_stream
  type 'a auth = string
  type 'a authenticated_computation = proof_state -> (proof_state * 'a) option

  let cache: string SMap.t ref = ref (map_empty ())

  let return a prf = Some (prf, a)

  let bind c f pf =
    match c pf with
    | None -> None
    | Some x ->
      let (pf', a) = x in 
      f a pf'

  module Authenticatable = struct
    include Authenticatable_base.Verifier
  end
  open Authenticatable

  let push_proof pf prf = pf :: prf

  let pop_proof prf = 
    match list_head prf with
    | None -> None
    | Some h -> Some (h, list_tail prf)

  let auth evi a =
    hash (evi.serialize a)

  let unauth evi h prf =
    let serialize, deserialize = evi.serialize, evi.deserialize in
    match Obj.magic (map_lookup h (!cache)) with
    | None ->
      begin match list_head prf with
      | None -> None
      | Some p ->
        if hash p = h then
          begin match deserialize p with
          | None -> None
          | Some a -> 
            cache := SMap.add h (Obj.magic a) (!cache);
            let prf' = list_tail prf in
            Some (prf', a)
          end
        else None
      end
    | Some a -> Some (prf, a)

  let run c pf =
    cache := map_empty ();
    match (c pf) with
    | Some v -> Some (snd v)
    | None -> None

end
