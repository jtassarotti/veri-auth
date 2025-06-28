(* Signature of the Authentikit module type. *)

module type AUTHENTIKIT = sig
  type proof_val
  type proof_state
  type 'a auth
  type 'a authenticated_computation
  val return : 'a -> 'a authenticated_computation
  val bind : 'a authenticated_computation -> ('a -> 'b authenticated_computation) ->
             'b authenticated_computation
               

  module Authenticatable : sig
    type 'a evidence
    val auth : 'a auth evidence
    val pair : 'a evidence -> 'b evidence -> ('a * 'b) evidence
    (* We don't include trio and quad in our proofs. But they should follow
       similarly as the proofs for pair. *)
    val trio : 'a evidence -> 'b evidence -> 'c evidence -> ('a * 'b * 'c) evidence
    val quad : 'a evidence -> 'b evidence -> 'c evidence -> 'd evidence -> ('a * 'b * 'c * 'd) evidence
    val sum : 'a evidence -> 'b evidence -> [`left of 'a | `right of 'b] evidence
    val bool : bool evidence
    val string : string evidence
    val int : int evidence
  end

  (* push_proof and pop_proof are only required for hand-optimized functions.
     However, our proofs only concern with Proof Accumulator version
     of Authentikit, and hence, these functions don't appear in the proof. *)
  val push_proof : proof_val -> proof_state -> proof_state
  val pop_proof : proof_state -> (proof_val * proof_state) option
  val auth : 'a Authenticatable.evidence -> 'a -> 'a auth
  val unauth : 'a Authenticatable.evidence -> 'a auth -> 'a authenticated_computation
end
