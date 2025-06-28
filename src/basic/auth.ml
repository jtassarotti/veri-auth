(** The Authentikit module type. *)
module type AUTHENTIKIT = sig
  type 'a auth
  type 'a authenticated_computation
  
  val return : 'a -> 'a authenticated_computation
  val bind : 'a authenticated_computation -> ('a -> 'b authenticated_computation) ->
             'b authenticated_computation
               
  module Authenticatable : sig
    type 'a evidence
    val auth : 'a auth evidence
    val pair : 'a evidence -> 'b evidence -> ('a * 'b) evidence
    val sum : 'a evidence -> 'b evidence -> [`left of 'a | `right of 'b] evidence
    val bool : bool evidence
    val string : string evidence
    val int : int evidence
  end

  val auth : 'a Authenticatable.evidence -> 'a -> 'a auth
  val unauth : 'a Authenticatable.evidence -> 'a auth -> 'a authenticated_computation

  (* push_proof and pop_proof are only required for generic hand-optimized
     implementations and can otherwise be ignored. *)
  type proof_val
  type proof_state
  
  val push_proof : proof_val -> proof_state -> proof_state
  val pop_proof : proof_state -> (proof_val * proof_state) option
end
