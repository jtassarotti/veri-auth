type 'a evi_option = [`left | `right of 'a]

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
    val trio : 'a evidence -> 'b evidence -> 'c evidence -> ('a * 'b * 'c) evidence
    val quad : 'a evidence -> 'b evidence -> 'c evidence -> 'd evidence -> ('a * 'b * 'c * 'd) evidence
    (* val quint : 'a evidence -> 'b evidence -> 'c evidence -> 'd evidence -> 'e evidence -> ('a * 'b * 'c * 'd * 'e) evidence *)
    val sum : 'a evidence -> 'b evidence -> [`left of 'a | `right of 'b] evidence
    val option : 'a evidence -> [`left | `right of 'a] evidence
    val list : 'a evidence -> 'a list evidence
    val bool : bool evidence
    val string : string evidence
    val int : int evidence
  end

  val push_proof : proof_val -> proof_state -> proof_state
  val pop_proof : proof_state -> (proof_val * proof_state) option
  val auth : 'a Authenticatable.evidence -> 'a -> 'a auth
  val unauth : 'a Authenticatable.evidence -> 'a auth -> 'a authenticated_computation
end


module type AUTHENTIKIT2 = sig
  type proof_val
  type proof_state
  type 'a auth
  type 'a authenticated_computation
  val return : 'a -> 'a authenticated_computation
  val bind : 'a authenticated_computation -> ('a -> 'b authenticated_computation) ->
             'b authenticated_computation
               
  type random = int64

  module Authenticatable : sig
    type 'a evidence
    val auth : 'a auth evidence
    val pair : 'a evidence -> 'b evidence -> ('a * 'b) evidence
    val trio : 'a evidence -> 'b evidence -> 'c evidence -> ('a * 'b * 'c) evidence
    val quad : 'a evidence -> 'b evidence -> 'c evidence -> 'd evidence -> ('a * 'b * 'c * 'd) evidence
    (* val quint : 'a evidence -> 'b evidence -> 'c evidence -> 'd evidence -> 'e evidence -> ('a * 'b * 'c * 'd * 'e) evidence *)
    val sum : 'a evidence -> 'b evidence -> [`left of 'a | `right of 'b] evidence
    val option : 'a evidence -> 'a evi_option evidence
    val list : 'a evidence -> 'a list evidence
    val random : int64 evidence
    val bool : bool evidence
    val string : string evidence
    val int : int evidence
  end

  val push_proof : proof_val -> proof_state -> proof_state
  val pop_proof : proof_state -> (proof_val * proof_state) option
  val auth : 'a Authenticatable.evidence -> 'a -> 'a auth
  val unauth : 'a Authenticatable.evidence -> 'a auth -> 'a authenticated_computation

  val ( let* ) : 'a authenticated_computation -> ('a -> 'b authenticated_computation) ->
                  'b authenticated_computation
  val randomize : 'a Authenticatable.evidence -> 'a -> random authenticated_computation
  val eqauth : 'a auth -> 'a auth -> bool authenticated_computation
end