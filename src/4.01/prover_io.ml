open Auth
open Hash
open Utils

let output = ref (open_out_bin "/dev/null")

module Prover_io : sig
  include AUTHENTIKIT with
  type 'a authenticated_computation = unit list -> 'a
  val get_hash : 'a auth -> string
  val run : 'a authenticated_computation -> 'a
  val set_output : string -> unit
  val close_output : unit -> unit
end = struct
  type proof_val = proof_value
  type proof_state = unit list
  type 'a auth = 'a * string
  type 'a authenticated_computation = proof_state -> 'a
  let set_output s = 
    close_out !output; output := open_out_bin s
  let close_output () = close_out !output; output := open_out_bin "/dev/null"
  let get_hash (a, h) = h
  let return a = fun _ -> a

  let bind ma f = f (ma [])
    (* let run = 
      fun buf_state ->
        let (buf_state', a) = (ma.run[@inlined]) buf_state in
        ((f[@inlined]) a).run buf_state'
    in { run } *)

  module Authenticatable = struct
    include Authenticatable_marshal.Prover
    let auth =
      let prepare (a, h) = h 
      and serialize y = Marshal.to_string y marshal_flags
      in
      T {prepare; serialize }
      
  end
  open Authenticatable

  let push_proof prf x =
    Marshal.to_channel !output prf marshal_flags; x
  
  let pop_proof prf_state = None

  let auth evi a =
    match evi with
    | T evi -> (a, hash (evi.serialize (evi.prepare a)))

  let unauth evi (a, h) _ = 
    match evi with
    | T evi -> 
      Marshal.to_channel !output (evi.prepare a) marshal_flags;
      a
    (* let run = fun buf -> ((evi.serialize a) :: buf, a) in
    { run } *)

  let run m =
    (* print_string "prover run"; print_newline (); *)
    let res = m [] in
    (* let pf_s = Marshal.to_string (List.rev pf) marshal_flags in *)
    (* print_string "prover run done"; print_newline (); *)
    res
end
