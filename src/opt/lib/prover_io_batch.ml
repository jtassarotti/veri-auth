(* This implements a prover that directly writes proof objects to a file. This
   version also implements batched writing for enhanced performance. 
   This does not appear in the paper, or in our proofs, and is only used 
   for experiments. *)

open Auth
open Hash
open Utils

let output = ref (open_out_bin "/dev/null")

module Prover_io_batch : sig
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
  let buf: 'a list ref = ref []
  
  let write o =
    buf := (Obj.magic o)::!buf;
    if List.length !buf = 1000 then begin
      Marshal.to_channel !output (List.rev !buf) marshal_flags;
      buf := []
    end

  let get_hash (a, h) = h
  let[@inline] return a = fun _ -> a

  let[@inline] bind ma f = (f[@inlined]) (ma [])

  module Authenticatable = struct
    include Authenticatable_marshal.Prover
    let[@inline] auth =
      let[@inline] prepare (a, h) = h 
      and[@inline] serialize y = Marshal.to_string y marshal_flags
      in
      T {prepare; serialize }
      
  end
  open Authenticatable

  let push_proof prf x =
    Marshal.to_channel !output prf marshal_flags; x
  
  let pop_proof prf_state = None

  let[@inline] auth evi a =
    match evi with
    | T evi -> (a, hash (evi.serialize (evi.prepare a)))

  let[@inline] unauth evi (a, h) _ = 
    match evi with
    | T evi -> 
      write (evi.prepare a); a

  let[@inline] run m =
    let res = m [] in
    if List.length! buf > 0 then
      Marshal.to_channel !output (List.rev !buf) marshal_flags;
    buf := [];
    res
end
