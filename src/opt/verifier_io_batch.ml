(* This implements a verifier that directly reads proof objects from a file.
   This version also implements batched reading for enhanced performance. 
   This does not appear in the paper, or in our proofs, and is only used for 
   experiments. *)

open Auth
open Hash
open Utils

let input = ref (open_in_bin "/dev/null")

let from_channel_with_string chan =
  let s = Bytes.create Marshal.header_size in
  really_input chan s 0 Marshal.header_size;
  let d = Marshal.data_size s 0 in
  let str = Bytes.create (Marshal.header_size + d) in
  Bytes.blit s 0 str 0 Marshal.header_size;
  really_input chan str Marshal.header_size d;
  Bytes.to_string str

module Verifier_io_batch : sig
  include AUTHENTIKIT with
  type 'a authenticated_computation = unit list -> 'a
  and type 'a auth = string
  val run : 'a authenticated_computation -> 'a
  val set_input : string -> unit
  val close_input : unit -> unit
end = struct
  type proof_val = proof_value
  type proof_state = unit list
  type 'a authenticated_computation = unit list -> 'a
  type 'a auth = string

  let set_input s = 
    close_in !input; input := open_in_bin s
  let close_input () = close_in !input; input := open_in_bin "/dev/null"
  let buf: 'a list ref = ref []

  let read () =
    if List.length !buf = 0 then
      buf := Marshal.from_string (from_channel_with_string !input) 0;
    let a, t = List.hd !buf, List.tl !buf in
    buf := t; a

  let return a = fun _ -> a

  let[@inline] bind c f = (f[@inlined]) (c [])

  module Authenticatable = struct
    include Authenticatable_marshal.Verifier
    let[@inline] auth =
      let[@inline] serialize x = Marshal.to_string x marshal_flags in
      let[@inline] deserialize s = Some (Marshal.from_string s 0) in
      { serialize; deserialize }

  end
  open Authenticatable

  let push_proof _ _ = []
  
  let pop_proof _ = 
    let s = from_channel_with_string !input in
    Some (Marshal.from_string s 0, [])

  let[@inline] auth evi a =
    hash (evi.serialize a)    

  let[@inline] unauth evi h _ =
    let p = read () in
    if hash p = h then 
      match evi.deserialize p with
      | Some a -> a
      | None -> failwith "Proof failure"
    else failwith "Proof failure"

  let run c =
    (* let pf = Marshal.from_string pf_s 0 in *)
    let a = c [] in
    a

end
