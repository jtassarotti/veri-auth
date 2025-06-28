open Auth
open Proof
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

module Verifier_io : sig
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

  let return a = fun _ -> a

  let bind c f = f (c [])

  module Authenticatable = struct
    include Authenticatable_marshal_401.Verifier
    let auth =
      let serialize x = Marshal.to_string x marshal_flags in
      let deserialize s = Some (Marshal.from_string s 0) in
      { serialize; deserialize }

  end
  open Authenticatable

  let push_proof _ _ = []
  
  let pop_proof _ = 
    let s = from_channel_with_string !input in
    Some (Marshal.from_string s 0, [])

  let auth evi a =
    hash_json (evi.serialize a)    

  let unauth evi h _ =
    let p = from_channel_with_string !input in
    if hash_json p = h then 
      match evi.deserialize p with
      | Some a -> a
      | None -> failwith "Proof failure"
    else failwith "Proof failure"

  let run c =
    (* let pf = Marshal.from_string pf_s 0 in *)
    let a = c [] in
    a

end
