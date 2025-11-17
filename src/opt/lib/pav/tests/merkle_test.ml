open Pav
open Merkle
open Cryptoffi
open Utils


let prove_and_verify (m: map) (label: bytes) (exp_in_map: bool) (exp_val: bytes) =
  let opt_val, proof = prove m label in
  let hash = get_map_hash m in
  
  match opt_val with
  | None ->
    begin if exp_in_map then failwith "Key put in map, but not detected"
      else
        match verify_nonmemb label proof with
        | None -> failwith "Error in verify_nonmemb"
        | Some hash0 -> assert (Bytes.equal hash hash0)
    end
  | Some value ->
    if not exp_in_map then failwith "Key not in map, but detected"
    else if not (Bytes.equal value exp_val) then
      failwith "inconsistent value"
    else
      match verify_memb label value proof with
      | None -> failwith "Error in verify_memb"
      | Some hash0 -> assert (Bytes.equal hash hash0)
 
let test_get_recent () =
  print_endline "testing get recent";
  let m = empty_map () in
  
  let rec aux i =
    if i = 100000 then () else begin 
      (* print_endline ("i "^(string_of_int i)); *)

      let label = secure_random_bytes hash_len in
      let value = secure_random_bytes 4 in

      prove_and_verify m label false Bytes.empty;

      let l = Bytes.copy label in
      let v = Bytes.copy value in

      let _ = put m l v in
      (* print_child !(m.root); *)

      prove_and_verify m label true value;
      
      aux (i+1)
    end
  in
  aux 0


let test_map () =
  print_endline "testing map";
  let m = empty_map () in
  let bmap_init = BMap.empty in

  let rec aux i bmap =
    if i = 100000 then bmap else begin 
      (* print_endline ("i "^(string_of_int i)); *)

      let label = secure_random_bytes hash_len in
      let value = secure_random_bytes 4 in

      let l = Bytes.copy label in
      let v = Bytes.copy value in

      let _ = put m l v in
      (* print_child !(m.root); *)
      
      let v1 = Bytes.copy v in

      aux (i+1) (BMap.add label v1 bmap)
    end
  in
  let bmap = aux 0 bmap_init in

  BMap.iter (fun l v ->
    prove_and_verify m l true v
  ) bmap


let test_update () =
  print_endline "Testing update";
  let m = empty_map () in

  let rec aux i =
    if i = 100 then () else
      let l = secure_random_bytes hash_len in
      let v = secure_random_bytes 4 in

      let d_old = get_map_hash m in
      let p = put m l v in
      let d_new = get_map_hash m in

      match verify_update l v p with
      | None -> failwith "Error in verify_update"
      | Some (d_old0, d_new0) ->
        assert (Bytes.equal d_old d_old0);
        assert (Bytes.equal d_new d_new0);

        aux (i+1)
  in
  aux 0


let () =
  test_get_recent ();
  test_map ();
  test_update ()


