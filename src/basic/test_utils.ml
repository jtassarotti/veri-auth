open Utils

let set_default_seed () =
  Random.set_state (Random.State.make ([|1|]))

let random_even () =
  Random.int(50000000) * 2

let random_odd () =
  Random.int(50000000) * 2 + 1

let print_opt_string r =
  match r with
  | None -> print_string "None"
  | Some s -> print_string ("Some " ^ s)

let print_prover_res s =
  print_string "Result: "; print_opt_string s

let print_verifier_res s =
  match s with
  | None -> print_string "Proof failure"
  | Some s ->
    print_string "Verifier Result: "; print_opt_string s

let equal_res pres vres =
  match vres with
  | `Ok (_, v) -> pres = v
  | _ -> false

let print_proof_size proof =
  print_string "Proof stream (every proof object appears in different lines. 
    Some proof objects might have a line break in them):\n";
  proof
  |> List.map (fun s -> print_string (s^"\n"); String.length s)
  |> List.fold_left (+) 0
  |> Printf.printf "(pf size: %d)"

(* Test similar to in Lambda auth paper *)
let random_alpha_char () =
  Char.chr (97 + Random.int 26)

let random_string len =
  let s = BytesLabels.create len in
  for i = 0 to len -1 do BytesLabels.set s i (random_alpha_char ()) done;
  BytesLabels.to_string s;;

let random_leaves num len =
  let rec go num acc =
    match num with
    | 0 -> acc
    | _ -> go (num - 1) (random_string len :: acc)
  in
  go num []
;;

let random_key_vals num len =
  let rec go num acc =
    match num with
    | 0 -> acc
    | _ -> go (num-1) ((num, random_string len) :: acc)
  in
  go num [] 
  |> List.sort (fun (_, a) (_, b) -> String.compare a b)
;;

let random_odd_key_vals num =
  let rec go num acc1 acc2 =
    match num with
    | 0 -> (acc1, acc2)
    | _ -> 
      let a = random_odd () in
      go (num - 1) (a::acc1) (string_of_int a::acc2)
  in
  go num [] []
;;

let random_even_key_vals num =
  let rec go num acc1 acc2 =
    match num with
    | 0 -> (acc1, acc2)
    | _ -> 
      let a = random_even () in
      go (num-1) (a::acc1) (string_of_int a::acc2)
  in
  go num [] []
;;

let random_keys num =
  let rec go num acc =
    match num with
    | 0 -> acc
    | _ -> 
      let n = random_odd () in
      go (num-1) (n :: acc)
  in
  go num []


