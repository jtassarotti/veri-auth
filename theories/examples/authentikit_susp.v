From auth.typing Require Export types typing.
From auth.heap_lang.lib Require Export list map set serialization.
From auth.examples Require Export authentikit authenticatable_base_susp.

(** * Proof suspension *)

(** ** Verifier  *)

(* type proof_val = string *)
(* type type_finish = unit -> unit *)
(* type proof_state = { pf_stream: string list; counter : int } *)
(* type 'a authenticated_computation = proof_state -> proof_state * 'a *)
(* type suspension = | Tag of int | Hash of string *)
(* type 'a auth = | Shallow of string | Suspension of suspension ref *)

Definition v_return : val := Λ: λ: "a" "pf", SOME ("pf", "a") .
Definition v_bind : val :=
  Λ: Λ: λ: "c" "f" "pf",
        match: "c" "pf" with
          NONE => NONE
        | SOME "x" =>
            let, ("pf'", "a") := "x" in
            "f" "a" "pf'"
        end.

Definition v_auth : val :=
  Λ: λ: "evi" "a",
      let, ("serialize", "deserialize", "count") := "evi" in
      InjL (Hash ("serialize" "a")).

Definition v_unauth : val :=
  λ: "susp_table", Λ: λ: "evi" "a" "proof",
      match: list_head "proof" with
        NONE => NONE
      | SOME "p" =>
          let, ("pf_stream", "counter") := "proof" in
          let: "id" := "counter" in
          let, ("serialize", "deserialize", "count") := "evi" in
          match: "deserialize" "id" "p" with
            NONE => NONE
          | SOME "x" =>
              let: "nchild" := "count" "p" in
              let: "finish" :=
                λ: <>,
                  let: "y" := "serialize" "x" in
                  match: "a" with
                    InjL "h" =>
                      if: Hash "y" = "h" then SOMEV #()
                      else NONEV
                  | InjR "susp" =>
                      match: !"susp" with
                        InjL "h" =>
                          if: Hash "y" = "h" then SOMEV #()
                          else NONEV
                      | InjR "pid" =>
                          let, ("ctr", "finish") :=
                            map.map_lookup "pid" (!"susp_table")
                          in
                          if: "ctr" = #1 then
                            "susp_table" <- map.map_remove "pid" (!"susp_table");;
                            "susp" <- InjR (Hash "y");;
                            "finish" #()
                          else
                            "susp" <- InjR (Hash "y");;
                            "susp_table" <- map.map_insert "pid" ("ctr" - #1, "finish") (!"susp_table")
                      end
                  end
              in
              (if: "nchild" = #0 then
                 "finish" #()
               else
                 "susp_table" <- map.map_insert "pid" ("nchild", "finish") (!"susp_table"));;
              SOME ((list_tail "proof", "id" + #1), "x")
          end
      end.

Definition v_run : val :=
  Λ: λ: "c" "pf",
      let: "init_state" := ("pf", #0) in
      match: "c" "init_state" with
        NONE => NONE
      | SOME "res" => SOME (Snd "res")
      end.

Definition v_Authenticable : expr :=
  let: "init_susp" := map.map_empty #() in
  (v_Auth_auth, v_Auth_mu, v_Auth_pair, v_Auth_sum, v_Auth_string, v_Auth_int, v_auth, v_unauth "init_susp").
Definition v_Authentikit : expr := (v_return, v_bind, v_Authenticable).

(** ** Prover  *)

(* type proof_val = string *)
(* type proof_state = { pf_stream : string list; buffer : (unit -> string) list } *)
(* Only composite objects can be of variant Merkle (InjLV). *)
(* Any thing that the client may have will be of variant MerkleSusp (InjRV). *)
(* type 'a auth = | Merkle of 'a * string | MerkleSusp of bool ref * 'a * string *)
(* type 'a authenticated_computation = proof_state -> (proof_state * 'a) *)

Definition p_return : val :=
  Λ: λ: "a" "p" "buf", ("buf", "a").

Definition p_bind : val :=
  Λ: Λ: λ: "c" "f" "p" "buf",
    let, ("buf'", "a") := "c" "p" "buf" in
    "f" "a" "p" "buf'".

Definition p_auth : val :=
  Λ: λ: "evi" "a",
      let, ("serialize", "suspend", "unsuspend") := "evi" in
      let: "unsusp_a" := "unsuspend" "a" in
      InjL (ref #true, "unsusp_a", Hash ("serialize" "unsusp_a")).

Definition p_unauth : val :=
  Λ: λ: "evi" "a" "prf_state",
      let, ("pf_stream", "buffer") := "prf_state" in
      let, ("serialize", "suspend", "unsuspend") := "evi" in
      let: "un_a" :=
        match: "a" with
          InjL "susp_data" =>
            let, ("b", "a", <>) := "susp_data" in
            "b" <- #false;; "a"
        | InjR "data" =>
            let, ("a", "<>") := "data" in "a"
        end
      in
      let: "susp_un_a" := "suspend" "un_a" in
      let: "finish" := λ: <>,"serialize" "susp_un_a" in
      let: "prf_state'" := ("pf_stream", "finish" :: "buffer") in
      ("prf_state'", "susp_un_a").

Definition flush_buf_stream : val :=
  rec: "aux" "buffer" "pf_stream" :=
      match: list_head "buffer" with
        NONE => "pf_stream"
      | SOME "f" =>
          "aux" (list_tail "buffer") ("f" #() :: "pf_stream")
      end.

Definition p_run : val :=
  Λ: λ: "p" "m",
      let: "init_state" := ([], []) in
      let, ("fin_state", "res") := "m" "init_state" in
      let, ("pf_stream", "buffer") := "fin_state" in
      let: "pf_stream'" := flush_buf_stream "buffer" in
      let: "pf_stream" := (list_rev "pf_stream") @@ "pf_stream'" in
      ("pf_stream", "res").

Definition p_Authenticatable : val :=
  (p_Auth_auth, p_Auth_mu, p_Auth_pair, p_Auth_sum, p_Auth_string, p_Auth_int, p_auth, p_unauth).
Definition p_Authentikit : val := (p_return, p_bind, p_Authenticatable).
