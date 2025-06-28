From auth.typing Require Export types typing.
From auth.heap_lang.lib Require Export linked_list table set serialization.
From auth.examples Require Export authentikit authenticatable_base.

(** * Proof buffering with state and w/o re-deserialization using hetereogenous cache *)

(** type proof = string list *)

(** ** Verifier *)

(** type 'a auth = string *)
(** type 'a authenticated_computation = proof -> (proof * 'a) option *)
(** type 'a evidence = {serialize : 'a -> string; deserialize : string -> 'a} *)

Definition v_return : val := Λ: λ: "a" "prf", SOME ("prf", "a") .
Definition v_bind : val :=
  Λ: Λ: λ: "c" "f" "pf",
        match: "c" "pf" with
          NONE => NONE
        | SOME "x" =>
            let, ("pf'", "a") := "x" in
            "f" "a" "pf'"
        end.

Definition v_unauth: val :=
  λ: "cache", Λ: λ: "evi" "h" "prf",
      let, ("serialize", "deserialize") := "evi" in
      match: Table.lookup "h" "cache" with
        NONE =>
          match: list_head "prf" with
            NONE => NONE
          | SOME "p" =>
              if: Hash "p" = "h" then
                match: "deserialize" "p" with
                  NONE => NONE
                | SOME "a" =>
                    Table.insert "h" "a" "cache";;
                    let: "prf'" := list_tail "prf" in
                    SOME ("prf'", "a")
                end
              else NONE
          end
      | SOME "a" => SOME ("prf", "a")
      end.

Definition v_Authenticable : expr :=
  let: "cache" := Table.empty #() in
  (v_Auth_auth, v_Auth_mu, v_Auth_pair, v_Auth_sum, v_Auth_string, v_Auth_int, v_auth, v_unauth "cache").
Definition v_Authentikit : expr :=
  (v_return, v_bind, v_Authenticable).

(** val run : 'a authenticated_computation -> proof -> 'a *)
Definition v_run : val :=
  Λ: λ: "c" "prf",
    match: "c" "prf" with
      NONE => NONE
    | SOME "v" => SOME (Snd "v")
    end.

(** ** Prover  *)

(** type 'a auth = 'a * string *)
(** type 'a authenticated_computation = proph -> proof -> proof * 'a *)
(** type 'a evidence = 'a -> string *)

Definition p_return : val :=
  Λ: λ: "a" "p" "buf", ("buf", "a").
Definition p_bind : val :=
  Λ: Λ: λ: "c" "f" "p" "buf",
    let, ("buf'", "a") := "c" "p" "buf" in
    "f" "a" "p" "buf'".

Definition p_add_obj : val :=
  Λ: λ: "cache" "evi" "p" "ah" "prf",
    let, ("a", "h") := "ah" in
    let: "s" := "evi" "a" in
    resolve_proph: "p" to: (SOME "s");;
    let: "prf'" := "s" :: "prf" in
    "cache" <- set_add "h" (!"cache");;
    "prf'".

Definition p_unauth : val :=
  λ: "cache", Λ: λ: "evi" "ah" "p" "prf",
    let, ("a", "h") := "ah" in
    if: set_mem "h" !"cache" then
      ("prf", "a")
    else
      (p_add_obj #~ "cache" "evi" "p" "ah" "prf", "a").

(** val run : proph -> 'a authenticated_computation -> proof * 'a *)
Definition p_run : val :=
  Λ: λ: "p" "c",
    let, ("prf", "res") := "c" "p" [] in
    resolve_proph: "p" to: NONEV;;
    (list_rev "prf", "res").

Definition p_Authenticable : expr :=
  let: "cache" := ref (set_empty #()) in
  (p_Auth_auth, p_Auth_mu, p_Auth_pair, p_Auth_sum, p_Auth_string, p_Auth_int, p_auth, p_unauth "cache").
Definition p_Authentikit : expr :=
  (p_return, p_bind, p_Authenticable).
