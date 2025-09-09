From auth.heap_lang.lib Require Export list serialization.
From auth.examples Require Export authenticatable_base.

(** * Naïve functional list-based implementation based on Atkey's blog post *)

(** type proof = string list *)

(** ** Verifier *)

(** type 'a auth = string *)
(** type 'a authenticated_computation = proof -> (proof * 'a) option *)

Definition v_return : val := Λ: λ: "a" "proof", SOME ("proof", "a") .
Definition v_bind : val :=
  Λ: Λ: λ: "c" "f" "prfs",
        match: "c" "prfs" with
          NONE => NONE
        | SOME "x" =>
            let, ("prfs'", "a") := "x" in
            "f" "a" "prfs'"
        end.
Definition v_eqauth : val := Λ: λ: "a" "b" "proof", SOME ("proof", "a" = "b").

Definition v_unauth : val :=
  Λ: λ: "a_scheme" "h" "proof",
      match: list_head "proof" with
        NONE => NONE
      | SOME "p" =>
          if: Hash "p" = "h" then
            match: Snd "a_scheme" "p" with
              NONE => NONE
            | SOME "a" => SOME (list_tail "proof", "a")
            end
          else NONE
      end.

Definition v_Authenticable : val :=
  (v_Auth_auth, v_Auth_mu, v_Auth_pair, v_Auth_sum, v_Auth_string, v_Auth_int, v_auth, v_unauth).
Definition v_Authentikit : val := (v_return, v_bind, v_Authenticable).
Definition v_Authentikit_eq : val := (v_return, v_bind, v_eqauth, v_Authenticable).

(** val run : 'a authenticated_computation -> proof -> 'a *)
Definition v_run : val :=
  Λ: λ: "c" "prf",
    match: "c" "prf" with
      NONE => NONE
    | SOME "v" => SOME (Snd "v")
    end.

(** ** Prover  *)

(** type 'a auth = 'a * string *)
(** type 'a authenticated_computation = proph -> unit -> proof * 'a *)

Definition p_return : val :=
  Λ: λ: "a" "p" <>, ([], "a").
Definition p_bind : val :=
  Λ: Λ: λ: "c" "f" "p" <>,
    let, ("prf", "a") := "c" "p" #() in
    let, ("prf'", "b") := "f" "a" "p" #() in
    ("prf" @@ "prf'", "b")%E.
Definition p_eqauth : val :=
  Λ: λ: "ah" "bh" "proof" <>,
      let, ("a", "ha") := "ah" in
      let, ("b", "hb") := "bh" in
      ([], "ha" = "hb").

Definition p_unauth : val :=
  Λ: λ: "serializer" "ah" "p" <>,
     let, ("a", "h") := "ah" in
     let: "s" := "serializer" "a" in
     resolve_proph: "p" to: (SOME "s");;
     (["s"], "a").

(** val run : proph -> 'a authenticated_computation -> proof * 'a *)
Definition p_run : val :=
  Λ: λ: "p" "c",
     let: "r" := "c" "p" #() in
     resolve_proph: "p" to: NONEV;;
     "r".

Definition p_Authenticable : val :=
  (p_Auth_auth, p_Auth_mu, p_Auth_pair, p_Auth_sum, p_Auth_string, p_Auth_int, p_auth, p_unauth).
Definition p_Authentikit : val := (p_return, p_bind, p_Authenticable).
Definition p_Authentikit_eq : val := (p_return, p_bind, p_eqauth, p_Authenticable).
