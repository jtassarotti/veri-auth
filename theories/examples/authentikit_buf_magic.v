From auth.typing Require Export types typing.
From auth.heap_lang.lib Require Export list map set serialization.
From auth.examples Require Export authentikit authenticatable_base.

(** * Proof buffering, functional w/o re-deserialization using hetereogenous cache *)

(** To avoid re-deserialization on cache hits (as done in [authentikit_buf.v]), this implementation
    exploits a hetereogenous cache and stores the values directly. Authenticated values are not
    necessarily of the same type, so this requires the use of [Obj.magic] in OCaml. *)

(** Note that it is crucial for this implementation that our serialization mechanism is
    non-ambiguous: if, e.g., the string ["42"] is serialized to the same string as the integer [42],
    their authenticated values would be assigned the same key in the cache, which would not be sound
    (as the integer [42] could be cached as the string ["42"]). Notably, we crucial rely on
    uniqueness of serialization in the sense of the lemma [v_evi_type_ser_inj].

    Bob Atkey's serialization scheme *is* ambiguous. Our serialization scheme is non-ambiguous as
    the output of our serialization combinators is prefixed with a type tag. *)

(** type proof = string list *)

(** ** Verifier *)

(** type 'a auth = string *)
(** type proof_state = { pf_stream : proof; cache : Ezjsonm.value SMap.t }  *)
(** type 'a authenticated_computation = proof_state -> (proof_state * 'a) option *)
(** type 'a evidence = {serialize : 'a -> string; deserialize : string -> 'a} *)

Definition v_return : val := Λ: λ: "a" "pf", SOME ("pf", "a") .
Definition v_bind : val :=
  Λ: Λ: λ: "c" "f" "pf",
        match: "c" "pf" with
          NONE => NONE
        | SOME "x" =>
            let, ("pf'", "a") := "x" in
            "f" "a" "pf'"
        end.

Definition v_unauth : val :=
  Λ: λ: "evi" "h" "pf",
      let, ("serialize", "deserialize") := "evi" in
      let, ("prf", "cache") := "pf" in
      match: map_lookup "h" "cache" with
        NONE =>
          match: list_head "prf" with
            NONE => NONE
          | SOME "p" =>
              if: Hash "p" = "h" then
                match: "deserialize" "p" with
                  NONE => NONE
                | SOME "a" =>
                    (** This cache insertion requires [Obj.magic] in OCaml as the type of [a] varies *)
                    let: "pf'" := (list_tail "prf", map.map_insert "h" "a" "cache") in
                    SOME ("pf'", "a")
                end
              else NONE
          end
      | SOME "a" =>
          (** Here we now simply return the value from the cache  *)
          SOME ("pf", "a")
      end.

Definition v_Authenticable : val :=
  (v_Auth_auth, v_Auth_mu, v_Auth_pair, v_Auth_sum, v_Auth_string, v_Auth_int, v_auth, v_unauth).
Definition v_Authentikit : val := (v_return, v_bind, v_Authenticable).

(** val run : 'a authenticated_computation -> proof -> 'a *)
Definition v_run : val :=
  Λ: λ: "c" "prf",
    let: "init_state" := ("prf", map.map_empty #()) in
    match: "c" "init_state" with
      NONE => NONE
    | SOME "v" => SOME (Snd "v")
    end.

(** ** Prover  *)

(** type 'a auth = 'a * string *)
(** type proof_state = { pf_stream : proof; cache : SSet.t }  *)
(** type 'a authenticated_computation = proph -> proof_state -> proof_state * 'a *)
(** type 'a evidence = 'a -> string *)

Definition p_return : val :=
  Λ: λ: "a" "p" "buf", ("buf", "a").
Definition p_bind : val :=
  Λ: Λ: λ: "c" "f" "p" "buf",
    let, ("buf'", "a") := "c" "p" "buf" in
    "f" "a" "p" "buf'".

Definition p_add_obj : val :=
  Λ: λ: "evi" "p" "ah" "pf",
    let, ("a", "h") := "ah" in
    let, ("prf", "cache") := "pf" in
    let: "s" := "evi" "a" in
    resolve_proph: "p" to: (SOME "s");;
    let: "prf'" := "s" :: "prf" in
    let: "cache'" := set_add "h" "cache" in
    ("prf'", "cache'").

Definition p_unauth : val :=
  Λ: λ: "evi" "ah" "p" "pf",
    let, ("a", "h") := "ah" in
    let, ("prf", "cache") := "pf" in
    if: set_mem "h" "cache" then
      ("pf", "a")
    else
      (p_add_obj #~ "evi" "p" "ah" "pf", "a").

(** val run : proph -> 'a authenticated_computation -> proof * 'a *)
Definition p_run : val :=
  Λ: λ: "p" "c",
    let: "init_state" := ([], set_empty #()) in
    let, ("fin_state", "res") := "c" "p" "init_state" in
    let, ("prf", "cache") := "fin_state" in
    resolve_proph: "p" to: NONEV;;
    (list_rev "prf", "res").

Definition p_Authenticable : val :=
  (p_Auth_auth, p_Auth_mu, p_Auth_pair, p_Auth_sum, p_Auth_string, p_Auth_int, p_auth, p_unauth).
Definition p_Authentikit : val := (p_return, p_bind, p_Authenticable).
