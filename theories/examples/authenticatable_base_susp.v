From auth.heap_lang.lib Require Export serialization.
From auth.typing Require Export types typing.
From auth.prelude Require Import strings.

Definition int_count : val :=
  λ: <>, #0.
Definition string_count : val := int_count.
Definition prod_count : val :=
  λ: "countA" "countB" "v",
    let, ("vA", "vB") := "v" in
    "countA" "vA" + "countB" "vB".
Definition sum_count : val :=
  λ: "countA" "countB" "v",
    match: "v" with
      InjL "vA" => "countA" "vA"
    | InjR "vB" => "countB" "vB"
    end.

Definition auth_scheme : expr := sum_scheme string_scheme string_scheme.

Definition auth_ser_v : val :=
  λ: "v",
    match: "v" with
      InjL "h" => string_ser "h"
    | InjR "susp" =>
        match: !"susp" with
          InjR "h" => string_ser "h"
        | InjL <> => NONEV
        end
    end.

Definition auth_deser_v : val :=
  λ: "s" "pid",
    match: (Snd auth_scheme) "s" with
      NONE => NONE
    | SOME "v" =>
        match: "v" with
          InjL <> => SOME (InjR (ref (InjL "pid")))
        | InjR "h" => SOME (InjL "h")
        end
    end.

Definition auth_count : val :=
  λ: "v",
    match: "v" with
      InjL <> => #1
    | InjR <> => #0
    end.

(** type 'a evidence = {serialize : 'a -> string; deserialize : string -> 'a; count : 'a -> int} *)
Definition v_Auth_auth : val :=
  Λ: (auth_ser_v, auth_deser_v, auth_count).    
Definition v_Auth_mu : val :=
  Λ: λ: "s",
      let, ("ser", "deser", "count") := "s" in
      let: "ser" := λ: "x", "ser" "x" in
      let: "deser" := λ: "pid" "x", "deser" "pid" "x" in
      let: "count" := λ: "x", "count" "x" in
      ("ser", "deser", "count").
Definition v_Auth_pair : val :=
  Λ: Λ: λ: "A" "B",
        let, ("ser_A", "deser_A", "count_A") := "A" in
        let, ("ser_B", "deser_B", "count_B") := "B" in
        let: "ser" := prod_ser "ser_A" "ser_B" in
        let: "deser" := λ: "pid", prod_deser ("deser_A" "pid") ("deser_B" "pid") in
        let: "count" := prod_count "count_A" "count_B" in
        ("ser", "deser", "count").
Definition v_Auth_sum : val :=
  Λ: Λ: λ: "A" "B",
        let, ("ser_A", "deser_A", "count_A") := "A" in
        let, ("ser_B", "deser_B", "count_B") := "B" in
        let: "ser" := sum_ser "ser_A" "ser_B" in
        let: "deser" := λ: "pid", sum_deser ("deser_A" "pid") ("deser_B" "pid") in
        let: "count" := sum_count "count_A" "count_B" in
        ("ser", "deser", "count").
Definition v_Auth_string : val :=
  (string_ser, λ: <>, string_deser, string_count).
Definition v_Auth_int : val :=
  (int_ser, λ: <>, int_deser, int_count).

Definition auth_ser_p : val :=
  λ: "a",
    let: "a_ser" := Fst auth_scheme in
    match: "a" with
      InjL "d" =>
        let, ("a", "h") := "d" in
        "a_ser" (InjR "h")
    | InjR "d" =>
        let, ("b", <>, "a", "h") := "d" in
        if: !"b" then "a_ser" (InjL #"")
        else "a_ser" (InjR "h")
    end.

Definition auth_suspend_p : val :=
  λ: "a",
    match: "a" with
      InjL "d" =>
        let, ("a", "h") := "d" in
        InjR (ref #false, ref #false, "a", "h")
    | InjR <> => NONE
    end.

Definition auth_unsuspend_p : val :=
  λ: "a",
    match: "a" with
      InjL "d" => NONE
    | InjR "d" =>
        let, ("b", "r", "a", "h") := "d" in
        "r" <- #true;;
        InjL ("a", "h")
    end.

(** type 'a evidence = 'a -> string; suspend : 'a -> 'a; unsuspend : 'a -> 'a *)
Definition p_Auth_auth : val :=
  Λ: (auth_ser_p, auth_suspend_p, auth_unsuspend_p).
Definition p_Auth_mu : val :=
  Λ: λ: "s",
      let, ("ser", "suspend", "unsuspend") := "s" in
      let: "ser" := 
        λ: "a", rec_fold "ser" "a"
      in
      let: "suspend" :=
        λ: "a", rec_fold "suspend" "a"
      in
      let: "unsuspend" :=
        λ: "a", rec_fold "unsuspend" "a"
      in
      ("ser", "suspend", "unsuspend").
Definition p_Auth_pair : val :=
  Λ: Λ: λ: "A" "B",
        let, ("ser_A", "suspend_A", "unsuspend_A") := "A" in
        let, ("ser_B", "suspend_B", "unsuspend_B") := "B" in
        let: "ser" := prod_ser "ser_A" "ser_B" in
        let: "suspend" :=
          λ: "a",
            let, ("a", "b") := "a" in
            ("suspend_A" "a", "suspend_B" "b")
        in
        let: "unsuspend" :=
          λ: "a",
            let, ("a", "b") := "a" in
            ("unsuspend_A" "a", "unsuspend_B" "b")
        in
        ("ser", "suspend", "unsuspend").
Definition p_Auth_sum : val :=
  Λ: Λ: λ: "A" "B",
        let, ("ser_A", "suspend_A", "unsuspend_A") := "A" in
        let, ("ser_B", "suspend_B", "unsuspend_B") := "B" in
        let: "ser" := sum_ser "ser_A" "ser_B" in
        let: "suspend" :=
          λ: "a",
            match: "a" with
              InjL "a" => InjL ("suspend_A" "a")
            | InjR "b" => InjR ("suspend_B" "b")
            end
        in
        let: "unsuspend" :=
          λ: "a",
            match: "a" with
              InjL "a" => InjL ("unsuspend_A" "a")
            | InjR "b" => InjR ("unsuspend_B" "b")
            end
        in
        ("ser", "suspend", "unsuspend").
Definition id : val := λ: "x", "x".
Definition p_Auth_string : val := (string_ser, id, id).
Definition p_Auth_int : val := (int_ser, id, id).

