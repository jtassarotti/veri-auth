From auth.heap_lang.lib Require Export serialization_susp.
From auth.typing Require Export types typing.
From auth.prelude Require Import strings.

Definition int_count : val :=
  λ: <>, #0.
Definition string_count : val := int_count.
Definition prod_count : val :=
  λ: "countA" "countB" "v",
    "countA" (Fst "v") + "countB" (Snd "v").
Definition sum_count : val :=
  λ: "countA" "countB" "v",
    match: "v" with
      InjL "vA" => "countA" "vA"
    | InjR "vB" => "countB" "vB"
    end.
Definition option_count : val :=
  λ: "countA" "v",
    match: "v" with
      InjL <> => #0
    | InjR "vA" => "countA" "vA"
    end.

Definition auth_scheme : serialization_scheme :=
  option_serialization_scheme string_serialization_scheme.
Arguments s_serializer' : simpl never.
Arguments s_deserializer : simpl never.

Definition auth_ser_v : val :=
  λ: "v",
    match: "v" with
      NONE => NONEV
    | SOME "v" =>
        match: "v" with
          InjL "h" => auth_scheme.(s_serializer') (SOME "h")
        | InjR "susp" =>
            match: !"susp" with
              InjR "h" => auth_scheme.(s_serializer') (SOME "h")
            | InjL <> => NONEV
            end
        end
    end.

Definition auth_deser_v : val :=
  λ: "pid" "s",
    match: auth_scheme.(s_deserializer) "s" with
      NONE => NONE
    | SOME "v" =>
        match: "v" with
          NONE => SOME (SOME (InjR (ref (InjL ("pid", NewProph)))))
        | SOME "h" => SOME (SOME (InjL "h"))
        end
    end.

Definition auth_count : val :=
  λ: "v",
    match: "v" with
      NONE => #0
    | SOME "a" =>
        match: "a" with
          InjL <> => #0
        | InjR "susp" =>
            match: !"susp" with
              InjR "h" => #0
            | InjL <> => #1
            end
        end
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
        let: "ser" := prod_ser'' "ser_A" "ser_B" in
        let: "deser" := λ: "pid", prod_deser ("deser_A" "pid") ("deser_B" "pid") in
        let: "count" := prod_count "count_A" "count_B" in
        ("ser", "deser", "count").
Definition v_Auth_sum : val :=
  Λ: Λ: λ: "A" "B",
        let, ("ser_A", "deser_A", "count_A") := "A" in
        let, ("ser_B", "deser_B", "count_B") := "B" in
        let: "ser" := sum_ser'' "ser_A" "ser_B" in
        let: "deser" := λ: "pid", sum_deser ("deser_A" "pid") ("deser_B" "pid") in
        let: "count" := sum_count "count_A" "count_B" in
        ("ser", "deser", "count").
Definition v_Auth_string : val :=
  (string_ser', λ: <>, string_deser, string_count).
Definition v_Auth_int : val :=
  (int_ser', λ: <>, int_deser, int_count).

Definition v_auth : val :=
  Λ: λ: "evi" "a",
      let, ("serialize", "deserialize", "count") := "evi" in
      match: "serialize" "a" with
        NONE => NONEV
      | SOME "sera" => SOME (InjL (Hash "sera"))
      end.


(* Definition new_br : val :=
  λ: <>, (ref #false, NewProph).

(* Prophecy can only be resolved once (false -> true). This doesn't return anything *)
Definition resolve_br_proph : val :=
  λ: "p" "val",
    let, ("val", "proph") := "val" in
    if: "val" then #()
    else
      resolve_proph: "proph" to: (Hash "y");;
      "val" <- #true.

Definition read_br : val :=
  λ: "val",
    let, ("val", "p") := "val" in "val". *)

(* Definition auth_ser_p : val :=
  λ: "a",
    match: "a" with
      InjL "a_susp" =>
      let: "a_ser" := auth_scheme.(s_serializer) in
      let, ("pfl", "b", <>, "a", "h") := "a_susp" in
      resolve_proph: "pfl" to: NONEV;;
      if: !"b" then "a_ser" (InjL #"")
      else "a_ser" (InjR "h")
    | InjR "a_unsusp" =>
      let, ("a", "h") := "a_unsusp" in
      string_ser "h"
    end. *)

Definition auth_susp_ser_p : val :=
  λ: "a",
    let: "a_ser" := auth_scheme.(s_serializer) in
    let: "a" := Unbox "a" in
    let, ("b", <>, "a", "h", "pfl") := "a" in
    resolve_proph: "pfl" to: NONEV;;
    if: !"b" then "a_ser" (InjL #"")
    else "a_ser" (InjR "h").

Definition auth_unsusp_ser_p : val :=
  λ: "a",
    let, ("a", "h") := "a" in
    string_ser "h".

Definition auth_suspend_p : val :=
  λ: "unsusp_a",
    let, ("a", "h") := "unsusp_a" in
    Box (ref #false, ref #false, "a", "h", NewProph).

Definition auth_unsuspend_p : val :=
  λ: "susp_a",
    let: "susp_a" := Unbox "susp_a" in
    let, ("b", "r", "a", "h", "pfl") := "susp_a" in
    resolve_proph: "pfl" to: (SOMEV #false);;
    "r" <- #true;;
    ("a", "h").

(** type 'a evidence = 'a -> string; suspend : 'a -> 'a; unsuspend : 'a -> 'a *)
Definition p_Auth_auth : val :=
  Λ: (auth_susp_ser_p, auth_unsusp_ser_p, auth_suspend_p, auth_unsuspend_p).
Definition p_Auth_mu : val :=
  Λ: λ: "s",
      let, ("ser_susp", "ser_unsusp", "suspend", "unsuspend") := "s" in
      let: "ser_susp" :=
        λ: "a", rec_fold "ser_susp" "a"
      in
      let: "ser_unsusp" :=
        λ: "a", rec_fold "ser_unsusp" "a"
      in
      let: "suspend" :=
        λ: "a", rec_fold "suspend" "a"
      in
      let: "unsuspend" :=
        λ: "a", rec_fold "unsuspend" "a"
      in
      ("ser_susp", "ser_unsusp", "suspend", "unsuspend").
Definition p_Auth_pair : val :=
  Λ: Λ: λ: "A" "B",
        let, ("ser_susp_A", "ser_unsusp_A", "suspend_A", "unsuspend_A") := "A" in
        let, ("ser_susp_B", "ser_unsusp_B", "suspend_B", "unsuspend_B") := "B" in
        let: "ser_susp" := prod_ser "ser_susp_A" "ser_susp_B" in
        let: "ser_unsusp" := prod_ser "ser_unsusp_A" "ser_unsusp_B" in
        let: "suspend" :=
          λ: "a",
            let, ("a", "b") := "a" in
            let: "ra" := "suspend_A" "a" in
            let: "rb" := "suspend_B" "b" in
            ("ra", "rb")
        in
        let: "unsuspend" :=
          λ: "a",
            let, ("a", "b") := "a" in
            ("unsuspend_A" "a", "unsuspend_B" "b")
        in
        ("ser_susp", "ser_unsusp", "suspend", "unsuspend").
Definition p_Auth_sum : val :=
  Λ: Λ: λ: "A" "B",
        let, ("ser_susp_A", "ser_unsusp_A", "suspend_A", "unsuspend_A") := "A" in
        let, ("ser_susp_B", "ser_unsusp_B", "suspend_B", "unsuspend_B") := "B" in
        let: "ser_susp" := sum_ser "ser_susp_A" "ser_susp_B" in
        let: "ser_unsusp" := sum_ser "ser_unsusp_A" "ser_unsusp_B" in
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
              InjL "a" =>
                InjL ("unsuspend_A" "a")
            | InjR "b" =>
                InjR ("unsuspend_B" "b")
            end
        in
        ("ser_susp", "ser_unsusp", "suspend", "unsuspend").
Definition id : val := λ: "x", "x".
(* Definition id_some : val := λ: "x", SOME "x". *)
Definition p_Auth_string : val := (string_ser, string_ser, id, id).
Definition p_Auth_int : val := (int_ser, int_ser, id, id).

Definition p_auth : val :=
  Λ: λ: "evi" "a",
    let, ("s", "serialize", "suspend", "unsuspend") := "evi" in
    match: ("unsuspend" "a") with
      NONE => NONEV
    | SOME "unsusp_a" =>
        Box (ref #false, ref #false, "unsusp_a",
           Hash ("serialize" "unsusp_a"), NewProph)
    end.

