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


Definition auth_ser_p : val :=
  λ: "a",
    match: "a" with
      NONE => NONEV
    | SOME "a" =>
      let: "a_ser" := auth_scheme.(s_serializer') in
      match: "a" with
        InjL "d" =>
          let, ("a", "h") := "d" in
          "a_ser" (InjR "h")
      | InjR "d" =>
          let, ("p", "b", <>, "a", "h") := "d" in
          if: !"b" then "a_ser" (InjL #"")
          else "a_ser" (InjR "h")
      end
    end.

Definition auth_suspend_p : val :=
  λ: "a",
    match: "a" with
      NONE => NONEV
    | SOME "a" =>
      match: "a" with
        InjL "d" =>
          let, ("a", "h") := "d" in
          InjR (NewProph, ref #false, ref #false, "a", "h")
      | InjR <> => NONEV
      end
    end.

Definition auth_unsuspend_p : val :=
  λ: "a",
    match: "a" with
      NONE => NONEV
    | SOME "a" =>
      match: "a" with
        InjL "d" => NONEV
      | InjR "d" =>
          let, ("p", "b", "r", "a", "h") := "d" in
          resolve_proph: "p" to: #false;;
          "r" <- #true;;
          SOME (InjL ("a", "h"))
      end
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
        let: "ser" := prod_ser'' "ser_A" "ser_B" in
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
        let: "ser" := sum_ser'' "ser_A" "ser_B" in
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
Definition p_Auth_string : val := (string_ser', id, id).
Definition p_Auth_int : val := (int_ser', id, id).

