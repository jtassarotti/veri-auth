From stdpp Require Import tactics.

Ltac destruct_go H :=
  try
    lazymatch type of H with
    | True => clear H
    | ∃ _, _ =>
      let x := fresh in
      let H' := fresh in
      destruct H as [x H'];
      destruct_go H'
    | _ ∧ _ =>
      let H1 := fresh in
      let H2 := fresh in
      destruct H as [ H1 H2 ];
      destruct_go H1; destruct_go H2
    | _ ∨ _ => destruct H as [H|H]; destruct_go H
    | Is_true (bool_decide _) => apply (bool_decide_unpack _) in H
    | Is_true (_ || _) => apply orb_True in H; destruct H as [H|H]
    | Is_true (bool_decide _) =>
      apply (bool_decide_unpack _) in H; destruct_go H
    | Is_true (_ && _) =>
      apply andb_True in H; destruct_go H
  end.

Tactic Notation "destruct" "?" ident(H) :=
  destruct_go H.
Tactic Notation "destruct" "!" ident(H) :=
  hnf in H; progress (destruct? H).

From stdpp Require Import list fin_maps gmap.

(* TODO: move and upstream *)
Lemma list_to_map_list_insert `{Countable K} {V} i (k : K) (v v' : V) xs :
  NoDup xs.*1 →
  xs !! i = Some (k, v') →
  list_to_map (<[i:=(k, v)]> xs) = <[k:=v]> (list_to_map (M := gmap K V) xs).
Proof.
  induction xs as [|[k' w] xs IH] in i, k, v, v' |-*; [done|].
  rewrite lookup_cons. destruct i => /=.
  - intros ? [= -> <-]. rewrite insert_insert. done.
  - intros [Hk' Hxs]%NoDup_cons Hlook => /=.
    assert (k ≠ k').
    { intros <-. apply Hk'. apply elem_of_list_fmap.
      eexists (k, v'). split; [done|].
      by eapply elem_of_list_lookup_2. }
    rewrite insert_commute; [|done].
    by setoid_rewrite IH.
Qed.

Lemma NoDup_fst_list_alter_pair {K V} (xs : list (K * V)) k v w i :
  xs !! i = Some (k, w) →
  NoDup xs.*1 →
  NoDup (alter (λ _ : K * V, (k, v)) i xs).*1.
Proof.
  induction xs as [|[k' w'] xs IH] in i, k, v, w |-*; [done|].
  rewrite lookup_cons. destruct i => /=.
  { by intros [= -> ->]. }
  rewrite !NoDup_cons.
  intros Hlook [Hk' Hxs].
  split; [|by eapply IH].
  rewrite elem_of_list_fmap.
  intros ([k'' w''] & ? & H). simplify_eq/=.
  apply elem_of_list_lookup_1 in H as (j &?).
  eapply Hk'. apply elem_of_list_fmap.
  (* Why is this necessary? *)
  replace list_alter with
    (alter (Alter := (list_alter (A := K * V)))) in H; [|done].
  destruct (decide (i = j)) as [<-|].
  - rewrite list_lookup_alter, Hlook in H. simplify_eq/=.
    eexists (_, _). split; [done|]. apply elem_of_list_lookup. eauto.
  - rewrite list_lookup_alter_ne in H; [|done].
    eexists (_, _). split; [done|]. apply elem_of_list_lookup. eauto.
Qed.
