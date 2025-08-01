From Coq Require Import Ascii String.
From Coq.ssr Require Import ssreflect.
From stdpp Require Import pretty strings.
Coercion Z.of_nat : nat >-> Z.

Definition StringOfZ (x : Z) : string := pretty x.

Definition ZOfAscii (c : Ascii.ascii) : option N :=
  match c with
  | "0"%char => Some 0%N
  | "1"%char => Some 1%N
  | "2"%char => Some 2%N
  | "3"%char => Some 3%N
  | "4"%char => Some 4%N
  | "5"%char => Some 5%N
  | "6"%char => Some 6%N
  | "7"%char => Some 7%N
  | "8"%char => Some 8%N
  | "9"%char => Some 9%N
  | _ => None
  end.

Fixpoint ZOfString' (x : string) (ac : N) : option N :=
  match x with
  | EmptyString => Some ac
  | String c x' =>
    match ZOfAscii c with
      None => None
    | Some d => ZOfString' x' (ac * 10 + d)%N
    end
  end.

Definition ZOfString (x : string) : option Z :=
  match x with
  | EmptyString => None
  | String "-"%char x' =>
      match ZOfString' x' 0 with
      | Some z => Some (- (Z.of_N z))%Z
      | None => None
      end
  | String _ _ =>
      match (ZOfString' x 0) with
      | Some z => Some (Z.of_N z)
      | None => None
      end
  end.

Lemma lt_acc (n : N) : Acc N.lt n.
Proof.
  induction n using N.peano_ind; first by constructor; intros; lia.
  constructor => m Hlt.
  destruct (decide (m < n)%N); first by apply IHn.
    by replace m with n by lia.
Qed.

Lemma ZOfAscii_pretty x :
  (x < 10)%N →
  ZOfAscii (pretty_N_char x) = Some x.
Proof.
  intros Hlt.
  inversion Hlt as [Hlt']; cbv in Hlt'.
  destruct x as [|p]; first done.
  destruct p as [[[[]|[]|]|[[]|[]|]|]|[[[]|[]|]|[[]|[]|]|]|]; try done.
Qed.

Lemma ZOfAscii_inv a x :
  ZOfAscii a = Some x → pretty_N_char x = a ∧ (x < 10)%N.
Proof.
  intros Hlt.
  rewrite /ZOfAscii in Hlt.
  destruct a as [[] [] [] [] [] [] [] []]; try done;
    simplify_eq; (split; [done| lia]).
Qed.

Lemma ZOfString'_app s s' k :
  match ZOfString' s k with
  | None => ZOfString' (s +:+ s') k = None
  | Some m => ZOfString' (s +:+ s') k = ZOfString' s' m
  end.
Proof.
  revert s' k; induction s.
  - induction s'; simpl; first done.
    intros k.
    destruct a as [[] [] [] [] [] [] [] []]; simpl; auto;
      match goal with
        |- match ZOfString' s' ?A with _ => _ end =>
        specialize (IHs' A);
          destruct (ZOfString' s' A); trivial
      end.
  - intros s' k; simpl; fold String.app.
    destruct a as [[] [] [] [] [] [] [] []]; simpl; auto;
      match goal with
        |- match ZOfString' s ?A with _ => _ end =>
        specialize (IHs s' A);
          destruct (ZOfString' s (k * 10 + 7)); auto
      end.
Qed.

Global Instance append_assoc : Assoc eq String.app.
Proof.
  intros x.
  induction x.
  - induction y; auto with f_equal.
  - intros y z.
    rewrite /String.app -/String.app IHx. f_equal.
Qed.

Lemma pretty_N_go_app m s :
  (0 < m)%N → pretty_N_go m s = (pretty_N_go m "") +:+ s.
Proof.
  intros Hlt. revert s.
  induction (lt_acc m) as [? ? IH] => s.
  rewrite !(pretty_N_go_step x) //.
  destruct (decide (x < 10)%N).
  - rewrite N.div_small // pretty_N_go_0 /=.
  - assert (x `div` 10 < x)%N as Hltdv.
    { apply N.div_lt; auto with lia. }
    assert (0 < x `div` 10)%N as Hdvp.
    { apply N.div_str_pos; lia. }
    pose proof (IH _ Hltdv Hdvp) as IH'.
    rewrite (IH' (String (pretty_N_char (x `mod` 10)) "")).
    rewrite IH'; simpl.
      by rewrite -assoc.
Qed.

Lemma ZOfString'_inv (n : nat) :
  ZOfString' (StringOfZ n) 0 = Some (N.of_nat n).
Proof.
  destruct n; first done; simpl.
  rewrite /pretty /= /pretty_positive /pretty /pretty_N.
  remember (N.pos (Pos.of_succ_nat n)) as m.
  replace (S n) with (N.to_nat m); last first.
  { by rewrite Heqm positive_N_nat SuccNat2Pos.id_succ. }
  assert (Hmlt : (0 < m)%N) by lia.
  rewrite decide_False; [lia|].
  clear dependent n.
  induction (lt_acc m) as [? ? IH].
  rewrite pretty_N_go_step; [done|].
  destruct (decide (x < 10)%N).
  - rewrite N.mod_small //.
    rewrite N.div_small // pretty_N_go_0 /= ZOfAscii_pretty //.
    rewrite N2Nat.id //.
  - assert (x `div` 10 < x)%N as Hltdv.
    { apply N.div_lt; auto with lia. }
    assert (0 < x `div` 10)%N as Hdvp.
    { apply N.div_str_pos; lia. }
    rewrite pretty_N_go_app //.
    pose proof (ZOfString'_app
                  (pretty_N_go (x `div` 10) "")
                  (String (pretty_N_char (x `mod` 10)) "") 0) as Hlp.
    rewrite (IH _ Hltdv Hdvp) in Hlp.
    rewrite Hlp.
    rewrite /= ZOfAscii_pretty; [by apply N.mod_lt|].
    replace (x `div` 10 * 10)%N with (10 * x `div` 10)%N by lia.
    rewrite 2!N2Nat.id.
    f_equal.
    rewrite N.mul_comm.
    rewrite -N.div_mod' //.
Qed.

Lemma pretty_N_go_nnil m s :
  (0 < m)%N → pretty_N_go m s ≠ "".
Proof.
  intros Hlt. revert s.
  induction (lt_acc m) as [? ? IH] => s.
  rewrite !(pretty_N_go_step x) //.
  destruct (decide (x < 10)%N).
  - rewrite N.div_small // pretty_N_go_0 /=.
  - assert (x `div` 10 < x)%N as Hltdv.
    { apply N.div_lt; auto with lia. }
    assert (0 < x `div` 10)%N as Hdvp.
    { apply N.div_str_pos; lia. }
    apply (IH _ Hltdv Hdvp).
Qed.

Lemma pretty_N_go_pos_nneg m s s':
  (0 < m)%N → pretty_N_go m s ≠ String "-" s'.
Proof.
  intros Hlt. revert s.
  induction (lt_acc m) as [? ? IH] => s.
  rewrite !(pretty_N_go_step x) //.
  destruct (decide (x < 10)%N).
  - rewrite N.div_small // pretty_N_go_0 /=.
    destruct x as [|p]; first done.
    destruct p as [[[[]|[]|]|[[]|[]|]|]|[[[]|[]|]|[[]|[]|]|]|]; done.
  - assert (x `div` 10 < x)%N as Hltdv.
    { apply N.div_lt; auto with lia. }
    assert (0 < x `div` 10)%N as Hdvp.
    { apply N.div_str_pos; lia. }
    apply (IH _ Hltdv Hdvp).
Qed.

Lemma StringOfZ_nnil m : StringOfZ m ≠ "".
Proof.
  unfold StringOfZ; simpl.
  destruct m; auto.
  apply pretty_N_go_nnil; lia.
Qed.

Lemma ZOfString_inv (n : Z) : ZOfString (StringOfZ n) = Some n.
Proof.
  unfold ZOfString.
  destruct (StringOfZ n) eqn:Heq;
    first by exfalso; eapply StringOfZ_nnil; eauto.
  destruct n as [|p|p] eqn:Heqn.
  - destruct a as [[] [] [] [] [] [] [] []]; try done.
    rewrite -?Heq //.
  - rewrite -?Heq.
    pose proof (ZOfString'_inv (Pos.to_nat p)) as HZSi.
    rewrite positive_nat_Z in HZSi.
    rewrite HZSi nat_N_Z positive_nat_Z.
    destruct a as [[] [] [] [] [] [] [] []]; auto.
    by rewrite Heq in HZSi.
  - simpl in Heq.
    assert (0 < 1)%nat as Hneq by lia.
    pose proof (String.append_correct1 "-" (pretty (N.pos p)) 0 Hneq) as Hf;
      simpl in Heq.
    rewrite Heq in Hf; inversion Hf; subst.
    rewrite -(@String.app_inj "-" (pretty (N.pos p)) s Heq).
    pose proof (ZOfString'_inv (Pos.to_nat p)) as HZSi.
    rewrite positive_nat_Z in HZSi.
    by rewrite HZSi nat_N_Z positive_nat_Z.
Qed.

#[global] Instance StringOfZ_inj : Inj (=) (=) StringOfZ.
Proof.
  intros [|x|x] [|y|y] Hpretty; simplify_eq/=; try done.
  - by destruct (pretty_N_go_ne_0 (N.pos y) "").
  - by destruct (pretty_N_go_ne_0 (N.pos x) "").
  - by edestruct (pretty_N_go_ne_dash (N.pos x) "").
  - by edestruct (pretty_N_go_ne_dash (N.pos y) "").
Qed.

Lemma append_nil_l s :
  "" +:+ s = s.
Proof. done. Qed.

Lemma append_cons s1 :
  ∀ s2 a, String a (s1 +:+ s2) = (String a s1) +:+ s2.
Proof.
  induction s1; intros.
  - by rewrite append_nil_l.
  - rewrite -IHs1. done.
Qed.

Lemma length_Sn a s :
  String.length (String a s) = S (String.length s).
Proof. by cbn. Qed.

Lemma length_app s1 :
  ∀ s2, String.length (s1 +:+ s2) = (String.length s1 + String.length s2)%nat.
Proof.
  induction s1; intros.
  - by rewrite append_nil_l.
  - by rewrite -append_cons !length_Sn IHs1.
Qed.

Lemma prefix_empty_true s :
  String.prefix "" s = true.
Proof. destruct s; cbn; auto. Qed.

Lemma index_0_empty s :
  String.index 0 "" s = Some 0%nat.
Proof. destruct s; by cbn. Qed.

Lemma index_prefix_true s s' :
  String.index 0 s s' = Some 0%nat →
  String.prefix s s' = true.
Proof.
  destruct s,s'; simpl; cbn; auto.
  - intro; inversion H.
  - intro; destruct ascii_dec.
    + destruct (String.prefix s s'); auto; destruct (String.index 0 _ s'); inversion H.
    + destruct (String.index 0 _ s'); inversion H.
Qed.

Lemma index_cons_0_eq a s s' :
  String.index 0 s s' = Some 0%nat → String.index 0 (String a s) (String a s') = Some 0%nat.
Proof.
  intros Hindex.
  cbn. destruct ascii_dec.
  - assert (Hprefix: String.prefix s s' = true).
    { by apply index_prefix_true. }
      by rewrite Hprefix.
  - by destruct n.
Qed.

Lemma index_append_here s t :
  index 0 s (s +:+ t) = Some 0%nat.
Proof.
  induction s.
  - apply index_0_empty.
  - apply index_cons_0_eq.
    apply IHs.
Qed.

Lemma index_0_append_char a t v s :
  s = String a "" →
  index 0 s t = None →
  index 0 s (t +:+ s +:+ v) = Some (String.length t).
Proof.
  induction t; intros.
  - rewrite append_nil_l. apply index_append_here.
  - rewrite H. rewrite -append_cons. cbn.
    destruct ascii_dec; subst. cbn in H0. destruct ascii_dec.
    rewrite prefix_empty_true in H0. inversion H0.
      by destruct n.
      rewrite IHt; auto. cbn in H0. destruct ascii_dec. by destruct n.
      destruct index; auto. inversion H0.
Qed.

Lemma substring_0_length s :
  substring 0 (String.length s) s = s.
Proof. induction s; simpl; auto. by rewrite IHs. Qed.

Lemma substring_Sn a n m s :
  substring (S n) m (String a s) = substring n m s.
Proof. induction s; destruct n,m; simpl; auto. Qed.

Lemma substring_add_length_app n m s1 :
  ∀ s2, substring (String.length s1 + n) m (s1 +:+ s2) = substring n m s2.
Proof. induction s1; destruct n,m; simpl; auto. Qed.

Lemma substring_0_length_append s1 s2 :
  substring 0 (String.length s1) (s1 +:+ s2) = s1.
Proof. apply prefix_correct, index_prefix_true, index_append_here. Qed.

Lemma substring_length_append s1 :
  ∀ s2, substring (String.length s1) (String.length s2) (s1 +:+ s2) = s2.
Proof.
  induction s1; intros s2.
  - rewrite append_nil_l. apply substring_0_length.
  - rewrite length_Sn substring_Sn. apply IHs1.
Qed.

Lemma substring_n_0 n s :
  substring n 0 s = "".
Proof.
  induction n in s |-* => /=.
  { by destruct s. }
  destruct s; [done|].
  by simpl.
Qed.

Lemma substring_empty_string n m :
  substring n m "" = "".
Proof. by destruct n, m. Qed.

Lemma substring_n_Sm_split_1 n m s :
  substring n (S m) s = substring n 1 s +:+ substring (S n) m s.
Proof.
  induction n in m, s |-*.
  - destruct s => /=; rewrite ?substring_empty_string //.
    rewrite -append_cons substring_n_0.
    rewrite append_nil_l //.
  - destruct s => /=; rewrite ?substring_empty_string //.
Qed.

Lemma substring_append_shift p n s m :
  substring p n s +:+ substring (p + n) (S m) s = substring p (S n) s +:+ substring (p + S n) m s.
Proof.
  induction n in s, m, p |-*.
  - rewrite Nat.add_0_r.
    rewrite substring_n_0.
    rewrite append_nil_l Nat.add_1_r.
    apply substring_n_Sm_split_1.
  - rewrite {1}substring_n_Sm_split_1.
    rewrite Nat.add_succ_r.
    rewrite -append_assoc.
    rewrite IHn.
    rewrite append_assoc.
    rewrite -substring_n_Sm_split_1.
    do 2 f_equal. lia.
Qed.

Lemma substring_split n s m p :
  n ≤ m →
  substring p m s = substring p n s +:+ substring (p + n) (m - n) s.
Proof.
  induction n in s, m, p |-* => Hle.
  - destruct s; rewrite ?substring_empty_string //.
    destruct m, p; rewrite Nat.add_0_r substring_n_0 //.
  - destruct s; rewrite ?substring_empty_string //.
    destruct m; [lia|].
    destruct p => /=.
    + rewrite -append_cons. rewrite IHn //. lia.
    + rewrite -substring_append_shift.
      rewrite IHn; [lia|].
      rewrite Nat.sub_succ_l //. lia.
Qed.

Lemma substring_split_from_O s n :
  n ≤ String.length s →
  s = substring 0 n s +:+ substring n (String.length s - n) s.
Proof. intros. rewrite -{1}(substring_0_length s) (substring_split n) //. Qed.

Lemma length_substring s n m :
  n + m ≤ String.length s →
  String.length (substring n m s) = m.
Proof.
  induction s in n, m |-* => /=.
  { destruct n, m; lia || done. }
  intros Hle.
  destruct n; last first.
  { apply IHs. lia. }
  destruct m => /=; [done|].
  rewrite IHs //.
  lia.
Qed.

Lemma length_substring_le n m s :
  String.length (substring n m s) ≤ String.length s.
Proof.
  induction s in n, m |-*.
  - rewrite substring_empty_string //.
  - destruct n => /=.
    + destruct m => /=; try lia. by apply le_n_S.
    + eauto with lia.
Qed.

Definition not_number (c : ascii) :=
  (c ≠ "0" ∧ c ≠ "1" ∧ c ≠ "2" ∧ c ≠ "3" ∧ c ≠ "4" ∧
   c ≠ "5" ∧ c ≠ "6" ∧ c ≠ "7" ∧ c ≠ "8" ∧ c ≠ "9")%char.

Lemma get_n_pretty_N_go_ne n N s (c : ascii) :
  not_number c →
  (∀ m, get m s ≠ Some c) → get n (pretty_N_go N s) ≠ Some c.
Proof.
  intros (?&?&?&?&?&?&?&?&?&?). revert s.
  induction (N.lt_wf_0 N) as [x _ IH]. intros s Hs.
  assert (x = 0 ∨ 0 < x < 10 ∨ 10 ≤ x)%N as [->|[[??]|?]] by lia.
  - rewrite pretty_N_go_0. done.
  - rewrite pretty_N_go_step //.
    apply IH.
    { by apply N.div_lt. }
    assert (x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6
            ∨ x = 7 ∨ x = 8 ∨ x = 9)%N as Hx by lia.
    destruct_or! Hx; simplify_eq; intros [];
      simpl; (done || by intros [=]).
  - rewrite pretty_N_go_step; [lia|].
    apply IH.
    { apply N.div_lt; lia. }
    intros []; [|by simpl].
    unfold pretty_N_char;
      repeat (discriminate || case_match); simpl;
        by intros [=].
Qed.

Lemma get_StringOfZ_ne z n c :
  not_number c ∧ c ≠ "-"%char → get n (StringOfZ z) ≠ Some c.
Proof.
  intros [Hc Hdash].
  destruct z.
  - destruct n; intros [=]. by destruct_and! Hc.
  - simpl.
    rewrite /pretty /= /pretty_positive /pretty /pretty_N.
    destruct decide; [done|]. by eapply get_n_pretty_N_go_ne.
  - destruct n; simpl; [congruence|]. by eapply get_n_pretty_N_go_ne.
Qed.

Lemma pretty_N_go_length N s :
  N ≠ 0%N ∨ s ≠ "" →
  0 < String.length (pretty_N_go N s).
Proof.
  induction (N.lt_wf_0 N) as [x _ IH] in s |-*.
  assert (x = 0 ∨ 0 < x < 10 ∨ 10 ≤ x)%N as [-> | [[??]|?] ] by lia.
  - intros [? | ?]; [lia|].
    rewrite pretty_N_go_0. induction s => /=; [done|lia].
  - intros Hs.
    rewrite pretty_N_go_step //.
    apply IH.
    { by apply N.div_lt. }
    assert (x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6
            ∨ x = 7 ∨ x = 8 ∨ x = 9)%N as Hx by lia.
    destruct_or! Hx; simplify_eq; eauto.
  - intros Hs.
    rewrite pretty_N_go_step; [lia|].
    apply IH.
    { apply N.div_lt; lia. }
    auto.
Qed.

Lemma StringOfZ_length z :
  0 < String.length (StringOfZ z).
Proof.
  induction z => /=; [lia| |lia].
  rewrite /pretty /pretty_positive /pretty /pretty_N.
  destruct decide; [lia|].
  eapply pretty_N_go_length.
  by left.
Qed.

Lemma gt_exists_S_n n m :
  n < m → ∃ m', m = S m'.
Proof. destruct n, m; [lia|eauto with lia|lia|eauto with lia]. Qed.

Lemma append_length_gt (n : nat) s1 s2 :
  String.length s1 < n → get n (s1 +:+ s2) = get (n - String.length s1) s2.
Proof.
  revert s2 n; induction s1; intros s2 n Hgt.
  - rewrite append_nil_l Nat.sub_0_r //.
  - destruct (gt_exists_S_n _ _ Hgt) as [m ->].
    rewrite -append_cons.
    simpl in *. apply IHs1. lia.
Qed.

Lemma get_n_append_ne s1 s2 c n :
  (∀ m, get m s1 ≠ Some c) →
  (∀ m, get m s2 ≠ Some c) →
  get n (s1 +:+ s2) ≠ Some c.
Proof.
  destruct (decide (n < String.length s1)).
  { rewrite -append_correct1 //. }
  destruct (decide (n = String.length s1)) as [-> |].
  { rewrite -(append_correct2 _ _ 0). auto. }
  rewrite append_length_gt //. lia.
Qed.

Lemma get_head_ne_succ a a' n s :
  a ≠ a' → get n (String a s) = Some a' →
  ∃ n', n = S n' ∧ get (S n') (String a s) = Some a'.
Proof. intros Hneq Hget. destruct n; [by inversion Hget|by exists n]. Qed.

Lemma string_length_zero s : String.length s = 0 → s = "".
Proof. by destruct s. Qed.

Lemma append_eq_length_inv (s1 s2 s1' s2' : string) :
  String.length s1 = String.length s2 →
  s1 +:+ s1' = s2 +:+ s2' → s1 = s2 ∧ s1' = s2'.
Proof.
  revert s2; induction s1; simpl.
  - destruct s2; [done|]. intros [=].
  - destruct s2; simpl; [intros [=]|].
    rewrite -!append_cons.
    intros [=] [=]. simplify_eq.
    split; [f_equal|]; by eapply IHs1.
Qed.

Lemma char_splits_l s1 s2 s1' s2' (c : ascii) :
  (∀ n, get n s2 ≠ Some c) →
  (∀ n, get n s2' ≠ Some c) →
  s1 +:+ (String c "") +:+ s1' = s2 +:+ (String c "") +:+ s2' →
  s1 = s2 ∧ s1' = s2'.
Proof.
  intros Hs2 Hs2' Heq.
  apply append_eq_length_inv in Heq as [? [=]]; [done|].
  pose proof ((proj2 (get_correct _ _) Heq (String.length s1))) as Hget.
  rewrite -(append_correct2 _ _ 0) /= in Hget.
  edestruct Nat.lt_trichotomy as [Hlt | [Heq' | Hgt]]; [ |exact Heq'|].
  - rewrite -(append_correct1) //= in Hget.
    symmetry in Hget. by apply Hs2 in Hget.
  - rewrite (append_length_gt _ s2) // in Hget.
    destruct (gt_exists_S_n _ _ Hgt) as [n Hn].
    rewrite Hn in Hget.
    rewrite Nat.sub_succ_l in Hget; [lia|].
    simpl in Hget. symmetry in Hget.
    by apply Hs2' in Hget.
Qed.

Inductive elem_of_string : ElemOf ascii string :=
| elem_of_string_here (x : ascii) s : elem_of x (String x s)
| elem_of_string_further (x y : ascii) s : elem_of x s → elem_of x (String y s).
Local Existing Instance elem_of_string.

Lemma elem_of_string_cons (a1 a2 : ascii) (s : string)  :
  a1 ∈ String a2 s ↔ a1 = a2 ∨ a1 ∈ s.
Proof. by split; [inversion 1; subst|intros [->|?]]; constructor. Qed.
Lemma not_elem_of_string_cons (s : string) (x y : ascii) :
  x ∉ String y s ↔ x ≠ y ∧ x ∉ s.
Proof. rewrite elem_of_string_cons. tauto. Qed.

(** This lemma is ported from the stdpp library on lists.
    It is very similar to [char_splits_l], although it asserts properties
    about the prefix, rather than suffix.
    The suffix variant has not been ported, as it relies on list reverse,
    which has no analog for strings. *)
Lemma not_elem_of_string_app_cons_inv_l (a1 a2 : ascii) (l1 l2 k1 k2 : string) :
  a1 ∉ k1 → a2 ∉ l1 →
  l1 +:+ String a1 l2 = k1 +:+ String a2 k2 →
  l1 = k1 ∧ a1 = a2 ∧ l2 = k2.
Proof.
  revert k1.
  induction l1 as [|x' l1 IH]; intros [|y' k1] Hx Hy ?; simplify_eq/=;
    try apply not_elem_of_string_cons in Hx as [??];
      try apply not_elem_of_string_cons in Hy as [??]; naive_solver.
Qed.
Lemma get_string_elem_of a s : (∃ n, get n s = Some a) ↔ a ∈ s.
Proof.
  split.
  - intros [n Hget].
    generalize dependent n.
    induction s as [|a' s IHs]; [done|].
    intros n Hget.
    destruct (decide (a=a')) as [<-|]; [apply elem_of_string_here|].
    apply elem_of_string_further.
    apply get_head_ne_succ in Hget; [|done].
    destruct Hget as (n'&->&Hget).
    by eapply IHs.
  - intros Hin.
    induction s as [|a' s IHs]; [by inversion Hin|].
    apply elem_of_string_cons in Hin.
    destruct Hin as [<-|Hin]; [by exists 0|].
    apply IHs in Hin. destruct Hin as [m Hget].
    by exists (S m).
Qed.

(** This is very domain specific. Can maybe be generalised to derive the
    possible values of [a] *)
Lemma StringOfZ_not_sep a n :
  a ∈ StringOfZ n → a ≠ "_"%char.
Proof.
  intros Hin ->.
  rewrite -get_string_elem_of in Hin.
  destruct Hin as [n' Hin].
  assert (not_number "_"%char ∧ "_"%char ≠ "-"%char) as Hnan by done.
  by eapply get_StringOfZ_ne in Hnan.
Qed.

Definition valid_tag t := index 0 "_" t = None.

Lemma valid_tag_String c s :
  index 0 "_" (String c "") = None → valid_tag s → valid_tag (String c s).
Proof.
  rewrite /valid_tag /=.
  case_match; try done.
  intros _ ->.
  case_match; try done.
Qed.

Lemma valid_tag_pretty_Npos p :
  valid_tag (pretty.pretty (N.pos p)).
Proof.
  rewrite /pretty.pretty /pretty.pretty_N.
  assert (valid_tag "") as Hemp by done; revert Hemp.
  apply (λ H, N.strong_right_induction
                (λ n, ∀ s, valid_tag s → valid_tag (pretty.pretty_N_go n s))
                0%N H); last done.
  intros n Hn IH s Hs.
  destruct (decide (n = 0%N)); first by subst.
  rewrite pretty.pretty_N_go_step; [lia|].
  destruct (decide (n < 10)%N).
  - rewrite N.div_small //.
    rewrite pretty.pretty_N_go_0.
    apply valid_tag_String; auto.
    rewrite /pretty.pretty_N_char.
    repeat case_match; done.
  - apply IH; first apply N.le_0_l.
    + eapply N.lt_le_trans; last by apply (N.Div0.mul_div_le _ 10).
      assert (n `div` 10 ≠ 0)%N.
      { by intros ?%N.div_small_iff. }
      assert (0 < n `div` 10)%N by by apply N.div_str_pos; auto with lia.
      lia.
    + apply valid_tag_String; auto.
      rewrite /pretty.pretty_N_char.
      repeat case_match; done.
Qed.

Lemma valid_tag_stringOfZ a :
  valid_tag (StringOfZ a).
Proof.
  destruct a; rewrite/valid_tag /=; first done.
  apply valid_tag_pretty_Npos.
  by rewrite valid_tag_pretty_Npos.
Qed.
