From iris.proofmode Require Import
     coq_tactics ltac_tactics
     sel_patterns environments
     reduction.
From auth.rel_logic_tern Require Export model spec_rules.
Set Default Proof Using "Type".

(** * Verifier tactics *)

(** ** bind *)
Lemma tac_v_bind_gen `{authG Σ} k Δ Δ' i p e e' Q :
  envs_lookup i Δ = Some (p, spec_verifier k e)%I →
  e = e' →
  envs_simple_replace i p (Esnoc Enil i (spec_verifier k e')) Δ = Some Δ' →
  (envs_entails Δ' Q) →
  (envs_entails Δ Q).
Proof.
  rewrite envs_entails_unseal. intros; subst. simpl.
  rewrite envs_simple_replace_sound // /=.
  destruct p; rewrite /= ?right_id; by rewrite bi.wand_elim_r.
Qed.

Lemma tac_v_bind `{authG Σ} k e' Δ Δ' i p K' e Q :
  envs_lookup i Δ = Some (p, spec_verifier k e)%I →
  e = fill K' e' →
  envs_simple_replace i p (Esnoc Enil i (spec_verifier k (fill K' e'))) Δ = Some Δ' →
  (envs_entails Δ' Q) →
  (envs_entails Δ Q).
Proof. intros. by eapply tac_v_bind_gen. Qed.

Ltac v_bind_helper :=
  simpl;
  lazymatch goal with
  | |- fill ?K ?e = fill _ ?efoc =>
     reshape_expr e ltac:(fun K' e' =>
       unify e' efoc;
       let K'' := eval cbn[app] in (K' ++ K) in
       replace (fill K e) with (fill K'' e') by (by rewrite ?fill_app))
  | |- ?e = fill _ ?efoc =>
     reshape_expr e ltac:(fun K' e' =>
       unify e' efoc;
       replace e with (fill K' e') by (by rewrite ?fill_app))
  end; reflexivity.

Tactic Notation "v_normalise" constr(j) :=
  iStartProof;
  eapply (tac_v_bind_gen j);
    [iAssumptionCore (* prove the lookup *)
    | lazymatch goal with
      | |- fill ?K ?e = _ =>
          by rewrite /= ?fill_app /=
      | |- ?e = _ => try fast_done
      end
    |reflexivity
    |(* new goal *)].

Tactic Notation "v_bind" open_constr(j) open_constr(efoc) :=
  iStartProof;
  eapply (tac_v_bind j efoc);
    [iAssumptionCore (* prove the lookup *)
    |v_bind_helper (* do actual work *)
    |reflexivity
    |(* new goal *)].
Tactic Notation "v_bind" open_constr(efoc) :=
  v_bind _ efoc.

Lemma tac_v_pure `{authG Σ} e K' e1 k e2 Δ1 E1 i1 e' ϕ ψ Q n :
  (* we have those premises first, because we will be trying to solve them *)
(*      with backtracking using reashape_expr; see the accompanying Ltac. *)
(*      the first premise decomposes the expression, the second one checks *)
(*      that we can make a pure step *)
  e = fill K' e1 →
  PureExec ϕ n e1 e2 →
  (∀ P, ElimModal ψ false false (|={E1}=> P) P Q Q) →
  nclose specN ⊆ E1 →
  envs_lookup i1 Δ1 = Some (false, spec_verifier k e)%I →
  ψ →
  ϕ →
  (* we will call simpl on this goal thus re-composing the expression again *)
  e' = fill K' e2 →
  match envs_simple_replace i1 false (Esnoc Enil i1 (spec_verifier k e')) Δ1 with
  | Some Δ2 => envs_entails Δ2 Q
  | None => False
  end →
  envs_entails Δ1 Q.
Proof.
  rewrite envs_entails_unseal. intros -> Hpure ?? HΔ1 Hψ Hϕ -> ?.
  destruct (envs_simple_replace _ _ _ _) as [Δ2|] eqn:HΔ2; try done.
  rewrite (envs_simple_replace_sound Δ1 Δ2 i1) //; simpl.
  rewrite right_id.
  rewrite step_verifier_pure //.
  rewrite -[Q]elim_modal // /=.
  apply bi.sep_mono_r.
  apply bi.wand_intro_l.
  by rewrite bi.wand_elim_r.
Qed.

Tactic Notation "v_pure" constr(j) open_constr(ef) :=
  iStartProof;
  lazymatch goal with
  | |- context[environments.Esnoc _ ?H (spec_verifier j (fill ?K' ?e))] =>
    reshape_expr e ltac:(fun K e' =>
      unify e' ef;
      eapply (tac_v_pure (fill K' e) (K++K') e' j);
      [by rewrite ?fill_app | tc_solve | ..])
  | |- context[environments.Esnoc _ ?H (spec_verifier j ?e)] =>
    reshape_expr e ltac:(fun K e' =>
      unify e' ef;
      eapply (tac_v_pure e K e' j);
      [by rewrite ?fill_app | tc_solve | ..])
  end;
  [tc_solve || fail "v_pure: cannot eliminate modality in the goal"
  |solve_ndisj || fail "v_pure: cannot prove 'nclose specN ⊆ ?'"
  (* |iAssumptionCore || fail "v_pure: cannot find spec_ctx" (* spec_ctx *) *)
  |iAssumptionCore || fail "v_pure: cannot find the RHS" (* TODO fix error message *)
  |try (exact I || reflexivity) (* ψ *)
  |try (exact I || reflexivity) (* ϕ *)
  |simpl; reflexivity ||  fail "v_pure: this should not happen" (* e' = fill K' e2 *)
  |pm_reduce (* new goal *)].


Tactic Notation "v_pures" open_constr(j) := repeat (v_pure j _).
Tactic Notation "v_pures" := v_pures _.
Tactic Notation "v_rec" constr(j) :=
  let H := fresh in
  assert (H := AsRecV_recv);
  v_pure j (App _ _);
  clear H.
Tactic Notation "v_seq" constr(j) := v_rec j.
Tactic Notation "v_let" constr(j) := v_rec j.
Tactic Notation "v_lam" constr(j) := v_rec j.
Tactic Notation "v_fst" constr(j) := v_pure j (Fst (PairV _ _)).
Tactic Notation "v_snd" constr(j) := v_pure j (Snd (PairV _ _)).
Tactic Notation "v_proj" constr(j) := v_pure j (_ (PairV _ _)).
Tactic Notation "v_case_inl" constr(j) := v_pure j (Case (InjLV _) _ _).
Tactic Notation "v_case_inr" constr(j) := v_pure j (Case (InjRV _) _ _).
Tactic Notation "v_case" constr(j) := v_pure j (Case _ _ _).
Tactic Notation "v_binop" constr(j) := v_pure j (BinOp _ _ _).
Tactic Notation "v_op" constr(j) := v_binop j.
Tactic Notation "v_if_true" constr(j) := v_pure j (If #true _ _).
Tactic Notation "v_if_false" constr(j) := v_pure j (If #false _ _).
Tactic Notation "v_if" constr(j) := v_pure j (If _ _ _).
Tactic Notation "v_pair" constr(j) := v_pure j (Pair _ _).
Tactic Notation "v_closure" constr(j) := v_pure j (Rec _ _ _).

Lemma tac_v_store `{authG Σ} k Δ1 Δ2 E1 i1 i2 K' e (l : loc) e' e2 v' v Q :
  (* TODO: here instead of True we can consider another Coq premise, like in v_pure. *)
(*      Same goes for the rest of those tactics *)
  envs_lookup_delete false i1 Δ1 = Some (false, spec_verifier k e, Δ2)%I →
  (∀ P, ElimModal True false false (|={E1}=> P) P Q Q) →
  nclose specN ⊆ E1 →
  e = fill K' (Store (# l) e') →
  IntoVal e' v →
  (* re-compose the expression and the evaluation context *)
  e2 = fill K' #() →
  envs_lookup i2 Δ2 = Some (false, l ↦ᵥ v')%I →
  match envs_simple_replace i2 false
     (Esnoc (Esnoc Enil i1 (spec_verifier k e2)) i2 (l ↦ᵥ v)) Δ2 with
  | None => False
  | Some Δ3 => envs_entails Δ3 Q
  end →
  envs_entails Δ1 Q.
Proof.
  rewrite /IntoVal.
  rewrite envs_entails_unseal. intros ??? -> <- -> ? HQ.
  rewrite envs_lookup_delete_sound //; simpl.
  destruct (envs_simple_replace _ _ _ _) as [Δ3|] eqn:HΔ3; last done.
  rewrite envs_simple_replace_sound //; simpl.
  rewrite right_id.
  rewrite !assoc.
  rewrite step_verifier_store //.
  rewrite -[Q]elim_modal //.
  apply bi.sep_mono_r.
  apply bi.wand_intro_l.
  rewrite (comm _ _ (l ↦ᵥ v)%I). simpl.
  rewrite assoc.
  by rewrite bi.wand_elim_r.
Qed.

Tactic Notation "v_store" open_constr(j) :=
  iStartProof;
  eapply (tac_v_store j);
  [iAssumptionCore || fail "v_store: cannot find '" j " ' RHS"
  |tc_solve || fail "v_store: cannot eliminate modality in the goal"
  |solve_ndisj || fail "v_store: cannot prove 'nclose specN ⊆ ?'"
  |v_bind_helper
  |tc_solve || fail "v_store: cannot convert the argument to a value"
  |simpl; reflexivity || fail "v_store: this should not happen"
  |iAssumptionCore || fail "v_store: cannot find '? ↦ᵥ ?'"
  |pm_reduce (* new goal *)].

Tactic Notation "v_store" :=
  v_store _.

Lemma tac_v_xchg `{authG Σ} k Δ1 Δ2 E1 i1 i2 K' e (l : loc) e' e2 v' v Q :
  envs_lookup_delete false i1 Δ1 = Some (false, spec_verifier k e, Δ2)%I →
  (∀ P, ElimModal True false false (|={E1}=> P) P Q Q) →
  nclose specN ⊆ E1 →
  e = fill K' (Xchg (# l) e') →
  IntoVal e' v →
  (* re-compose the expression and the evaluation context *)
  envs_lookup i2 Δ2 = Some (false, l ↦ᵥ v')%I →
  e2 = fill K' (of_val v') →
  match envs_simple_replace i2 false
     (Esnoc (Esnoc Enil i1 (spec_verifier k e2)) i2 (l ↦ᵥ v)) Δ2 with
  | None => False
  | Some Δ3 => envs_entails Δ3 Q
  end →
  envs_entails Δ1 Q.
Proof.
  rewrite /IntoVal.
  rewrite envs_entails_unseal. intros ??? -> <- ? -> HQ.
  rewrite envs_lookup_delete_sound //; simpl.
  destruct (envs_simple_replace _ _ _ _) as [Δ3|] eqn:HΔ3; last done.
  rewrite envs_simple_replace_sound //; simpl.
  rewrite right_id.
  rewrite !assoc.
  rewrite step_verifier_xchg //.
  rewrite -[Q]elim_modal //.
  apply bi.sep_mono_r.
  apply bi.wand_intro_l.
  rewrite (comm _ _ (l ↦ᵥ v)%I). simpl.
  rewrite assoc.
  by rewrite bi.wand_elim_r.
Qed.

Tactic Notation "v_xchg" open_constr(j) :=
  iStartProof;
  eapply (tac_v_xchg j);
  [iAssumptionCore || fail "v_xchg: cannot find '" j " ' RHS"
  |tc_solve || fail "v_xchg: cannot eliminate modality in the goal"
  |solve_ndisj || fail "v_xchg: cannot prove 'nclose specN ⊆ ?'"
  |v_bind_helper
  |tc_solve || fail "v_xchg: cannot convert the argument to a value"
  |iAssumptionCore || fail "v_xchg: cannot find '? ↦ᵥ ?'"
  |simpl; reflexivity || fail "v_xchg: this should not happen"
  |pm_reduce (* new goal *)].
Tactic Notation "v_xchg" :=
  v_xchg _.

Lemma tac_v_load `{authG Σ} k Δ1 Δ2 E1 i1 i2 K' e e2 (l : loc) v Q q :
  envs_lookup_delete false i1 Δ1 = Some (false, spec_verifier k e, Δ2)%I →
  (∀ P, ElimModal True false false (|={E1}=> P) P Q Q) →
  nclose specN ⊆ E1 →
  e = fill K' (Load #l) →
  envs_lookup i2 Δ2 = Some (false, l ↦ᵥ{q} v)%I →
  e2 = fill K' (of_val v) →
  match envs_simple_replace i2 false
    (Esnoc (Esnoc Enil i1 (spec_verifier k e2)) i2 (l ↦ᵥ{q} v)%I) Δ2 with
  | Some Δ3 => envs_entails Δ3 Q
  | None    => False
  end →
  envs_entails Δ1 Q.
Proof.
  rewrite envs_entails_unseal. intros ??? -> ? -> HQ.
  rewrite envs_lookup_delete_sound //; simpl.
  destruct (envs_simple_replace _ _ _ _) as [Δ3|] eqn:HΔ3; last done.
  rewrite (envs_simple_replace_sound Δ2 Δ3 i2) //; simpl.
  rewrite /spec_verifier.
  rewrite right_id.
  rewrite assoc.
  rewrite step_verifier_load /= //.
  rewrite -[Q]elim_modal //.
  apply bi.sep_mono_r.
  apply bi.wand_intro_l.
  rewrite (comm _ _ (l ↦ᵥ{q} v)%I).
  rewrite HQ. by apply bi.wand_elim_r.
Qed.

Tactic Notation "v_load" open_constr(j) :=
  iStartProof;
  eapply (tac_v_load j);
  [iAssumptionCore || fail "v_load: cannot find the RHS '" j "'"
  |tc_solve || fail "v_load: cannot eliminate modality in the goal"
  |solve_ndisj || fail "v_load: cannot prove 'nclose specN ⊆ ?'"
  |v_bind_helper
  |iAssumptionCore || fail "v_load: cannot find '? ↦ᵥ ?'"
  |simpl; reflexivity || fail "v_load: this should not happen"
  |pm_reduce (* new goal *)].
Tactic Notation "v_load" :=
  v_load _.

Lemma tac_v_cmpxchg_fail `{authG Σ} k Δ1 Δ2 E1 i1 i2 K' e enew (l : loc) e1 e2 v' v1 v2 Q q :
  envs_lookup_delete false i1 Δ1 = Some (false, spec_verifier k e, Δ2)%I →
  (∀ P, ElimModal True false false (|={E1}=> P) P Q Q) →
  nclose specN ⊆ E1 →
  e = fill K' (CmpXchg #l e1 e2) →
  IntoVal e1 v1 →
  IntoVal e2 v2 →
  envs_lookup i2 Δ2 = Some (false, l ↦ᵥ{q} v')%I →
  v' ≠ v1 →
  vals_compare_safe v' v1 →
  enew = fill K' (v', #false)%V →
  match envs_simple_replace i2 false
    (Esnoc (Esnoc Enil i1 (spec_verifier k enew)) i2 (l ↦ᵥ{q} v')%I) Δ2 with
  | Some Δ3 => envs_entails Δ3 Q
  | None    =>  False
  end →
  envs_entails Δ1 Q.
Proof.
  rewrite envs_entails_unseal. intros ??? -> Hv1 Hv2 ??? -> HQ.
  rewrite envs_lookup_delete_sound //; simpl.
  destruct (envs_simple_replace _ _ _ _) as [Δ3|] eqn:HΔ3; last done.
  rewrite (envs_simple_replace_sound Δ2 Δ3 i2) //; simpl.
  rewrite right_id.
  rewrite /spec_verifier.
  rewrite assoc.
  rewrite step_verifier_cmpxchg_fail //.
  rewrite -[Q]elim_modal //.
  apply bi.sep_mono_r.
  apply bi.wand_intro_l.
  rewrite (comm _ _ (l ↦ᵥ{q} _)%I).
  rewrite HQ. by apply bi.wand_elim_r.
Qed.

Tactic Notation "v_cmpxchg_fail" open_constr(j) :=
  iStartProof;
  eapply (tac_v_cmpxchg_fail j);
  [iAssumptionCore || fail "v_cmpxchg_fail: cannot find the RHS '" j "'"
  |tc_solve || fail "v_cmpxchg_fail: cannot eliminate modality in the goal"
  |solve_ndisj || fail "v_cmpxchg_fail: cannot prove 'nclose specN ⊆ ?'"
  |v_bind_helper (* e = K'[CmpXchg _ _ _] *)
  |tc_solve || fail "v_cmpxchg_fail: argument is not a value"
  |tc_solve || fail "v_cmpxchg_fail: argument is not a value"
  |iAssumptionCore || fail "v_cmpxchg_fail: cannot find '? ↦ ?'"
  |try (simpl; congruence) (* v' ≠ v1 *)
  |try heap_lang.proofmode_upto_bad.solve_vals_compare_safe
  |simpl; reflexivity || fail "v_cmpxchg_fail: this should not happen"
  |pm_reduce (* new goal *)].
Tactic Notation "v_cmpxchg_fail" :=
  v_cmpxchg_fail _.

Lemma tac_v_cmpxchg_suc `{authG Σ} k Δ1 Δ2 E1 i1 i2 K' e enew (l : loc) e1 e2 v' v1 v2 Q :
  envs_lookup_delete false i1 Δ1 = Some (false, spec_verifier k e, Δ2)%I →
  (∀ P, ElimModal True false false (|={E1}=> P) P Q Q) →
  nclose specN ⊆ E1 →
  e = fill K' (CmpXchg #l e1 e2) →
  IntoVal e1 v1 →
  IntoVal e2 v2 →
  envs_lookup i2 Δ2 = Some (false, l ↦ᵥ v')%I →
  v' = v1 →
  vals_compare_safe v' v1 →
  enew = fill K' (v', #true)%V →
  match envs_simple_replace i2 false
    (Esnoc (Esnoc Enil i1 (spec_verifier k enew)) i2 (l ↦ᵥ v2)%I) Δ2 with
  | Some Δ3 => envs_entails Δ3 Q
  | None => False
  end →
  envs_entails Δ1 Q.
Proof.
  rewrite envs_entails_unseal. intros ??? -> Hv1 Hv2 ??? -> HQ.
  rewrite envs_lookup_delete_sound //; simpl.
  destruct (envs_simple_replace _ _ _ _) as [Δ3|] eqn:HΔ3; last done.
  rewrite (envs_simple_replace_sound Δ2 Δ3 i2) //; simpl.
  rewrite right_id.
  rewrite /spec_verifier.
  rewrite assoc.
  rewrite step_verifier_cmpxchg_suc //.
  rewrite -[Q]elim_modal //.
  apply bi.sep_mono_r.
  apply bi.wand_intro_l.
  rewrite (comm _ _ (l ↦ᵥ _)%I) assoc.
  rewrite HQ. by apply bi.wand_elim_r.
Qed.

Tactic Notation "v_cmpxchg_suc" open_constr(j) :=
  iStartProof;
  eapply (tac_v_cmpxchg_suc j);
  [iAssumptionCore || fail "v_cmpxchg_suc: cannot the RHS '" j "'"
  |tc_solve || fail "v_cmpxchg_suc: cannot eliminate modality in the goal"
  |solve_ndisj || fail "v_cmpxchg_suc: cannot prove 'nclose specN ⊆ ?'"
  |v_bind_helper (* e = K'[CmpXchg _ _ _] *)
  |tc_solve || fail "v_cmpxchg_suc: argument is not a value"
  |tc_solve || fail "v_cmpxchg_suc: argument is not a value"
  |iAssumptionCore || fail "v_cmpxchg_suc: cannot find '? ↦ ?'"
  |try (simpl; congruence)     (* v' = v1 *)
  |try heap_lang.proofmode_upto_bad.solve_vals_compare_safe
  |simpl; reflexivity || fail "v_cmpxchg_suc: this should not happen"
  |pm_reduce (* new goal *)].
Tactic Notation "v_cmpxchg_suc" :=
  v_cmpxchg_suc _.

Lemma tac_v_faa `{authG Σ} k Δ1 Δ2 E1 i1 i2 K' e enew (l : loc)  e2 (z1 z2 : Z) Q :
  envs_lookup_delete false i1 Δ1 = Some (false, spec_verifier k e, Δ2)%I →
  (∀ P, ElimModal True false false (|={E1}=> P) P Q Q) →
  nclose specN ⊆ E1 →
  e = fill K' (FAA #l e2) →
  IntoVal e2 #z2 →
  envs_lookup i2 Δ2 = Some (false, l ↦ᵥ #z1)%I →
  enew = fill K' #z1 →
  match envs_simple_replace i2 false
    (Esnoc (Esnoc Enil i1 (spec_verifier k enew)) i2 (l ↦ᵥ #(z1+z2))%I) Δ2 with
    | Some Δ3 =>   envs_entails Δ3 Q
    | None => False
  end →
  envs_entails Δ1 Q.
Proof.
  rewrite envs_entails_unseal. intros ??? -> ?? -> HQ.
  rewrite envs_lookup_delete_sound //; simpl.
  destruct (envs_simple_replace _ _ _ _) as [Δ3|] eqn:HΔ3; last done.
  rewrite (envs_simple_replace_sound Δ2 Δ3 i2) //; simpl.
  rewrite right_id.
  rewrite /spec_verifier.
  rewrite assoc.
  rewrite step_verifier_faa //.
  rewrite -[Q]elim_modal //.
  apply bi.sep_mono_r.
  apply bi.wand_intro_l.
  rewrite (comm _ _ (l ↦ᵥ _)%I) assoc.
  rewrite HQ. by apply bi.wand_elim_r.
Qed.

Tactic Notation "v_faa" open_constr(j) :=
  iStartProof;
  eapply (tac_v_faa j);
  [iAssumptionCore || fail "v_faa: cannot find the RHS '" j "'"
  |tc_solve || fail "v_faa: cannot eliminate modality in the goal"
  |solve_ndisj || fail "v_faa: cannot prove 'nclose specN ⊆ ?'"
  |v_bind_helper (* e = K'[FAA _ _ _] *)
  |tc_solve (* IntoVal *)
  |iAssumptionCore || fail "v_faa: cannot find '? ↦ ?'"
  |simpl;reflexivity || fail "v_faa: this should not happen"
  |pm_reduce (* new goal *)].
Tactic Notation "v_faa" :=
  v_faa _.

Lemma tac_v_fork `{authG Σ} k Δ1 E1 i1 K' e enew e' Q :
  envs_lookup i1 Δ1 = Some (false, spec_verifier k e)%I →
  (∀ P, ElimModal True false false (|={E1}=> P) P Q Q) →
  nclose specN ⊆ E1 →
  e = fill K' (Fork e') →
  enew = fill K' #() →
  match envs_simple_replace i1 false
      (Esnoc Enil i1 (spec_verifier k (fill K' #()))) Δ1 with
  | Some Δ2 => envs_entails Δ2 (∀ k', spec_verifier k' e' -∗ Q)%I
  | None => False
  end →
  envs_entails Δ1 Q.
Proof.
  rewrite envs_entails_unseal. intros ???->-> HQ.
  destruct (envs_simple_replace _ _ _ _) as [Δ2|] eqn:HΔ2; last done.
  rewrite (envs_simple_replace_sound Δ1 Δ2 i1) //; simpl.
  rewrite right_id.
  rewrite step_verifier_fork //.
  rewrite -[Q]elim_modal //.
  apply bi.sep_mono_r.
  apply bi.wand_intro_l.
  rewrite bi.sep_exist_r.
  apply bi.exist_elim. intros j'.
  rewrite -!assoc.
  iIntros "(#Hspec & Hk & Hj' & Hcnt)".
  rewrite HQ.
  iApply ("Hcnt" with "[$Hspec $Hk]").
  by iFrame.
Qed.

Tactic Notation "v_fork" open_constr(j) :=
  iStartProof;
  eapply (tac_v_fork j);
  [iAssumptionCore || fail "v_fork: cannot find the RHS '" j "'"
  |tc_solve || fail "v_fork: cannot eliminate modality in the goal"
  |solve_ndisj || fail "v_fork: cannot prove 'nclose specN ⊆ ?'"
  |v_bind_helper
  |simpl; reflexivity || fail "v_fork: this should not happen"
  |pm_reduce (* new goal *)].
Tactic Notation "v_fork" := v_fork _.

Tactic Notation "v_fork" open_constr(j) "as" ident(j') constr(H) :=
  iStartProof;
  eapply (tac_v_fork j);
  [iAssumptionCore || fail "v_fork: cannot find the RHS '" j "'"
  |tc_solve || fail "v_fork: cannot eliminate modality in the goal"
  |solve_ndisj || fail "v_fork: cannot prove 'nclose specN ⊆ ?'"
  |v_bind_helper
  |simpl; reflexivity || fail "v_fork: this should not happen"
  |pm_reduce;
   (iIntros (j') || fail 1 "v_fork: " j' " not fresh ");
   (iIntros H || fail 1 "v_fork: " H " not fresh")
   (* new goal *)].
Tactic Notation "v_fork" "as" ident(j') constr(H) :=
  v_fork _ as j' H.

Tactic Notation "v_fork" constr(j) "as" ident(j') :=
  let H := iFresh in v_fork j as j' H.

Lemma tac_v_alloc `{authG Σ} k Δ1 E1 i1 K' e e' v Q :
  envs_lookup i1 Δ1 = Some (false, spec_verifier k e)%I →
  (∀ P, ElimModal True false false (|={E1}=> P) P Q Q) →
  nclose specN ⊆ E1 →
  e = fill K' (ref e') →
  IntoVal e' v →
  (* TODO use match here as well *)
  (∀ l : loc, ∃ Δ2,
    envs_simple_replace i1 false
       (Esnoc Enil i1 (spec_verifier k (fill K' #l))) Δ1 = Some Δ2 ∧
    (envs_entails Δ2 ((l ↦ᵥ v) -∗ Q)%I)) →
  envs_entails Δ1 Q.
Proof.
  rewrite envs_entails_unseal. intros ??? Hfill <- HQ.
  rewrite (envs_lookup_sound' Δ1 false i1); last by eassumption.
  rewrite Hfill /=.
  rewrite step_verifier_alloc //.
  rewrite -[Q]elim_modal //.
  apply bi.sep_mono_r, bi.wand_intro_l.
  rewrite bi.sep_exist_r.
  apply bi.exist_elim=> l.
  destruct (HQ l) as (Δ2 & HΔ2 & HQ').
  rewrite (envs_simple_replace_sound' _ _ i1 _ _ HΔ2) /=.
  rewrite HQ' right_id.
  rewrite (comm _ _ (l ↦ᵥ _)%I).
  rewrite assoc.
  rewrite -(assoc _ (l ↦ᵥ _)%I spec_ctx _). rewrite -assoc.
  rewrite bi.wand_elim_r.
  by rewrite bi.wand_elim_r.
Qed.

Tactic Notation "v_alloc" open_constr(j) "as" ident(l) constr(H) :=
  let finish _ :=
      first [ intros l | fail 1 "v_alloc:" l "not fresh"];
        eexists; split;
        [ reduction.pm_reflexivity
        | (iIntros H; v_normalise j) || fail 1 "v_alloc:" H "not correct intro pattern" ] in
  iStartProof;
  eapply (tac_v_alloc j);
  [iAssumptionCore || fail "v_alloc: cannot find the RHS '" j "'"
  |tc_solve || fail "v_alloc: cannot eliminate modality in the goal"
  |solve_ndisj || fail "v_alloc: cannot prove 'nclose specN ⊆ ?'"
  |v_bind_helper
  |tc_solve || fail "v_alloc: expressions is not a value"
  |finish ()
   (* new goal *)].
Tactic Notation "v_alloc" "as" ident(l) constr(H) :=
  v_alloc _ as l H.

Tactic Notation "v_alloc" constr(j) "as" ident(j') :=
  let H := iFresh in v_alloc j as j' H.

(** * Ideal tactics *)

(** ** bind *)
Lemma tac_i_bind_gen `{authG Σ} k Δ Δ' i p e e' Q :
  envs_lookup i Δ = Some (p, spec_ideal k e)%I →
  e = e' →
  envs_simple_replace i p (Esnoc Enil i (spec_ideal k e')) Δ = Some Δ' →
  (envs_entails Δ' Q) →
  (envs_entails Δ Q).
Proof.
  rewrite envs_entails_unseal. intros; subst. simpl.
  rewrite envs_simple_replace_sound // /=.
  destruct p; rewrite /= ?right_id; by rewrite bi.wand_elim_r.
Qed.

Lemma tac_i_bind `{authG Σ} k e' Δ Δ' i p K' e Q :
  envs_lookup i Δ = Some (p, spec_ideal k e)%I →
  e = fill K' e' →
  envs_simple_replace i p (Esnoc Enil i (spec_ideal k (fill K' e'))) Δ = Some Δ' →
  (envs_entails Δ' Q) →
  (envs_entails Δ Q).
Proof. intros. by eapply tac_i_bind_gen. Qed.

Ltac i_bind_helper :=
  simpl;
  lazymatch goal with
  | |- fill ?K ?e = fill _ ?efoc =>
     reshape_expr e ltac:(fun K' e' =>
       unify e' efoc;
       let K'' := eval cbn[app] in (K' ++ K) in
       replace (fill K e) with (fill K'' e') by (by rewrite ?fill_app))
  | |- ?e = fill _ ?efoc =>
     reshape_expr e ltac:(fun K' e' =>
       unify e' efoc;
       replace e with (fill K' e') by (by rewrite ?fill_app))
  end; reflexivity.

Tactic Notation "i_normalise" constr(j) :=
  iStartProof;
  eapply (tac_i_bind_gen j);
    [iAssumptionCore (* prove the lookup *)
    | lazymatch goal with
      | |- fill ?K ?e = _ =>
          by rewrite /= ?fill_app /=
      | |- ?e = _ => try fast_done
      end
    |reflexivity
    |(* new goal *)].

Tactic Notation "i_bind" open_constr(j) open_constr(efoc) :=
  iStartProof;
  eapply (tac_i_bind j efoc);
    [iAssumptionCore (* prove the lookup *)
    |i_bind_helper (* do actual work *)
    |reflexivity
    |(* new goal *)].
Tactic Notation "i_bind" open_constr(efoc) :=
  i_bind _ efoc.
Lemma tac_i_pure `{authG Σ} e K' e1 k e2 Δ1 E1 i1 e' ϕ ψ Q n :
  (* we have those premises first, because we will be trying to solve them *)
(*      with backtracking using reashape_expr; see the accompanying Ltac. *)
(*      the first premise decomposes the expression, the second one checks *)
(*      that we can make a pure step *)
  e = fill K' e1 →
  PureExec ϕ n e1 e2 →
  (∀ P, ElimModal ψ false false (|={E1}=> P) P Q Q) →
  nclose specN ⊆ E1 →
  envs_lookup i1 Δ1 = Some (false, spec_ideal k e)%I →
  ψ →
  ϕ →
  (* we will call simpl on this goal thus re-composing the expression again *)
  e' = fill K' e2 →
  match envs_simple_replace i1 false (Esnoc Enil i1 (spec_ideal k e')) Δ1 with
  | Some Δ2 => envs_entails Δ2 Q
  | None => False
  end →
  envs_entails Δ1 Q.
Proof.
  rewrite envs_entails_unseal. intros -> Hpure ?? HΔ1 Hψ Hϕ -> ?.
  destruct (envs_simple_replace _ _ _ _) as [Δ2|] eqn:HΔ2; try done.
  rewrite (envs_simple_replace_sound Δ1 Δ2 i1) //; simpl.
  rewrite right_id.
  rewrite step_ideal_pure //.
  rewrite -[Q]elim_modal // /=.
  apply bi.sep_mono_r.
  apply bi.wand_intro_l.
  by rewrite bi.wand_elim_r.
Qed.

Tactic Notation "i_pure" constr(j) open_constr(ef) :=
  iStartProof;
  lazymatch goal with
  | |- context[environments.Esnoc _ ?H (spec_ideal j (fill ?K' ?e))] =>
    reshape_expr e ltac:(fun K e' =>
      unify e' ef;
      eapply (tac_i_pure (fill K' e) (K++K') e' j);
      [by rewrite ?fill_app | tc_solve | ..])
  | |- context[environments.Esnoc _ ?H (spec_ideal j ?e)] =>
    reshape_expr e ltac:(fun K e' =>
      unify e' ef;
      eapply (tac_i_pure e K e' j);
      [by rewrite ?fill_app | tc_solve | ..])
  end;
  [tc_solve || fail "i_pure: cannot eliminate modality in the goal"
  |solve_ndisj || fail "i_pure: cannot prove 'nclose specN ⊆ ?'"
  |iAssumptionCore || fail "i_pure: cannot find the RHS" (* TODO fix error message *)
  |try (exact I || reflexivity) (* ψ *)
  |try (exact I || reflexivity) (* ϕ *)
  |simpl; reflexivity ||  fail "i_pure: this should not happen" (* e' = fill K' e2 *)
  |pm_reduce (* new goal *)].

Tactic Notation "i_pures" open_constr (j) := repeat (i_pure j _).
Tactic Notation "i_pures" := i_pures _.
Tactic Notation "i_rec" constr(j) :=
  let H := fresh in
  assert (H := AsRecV_recv);
  i_pure j (App _ _);
  clear H.
Tactic Notation "i_seq" constr(j) := i_rec j.
Tactic Notation "i_let" constr(j) := i_rec j.
Tactic Notation "i_lam" constr(j) := i_rec j.
Tactic Notation "i_fst" constr(j) := i_pure j (Fst (PairV _ _)).
Tactic Notation "i_snd" constr(j) := i_pure j (Snd (PairV _ _)).
Tactic Notation "i_proj" constr(j) := i_pure j (_ (PairV _ _)).
Tactic Notation "i_case_inl" constr(j) := i_pure j (Case (InjLV _) _ _).
Tactic Notation "i_case_inr" constr(j) := i_pure j (Case (InjRV _) _ _).
Tactic Notation "i_case" constr(j) := i_pure j (Case _ _ _).
Tactic Notation "i_binop" constr(j) := i_pure j (BinOp _ _ _).
Tactic Notation "i_op" constr(j) := i_binop j.
Tactic Notation "i_if_true" constr(j) := i_pure j (If #true _ _).
Tactic Notation "i_if_false" constr(j) := i_pure j (If #false _ _).
Tactic Notation "i_if" constr(j) := i_pure j (If _ _ _).
Tactic Notation "i_pair" constr(j) := i_pure j (Pair _ _).
Tactic Notation "i_closure" constr(j) := i_pure j (Rec _ _ _).

Lemma tac_i_store `{authG Σ} k Δ1 Δ2 E1 i1 i2 K' e (l : loc) e' e2 v' v Q :
  envs_lookup_delete false i1 Δ1 = Some (false, spec_ideal k e, Δ2)%I →
  (∀ P, ElimModal True false false (|={E1}=> P) P Q Q) →
  nclose specN ⊆ E1 →
  e = fill K' (Store (# l) e') →
  IntoVal e' v →
  (* re-compose the expression and the evaluation context *)
  e2 = fill K' #() →
  envs_lookup i2 Δ2 = Some (false, l ↦ᵢ v')%I →
  match envs_simple_replace i2 false
     (Esnoc (Esnoc Enil i1 (spec_ideal k e2)) i2 (l ↦ᵢ v)) Δ2 with
  | None => False
  | Some Δ3 => envs_entails Δ3 Q
  end →
  envs_entails Δ1 Q.
Proof.
  rewrite /IntoVal.
  rewrite envs_entails_unseal. intros ??? -> <- -> ? HQ.
  rewrite envs_lookup_delete_sound //; simpl.
  destruct (envs_simple_replace _ _ _ _) as [Δ3|] eqn:HΔ3; last done.
  rewrite envs_simple_replace_sound //; simpl.
  rewrite right_id.
  rewrite !assoc.
  rewrite step_ideal_store //.
  rewrite -[Q]elim_modal //.
  apply bi.sep_mono_r.
  apply bi.wand_intro_l.
  rewrite (comm _ _ (l ↦ᵢ v)%I). simpl.
  rewrite assoc.
  by rewrite bi.wand_elim_r.
Qed.

Tactic Notation "i_store" open_constr(j) :=
  iStartProof;
  eapply (tac_i_store j);
  [iAssumptionCore || fail "i_store: cannot find '" j " ' RHS"
  |tc_solve || fail "i_store: cannot eliminate modality in the goal"
  |solve_ndisj || fail "i_store: cannot prove 'nclose specN ⊆ ?'"
  |i_bind_helper
  |tc_solve || fail "i_store: cannot convert the argument to a value"
  |simpl; reflexivity || fail "i_store: this should not happen"
  |iAssumptionCore || fail "i_store: cannot find '? ↦ᵢ ?'"
  |pm_reduce (* new goal *)].
Tactic Notation "i_store" :=
  i_store _.

Lemma tac_i_xchg `{authG Σ} k Δ1 Δ2 E1 i1 i2 K' e (l : loc) e' e2 v' v Q :
  envs_lookup_delete false i1 Δ1 = Some (false, spec_ideal k e, Δ2)%I →
  (∀ P, ElimModal True false false (|={E1}=> P) P Q Q) →
  nclose specN ⊆ E1 →
  e = fill K' (Xchg (# l) e') →
  IntoVal e' v →
  (* re-compose the expression and the evaluation context *)
  envs_lookup i2 Δ2 = Some (false, l ↦ᵢ v')%I →
  e2 = fill K' (of_val v') →
  match envs_simple_replace i2 false
     (Esnoc (Esnoc Enil i1 (spec_ideal k e2)) i2 (l ↦ᵢ v)) Δ2 with
  | None => False
  | Some Δ3 => envs_entails Δ3 Q
  end →
  envs_entails Δ1 Q.
Proof.
  rewrite /IntoVal.
  rewrite envs_entails_unseal. intros ??? -> <- ? -> HQ.
  rewrite envs_lookup_delete_sound //; simpl.
  destruct (envs_simple_replace _ _ _ _) as [Δ3|] eqn:HΔ3; last done.
  rewrite envs_simple_replace_sound //; simpl.
  rewrite right_id.
  rewrite !assoc.
  rewrite step_ideal_xchg //.
  rewrite -[Q]elim_modal //.
  apply bi.sep_mono_r.
  apply bi.wand_intro_l.
  rewrite (comm _ _ (l ↦ᵢ v)%I). simpl.
  rewrite assoc.
  by rewrite bi.wand_elim_r.
Qed.

Tactic Notation "i_xchg" open_constr(j) :=
  iStartProof;
  eapply (tac_i_xchg j);
  [iAssumptionCore || fail "i_xchg: cannot find '" j " ' RHS"
  |tc_solve || fail "i_xchg: cannot eliminate modality in the goal"
  |solve_ndisj || fail "i_xchg: cannot prove 'nclose specN ⊆ ?'"
  |i_bind_helper
  |tc_solve || fail "i_xchg: cannot convert the argument to a value"
  |iAssumptionCore || fail "i_xchg: cannot find '? ↦ᵢ ?'"
  |simpl; reflexivity || fail "i_xchg: this should not happen"
  |pm_reduce (* new goal *)].
Tactic Notation "i_xchg" :=
  i_xchg _.

Lemma tac_i_load `{authG Σ} k Δ1 Δ2 E1 i1 i2 K' e e2 (l : loc) v Q q :
  envs_lookup_delete false i1 Δ1 = Some (false, spec_ideal k e, Δ2)%I →
  (∀ P, ElimModal True false false (|={E1}=> P) P Q Q) →
  nclose specN ⊆ E1 →
  e = fill K' (Load #l) →
  envs_lookup i2 Δ2 = Some (false, l ↦ᵢ{q} v)%I →
  e2 = fill K' (of_val v) →
  match envs_simple_replace i2 false
    (Esnoc (Esnoc Enil i1 (spec_ideal k e2)) i2 (l ↦ᵢ{q} v)%I) Δ2 with
  | Some Δ3 => envs_entails Δ3 Q
  | None    => False
  end →
  envs_entails Δ1 Q.
Proof.
  rewrite envs_entails_unseal. intros ??? -> ? -> HQ.
  rewrite envs_lookup_delete_sound //; simpl.
  destruct (envs_simple_replace _ _ _ _) as [Δ3|] eqn:HΔ3; last done.
  rewrite (envs_simple_replace_sound Δ2 Δ3 i2) //; simpl.
  rewrite /spec_ideal.
  rewrite right_id.
  rewrite assoc.
  rewrite step_ideal_load /= //.
  rewrite -[Q]elim_modal //.
  apply bi.sep_mono_r.
  apply bi.wand_intro_l.
  rewrite (comm _ _ (l ↦ᵢ{q} v)%I).
  rewrite assoc.
  rewrite HQ. by apply bi.wand_elim_r.
Qed.

Tactic Notation "i_load" open_constr(j) :=
  iStartProof;
  eapply (tac_i_load j);
  [iAssumptionCore || fail "i_load: cannot find the RHS '" j "'"
  |tc_solve || fail "i_load: cannot eliminate modality in the goal"
  |solve_ndisj || fail "i_load: cannot prove 'nclose specN ⊆ ?'"
  |i_bind_helper
  |iAssumptionCore || fail "i_load: cannot find '? ↦ᵢ ?'"
  |simpl; reflexivity || fail "i_load: this should not happen"
  |pm_reduce (* new goal *)].
Tactic Notation "i_load" :=
  i_load _.

Lemma tac_i_cmpxchg_fail `{authG Σ} k Δ1 Δ2 E1 i1 i2 K' e enew (l : loc) e1 e2 v' v1 v2 Q q :
  envs_lookup_delete false i1 Δ1 = Some (false, spec_ideal k e, Δ2)%I →
  (∀ P, ElimModal True false false (|={E1}=> P) P Q Q) →
  nclose specN ⊆ E1 →
  e = fill K' (CmpXchg #l e1 e2) →
  IntoVal e1 v1 →
  IntoVal e2 v2 →
  envs_lookup i2 Δ2 = Some (false, l ↦ᵢ{q} v')%I →
  v' ≠ v1 →
  vals_compare_safe v' v1 →
  enew = fill K' (v', #false)%V →
  match envs_simple_replace i2 false
    (Esnoc (Esnoc Enil i1 (spec_ideal k enew)) i2 (l ↦ᵢ{q} v')%I) Δ2 with
  | Some Δ3 => envs_entails Δ3 Q
  | None    =>  False
  end →
  envs_entails Δ1 Q.
Proof.
  rewrite envs_entails_unseal. intros ??? -> Hv1 Hv2 ??? -> HQ.
  rewrite envs_lookup_delete_sound //; simpl.
  destruct (envs_simple_replace _ _ _ _) as [Δ3|] eqn:HΔ3; last done.
  rewrite (envs_simple_replace_sound Δ2 Δ3 i2) //; simpl.
  rewrite right_id.
  rewrite /spec_ideal.
  rewrite assoc.
  rewrite step_ideal_cmpxchg_fail //.
  rewrite -[Q]elim_modal //.
  apply bi.sep_mono_r.
  apply bi.wand_intro_l.
  rewrite (comm _ _ (l ↦ᵢ{q} _)%I).
  rewrite assoc.
  rewrite HQ. by apply bi.wand_elim_r.
Qed.

Tactic Notation "i_cmpxchg_fail" open_constr(j) :=
  iStartProof;
  eapply (tac_i_cmpxchg_fail j);
  [iAssumptionCore || fail "i_cmpxchg_fail: cannot find the RHS '" j "'"
  |tc_solve || fail "i_cmpxchg_fail: cannot eliminate modality in the goal"
  |solve_ndisj || fail "i_cmpxchg_fail: cannot prove 'nclose specN ⊆ ?'"

  |i_bind_helper (* e = K'[CmpXchg _ _ _] *)
  |tc_solve || fail "i_cmpxchg_fail: argument is not a value"
  |tc_solve || fail "i_cmpxchg_fail: argument is not a value"
  |iAssumptionCore || fail "i_cmpxchg_fail: cannot find '? ↦ ?'"
  |try (simpl; congruence) (* v' ≠ v1 *)
  |try heap_lang.proofmode_upto_bad.solve_vals_compare_safe
  |simpl; reflexivity || fail "i_cmpxchg_fail: this should not happen"
  |pm_reduce (* new goal *)].
Tactic Notation "i_cmpxchg_fail" :=
  i_cmpxchg_fail _.

Lemma tac_i_cmpxchg_suc `{authG Σ} k Δ1 Δ2 E1 i1 i2 K' e enew (l : loc) e1 e2 v' v1 v2 Q :
  envs_lookup_delete false i1 Δ1 = Some (false, spec_ideal k e, Δ2)%I →
  (∀ P, ElimModal True false false (|={E1}=> P) P Q Q) →
  nclose specN ⊆ E1 →
  e = fill K' (CmpXchg #l e1 e2) →
  IntoVal e1 v1 →
  IntoVal e2 v2 →
  envs_lookup i2 Δ2 = Some (false, l ↦ᵢ v')%I →
  v' = v1 →
  vals_compare_safe v' v1 →
  enew = fill K' (v', #true)%V →
  match envs_simple_replace i2 false
    (Esnoc (Esnoc Enil i1 (spec_ideal k enew)) i2 (l ↦ᵢ v2)%I) Δ2 with
  | Some Δ3 => envs_entails Δ3 Q
  | None => False
  end →
  envs_entails Δ1 Q.
Proof.
  rewrite envs_entails_unseal. intros ??? -> Hv1 Hv2 ??? -> HQ.
  rewrite envs_lookup_delete_sound //; simpl.
  destruct (envs_simple_replace _ _ _ _) as [Δ3|] eqn:HΔ3; last done.
  rewrite (envs_simple_replace_sound Δ2 Δ3 i2) //; simpl.
  rewrite right_id.
  rewrite /spec_ideal.
  rewrite assoc.
  rewrite step_ideal_cmpxchg_suc //.
  rewrite -[Q]elim_modal //.
  apply bi.sep_mono_r.
  apply bi.wand_intro_l.
  rewrite (comm _ _ (l ↦ᵢ _)%I) assoc.
  rewrite HQ. by apply bi.wand_elim_r.
Qed.

Tactic Notation "i_cmpxchg_suc" open_constr(j) :=
  iStartProof;
  eapply (tac_i_cmpxchg_suc j);
  [iAssumptionCore || fail "i_cmpxchg_suc: cannot the RHS '" j "'"
  |tc_solve || fail "i_cmpxchg_suc: cannot eliminate modality in the goal"
  |solve_ndisj || fail "i_cmpxchg_suc: cannot prove 'nclose specN ⊆ ?'"
  |i_bind_helper (* e = K'[CmpXchg _ _ _] *)
  |tc_solve || fail "i_cmpxchg_suc: argument is not a value"
  |tc_solve || fail "i_cmpxchg_suc: argument is not a value"
  |iAssumptionCore || fail "i_cmpxchg_suc: cannot find '? ↦ ?'"
  |try (simpl; congruence)     (* v' = v1 *)
  |try heap_lang.proofmode_upto_bad.solve_vals_compare_safe
  |simpl; reflexivity || fail "i_cmpxchg_suc: this should not happen"
  |pm_reduce (* new goal *)].
Tactic Notation "i_cmpxchg_suc" :=
  i_cmpxchg_suc _.

Lemma tac_i_faa `{authG Σ} k Δ1 Δ2 E1 i1 i2 K' e enew (l : loc)  e2 (z1 z2 : Z) Q :
  envs_lookup_delete false i1 Δ1 = Some (false, spec_ideal k e, Δ2)%I →
  (∀ P, ElimModal True false false (|={E1}=> P) P Q Q) →
  nclose specN ⊆ E1 →
  e = fill K' (FAA #l e2) →
  IntoVal e2 #z2 →
  envs_lookup i2 Δ2 = Some (false, l ↦ᵢ #z1)%I →
  enew = fill K' #z1 →
  match envs_simple_replace i2 false
    (Esnoc (Esnoc Enil i1 (spec_ideal k enew)) i2 (l ↦ᵢ #(z1+z2))%I) Δ2 with
    | Some Δ3 =>   envs_entails Δ3 Q
    | None => False
  end →
  envs_entails Δ1 Q.
Proof.
  rewrite envs_entails_unseal. intros ??? -> ?? -> HQ.
  rewrite envs_lookup_delete_sound //; simpl.
  destruct (envs_simple_replace _ _ _ _) as [Δ3|] eqn:HΔ3; last done.
  rewrite (envs_simple_replace_sound Δ2 Δ3 i2) //; simpl.
  rewrite right_id.
  rewrite /spec_ideal.
  rewrite assoc.
  rewrite step_ideal_faa //.
  rewrite -[Q]elim_modal //.
  apply bi.sep_mono_r.
  apply bi.wand_intro_l.
  rewrite (comm _ _ (l ↦ᵢ _)%I) assoc.
  rewrite HQ. by apply bi.wand_elim_r.
Qed.

Tactic Notation "i_faa" open_constr(j) :=
  iStartProof;
  eapply (tac_i_faa j);
  [iAssumptionCore || fail "i_faa: cannot find the RHS '" j "'"
  |tc_solve || fail "i_faa: cannot eliminate modality in the goal"
  |solve_ndisj || fail "i_faa: cannot prove 'nclose specN ⊆ ?'"
  |i_bind_helper (* e = K'[FAA _ _ _] *)
  |tc_solve (* IntoVal *)
  |iAssumptionCore || fail "i_faa: cannot find '? ↦ ?'"
  |simpl;reflexivity || fail "i_faa: this should not happen"
  |pm_reduce (* new goal *)].
Tactic Notation "i_faa" :=
  i_faa _.

Lemma tac_i_fork `{authG Σ} k Δ1 E1 i1 K' e enew e' Q :
  envs_lookup i1 Δ1 = Some (false, spec_ideal k e)%I →
  (∀ P, ElimModal True false false (|={E1}=> P) P Q Q) →
  nclose specN ⊆ E1 →
  e = fill K' (Fork e') →
  enew = fill K' #() →
  match envs_simple_replace i1 false
      (Esnoc Enil i1 (spec_ideal k (fill K' #()))) Δ1 with
  | Some Δ2 => envs_entails Δ2 (∀ k', spec_ideal k' e' -∗ Q)%I
  | None => False
  end →
  envs_entails Δ1 Q.
Proof.
  rewrite envs_entails_unseal. intros ???->-> HQ.
  destruct (envs_simple_replace _ _ _ _) as [Δ2|] eqn:HΔ2; last done.
  rewrite (envs_simple_replace_sound Δ1 Δ2 i1) //; simpl.
  rewrite right_id.
  rewrite step_ideal_fork //.
  rewrite -[Q]elim_modal //.
  apply bi.sep_mono_r.
  apply bi.wand_intro_l.
  rewrite bi.sep_exist_r.
  apply bi.exist_elim. intros j'.
  rewrite -!assoc.
  iIntros "(#Hspec & Hk & Hj' & Hcnt)".
  rewrite HQ.
  iApply ("Hcnt" with "[$Hspec $Hk]").
  by iFrame.
Qed.

Tactic Notation "i_fork" open_constr(j) :=
  iStartProof;
  eapply (tac_i_fork j);
  [iAssumptionCore || fail "i_fork: cannot find the RHS '" j "'"
  |tc_solve || fail "i_fork: cannot eliminate modality in the goal"
  |solve_ndisj || fail "i_fork: cannot prove 'nclose specN ⊆ ?'"
  |i_bind_helper
  |simpl; reflexivity || fail "i_fork: this should not happen"
  |pm_reduce (* new goal *)].
Tactic Notation "i_fork" :=
  i_fork _.

Tactic Notation "i_fork" open_constr(j) "as" ident(j') constr(H) :=
  iStartProof;
  eapply (tac_i_fork j);
  [iAssumptionCore || fail "i_fork: cannot find the RHS '" j "'"
  |tc_solve || fail "i_fork: cannot eliminate modality in the goal"
  |solve_ndisj || fail "i_fork: cannot prove 'nclose specN ⊆ ?'"
  |i_bind_helper
  |simpl; reflexivity || fail "i_fork: this should not happen"
  |pm_reduce;
   (iIntros (j') || fail 1 "i_fork: " j' " not fresh ");
   (iIntros H || fail 1 "i_fork: " H " not fresh")
   (* new goal *)].
Tactic Notation "i_fork" "as" ident(j') constr(H) :=
  i_fork _ as j' H.

Tactic Notation "i_fork" constr(j) "as" ident(j') :=
  let H := iFresh in i_fork j as j' H.

Lemma tac_i_alloc `{authG Σ} k Δ1 E1 i1 K' e e' v Q :
  envs_lookup i1 Δ1 = Some (false, spec_ideal k e)%I →
  (∀ P, ElimModal True false false (|={E1}=> P) P Q Q) →
  nclose specN ⊆ E1 →
  e = fill K' (ref e') →
  IntoVal e' v →
  (* TODO use match here as well *)
  (∀ l : loc, ∃ Δ2,
    envs_simple_replace i1 false
       (Esnoc Enil i1 (spec_ideal k (fill K' #l))) Δ1 = Some Δ2 ∧
    (envs_entails Δ2 ((l ↦ᵢ v) -∗ Q)%I)) →
  envs_entails Δ1 Q.
Proof.
  rewrite envs_entails_unseal. intros ??? Hfill <- HQ.
  rewrite (envs_lookup_sound' Δ1 false i1); last by eassumption.
  rewrite Hfill /=.
  rewrite step_ideal_alloc //.
  rewrite -[Q]elim_modal //.
  apply bi.sep_mono_r, bi.wand_intro_l.
  rewrite bi.sep_exist_r.
  apply bi.exist_elim=> l.
  destruct (HQ l) as (Δ2 & HΔ2 & HQ').
  rewrite (envs_simple_replace_sound' _ _ i1 _ _ HΔ2) /=.
  rewrite HQ' right_id.
  rewrite (comm _ _ (l ↦ᵢ _)%I).
  rewrite assoc.
  rewrite -(assoc _ (l ↦ᵢ _)%I spec_ctx _).
  rewrite -assoc.
  rewrite bi.wand_elim_r.
  by rewrite bi.wand_elim_r.
Qed.

Tactic Notation "i_alloc" open_constr(j) "as" ident(l) constr(H) :=
  let finish _ :=
      first [ intros l | fail 1 "i_alloc:" l "not fresh"];
        eexists; split;
        [ reduction.pm_reflexivity
        | (iIntros H; i_normalise j) || fail 1 "i_alloc:" H "not correct intro pattern" ] in
  iStartProof;
  eapply (tac_i_alloc j);
  [iAssumptionCore || fail "i_alloc: cannot find the RHS '" j "'"
  |tc_solve || fail "i_alloc: cannot eliminate modality in the goal"
  |solve_ndisj || fail "i_alloc: cannot prove 'nclose specN ⊆ ?'"
  |i_bind_helper
  |tc_solve || fail "i_alloc: expressions is not a value"
  |finish ()
   (* new goal *)].
Tactic Notation "i_alloc" "as" ident(l) constr(H) :=
  i_alloc _ as l H.

Tactic Notation "i_alloc" open_constr(j) "as" ident(j') :=
  let H := iFresh in i_alloc j as j' H.
Tactic Notation "i_alloc" "as" ident(j') :=
  i_alloc _ as j'.
