(** interpretations for System F_mu_ref types *)
From iris.algebra Require Export list.
From iris.proofmode Require Import proofmode.

From auth.typing Require Export types typing.
From auth.rel_logic_tern Require Import model.
From auth.prelude Require Import properness.

(** * Interpretation of kinds *)
Fixpoint kindO (Σ : gFunctors) (κ : kind) : ofe :=
  match κ with
  | KType => lrelC Σ
  | KArrow κ1 κ2 => kindO Σ κ1 -n> kindO Σ κ2
  end.

#[global] Instance kindO_cofe (Σ : gFunctors) (κ : kind) :
  Cofe (kindO Σ κ).
Proof. induction κ; apply _. Qed.

#[global] Instance kindO_Inhabited (Σ : gFunctors) (κ : kind) :
  Inhabited (kindO Σ κ).
Proof. induction κ; apply _. Qed.

(** * The OFE structure on well-kinded type contexts *)
Section interp_ctx.
  Context (Σ : gFunctors).

  Definition interp_ctx (Θ : Ctx kind) : Type :=
    ∀ x : dom Θ, kindO Σ (Θ x).

  #[global] Instance interp_ctx_equiv Θ : Equiv (interp_ctx Θ) := λ Δ1 Δ2, ∀ (x : dom Θ), Δ1 x ≡ Δ2 x.
  #[global] Instance interp_ctx_dist Θ : Dist (interp_ctx Θ) := λ n Δ1 Δ2, ∀ (x : dom Θ), Δ1 x ≡{n}≡ Δ2 x.
  Lemma interp_ctx_ofe_mixin Θ : OfeMixin (interp_ctx Θ).
  Proof.
    constructor.
    - intros Δ1 Δ2. split.
      + intros Heq n m. apply equiv_dist. f_equiv.
      + intros Hn x. apply equiv_dist => n. apply Hn.
    - intros n. constructor.
      + intros Δ1 x. f_equiv.
      + intros Δ1 Δ2 Heq x. rewrite Heq //.
      + intros Δ1 Δ2 Δ3 HeqA HeqB x. rewrite HeqA HeqB //.
    - intros n m Δ1 Δ2 Heq Hlt b. by eapply dist_lt.
  Qed.
  Canonical Structure ctxO Θ := Ofe (interp_ctx Θ) (interp_ctx_ofe_mixin Θ).

End interp_ctx.

(** * Interpretation of types *)
Section semtypes.
  Context `{authG Σ}.

  Definition empty_ctx : ctxO Σ ε := λ x, match x with end.

  #[global] Instance : Empty (ctxO Σ ε) := empty_ctx.

  Program Definition ext {Σ Θ κ} : ctxO Σ Θ -n> kindO Σ κ -n> ctxO Σ (Θ ▹ κ) :=
    λne Δ A, Inc.maybe Δ A.
  Next Obligation. solve_proper. Qed.
  Next Obligation. by intros ???? ??? ? [|?] => /=. Qed.

  Program Definition interp_tvar {Θ : Ctx kind} {κ : kind} (x : dom Θ) (EQ : Θ x = κ) : ctxO Σ Θ -n> kindO Σ κ :=
    λne Δ, eq_rect (Θ x) (kindO Σ) (Δ x) κ EQ.
  Solve Obligations with solve_proper.

  Program Definition interp_tlam {Θ κ1 κ2} (A2 : ctxO Σ (Θ ▹ κ1) -n> kindO Σ κ2) :
    ctxO Σ Θ -n> kindO Σ (κ1 ⇒ κ2) := λne Δ A1, A2 (ext Δ A1).
  Solve Obligations with (intros ????????? => /=; f_equiv; solve_proper).

  Program Definition interp_tapp {Θ κ1 κ2} (A : ctxO Σ Θ -n> kindO Σ (κ1 ⇒ κ2))
    (B : ctxO Σ Θ -n> kindO Σ κ1) : ctxO Σ Θ -n> kindO Σ κ2 := λne Δ, (A Δ) (B Δ).
  Solve Obligations with solve_proper.

  Program Fixpoint interp_rec1 {κ} : (kindO Σ κ -n> kindO Σ κ) -n> kindO Σ κ -n> kindO Σ κ :=
    match κ with
    | ⋆%kind => λne C rec, lrel_rec1 C rec
    | (κ1 ⇒ κ2)%kind => λne C rec A, interp_rec1 cid (C rec A)
    end.
  Solve Obligations with solve_proper.

  Global Instance interp_rec1_contractive {κ} (C : kindO Σ κ -n> kindO Σ κ) : Contractive (interp_rec1 C).
  Proof.
    induction κ => n P Q HPQ.
    - by f_contractive.
    - intros κ. eapply IHκ2. dist_later_intro. solve_proper.
  Qed.

  Lemma interp_rec1_shift κ (C : kindO Σ κ -n> kindO Σ κ) (res : kindO Σ κ) :
    interp_rec1 C res ≡ interp_rec1 cid (C res).
  Proof. by destruct κ. Qed.

  Program Definition interp_rec {κ} : (kindO Σ κ -n> kindO Σ κ) -n> kindO Σ κ :=
    λne C, fixpoint (interp_rec1 C).
  Next Obligation.
    intros κ n F F' HF.
    apply fixpoint_ne=> X.
    solve_proper.
  Qed.

  Lemma interp_rec_unfold {κ} (C : kindO Σ κ -n> kindO Σ κ) :
    interp_rec C ≡ interp_rec1 C (interp_rec C).
  Proof. apply fixpoint_unfold. Qed.

  #[global] Opaque interp_rec.

  Definition interp_tconstr {Θ κ} (c : tconstr κ) : ctxO Σ Θ -n> kindO Σ κ := λne _,
    match c in tconstr κ return kindO Σ κ with
    | TUnit => lrel_unit
    | TNat => lrel_int
    | TBool => lrel_bool
    | TString => lrel_string
    | TProd => lrel_prod
    | TSum => lrel_sum
    | TArrow => lrel_arr
    | TRef => lrel_ref
    | TRec κ => interp_rec
    | TForall κ => lrel_forall
    | TExists κ => lrel_exists
    end.

  Fixpoint interp {Θ : Ctx kind} {κ : kind} (τ : typ κ Θ) : ctxO Σ Θ -n> kindO Σ κ :=
    match τ in type _ κ return ctxO Σ Θ -n> kindO Σ κ with
    | TVar x EQ => interp_tvar x EQ
    | TLam τ => interp_tlam (interp τ)
    | TApp τ τ' => interp_tapp (interp τ) (interp τ')
    | TConstr c => interp_tconstr c
    end.

  Lemma unboxed_type_sound Θ (τ : type Θ ⋆) Δ v v' v'' :
    UnboxedType τ →
    interp τ Δ v v' v'' ⊢
      ⌜val_is_unboxed v ∧ val_is_unboxed v' ∧ val_is_unboxed v''⌝.
  Proof.
    induction 1; simpl;
    first [iDestruct 1 as (? ?) "[% [% (% & % & ?)]]"
          |iDestruct 1 as (?) "[% [% %]]"
          |iIntros "[% [% %]]"];
    simplify_eq/=; eauto with iFrame.
  Qed.

  Lemma eq_type_sound Θ (τ : type Θ ⋆) Δ v v' v'' :
    EqType τ →
    interp τ Δ v v' v'' ⊢ ⌜v = v' ∧ v' = v''⌝.
  Proof.
    intros Hτ; revert v v' v''; induction Hτ; iIntros (v v' v'') "#H1 /=".
    - by iDestruct "H1" as %(-> & -> & ->).
    - by iDestruct "H1" as (n) "(% & % & %)"; subst.
    - by iDestruct "H1" as (b) "(% & % & %)"; subst.
    - by iDestruct "H1" as (b) "(% & % & %)"; subst.
    - iDestruct "H1" as (?? ??) "(% & % & % & % & % & H1 & H2)"; simplify_eq/=.
      rewrite IHHτ1 IHHτ2.
      by iDestruct "H1" as %[? ?]; iDestruct "H2" as %[? ?]; subst.
    - iDestruct "H1" as (???) "[(%&%&%&H1)|(%&%&%&H1)]"; simplify_eq.
      + rewrite IHHτ1. by iDestruct "H1" as %[-> ->].
      + rewrite IHHτ2. by iDestruct "H1" as %[-> ->].
  Qed.

  Lemma unboxed_type_eq_1_2 Θ (τ : type Θ ⋆) Δ v1 v2 v3 w1 w2 w3 :
    UnboxedType τ →
    interp τ Δ v1 v2 v3 -∗
    interp τ Δ w1 w2 w3 -∗
    |={⊤}=> ⌜v1 = w1 ↔ v2 = w2⌝.
  Proof.
    intros Hunboxed.
    cut (EqType τ ∨ ∃ τ', τ = t_ref τ').
    { intros [Hτ | [τ' ->]].
      - rewrite !eq_type_sound //.
        iIntros "% %". iModIntro.
        iPureIntro. naive_solver.
      - rewrite /lrel_car /=.
        iDestruct 1 as (l1 l2 l3 -> -> ->) "Hl".
        iDestruct 1 as (r1 r2 r3 -> -> ->) "Hr".
        destruct (decide (l1 = r1)); subst.
        + destruct (decide (l2 = r2)); subst; first by eauto.
          iInv (authN.@"ref".@(r1, l2, l3)) as (v1 v2 v3) "(>Hr1 & >Hr2 & >Hl3 & Hinv1)".
          iInv (authN.@"ref".@(r1, r2, r3)) as (w1 w2 w3) "(>Hr1' & >Hr2' & > Hr3' & Hinv2)".
          iExFalso. by iCombine "Hr1 Hr1'" gives %[].
        + destruct (decide (l2 = r2)); subst; last first.
          { iModIntro. iPureIntro. naive_solver. }
          iInv (authN.@"ref".@(r1, r2, r3)) as (v1 v2 v3) "(>Hr1 & >Hr2 & >Hr3 & Hinv1)".
          iInv (authN.@"ref".@(l1, r2, l3)) as (w1 w2 w3) "(>Hr1' & >Hr2' & >Hl3 & Hinv2)".
          iExFalso. by iCombine "Hr2 Hr2'" gives %[]. }
    by apply unboxed_type_ref_or_eqtype.
  Qed.

  Lemma unboxed_type_eq_2_3 Θ (τ : type Θ ⋆) Δ v1 v2 v3 w1 w2 w3 :
    UnboxedType τ →
    interp τ Δ v1 v2 v3 -∗
    interp τ Δ w1 w2 w3 -∗
    |={⊤}=> ⌜v2 = w2 ↔ v3 = w3⌝.
  Proof.
    intros Hunboxed.
    cut (EqType τ ∨ ∃ τ', τ = t_ref τ').
    { intros [Hτ | [τ' ->]].
      - rewrite !eq_type_sound //.
        iIntros "[% %] [% %]". iModIntro.
        iPureIntro. naive_solver.
      - rewrite /lrel_car /=.
        iDestruct 1 as (l1 l2 l3 -> -> ->) "Hl".
        iDestruct 1 as (r1 r2 r3 -> -> ->) "Hr".
        destruct (decide (l2 = r2)); subst.
        + destruct (decide (l3 = r3)); subst; first by eauto.
          iInv (authN.@"ref".@(l1, r2, l3)) as (v1 v2 v3) "(>Hr1 & >Hr2 & >Hl3 & Hinv1)".
          iInv (authN.@"ref".@(r1, r2, r3)) as (w1 w2 w3) "(>Hr1' & >Hr2' & > Hr3' & Hinv2)".
          iExFalso. by iCombine "Hr2 Hr2'" gives %[].
        + destruct (decide (l3 = r3)); subst; last first.
          { iModIntro. iPureIntro. naive_solver. }
          iInv (authN.@"ref".@(r1, r2, r3)) as (v1 v2 v3) "(>Hr1 & >Hr2 & >Hr3 & Hinv1)".
          iInv (authN.@"ref".@(l1, l2, r3)) as (w1 w2 w3) "(>Hr1' & >Hr2' & >Hr3' & Hinv2)".
          iExFalso. by iCombine "Hr3 Hr3'" gives %[]. }
    by apply unboxed_type_ref_or_eqtype.
  Qed.

End semtypes.

(** ** Properties of the type interpretation w.r.t. the substitutions *)
Section interp_subst.
  Context `{authG Σ}.

  Definition eqCK {κ₁ κ₂} (EQ : κ₁ = κ₂) : kindO Σ κ₁ → kindO Σ κ₂ → Prop :=
    match EQ with
    | eq_refl => (≡)
    end.

  Lemma fmap_eq {Θ1 Θ2 : Ctx kind} {κ} (δ : Θ1 [→] Θ2) (τ : typ κ Θ1) (Δ1 : ctxO Σ Θ1) (Δ2 : ctxO Σ Θ2) :
    (∀ x : dom Θ1, eqCK (arr_hom δ x) (Δ2 (δ x)) (Δ1 x)) →
    interp τ Δ1 ≡ interp (Core.fmap δ τ) Δ2.
  Proof.
    revert Θ2 δ Δ2; induction τ; intros Θ2 δ Δ2 Heq.
    - subst κ; simpl; symmetry; specialize (Heq x); revert Heq.
      generalize (arr_hom δ x), (Δ1 x) as ν₁. generalize (Θ x) as κ.
      intros. subst κ. now simpl in *.
    - intros ν. apply IHτ; intros [| x]; simpl; [reflexivity|apply Heq].
    - rewrite /= IHτ2 //. by erewrite (IHτ1 Δ1 Θ2 δ Δ2 Heq _).
    - reflexivity.
  Qed.

  Lemma shift_eq {Θ : Ctx kind} {κ1 κ2} (τ : typ κ2 Θ) (Δ : ctxO Σ Θ) (A : kindO Σ κ1) :
    interp τ Δ ≡ interp (Core.shift τ) (ext Δ A).
  Proof. apply fmap_eq; intros x; simpl; reflexivity. Qed.

  Lemma bind_eq {Θ1 Θ2 : Ctx kind} {κ} (ρ : Θ1 [⇒] Θ2) (τ : typ κ Θ1) (Δ1 : ctxO Σ Θ1) (Δ2 : ctxO Σ Θ2) :
    (∀ (x : dom Θ1), Δ1 x ≡ interp (ρ (Θ1 x) x eq_refl) Δ2) →
    interp τ Δ1 ≡ interp (bind ρ τ) Δ2.
  Proof.
    revert Θ2 ρ Δ2; induction τ; intros Θ2 rho Δ2 Heq; simpl.
    - subst κ; simpl; apply Heq.
    - intros ν; apply IHτ; intros [|] => //=. rewrite Heq; apply shift_eq.
    - rewrite /= IHτ2 //. by erewrite (IHτ1 _ _ _ _ Heq _).
    - reflexivity.
  Qed.

  Lemma subst_eq {Θ κ1 κ2} σ (τ : typ κ2 (Θ ▹ κ1)) (Δ : ctxO Σ Θ) :
    interp τ (ext Δ (interp σ Δ)) ≡ interp τ.[σ/] Δ.
  Proof.
    apply bind_eq; intros [| x]; simpl; reflexivity.
  Qed.

  Lemma tequiv_eq {Θ κ} (τ1 τ2 : typ κ Θ) (Δ : ctxO Σ Θ) :
    Θ ⊢ₑ τ1 ≃ τ2 : κ →
    interp τ1 Δ ≡ interp τ2 Δ.
  Proof.
    induction 1; simpl.
    - reflexivity.
    - by symmetry.
    - by transitivity (interp τ' Δ).
    - intros A => /=. rewrite IHtequiv //.
    - rewrite IHtequiv2. by erewrite (IHtequiv1 Δ _).
    - apply subst_eq.
    - intros A => /=. rewrite (shift_eq τ Δ A _) //.
  Qed.

  Lemma shift_env_eq (Θ : Ctx kind) (Γ : gmap string (typ ⋆ Θ)) (Δ : ctxO Σ Θ) κ (A : kindO Σ κ) :
    flip interp Δ <$> Γ ≡ flip interp (ext Δ A) <$> ⤉ Γ.
  Proof.
    rewrite -map_fmap_compose => x.
    rewrite !lookup_fmap.
    destruct (Γ !! x) => /=; [|done].
    f_equiv.
    rewrite (shift_eq _ _ A) //.
  Qed.

  Lemma tfill_rec_eq Θ (Δ : ctxO Σ Θ) κ κ' (T : telim_ctx Θ κ κ') (τ : typ κ (Θ ▹ κ)) :
    interp (tfill T (μ: κ; τ)) Δ ≡ interp_rec1 cid (interp (tfill T τ.[μ: κ; τ/]) Δ).
  Proof.
    induction T.
    - rewrite ![tfill _ _]/=. rewrite /= -/kindO.
      rewrite interp_rec_unfold.
      rewrite interp_rec1_shift.
      rewrite -subst_eq //.
    - rewrite /= -/kindO.
      specialize (IHT τ).
      rewrite ofe_mor_ext -/kindO in IHT.
      rewrite IHT //.
  Qed.

End interp_subst.

(** * Interpretation of the variable environment *)
Section env_typed.
  Context `{authG Σ}.
  Implicit Types A B : lrel Σ.
  Implicit Types Γ : gmap string (lrel Σ).

  (** Substitution [vs] is well-typed w.r.t. [Γ] *)
  Definition env_ltyped (Γ : gmap string (lrel Σ)) (vs : gmap string (val * val * val)) : iProp Σ :=
    ([∗ map] i ↦ A; '(v1,v2,v3) ∈ Γ;vs, A v1 v2 v3)%I.

  Notation "⟦ Γ ⟧*" := (env_ltyped Γ).

  Global Instance env_ltyped_ne n :
    Proper (dist n ==> (=) ==> dist n) env_ltyped.
  Proof.
    intros Γ Γ' HΓ ? vvs ->. apply big_sepM2_ne_2; [done..|solve_proper].
  Qed.

  Global Instance env_ltyped_proper :
    Proper ((≡) ==> (=) ==> (≡)) env_ltyped.
  Proof. solve_proper_from_ne. Qed.

  Lemma env_ltyped_lookup Γ vs x A :
    Γ !! x = Some A →
    ⟦ Γ ⟧* vs ⊢ ∃ v1 v2 v3, ⌜ vs !! x = Some (v1,v2, v3) ⌝ ∧ A v1 v2 v3.
  Proof.
    intros ?. rewrite /env_ltyped big_sepM2_lookup_l //.
    iDestruct 1 as ([[] ?] ?) "H". eauto with iFrame.
  Qed.

  Lemma env_ltyped_insert Γ vs x A v1 v2 v3 :
    A v1 v2 v3 -∗ ⟦ Γ ⟧* vs -∗
    ⟦ (binder_insert x A Γ) ⟧* (binder_insert x (v1, v2, v3) vs).
  Proof.
    destruct x as [|x]=> /=; first by auto.
    rewrite /env_ltyped. iIntros "HA HΓ".
    by iApply (big_sepM2_insert_2 with "[HA] [HΓ]").
  Qed.

  Lemma env_ltyped_empty :
    ⊢ ⟦ ∅ ⟧* ∅.
  Proof. apply (big_sepM2_empty' _). Qed.

  Lemma env_ltyped_empty_inv vs :
    ⟦ ∅ ⟧* vs ⊢ ⌜vs = ∅⌝.
  Proof. apply big_sepM2_empty_r. Qed.

  Global Instance env_ltyped_persistent Γ vs : Persistent (⟦ Γ ⟧* vs).
  Proof.
    apply big_sepM2_persistent.
    intros ?? [[] ?] ??. apply _.
  Qed.

End env_typed.

Notation "⟦ Γ ⟧*" := (env_ltyped Γ).
Notation "⟦ τ ⟧" := (interp τ).

(** * The semantic typing judgement *)
Section bin_log_related.
  Context `{authG Σ}.

  Definition bin_log_related (E : coPset) (Θ : Ctx kind)
    (Δ : ctxO Σ Θ) (Γ : stringmap (type Θ ⋆)) (e e' e'' : expr) (τ : type Θ ⋆) : iProp Σ :=
    (∀ (vs : gmap string (val * val * val)),
        ⟦ (λ τ, interp τ Δ) <$> Γ ⟧* vs -∗
        REL (subst_map (fst ∘ fst <$> vs) e)
        <<  (subst_map (snd ∘ fst <$> vs) e')
        <<  (subst_map (snd <$> vs) e'') @ E
        : interp τ Δ)%I.

End bin_log_related.

Notation "'{' E ';' Θ ';' Δ ';' Γ '}' ⊨ e '≤log≤' e' '≤log≤' e'' : τ" :=
  (bin_log_related E Θ Δ Γ e%E e'%E e''%E τ%ty)
  (at level 100, E at next level, Δ, Θ at next level, Γ at next level, e, e', e'' at next level,
   τ at level 200,
   format "'[hv' '{' E ';'  Θ ';'  Δ ';'  Γ '}'  ⊨  '/  ' e  '/' '≤log≤'  '/  ' e'  '/' '≤log≤'  '/  ' e''  :  τ ']'").
Notation "'{' Θ ';' Δ ';' Γ '}' ⊨ e '≤log≤' e' '≤log≤' e'' : τ" :=
  (bin_log_related ⊤ Θ Δ Γ e%E e'%E e''%E (τ)%ty)
  (at level 100, Δ at next level, Γ at next level, e, e', e'' at next level,
   τ at level 200,
   format "'[hv' '{' Θ ';'  Δ ';'  Γ '}'  ⊨  '/  ' e  '/' '≤log≤'  '/  ' e'  '/' '≤log≤'  '/  ' e''  :  τ ']'").
