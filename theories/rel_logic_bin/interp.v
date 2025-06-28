(** interpretations for System F_mu_ref types *)
From iris.algebra Require Export list.
From iris.proofmode Require Import proofmode.

From auth.typing Require Export types typing.
From auth.rel_logic_bin Require Import model.
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

  Program Definition ext {Σ Θ κ} : ctxO Σ Θ →  kindO Σ κ → ctxO Σ (Θ ▹ κ) := Inc.maybe.

  Program Definition interp_tvar {Θ : Ctx kind} {κ : kind} (x : dom Θ) (EQ : Θ x = κ) : ctxO Σ Θ -n> kindO Σ κ :=
    λne Δ, eq_rect (Θ x) (kindO Σ) (Δ x) κ EQ.
  Solve Obligations with solve_proper.

  Program Definition interp_tlam {Θ κ1 κ2} (A2 : ctxO Σ (Θ ▹ κ1) -n> kindO Σ κ2) :
    ctxO Σ Θ -n> kindO Σ (κ1 ⇒ κ2) := λne Δ A1, A2 (ext Δ A1).
  Solve Obligations with (intros ????????? => /=; f_equiv; rewrite /ext; solve_proper).

  Program Definition interp_tapp {Θ κ1 κ2} (A : ctxO Σ Θ -n> kindO Σ (κ1 ⇒ κ2))
    (B : ctxO Σ Θ -n> kindO Σ κ1) : ctxO Σ Θ -n> kindO Σ κ2 := λne Δ, (A Δ) (B Δ).
  Solve Obligations with solve_proper.

  Definition lrel_ktype (C : lrelC Σ -n> lrelC Σ) (rec : lrel Σ) : lrel Σ :=
    LRel (λ w1 w2, ▷ C rec w1 w2)%I.

  Global Instance lrel_ktype_contractive C : Contractive (lrel_ktype C).
  Proof.
    intros n. intros P Q HPQ.
    intros w1 w2. rewrite /lrel_car /=.
    f_contractive. f_equiv. by apply C.
  Qed.

  Program Fixpoint interp_rec1 {κ} : (kindO Σ κ -n> kindO Σ κ) -n> kindO Σ κ -n> kindO Σ κ :=
    match κ with
    | ⋆%kind => λne C rec, lrel_ktype C rec
    | (κ1 ⇒ κ2)%kind => λne C rec A1, interp_rec1 (κ := κ2) cid (C rec A1)
    end.
  Solve Obligations with solve_proper.

  Global Instance interp_rec1_contractive {κ} (C : kindO Σ κ -n> kindO Σ κ) : Contractive (interp_rec1 C).
  Proof.
    induction κ => n P Q HPQ.
    - by f_contractive.
    - intros κ. eapply IHκ2. dist_later_intro. solve_proper.
  Qed.

  Lemma interp_rec1_shift κ (C : kindO Σ κ -n> kindO Σ κ) (rec : kindO Σ κ) :
    interp_rec1 C rec ≡ interp_rec1 cid (C rec).
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

  #[local] Definition interp_tconstr {Θ κ} (c : tconstr κ) : ctxO Σ Θ -n> kindO Σ κ := λne _,
    match c in tconstr κ return kindO Σ κ with
    | TUnit => lrel_unit
    | TNat => lrel_int
    | TBool => lrel_bool
    | TString => lrel_string
    | TProd => lrel_prod'
    | TSum => lrel_sum'
    | TArrow => lrel_arr'
    | TRef => lrel_ref'
    | TRec κ => interp_rec
    | TForall κ => lrel_forall'
    | TExists κ => lrel_exists'
    end.

  #[local] Fixpoint interp_def {Θ : Ctx kind} {κ : kind} (τ : typ κ Θ) : ctxO Σ Θ -n> kindO Σ κ :=
    match τ in type _ κ return ctxO Σ Θ -n> kindO Σ κ with
    | TVar x EQ => interp_tvar x EQ
    | TLam τ => interp_tlam (interp_def τ)
    | TApp τ τ' => interp_tapp (interp_def τ) (interp_def τ')
    | TConstr c => interp_tconstr c
    end.

  (** We seal [interp] for performance reasons; [simpl] is at times too
      aggressive and ruins [Qed.] performance completely... *)
  #[local] Definition interp_aux : seal (@interp_def).
  Proof. by eexists. Qed.
  Definition interp := interp_aux.(unseal).
  Definition interp_unseal : @interp = @interp_def := interp_aux.(seal_eq).

  #[global] Arguments interp {Θ κ} τ.

End semtypes.

Notation "⟦ τ ⟧" := (interp τ).

Section semtypes_lemmas.
  Context `{!authG Σ}.

  Lemma unboxed_type_sound Θ (τ : type Θ ⋆) Δ v v' :
    UnboxedType τ →
    interp τ Δ v v' ⊢ ⌜val_is_unboxed v ∧ val_is_unboxed v'⌝.
  Proof.
    rewrite interp_unseal.
    induction 1; simpl.
    - by iDestruct 1 as "[-> ->]".
    - by iDestruct 1 as (?) "[-> ->]".
    - by iDestruct 1 as (?) "[-> ->]".
    - by iDestruct 1 as (?? -> ->) "H".
  Qed.

  Lemma eq_type_sound Θ (τ : type Θ ⋆) Δ v v':
    EqType τ →
    interp τ Δ v v' ⊢ ⌜v = v'⌝.
  Proof.
    rewrite interp_unseal.
    intros Hτ; revert v v'; induction Hτ; iIntros (v v') "#H1 /=".
    - by iDestruct "H1" as %(-> & ->).
    - by iDestruct "H1" as (n) "(% & %)"; subst.
    - by iDestruct "H1" as (b) "(% & %)"; subst.
    - by iDestruct "H1" as (b) "(% & %)"; subst.
    - iDestruct "H1" as (??) "(% & % & % & % & H1 & H2)"; simplify_eq/=.
      rewrite IHHτ1 IHHτ2. by iDestruct "H1" as %->; iDestruct "H2" as %->.
    - iDestruct "H1" as (??) "[(%&%&H1)|(%&%&H1)]"; simplify_eq.
      + rewrite IHHτ1. by iDestruct "H1" as %->.
      + rewrite IHHτ2. by iDestruct "H1" as %->.
  Qed.

  Lemma unboxed_type_eq Θ (τ : type Θ ⋆) Δ v1 v2 w1 w2 :
    UnboxedType τ →
    interp τ Δ v1 v2 -∗
    interp τ Δ w1 w2 -∗
    |={⊤}=> ⌜v1 = w1 ↔ v2 = w2⌝.
  Proof.
    intros Hunboxed.
    cut (EqType τ ∨ ∃ τ', τ = t_ref τ').
    { intros [Hτ | [τ' ->]].
      - rewrite !eq_type_sound //.
        iIntros "% %". iModIntro.
        iPureIntro. naive_solver.
      - rewrite interp_unseal.
        iDestruct 1 as (l1 l2 -> ->) "Hl".
        iDestruct 1 as (r1 r2 -> ->) "Hr".
        destruct (decide (l1 = r1)); subst.
        + destruct (decide (l2 = r2)); subst; first by eauto.
          iInv (authN.@"ref".@(r1, l2)) as (v1 v2) "(>Hr1 & >Hr2 & Hinv1)".
          iInv (authN.@"ref".@(r1, r2)) as (w1 w2) "(>Hr1' & >Hr2' & Hinv2)".
          iExFalso. by iCombine "Hr1 Hr1'" gives %[].
        + destruct (decide (l2 = r2)); subst; last first.
          { iModIntro. iPureIntro. naive_solver. }
          iInv (authN.@"ref".@(r1, r2)) as (v1 v2) "(>Hr1 & >Hr2 & Hinv1)".
          iInv (authN.@"ref".@(l1, r2)) as (w1 w2) "(>Hr1' & >Hr2' & Hinv2)".
          iExFalso. by iCombine "Hr2 Hr2'" gives %[]. }
    by apply unboxed_type_ref_or_eqtype.
  Qed.

End semtypes_lemmas.

Section semtype_unfold_lemmas.
  Context `{!authG Σ}.
  Context {Θ : Ctx kind} (Δ : ctxO Σ Θ).

  Lemma interp_unit_unfold :
    ⟦ () ⟧ Δ ≡ lrel_unit.
  Proof. rewrite interp_unseal //. Qed.
  Lemma interp_nat_unfold:
    ⟦ t_nat ⟧ Δ ≡ lrel_int.
  Proof. rewrite interp_unseal //. Qed.
  Lemma interp_bool_unfold :
    ⟦ t_bool ⟧ Δ ≡ lrel_bool.
  Proof. rewrite interp_unseal //. Qed.
  Lemma interp_string_unfold :
    ⟦ t_string ⟧ Δ ≡ lrel_string.
  Proof. rewrite interp_unseal //. Qed.
  Lemma interp_prod_unfold τ1 τ2 :
    ⟦ τ1 * τ2 ⟧ Δ ≡ (⟦ τ1 ⟧ Δ * ⟦ τ2 ⟧ Δ)%lrel.
  Proof. rewrite interp_unseal //. Qed.
  Lemma interp_sum_unfold τ1 τ2 :
    ⟦ τ1 + τ2 ⟧ Δ ≡ (⟦ τ1 ⟧ Δ + ⟦ τ2 ⟧ Δ)%lrel.
  Proof. rewrite interp_unseal //. Qed.
  Lemma interp_arr_unfold τ1 τ2:
    ⟦ τ1 → τ2 ⟧ Δ ≡ (⟦ τ1 ⟧ Δ → ⟦ τ2 ⟧ Δ)%lrel.
  Proof. rewrite interp_unseal //. Qed.
  Lemma interp_ref_unfold τ :
    ⟦ ref τ ⟧ Δ ≡ (ref (⟦ τ ⟧ Δ))%lrel.
  Proof. rewrite interp_unseal //. Qed.

  Lemma interp_rec_star_unfold (τ : type (Θ ▹ ⋆)%kind ⋆) v1 v2 :
    ⟦ μ: ⋆; τ ⟧ Δ v1 v2 ≡ (▷ ⟦ τ ⟧ (ext Δ (⟦ μ: ⋆; τ ⟧ Δ)) v1 v2)%I.
  Proof.
    rewrite interp_unseal /interp_def /= -/interp_def.
    rewrite {1}interp_rec_unfold //.
  Qed.
  Lemma interp_forall_unfold (κ : kind) (τ : type (Θ ▹ κ) ⋆) v1 v2 :
    ⟦ ∀: κ, τ ⟧ Δ v1 v2 ≡ (∀ A, (lrel_true → (⟦ τ ⟧ (ext Δ A)))%lrel v1 v2)%I .
  Proof. rewrite interp_unseal //. Qed.
  Lemma interp_exists_unfold (κ : kind) (τ : type (Θ ▹ κ) ⋆) v1 v2 :
    ⟦ ∃: κ, τ ⟧ Δ v1 v2 ≡ (∃ A, (⟦ τ ⟧ (ext Δ A)) v1 v2)%I .
  Proof. rewrite interp_unseal //. Qed.

  Lemma interp_tvar_unfold (κ : kind) x EQ :
    ⟦ TVar x EQ ⟧ Δ ≡ interp_tvar (κ := κ) x EQ Δ.
  Proof. rewrite interp_unseal //. Qed.
  Lemma interp_lam_unfold κ1 κ2 (τ : type (Θ ▹ κ1) κ2) (A : kindO Σ κ1) :
    (⟦ Λ: τ ⟧) Δ A ≡ ⟦ τ ⟧ (ext Δ A).
  Proof. rewrite interp_unseal //. Qed.
  Lemma interp_app_unfold κ1 κ2 (τ2 : type Θ (κ1 ⇒ κ2)) (τ1 : type Θ κ1) :
    ⟦ τ2 τ1 ⟧ Δ ≡ ⟦ τ2 ⟧ Δ (⟦ τ1 ⟧ Δ).
  Proof. rewrite interp_unseal //. Qed.
  Lemma interp_lam_app_unfold κ1 κ2 (τ2 : type (Θ ▹ κ1) κ2) (τ1 : type Θ κ1) :
    (⟦ (Λ: τ2) τ1 ⟧) Δ ≡ ⟦ τ2 ⟧ (ext Δ (⟦ τ1 ⟧ Δ)).
  Proof. rewrite interp_app_unfold interp_lam_unfold //. Qed.

End semtype_unfold_lemmas.

Ltac interp_unfold_tac :=
  match goal with
  | |- context [interp t_unit] => rewrite interp_unit_unfold
  | |- context [interp t_nat] => rewrite interp_nat_unfold
  | |- context [interp t_bool] => rewrite interp_bool_unfold
  | |- context [interp t_string] => rewrite interp_string_unfold

  | |- context [interp (t_prod _ _)] => rewrite interp_prod_unfold
  | |- context [interp (t_sum _ _)] => rewrite interp_sum_unfold
  | |- context [interp (t_option _)] => rewrite interp_sum_unfold
  | |- context [interp (t_arr _ _)] => rewrite interp_arr_unfold

  | |- context [interp (t_forall _ _)] => rewrite interp_forall_unfold
  | |- context [interp (t_exists _ _)] => rewrite interp_exists_unfold

  | |- context [interp (TApp _ _)] => rewrite interp_app_unfold

  | |- context [ofe_mor_car _ _ (interp var0) ?Δ] =>
      eassert (interp var0 Δ = _) as -> by rewrite interp_unseal /=//
  | |- context[ofe_mor_car _ _ (interp var1) ?Δ] =>
      eassert (interp var1 Δ = _) as -> by rewrite interp_unseal /=//
  | |- context[ofe_mor_car _ _ (interp var2) ?Δ] =>
      eassert (interp var2 Δ = _) as -> by rewrite interp_unseal /=//
  | |- context[ofe_mor_car _ _ (interp var3) ?Δ] =>
      eassert (interp var3 Δ = _) as -> by rewrite interp_unseal /=//
  | |- context[ofe_mor_car _ _ (interp var4) ?Δ] =>
      eassert (interp var4 Δ = _) as -> by rewrite interp_unseal /=//                                                                                                                | |- context[ofe_mor_car _ _ (interp var5) ?Δ] =>
                                                                                                                                                                                         eassert (interp var5 Δ = _) as -> by rewrite interp_unseal /=//
  end.

Tactic Notation "interp_unfold":= iEval (interp_unfold_tac).
Tactic Notation "interp_unfold" "!" := iEval (repeat interp_unfold_tac).
Tactic Notation "interp_unfold" "in" constr(H) := iEval (repeat interp_unfold_tac) in H.
Tactic Notation "interp_unfold" "!" "in" constr(H) := iEval (repeat interp_unfold_tac) in H.

(** * Proof mode instances that will allow us to avoid manually unsealing/unfolding [interp] in many situations *)

(** unit  *)
#[global] Instance into_and_interp_t_unit `{authG Σ} {Θ} (Δ : ctxO Σ Θ) (w1 w2 : val) b :
  IntoAnd b (⟦ () ⟧ Δ w1 w2)%I (⌜w1 = #()⌝)%I (⌜w2 = #()⌝)%I.
Proof. rewrite /IntoAnd. rewrite interp_unit_unfold/=.
       by destruct b => /=; try iModIntro; iIntros "[-> ->]".
Qed.
#[global] Instance from_and_interp_t_unit `{authG Σ} {Θ} (Δ : ctxO Σ Θ) (w1 w2 : val) :
  FromAnd (⟦ () ⟧ Δ w1 w2)%I (⌜w1 = #()⌝)%I (⌜w2 = #()⌝)%I .
Proof. rewrite /FromAnd. rewrite interp_unit_unfold/=. by iIntros "#[-> ->]". Qed.

(** bool *)
#[global] Instance into_exist_interp_t_bool `{authG Σ} {Θ} (Δ : ctxO Σ Θ) (w1 w2 : val) name :
  AsIdentName (λ (b : bool), ⌜w1 = #b ∧ w2 = #b⌝ : iProp Σ)%I name →
  IntoExist (⟦ t_bool ⟧ Δ w1 w2)%I (λ (b : bool), ⌜w1 = #b ∧ w2 = #b⌝)%I name.
Proof. rewrite /IntoExist. rewrite interp_bool_unfold //. Qed.
#[global] Instance from_exist_interp_t_bool `{authG Σ} {Θ} (Δ : ctxO Σ Θ) (w1 w2 : val) :
  FromExist (⟦ t_bool ⟧ Δ w1 w2)%I (λ (b : bool), ⌜w1 = #b ∧ w2 = #b⌝)%I.
Proof. rewrite /FromExist. rewrite interp_bool_unfold //. Qed.

(** nat *)
#[global] Instance into_exist_interp_t_nat `{authG Σ} {Θ} (Δ : ctxO Σ Θ) (w1 w2 : val) name :
  AsIdentName (λ (b : Z), ⌜w1 = #b ∧ w2 = #b⌝ : iProp Σ)%I name →
  IntoExist (⟦ t_nat ⟧ Δ w1 w2)%I (λ (b : Z), ⌜w1 = #b ∧ w2 = #b⌝)%I name.
Proof. rewrite /IntoExist. rewrite interp_nat_unfold //. Qed.
#[global] Instance from_exist_interp_t_nat `{authG Σ} {Θ} (Δ : ctxO Σ Θ) (w1 w2 : val) :
  FromExist (⟦ t_nat ⟧ Δ w1 w2)%I (λ (b : Z), ⌜w1 = #b ∧ w2 = #b⌝)%I.
Proof. rewrite /FromExist. rewrite interp_nat_unfold //. Qed.

(** nat *)
#[global] Instance into_exist_interp_t_string `{authG Σ} {Θ} (Δ : ctxO Σ Θ) (w1 w2 : val) name :
  AsIdentName (λ (b : string), ⌜w1 = #b ∧ w2 = #b⌝ : iProp Σ)%I name →
  IntoExist (⟦ t_string ⟧ Δ w1 w2)%I (λ (b : string), ⌜w1 = #b ∧ w2 = #b⌝)%I name.
Proof. rewrite /IntoExist. rewrite interp_string_unfold //. Qed.
#[global] Instance from_exist_interp_t_string `{authG Σ} {Θ} (Δ : ctxO Σ Θ) (w1 w2 : val) :
  FromExist (⟦ t_string ⟧ Δ w1 w2)%I (λ (b : string), ⌜w1 = #b ∧ w2 = #b⌝)%I.
Proof. rewrite /FromExist. rewrite interp_string_unfold //. Qed.

(** arrow *)
#[global] Instance into_forall_interp_t_arr `{authG Σ} {Θ} (Δ : ctxO Σ Θ) (τ1 τ2 : type Θ ⋆) (w1 w2 : val) :
  IntoForall (⟦ τ1 → τ2 ⟧ Δ w1 w2)
    (λ (v1 : val), □ ∀ v2, ⟦ τ1 ⟧ Δ v1 v2 -∗ REL App w1 v1 << App w2 v2 @ ⊤ : (⟦ τ2 ⟧ Δ))%I.
Proof. rewrite /IntoForall. rewrite interp_arr_unfold. eauto. Qed.

#[global] Instance from_forall_interp_t_arr `{authG Σ} {Θ} (Δ : ctxO Σ Θ) (τ1 τ2 : type Θ ⋆) (w1 w2 : val) name:
  AsIdentName (λ (v1 : val), □ ∀ v2, ⟦ τ1 ⟧ Δ v1 v2 -∗ REL App w1 v1 << App w2 v2 @ ⊤ : (⟦ τ2 ⟧ Δ))%I name →
  FromForall (⟦ τ1 → τ2 ⟧ Δ w1 w2)
    (λ (v1 : val), □ ∀ v2, ⟦ τ1 ⟧ Δ v1 v2 -∗ REL App w1 v1 << App w2 v2 @ ⊤ : (⟦ τ2 ⟧ Δ))%I name.
Proof.
  rewrite /FromForall => ?. rewrite interp_arr_unfold.
  iIntros "H" (v1). iApply "H".
Qed.

(** product *)
#[global] Instance into_exist_interp_t_prod `{authG Σ} {Θ} (Δ : ctxO Σ Θ) (τ1 τ2 : type Θ ⋆) (w1 w2 : val) name :
  AsIdentName (λ (v1 : val), ∃ v2 v1' v2',
        ⌜w1 = (v1,v1')%V⌝ ∧ ⌜w2 = (v2,v2')%V⌝ ∧ ⟦ τ1 ⟧ Δ v1 v2 ∗ ⟦ τ2 ⟧ Δ v1' v2')%I name →
  IntoExist (⟦ τ1 * τ2 ⟧ Δ w1 w2)
    (λ (v1 : val), ∃ v2 v1' v2', ⌜w1 = (v1,v1')%V⌝ ∧ ⌜w2 = (v2,v2')%V⌝ ∧ ⟦ τ1 ⟧ Δ v1 v2 ∗ ⟦ τ2 ⟧ Δ v1' v2')%I name.
Proof. rewrite /IntoExist. rewrite interp_prod_unfold //. Qed.
#[global] Instance from_exist_interp_t_prod `{authG Σ} {Θ} (Δ : ctxO Σ Θ) (τ1 τ2 : type Θ ⋆) (w1 w2 : val):
  FromExist (⟦ τ1 * τ2 ⟧ Δ w1 w2) (λ (v1 : val),
      ∃ v2 v1' v2', ⌜w1 = (v1,v1')%V⌝ ∧ ⌜w2 = (v2,v2')%V⌝ ∧ ⟦ τ1 ⟧ Δ v1 v2 ∗ ⟦ τ2 ⟧ Δ v1' v2')%I.
Proof. rewrite /FromExist. rewrite interp_prod_unfold //. Qed.

(** sum *)
#[global] Instance into_exist_interp_t_sum `{authG Σ} {Θ} (Δ : ctxO Σ Θ) (τ1 τ2 : type Θ ⋆) (w1 w2 : val) name :
  AsIdentName (λ (v1 : val), ∃ v2,
      (⌜w1 = InjLV v1⌝ ∧ ⌜w2 = InjLV v2⌝ ∧ ⟦ τ1 ⟧ Δ v1 v2) ∨ (⌜w1 = InjRV v1⌝ ∧ ⌜w2 = InjRV v2⌝ ∧ ⟦ τ2 ⟧ Δ v1 v2))%I name →
  IntoExist (⟦ τ1 + τ2 ⟧ Δ w1 w2)
    (λ (v1 : val), ∃ v2,
      (⌜w1 = InjLV v1⌝ ∧ ⌜w2 = InjLV v2⌝ ∧ ⟦ τ1 ⟧ Δ v1 v2) ∨ (⌜w1 = InjRV v1⌝ ∧ ⌜w2 = InjRV v2⌝ ∧ ⟦ τ2 ⟧ Δ v1 v2))%I name.
Proof. rewrite /IntoExist. rewrite interp_sum_unfold //. Qed.
#[global] Instance from_exist_interp_t_sum `{authG Σ} {Θ} (Δ : ctxO Σ Θ) (τ1 τ2 : type Θ ⋆) (w1 w2 : val) :
  FromExist (⟦ τ1 + τ2 ⟧ Δ w1 w2)
    (λ (v1 : val), ∃ v2,
      (⌜w1 = InjLV v1⌝ ∧ ⌜w2 = InjLV v2⌝ ∧ ⟦ τ1 ⟧ Δ v1 v2) ∨ (⌜w1 = InjRV v1⌝ ∧ ⌜w2 = InjRV v2⌝ ∧ ⟦ τ2 ⟧ Δ v1 v2))%I.
Proof. rewrite /FromExist. rewrite interp_sum_unfold //. Qed.

(** forall *)
#[global] Instance into_forall_interp_t_forall `{authG Σ} {Θ} (Δ : ctxO Σ Θ) κ (τ : type (Θ ▹ κ) ⋆) (v1 v2 : val) :
  IntoForall (⟦ ∀: κ, τ ⟧ Δ v1 v2) (λ A, (lrel_true → (⟦ τ ⟧ (ext Δ A)))%lrel v1 v2).
Proof. rewrite /IntoForall. rewrite interp_forall_unfold //. Qed.
#[global] Instance from_forall_interp_t_forall `{authG Σ} {Θ} (Δ : ctxO Σ Θ) κ (τ : type (Θ ▹ κ) ⋆) (v1 v2 : val) name :
  AsIdentName (λ A, (lrel_true → (⟦ τ ⟧ (ext Δ A)))%lrel v1 v2) name →
  FromForall (⟦ ∀: κ, τ ⟧ Δ v1 v2) (λ A, (lrel_true → (⟦ τ ⟧ (ext Δ A)))%lrel v1 v2) name.
Proof. rewrite /FromForall. rewrite interp_forall_unfold //. Qed.

(** exist *)
#[global] Instance into_exist_interp_t_exists `{authG Σ} {Θ} (Δ : ctxO Σ Θ) κ (τ : type (Θ ▹ κ) ⋆) (v1 v2 : val) name :
  AsIdentName (λ A, ⟦ τ ⟧ (ext Δ A) v1 v2) name →
  IntoExist (⟦ ∃: κ, τ ⟧ Δ v1 v2) (λ A, ⟦ τ ⟧ (ext Δ A) v1 v2) name.
Proof. rewrite /IntoExist. rewrite interp_exists_unfold //. Qed.
#[global] Instance from_exist_interp_t_exists `{authG Σ} {Θ} (Δ : ctxO Σ Θ) κ (τ : type (Θ ▹ κ) ⋆) (v1 v2 : val):
  FromExist (⟦ ∃: κ, τ ⟧ Δ v1 v2) (λ A, ⟦ τ ⟧ (ext Δ A) v1 v2).
Proof. rewrite /FromExist. rewrite interp_exists_unfold //. Qed.

(** ref  *)
#[global] Instance into_exist_interp_t_ref `{authG Σ} {Θ} (Δ : ctxO Σ Θ) (τ : type Θ ⋆) (w1 w2 : val) name :
  AsIdentName (λ (l1 : loc), ∃ l2 : loc, ⌜w1 = #l1⌝ ∧ ⌜w2 = #l2⌝ ∧
      inv (authN .@ "ref" .@ (l1,l2)) (∃ v1 v2, l1 ↦ v1 ∗ l2 ↦ᵢ v2 ∗ ⟦ τ ⟧ Δ v1 v2))%I name →
  IntoExist (⟦ ref τ ⟧ Δ w1 w2)
    (λ (l1 : loc), ∃ l2 : loc, ⌜w1 = #l1⌝ ∧ ⌜w2 = #l2⌝ ∧
      inv (authN .@ "ref" .@ (l1,l2)) (∃ v1 v2, l1 ↦ v1 ∗ l2 ↦ᵢ v2 ∗ ⟦ τ ⟧ Δ v1 v2))%I name.
Proof. rewrite /IntoExist. rewrite interp_ref_unfold //. Qed.
#[global] Instance from_exist_interp_t_ref `{authG Σ} {Θ} (Δ : ctxO Σ Θ) (τ : type Θ ⋆) (w1 w2 : val) :
  FromExist (⟦ ref τ ⟧ Δ w1 w2)
    (λ (l1 : loc), ∃ l2 : loc, ⌜w1 = #l1⌝ ∧ ⌜w2 = #l2⌝ ∧
      inv (authN .@ "ref" .@ (l1,l2)) (∃ v1 v2, l1 ↦ v1 ∗ l2 ↦ᵢ v2 ∗ ⟦ τ ⟧ Δ v1 v2))%I.
Proof. rewrite /FromExist. rewrite interp_ref_unfold //. Qed.

(** ** Properties of the type interpretation w.r.t. the substitutions *)
Section interp_subst.
  Context `{authG Σ}.

  Definition eqCK {κ₁ κ₂} (EQ : κ₁ = κ₂) : kindO Σ κ₁ → kindO Σ κ₂ → Prop :=
    match EQ with
    | eq_refl => (≡)
    end.

  Lemma fmap_eq {Θ1 Θ2 : Ctx kind} {κ} (δ : Θ1 [→] Θ2) (τ : typ κ Θ1) (Δ1 : ctxO Σ Θ1) (Δ2 : ctxO Σ Θ2) :
    (∀ x : dom Θ1, eqCK (arr_hom δ x) (Δ2 (δ x)) (Δ1 x)) →
    ⟦ τ ⟧ Δ1 ≡  ⟦ Core.fmap δ τ ⟧ Δ2.
  Proof.
    rewrite interp_unseal.
    revert Θ2 δ Δ2; induction τ; intros Θ2 δ Δ2 Heq.
    - subst κ; simpl; symmetry; specialize (Heq x); revert Heq.
      generalize (arr_hom δ x), (Δ1 x) as ν₁. generalize (Θ x) as κ.
      intros. subst κ. now simpl in *.
    - intros ν. apply IHτ; intros [| x]; simpl; [reflexivity|apply Heq].
    - rewrite /= IHτ2 //. by erewrite (IHτ1 Δ1 Θ2 δ Δ2 Heq _).
    - reflexivity.
  Qed.

  Lemma shift_eq {Θ : Ctx kind} {κ1 κ2} (τ : typ κ2 Θ) (Δ : ctxO Σ Θ) (A : kindO Σ κ1) :
    ⟦ τ ⟧ Δ ≡ ⟦ Core.shift τ ⟧ (ext Δ A).
  Proof. apply fmap_eq; intros x; simpl; reflexivity. Qed.

  Lemma bind_eq {Θ1 Θ2 : Ctx kind} {κ} (ρ : Θ1 [⇒] Θ2) (τ : typ κ Θ1) (Δ1 : ctxO Σ Θ1) (Δ2 : ctxO Σ Θ2) :
    (∀ (x : dom Θ1), Δ1 x ≡ ⟦ ρ (Θ1 x) x eq_refl ⟧ Δ2) →
    ⟦ τ ⟧ Δ1 ≡ ⟦ bind ρ τ ⟧ Δ2.
  Proof.
    rewrite interp_unseal.
    revert Θ2 ρ Δ2; induction τ; intros Θ2 rho Δ2 Heq; simpl.
    - subst κ; simpl. apply Heq.
    - intros ν => /=. apply IHτ. intros [|] => //=. rewrite Heq.
      epose proof shift_eq as Hshift. rewrite interp_unseal in Hshift. apply Hshift.
    - rewrite /= IHτ2 //. by erewrite (IHτ1 _ _ _ _ Heq _).
    - reflexivity.
  Qed.

  Lemma subst_eq {Θ κ1 κ2} σ (τ : typ κ2 (Θ ▹ κ1)) (Δ : ctxO Σ Θ) :
    ⟦ τ ⟧ (ext Δ (⟦ σ ⟧ Δ)) ≡ ⟦ τ.[σ/] ⟧ Δ.
  Proof.
    apply bind_eq; intros [| x] => /=; [done|]. rewrite interp_unseal //.
  Qed.

  Lemma tequiv_eq {Θ κ} (τ1 τ2 : typ κ Θ) (Δ : ctxO Σ Θ) :
    Θ ⊢ₑ τ1 ≃ τ2 : κ → ⟦ τ1 ⟧ Δ ≡ ⟦ τ2 ⟧ Δ.
  Proof.
    induction 1; simpl.
    - reflexivity.
    - by symmetry.
    - by transitivity (interp τ' Δ).
    - intros A => /=.
      rewrite !interp_lam_unfold.
      rewrite IHtequiv //.
    - rewrite !interp_app_unfold. rewrite IHtequiv2. by erewrite (IHtequiv1 Δ _).
    - rewrite interp_lam_app_unfold. apply subst_eq.
    - intros A => /=. rewrite (shift_eq τ Δ A _). rewrite interp_unseal //.
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
    ⟦ tfill T (μ: κ; τ) ⟧ Δ ≡ interp_rec1 cid (⟦ tfill T τ.[μ: κ; τ/] ⟧ Δ).
  Proof.
    induction T.
    - rewrite ![tfill _ _]/=.
      rewrite {1}interp_unseal /interp_def /= -/kindO -/interp_def.
      rewrite interp_rec_unfold.
      rewrite interp_rec1_shift.
      rewrite -subst_eq //.
      rewrite interp_unseal //.
    - rewrite /= -/kindO.
      specialize (IHT τ).
      rewrite interp_app_unfold.
      rewrite ofe_mor_ext -/kindO in IHT.
      rewrite IHT //. rewrite interp_unseal //.
  Qed.

End interp_subst.

(** * Interpretation of the variable environment *)
Section env_typed.
  Context `{authG Σ}.
  Implicit Types A B : lrel Σ.
  Implicit Types Γ : gmap string (lrel Σ).

  (** Substitution [vs] is well-typed w.r.t. [Γ] *)
  Definition env_ltyped (Γ : gmap string (lrel Σ)) (vs : gmap string (val * val)) : iProp Σ :=
    ([∗ map] i ↦ A; '(v1,v2) ∈ Γ;vs, A v1 v2)%I.

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
    ⟦ Γ ⟧* vs ⊢ ∃ v1 v2, ⌜ vs !! x = Some (v1,v2) ⌝ ∧ A v1 v2.
  Proof.
    intros ?. rewrite /env_ltyped big_sepM2_lookup_l //.
    iDestruct 1 as ([? ?] ?) "H". eauto with iFrame.
  Qed.

  Lemma env_ltyped_insert Γ vs x A v1 v2 :
    A v1 v2 -∗ ⟦ Γ ⟧* vs -∗
    ⟦ (binder_insert x A Γ) ⟧* (binder_insert x (v1, v2) vs).
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
    intros ?? [? ?] ??. apply _.
  Qed.

End env_typed.

Notation "⟦ Γ ⟧*" := (env_ltyped Γ).

(** * The semantic typing judgement *)
Section bin_log_related.
  Context `{authG Σ}.

  Definition bin_log_related (E : coPset) (Θ : Ctx kind)
    (Δ : ctxO Σ Θ) (Γ : stringmap (type Θ ⋆)) (e e' : expr) (τ : type Θ ⋆) : iProp Σ :=
    (∀ (vs : gmap string (val * val)),
        ⟦ (λ τ, interp τ Δ) <$> Γ ⟧* vs -∗
        REL (subst_map (fst <$> vs) e)
        <<  (subst_map (snd <$> vs) e') @ E : interp τ Δ)%I.

End bin_log_related.

Notation "'{' E ';' Θ ';' Δ ';' Γ '}' ⊨ e '≤log≤' e' : τ" :=
  (bin_log_related E Θ Δ Γ e%E e'%E τ%ty)
  (at level 100, E at next level, Δ, Θ at next level, Γ at next level, e, e' at next level,
   τ at level 200,
   format "'[hv' '{' E ';'  Θ ';'  Δ ';'  Γ '}'  ⊨  '/  ' e  '/' '≤log≤'  '/  ' e'  :  τ ']'").
Notation "'{' Θ ';' Δ ';' Γ '}' ⊨ e '≤log≤' e' : τ" :=
  (bin_log_related ⊤ Θ Δ Γ e%E e'%E (τ)%ty)
  (at level 100, Δ at next level, Γ at next level, e, e' at next level,
   τ at level 200,
   format "'[hv' '{' Θ ';'  Δ ';'  Γ '}'  ⊨  '/  ' e  '/' '≤log≤'  '/  ' e'  :  τ ']'").
