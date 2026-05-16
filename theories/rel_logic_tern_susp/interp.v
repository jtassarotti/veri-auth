(** interpretations for System F_mu_ref types *)
From iris.algebra Require Export list.
From iris.proofmode Require Import proofmode.

From auth.typing Require Export types typing.
From auth.rel_logic_tern_susp Require Import model.
From auth.prelude Require Import properness.

(** * Interpretation of kinds *)
Fixpoint kindO (Σ : gFunctors) (κ : kind) : ofe :=
  match κ with
  | KType => lrel_ternC Σ
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
  Context `{authG Σ, seqG Σ}.

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

  Definition lrel_ktype (C : lrel_ternC Σ -n> lrel_ternC Σ) (rec : lrel_ternC Σ) : lrel_ternC Σ :=
    LRelTern (LRel (λ w1 w2 w3, ▷ lrel_tern_tern (C rec) w1 w2 w3)%I)
             (LRelUn (λ w, ▷ lrel_tern_un (C rec) w)%I).

  Global Instance lrel_ktype_contractive C : Contractive (lrel_ktype C).
  Proof.
    intros n P Q HPQ.
    split.
    - intros w1 w2 w3; rewrite /lrel_car /=.
      f_contractive; f_equiv; by apply C.
    - intros w; rewrite /lrel_un_car /=.
      f_contractive; f_equiv; by apply C.
  Qed.

  Global Instance lrel_ktype_ne : NonExpansive2 lrel_ktype.
  Proof.
    intros n C1 C2 HC rec1 rec2 Hrec.
    split.
    - intros w1 w2 w3; rewrite /lrel_car /=.
      f_contractive. do 2 f_equiv. f_equiv.
      1: eapply dist_lt; [exact HC | exact Hlt].
      eapply dist_lt; [exact Hrec | exact Hlt].
    - intros w; rewrite /lrel_un_car /=.
      f_contractive. do 2 f_equiv. f_equiv.
      1: eapply dist_lt; [exact HC | exact Hlt].
      eapply dist_lt; [exact Hrec | exact Hlt].
  Qed.

  Program Fixpoint interp_rec1 {κ} : (kindO Σ κ -n> kindO Σ κ) -n> kindO Σ κ -n> kindO Σ κ :=
    match κ with
    | ⋆%kind => λne C rec, lrel_ktype C rec
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

  (** Combined constructors for [lrel_tern] *)
  Definition lrel_tern_prod (A B : lrel_ternC Σ) : lrel_ternC Σ :=
    LRelTern (lrel_prod' (lrel_tern_tern A) (lrel_tern_tern B))
             (lrel_un_prod' (lrel_tern_un A) (lrel_tern_un B)).
  Program Definition lrel_tern_prod' : lrel_ternC Σ -n> lrel_ternC Σ -n> lrel_ternC Σ :=
    λne A B, lrel_tern_prod A B.
  Solve Obligations with intros ?????; split; solve_proper.

  Definition lrel_tern_sum (A B : lrel_ternC Σ) : lrel_ternC Σ :=
    LRelTern (lrel_sum' (lrel_tern_tern A) (lrel_tern_tern B))
             (lrel_un_sum' (lrel_tern_un A) (lrel_tern_un B)).
  Program Definition lrel_tern_sum' : lrel_ternC Σ -n> lrel_ternC Σ -n> lrel_ternC Σ :=
    λne A B, lrel_tern_sum A B.
  Solve Obligations with intros ?????; split; solve_proper.

  Definition lrel_tern_arr (A B : lrel_ternC Σ) : lrel_ternC Σ :=
    LRelTern (lrel_arr' (lrel_tern_as_lrel A) (lrel_tern_as_lrel B))
             (lrel_un_arr' (lrel_tern_un A) (lrel_tern_un B)).
  Program Definition lrel_tern_arr' : lrel_ternC Σ -n> lrel_ternC Σ -n> lrel_ternC Σ :=
    λne A B, lrel_tern_arr A B.
  Solve Obligations with intros ?????; split; solve_proper.

  Program Definition lrel_tern_forall {κ} : (kindO Σ κ -n> lrel_ternC Σ) -n> lrel_ternC Σ :=
    λne C, LRelTern
      (LRel (λ w1 w2 w3, ∀ A : kindO Σ κ, (lrel_arr lrel_true (lrel_tern_as_lrel (C A))) w1 w2 w3)%I)
      (LRelUn (λ w, ∀ A : kindO Σ κ, (lrel_un_arr lrel_un_true (lrel_tern_un (C A))) w)%I).
  Solve Obligations with intros ????; split; solve_proper.

  Program Definition lrel_tern_exists {κ} : (kindO Σ κ -n> lrel_ternC Σ) -n> lrel_ternC Σ :=
    λne C, LRelTern
      (LRel (λ w1 w2 w3, ∃ A : kindO Σ κ, (lrel_tern_as_lrel (C A)) w1 w2 w3)%I)
      (LRelUn (λ w, ∃ A : kindO Σ κ, lrel_tern_un (C A) w)%I).
  Next Obligation.
    intros κ n C1 C2 HC. split.
    - intros w1 w2 w3. rewrite /lrel_tern_as_lrel /lrel_car /=.
      f_equiv => A. apply lrel_tern_as_lrel_ne, HC.
    - intros w. rewrite /lrel_tern_un /lrel_un_car /=.
      f_equiv => A. apply lrel_tern_un_ne, HC.
  Qed.

  #[local] Definition interp_tconstr {Θ κ} (c : tconstr κ) : ctxO Σ Θ -n> kindO Σ κ := λne _,
    match c in tconstr κ return kindO Σ κ with
    | TUnit    => LRelTern lrel_unit lrel_un_unit
    | TNat     => LRelTern lrel_int lrel_un_int
    | TBool    => LRelTern lrel_bool lrel_un_bool
    | TString  => LRelTern lrel_string lrel_un_string
    | TProd    => lrel_tern_prod'
    | TSum     => lrel_tern_sum'
    | TArrow   => lrel_tern_arr'
    (* | TRef => lrel_tern_ref' *)
    | TRec κ   => interp_rec
    | TForall κ => lrel_tern_forall
    | TExists κ => lrel_tern_exists
    end.

  Fixpoint interp_def {Θ : Ctx kind} {κ : kind} (τ : typ κ Θ) : ctxO Σ Θ -n> kindO Σ κ :=
    match τ in type _ κ return ctxO Σ Θ -n> kindO Σ κ with
    | TVar x EQ => interp_tvar x EQ
    | TLam τ => interp_tlam (interp_def τ)
    | TApp τ τ' => interp_tapp (interp_def τ) (interp_def τ')
    | TConstr c => interp_tconstr c
    end.

  #[local] Definition interp_aux : seal (@interp_def).
  Proof. by eexists. Qed.
  Definition interp := interp_aux.(unseal).
  Definition interp_unseal : @interp = @interp_def := interp_aux.(seal_eq).

  #[global] Arguments interp {Θ κ} τ.

End semtypes.

Notation "⟦ τ ⟧" := (interp τ).
(* Notation "⟦ τ ⟧_un" := (interp_un τ). *)

Section semtypes_lemmas.
  Context `{!authG Σ, !seqG Σ}.

  Lemma unboxed_type_sound_tern Θ (τ : type Θ ⋆) Δ v v' v'' :
    UnboxedType τ →
    lrel_tern_tern (interp τ Δ) v v' v'' ⊢
      ⌜val_is_unboxed v ∧ val_is_unboxed v' ∧ val_is_unboxed v''⌝.
  Proof.
    rewrite interp_unseal.
    induction 1; simpl;
    first [iDestruct 1 as (? ?) "[% [% (% & % & ?)]]"
          |iDestruct 1 as (?) "[% [% %]]"
          |iIntros "[% [% %]]"];
    simplify_eq/=; eauto with iFrame.
  Qed.

  Lemma unboxed_type_sound Θ (τ : type Θ ⋆) Δ v v' v'' :
    UnboxedType τ →
    interp τ Δ v v' v'' ⊢
      ⌜val_is_unboxed v ∧ val_is_unboxed v' ∧ val_is_unboxed v''⌝.
  Proof.
    intros ?. iIntros "[H _]". by iApply unboxed_type_sound_tern.
  Qed.

  Lemma eq_type_sound_tern Θ (τ : type Θ ⋆) Δ v v' v'' :
    EqType τ →
    lrel_tern_tern (interp τ Δ) v v' v'' ⊢ ⌜v = v' ∧ v' = v''⌝.
  Proof.
    rewrite interp_unseal.
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

  Lemma eq_type_sound Θ (τ : type Θ ⋆) Δ v v' v'' :
    EqType τ →
    interp τ Δ v v' v'' ⊢ ⌜v = v' ∧ v' = v''⌝.
  Proof.
    intros ?. iIntros "[H _]". by iApply eq_type_sound_tern.
  Qed.

  Lemma unboxed_type_eq_1_2 Θ (τ : type Θ ⋆) Δ v1 v2 v3 w1 w2 w3 :
    UnboxedType τ →
    interp τ Δ v1 v2 v3 -∗
    interp τ Δ w1 w2 w3 -∗
    |={⊤}=> ⌜v1 = w1 ↔ v2 = w2⌝.
  Proof.
    intros Hunboxed.
    cut (EqType τ).
    { intros Hτ.
      rewrite !eq_type_sound //.
      iIntros "% %". iModIntro.
      iPureIntro. naive_solver. }
    inversion Hunboxed; econstructor.
    (* intros Hunboxed.
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
    by apply unboxed_type_ref_or_eqtype. *)
  Qed.

  Lemma unboxed_type_eq_2_3 Θ (τ : type Θ ⋆) Δ v1 v2 v3 w1 w2 w3 :
    UnboxedType τ →
    interp τ Δ v1 v2 v3 -∗
    interp τ Δ w1 w2 w3 -∗
    |={⊤}=> ⌜v2 = w2 ↔ v3 = w3⌝.
  Proof.
    intros Hunboxed.
    cut (EqType τ).
    { intros Hτ.
      rewrite !eq_type_sound //.
      iIntros "% %". iModIntro.
      iPureIntro. naive_solver. }
    inversion Hunboxed; econstructor.
    (* intros Hunboxed.
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
    by apply unboxed_type_ref_or_eqtype. *)
  Qed.

End semtypes_lemmas.

(** * Unfold lemmas for the type interpretation *)
Section interp_unfold.
  Context `{authG Σ, seqG Σ}.
  Context {Θ : Ctx kind} (Δ : ctxO Σ Θ).

  (** Ternary projection unfold lemmas *)
  Lemma interp_tern_unit_unfold : lrel_tern_tern (interp t_unit Δ) = lrel_unit.
  Proof. rewrite interp_unseal //. Qed.
  Lemma interp_tern_nat_unfold : lrel_tern_tern (interp t_nat Δ) = lrel_int.
  Proof. rewrite interp_unseal //. Qed.
  Lemma interp_tern_bool_unfold : lrel_tern_tern (interp t_bool Δ) = lrel_bool.
  Proof. rewrite interp_unseal //. Qed.
  Lemma interp_tern_string_unfold : lrel_tern_tern (interp t_string Δ) = lrel_string.
  Proof. rewrite interp_unseal //. Qed.
  Lemma interp_tern_prod_unfold τ1 τ2 :
    lrel_tern_tern (interp (t_prod τ1 τ2) Δ) =
    lrel_prod (lrel_tern_tern (interp τ1 Δ)) (lrel_tern_tern (interp τ2 Δ)).
  Proof. rewrite interp_unseal //. Qed.
  Lemma interp_tern_sum_unfold τ1 τ2 :
    lrel_tern_tern (interp (t_sum τ1 τ2) Δ) =
    lrel_sum (lrel_tern_tern (interp τ1 Δ)) (lrel_tern_tern (interp τ2 Δ)).
  Proof. rewrite interp_unseal //. Qed.
  Lemma interp_tern_arr_unfold τ1 τ2 :
    lrel_tern_tern (interp (t_arr τ1 τ2) Δ) =
    lrel_arr (lrel_tern_as_lrel (interp τ1 Δ)) (lrel_tern_as_lrel (interp τ2 Δ)).
  Proof. rewrite interp_unseal //. Qed.

  (** Unary projection unfold lemmas *)
  Lemma interp_un_unit_unfold : lrel_tern_un (interp t_unit Δ) = lrel_un_unit.
  Proof. rewrite interp_unseal //. Qed.
  Lemma interp_un_nat_unfold : lrel_tern_un (interp t_nat Δ) = lrel_un_int.
  Proof. rewrite interp_unseal //. Qed.
  Lemma interp_un_bool_unfold : lrel_tern_un (interp t_bool Δ) = lrel_un_bool.
  Proof. rewrite interp_unseal //. Qed.
  Lemma interp_un_string_unfold : lrel_tern_un (interp t_string Δ) = lrel_un_string.
  Proof. rewrite interp_unseal //. Qed.
  Lemma interp_un_prod_unfold τ1 τ2 :
    lrel_tern_un (interp (t_prod τ1 τ2) Δ) =
    lrel_un_prod (lrel_tern_un (interp τ1 Δ)) (lrel_tern_un (interp τ2 Δ)).
  Proof. rewrite interp_unseal //. Qed.
  Lemma interp_un_sum_unfold τ1 τ2 :
    lrel_tern_un (interp (t_sum τ1 τ2) Δ) =
    lrel_un_sum (lrel_tern_un (interp τ1 Δ)) (lrel_tern_un (interp τ2 Δ)).
  Proof. rewrite interp_unseal //. Qed.
  Lemma interp_un_arr_unfold τ1 τ2 :
    lrel_tern_un (interp (t_arr τ1 τ2) Δ) =
    lrel_un_arr (lrel_tern_un (interp τ1 Δ)) (lrel_tern_un (interp τ2 Δ)).
  Proof. rewrite interp_unseal //. Qed.

  (** Forall/Exists projection unfold lemmas *)
  Lemma interp_tern_forall_unfold κ (τ : type (Θ ▹ κ) ⋆) v1 v2 v3 :
    lrel_tern_tern (interp (∀: κ, τ) Δ) v1 v2 v3 ≡
    (∀ A : kindO Σ κ, lrel_arr lrel_true (lrel_tern_as_lrel (interp τ (ext Δ A))) v1 v2 v3)%I.
  Proof. rewrite interp_unseal //. Qed.
  Lemma interp_un_forall_unfold κ (τ : type (Θ ▹ κ) ⋆) v :
    lrel_tern_un (interp (∀: κ, τ) Δ) v ≡
    (∀ A : kindO Σ κ, lrel_un_arr lrel_un_true (lrel_tern_un (interp τ (ext Δ A))) v)%I.
  Proof. rewrite interp_unseal //. Qed.

  Lemma interp_tern_exists_unfold κ (τ : type (Θ ▹ κ) ⋆) v1 v2 v3 :
    lrel_tern_tern (interp (∃: κ, τ) Δ) v1 v2 v3 ≡
    (∃ A : kindO Σ κ, lrel_tern_as_lrel (interp τ (ext Δ A)) v1 v2 v3)%I.
  Proof. rewrite interp_unseal //. Qed.
  Lemma interp_un_exists_unfold κ (τ : type (Θ ▹ κ) ⋆) v :
    lrel_tern_un (interp (∃: κ, τ) Δ) v ≡
    (∃ A : kindO Σ κ, lrel_tern_un (interp τ (ext Δ A)) v)%I.
  Proof. rewrite interp_unseal //. Qed.

  (** Recursive type unfold lemmas *)
  Lemma interp_rec_star_tern_unfold (τ : type (Θ ▹ ⋆)%kind ⋆) v1 v2 v3 :
    lrel_tern_tern (interp (μ: ⋆; τ) Δ) v1 v2 v3 ≡
    (▷ lrel_tern_tern (interp τ (ext Δ (interp (μ: ⋆; τ) Δ))) v1 v2 v3)%I.
  Proof. 
    rewrite interp_unseal /interp_def /= -/interp_def.
    rewrite /= {1}interp_rec_unfold //.
  Qed.
  Lemma interp_rec_star_un_unfold (τ : type (Θ ▹ ⋆)%kind ⋆) v :
    lrel_tern_un (interp (μ: ⋆; τ) Δ) v ≡
    (▷ lrel_tern_un (interp τ (ext Δ (interp (μ: ⋆; τ) Δ))) v)%I.
  Proof. 
    rewrite interp_unseal /interp_def /= -/interp_def.
    rewrite /= {1}interp_rec_unfold //.
  Qed.

  Lemma interp_rec_star_unfold (τ : type (Θ ▹ ⋆)%kind ⋆) v1 v2 v3 :
    lrel_tern_as_lrel (interp (μ: ⋆; τ) Δ) v1 v2 v3 ≡
    (▷ lrel_tern_as_lrel (interp τ (ext Δ (interp (μ: ⋆; τ) Δ))) v1 v2 v3)%I.
  Proof.
    trans (lrel_tern_tern (interp (μ: ⋆; τ) Δ) v1 v2 v3 ∧
           lrel_tern_un (interp (μ: ⋆; τ) Δ) v1)%I.
    { rewrite /lrel_tern_as_lrel. cbv [lrel_car]. done. }
    rewrite interp_rec_star_tern_unfold interp_rec_star_un_unfold.
    rewrite -bi.later_and.
    f_equiv. rewrite /lrel_tern_as_lrel. cbv [lrel_car]. done.
  Qed.

  (** Combined product factoring lemma *)
  Lemma interp_prod_combined τ1 τ2 v1 v2 v3 :
    lrel_tern_as_lrel (interp (t_prod τ1 τ2) Δ) v1 v2 v3 ⊣⊢
    (∃ a1 a2 b1 b2 c1 c2,
      ⌜v1 = (a1, a2)%V⌝ ∧ ⌜v2 = (b1, b2)%V⌝ ∧ ⌜v3 = (c1, c2)%V⌝ ∧
      lrel_tern_as_lrel (interp τ1 Δ) a1 b1 c1 ∗
      lrel_tern_as_lrel (interp τ2 Δ) a2 b2 c2).
  Proof.
    iSplit.
    - iIntros "[Htern Hun]".
      rewrite interp_tern_prod_unfold.
      iDestruct "Htern" as (a1 a2 b1 b2 c1 c2 -> -> ->) "[Ha Hb]".
      rewrite interp_un_prod_unfold.
      iDestruct "Hun" as (xa1 xa2) "(%Heq & Ha' & Hb')".
      injection Heq as -> ->.
      iExists xa1, xa2, a2, c1, b1, c2. do 3 (iSplit; [done|]).
      iSplitL "Ha Ha'"; iSplit; iFrame.
    - iDestruct 1 as (a1 a2 b1 b2 c1 c2) "(% & % & % & [Ha Ha'] & [Hb Hb'])".
      simplify_eq. iSplit.
      + rewrite interp_tern_prod_unfold.
        iExists a1, b1, c1, a2, b2, c2. do 3 (iSplit; [done|]). iFrame.
      + rewrite interp_un_prod_unfold.
        iExists a1, a2. iSplit; [done|]. iFrame.
  Qed.

  (** Combined sum factoring lemma *)
  Lemma interp_sum_combined τ1 τ2 v1 v2 v3 :
    lrel_tern_as_lrel (interp (t_sum τ1 τ2) Δ) v1 v2 v3 ⊣⊢
    (∃ w1 w2 w3,
      (⌜v1 = InjLV w1⌝ ∧ ⌜v2 = InjLV w2⌝ ∧ ⌜v3 = InjLV w3⌝ ∧
        lrel_tern_as_lrel (interp τ1 Δ) w1 w2 w3)
      ∨ (⌜v1 = InjRV w1⌝ ∧ ⌜v2 = InjRV w2⌝ ∧ ⌜v3 = InjRV w3⌝ ∧
        lrel_tern_as_lrel (interp τ2 Δ) w1 w2 w3)).
  Proof.
    iSplit.
    - iIntros "[Htern Hun]".
      rewrite interp_tern_sum_unfold.
      iDestruct "Htern" as (a1 a2 a3) "[(-> & -> & -> & Ha) | (-> & -> & -> & Ha)]";
        rewrite interp_un_sum_unfold;
        iDestruct "Hun" as (xu) "[[%Heq Ha']|[%Heq Ha']]";
        try (by inversion Heq); injection Heq as ->.
      + iExists xu, a2, a3. iLeft. do 3 (iSplit; [done|]). iSplit; iFrame.
      + iExists xu, a2, a3. iRight. do 3 (iSplit; [done|]). iSplit; iFrame.
    - iDestruct 1 as (w1 w2 w3) "[(% & % & % & [Ha Ha']) | (% & % & % & [Ha Ha'])]";
        simplify_eq; iSplit.
      + rewrite interp_tern_sum_unfold.
        iExists w1, w2, w3. iLeft. do 3 (iSplit; [done|]). iFrame.
      + rewrite interp_un_sum_unfold.
        iExists w1. iLeft. iSplit; [done|]. iFrame.
      + rewrite interp_tern_sum_unfold.
        iExists w1, w2, w3. iRight. do 3 (iSplit; [done|]). iFrame.
      + rewrite interp_un_sum_unfold.
        iExists w1. iRight. iSplit; [done|]. iFrame.
  Qed.

  (** Combined base type lemmas *)
  Lemma interp_unit_combined v1 v2 v3 :
    lrel_tern_as_lrel (interp t_unit Δ) v1 v2 v3 ⊣⊢
    ⌜v1 = #() ∧ v2 = #() ∧ v3 = #()⌝.
  Proof.
    rewrite /lrel_tern_as_lrel. cbv [lrel_car].
    rewrite interp_tern_unit_unfold interp_un_unit_unfold.
    cbv [lrel_unit lrel_un_unit lrel_car lrel_un_car].
    iSplit.
    - iIntros "[% _]". done.
    - iIntros "%". destruct_and!. iSplit; iPureIntro; done.
  Qed.

  Lemma interp_bool_combined v1 v2 v3 :
    lrel_tern_as_lrel (interp t_bool Δ) v1 v2 v3 ⊣⊢
    (∃ b : bool, ⌜v1 = #b ∧ v2 = #b ∧ v3 = #b⌝).
  Proof.
    rewrite /lrel_tern_as_lrel. cbv [lrel_car].
    rewrite interp_tern_bool_unfold interp_un_bool_unfold.
    cbv [lrel_bool lrel_un_bool lrel_car lrel_un_car].
    iSplit.
    - iIntros "[[%b %] _]". iExists b. done.
    - iIntros "[%b %]". destruct_and!. subst.
      iSplit; [iExists b; iPureIntro; done|iExists b; iPureIntro; done].
  Qed.

  Lemma interp_nat_combined v1 v2 v3 :
    lrel_tern_as_lrel (interp t_nat Δ) v1 v2 v3 ⊣⊢
    (∃ n : Z, ⌜v1 = #n ∧ v2 = #n ∧ v3 = #n⌝).
  Proof.
    rewrite /lrel_tern_as_lrel. cbv [lrel_car].
    rewrite interp_tern_nat_unfold interp_un_nat_unfold.
    cbv [lrel_int lrel_un_int lrel_car lrel_un_car].
    iSplit.
    - iIntros "[[%n %] _]". iExists n. done.
    - iIntros "[%n %]". destruct_and!. subst.
      iSplit; [iExists n; iPureIntro; done|iExists n; iPureIntro; done].
  Qed.

  Lemma interp_string_combined v1 v2 v3 :
    lrel_tern_as_lrel (interp t_string Δ) v1 v2 v3 ⊣⊢
    (∃ s : string, ⌜v1 = #s ∧ v2 = #s ∧ v3 = #s⌝).
  Proof.
    rewrite /lrel_tern_as_lrel. cbv [lrel_car].
    rewrite interp_tern_string_unfold interp_un_string_unfold.
    cbv [lrel_string lrel_un_string lrel_car lrel_un_car].
    iSplit.
    - iIntros "[[%s %] _]". iExists s. done.
    - iIntros "[%s %]". destruct_and!. subst.
      iSplit; [iExists s; iPureIntro; done|iExists s; iPureIntro; done].
  Qed.

  (** Structural unfolds: [TApp] / [TLam]. *)
  Lemma interp_app_unfold κ1 κ2 (τ2 : type Θ (κ1 ⇒ κ2)) (τ1 : type Θ κ1) :
    interp (TApp τ2 τ1) Δ ≡ interp τ2 Δ (interp τ1 Δ).
  Proof. rewrite interp_unseal //. Qed.

  Lemma interp_lam_unfold κ1 κ2 (τ : type (Θ ▹ κ1) κ2) (A : kindO Σ κ1) :
    interp (TLam τ) Δ A ≡ interp τ (ext Δ A).
  Proof. rewrite interp_unseal //. Qed.

  Lemma interp_lam_app_unfold κ1 κ2 (τ2 : type (Θ ▹ κ1) κ2) (τ1 : type Θ κ1) :
    (⟦ (Λ: τ2) τ1 ⟧) Δ ≡ ⟦ τ2 ⟧ (ext Δ (⟦ τ1 ⟧ Δ)).
  Proof. rewrite interp_app_unfold interp_lam_unfold //. Qed.

  (** De Bruijn variable unfolds: the [k]-th binder in a context of depth
      [k+1] selects the innermost-but-[k] element. *)
  Lemma interp_var0_ext1 {κ} (A : kindO Σ κ) :
    interp (var0 : type (Θ ▹ κ) κ) (ext Δ A) = A.
  Proof. rewrite interp_unseal //. Qed.

  Lemma interp_var1_ext2 {κ1 κ2} (F : kindO Σ κ1) (A : kindO Σ κ2) :
    interp (var1 : type (Θ ▹ κ1 ▹ κ2) κ1) (ext (ext Δ F) A) = F.
  Proof. rewrite interp_unseal //. Qed.

  Lemma interp_var2_ext3 {κ1 κ2 κ3} (F : kindO Σ κ1) (A : kindO Σ κ2) (B : kindO Σ κ3) :
    interp (var2 : type (Θ ▹ κ1 ▹ κ2 ▹ κ3) κ1) (ext (ext (ext Δ F) A) B) = F.
  Proof. rewrite interp_unseal //. Qed.

  Lemma interp_var3_ext4 {κ1 κ2 κ3 κ4} (F : kindO Σ κ1)
      (A : kindO Σ κ2) (B : kindO Σ κ3) (C : kindO Σ κ4) :
    interp (var3 : type (Θ ▹ κ1 ▹ κ2 ▹ κ3 ▹ κ4) κ1)
           (ext (ext (ext (ext Δ F) A) B) C) = F.
  Proof. rewrite interp_unseal //. Qed.

  Lemma interp_var4_ext5 {κ1 κ2 κ3 κ4 κ5} (F : kindO Σ κ1)
      (A : kindO Σ κ2) (B : kindO Σ κ3) (C : kindO Σ κ4) (D' : kindO Σ κ5) :
    interp (var4 : type (Θ ▹ κ1 ▹ κ2 ▹ κ3 ▹ κ4 ▹ κ5) κ1)
           (ext (ext (ext (ext (ext Δ F) A) B) C) D') = F.
  Proof. rewrite interp_unseal //. Qed.

  Lemma interp_var5_ext6 {κ1 κ2 κ3 κ4 κ5 κ6} (F : kindO Σ κ1)
      (A : kindO Σ κ2) (B : kindO Σ κ3) (C : kindO Σ κ4) (D' : kindO Σ κ5) (E' : kindO Σ κ6) :
    interp (var5 : type (Θ ▹ κ1 ▹ κ2 ▹ κ3 ▹ κ4 ▹ κ5 ▹ κ6) κ1)
           (ext (ext (ext (ext (ext (ext Δ F) A) B) C) D') E') = F.
  Proof. rewrite interp_unseal //. Qed.

End interp_unfold.

(** * [interp_unfold] tactic

    Rewrites the goal (or a hypothesis) by repeatedly matching known
    projection / structural shapes of [interp].  Ordered with the
    ternary-projection patterns first, then unary. *)

Ltac interp_unfold_tac :=
  match goal with
  (* Compound types: prefer the [_combined] lemma when available — it
     rewrites the [lrel_tern_as_lrel] wrapper in one shot into a directly
     destructible form (no follow-up [iDestruct as "[Htern Hun]"] split
     needed), and falls back to the individual [tern]/[un] projections
     when only one half is exposed (e.g. inside [iSplit; ...]). *)
  | |- context [interp (_ * _)] =>
      first [ rewrite interp_prod_combined
            | rewrite interp_tern_prod_unfold
            | rewrite interp_un_prod_unfold ]
  | |- context [interp (_ + _)] =>
      first [ rewrite interp_sum_combined
            | rewrite interp_tern_sum_unfold
            | rewrite interp_un_sum_unfold ]
  | |- context [interp (_ → _)] =>
      first [rewrite interp_tern_arr_unfold | rewrite interp_un_arr_unfold]
  | |- context [interp (t_forall _ _)] =>
      first [rewrite interp_tern_forall_unfold | rewrite interp_un_forall_unfold]
  | |- context [interp (t_exists _ _)] =>
      first [rewrite interp_tern_exists_unfold | rewrite interp_un_exists_unfold]
  (* Base type projections *)
  | |- context [interp ()] =>
      first [ rewrite interp_unit_combined
            | rewrite interp_tern_unit_unfold
            | rewrite interp_un_unit_unfold ]
  | |- context [interp t_nat] =>
      first [ rewrite interp_nat_combined
            | rewrite interp_tern_nat_unfold
            | rewrite interp_un_nat_unfold ]
  | |- context [interp t_bool] =>
      first [ rewrite interp_bool_combined
            | rewrite interp_tern_bool_unfold
            | rewrite interp_un_bool_unfold ]
  | |- context [interp t_string] =>
      first [ rewrite interp_string_combined
            | rewrite interp_tern_string_unfold
            | rewrite interp_un_string_unfold ]
  (* Structural unfolds (last: they would otherwise descend into μ-types
     and leak the [▷] from the [interp_rec] fixpoint). *)
  | |- context [interp (TApp _ _)] => rewrite interp_app_unfold
  | |- context [interp (TLam _)]   => rewrite interp_lam_unfold
  (* De Bruijn variable lookups — looser [context [interp varN]] pattern
     fires through transparent context wrappers like [auth_ctx Δ] which the
     old [ofe_mor_car _ _ (interp varN) (ext _ _)] pattern could not see
     through, removing the need for follow-up [rewrite interp_varN_extM]
     chains after every [interp_unfold!]. *)
  | |- context [interp var0] => rewrite interp_var0_ext1
  | |- context [interp var1] => rewrite interp_var1_ext2
  | |- context [interp var2] => rewrite interp_var2_ext3
  | |- context [interp var3] => rewrite interp_var3_ext4
  | |- context [interp var4] => rewrite interp_var4_ext5
  | |- context [interp var5] => rewrite interp_var5_ext6
  end.

Tactic Notation "interp_unfold" := iEval interp_unfold_tac.
Tactic Notation "interp_unfold" "!" := iEval (repeat interp_unfold_tac).
Tactic Notation "interp_unfold" "in" constr(H) := iEval interp_unfold_tac in H.
Tactic Notation "interp_unfold" "!" "in" constr(H) := iEval (repeat interp_unfold_tac) in H.

(** * Proof mode instances that will allow us to avoid manually unsealing/unfolding [interp] in many situations *)

(** unit  *)
#[global] Instance into_and_interp_t_unit `{authG Σ, seqG Σ} {Θ} (Δ : ctxO Σ Θ) (w1 w2 w3 : val) b :
  IntoAnd b (⟦ () ⟧ Δ w1 w2 w3)%I (⌜w1 = #()⌝)%I (⌜w2 = #() ∧ w3 = #()⌝)%I.
Proof.
  rewrite /IntoAnd. destruct b; simpl.
  all: iIntros "#H"; rewrite (interp_unit_combined Δ);
       iDestruct "H" as %(-> & -> & ->); auto.
Qed.
#[global] Instance from_and_interp_t_unit `{authG Σ, seqG Σ} {Θ} (Δ : ctxO Σ Θ) (w1 w2 w3 : val) :
  FromAnd (⟦ () ⟧ Δ w1 w2 w3)%I (⌜w1 = #()⌝)%I (⌜w2 = #() ∧ w3 = #()⌝)%I.
Proof.
  rewrite /FromAnd. iIntros "#[%Hw1 [%Hw2 %Hw3]]". subst.
  rewrite (interp_unit_combined Δ). iPureIntro. done.
Qed.

(** bool *)
#[global] Instance into_exist_interp_t_bool `{authG Σ, seqG Σ} {Θ} (Δ : ctxO Σ Θ) (w1 w2 w3 : val) name :
  AsIdentName (λ (b : bool), ⌜w1 = #b ∧ w2 = #b ∧ w3 = #b⌝ : iProp Σ)%I name →
  IntoExist (⟦ t_bool ⟧ Δ w1 w2 w3)%I (λ (b : bool), ⌜w1 = #b ∧ w2 = #b ∧ w3 = #b⌝)%I name.
Proof.
  intros _. rewrite /IntoExist. iIntros "#H". rewrite interp_bool_combined.
  iExact "H".
Qed.
#[global] Instance from_exist_interp_t_bool `{authG Σ, seqG Σ} {Θ} (Δ : ctxO Σ Θ) (w1 w2 w3 : val) :
  FromExist (⟦ t_bool ⟧ Δ w1 w2 w3)%I (λ (b : bool), ⌜w1 = #b ∧ w2 = #b ∧ w3 = #b⌝)%I.
Proof.
  rewrite /FromExist. iIntros "#H". rewrite interp_bool_combined.
  iDestruct "H" as (b) "%Hb". iExists b. iPureIntro. done.
Qed.

(** nat *)
#[global] Instance into_exist_interp_t_nat `{authG Σ, seqG Σ} {Θ} (Δ : ctxO Σ Θ) (w1 w2 w3 : val) name :
  AsIdentName (λ (n : Z), ⌜w1 = #n ∧ w2 = #n ∧ w3 = #n⌝ : iProp Σ)%I name →
  IntoExist (⟦ t_nat ⟧ Δ w1 w2 w3)%I (λ (n : Z), ⌜w1 = #n ∧ w2 = #n ∧ w3 = #n⌝)%I name.
Proof.
  intros _. rewrite /IntoExist. iIntros "#H". rewrite interp_nat_combined.
  iExact "H".
Qed.
#[global] Instance from_exist_interp_t_nat `{authG Σ, seqG Σ} {Θ} (Δ : ctxO Σ Θ) (w1 w2 w3 : val) :
  FromExist (⟦ t_nat ⟧ Δ w1 w2 w3)%I (λ (n : Z), ⌜w1 = #n ∧ w2 = #n ∧ w3 = #n⌝)%I.
Proof.
  rewrite /FromExist. iIntros "#H". rewrite interp_nat_combined.
  iDestruct "H" as (n) "%Hn". iExists n. iPureIntro. done.
Qed.

(** string *)
#[global] Instance into_exist_interp_t_string `{authG Σ, seqG Σ} {Θ} (Δ : ctxO Σ Θ) (w1 w2 w3 : val) name :
  AsIdentName (λ (s : string), ⌜w1 = #s ∧ w2 = #s ∧ w3 = #s⌝ : iProp Σ)%I name →
  IntoExist (⟦ t_string ⟧ Δ w1 w2 w3)%I (λ (s : string), ⌜w1 = #s ∧ w2 = #s ∧ w3 = #s⌝)%I name.
Proof.
  intros _. rewrite /IntoExist. iIntros "#H". rewrite interp_string_combined.
  iExact "H".
Qed.
#[global] Instance from_exist_interp_t_string `{authG Σ, seqG Σ} {Θ} (Δ : ctxO Σ Θ) (w1 w2 w3 : val) :
  FromExist (⟦ t_string ⟧ Δ w1 w2 w3)%I (λ (s : string), ⌜w1 = #s ∧ w2 = #s ∧ w3 = #s⌝)%I.
Proof.
  rewrite /FromExist. iIntros "#H". rewrite interp_string_combined.
  iDestruct "H" as (s) "%Hs". iExists s. iPureIntro. done.
Qed.

(** arrow: IntoForall extracts the ternary component *)
#[global] Instance into_forall_interp_t_arr `{authG Σ, seqG Σ} {Θ} (Δ : ctxO Σ Θ) (τ1 τ2 : type Θ ⋆) (w1 w2 w3 : val) :
  IntoForall (⟦ τ1 → τ2 ⟧ Δ w1 w2 w3)
    (λ (v1 : val), □ ∀ v2 v3, ⟦ τ1 ⟧ Δ v1 v2 v3 -∗ REL App w1 v1 << App w2 v2 << App w3 v3 @ ⊤ : (⟦ τ2 ⟧ Δ))%I.
Proof.
  rewrite /IntoForall. iIntros "#H". iDestruct "H" as "[Htern _]".
  iEval (rewrite interp_tern_arr_unfold /lrel_arr /lrel_arr'; cbv [lrel_car]) in "Htern".
  iIntros (x). by iApply ("Htern" $! x).
Qed.

(** product *)
#[global] Instance into_exist_interp_t_prod `{authG Σ, seqG Σ} {Θ} (Δ : ctxO Σ Θ) (τ1 τ2 : type Θ ⋆) (w1 w2 w3 : val) name :
  AsIdentName (λ (a1 : val), ∃ b1 c1 a2 b2 c2,
        ⌜w1 = (a1,a2)%V⌝ ∧ ⌜w2 = (b1,b2)%V⌝ ∧ ⌜w3 = (c1,c2)%V⌝ ∧
        ⟦ τ1 ⟧ Δ a1 b1 c1 ∗ ⟦ τ2 ⟧ Δ a2 b2 c2)%I name →
  IntoExist (⟦ τ1 * τ2 ⟧ Δ w1 w2 w3)
    (λ (a1 : val), ∃ b1 c1 a2 b2 c2,
        ⌜w1 = (a1,a2)%V⌝ ∧ ⌜w2 = (b1,b2)%V⌝ ∧ ⌜w3 = (c1,c2)%V⌝ ∧
        ⟦ τ1 ⟧ Δ a1 b1 c1 ∗ ⟦ τ2 ⟧ Δ a2 b2 c2)%I name.
Proof.
  intros _. rewrite /IntoExist. iIntros "#H". rewrite interp_prod_combined.
  iDestruct "H" as (a1 a2 b1 b2 c1 c2) "(% & % & % & #Ha & #Hb)".
  iExists a1, b1, c1, a2, b2, c2. iFrame "# %".
Qed.
#[global] Instance from_exist_interp_t_prod `{authG Σ, seqG Σ} {Θ} (Δ : ctxO Σ Θ) (τ1 τ2 : type Θ ⋆) (w1 w2 w3 : val):
  FromExist (⟦ τ1 * τ2 ⟧ Δ w1 w2 w3) (λ (a1 : val),
      ∃ b1 c1 a2 b2 c2,
        ⌜w1 = (a1,a2)%V⌝ ∧ ⌜w2 = (b1,b2)%V⌝ ∧ ⌜w3 = (c1,c2)%V⌝ ∧
        ⟦ τ1 ⟧ Δ a1 b1 c1 ∗ ⟦ τ2 ⟧ Δ a2 b2 c2)%I.
Proof.
  rewrite /FromExist. iIntros "#H".
  iDestruct "H" as (a1 b1 c1 a2 b2 c2) "(% & % & % & #Ha & #Hb)".
  rewrite interp_prod_combined.
  iExists a1, a2, b1, b2, c1, c2. iFrame "# %".
Qed.

(** sum *)
#[global] Instance into_exist_interp_t_sum `{authG Σ, seqG Σ} {Θ} (Δ : ctxO Σ Θ) (τ1 τ2 : type Θ ⋆) (w1 w2 w3 : val) name :
  AsIdentName (λ (v1 : val), ∃ v2 v3,
      (⌜w1 = InjLV v1⌝ ∧ ⌜w2 = InjLV v2⌝ ∧ ⌜w3 = InjLV v3⌝ ∧ ⟦ τ1 ⟧ Δ v1 v2 v3)
      ∨ (⌜w1 = InjRV v1⌝ ∧ ⌜w2 = InjRV v2⌝ ∧ ⌜w3 = InjRV v3⌝ ∧ ⟦ τ2 ⟧ Δ v1 v2 v3))%I name →
  IntoExist (⟦ τ1 + τ2 ⟧ Δ w1 w2 w3)
    (λ (v1 : val), ∃ v2 v3,
      (⌜w1 = InjLV v1⌝ ∧ ⌜w2 = InjLV v2⌝ ∧ ⌜w3 = InjLV v3⌝ ∧ ⟦ τ1 ⟧ Δ v1 v2 v3)
      ∨ (⌜w1 = InjRV v1⌝ ∧ ⌜w2 = InjRV v2⌝ ∧ ⌜w3 = InjRV v3⌝ ∧ ⟦ τ2 ⟧ Δ v1 v2 v3))%I name.
Proof.
  intros _. rewrite /IntoExist. iIntros "#H". rewrite interp_sum_combined.
  iDestruct "H" as (v1 v2 v3) "#[(% & % & % & Ha) | (% & % & % & Ha)]".
  - iExists v1, v2, v3. iLeft. iFrame "# %".
  - iExists v1, v2, v3. iRight. iFrame "# %".
Qed.
#[global] Instance from_exist_interp_t_sum `{authG Σ, seqG Σ} {Θ} (Δ : ctxO Σ Θ) (τ1 τ2 : type Θ ⋆) (w1 w2 w3 : val) :
  FromExist (⟦ τ1 + τ2 ⟧ Δ w1 w2 w3)
    (λ (v1 : val), ∃ v2 v3,
      (⌜w1 = InjLV v1⌝ ∧ ⌜w2 = InjLV v2⌝ ∧ ⌜w3 = InjLV v3⌝ ∧ ⟦ τ1 ⟧ Δ v1 v2 v3)
      ∨ (⌜w1 = InjRV v1⌝ ∧ ⌜w2 = InjRV v2⌝ ∧ ⌜w3 = InjRV v3⌝ ∧ ⟦ τ2 ⟧ Δ v1 v2 v3))%I.
Proof.
  rewrite /FromExist. iIntros "#H".
  iDestruct "H" as (v1 v2 v3) "#[(% & % & % & Ha) | (% & % & % & Ha)]";
    rewrite interp_sum_combined.
  - iExists v1, v2, v3. iLeft. iFrame "# %".
  - iExists v1, v2, v3. iRight. iFrame "# %".
Qed.

(** forall: IntoForall extracts ternary component *)
#[global] Instance into_forall_interp_t_forall `{authG Σ, seqG Σ} {Θ} (Δ : ctxO Σ Θ) κ (τ : type (Θ ▹ κ) ⋆) (v1 v2 v3 : val) :
  IntoForall (⟦ ∀: κ, τ ⟧ Δ v1 v2 v3) (λ A, (lrel_true → (⟦ τ ⟧ (ext Δ A)))%lrel v1 v2 v3).
Proof.
  rewrite /IntoForall. iIntros "#H". iDestruct "H" as "[Htern _]".
  iEval (rewrite interp_tern_forall_unfold) in "Htern".
  iIntros (A). by iApply ("Htern" $! A).
Qed.

(** exist *)
#[global] Instance into_exist_interp_t_exists `{authG Σ, seqG Σ} {Θ} (Δ : ctxO Σ Θ) κ (τ : type (Θ ▹ κ) ⋆) (v1 v2 v3 : val) name :
  AsIdentName (λ A, ⟦ τ ⟧ (ext Δ A) v1 v2 v3) name →
  IntoExist (⟦ ∃: κ, τ ⟧ Δ v1 v2 v3) (λ A, ⟦ τ ⟧ (ext Δ A) v1 v2 v3) name.
Proof.
  intros _. rewrite /IntoExist. iIntros "#H". iDestruct "H" as "[Htern _]".
  iEval (rewrite interp_tern_exists_unfold) in "Htern".
  iDestruct "Htern" as (A) "#HA". iExists A. iExact "HA".
Qed.
#[global] Instance from_exist_interp_t_exists `{authG Σ, seqG Σ} {Θ} (Δ : ctxO Σ Θ) κ (τ : type (Θ ▹ κ) ⋆) (v1 v2 v3 : val):
  FromExist (⟦ ∃: κ, τ ⟧ Δ v1 v2 v3) (λ A, ⟦ τ ⟧ (ext Δ A) v1 v2 v3).
Proof.
  rewrite /FromExist. iIntros "#H". iDestruct "H" as (A) "[#HAtern #HAun]".
  iSplit.
  { iEval (rewrite interp_tern_exists_unfold). iExists A.
    iSplit; [iExact "HAtern" | iExact "HAun"]. }
  { iEval (rewrite interp_un_exists_unfold). iExists A. iExact "HAun". }
Qed.

(** ** Properties of the type interpretation w.r.t. the substitutions *)
Section interp_subst.
  Context `{authG Σ, seqG Σ}.

  Definition eqCK {κ₁ κ₂} (EQ : κ₁ = κ₂) : kindO Σ κ₁ → kindO Σ κ₂ → Prop :=
    match EQ with
    | eq_refl => (≡)
    end.

  Lemma fmap_eq {Θ1 Θ2 : Ctx kind} {κ} (δ : Θ1 [→] Θ2) (τ : typ κ Θ1) (Δ1 : ctxO Σ Θ1) (Δ2 : ctxO Σ Θ2) :
    (∀ x : dom Θ1, eqCK (arr_hom δ x) (Δ2 (δ x)) (Δ1 x)) →
    interp τ Δ1 ≡ interp (Core.fmap δ τ) Δ2.
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
    interp τ Δ ≡ interp (Core.shift τ) (ext Δ A).
  Proof. apply fmap_eq; intros x; simpl; reflexivity. Qed.

  Lemma bind_eq {Θ1 Θ2 : Ctx kind} {κ} (ρ : Θ1 [⇒] Θ2) (τ : typ κ Θ1) (Δ1 : ctxO Σ Θ1) (Δ2 : ctxO Σ Θ2) :
    (∀ (x : dom Θ1), Δ1 x ≡ interp (ρ (Θ1 x) x eq_refl) Δ2) →
    interp τ Δ1 ≡ interp (bind ρ τ) Δ2.
  Proof.
    rewrite interp_unseal.
    revert Θ2 ρ Δ2; induction τ; intros Θ2 rho Δ2 Heq; simpl.
    - subst κ; simpl; apply Heq.
    - intros ν; apply IHτ; intros [|] => //=. rewrite Heq.
      epose proof shift_eq as Hshift. rewrite interp_unseal in Hshift. apply Hshift.
    - rewrite /= IHτ2 //. by erewrite (IHτ1 _ _ _ _ Heq _).
    - reflexivity.
  Qed.

  Lemma subst_eq {Θ κ1 κ2} σ (τ : typ κ2 (Θ ▹ κ1)) (Δ : ctxO Σ Θ) :
    interp τ (ext Δ (interp σ Δ)) ≡ interp τ.[σ/] Δ.
  Proof.
    apply bind_eq; intros [| x] => /=; [done|]. rewrite interp_unseal //.
  Qed.

  Lemma tequiv_eq {Θ κ} (τ1 τ2 : typ κ Θ) (Δ : ctxO Σ Θ) :
    Θ ⊢ₑ τ1 ≃ τ2 : κ →
    interp τ1 Δ ≡ interp τ2 Δ.
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

  Lemma shift_env_eq_as_lrel (Θ : Ctx kind) (Γ : gmap string (typ ⋆ Θ)) (Δ : ctxO Σ Θ) κ (A : kindO Σ κ) :
    (λ σ : typ ⋆ Θ, lrel_tern_as_lrel (interp σ Δ)) <$> Γ ≡
    (λ σ : typ ⋆ (Θ ▹ κ), lrel_tern_as_lrel (interp σ (ext Δ A))) <$> ⤉ Γ.
  Proof.
    rewrite -map_fmap_compose => x.
    rewrite !lookup_fmap.
    destruct (Γ !! x) => /=; [|done].
    constructor. intros w1 w2 w3. apply equiv_dist. intros n.
    apply lrel_tern_as_lrel_ne.
    exact (proj1 (equiv_dist _ _) (shift_eq t Δ A) n).
  Qed.

  Lemma shift_env_un_eq (Θ : Ctx kind) (Γ : gmap string (typ ⋆ Θ)) (Δ : ctxO Σ Θ) κ (A : kindO Σ κ) :
    (λ σ : typ ⋆ Θ, lrel_tern_un (interp σ Δ)) <$> Γ ≡
    (λ σ : typ ⋆ (Θ ▹ κ), lrel_tern_un (interp σ (ext Δ A))) <$> ⤉ Γ.
  Proof.
    rewrite -map_fmap_compose => x.
    rewrite !lookup_fmap.
    destruct (Γ !! x) => /=; [|done].
    constructor. intros w. apply equiv_dist. intros n.
    apply lrel_tern_un_ne.
    exact (proj1 (equiv_dist _ _) (shift_eq t Δ A) n).
  Qed.

  Lemma tfill_rec_eq Θ (Δ : ctxO Σ Θ) κ κ' (T : telim_ctx Θ κ κ') (τ : typ κ (Θ ▹ κ)) :
    interp (tfill T (μ: κ; τ)) Δ ≡ interp_rec1 cid (interp (tfill T τ.[μ: κ; τ/]) Δ).
  Proof.
    induction T.
    - rewrite ![tfill _ _]/=.
      rewrite -subst_eq.
      rewrite {1}interp_unseal /interp_def /= -/kindO -/interp_def.
      rewrite interp_rec_unfold interp_rec1_shift.
      f_equiv. simpl.
      rewrite -interp_unseal.
      do 2 f_equiv. rewrite interp_unseal //.
    - rewrite /= -/kindO.
      specialize (IHT τ).
      rewrite ofe_mor_ext -/kindO in IHT.
      rewrite !interp_app_unfold.
      rewrite IHT //.
  Qed.

End interp_subst.

(** * Interpretation of the variable environment *)
Section env_typed.
  Context `{authG Σ, seqG Σ}.
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

(** * Unary environment typing (prover) *)
Section env_typed_un.
  Context `{authG Σ, seqG Σ}.
  Implicit Types A B : lrel_un Σ.
  Implicit Types Γ : gmap string (lrel_un Σ).

  Definition env_ltyped_un (Γ : gmap string (lrel_un Σ)) (vs : gmap string val) : iProp Σ :=
    ([∗ map] i ↦ A; v ∈ Γ;vs, A v)%I.

  Notation "⟦ Γ ⟧*ᵤ" := (env_ltyped_un Γ).

  Global Instance env_ltyped_un_ne n :
    Proper (dist n ==> (=) ==> dist n) env_ltyped_un.
  Proof.
    intros Γ Γ' HΓ ? vvs ->. apply big_sepM2_ne_2; [done..|solve_proper].
  Qed.

  Global Instance env_ltyped_un_proper :
    Proper ((≡) ==> (=) ==> (≡)) env_ltyped_un.
  Proof. solve_proper_from_ne. Qed.

  Lemma env_ltyped_un_lookup Γ vs x A :
    Γ !! x = Some A →
    ⟦ Γ ⟧*ᵤ vs ⊢ ∃ v, ⌜ vs !! x = Some v ⌝ ∗ A v.
  Proof.
    intros ?. rewrite /env_ltyped_un big_sepM2_lookup_l //.
    iDestruct 1 as (? ?) "H". eauto with iFrame.
  Qed.

  Lemma env_ltyped_un_insert Γ vs x A v :
    A v -∗ ⟦ Γ ⟧*ᵤ vs -∗
    ⟦ (binder_insert x A Γ) ⟧*ᵤ (binder_insert x v vs).
  Proof.
    destruct x as [|x]=> /=; first by auto.
    rewrite /env_ltyped_un. iIntros "HA HΓ".
    by iApply (big_sepM2_insert_2 with "[HA] [HΓ]").
  Qed.

  Lemma env_ltyped_un_empty :
    ⊢ ⟦ ∅ ⟧*ᵤ ∅.
  Proof. apply (big_sepM2_empty' _). Qed.

  Lemma env_ltyped_un_empty_inv vs :
    ⟦ ∅ ⟧*ᵤ vs ⊢ ⌜vs = ∅⌝.
  Proof. apply big_sepM2_empty_r. Qed.

  Global Instance env_ltyped_un_persistent Γ vs : Persistent (⟦ Γ ⟧*ᵤ vs).
  Proof.
    apply big_sepM2_persistent.
    intros ???  ??. apply _.
  Qed.

  Lemma env_tern_to_un {Θ} (Δ : ctxO Σ Θ) (Γ : stringmap (typ ⋆ Θ)) vs :
    env_ltyped ((λ (σ : typ ⋆ Θ), lrel_tern_as_lrel (interp σ Δ)) <$> Γ) vs ⊢
    env_ltyped_un ((λ (σ : typ ⋆ Θ), lrel_tern_un (interp σ Δ)) <$> Γ) (fst ∘ fst <$> vs).
  Proof.
    rewrite /env_ltyped /env_ltyped_un.
    iIntros "H".
    rewrite big_sepM2_fmap_l.
    rewrite big_sepM2_fmap_l big_sepM2_fmap_r.
    iApply (big_sepM2_mono with "H").
    intros k σ [[v1 v2] v3] _ _. simpl. apply lrel_tern_proj_un.
  Qed.

End env_typed_un.

Notation "⟦ Γ ⟧*ᵤ" := (env_ltyped_un Γ).

(** * The semantic typing judgement *)
Section tern_log_related.
  Context `{authG Σ, seqG Σ}.

  Definition tern_log_related (E : coPset) (Θ : Ctx kind)
    (Δ : ctxO Σ Θ) (Γ : stringmap (type Θ ⋆)) (e e' e'' : expr) (τ : type Θ ⋆) : iProp Σ :=
    (∀ (vs : gmap string (val * val * val)),
        ⟦ (λ (σ : type Θ ⋆), lrel_tern_as_lrel (interp σ Δ)) <$> Γ ⟧* vs -∗
        REL (subst_map (fst ∘ fst <$> vs) e)
        <<  (subst_map (snd ∘ fst <$> vs) e')
        <<  (subst_map (snd <$> vs) e'') @ E
        : interp τ Δ)%I.

End tern_log_related.

Notation "'{' E ';' Θ ';' Δ ';' Γ '}' ⊨ e '≤log≤' e' '≤log≤' e'' : τ" :=
  (tern_log_related E Θ Δ Γ e%E e'%E e''%E τ%ty)
  (at level 100, E at next level, Δ, Θ at next level, Γ at next level, e, e', e'' at next level,
   τ at level 200,
   format "'[hv' '{' E ';'  Θ ';'  Δ ';'  Γ '}'  ⊨  '/  ' e  '/' '≤log≤'  '/  ' e'  '/' '≤log≤'  '/  ' e''  :  τ ']'").
Notation "'{' Θ ';' Δ ';' Γ '}' ⊨ e '≤log≤' e' '≤log≤' e'' : τ" :=
  (tern_log_related ⊤ Θ Δ Γ e%E e'%E e''%E (τ)%ty)
  (at level 100, Δ at next level, Γ at next level, e, e', e'' at next level,
   τ at level 200,
   format "'[hv' '{' Θ ';'  Δ ';'  Γ '}'  ⊨  '/  ' e  '/' '≤log≤'  '/  ' e'  '/' '≤log≤'  '/  ' e''  :  τ ']'").

(** * Unary semantic typing (prover) *)
Section un_log_related.
  Context `{authG Σ, seqG Σ}.

  Definition un_log_related (E : coPset) (Θ : Ctx kind)
    (Δ : ctxO Σ Θ) (Γ : stringmap (type Θ ⋆)) (eₚ : expr) (τ : type Θ ⋆) : iProp Σ :=
    (∀ (vs : gmap string val),
        ⟦ (λ (σ : type Θ ⋆), lrel_tern_un (interp σ Δ)) <$> Γ ⟧*ᵤ vs -∗
        PRV (subst_map vs eₚ) @ E
        : lrel_tern_un (interp τ Δ))%I.

End un_log_related.

Notation "'{' E ';' Θ ';' Δ ';' Γ '}' ⊨ᵤ eₚ : τ" :=
  (un_log_related E Θ Δ Γ eₚ%E τ%ty)
  (at level 100, E at next level, Δ, Θ at next level, Γ at next level, eₚ at next level,
   τ at level 200,
   format "'[hv' '{' E ';'  Θ ';'  Δ ';'  Γ '}'  ⊨ᵤ  '/  ' eₚ  :  τ ']'").
Notation "'{' Θ ';' Δ ';' Γ '}' ⊨ᵤ eₚ : τ" :=
  (un_log_related ⊤ Θ Δ Γ eₚ%E τ%ty)
  (at level 100, Δ at next level, Γ at next level, eₚ at next level,
   τ at level 200,
   format "'[hv' '{' Θ ';'  Δ ';'  Γ '}'  ⊨ᵤ  '/  ' eₚ  :  τ ']'").
