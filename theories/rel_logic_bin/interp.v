(** interpretations for System F_mu_ref types *)
From iris.algebra Require Export list.
From iris.proofmode Require Import proofmode.

From auth.typing Require Export types typing.
From auth.rel_logic_bin Require Import model.
From auth.prelude Require Import properness.

(** * Interpretation of kinds *)
Fixpoint kind_unO (Σ : gFunctors) (κ : kind) : ofe :=
  match κ with
  | KType => lrel_unC Σ
  | KArrow κ1 κ2 => kind_unO Σ κ1 -n> kind_unO Σ κ2
  end.

#[global] Instance kind_unO_cofe (Σ : gFunctors) (κ : kind) :
  Cofe (kind_unO Σ κ).
Proof. induction κ; apply _. Qed.

#[global] Instance kind_unO_Inhabited (Σ : gFunctors) (κ : kind) :
  Inhabited (kind_unO Σ κ).
Proof. induction κ; apply _. Qed.

Fixpoint kind_binO (Σ : gFunctors) (κ : kind) : ofe :=
  match κ with
  | KType => lrelC Σ
  | KArrow κ1 κ2 => kind_binO Σ κ1 -n> kind_binO Σ κ2
  end.

#[global] Instance kind_binO_cofe (Σ : gFunctors) (κ : kind) :
  Cofe (kind_binO Σ κ).
Proof. induction κ; apply _. Qed.

#[global] Instance kind_binO_Inhabited (Σ : gFunctors) (κ : kind) :
  Inhabited (kind_binO Σ κ).
Proof. induction κ; apply _. Qed.

(** ** Kind OFE *)
Fixpoint kindO (Σ : gFunctors) (κ : kind) : ofe :=
  match κ with
  | KType => lrel_biC Σ
  | KArrow κ1 κ2 => kindO Σ κ1 -n> kindO Σ κ2
  end.

#[global] Instance kindO_cofe (Σ : gFunctors) (κ : kind) : Cofe (kindO Σ κ).
Proof. induction κ; apply _. Qed.

#[global] Instance kindO_Inhabited (Σ : gFunctors) (κ : kind) : Inhabited (kindO Σ κ).
Proof. induction κ; apply _. Qed.

Program Fixpoint π_un {Σ} (κ : kind) : kindO Σ κ -n> kind_unO Σ κ :=
  match κ with
  | KType         => λne A, lrel_bi_un A
  | KArrow κ1 κ2  => λne f A_un, π_un κ2 (f (ι_un κ1 A_un))
  end with
ι_un {Σ} (κ : kind) : kind_unO Σ κ -n> kindO Σ κ :=
  match κ with
  | KType         => λne A_un, LRelBi A_un lrel_true
  | KArrow κ1 κ2  => λne f_un A, ι_un κ2 (f_un (π_un κ1 A))
  end.
Solve All Obligations with solve_proper.

Program Fixpoint π_bin {Σ} (κ : kind) : kindO Σ κ -n> kind_binO Σ κ :=
  match κ with
  | KType         => λne A, lrel_bi_bin A
  | KArrow κ1 κ2  => λne f A_bin, π_bin κ2 (f (ι_bin κ1 A_bin))
  end with
ι_bin {Σ} (κ : kind) : kind_binO Σ κ -n> kindO Σ κ :=
  match κ with
  | KType         => λne A_bin, LRelBi lrel_un_true A_bin
  | KArrow κ1 κ2  => λne f_bin A, ι_bin κ2 (f_bin (π_bin κ1 A))
  end.
Solve All Obligations with solve_proper.

Lemma π_un_ι_un_section {Σ} (κ : kind) (A_un : kind_unO Σ κ) :
  π_un κ (ι_un κ A_un) ≡ A_un.
Proof.
  induction κ as [| κ1 IH1 κ2 IH2].
  - done.
  - intro A_un'. simpl. rewrite IH2. f_equiv. apply IH1.
Qed.

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

  Program Definition ext {Σ Θ κ} : ctxO Σ Θ →  kindO Σ κ → ctxO Σ (Θ ▹ κ) := Inc.maybe.

  Program Definition interp_un_tvar {Θ : Ctx kind} {κ : kind} (x : dom Θ) (EQ : Θ x = κ) : ctxO Σ Θ -n> kind_unO Σ κ :=
    λne Δ, eq_rect (Θ x) (kind_unO Σ) (π_un (Θ x) (Δ x)) κ EQ.
  Solve Obligations with solve_proper.

  Program Definition interp_un_tlam {Θ κ1 κ2} (A2 : ctxO Σ (Θ ▹ κ1) -n> kind_unO Σ κ2) :
    ctxO Σ Θ -n> kind_unO Σ (κ1 ⇒ κ2) := λne Δ A1, A2 (ext Δ (ι_un κ1 A1)).
  Solve Obligations with (intros ????????? => /=; f_equiv; rewrite /ext; solve_proper).

  Program Definition interp_un_tapp {Θ κ1 κ2} (A : ctxO Σ Θ -n> kind_unO Σ (κ1 ⇒ κ2))
    (B : ctxO Σ Θ -n> kind_unO Σ κ1) : ctxO Σ Θ -n> kind_unO Σ κ2 := λne Δ, (A Δ) (B Δ).
  Solve Obligations with solve_proper.

  Definition lrel_un_ktype (C : lrel_unC Σ -n> lrel_unC Σ) (rec : lrel_unC Σ) : lrel_unC Σ :=
    LRelUn (λ w, ▷ C rec w)%I.

  Global Instance lrel_un_ktype_contractive C : Contractive (lrel_un_ktype C).
  Proof.
    intros n. intros P Q HPQ.
    intros w; rewrite /lrel_un_car /=.
    f_contractive; f_equiv; by apply C.
  Qed.

  Global Instance lrel_un_ktype_ne : NonExpansive2 lrel_un_ktype.
  Proof.
    intros n C1 C2 HC rec1 rec2 Hrec.
    intros w; rewrite /lrel_un_car /=.
    f_contractive; do 2 f_equiv;
      eapply dist_lt; try exact Hlt;
      try apply HC; try apply Hrec.
  Qed.

  Program Fixpoint interp_un_rec1 {κ} : (kind_unO Σ κ -n> kind_unO Σ κ) -n> kind_unO Σ κ -n> kind_unO Σ κ :=
    match κ with
    | ⋆%kind => λne C rec, lrel_un_ktype C rec
    | (κ1 ⇒ κ2)%kind => λne C rec A1, interp_un_rec1 (κ := κ2) cid (C rec A1)
    end.
  Solve Obligations with solve_proper.

  Global Instance interp_un_rec1_contractive {κ} (C : kind_unO Σ κ -n> kind_unO Σ κ) : Contractive (interp_un_rec1 C).
  Proof.
    induction κ => n P Q HPQ.
    - by f_contractive.
    - intros κ. eapply IHκ2. dist_later_intro. solve_proper.
  Qed.

  Lemma interp_un_rec1_shift κ (C : kind_unO Σ κ -n> kind_unO Σ κ) (rec : kind_unO Σ κ) :
    interp_un_rec1 C rec ≡ interp_un_rec1 cid (C rec).
  Proof. by destruct κ. Qed.

  Program Definition interp_un_rec {κ} : (kind_unO Σ κ -n> kind_unO Σ κ) -n> kind_unO Σ κ :=
    λne C, fixpoint (interp_un_rec1 C).
  Next Obligation.
    intros κ n F F' HF.
    apply fixpoint_ne=> X.
    solve_proper.
  Qed.
  Lemma interp_un_rec_unfold {κ} (C : kind_unO Σ κ -n> kind_unO Σ κ) :
    interp_un_rec C ≡ interp_un_rec1 C (interp_un_rec C).
  Proof. apply fixpoint_unfold. Qed.

  #[global] Opaque interp_un_rec.

  #[local] Definition interp_un_tconstr {Θ κ} (c : tconstr κ) : ctxO Σ Θ -n> kind_unO Σ κ := λne _,
    match c in tconstr κ return kind_unO Σ κ with
    | TUnit => lrel_un_unit
    | TNat => lrel_un_int
    | TBool => lrel_un_bool
    | TString => lrel_un_string
    | TProd => lrel_un_prod'
    | TSum => lrel_un_sum'
    | TArrow => lrel_un_arr'
    (* | TRef => lrel_un_ref' *)
    | TRec κ => interp_un_rec
    | TForall κ => lrel_un_forall'
    | TExists κ => lrel_un_exists'
    end.

  Program Definition interp_tvar {Θ : Ctx kind} {κ : kind} (x : dom Θ) (EQ : Θ x = κ) : ctxO Σ Θ -n> kindO Σ κ :=
    λne Δ, eq_rect (Θ x) (kindO Σ) (Δ x) κ EQ.
  Solve Obligations with solve_proper.

  Program Definition interp_tlam {Θ κ1 κ2} (A2 : ctxO Σ (Θ ▹ κ1) -n> kindO Σ κ2) :
    ctxO Σ Θ -n> kindO Σ (κ1 ⇒ κ2) := λne Δ A1, A2 (ext Δ A1).
  Solve Obligations with (intros ????????? => /=; f_equiv; rewrite /ext; solve_proper).

  Program Definition interp_tapp {Θ κ1 κ2} (A : ctxO Σ Θ -n> kindO Σ (κ1 ⇒ κ2))
    (B : ctxO Σ Θ -n> kindO Σ κ1) : ctxO Σ Θ -n> kindO Σ κ2 := λne Δ, (A Δ) (B Δ).
  Solve Obligations with solve_proper.

  Definition lrel_ktype (C : lrel_biC Σ -n> lrel_biC Σ) (rec : lrel_biC Σ) : lrel_biC Σ :=
    LRelBi (LRelUn (λ w, ▷ lrel_bi_un (C rec) w)%I)
           (LRel (λ w1 w2, ▷ lrel_bi_bin (C rec) w1 w2)%I).

  Global Instance lrel_ktype_contractive C : Contractive (lrel_ktype C).
  Proof.
    intros n. intros P Q HPQ.
    split; [intros w; rewrite /lrel_un_car /= |
             intros w1 w2; rewrite /lrel_car /=];
    f_contractive; f_equiv; by apply C.
  Qed.

  Global Instance lrel_ktype_ne : NonExpansive2 lrel_ktype.
  Proof.
    intros n C1 C2 HC rec1 rec2 Hrec.
    split; [intros w; rewrite /lrel_un_car /= |
             intros w1 w2; rewrite /lrel_car /=];
      f_contractive; do 3 f_equiv;
      eapply dist_lt; try exact Hlt;
      try apply HC; try apply Hrec.
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

  Definition lrel_bi_prod (A B : lrel_biC Σ) : lrel_biC Σ :=
    LRelBi (lrel_un_prod' (lrel_bi_un A) (lrel_bi_un B))
           (lrel_prod' (lrel_bi_bin A) (lrel_bi_bin B)).
  Program Definition lrel_bi_prod' : lrel_biC Σ -n> lrel_biC Σ -n> lrel_biC Σ :=
    λne A B, lrel_bi_prod A B.
  Solve Obligations with intros ?????; split; solve_proper.

  Definition lrel_bi_sum (A B : lrel_biC Σ) : lrel_biC Σ :=
    LRelBi (lrel_un_sum' (lrel_bi_un A) (lrel_bi_un B))
           (lrel_sum' (lrel_bi_bin A) (lrel_bi_bin B)).
  Program Definition lrel_bi_sum' : lrel_biC Σ -n> lrel_biC Σ -n> lrel_biC Σ :=
    λne A B, lrel_bi_sum A B.
  Solve Obligations with intros ?????; split; solve_proper.

  (** The binary arrow takes/returns the full conjunction so that the body IH
      can use the conjunction environment and produce a conjunction result. *)
  Definition lrel_bi_arr (A B : lrel_biC Σ) : lrel_biC Σ :=
    LRelBi (lrel_un_arr' (lrel_bi_un A) (lrel_bi_un B))
           (lrel_arr' (lrel_bi_as_lrel A) (lrel_bi_as_lrel B)).
  Program Definition lrel_bi_arr' : lrel_biC Σ -n> lrel_biC Σ -n> lrel_biC Σ :=
    λne A B, lrel_bi_arr A B.
  Solve Obligations with intros ?????; split; solve_proper.

  (* Definition lrel_bi_ref (A : lrel_biC Σ) : lrel_biC Σ :=
    LRelBi (lrel_un_ref' (lrel_bi_un A)) (lrel_ref' (lrel_bi_bin A)).
  Program Definition lrel_bi_ref' : lrel_biC Σ -n> lrel_biC Σ :=
    λne A, lrel_bi_ref A.
  Solve Obligations with intros ????; split; solve_proper. *)

  Program Definition lrel_bi_forall {κ} : (kindO Σ κ -n> lrel_biC Σ) -n> lrel_biC Σ :=
    λne C, LRelBi
      (LRelUn (λ w, ∀ A : kindO Σ κ, (lrel_un_arr lrel_un_true (lrel_bi_un (C A))) w)%I)
      (LRel (λ w1 w2, ∀ A : kindO Σ κ, (lrel_arr lrel_true (lrel_bi_as_lrel (C A))) w1 w2)%I).
  Solve Obligations with intros ????; split; solve_proper.

  Program Definition lrel_bi_exists {κ} : (kindO Σ κ -n> lrel_biC Σ) -n> lrel_biC Σ :=
    λne C, LRelBi
      (LRelUn (λ w, ∃ A : kindO Σ κ, lrel_bi_un (C A) w)%I)
      (LRel (λ w1 w2, ∃ A : kindO Σ κ, (lrel_bi_as_lrel (C A)) w1 w2)%I).
  Next Obligation.
    intros κ n C1 C2 HC. split.
    - intros w. rewrite /lrel_bi_un /lrel_un_car /=.
      f_equiv => A. apply lrel_bi_un_ne, HC.
    - intros w1 w2. rewrite /lrel_bi_as_lrel /lrel_car /=.
      f_equiv => A. apply lrel_bi_as_lrel_ne, HC.
  Qed.

  #[local] Definition interp_tconstr {Θ κ} (c : tconstr κ) : ctxO Σ Θ -n> kindO Σ κ := λne _,
    match c in tconstr κ return kindO Σ κ with
    | TUnit    => LRelBi lrel_un_unit   lrel_unit
    | TNat     => LRelBi lrel_un_int    lrel_int
    | TBool    => LRelBi lrel_un_bool   lrel_bool
    | TString  => LRelBi lrel_un_string lrel_string
    | TProd    => lrel_bi_prod'
    | TSum     => lrel_bi_sum'
    | TArrow   => lrel_bi_arr'
    (* | TRef     => lrel_bi_ref' *)
    | TRec κ   => interp_rec
    | TForall κ => lrel_bi_forall
    | TExists κ => lrel_bi_exists
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

  #[local] Fixpoint interp_un_def {Θ κ} (τ : typ κ Θ) : ctxO Σ Θ -n> kind_unO Σ κ :=
    match τ in type _ κ return ctxO Σ Θ -n> kind_unO Σ κ with
    | TVar x EQ   => interp_un_tvar x EQ
    | TLam τ      => interp_un_tlam (interp_un_def τ)
    | TApp τ τ'   => interp_un_tapp (interp_un_def τ) (interp_un_def τ')
    | TConstr c   => interp_un_tconstr c
    end.

  #[local] Definition interp_un_aux : seal (@interp_un_def). Proof. by eexists. Qed.
  Definition interp_un := interp_un_aux.(unseal).
  Definition interp_un_unseal : @interp_un = @interp_un_def := interp_un_aux.(seal_eq).
  #[global] Arguments interp_un {Θ κ} τ.

End semtypes.

Notation "⟦ τ ⟧" := (interp τ).
Notation "⟦ τ ⟧_un" := (interp_un τ).

Section semtypes_lemmas.
  Context `{!authG Σ, !seqG Σ}.

  Lemma unboxed_type_sound Θ (τ : type Θ ⋆) Δ v v' :
    UnboxedType τ →
    lrel_bi_bin (interp τ Δ) v v' ⊢ ⌜val_is_unboxed v ∧ val_is_unboxed v'⌝.
  Proof.
    rewrite interp_unseal.
    induction 1; simpl.
    - by iDestruct 1 as "[-> ->]".
    - by iDestruct 1 as (?) "[-> ->]".
    - by iDestruct 1 as (?) "[-> ->]".
    (* - by iDestruct 1 as (?? -> ->) "H". *)
  Qed.

  Lemma eq_type_sound_bin Θ (τ : type Θ ⋆) Δ v v' :
    EqType τ →
    lrel_bi_bin (interp τ Δ) v v' ⊢ ⌜v = v'⌝.
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

  Lemma eq_type_sound Θ (τ : type Θ ⋆) Δ v v':
    EqType τ →
    interp τ Δ v v' ⊢ ⌜v = v'⌝.
  Proof. intros Hτ. iIntros "[H _]". by iApply eq_type_sound_bin. Qed.

  Lemma unboxed_type_eq Θ (τ : type Θ ⋆) Δ v1 v2 w1 w2 :
    UnboxedType τ →
    interp τ Δ v1 v2 -∗
    interp τ Δ w1 w2 -∗
    |={⊤}=> ⌜v1 = w1 ↔ v2 = w2⌝.
  Proof.
    intros Hunboxed.
    cut (EqType τ).
    { intros Hτ.
      rewrite !eq_type_sound //.
      iIntros "% %". iModIntro.
      iPureIntro. naive_solver. }
    inversion Hunboxed; econstructor.
  Qed.

End semtypes_lemmas.

Section semtype_unfold_lemmas.
  Context `{!authG Σ, !seqG Σ}.
  Context {Θ : Ctx kind} (Δ : ctxO Σ Θ).

  Lemma interp_unit_unfold :
    lrel_bi_bin (⟦ () ⟧ Δ)%lrel ≡ lrel_unit.
  Proof. rewrite interp_unseal //. Qed.
  Lemma interp_nat_unfold:
    lrel_bi_bin (⟦ t_nat ⟧ Δ) ≡ lrel_int.
  Proof. rewrite interp_unseal //. Qed.
  Lemma interp_bool_unfold :
    lrel_bi_bin (⟦ t_bool ⟧ Δ) ≡ lrel_bool.
  Proof. rewrite interp_unseal //. Qed.
  Lemma interp_string_unfold :
    lrel_bi_bin (⟦ t_string ⟧ Δ) ≡ lrel_string.
  Proof. rewrite interp_unseal //. Qed.
  Lemma interp_prod_unfold τ1 τ2 :
    lrel_bi_bin (⟦ τ1 * τ2 ⟧ Δ) ≡ lrel_prod (lrel_bi_bin (⟦ τ1 ⟧ Δ)) (lrel_bi_bin (⟦ τ2 ⟧ Δ)).
  Proof. rewrite interp_unseal //. Qed.
  Lemma interp_sum_unfold τ1 τ2 :
    lrel_bi_bin (⟦ τ1 + τ2 ⟧ Δ) ≡ lrel_sum (lrel_bi_bin (⟦ τ1 ⟧ Δ)) (lrel_bi_bin (⟦ τ2 ⟧ Δ)).
  Proof. rewrite interp_unseal //. Qed.
  Lemma interp_arr_unfold τ1 τ2 :
    lrel_bi_bin (⟦ τ1 → τ2 ⟧ Δ) ≡ lrel_arr (⟦ τ1 ⟧ Δ) (⟦ τ2 ⟧ Δ).
  Proof. rewrite interp_unseal //. Qed.
  Lemma interp_un_arr_unfold τ1 τ2 :
    lrel_bi_un (⟦ τ1 → τ2 ⟧ Δ) ≡ lrel_un_arr (lrel_bi_un (⟦ τ1 ⟧ Δ)) (lrel_bi_un (⟦ τ2 ⟧ Δ)).
  Proof. rewrite interp_unseal //. Qed.
  Lemma interp_un_prod_unfold τ1 τ2 v :
    lrel_bi_un (⟦ τ1 * τ2 ⟧ Δ) v ≡ lrel_un_prod (lrel_bi_un (⟦ τ1 ⟧ Δ)) (lrel_bi_un (⟦ τ2 ⟧ Δ)) v.
  Proof. rewrite interp_unseal //. Qed.
  Lemma interp_un_sum_unfold τ1 τ2 v :
    lrel_bi_un (⟦ τ1 + τ2 ⟧ Δ) v ≡ lrel_un_sum (lrel_bi_un (⟦ τ1 ⟧ Δ)) (lrel_bi_un (⟦ τ2 ⟧ Δ)) v.
  Proof. rewrite interp_unseal //. Qed.
  Lemma interp_un_exists_unfold (κ : kind) (τ : type (Θ ▹ κ) ⋆) v :
    lrel_bi_un (⟦ ∃: κ, τ ⟧ Δ) v ≡ (∃ A, lrel_bi_un (⟦ τ ⟧ (ext Δ A)) v)%I.
  Proof. rewrite interp_unseal //. Qed.

  Lemma interp_rec_star_bin_unfold (τ : type (Θ ▹ ⋆)%kind ⋆) v1 v2 :
    lrel_bi_bin (⟦ μ: ⋆; τ ⟧ Δ) v1 v2 ≡ (▷ lrel_bi_bin (⟦ τ ⟧ (ext Δ (⟦ μ: ⋆; τ ⟧ Δ))) v1 v2)%I.
  Proof.
    rewrite interp_unseal /interp_def /= -/interp_def.
    rewrite {1}interp_rec_unfold //.
  Qed.
  Lemma interp_rec_star_un_unfold (τ : type (Θ ▹ ⋆)%kind ⋆) v :
    lrel_bi_un (⟦ μ: ⋆; τ ⟧ Δ) v ≡ (▷ lrel_bi_un (⟦ τ ⟧ (ext Δ (⟦ μ: ⋆; τ ⟧ Δ))) v)%I.
  Proof.
    rewrite interp_unseal /interp_def /= -/interp_def.
    rewrite {1}interp_rec_unfold //.
  Qed.
  (** Combined unfold: uses later_and to package both components *)
  Lemma interp_rec_star_unfold (τ : type (Θ ▹ ⋆)%kind ⋆) v1 v2 :
    (⟦ μ: ⋆; τ ⟧ Δ : lrel Σ) v1 v2 ≡
    (▷ (⟦ τ ⟧ (ext Δ (⟦ μ: ⋆; τ ⟧ Δ)) : lrel Σ) v1 v2)%I.
  Proof.
    trans (lrel_bi_bin (⟦ μ: ⋆; τ ⟧ Δ) v1 v2 ∧ lrel_bi_un (⟦ μ: ⋆; τ ⟧ Δ) v1)%I.
    { rewrite /lrel_bi_as_lrel. cbv [lrel_car]. done. }
    rewrite interp_rec_star_bin_unfold interp_rec_star_un_unfold -bi.later_and.
    f_equiv. rewrite /lrel_bi_as_lrel. cbv [lrel_car]. done.
  Qed.
  Lemma interp_forall_unfold (κ : kind) (τ : type (Θ ▹ κ) ⋆) v1 v2 :
    lrel_bi_bin (⟦ ∀: κ, τ ⟧ Δ) v1 v2 ≡
      (∀ A, lrel_arr lrel_true (⟦ τ ⟧ (ext Δ A)) v1 v2)%I.
  Proof. rewrite interp_unseal //. Qed.
  Lemma interp_un_forall_unfold (κ : kind) (τ : type (Θ ▹ κ) ⋆) v :
    lrel_bi_un (⟦ ∀: κ, τ ⟧ Δ) v ≡
      (∀ A, lrel_un_arr lrel_un_true (lrel_bi_un (⟦ τ ⟧ (ext Δ A))) v)%I.
  Proof. rewrite interp_unseal //. Qed.

  Lemma interp_exists_unfold (κ : kind) (τ : type (Θ ▹ κ) ⋆) v1 v2 :
    lrel_bi_bin (⟦ ∃: κ, τ ⟧ Δ) v1 v2 ≡ (∃ A, (⟦ τ ⟧ (ext Δ A) : lrel Σ) v1 v2)%I.
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

Lemma interp_var0_ext1 {κ} (A : kindO Σ κ) :
  interp (var0 : type (Θ ▹ κ) κ) (ext Δ A) = A.
Proof. rewrite interp_unseal /= //. Qed.

Lemma interp_var1_ext2 {κ1 κ2} (F : kindO Σ κ1) (A : kindO Σ κ2) :
  interp (var1 : type (Θ ▹ κ1 ▹ κ2) κ1) (ext (ext Δ F) A) = F.
Proof. rewrite interp_unseal /= //. Qed.

Lemma interp_var2_ext3 {κ1 κ2 κ3} (F : kindO Σ κ1) (A : kindO Σ κ2) (B : kindO Σ κ3) :
  interp (var2 : type (Θ ▹ κ1 ▹ κ2 ▹ κ3) κ1) (ext (ext (ext Δ F) A) B) = F.
Proof. rewrite interp_unseal /= //. Qed.

Lemma interp_var3_ext4 {κ1 κ2 κ3 κ4} (F : kindO Σ κ1)
    (A : kindO Σ κ2) (B : kindO Σ κ3) (C : kindO Σ κ4) :
  interp (var3 : type (Θ ▹ κ1 ▹ κ2 ▹ κ3 ▹ κ4) κ1) (ext (ext (ext (ext Δ F) A) B) C) = F.
Proof. rewrite interp_unseal /= //. Qed.

Lemma interp_var4_ext5 {κ1 κ2 κ3 κ4 κ5} (F : kindO Σ κ1)
    (A : kindO Σ κ2) (B : kindO Σ κ3) (C : kindO Σ κ4) (D' : kindO Σ κ5) :
  interp (var4 : type (Θ ▹ κ1 ▹ κ2 ▹ κ3 ▹ κ4 ▹ κ5) κ1)
         (ext (ext (ext (ext (ext Δ F) A) B) C) D') = F.
Proof. rewrite interp_unseal /= //. Qed.

Lemma interp_var5_ext6 {κ1 κ2 κ3 κ4 κ5 κ6} (F : kindO Σ κ1)
    (A : kindO Σ κ2) (B : kindO Σ κ3) (C : kindO Σ κ4) (D' : kindO Σ κ5) (E' : kindO Σ κ6) :
  interp (var5 : type (Θ ▹ κ1 ▹ κ2 ▹ κ3 ▹ κ4 ▹ κ5 ▹ κ6) κ1)
         (ext (ext (ext (ext (ext (ext Δ F) A) B) C) D') E') = F.
Proof. rewrite interp_unseal /= //. Qed.

End semtype_unfold_lemmas.

Ltac interp_unfold_tac :=
  match goal with
  | |- context [interp t_unit] => rewrite interp_unit_unfold
  | |- context [interp t_nat] => rewrite interp_nat_unfold
  | |- context [interp t_bool] => rewrite interp_bool_unfold
  | |- context [interp t_string] => rewrite interp_string_unfold

  (* unary forms — must come before binary to avoid failed interp_prod_unfold attempts *)
  | |- context [lrel_bi_un (⟦ _ * _ ⟧ _) _] => rewrite interp_un_prod_unfold
  | |- context [lrel_bi_un (⟦ _ + _ ⟧ _) _] => rewrite interp_un_sum_unfold
  | |- context [lrel_bi_un (⟦ _ → _ ⟧ _)]   => rewrite interp_un_arr_unfold
  | |- context [lrel_bi_un (⟦ ∀: _, _ ⟧ _) _] => rewrite interp_un_forall_unfold
  | |- context [lrel_bi_un (⟦ ∃: _, _ ⟧ _) _] => rewrite interp_un_exists_unfold

  | |- context [interp (t_prod _ _)] => rewrite interp_prod_unfold
  | |- context [interp (t_sum _ _)] => rewrite interp_sum_unfold
  | |- context [interp (t_option _)] => rewrite interp_sum_unfold
  | |- context [interp (t_arr _ _)] => rewrite interp_arr_unfold

  | |- context [interp (t_forall _ _)] => rewrite interp_forall_unfold
  | |- context [interp (t_exists _ _)] => rewrite interp_exists_unfold

  | |- context [interp (TApp _ _)] => rewrite interp_app_unfold

  | |- context[ofe_mor_car _ _ (interp var0) (ext _ _)] =>
      rewrite interp_var0_ext1
  | |- context[ofe_mor_car _ _ (interp var1) (ext (ext _ _) _)] =>
      rewrite interp_var1_ext2
  | |- context[ofe_mor_car _ _ (interp var2) (ext (ext (ext _ _) _) _)] =>
      rewrite interp_var2_ext3
  | |- context[ofe_mor_car _ _ (interp var3) (ext (ext (ext (ext _ _) _) _) _)] =>
      rewrite interp_var3_ext4
  | |- context[ofe_mor_car _ _ (interp var4) (ext (ext (ext (ext (ext _ _) _) _) _) _)] =>
      rewrite interp_var4_ext5
  | |- context[ofe_mor_car _ _ (interp var5) (ext (ext (ext (ext (ext (ext _ _) _) _) _) _) _)] =>
      rewrite interp_var5_ext6
  end.

Tactic Notation "interp_unfold":= iEval (interp_unfold_tac).
Tactic Notation "interp_unfold" "!" := iEval (repeat interp_unfold_tac).
Tactic Notation "interp_unfold" "in" constr(H) := iEval (repeat interp_unfold_tac) in H.
Tactic Notation "interp_unfold" "!" "in" constr(H) := iEval (repeat interp_unfold_tac) in H.

(** * Proof mode instances that will allow us to avoid manually unsealing/unfolding [interp] in many situations *)

(** unit  *)
#[global] Instance into_and_interp_t_unit `{authG Σ, seqG Σ} {Θ} (Δ : ctxO Σ Θ) (w1 w2 : val) b :
  IntoAnd b (⟦ () ⟧ Δ w1 w2)%I (⌜w1 = #()⌝)%I (⌜w2 = #()⌝)%I.
Proof.
  rewrite /IntoAnd. destruct b; simpl.
  all: iIntros "#H"; iDestruct "H" as "[Hbin _]";
       iEval (rewrite interp_unit_unfold /lrel_unit) in "Hbin";
       iEval (cbv [lrel_car]) in "Hbin";
       iDestruct "Hbin" as %[-> ->]; auto.
Qed.
#[global] Instance from_and_interp_t_unit `{authG Σ, seqG Σ} {Θ} (Δ : ctxO Σ Θ) (w1 w2 : val) :
  FromAnd (⟦ () ⟧ Δ w1 w2)%I (⌜w1 = #()⌝)%I (⌜w2 = #()⌝)%I .
Proof.
  rewrite /FromAnd. iIntros "#[%Hw1 %Hw2]". subst.
  iSplit.
  { iEval (rewrite interp_unit_unfold /lrel_unit; cbv [lrel_car]). iPureIntro. done. }
  rewrite interp_unseal /= /lrel_un_unit /=. iPureIntro. done.
Qed.

(** bool *)
#[global] Instance into_exist_interp_t_bool `{authG Σ, seqG Σ} {Θ} (Δ : ctxO Σ Θ) (w1 w2 : val) name :
  AsIdentName (λ (b : bool), ⌜w1 = #b ∧ w2 = #b⌝ : iProp Σ)%I name →
  IntoExist (⟦ t_bool ⟧ Δ w1 w2)%I (λ (b : bool), ⌜w1 = #b ∧ w2 = #b⌝)%I name.
Proof.
  intros _. rewrite /IntoExist. iIntros "#H". iDestruct "H" as "[Hbin _]".
  iEval (rewrite interp_bool_unfold /lrel_bool; cbv [lrel_car]) in "Hbin". iExact "Hbin".
Qed.
#[global] Instance from_exist_interp_t_bool `{authG Σ, seqG Σ} {Θ} (Δ : ctxO Σ Θ) (w1 w2 : val) :
  FromExist (⟦ t_bool ⟧ Δ w1 w2)%I (λ (b : bool), ⌜w1 = #b ∧ w2 = #b⌝)%I.
Proof.
  rewrite /FromExist. iIntros "#H". iDestruct "H" as (b) "%Hb". destruct Hb as [-> ->].
  iSplit.
  { iEval (rewrite interp_bool_unfold /lrel_bool; cbv [lrel_car]). iExists b. iPureIntro. done. }
  { rewrite interp_unseal /= /lrel_un_bool /=. iExists b. iPureIntro. done. }
Qed.

(** nat *)
#[global] Instance into_exist_interp_t_nat `{authG Σ, seqG Σ} {Θ} (Δ : ctxO Σ Θ) (w1 w2 : val) name :
  AsIdentName (λ (b : Z), ⌜w1 = #b ∧ w2 = #b⌝ : iProp Σ)%I name →
  IntoExist (⟦ t_nat ⟧ Δ w1 w2)%I (λ (b : Z), ⌜w1 = #b ∧ w2 = #b⌝)%I name.
Proof.
  intros _. rewrite /IntoExist. iIntros "#H". iDestruct "H" as "[Hbin _]".
  iEval (rewrite interp_nat_unfold /lrel_int; cbv [lrel_car]) in "Hbin". iExact "Hbin".
Qed.
#[global] Instance from_exist_interp_t_nat `{authG Σ, seqG Σ} {Θ} (Δ : ctxO Σ Θ) (w1 w2 : val) :
  FromExist (⟦ t_nat ⟧ Δ w1 w2)%I (λ (b : Z), ⌜w1 = #b ∧ w2 = #b⌝)%I.
Proof.
  rewrite /FromExist. iIntros "#H". iDestruct "H" as (n) "%Hn". destruct Hn as [-> ->].
  iSplit.
  { iEval (rewrite interp_nat_unfold /lrel_int; cbv [lrel_car]). iExists n. iPureIntro. done. }
  { rewrite interp_unseal /= /lrel_un_int /=. iExists n. iPureIntro. done. }
Qed.

(** string *)
#[global] Instance into_exist_interp_t_string `{authG Σ, seqG Σ} {Θ} (Δ : ctxO Σ Θ) (w1 w2 : val) name :
  AsIdentName (λ (b : string), ⌜w1 = #b ∧ w2 = #b⌝ : iProp Σ)%I name →
  IntoExist (⟦ t_string ⟧ Δ w1 w2)%I (λ (b : string), ⌜w1 = #b ∧ w2 = #b⌝)%I name.
Proof.
  intros _. rewrite /IntoExist. iIntros "#H". iDestruct "H" as "[Hbin _]".
  iEval (rewrite interp_string_unfold /lrel_string; cbv [lrel_car]) in "Hbin". iExact "Hbin".
Qed.
#[global] Instance from_exist_interp_t_string `{authG Σ, seqG Σ} {Θ} (Δ : ctxO Σ Θ) (w1 w2 : val) :
  FromExist (⟦ t_string ⟧ Δ w1 w2)%I (λ (b : string), ⌜w1 = #b ∧ w2 = #b⌝)%I.
Proof.
  rewrite /FromExist. iIntros "#H". iDestruct "H" as (s) "%Hs". destruct Hs as [-> ->].
  iSplit.
  { iEval (rewrite interp_string_unfold /lrel_string; cbv [lrel_car]). iExists s. iPureIntro. done. }
  { rewrite interp_unseal /= /lrel_un_string /=. iExists s. iPureIntro. done. }
Qed.

(** arrow: IntoForall extracts the binary component *)
#[global] Instance into_forall_interp_t_arr `{authG Σ, seqG Σ} {Θ} (Δ : ctxO Σ Θ) (τ1 τ2 : type Θ ⋆) (w1 w2 : val) :
  IntoForall (⟦ τ1 → τ2 ⟧ Δ w1 w2)
    (λ (v1 : val), □ ∀ v2, ⟦ τ1 ⟧ Δ v1 v2 -∗ REL App w1 v1 << App w2 v2 @ ⊤ : (⟦ τ2 ⟧ Δ))%I.
Proof.
  rewrite /IntoForall. iIntros "#H". iDestruct "H" as "[Hbin _]".
  iEval (rewrite interp_arr_unfold /lrel_arr; cbv [lrel_car]) in "Hbin".
  iIntros (x). by iApply ("Hbin" $! x).
Qed.

(** product *)
#[global] Instance into_exist_interp_t_prod `{authG Σ, seqG Σ} {Θ} (Δ : ctxO Σ Θ) (τ1 τ2 : type Θ ⋆) (w1 w2 : val) name :
  AsIdentName (λ (v1 : val), ∃ v2 v1' v2',
        ⌜w1 = (v1,v1')%V⌝ ∧ ⌜w2 = (v2,v2')%V⌝ ∧ ⟦ τ1 ⟧ Δ v1 v2 ∗ ⟦ τ2 ⟧ Δ v1' v2')%I name →
  IntoExist (⟦ τ1 * τ2 ⟧ Δ w1 w2)
    (λ (v1 : val), ∃ v2 v1' v2', ⌜w1 = (v1,v1')%V⌝ ∧ ⌜w2 = (v2,v2')%V⌝ ∧ ⟦ τ1 ⟧ Δ v1 v2 ∗ ⟦ τ2 ⟧ Δ v1' v2')%I name.
Proof.
  intros _. rewrite /IntoExist. iIntros "#H". iDestruct "H" as "[#Hbin #Hun]".
  iEval (rewrite interp_prod_unfold /lrel_prod; cbv [lrel_car]) in "Hbin".
  iEval (rewrite interp_un_prod_unfold /lrel_un_prod; cbv [lrel_un_car]) in "Hun".
  iDestruct "Hbin" as (v1 v2 v1' v2') "[%Hw1 [%Hw2 [#H1bin #H2bin]]]".
  iDestruct "Hun" as (u u') "[%Hw1' [#H1un #H2un]]".
  simplify_eq/=.
  iExists u. iExists v2, u', v2'. iSplit; [done|]. iSplit; [done|].
  iSplitL "H1bin H1un". { iSplit; [iExact "H1bin" | iExact "H1un"]. } { iSplit; [iExact "H2bin" | iExact "H2un"]. }
Qed.
#[global] Instance from_exist_interp_t_prod `{authG Σ, seqG Σ} {Θ} (Δ : ctxO Σ Θ) (τ1 τ2 : type Θ ⋆) (w1 w2 : val):
  FromExist (⟦ τ1 * τ2 ⟧ Δ w1 w2) (λ (v1 : val),
      ∃ v2 v1' v2', ⌜w1 = (v1,v1')%V⌝ ∧ ⌜w2 = (v2,v2')%V⌝ ∧ ⟦ τ1 ⟧ Δ v1 v2 ∗ ⟦ τ2 ⟧ Δ v1' v2')%I.
Proof.
  rewrite /FromExist. iIntros "#H".
  iDestruct "H" as (v1 v2 v1' v2') "(% & % & [#H1bin #H1un] & [#H2bin #H2un])".
  subst.
  iSplit.
  { iEval (rewrite interp_prod_unfold /lrel_prod; cbv [lrel_car]).
    iExists v1, v2, v1', v2'. do 2 (iSplit; [done|]). iSplit; [iExact "H1bin" | iExact "H2bin"]. }
  { iEval (rewrite interp_un_prod_unfold /lrel_un_prod; cbv [lrel_un_car]).
    iExists v1, v1'. iSplit; [done|]. iSplit; [iExact "H1un" | iExact "H2un"]. }
Qed.

(** sum *)
#[global] Instance into_exist_interp_t_sum `{authG Σ, seqG Σ} {Θ} (Δ : ctxO Σ Θ) (τ1 τ2 : type Θ ⋆) (w1 w2 : val) name :
  AsIdentName (λ (v1 : val), ∃ v2,
      (⌜w1 = InjLV v1⌝ ∧ ⌜w2 = InjLV v2⌝ ∧ ⟦ τ1 ⟧ Δ v1 v2) ∨ (⌜w1 = InjRV v1⌝ ∧ ⌜w2 = InjRV v2⌝ ∧ ⟦ τ2 ⟧ Δ v1 v2))%I name →
  IntoExist (⟦ τ1 + τ2 ⟧ Δ w1 w2)
    (λ (v1 : val), ∃ v2,
      (⌜w1 = InjLV v1⌝ ∧ ⌜w2 = InjLV v2⌝ ∧ ⟦ τ1 ⟧ Δ v1 v2) ∨ (⌜w1 = InjRV v1⌝ ∧ ⌜w2 = InjRV v2⌝ ∧ ⟦ τ2 ⟧ Δ v1 v2))%I name.
Proof.
  intros _. rewrite /IntoExist. iIntros "#H". iDestruct "H" as "[#Hbin #Hun]".
  iEval (rewrite interp_sum_unfold /lrel_sum; cbv [lrel_car]) in "Hbin".
  iEval (rewrite interp_un_sum_unfold /lrel_un_sum; cbv [lrel_un_car]) in "Hun".
  iDestruct "Hbin" as (v1 v2) "#[(% & % & #Hbin1) | (% & % & #Hbin2)]".
  - iDestruct "Hun" as (u) "#[(% & #Hun1) | (% & #Hun2)]"; simplify_eq/=.
    iExists u, v2. iLeft. iSplit; [done|]. iSplit; [done|].
    iSplit; [iExact "Hbin1" | iExact "Hun1"].
  - iDestruct "Hun" as (u) "#[(% & #Hun1) | (% & #Hun2)]"; simplify_eq/=.
    iExists u, v2. iRight. iSplit; [done|]. iSplit; [done|].
    iSplit; [iExact "Hbin2" | iExact "Hun2"].
Qed.
#[global] Instance from_exist_interp_t_sum `{authG Σ, seqG Σ} {Θ} (Δ : ctxO Σ Θ) (τ1 τ2 : type Θ ⋆) (w1 w2 : val) :
  FromExist (⟦ τ1 + τ2 ⟧ Δ w1 w2)
    (λ (v1 : val), ∃ v2,
      (⌜w1 = InjLV v1⌝ ∧ ⌜w2 = InjLV v2⌝ ∧ ⟦ τ1 ⟧ Δ v1 v2) ∨ (⌜w1 = InjRV v1⌝ ∧ ⌜w2 = InjRV v2⌝ ∧ ⟦ τ2 ⟧ Δ v1 v2))%I.
Proof.
  rewrite /FromExist. iIntros "#H".
  iDestruct "H" as (v1 v2) "#[(% & % & [#Hbin1 #Hun1]) | (% & % & [#Hbin2 #Hun2])]". subst.
  - iSplit.
    { iEval (rewrite interp_sum_unfold /lrel_sum; cbv [lrel_car]).
      iExists v1, v2. iLeft. iSplit; [done|]. iSplit; [done|]. iExact "Hbin1". }
    { iEval (rewrite interp_un_sum_unfold /lrel_un_sum; cbv [lrel_un_car]).
      iExists v1. iLeft. iSplit; [done|]. iExact "Hun1". }
  - iSplit.
    { iEval (rewrite interp_sum_unfold /lrel_sum; cbv [lrel_car]).
      iExists v1, v2. iRight. iSplit; [done|]. iSplit; [done|]. iExact "Hbin2". }
    { iEval (rewrite interp_un_sum_unfold /lrel_un_sum; cbv [lrel_un_car]).
      iExists v1. iRight. iSplit; [done|]. iExact "Hun2". }
Qed.

(** forall: IntoForall extracts binary component *)
#[global] Instance into_forall_interp_t_forall `{authG Σ, seqG Σ} {Θ} (Δ : ctxO Σ Θ) κ (τ : type (Θ ▹ κ) ⋆) (v1 v2 : val) :
  IntoForall (⟦ ∀: κ, τ ⟧ Δ v1 v2) (λ A, (lrel_true → (⟦ τ ⟧ (ext Δ A)))%lrel v1 v2).
Proof.
  rewrite /IntoForall. iIntros "#H". iDestruct "H" as "[Hbin _]".
  iEval (rewrite interp_forall_unfold; cbv [lrel_car]) in "Hbin".
  iIntros (A). by iApply ("Hbin" $! A).
Qed.

(** exist *)
#[global] Instance into_exist_interp_t_exists `{authG Σ, seqG Σ} {Θ} (Δ : ctxO Σ Θ) κ (τ : type (Θ ▹ κ) ⋆) (v1 v2 : val) name :
  AsIdentName (λ A, ⟦ τ ⟧ (ext Δ A) v1 v2) name →
  IntoExist (⟦ ∃: κ, τ ⟧ Δ v1 v2) (λ A, ⟦ τ ⟧ (ext Δ A) v1 v2) name.
Proof.
  intros _. rewrite /IntoExist. iIntros "#H". iDestruct "H" as "[Hbin _]".
  iEval (rewrite interp_exists_unfold; cbv [lrel_car]) in "Hbin".
  iDestruct "Hbin" as (A) "#HA". iExists A. iExact "HA".
Qed.
#[global] Instance from_exist_interp_t_exists `{authG Σ, seqG Σ} {Θ} (Δ : ctxO Σ Θ) κ (τ : type (Θ ▹ κ) ⋆) (v1 v2 : val):
  FromExist (⟦ ∃: κ, τ ⟧ Δ v1 v2) (λ A, ⟦ τ ⟧ (ext Δ A) v1 v2).
Proof.
  rewrite /FromExist. iIntros "#H". iDestruct "H" as (A) "[#HAbin #HAun]".
  iSplit.
  { iEval (rewrite interp_exists_unfold; cbv [lrel_car]). iExists A. iSplit; [iExact "HAbin" | iExact "HAun"]. }
  { iEval (rewrite interp_un_exists_unfold). iExists A. iExact "HAun". }
Qed.

(* (** ref  *)
#[global] Instance into_exist_interp_t_ref `{authG Σ, seqG Σ} {Θ} (Δ : ctxO Σ Θ) (τ : type Θ ⋆) (w1 w2 : val) name :
  AsIdentName (λ (l1 : loc), ∃ l2 : loc, ⌜w1 = #l1⌝ ∧ ⌜w2 = #l2⌝ ∧
      inv (authN .@ "ref" .@ (l1,l2)) (∃ v1 v2, l1 ↦ v1 ∗ l2 ↦ᵢ v2 ∗ ⟦ τ ⟧ Δ v1 v2))%I name →
  IntoExist (⟦ ref τ ⟧ Δ w1 w2)
    (λ (l1 : loc), ∃ l2 : loc, ⌜w1 = #l1⌝ ∧ ⌜w2 = #l2⌝ ∧
      inv (authN .@ "ref" .@ (l1,l2)) (∃ v1 v2, l1 ↦ v1 ∗ l2 ↦ᵢ v2 ∗ ⟦ τ ⟧ Δ v1 v2))%I name.
Proof. rewrite /IntoExist. rewrite interp_ref_unfold //. Qed.
#[global] Instance from_exist_interp_t_ref `{authG Σ, seqG Σ} {Θ} (Δ : ctxO Σ Θ) (τ : type Θ ⋆) (w1 w2 : val) :
  FromExist (⟦ ref τ ⟧ Δ w1 w2)
    (λ (l1 : loc), ∃ l2 : loc, ⌜w1 = #l1⌝ ∧ ⌜w2 = #l2⌝ ∧
      inv (authN .@ "ref" .@ (l1,l2)) (∃ v1 v2, l1 ↦ v1 ∗ l2 ↦ᵢ v2 ∗ ⟦ τ ⟧ Δ v1 v2))%I.
Proof. rewrite /FromExist. rewrite interp_ref_unfold //. Qed. *)

(** ** Properties of the type interpretation w.r.t. the substitutions *)
Section interp_subst.
  Context `{authG Σ, seqG Σ}.

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

  Lemma shift_env_bin_eq (Θ : Ctx kind) (Γ : gmap string (typ ⋆ Θ)) (Δ : ctxO Σ Θ) κ (A : kindO Σ κ) :
    (λ σ : typ ⋆ Θ, lrel_bi_as_lrel (interp σ Δ)) <$> Γ ≡
    (λ σ : typ ⋆ (Θ ▹ κ), lrel_bi_as_lrel (interp σ (ext Δ A))) <$> ⤉ Γ.
  Proof.
    rewrite -map_fmap_compose => x.
    rewrite !lookup_fmap.
    destruct (Γ !! x) => /=; [|done].
    constructor. intros w1 w2. apply equiv_dist. intros n. apply lrel_bi_as_lrel_ne.
    exact (proj1 (equiv_dist _ _) (shift_eq t Δ A) n).
  Qed.

  Lemma shift_env_un_eq (Θ : Ctx kind) (Γ : gmap string (typ ⋆ Θ)) (Δ : ctxO Σ Θ) κ (A : kindO Σ κ) :
    (λ σ : typ ⋆ Θ, lrel_bi_un (interp σ Δ)) <$> Γ ≡
    (λ σ : typ ⋆ (Θ ▹ κ), lrel_bi_un (interp σ (ext Δ A))) <$> ⤉ Γ.
  Proof.
    rewrite -map_fmap_compose => x.
    rewrite !lookup_fmap.
    destruct (Γ !! x) => /=; [|done].
    constructor. intros w. apply equiv_dist. intros n. apply lrel_bi_un_ne.
    exact (proj1 (equiv_dist _ _) (shift_eq t Δ A) n).
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
  Context `{authG Σ, seqG Σ}.
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

  (** Unary environment typing — single-value substitution *)
  Definition un_env_ltyped (Γ : gmap string (lrel_un Σ)) (vs : gmap string val) : iProp Σ :=
    ([∗ map] i ↦ (Au : lrel_un Σ); v ∈ Γ; vs, Au v)%I.

  Global Instance un_env_ltyped_persistent (Γ : gmap string (lrel_un Σ)) vs : Persistent (un_env_ltyped Γ vs).
  Proof. apply big_sepM2_persistent. intros ?? v ??. apply _. Qed.

  Global Instance un_env_ltyped_ne n :
    Proper (dist n ==> (=) ==> dist n) un_env_ltyped.
  Proof.
    intros Γ Γ' HΓ ? vs ->. apply big_sepM2_ne_2; [done..|solve_proper].
  Qed.

  Global Instance un_env_ltyped_proper :
    Proper ((≡) ==> (=) ==> (≡)) un_env_ltyped.
  Proof. solve_proper_from_ne. Qed.

  Lemma un_env_ltyped_insert (Γ : gmap string (lrel_un Σ)) vs x (Au : lrel_un Σ) v :
    Au v -∗ un_env_ltyped Γ vs -∗
    un_env_ltyped (binder_insert x Au Γ) (binder_insert x v vs).
  Proof.
    destruct x as [|x] => /=; first by auto.
    rewrite /un_env_ltyped. iIntros "HAu HΓ".
    by iApply (big_sepM2_insert_2 with "[HAu] [HΓ]").
  Qed.

  Lemma un_env_ltyped_empty : ⊢ un_env_ltyped ∅ ∅.
  Proof. apply (big_sepM2_empty' _). Qed.

  Lemma env_bin_to_un {Θ} (Δ : ctxO Σ Θ) (Γ : stringmap (typ ⋆ Θ)) vs :
    env_ltyped ((λ (σ : typ ⋆ Θ), lrel_bi_as_lrel (interp σ Δ)) <$> Γ) vs ⊢
    un_env_ltyped ((λ (σ : typ ⋆ Θ), lrel_bi_un (interp σ Δ)) <$> Γ) (fst <$> vs).
  Proof.
    rewrite /env_ltyped /un_env_ltyped.
    iIntros "H".
    rewrite big_sepM2_fmap_l.
    rewrite big_sepM2_fmap_l big_sepM2_fmap_r.
    iApply (big_sepM2_mono with "H").
    intros k σ [v1 v2] _ _. simpl. apply lrel_bi_proj_un.
  Qed.

  Global Instance env_ltyped_persistent Γ vs : Persistent (⟦ Γ ⟧* vs).
  Proof.
    apply big_sepM2_persistent.
    intros ?? [? ?] ??. apply _.
  Qed.

End env_typed.

Notation "⟦ Γ ⟧*" := (env_ltyped Γ).

(** * The semantic typing judgement *)
Section bin_log_related.
  Context `{authG Σ, seqG Σ}.

  Definition bin_log_related (E : coPset) (Θ : Ctx kind)
    (Δ : ctxO Σ Θ) (Γ : stringmap (type Θ ⋆)) (e e' : expr) (τ : type Θ ⋆) : iProp Σ :=
    (∀ (vs : gmap string (val * val)),
        ⟦ (λ (σ : type Θ ⋆), lrel_bi_as_lrel (interp σ Δ)) <$> Γ ⟧* vs -∗
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

(** * The unary semantic typing judgement *)
Section un_log_related.
  Context `{authG Σ, seqG Σ}.

  Definition un_log_related (Θ : Ctx kind) (Δ : ctxO Σ Θ)
    (Γ : stringmap (type Θ ⋆)) (e : expr) (τ : type Θ ⋆) : iProp Σ :=
    (∀ vs, un_env_ltyped ((λ (σ : typ ⋆ Θ), lrel_bi_un (interp σ Δ)) <$> Γ) vs -∗
           TRM (subst_map vs e) : lrel_bi_un (interp τ Δ))%I.

End un_log_related.

Notation "'{' Θ ';' Δ ';' Γ '}' ⊨ᵤ e : τ" :=
  (un_log_related Θ Δ Γ e%E τ%ty)
  (at level 100, Δ at next level, Γ at next level, e at next level,
   τ at level 200).
