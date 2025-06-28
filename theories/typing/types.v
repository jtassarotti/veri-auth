(** (Syntactic) Typing for System F_omega_mu_ref with existential types *)
From Coq.Unicode Require Import Utf8.
From Coq.Logic Require Import PropExtensionality.
From Coq.Program Require Import Basics.
From Coq.Classes Require Import RelationClasses.
From Coq.ssr Require Import ssreflect.
From auth.binding Require Import Lib Intrinsic Auto.

(** * Kinds *)
Inductive kind :=
| KType : kind
| KArrow : kind → kind → kind.

Declare Scope kind_scope.
Delimit Scope kind_scope with kind.
Bind Scope kind_scope with kind.

Notation "⋆" := KType : kind_scope.
Notation "κ₁ ⇒ κ₂" := (KArrow κ₁ κ₂) (at level 45, right associativity) : kind_scope.

(** * Types *)
Inductive tconstr : kind → Type :=
| TUnit : tconstr ⋆
| TNat : tconstr ⋆
| TBool : tconstr ⋆
| TString : tconstr ⋆
| TProd : tconstr (⋆ ⇒ ⋆ ⇒ ⋆)
| TSum : tconstr (⋆ ⇒ ⋆ ⇒ ⋆)
| TArrow : tconstr (⋆ ⇒ ⋆ ⇒ ⋆)
| TRef : tconstr (⋆ ⇒ ⋆)
| TForall κ : tconstr ((κ ⇒ ⋆) ⇒ ⋆)
| TExists κ : tconstr ((κ ⇒ ⋆) ⇒ ⋆)
| TRec κ : tconstr ((κ ⇒ κ) ⇒ κ).

Inductive type (Θ : Ctx kind) : kind → Type :=
| TVar κ (x : dom Θ) (EQ : Θ x = κ) : type Θ κ
| TLam κ1 κ2 (τ : type (Θ ▹ κ1) κ2) : type Θ (κ1 ⇒ κ2)
| TApp κ1 κ2 (τ : type Θ (κ1 ⇒ κ2)) (τ' : type Θ κ1) : type Θ κ2
| TConstr κ  (c : tconstr κ) : type Θ κ.

Arguments TVar {Θ κ}.
Arguments TLam {Θ κ1 κ2}.
Arguments TApp {Θ κ1 κ2}.
Arguments TConstr {Θ κ}.

Definition typ := flip type.

Local Open Scope bind_scope.

#[export] Instance IPC_typ : IntPureCore typ := @TVar.

Fixpoint tmap {κ} {Θ1 Θ2 : Ctx kind} (δ : Θ1 [→] Θ2) (τ : typ κ Θ1) : typ κ Θ2 :=
  match τ with
  | TVar x EQ => TVar (δ x) (eq_trans (arr_hom δ x) EQ)
  | TLam τ => TLam (tmap (δ ↑) τ)
  | TApp σ τ => TApp (tmap δ σ) (tmap δ τ)
  | TConstr c => TConstr c
  end.
#[export] Instance FMap_typ {κ : kind} : FunctorCore (typ κ) := @tmap κ.

Fixpoint tbind {κ} {Θ1 Θ2 : Ctx kind} (ρ : Θ1 [⇒] Θ2) (τ : typ κ Θ1) : typ κ Θ2 :=
  match τ with
  | TVar x EQ => ρ _ x EQ
  | TLam τ => TLam (tbind (ρ ↑) τ)
  | TApp σ τ => TApp (tbind ρ σ) (tbind ρ τ)
  | TConstr c => TConstr c
  end.
#[export] Instance BindCore_typ {κ} : BindCore (typ κ) := @tbind κ.

#[export] Instance IP_typ : IntPure typ.
Proof. split; intros; term_simpl; reflexivity. Qed.

Lemma tvar_ext {κ Δ} {x y : dom Δ} (EQx : Δ x = κ) (EQy : Δ y = κ) (EQ : x = y) :
  TVar x EQx = TVar y EQy.
Proof.
  subst y; destruct EQy.
  f_equal.
  apply proof_irrelevance.
Qed.

Fixpoint tmap_id {κ} Δ (δ : Δ [→] Δ) (τ : typ κ Δ) : δ ≡ ı → fmap δ τ = τ.
Proof.
  auto_map_id; [].
  apply tvar_ext, EQ.
Qed.

Fixpoint tmap_comp {κ} (A B C : Ctx kind) (f : B [→] C) (g : A [→] B) h (τ : typ κ A) :
  f ∘ g ≡ h → fmap f (fmap g τ) = fmap h τ.
Proof.
  auto_map_comp; [].
  apply tvar_ext, EQ.
Qed.

#[export] Instance Functor_typ {κ} : Functor (typ κ).
Proof.
  split; [exact tmap_id | exact tmap_comp].
Qed.

Fixpoint tmap_tbind_pure {κ} (A B : Ctx kind) (f : A [→] B) (g : A [⇒] B) (τ : typ κ A) :
  f ̂ ≡ g → fmap f τ = bind g τ.
Proof.
  auto_map_bind_pure.
Qed.

#[export] Instance BindMapPure_typ {κ} : BindMapPure (typ κ).
Proof.
  split; exact tmap_tbind_pure.
Qed.

Fixpoint tmap_tbind_comm {κ} (A B₁ B₂ C : Ctx kind) (f₁ : B₁ [→] C) (f₂ : A [→] B₂)
         (g₁ : A [⇒] B₁) (g₂ : B₂ [⇒] C) (τ : typ κ A) :
  g₂ ∘ f₂ ̂ ≡ f₁ ̂ ∘ g₁ → bind g₂ (fmap f₂ τ) = fmap f₁ (bind g₁ τ).
Proof.
  auto_map_bind_comm.
Qed.

#[export] Instance BindMapComm_typ {κ} : BindMapComm (typ κ).
Proof.
  split; exact tmap_tbind_comm.
Qed.

Fixpoint tbind_id {κ} (A : Ctx kind) (f : A [⇒] A) (τ : typ κ A) :
  f ≡ ı → bind f τ = τ.
Proof.
  auto_bind_id.
Qed.

Fixpoint tbind_comp {κ} (A B C : Ctx kind) (f : B [⇒] C) (g : A [⇒] B) h (τ : typ κ A) :
  f ∘ g ≡ h → bind f (bind g τ) = bind h τ.
Proof.
  auto_bind_comp.
Qed.

Instance Bind_expr {κ} : Bind (typ κ).
Proof.
  split; [exact tbind_id | exact tbind_comp].
Qed.

(** Type formers such as [TProd] and [TSum] are now type constructors *)
Definition t_unit {Θ} : type Θ ⋆ := TConstr TUnit.
Definition t_nat  {Θ} : type Θ ⋆ := TConstr TNat.
Definition t_bool {Θ} : type Θ ⋆ := TConstr TBool.
Definition t_string {Θ} : type Θ ⋆ := TConstr TString.
Definition t_prod {Θ} (τ1 τ2 : type Θ ⋆) := TApp (TApp (TConstr TProd) τ1) τ2.
Definition t_sum {Θ} (τ1 τ2 : type Θ ⋆) := TApp (TApp (TConstr TSum) τ1) τ2.
Definition t_option {Θ} (τ : type Θ ⋆) := t_sum t_unit τ.
Definition t_arr {Θ} (τ1 τ2 : type Θ ⋆) := TApp (TApp (TConstr TArrow) τ1) τ2.
Definition t_ref {Θ} (τ : type Θ ⋆) := TApp (TConstr TRef) τ.
Definition t_rec {Θ} (κ : kind) (τ : type (Θ ▹ κ)%kind κ) : type Θ κ := TApp (TConstr (TRec κ)) (TLam τ).
Definition t_forall {Θ} (κ : kind) (τ : type (Θ ▹ κ) ⋆) : type Θ ⋆ := TApp (TConstr (TForall κ)) (TLam τ).
Definition t_exists {Θ} (κ : kind) (τ : type (Θ ▹ κ) ⋆) : type Θ ⋆ := TApp (TConstr (TExists κ)) (TLam τ).

Declare Scope FType_scope.
Delimit Scope FType_scope with ty.
Bind Scope FType_scope with typ.
Bind Scope FType_scope with type.

Notation "()" := t_unit : FType_scope.
Infix "*" := t_prod : FType_scope.
Notation "(*)" := t_prod (only parsing) : FType_scope.
Infix "+" := t_sum : FType_scope.
Notation "(+)" := t_sum (only parsing) : FType_scope.
Infix "→" := t_arr : FType_scope.
Notation "(→)" := t_arr (only parsing) : FType_scope.
Notation "μ: κ ; τ" :=
  (t_rec κ%kind τ%ty)
  (at level 100, τ at level 200) : FType_scope.
Notation "∀: x ; .. ; y , τ" := (t_forall x%kind .. (t_forall y%kind τ%ty) ..)
  (at level 10, τ at level 200,
  format "'[  ' '[  ' ∀:  x ;  .. ;  y ']' ,  '/' τ ']'") : FType_scope.
Notation "∃: x ; .. ; y , τ" := (t_exists x%kind .. (t_exists y%kind τ%ty) ..)
  (at level 10, τ at level 200,
  format "'[  ' '[  ' ∃:  x ;  .. ;  y ']' ,  '/' τ ']'") : FType_scope.

Notation "'ref' τ" := (t_ref τ%ty) (at level 10, τ at next level, right associativity): FType_scope.

Notation "Λ: τ" := (TLam τ)%ty (at level 200) : FType_scope.
#[warning="-uniform-inheritance"]
Coercion TApp : type >-> Funclass.

Definition var0 {Θ : Ctx kind} {κ0 : kind} : typ κ0 (Θ ▹ κ0) := TVar (VZ : dom (_ ▹ _)) eq_refl.
Definition var1 {Θ : Ctx kind} {κ0 κ1 : kind} : typ κ1 (Θ ▹ κ1 ▹ κ0) := Core.shift var0.
Definition var2 {Θ : Ctx kind} {κ0 κ1 κ2 : kind} : typ κ2 (Θ ▹ κ2 ▹ κ1 ▹ κ0) := Core.shift var1.
Definition var3 {Θ : Ctx kind} {κ0 κ1 κ2 κ3 : kind} : typ κ3 (Θ ▹ κ3 ▹ κ2 ▹ κ1 ▹ κ0) := Core.shift var2.
Definition var4 {Θ : Ctx kind} {κ0 κ1 κ2 κ3 κ4 : kind} : typ κ4 (Θ ▹ κ4 ▹ κ3 ▹ κ2 ▹ κ1 ▹ κ0) := Core.shift var3.
Definition var5 {Θ : Ctx kind} {κ0 κ1 κ2 κ3 κ4 κ5 : kind} : typ κ5 (Θ ▹ κ5 ▹ κ4 ▹ κ3 ▹ κ2 ▹ κ1 ▹ κ0) := Core.shift var4.

Notation "τ .[ σ /]" := (subst (F := typ _) τ%ty σ%ty)
 (at level 2, σ at level 200, left associativity,
   format "τ .[ σ /]") : FType_scope.

(** * Type equivalence  *)
Reserved Notation "Θ ⊢ₑ x ≃ y : κ" (at level 70, x, y, κ at next level).

Inductive tequiv (Θ : Ctx kind) : ∀ κ, typ κ Θ → typ κ Θ → Prop :=
| TEquiv_refl κ τ :
  Θ ⊢ₑ τ ≃ τ : κ
| TEquiv_symm κ τ τ' :
  Θ ⊢ₑ τ' ≃ τ : κ →
  Θ ⊢ₑ τ ≃ τ' : κ
| TEquiv_trans κ τ τ' τ'' :
  Θ ⊢ₑ τ ≃ τ' : κ →
  Θ ⊢ₑ τ' ≃ τ'' : κ →
  Θ ⊢ₑ τ ≃ τ'' : κ

| TEquiv_lam κ1 κ2  τ τ' :
  Θ ▹ κ1 ⊢ₑ τ ≃ τ' : κ2 →
  Θ ⊢ₑ TLam τ ≃ TLam τ' : κ1 ⇒ κ2
| TEquiv_app κ1 κ2 τ σ τ' σ' :
  Θ ⊢ₑ τ ≃ σ : κ1 ⇒ κ2 →
  Θ ⊢ₑ τ' ≃ σ' : κ1 →
  Θ ⊢ₑ τ τ' ≃ σ σ' : κ2

| TEquiv_beta κ1 κ2 (τ : typ κ2 (Θ ▹ κ1)) (τ' : typ κ1 Θ) :
  Θ ⊢ₑ (Λ: τ) τ' ≃ τ.[τ'/] : κ2
| TEquiv_eta κ1 κ2 (τ : typ (κ1 ⇒ κ2) Θ) :
  Θ ⊢ₑ τ ≃ (Λ: (shift τ) var0) : κ1 ⇒ κ2

where "Θ ⊢ₑ τ1 ≃ τ2 : κ" := (tequiv Θ κ τ1 τ2).

#[global] Instance type_equiv_Equivalence Θ κ :
  Equivalence (tequiv Θ κ).
Proof.
  split; constructor; [assumption|].
  eapply TEquiv_symm. eapply TEquiv_trans; eauto.
Qed.

Inductive telim_ctx (Θ : Ctx kind) : kind → kind → Type :=
| TElim_empty κ : telim_ctx Θ κ κ
| TElim_app κ1 κ2 κ (τ1 : type Θ κ1):
  telim_ctx Θ κ (κ1 ⇒ κ2) → telim_ctx Θ κ κ2.
Arguments TElim_empty { _ _}.
Arguments TElim_app {_ _ _ _}.

Fixpoint tfill {Θ} {κ1 κ2} (T : telim_ctx Θ κ1 κ2) : type Θ κ1 → type Θ κ2 :=
  match T in telim_ctx _ κ κ' return type Θ κ → type Θ κ' with
  | TElim_empty => λ τ, τ
  | TElim_app τ2 T' => λ τ, TApp (tfill T' τ) τ2
  end.

Ltac fold_types :=
  repeat
    match goal with
    | |- context C[TConstr (Θ:=?Θ) TUnit] => let C' := context C[@t_unit Θ] in change C'
    | |- context C[TConstr (Θ:=?Θ) TNat] => let C' := context C[@t_nat Θ] in change C'
    | |- context C[TConstr (Θ:=?Θ) TBool] => let C' := context C[@t_bool Θ] in change C'
    | |- context C[TConstr (Θ:=?Θ) TString] => let C' := context C[@t_string Θ] in change C'

    | |- context C[TApp (TApp (TConstr TProd) ?τ1) ?τ2] =>
        let C' := context C[t_prod τ1 τ2] in change C'
    | |- context C[TApp (TApp (TConstr TSum) ?τ1) ?τ2] =>
        let C' := context C[t_sum τ1 τ2] in change C'
    | |- context C[TApp (TApp (TConstr TArrow) ?τ1) ?τ2] =>
        let C' := context C[t_arr τ1 τ2] in change C'
    | |- context C[TApp (TConstr (TForall ?κ)) (TLam ?τ)] =>
        let C' := context C[t_forall κ τ] in change C'
    | |- context C[TApp (TConstr (TExists ?κ)) (TLam ?τ)] =>
        let C' := context C[t_exists κ τ] in change C'
    | |- context C[TApp (TConstr (TRec ?κ)) (TLam ?τ)] =>
        let C' := context C[t_rec κ τ] in change C'                                                    
    end.

Ltac fold_tvars :=
  repeat
    match goal with
    | |- context C[@TVar (?Θ ▹ ?κ0) ?κ0 VZ _] =>
        let C' := context C[@var0 Θ κ0] in change C'
    | |- context C[@TVar (?Θ ▹ ?κ1 ▹ ?κ0) ?κ1 (VS VZ) _] =>
        let C' := context C[@var1 Θ κ0 κ1] in change C'
    | |- context C[@TVar (?Θ ▹ ?κ2 ▹ ?κ1 ▹ ?κ0) ?κ2 (VS (VS VZ)) _] =>
        let C' := context C[@var2 Θ κ0 κ1 κ2] in change C'
    | |- context C[@TVar (?Θ ▹ ?κ3 ▹ ?κ2 ▹ ?κ1 ▹ ?κ0) ?κ3 (VS (VS (VS VZ))) _] =>
        let C' := context C[@var3 Θ κ0 κ1 κ2 κ3] in change C'
    | |- context C[@TVar (?Θ ▹ ?κ4 ▹ ?κ3 ▹ ?κ2 ▹ ?κ1 ▹ ?κ0) ?κ4 (VS (VS (VS (VS VZ)))) _] =>
        let C' := context C[@var4 Θ κ0 κ1 κ2 κ3 κ4] in change C'
    | |- context C[@TVar (?Θ ▹ ?κ5 ▹ ?κ4 ▹ ?κ3 ▹ ?κ2 ▹ ?κ1 ▹ ?κ0) ?κ5 (VS (VS (VS (VS (VS VZ))))) _] =>
        let C' := context C[@var5 Θ κ0 κ1 κ2 κ3 κ4 κ5] in change C'
    end.

Ltac t_simpl :=
  term_simpl; unfold IPC_typ; fold_types; fold_tvars.

Ltac tequiv_beta_l :=
  repeat
    match goal with
    | |- tequiv _ _ (TApp (TLam _) _) _ =>
        etransitivity; [eapply TEquiv_beta|t_simpl]

    | |- tequiv _ _ (TLam _) _ => eapply TEquiv_lam
    | |- tequiv _ _ (TApp _ _) _ => eapply TEquiv_app

    | |- tequiv _ _ (t_prod _ _) _ => eapply TEquiv_app
    | |- tequiv _ _ (t_sum _ _) _ => eapply TEquiv_app
    | |- tequiv _ _ (t_arr _ _) _ => eapply TEquiv_app
    | |- tequiv _ _ (t_ref _) _ => eapply TEquiv_app
    | |- tequiv _ _ (t_forall _ _) _ => eapply TEquiv_app
    | |- tequiv _ _ (t_exists _ _) _ => eapply TEquiv_app
    | |- tequiv _ _ (t_rec _) _ => eapply TEquiv_app

    | |- _ => reflexivity
    end.
