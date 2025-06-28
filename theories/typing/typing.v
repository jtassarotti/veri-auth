From stdpp Require Export stringmap fin_map_dom gmap.
From auth.binding Require Export Lib Intrinsic Auto.
From auth.heap_lang Require Export lang notation metatheory.
From auth.typing Require Export types.

(** * Typing judgements *)
Reserved Notation "Θ |ₜ Γ ⊢ₜ e : τ" (at level 74, e, τ at next level).
Reserved Notation "Θ ⊢ᵥ v : τ" (at level 20, v, τ at next level).

(** We model type-level lambdas and applications as thunks *)
Notation "Λ: e" := (λ: <>, e)%E (at level 200, only parsing).
Notation "Λ: e" := (λ: <>, e)%V (at level 200, only parsing) : val_scope.

(** To unfold a recursive type, we need to take a step. We thus define the
    unfold operator to be the identity function. *)
Definition rec_unfold : val := λ: "x", "x".
Definition rec_fold : val := λ: "x", "x".
Definition unpack : val := λ: "x" "y", "y" "x".

Notation "'unpack:' x := e1 'in' e2" := (unpack e1%E (Lam x%binder e2%E))
  (at level 200, x at level 1, e1, e2 at level 200, only parsing) : expr_scope.

Notation "'unpack:' x := e1 'in' e2" := (unpack e1%E (LamV x%binder e2%E))
  (at level 200, x at level 1, e1, e2 at level 200, only parsing) : val_scope.

(** Operation lifts *)
Global Instance insert_binder (A : Type): Insert binder A (stringmap A) :=
  binder_insert.

Notation "⤉ Γ" := (Core.shift <$> Γ) (at level 10, format "⤉ Γ").

(** Which types are unboxed -- we can only do CAS on locations which hold unboxed types *)
Inductive UnboxedType {Θ} : type Θ ⋆ → Prop :=
  | UnboxedTUnit : UnboxedType t_unit
  | UnboxedTNat : UnboxedType t_nat
  | UnboxedTBool : UnboxedType t_bool
  | UnboxedTRef τ : UnboxedType (t_ref τ).

(** Types which support direct equality test. *)
Inductive EqType {Θ} : type Θ ⋆ → Prop :=
  | EqTUnit : EqType t_unit
  | EqTNat : EqType t_nat
  | EqTBool : EqType t_bool
  | EqTString : EqType t_string
  | EqTProd τ τ' : EqType τ → EqType τ' → EqType (t_prod τ τ')
  | EqSum τ τ' : EqType τ → EqType τ' → EqType (t_sum τ τ').

Lemma unboxed_type_ref_or_eqtype Θ (τ : type Θ ⋆) :
  UnboxedType τ → (EqType τ ∨ ∃ τ', τ = t_ref τ').
Proof. inversion 1; try (first [ left; now econstructor | eauto 10 ]). Qed.

Definition binop_nat_res_type {Θ} (op : bin_op) : option (type Θ ⋆) :=
  match op with
  | MultOp | PlusOp | MinusOp => Some t_nat
  | EqOp | LeOp | LtOp => Some t_bool
  | _ => None
  end.
Definition binop_bool_res_type {Θ} (op : bin_op) : option (type Θ ⋆) :=
  match op with
  | XorOp | EqOp => Some t_bool
  | _ => None
  end.
Definition unop_nat_res_type {Θ} (op : un_op) : option (type Θ ⋆) :=
  match op with
  | MinusUnOp => Some t_nat
  | StringOfIntOp => Some t_string
  | _ => None
  end.
Definition unop_bool_res_type {Θ} (op : un_op) : option (type Θ ⋆) :=
  match op with
  | NegOp => Some t_bool
  | _ => None
  end.
Definition unop_string_res_type {Θ} (op : un_op) : option (type Θ ⋆) :=
  match op with
  | IntOfStringOp => Some (t_sum t_unit t_nat)
  | LengthOp => Some t_nat
  | _ => None
  end.

(** Typing itself *)
Inductive typed (Θ : Ctx kind) : stringmap (typ ⋆ Θ) → expr → (typ ⋆ Θ) → Prop :=
| Var_typed Γ x τ :
  Γ !! x = Some τ →
  Θ |ₜ Γ ⊢ₜ Var x : τ
| Val_typed Γ v τ :
  Θ ⊢ᵥ v : τ →
  Θ |ₜ Γ ⊢ₜ Val v : τ
| BinOp_typed_nat Γ op e1 e2 τ :
  Θ |ₜ Γ ⊢ₜ e1 : t_nat →
  Θ |ₜ Γ ⊢ₜ e2 : t_nat →
  binop_nat_res_type op = Some τ →
  Θ |ₜ Γ ⊢ₜ BinOp op e1 e2 : τ
| BinOp_typed_bool Γ op e1 e2 τ :
  Θ |ₜ Γ ⊢ₜ e1 : t_bool →
  Θ |ₜ Γ ⊢ₜ e2 : t_bool →
  binop_bool_res_type op = Some τ →
  Θ |ₜ Γ ⊢ₜ BinOp op e1 e2 : τ
| UnOp_typed_nat Γ op e τ :
  Θ |ₜ Γ ⊢ₜ e : t_nat →
  unop_nat_res_type op = Some τ →
  Θ |ₜ Γ ⊢ₜ UnOp op e : τ
| UnOp_typed_bool Γ op e τ :
  Θ |ₜ Γ ⊢ₜ e : t_bool →
  unop_bool_res_type op = Some τ →
  Θ |ₜ Γ ⊢ₜ UnOp op e : τ
| UnOp_typed_string Γ op e τ :
  Θ |ₜ Γ ⊢ₜ e : t_string →
  unop_string_res_type op = Some τ →
  Θ |ₜ Γ ⊢ₜ UnOp op e : τ
| UnboxedEq_typed Γ e1 e2 τ :
  UnboxedType τ →
  Θ |ₜ Γ ⊢ₜ e1 : τ →
  Θ |ₜ Γ ⊢ₜ e2 : τ →
  Θ |ₜ Γ ⊢ₜ BinOp EqOp e1 e2 : t_bool
| IndexOp_typed Γ e1 e2 e3 :
  Θ |ₜ Γ ⊢ₜ e1 : t_nat → Θ |ₜ Γ ⊢ₜ e2 : t_string → Θ |ₜ Γ ⊢ₜ e3 : t_string →
  Θ |ₜ Γ ⊢ₜ TernOp IndexOp e1 e2 e3 : t_sum t_unit t_nat
| SubOp_typed Γ e1 e2 e3 :
  Θ |ₜ Γ ⊢ₜ e1 : t_nat → Θ |ₜ Γ ⊢ₜ e2 : t_nat → Θ |ₜ Γ ⊢ₜ e3 : t_string →
  Θ |ₜ Γ ⊢ₜ TernOp SubOp e1 e2 e3 : t_string
| Pair_typed Γ e1 e2 τ1 τ2 :
  Θ |ₜ Γ ⊢ₜ e1 : τ1 → Θ |ₜ Γ ⊢ₜ e2 : τ2 →
  Θ |ₜ Γ ⊢ₜ (e1, e2) : τ1 * τ2
| Fst_typed Γ e τ1 τ2 :
  Θ |ₜ Γ ⊢ₜ e : τ1 * τ2 →
  Θ |ₜ Γ ⊢ₜ Fst e : τ1
| Snd_typed Γ e τ1 τ2 :
  Θ |ₜ Γ ⊢ₜ e : τ1 * τ2 →
  Θ |ₜ Γ ⊢ₜ Snd e : τ2
| InjL_typed Γ e τ1 τ2 :
  Θ |ₜ Γ ⊢ₜ e : τ1 →
  Θ |ₜ Γ ⊢ₜ InjL e : τ1 + τ2
| InjR_typed Γ e τ1 τ2 :
  Θ |ₜ Γ ⊢ₜ e : τ2 →
  Θ |ₜ Γ ⊢ₜ InjR e : τ1 + τ2
| Case_typed Γ e0 e1 e2 τ1 τ2 τ3 :
  Θ |ₜ Γ ⊢ₜ e0 : τ1 + τ2 →
  Θ |ₜ Γ ⊢ₜ e1 : (τ1 → τ3) →
  Θ |ₜ Γ ⊢ₜ e2 : (τ2 → τ3) →
  Θ |ₜ Γ ⊢ₜ Case e0 e1 e2 : τ3
| If_typed Γ e0 e1 e2 τ :
  Θ |ₜ Γ ⊢ₜ e0 : t_bool →
  Θ |ₜ Γ ⊢ₜ e1 : τ →
  Θ |ₜ Γ ⊢ₜ e2 : τ →
  Θ |ₜ Γ ⊢ₜ If e0 e1 e2 : τ
| Rec_typed Γ f x e τ1 τ2 :
  Θ |ₜ <[f:=(τ1 → τ2)%ty]>(<[x:=τ1]>Γ) ⊢ₜ e : τ2 →
  Θ |ₜ Γ ⊢ₜ (rec: f x := e) : (τ1 → τ2)
| App_typed Γ e1 e2 τ1 τ2 :
  Θ |ₜ Γ ⊢ₜ e1 : (τ1 → τ2) →
  Θ |ₜ Γ ⊢ₜ e2 : τ1 →
  Θ |ₜ Γ ⊢ₜ e1 e2 : τ2
| TLam_typed Γ κ e τ :
  Θ ▹ κ |ₜ ⤉ Γ ⊢ₜ e : τ →
  Θ |ₜ Γ ⊢ₜ (Λ: e) : ∀: κ, τ
| TApp_typed Γ e κ (τ : typ ⋆ (Θ ▹ κ)) (τ' : typ κ Θ) :
  Θ |ₜ Γ ⊢ₜ e : (∀: κ, τ) →
  Θ |ₜ Γ ⊢ₜ e #~ : τ.[τ'/]
| TFold Γ e κ (τ : typ κ (Θ ▹ κ%kind)) (T : telim_ctx Θ κ ⋆) :
  Θ |ₜ Γ ⊢ₜ e : tfill T (τ.[μ: κ; τ/]) →
  Θ |ₜ Γ ⊢ₜ rec_fold e : tfill T (μ: κ; τ)
| TUnfold Γ e κ (τ : typ κ (Θ ▹ κ%kind)) (T : telim_ctx Θ κ ⋆) :
  Θ |ₜ Γ ⊢ₜ e : tfill T (μ: κ; τ) →
  Θ |ₜ Γ ⊢ₜ rec_unfold e : tfill T (τ.[μ: κ; τ/])
| TPack Γ e κ τ τ' :
  Θ |ₜ Γ ⊢ₜ e : τ.[τ'/] →
  Θ |ₜ Γ ⊢ₜ e : (∃: κ, τ)
| TUnpack Γ e1 x e2 κ τ τ2 :
  Θ |ₜ Γ ⊢ₜ e1 : (∃: κ, τ) →
  Θ ▹ κ |ₜ <[x:=τ]>(⤉ Γ) ⊢ₜ e2 : Core.shift τ2 →
  Θ |ₜ Γ ⊢ₜ (unpack: x := e1 in e2) : τ2
| TFork Γ e : Θ |ₜ Γ ⊢ₜ e : () → Θ |ₜ Γ ⊢ₜ Fork e : ()
| TAlloc Γ e τ : Θ |ₜ Γ ⊢ₜ e : τ → Θ |ₜ Γ ⊢ₜ Alloc e : ref τ
| TLoad Γ e τ : Θ |ₜ Γ ⊢ₜ e : ref τ → Θ |ₜ Γ ⊢ₜ Load e : τ
| TStore Γ e e' τ : Θ |ₜ Γ ⊢ₜ e : ref τ → Θ |ₜ Γ ⊢ₜ e' : τ → Θ |ₜ Γ ⊢ₜ Store e e' : ()
| TXchg Γ e e' τ : Θ |ₜ Γ ⊢ₜ e : ref τ → Θ |ₜ Γ ⊢ₜ e' : τ → Θ |ₜ Γ ⊢ₜ Xchg e e' : τ
| TFAA Γ e1 e2 :
   Θ |ₜ Γ ⊢ₜ e1 : ref t_nat →
   Θ |ₜ Γ ⊢ₜ e2 : t_nat →
   Θ |ₜ Γ ⊢ₜ FAA e1 e2 : t_nat
| TCmpXchg Γ e1 e2 e3 τ :
   UnboxedType τ →
   Θ |ₜ Γ ⊢ₜ e1 : ref τ → Θ |ₜ Γ ⊢ₜ e2 : τ → Θ |ₜ Γ ⊢ₜ e3 : τ →
   Θ |ₜ Γ ⊢ₜ CmpXchg e1 e2 e3 : τ * t_bool
| THash Γ e :
  Θ |ₜ Γ ⊢ₜ e : t_string →
  Θ |ₜ Γ ⊢ₜ Hash e : t_string
| TEquiv Γ e τ τ' :
  Θ ⊢ₑ τ ≃ τ' : ⋆ →
  Θ |ₜ Γ ⊢ₜ e : τ' →
  Θ |ₜ Γ ⊢ₜ e : τ

with val_typed (Θ : Ctx kind) : val → typ ⋆ Θ → Prop :=
| Unit_val_typed : Θ ⊢ᵥ #() : ()
| Nat_val_typed (n : nat) : Θ ⊢ᵥ #n : t_nat
| Bool_val_typed (b : bool) : Θ ⊢ᵥ #b : t_bool
| String_val_typed (s : string) : Θ ⊢ᵥ #s : t_string
| Pair_val_typed v1 v2 τ1 τ2 :
  Θ ⊢ᵥ v1 : τ1 →
  Θ ⊢ᵥ v2 : τ2 →
  Θ ⊢ᵥ (v1, v2) : (τ1 * τ2)
| InjL_val_typed v τ1 τ2 :
  Θ ⊢ᵥ v : τ1 →
  Θ ⊢ᵥ InjLV v : (τ1 + τ2)
| InjR_val_typed v τ1 τ2 :
  Θ ⊢ᵥ v : τ2 →
  Θ ⊢ᵥ InjRV v : (τ1 + τ2)
| Rec_val_typed f x e τ1 τ2 :
  Θ |ₜ <[f:= (τ1 → τ2)%ty]>(<[x:=τ1]>∅) ⊢ₜ e : τ2 →
  Θ ⊢ᵥ (rec: f x := e) : (τ1 → τ2)
| TLam_val_typed e κ τ :
  Θ ▹ κ |ₜ ∅ ⊢ₜ e : τ →
  Θ ⊢ᵥ (Λ: e) : (∀: κ, τ)
where "Θ |ₜ Γ ⊢ₜ e : τ" := (typed Θ Γ e τ)
and "Θ ⊢ᵥ e : τ" := (val_typed Θ e τ).

Lemma binop_nat_typed_safe (Θ : Ctx kind) (op : bin_op) (n1 n2 : Z) (τ : type Θ ⋆) :
  binop_nat_res_type op = Some τ → is_Some (bin_op_eval op #n1 #n2).
Proof. destruct op; simpl; eauto; discriminate. Qed.

Lemma binop_bool_typed_safe (Θ : Ctx kind) (op : bin_op) (b1 b2 : bool) (τ : type Θ ⋆) :
  binop_bool_res_type op = Some τ → is_Some (bin_op_eval op #b1 #b2).
Proof. destruct op; naive_solver. Qed.

Lemma unop_nat_typed_safe (Θ : Ctx kind) (op : un_op) (n : Z) (τ : type Θ ⋆) :
  unop_nat_res_type op = Some τ → is_Some (un_op_eval op #n).
Proof. destruct op; simpl; eauto ; discriminate. Qed.

Lemma unop_bool_typed_safe (Θ : Ctx kind) (op : un_op) (b : bool) (τ : type Θ ⋆) :
  unop_bool_res_type op = Some τ → is_Some (un_op_eval op #b).
Proof. destruct op; naive_solver. Qed.

Lemma unop_string_typed_safe (Θ : Ctx kind) (op : un_op) (s : string) (τ : type Θ ⋆) :
  unop_string_res_type op = Some τ → is_Some (un_op_eval op #s).
Proof. destruct op; naive_solver. Qed.

Lemma TApp_typed' Θ Γ e κ (τ : typ ⋆ (Θ ▹ κ)) (τ' : typ κ Θ) (τ'' : typ ⋆ Θ) :
  Θ |ₜ Γ ⊢ₜ e : (∀: κ, τ) →
  τ'' = (τ.[τ'/])%ty →
  Θ |ₜ Γ ⊢ₜ e #~ : τ''.
Proof. intros ? ->. by eapply TApp_typed. Qed.

Ltac simpl_anon_binders :=
  repeat rewrite [insert <>%binder _]/insert /insert_binder /binder_insert.

Ltac t_beta :=
  eapply TEquiv; [tequiv_beta_l|]; fold_types.

Ltac typecheck :=
  lazymatch goal with
  | |- typed ?Θ ?Γ ?e ?τ =>
      lazymatch e with
      | Var _ => eapply Var_typed; reflexivity
      | Val _ => eapply Val_typed; typecheck
      | BinOp _ _ _ => fail "typechek: BinOp not implemented"
      | TernOp _ _ _ _ => fail "typecheck: TernOp not implemented"
      | Pair _ _ => eapply Pair_typed; typecheck
      | Fst _ => eapply Fst_typed; typecheck
      | Snd _ => eapply Snd_typed; typecheck
      | InjL _ => eapply InjL_typed; typecheck
      | InjR _ => eapply InjR_typed; typecheck
      | Case _ _ _ => eapply Case_typed; typecheck
      | If _ _ _ => eapply If_typed; typecheck
      | Rec BAnon _ _ =>
          lazymatch τ with
          | t_forall _ _ => eapply TLam_typed; simpl_anon_binders; typecheck
          | _ => eapply Rec_typed; simpl_anon_binders; typecheck
          end
      | Rec _ _ _ => eapply Rec_typed; typecheck
      | App (Val rec_unfold) ?e' =>
          let H := fresh "H" in
          eassert (Θ |ₜ Γ ⊢ₜ e' : _) as H; [typecheck|];
          move: (TUnfold _ _ _ _ H); t_simpl; done
      | App (Val rec_fold) _ => eapply TFold; t_simpl; typecheck
      | App (App (Val unpack) _) _ => eapply TUnpack; [typecheck|t_simpl; typecheck]
      | App _ (Val (LitV LitPoison)) => eapply TApp_typed'; [typecheck|by t_simpl]
      | App _ _ => eapply App_typed; last first; typecheck
      | e => fail "typecheck: " e "not implemented"
      end
  | |- val_typed _ ?v ?τ =>
      lazymatch v with
      | LitV LitUnit => eapply Unit_val_typed
      | LitV (LitInt _)_ => eapply Nat_val_typed
      | LitV (LitBool _) => eapply Bool_val_typed
      | LitV (LitString _) => eapply String_val_typed
      | PairV _ _ => eapply Pair_val_typed; typecheck
      | InjLV _ => eapply InjL_val_typed; typecheck
      | InjRV _ => eapply InjR_val_typed; typecheck
      | RecV _ _ _ =>
          lazymatch τ with
          | t_arr _ _ => eapply Rec_val_typed; typecheck
          | t_forall _ _ => eapply TLam_val_typed; typecheck
          | _ => fail "typecheck: RecV assigned non-functional type"
          end
      end
  | |- ?H => fail "typecheck: No case for " H
  end.

(** ********************************)
(** Closedness of typed programs   *)
(** ********************************)
Definition maybe_insert_binder (x : binder) (X : stringset) : stringset :=
  match x with
  | BAnon => X
  | BNamed f => {[f]} ∪ X
  end.

Local Fixpoint is_closed_expr_set (X : stringset) (e : expr) : bool :=
  match e with
  | Val v => is_closed_val_set v
  | Var x => bool_decide (x ∈ X)
  | Rec f x e => is_closed_expr_set (maybe_insert_binder f (maybe_insert_binder x X)) e
  | UnOp _ e | Fst e | Snd e | InjL e | InjR e | Fork e | Free e | Load e | Hash e =>
     is_closed_expr_set X e
  | App e1 e2 | BinOp _ e1 e2 | Pair e1 e2 | AllocN e1 e2 | Store e1 e2 | FAA e1 e2 | Xchg e1 e2 =>
     is_closed_expr_set X e1 && is_closed_expr_set X e2
  | If e0 e1 e2 | Case e0 e1 e2 | CmpXchg e0 e1 e2 | Resolve e0 e1 e2 | TernOp _ e0 e1 e2  =>
     is_closed_expr_set X e0 && is_closed_expr_set X e1 && is_closed_expr_set X e2
  | NewProph => true
  end
with is_closed_val_set (v : val) : bool :=
  match v with
  | LitV _ => true
  | RecV f x e => is_closed_expr_set (maybe_insert_binder f (maybe_insert_binder x ∅)) e
  | PairV v1 v2 => is_closed_val_set v1 && is_closed_val_set v2
  | InjLV v | InjRV v => is_closed_val_set v
  end.

Lemma is_closed_expr_set_sound (X : stringset) (e : expr) :
  is_closed_expr_set X e → is_closed_expr X e
with is_closed_val_set_sound (v : val) :
  is_closed_val_set v → is_closed_val v.
Proof.
  - induction e; simplify_eq/=; try by (intros; destruct_and?; split_and?; eauto).
  - induction v; simplify_eq/=; try by (intros; destruct_and?; split_and?; eauto).
Qed.

Local Lemma typed_is_closed_set Θ Γ e τ :
  Θ |ₜ Γ ⊢ₜ e : τ → is_closed_expr_set (dom Γ) e
with typed_is_closed_val_set Θ v τ :
  Θ ⊢ᵥ v : τ → is_closed_val_set v.
Proof.
  - induction 1; simplify_eq/=; try (split_and?; by eapply typed_is_closed_set).
    + apply bool_decide_pack. apply elem_of_dom. eauto.
    + by eapply typed_is_closed_val_set.
    + destruct f as [|f], x as [|x]; simplify_eq/=.
      * eapply typed_is_closed_set. eauto.
      * specialize (typed_is_closed_set _ (<[x:=τ1]>Γ) e τ2 H).
        revert typed_is_closed_set. by rewrite dom_insert_L.
      * specialize (typed_is_closed_set _ (<[f:=(τ1→τ2)%ty]>Γ) e τ2 H).
        revert typed_is_closed_set. by rewrite dom_insert_L.
      * specialize (typed_is_closed_set _ _ e τ2 H).
        revert typed_is_closed_set.
        rewrite (dom_insert_L (<[x:=τ1]> Γ) f (τ1→τ2)%ty).
        by rewrite dom_insert_L.
    + specialize (typed_is_closed_set _ (⤉Γ) e τ H).
      revert typed_is_closed_set. by rewrite dom_fmap_L.
    + by split_and?.
    + by split_and?.
    + by split_and?.
    + split_and?; eauto. try (apply bool_decide_pack; by set_solver).
      destruct x as [|x]; simplify_eq/=.
      ++ specialize (typed_is_closed_set _ _ _ _ H0).
         revert typed_is_closed_set. by rewrite dom_fmap_L.
      ++ specialize (typed_is_closed_set _ _ _ _ H0).
         revert typed_is_closed_set. rewrite (dom_insert_L (⤉Γ) x).
         by rewrite dom_fmap_L.
  - induction 1; simplify_eq/=; try done.
    + by split_and?.
    + destruct f as [|f], x as [|x]; simplify_eq/=.
      * specialize (typed_is_closed_set _ _ _ _ H).
        revert typed_is_closed_set. by rewrite dom_empty_L.
      * specialize (typed_is_closed_set _ (<[x:=τ1]>∅) _ _ H).
        revert typed_is_closed_set. by rewrite dom_insert_L dom_empty_L.
      * specialize (typed_is_closed_set _ _ _ _ H).
        revert typed_is_closed_set.
        rewrite (dom_insert_L _ f (τ1→τ2)%ty).
        by rewrite dom_empty_L.
      * specialize (typed_is_closed_set _ _ _ _ H).
        revert typed_is_closed_set.
        rewrite (dom_insert_L (<[x:=τ1]> ∅) f (τ1→τ2)%ty).
        by rewrite dom_insert_L dom_empty_L.
    + specialize (typed_is_closed_set _ _ _ _ H).
      revert typed_is_closed_set. by rewrite dom_empty_L.
Qed.

Theorem typed_is_closed Θ Γ e τ :
  Θ |ₜ Γ ⊢ₜ e : τ → is_closed_expr (dom Γ) e.
Proof. intros. eapply is_closed_expr_set_sound, typed_is_closed_set; eauto. Qed.
