From auth.heap_lang Require Export lang notation derived_laws_upto_bad metatheory adequacy_upto_bad.
From auth.heap_lang Require Export proofmode_upto_bad.
From auth.base_logic Require Export spec_ra.

Class authPreG Σ := AuthPreG {
  auth_preG_heapGpreS :: heapGpreS Σ;
  auth_preG_spec :: inG Σ (authR cfgUR);
}.
Class authG Σ := AuthG {
  authG_heapG :: heapGS Σ;
  authG_verifierG :: cfgSG Σ;
  authG_idealG :: cfgSG Σ;
}.

Definition authΣ : gFunctors := #[heapΣ; GFunctor (authR cfgUR)].
Global Instance subG_authPreG {Σ} : subG authΣ Σ → authPreG Σ.
Proof. solve_inG. Qed.

(** Prover spec resources  *)
#[global] Notation cfg_authᵥ := (@cfg_auth _ authG_verifierG).
#[global] Notation "l ↦ᵥ dq v" :=
  (@heapS_pointsto _ authG_verifierG l dq v)
    (at level 20, dq custom dfrac at level 1, format "l  ↦ᵥ dq  v") : bi_scope.
#[global] Notation "j ⤇ᵥ e" :=
  (@tpool_pointsto _ authG_verifierG j e) (at level 20) : bi_scope.

(** Ideal spec resources  *)
#[global] Notation cfg_authᵢ := (@cfg_auth _ authG_idealG).
#[global] Notation "l ↦ᵢ dq v" :=
  (@heapS_pointsto _ authG_idealG l dq v)
    (at level 20, dq  custom dfrac at level 1, format "l  ↦ᵢ dq  v") : bi_scope.
#[global] Notation "j ⤇ᵢ e" :=
  (@tpool_pointsto _ authG_idealG j e) (at level 20) : bi_scope.

(** Semantic intepretation of types *)
Record lrel Σ := LRel {
  lrel_car :> val → val → val → iProp Σ;
  lrel_persistent v1 v2 v3 : Persistent (lrel_car v1 v2 v3)
}.
Arguments LRel {_} _%I {_}.
Arguments lrel_car {_} _ _ _ _ : simpl never.
Declare Scope lrel_scope.
Bind Scope lrel_scope with lrel.
Delimit Scope lrel_scope with lrel.
Global Existing Instance lrel_persistent.

Lemma ofe_ne_eta {A B : ofe} (F : A -n> B) :
  NonExpansive F → NonExpansive (λ a : A, F a).
Proof. apply _. Qed.

(** The COFE structure on semantic types *)
Section lrel_ofe.
  Context `{Σ : gFunctors}.

  Global Instance lrel_equiv : Equiv (lrel Σ) := λ A B, ∀ w1 w2 w3, A w1 w2 w3 ≡ B w1 w2 w3.
  Global Instance lrel_dist : Dist (lrel Σ) := λ n A B, ∀ w1 w2 w3, A w1 w2 w3 ≡{n}≡ B w1 w2 w3.
  Lemma lrel_ofe_mixin : OfeMixin (lrel Σ).
  Proof. by apply (iso_ofe_mixin (lrel_car : lrel Σ → (val -d> val -d> val -d> iPropO Σ))). Qed.
  Canonical Structure lrelC := Ofe (lrel Σ) lrel_ofe_mixin.

  Global Instance lrel_cofe : Cofe lrelC.
  Proof.
    apply (iso_cofe_subtype' (λ A : val -d> val -d> val -d> iPropO Σ,
      ∀ w1 w2 w3, Persistent (A w1 w2 w3)) (@LRel _) lrel_car)=>//.
    - apply _.
    - apply limit_preserving_forall=> w1.
      apply limit_preserving_forall=> w2.
      apply limit_preserving_forall=> w3.
      apply bi.limit_preserving_Persistent.
      intros n P Q HPQ. apply (HPQ w1 w2 w3).
  Qed.

  Global Instance lrel_inhabited : Inhabited (lrel Σ) := populate (LRel inhabitant).

  Global Instance lrel_car_ne n : Proper (dist n ==> (=) ==> (=) ==> (=) ==> dist n) lrel_car.
  Proof. by intros A A' ? w1 w2 <- w3 w4 <- w5 w6 <-.  Qed.
  Global Instance lrel_car_proper : Proper ((≡) ==> (=) ==> (=) ==> (=) ==> (≡)) lrel_car.
  Proof.
    intros ?? H ?????????. simplify_eq.
    apply equiv_dist => n.
    rewrite equiv_dist in H.
    rewrite H //.
  Qed.

  Lemma lrel_equivI (A B : lrel Σ) :
    A ≡@{lrel Σ} B ⊣⊢@{iProp Σ} (∀ w1 w2 w3, A w1 w2 w3 ≡@{iProp Σ} B w1 w2 w3).
  Proof.
    iSplit.
    - iIntros "H" (???). by iRewrite "H".
    - iStopProof. uPred.unseal.
      split. intros n x Hnx Heq ????. done.
  Qed.

End lrel_ofe.

Arguments lrelC : clear implicits.

(** Relational judgment *)
Section refines.
  Context `{!authG Σ}.

  Definition spec_inv (ρᵥ ρᵢ: cfg heap_lang) : iProp Σ :=
    (∃ tpᵥ σᵥ tpᵢ σᵢ,
        (** Authoritative resources for verifier and ideal *)
        cfg_authᵥ tpᵥ σᵥ ∗ cfg_authᵢ tpᵢ σᵢ ∗
        (** Valid verifier and ideal executions *)
        ⌜rtc erased_step ρᵥ (tpᵥ, σᵥ)⌝ ∗ ⌜rtc erased_step ρᵢ (tpᵢ, σᵢ)⌝)%I.
  Definition spec_ctx : iProp Σ :=
    (∃ ρᵥ ρᵢ, inv specN (spec_inv ρᵥ ρᵢ))%I.

  Global Instance spec_ctx_persistent : Persistent spec_ctx.
  Proof. apply _. Qed.

  Definition spec_verifier tᵥ eᵥ : iProp Σ :=
    (spec_ctx ∗ tᵥ ⤇ᵥ eᵥ)%I.

  Definition spec_ideal tᵢ eᵢ : iProp Σ :=
    (spec_ctx ∗ tᵢ ⤇ᵢ eᵢ)%I.

  Definition refines (E : coPset) (eₚ eᵥ eᵢ : expr) (A : lrel Σ) : iProp Σ :=
    (∀ Kᵥ tᵥ Kᵢ tᵢ,
        spec_verifier tᵥ (fill Kᵥ eᵥ) -∗
        spec_ideal tᵢ (fill Kᵢ eᵢ) -∗
        WP eₚ @ E {{ vₚ, ∃ (vᵥ vᵢ : val),
              spec_verifier tᵥ (fill Kᵥ vᵥ) ∗ spec_ideal tᵢ (fill Kᵢ vᵢ) ∗ A vₚ vᵥ vᵢ }})%I.

 Global Instance refines_ne E n :
    Proper ((=) ==> (=) ==> (=) ==> (dist n) ==> (dist n)) (refines E).
  Proof. solve_proper. Qed.

  Global Instance refines_proper E  :
    Proper ((=) ==> (=) ==> (=) ==> (≡) ==> (≡)) (refines E).
  Proof. solve_proper. Qed.

End refines.

Notation "'REL' e1 '<<' e2 '<<' e3 '@' E ':' A" :=
  (refines E e1%E e2%E e3%E A)
  (at level 100, E at next level, e1, e2, e3 at next level,
   A at level 200,
   format "'REL'  e1  '/ ' '<<'  e2  '/ ' '<<'  e3  '/ ' '@'  E  :  A").

Notation "'REL' e1 '<<' e2 '<<' e3 ':' A" :=
  (refines ⊤ e1%E e2%E e3%E A)
  (at level 100, e1, e2, e3 at next level,
   A at level 200,
    format "'REL'  e1  '/ ' '<<'  e2  '/ ' '<<'  e3  '/ ' :  A").

Section semtypes.
  Context `{authG Σ}.

  Implicit Types e : expr.
  Implicit Types E : coPset.
  Implicit Types A B : lrel Σ.

  Definition lrel_true : lrel Σ := LRel (λ w1 w2 w3, True)%I.
  Definition lrel_unit : lrel Σ := LRel (λ w1 w2 w3, ⌜w1 = #() ∧ w2 = #() ∧ w3 = #()⌝%I).
  Definition lrel_bool : lrel Σ := LRel (λ w1 w2 w3, ∃ b : bool, ⌜w1 = #b ∧ w2 = #b ∧ w3 = #b ⌝)%I.
  Definition lrel_int : lrel Σ := LRel (λ w1 w2 w3, ∃ n : Z, ⌜w1 = #n ∧ w2 = #n ∧ w3 = #n⌝)%I.
  Definition lrel_string : lrel Σ := LRel (λ w1 w2 w3, ∃ s : string, ⌜w1 = #s ∧ w2 = #s ∧ w3 = #s⌝)%I.

  Definition lrel_arr' (A1 A2 : lrel Σ) : lrel Σ := LRel (λ w1 w2 w3,
    □ ∀ v1 v2 v3, A1 v1 v2 v3 -∗ REL App w1 v1 << App w2 v2 << App w3 v3 @ ⊤ : A2)%I.
  Program Definition lrel_arr : lrelC Σ -n> lrelC Σ -n> lrelC Σ := λne A1 A2, lrel_arr' A1 A2.
  Solve Obligations with solve_proper.

  Definition lrel_ref' (A : lrel Σ) : lrel Σ := LRel (λ w1 w2 w3,
    ∃ l1 l2 l3 : loc, ⌜w1 = #l1⌝ ∧ ⌜w2 = #l2⌝ ∧ ⌜w3 = #l3⌝ ∧
      inv (authN .@ "ref" .@ (l1,l2,l3)) (∃ v1 v2 v3, l1 ↦ v1 ∗ l2 ↦ᵥ v2 ∗ l3 ↦ᵢ v3 ∗ A v1 v2 v3))%I.
  Program Definition lrel_ref : lrelC Σ -n> lrelC Σ := λne A, lrel_ref' A.
  Solve Obligations with solve_proper.

  Definition lrel_prod' (A B : lrel Σ) : lrel Σ := LRel (λ w1 w2 w3,
    ∃ v1 v2 v3 v1' v2' v3',
      ⌜w1 = (v1,v1')%V⌝ ∧ ⌜w2 = (v2,v2')%V⌝ ∧ ⌜w3 = (v3,v3')%V⌝ ∧
        A v1 v2 v3 ∗ B v1' v2' v3')%I.
  Program Definition lrel_prod : lrelC Σ -n> lrelC Σ -n> lrelC Σ := λne A1 A2, lrel_prod' A1 A2.
  Solve Obligations with solve_proper.

  Definition lrel_sum' (A B : lrel Σ) : lrel Σ := LRel (λ w1 w2 w3,
    ∃ v1 v2 v3, (⌜w1 = InjLV v1⌝ ∧ ⌜w2 = InjLV v2⌝ ∧ ⌜w3 = InjLV v3⌝ ∧ A v1 v2 v3)
                ∨  (⌜w1 = InjRV v1⌝ ∧ ⌜w2 = InjRV v2⌝ ∧ ⌜w3 = InjRV v3⌝ ∧ B v1 v2 v3))%I.
  Program Definition lrel_sum : lrelC Σ -n> lrelC Σ -n> lrelC Σ := λne A1 A2, lrel_sum' A1 A2.
  Solve Obligations with solve_proper.

  Definition lrel_option (A : lrel Σ) : lrel Σ := lrel_sum lrel_unit A.

  Definition lrel_forall' {T : ofe} (C : T -n> lrel Σ) : lrel Σ := LRel (λ w1 w2 w3,
    ∀ A : T, (lrel_arr lrel_true (C A)) w1 w2 w3)%I.
  Program Definition lrel_forall {T : ofe} : (T -n> lrelC Σ) -n> lrelC Σ := λne C, lrel_forall' C.
  Next Obligation. rewrite /lrel_forall'; solve_proper. Qed.

  Definition lrel_exists' {T : ofe} (C : T -n> lrel Σ) : lrel Σ := LRel (λ w1 w2 w3,
    ∃ A : T, C A w1 w2 w3)%I.
  Program Definition lrel_exists {T : ofe} : (T -n> lrelC Σ) -n> lrelC Σ := λne C, lrel_exists' C.
  Next Obligation. solve_proper. Qed.

  Definition lrel_rec1 (C : lrelC Σ -n> lrelC Σ) (rec : lrel Σ) : lrel Σ :=
    LRel (λ w1 w2 w3, ▷ C rec w1 w2 w3)%I.
  Global Instance lrel_rec1_contractive C : Contractive (lrel_rec1 C).
  Proof.
    intros n. intros P Q HPQ.
    unfold lrel_rec1. intros w1 w2 w3. rewrite {1 4}/lrel_car /=.
    f_contractive. f_equiv. by apply C.
  Qed.

  Program Definition lrel_rec : (lrelC Σ -n> lrelC Σ) -n> lrel Σ :=
    λne C, fixpoint (lrel_rec1 C).
  Next Obligation.
    intros n F F' HF.
    apply fixpoint_ne=> X w1 w2 w3.
    unfold lrel_rec1, lrel_car.
    f_equiv.
    apply lrel_car_ne; eauto.
  Qed.

  Lemma lrel_rec_equiv (C C' : lrelC Σ -n> lrelC Σ) :
    C ≡ C' → lrel_rec C ≡ lrel_rec C'.
  Proof. intros ?. by f_equiv. Qed.

  Lemma lrel_rec_unfold (C : lrelC Σ -n> lrelC Σ) : lrel_rec C ≡ lrel_rec1 C (lrel_rec C).
  Proof. apply fixpoint_unfold. Qed.

  #[global] Opaque lrel_rec.

End semtypes.

(** Nice notations *)
Notation "()" := lrel_unit : lrel_scope.
Infix "→" := lrel_arr : lrel_scope.
Infix "*" := lrel_prod : lrel_scope.
Infix "+" := lrel_sum : lrel_scope.
Notation "'ref' A" := (lrel_ref A) : lrel_scope.
Notation "∀; x .. y , P" :=
  (lrel_forall (λne x, .. (lrel_forall (λne y, P%lrel)) ..))
    (at level 200, x binder, y binder, right associativity) : lrel_scope.
Notation "∃; x .. y , P" :=
  (lrel_exists (λne x, .. (lrel_exists (λne y, P%lrel)) ..))
(at level 200, x binder, y binder, right associativity) : lrel_scope.
