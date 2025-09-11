From auth.prelude Require Import stdpp.
From auth.rel_logic_bin Require Export model spec_rules spec_tactics interp lib adequacy fundamental.
From auth.heap_lang.lib Require Import list serialization.
From auth.examples Require Export authentikit_susp authenticatable_base_susp.
From iris.base_logic.lib Require Export invariants.

Section authenticatable.
  Context `{!authG Σ} (N : namespace).

  Inductive evi_type : Type :=
  | tprod (t1 t2 : evi_type)
  | tsum (t1 t2 : evi_type)
  | tstring
  | tint
  | tauth.

  #[global] Instance : Inhabited evi_type.
  Proof. constructor. apply tstring. Qed.

  Definition auth_serialization_scheme : serialization_scheme :=
    sum_serialization_scheme string_serialization_scheme string_serialization_scheme.

  Fixpoint s_is_ser' (t : evi_type) (v : val) (s : string) : iProp Σ :=
    match t with
    | tprod t1 t2 => prod_is_ser' v s (s_is_ser' t1) (s_is_ser' t2)
    | tsum t1 t2 => sum_is_ser' v s (s_is_ser' t1) (s_is_ser' t2)
    | tstring => string_is_ser v s
    | tint => int_is_ser v s
    | tauth =>
        (∃ (h : string), ⌜v = InjLV #h⌝ ∗ s_is_ser (g := gwp_upto_bad) auth_serialization_scheme (InjRV #h) s) ∨
          (∃ (susp : loc), ⌜v = InjRV #susp⌝ ∗
            ((∃ (h : string), susp ↦ (InjRV #h) ∗ s_is_ser (g := gwp_upto_bad) auth_serialization_scheme (InjRV #h) s) ∨
               (∃ (v : val), susp ↦ InjLV v)))
    end.

  Fixpoint evi_type_ser (t : evi_type) : serialization_scheme :=
    match t with
    | tprod t1 t2 => prod_serialization_scheme (evi_type_ser t1) (evi_type_ser t2)
    | tsum t1 t2 => sum_serialization_scheme (evi_type_ser t1) (evi_type_ser t2)
    | tstring => string_serialization_scheme
    | tint => int_serialization_scheme
    | tauth => auth_serialization_scheme
    end.
  
  Fixpoint evi_type_count (t : evi_type) : expr :=
    match t with
    | tprod t1 t2 => prod_count (evi_type_count t1) (evi_type_count t2)
    | tsum t1 t2 => sum_count (evi_type_count t1) (evi_type_count t2)
    | tstring => string_count
    | tint => int_count
    | tauth => auth_count
    end.

  Fixpoint count_is_correct (t : evi_type) (v : val) (c : val) : iProp Σ :=
    match t with
    | tprod t1 t2 =>
        ∃ (c1 c2 : nat) (v1 v2 : val),
          count_is_correct t1 v1 #c1 ∗ count_is_correct t2 v2 #c2 ∗ ⌜#(c1 + c2) = c⌝
    | tsum t1 t2 =>
        (∃ (v1 : val), count_is_correct t1 v1 c) ∨ (∃ (v2 : val), count_is_correct t2 v2 c)
    | tstring | tint => ⌜c = #0⌝                                                 
    | tauth =>
        (∃ (l : val), ⌜v = InjLV l ∧ c = #1⌝) ∨ (∃ (r : val), ⌜v = InjRV r ∧ c = #0⌝)
    end.
                                                 
  Definition ser_spec (ser : val) (t : evi_type) (A : lrel Σ) : iProp Σ :=
    ∀ (v1 v2 : val),
      {{{ ▷ A v1 v2 }}} ser v1 {{{ s, RET #s; s_is_ser' t v1 s }}}.

  Definition deser_spec (deser : val) (t : evi_type) : iProp Σ :=
    ∀ (pid : nat) (s : string),
      {{{ True }}}
        deser #pid #s
        {{{ o, RET $o; if o is Some v then s_is_ser' t v s else True }}}.

  Definition count_spec (count : val) (t : evi_type) : iProp Σ :=
    ∀ (v : val),
      {{{ True }}}
        count v
        {{{ o, RET $o; if o is Some c then count_is_correct t v c else True }}}.

  Definition lrel_evidence' (A : lrel Σ) : lrel Σ :=
    LRel (λ v1 v2,
        ∃ (t : evi_type) (ser deser count : val),
          ⌜v1 = (ser, deser, count)%V⌝ ∗ ser_spec ser t A ∗ deser_spec deser t ∗ count_spec count t)%I.

  Program Definition lrel_evidence : kindO Σ (⋆ ⇒ ⋆)%kind := λne A, lrel_evidence' A.
  Next Obligation.
    intros ??????.
    rewrite /lrel_car/= /ser_spec.
    solve_proper.
  Qed.
  
End authenticatable.

Section proof.
  Context `{!authG Σ}.

  Lemma refines_Auth_pair Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆; ⋆, var2 var1 → var2 var0 → var2 (var1 * var0) ⟧
      (ext Δ lrel_evidence) v_Auth_pair i_Auth_pair.
  Proof.
    interp_unfold.
    iIntros (A ??) "!# _".
    iIntros (??) "Hi".
    rewrite /v_Auth_pair /i_Auth_pair.
    i_pures; wp_pures.
    iModIntro. iFrame.
    iIntros (B ??) "!# _".
    iIntros (??) "Hi".
    i_pures; wp_pures.
    iModIntro. iFrame.
    iIntros (??) "!# HA".
    interp_unfold! in "HA".
    iDestruct "HA" as (tA serA deserA countA ->) "(#HserA & #HdeserA & #HcountA)". clear.
    iIntros (??) "Hi".
    i_pures; wp_pures.
    iModIntro. iFrame.
    iIntros (??) "!# HB".
    interp_unfold! in "HB".
    iDestruct "HB" as (tB serB deserB countB ->) "(#HserB & #HdeserB & #HcountB)". clear.
    iIntros (??) "Hi".
    i_pures; wp_pures.
    rewrite /prod_scheme /prod_ser /prod_deser /prod_count.
    wp_pures. iFrame. iModIntro.
    interp_unfold!.
    iExists (tprod tA tB), _, _.
    iSplit; [done|]. clear. iSplit.
    - iIntros (v1 v2 ?) "!# Hp H".
      iDestruct "Hp" as (w1 w2 u1 u2) "(>-> & >-> & #HA & #HB)".
      wp_apply (prod_ser'_spec (evi_type_ser tA) (evi_type_ser tB)
                  (λ v1, A v1 w2)%I (λ v1, B v1 u2)%I) => /=; [done| | | |done]. 
      { iIntros (?) "!# _ H". by wp_apply ("HserA" with "HA"). }
      { iIntros (?) "!# _ H". by wp_apply ("HserB" with "HB"). }
      iExists _, _.  eauto.
    - iIntros (s Ψ) "!# _ HΨ". by wp_apply prod_deser'_sound.
  Qed.
  
  
  

End proof.
