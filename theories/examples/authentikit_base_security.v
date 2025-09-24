From auth.prelude Require Import stdpp.
From auth.rel_logic_bin Require Export model interp lib.
From auth.heap_lang.lib Require Import serialization list.
From auth.examples Require Export authentikit authenticatable_base.

Section authenticatable.
  Context `{aG : !authG Σ}.

  Inductive evi_type : Type :=
  | tprod (t1 t2 : evi_type)
  | tsum (t1 t2 : evi_type)
  | tstring
  | tint.

  #[global] Instance : Inhabited evi_type.
  Proof. constructor. apply tstring. Qed.

  Fixpoint evi_type_ser (t : evi_type) : serialization_scheme :=
    match t with
    | tprod t1 t2 => prod_serialization_scheme (evi_type_ser t1) (evi_type_ser t2)
    | tsum t1 t2 => sum_serialization_scheme (evi_type_ser t1) (evi_type_ser t2)
    | tstring => string_serialization_scheme
    | tint => int_serialization_scheme
    end.

  Lemma evi_type_ser_inj (t1 t2 : evi_type) v1 v2 s :
    s_is_ser (evi_type_ser t1) v1 s →
    s_is_ser (evi_type_ser t2) v2 s →
    v1 = v2.
  Proof.
    induction t1 in t2, v1, v2, s |-* => /=.
    - intros Ht1 Ht2. destruct! Ht1; simplify_eq.
      destruct t2 => /=; destruct! Ht2; simplify_eq.
      + f_equal; [by eapply IHt1_1|].  by eapply IHt1_2.
      + exfalso. by eapply prod_ser_inl_ser_neq.
      + exfalso. by eapply prod_ser_inr_ser_neq.
      + exfalso. by eapply prod_ser_string_ser_neq.
      + exfalso. by eapply prod_ser_int_ser_neq.
    - intros Ht1 Ht2. destruct! Ht1; simplify_eq.
      + destruct t2 => /=; destruct! Ht2; simplify_eq.
        * exfalso. by eapply prod_ser_inl_ser_neq.
        * f_equal. by eapply IHt1_1.
      + destruct t2 => /=; destruct! Ht2; simplify_eq.
        * exfalso. by eapply prod_ser_inr_ser_neq.
        * f_equal. by eapply IHt1_2.
    - intros Ht1 Ht2. destruct! Ht1; simplify_eq.
      destruct t2 => /=; destruct! Ht2; simplify_eq.
      + exfalso. by eapply prod_ser_string_ser_neq.
      + done.
    - intros Ht1 Ht2. destruct! Ht1; simplify_eq.
      destruct t2 => /=; destruct! Ht2; simplify_eq.
      + exfalso. by eapply prod_ser_int_ser_neq.
      + done.
  Qed.

  Definition ser_spec (ser : val) (t : evi_type) (A : lrel Σ) : iProp Σ :=
    ∀ (v1 v2 : val),
      {{{ ▷ A v1 v2 }}} ser v1 {{{ s, RET #s; ⌜s_is_ser (evi_type_ser t) v1 s⌝ }}}.

  Definition deser_spec (deser : val) (t : evi_type) : iProp Σ :=
    ∀ (s : string),
      {{{ True }}}
        deser #s
      {{{ o, RET $o; if o is Some v then ⌜s_is_ser (evi_type_ser t) v s⌝ else True }}}.

  Definition lrel_evidence' (A : lrel Σ) : lrel Σ :=
    LRel (λ v1 v2,
        ∃ (t : evi_type) (ser deser : val),
          ⌜v1 = (ser, deser)%V⌝ ∗ ser_spec ser t A ∗ deser_spec deser t)%I.

  Program Definition lrel_evidence : kindO Σ (⋆ ⇒ ⋆)%kind := λne A, lrel_evidence' A.
  Next Obligation.
    intros ??????.
    rewrite /lrel_car/= /ser_spec.
    solve_proper.
  Qed.

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
    iDestruct "HA" as (tA serA deserA ->) "[#HserA #HdeserA]". clear.
    iIntros (??) "Hi".
    i_pures; wp_pures.
    iModIntro. iFrame.
    iIntros (??) "!# HB".
    interp_unfold! in "HB".
    iDestruct "HB" as (tB serB deserB ->) "[#HserB #HdeserB]". clear.
    iIntros (??) "Hi".
    i_pures; wp_pures.
    rewrite /prod_scheme /prod_ser /prod_deser.
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

  Lemma refines_Auth_sum Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆; ⋆, var2 var1 → var2 var0 → var2 (var1 + var0) ⟧
      (ext Δ lrel_evidence) v_Auth_sum i_Auth_sum.
  Proof.
    iIntros (A ??) "!# _".
    iIntros (??) "Hi".
    rewrite /v_Auth_sum /i_Auth_sum.
    i_pures; wp_pures.
    iModIntro. iFrame.
    interp_unfold.
    iIntros (B ??) "!# _".
    iIntros (??) "Hi".
    i_pures; wp_pures.
    iModIntro. iFrame.
    iIntros (??) "!# HA".
    interp_unfold! in "HA".
    iDestruct "HA" as (tA serA deserA ->) "[#HserA #HdeserA]". clear.
    iIntros (??) "Hi".
    i_pures; wp_pures.
    iModIntro. iFrame.
    iIntros (??) "!# HB".
    interp_unfold! in "HB".
    iDestruct "HB" as (tB serB deserB ->) "[#HserB #HdeserB]". clear.
    iIntros (??) "Hi".
    i_pures; wp_pures.
    rewrite /sum_scheme /sum_ser /sum_deser.
    wp_pures. iModIntro. iFrame.
    interp_unfold!.
    iExists (tsum tA tB), _, _.
    iSplit; [done|]. clear. iSplit.
    - iIntros (v1 v2 Ψ) "!# (%w & %u & #Hsum) HΨ".
      wp_apply (sum_ser'_spec (evi_type_ser tA) (evi_type_ser tB)
                  (λ v1, A v1 u)%I (λ v1, B v1 u)%I with "[]"); [|done|done| |done].
      { iModIntro. iDestruct "Hsum" as "[(? & ? & HA) | (? & ? & HB)]"; eauto. }
      iExists _; iDestruct "Hsum" as "[(? & ? & HA) | (? & ? & HB)]"; eauto.
    - iIntros (s Ψ) "!# _ HΨ". by wp_apply sum_deser'_sound.
  Qed.

  Lemma refines_Auth_string :
    ⊢ lrel_evidence lrel_string v_Auth_string i_Auth_string.
  Proof.
    iExists tstring, _, _.
    iSplit; [done|]. rewrite /ser_spec /deser_spec.
    iSplit.
    - iIntros (v1 v2 Ψ) "!# (% & #? & #?) HΨ".
      wp_apply string_ser_spec; [|done]. by iExists _.
    - iIntros (s Ψ) "!# _ HΨ".
      wp_apply string_deser_spec; [done|].
      iIntros ([] ?); by iApply "HΨ".
  Qed.

  Lemma refines_Auth_int :
    ⊢ lrel_evidence lrel_int v_Auth_int i_Auth_int.
  Proof.
    iExists tint, _, _.
    iSplit; [done|]. rewrite /ser_spec /deser_spec.
    iSplit.
    - iIntros (v1 v2 Ψ) "!# (% & #? & #?) HΨ".
      wp_apply int_ser_spec; [|done]. by iExists _.
    - iIntros (s Ψ) "!# _ HΨ".
      wp_apply int_deser_spec; [done|].
      iIntros ([] ?); by iApply "HΨ".
  Qed.

  Lemma refines_Auth_mu Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆ ⇒ ⋆, var1 (var0 (μ: ⋆; var1 var0)) → var1 (μ: ⋆; var1 var0) ⟧
      (ext Δ lrel_evidence) v_Auth_mu i_Auth_mu.
  Proof.
    rewrite /lrel_car/=.
    iIntros (A v1 v2) "!# _". iIntros (??) "Hi".
    rewrite /i_Auth_mu /v_Auth_mu.
    i_pures. wp_pures.
    iFrame. iModIntro. clear.
    interp_unfold!.
    iIntros (??) "!# H".
    iIntros (??) "Hi".
    interp_unfold! in "H".
    iDestruct "H" as "(%t & %ser & %deser & -> & #Hser & #Hdeser)".
    i_pures. wp_pures.
    iFrame. iModIntro.
    interp_unfold!.
    iExists t, _, _. iSplit; [done|].
    clear. iSplit.
    - iIntros (v1 v2 Ψ) "!# Hs HΨ".
      wp_pures.
      rewrite interp_rec_star_unfold.
      rewrite interp_unseal /=.
      by wp_apply ("Hser" with "Hs").
    - iIntros (s Ψ) "!# _ HΨ". wp_pures. by wp_apply "Hdeser".
  Qed.

(*  Definition lrel_random (A : lrel Σ) : lrel Σ :=
    LRel (λ v1 v2,
        ∃ (p pk: val) (x1 x2 : string),
          A x1 x2 ∗ verify pk x1 p ∗ proof_to_hash p v1)%I. *)

  Definition lrel_auth' (A : lrel Σ) : lrel Σ :=
    LRel (λ v1 v2,
        ∃ (a1 : val) (t : evi_type) (s1 : string),
          ⌜s_is_ser (evi_type_ser t) a1 s1⌝ ∗ ⌜v1 = #(hash s1)⌝ ∗
          A a1 v2 ∗ hashed s1)%I.

  Program Definition lrel_auth : kindO Σ (⋆ ⇒ ⋆)%kind := λne A, lrel_auth' A.
  Next Obligation. solve_proper. Qed.

  Definition is_proof (v : val) : iProp Σ :=
    ∃ (l : list string), ⌜is_list l v⌝.

  Definition lrel_proof : lrel Σ :=
    LRel (λ v1 _, is_proof v1 )%I.

  Definition auth_ctx {Θ} (Δ : ctxO Σ Θ) (R : kindO Σ (⋆ ⇒ ⋆)) :=
    ext (ext (ext Δ lrel_auth) R) lrel_evidence.

  Lemma refines_Auth_auth Θ (Δ : ctxO Σ Θ) R :
    ⊢ ⟦ ∀: ⋆, var1 (var3 var0) ⟧
      (auth_ctx Δ R) v_Auth_auth i_Auth_auth.
  Proof.
    iIntros (A ??) "!# _"; rewrite -!/interp.
    iIntros (??) "Hi".
    rewrite /v_Auth_auth /i_Auth_auth.
    i_pures; wp_pures.
    iModIntro. iFrame.
    rewrite /auth_ctx.
    interp_unfold!.
    iExists tstring, _, _.
    iSplit; [done|]. clear. iSplit.
    - iIntros (???) "!# Hauth H".
      iDestruct "Hauth" as (???) "(#? & #? & #HA)".
      wp_apply string_ser_spec; [by iExists _|]. done.
    - iIntros (??) "!# _ H".
      wp_apply string_deser_spec; [done|].
      by iIntros ([] ?); iApply "H".
  Qed.

  Lemma refines_auth_auth Θ (Δ : ctxO Σ Θ) R :
    ⊢ ⟦ ∀: ⋆, var1 var0 → var0 → var3 var0 ⟧
      (auth_ctx Δ R) v_auth i_auth.
  Proof.
    iIntros (???) "!# _"; rewrite -/interp.
    iIntros (??) "Hi".
    rewrite /v_auth  /i_auth.
    i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iIntros (??) "!# #HeviA".
    rewrite /auth_ctx.
    interp_unfold! in "HeviA".
    iDestruct "HeviA" as (tA ser deser ->) "[#Hser #Hdeser]".
    iIntros (??) "Hi".
    i_pures; wp_pures.
    iFrame.
    interp_unfold.
    iIntros "!> !>" (w1 w2) "#HA". clear.
    iIntros (??) "Hi".
    i_pures; wp_pures.
    interp_unfold! in "HA".
    wp_apply "Hser"; [done|].
    iIntros (s1 Hs1).
    wp_apply (wp_hash with "[$]"). iIntros "#Hh1".
    iFrame.
    interp_unfold!.
    by iFrame "# %".
  Qed.

End authenticatable.
