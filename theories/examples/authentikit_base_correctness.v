From auth.prelude Require Import stdpp.
From auth.rel_logic_tern Require Export model interp spec_tactics.
From auth.heap_lang.lib Require Import serialization list.
From auth.examples Require Export authentikit authenticatable_base.

Section authenticatable.
  Context `{!authG Σ}.

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

  Lemma evi_type_ser_inj_str (t1 t2 : evi_type) v s1 s2 :
    s_is_ser (evi_type_ser t1) v s1 →
    s_is_ser (evi_type_ser t2) v s2 →
    s1 = s2.
  Proof.
    induction t1 in t2, v, s1, s2 |-* => /=.
    - intros Ht1 Ht2. destruct! Ht1; simplify_eq.
      destruct t2 => /=; destruct! Ht2; simplify_eq; eauto.
      erewrite (IHt1_1 t2_1 _ H0); [|done|done].
      erewrite (IHt1_2 t2_2 _ H2); [|done|done]. done.
    - intros Ht1 Ht2. destruct! Ht1; simplify_eq.
      + destruct t2 => /=; destruct! Ht2; simplify_eq; auto.
        by erewrite (IHt1_1 t2_1 _ H1).
      + destruct t2 => /=; destruct! Ht2; simplify_eq; auto.
        by erewrite (IHt1_2 t2_2 _ H1).
    - intros Ht1 Ht2. destruct! Ht1; simplify_eq.
      destruct t2 => /=; destruct! Ht2; simplify_eq => //; auto.
    - intros Ht1 Ht2. destruct! Ht1; simplify_eq.
      destruct t2 => /=; destruct! Ht2; simplify_eq => //; auto.
  Qed.

  Lemma evi_type_ser_inj_val (t1 t2 : evi_type) v1 v2 s :
    s_is_ser (evi_type_ser t1) v1 s →
    s_is_ser (evi_type_ser t2) v2 s →
    v1 = v2.
  Proof.
    induction t1 in t2, v1, v2, s |-* => /=.
    - intros Ht1 Ht2. destruct! Ht1; simplify_eq.
      destruct t2 => /=; destruct! Ht2; simplify_eq; eauto.
      + f_equal; [by eapply IHt1_1|]. by eapply IHt1_2.
      + exfalso. by eapply prod_ser_inl_ser_neq.
      + exfalso. by eapply prod_ser_inr_ser_neq.
      + exfalso. by eapply prod_ser_string_ser_neq.
      + exfalso. by eapply prod_ser_int_ser_neq.
    - intros Ht1 Ht2. destruct! Ht1; simplify_eq.
      + destruct t2 => /=; destruct! Ht2; simplify_eq; auto.
        * exfalso. by eapply prod_ser_inl_ser_neq.
        * f_equal. by eapply IHt1_1.
      + destruct t2 => /=; destruct! Ht2; simplify_eq; auto.
        * exfalso. by eapply prod_ser_inr_ser_neq.
        * f_equal. by eapply IHt1_2.
    - intros Ht1 Ht2. destruct! Ht1; simplify_eq.
      destruct t2 => /=; destruct! Ht2; simplify_eq => //; auto.
      exfalso. by eapply prod_ser_string_ser_neq.
    - intros Ht1 Ht2. destruct! Ht1; simplify_eq.
      destruct t2 => /=; destruct! Ht2; simplify_eq => //; auto.
      exfalso. by eapply prod_ser_int_ser_neq.
  Qed.

  Definition v_deser_spec (v_deser a2 : val) (s : string) : iProp Σ :=
    (□ ∀ K tᵥ, spec_verifier tᵥ (fill K (v_deser #s)) ={⊤}=∗ spec_verifier tᵥ (fill K (SOMEV a2))).
  Definition v_ser_spec (v_ser a2 : val) (s : string) : iProp Σ :=
    (□ ∀ K tᵥ, spec_verifier tᵥ (fill K (v_ser a2)) ={⊤}=∗ spec_verifier tᵥ (fill K #s)).

  Definition ser_spec (p_ser v_ser v_deser : val) (t : evi_type) (A : lrel Σ) : iProp Σ :=
    ∀ (a1 a2 a3 : val),
      {{{ ▷ A a1 a2 a3 }}}
        p_ser a1
      {{{ s, RET #s;
          ⌜s_is_ser (evi_type_ser t) a2 s⌝ ∗
           v_ser_spec v_ser a2 s ∗ v_deser_spec v_deser a2 s }}}.
  
  Definition injective_lrel (A: lrel Σ) : iProp Σ :=
    □ ∀ v1 v2 w1 w2 x1 x2, A x1 v1 w1 -∗ A x2 v2 w2 -∗ ⌜(v1 = v2 ↔ w1 = w2) ∧ (x1 = x2 ↔ w1 = w2)⌝.
  
  Definition lrel_serialization (A : lrel Σ) : lrel Σ := LRel (λ v1 v2 _,
    ∃ (t : evi_type) (p_ser v_ser v_deser  : val),
      ⌜v1 = p_ser⌝ ∗ ⌜v2 = (v_ser, v_deser)%V⌝ ∗ injective_lrel A ∗
      ser_spec p_ser v_ser v_deser t A)%I.

  Program Definition lrel_evidence : kindO Σ (⋆ ⇒ ⋆)%kind := λne A, lrel_serialization A.
  Next Obligation.
    intros ???????. rewrite /lrel_car/= /ser_spec /injective_lrel. solve_proper.
  Qed.

  Lemma refines_Auth_pair Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆; ⋆, var2 var1 → var2 var0 → var2 (var1 * var0) ⟧
      (ext Δ lrel_evidence) p_Auth_pair v_Auth_pair i_Auth_pair.
  Proof.
    iIntros (A ???) "!# _"; rewrite -/interp.
    iIntros (????) "Hv Hi".
    rewrite /p_Auth_pair /v_Auth_pair /i_Auth_pair.
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame.
    iIntros (B ???) "!# _"; rewrite -/interp.
    iIntros (????) "Hv Hi".
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame.
    iIntros (???) "!# #HA"; rewrite -!/interp /=.
    iDestruct "HA" as (tA p_sA v_sA v_dA -> ->) "(#HinjA & #HserA)". clear.
    iIntros (????) "Hv Hi".
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame.
    iIntros (???) "!# #HB". clear.
    iDestruct "HB" as (tB p_sB v_sB v_dB -> ->) "(#HinjB & #HserB)". clear.
    iIntros (????) "Hv Hi".
    v_pures; i_pures; wp_pures.
    rewrite /prod_scheme /prod_ser /prod_deser.
    v_pures. wp_pures. iModIntro. iFrame.
    iExists (tprod tA tB), _, _, _.
    do 2 (iSplit; [done|]). iSplit.
    - iIntros (??????) "!# (% & % & % & % & % & % & % & % & % & HA & HB)
                           (% & % & % & % & % & % & % & % & % & HA' & HB')".
      simplify_eq.
      iPoseProof ("HinjA" with "HA HA'") as "[% %]".
      iPoseProof ("HinjB" with "HB HB'") as "[% %]".
      iPureIntro.
      split; split; intros ?; simplify_eq.
      + do 2 (destruct H, H1); done.
      + destruct H, H1.
        destruct H3, H4; done.
      + do 2 (destruct H0, H2); done.
      + destruct H0, H2.
        destruct H3, H4; done.
    - iIntros (a1 a2 a3 Ψ) "!# Hp HΨ".
      iDestruct "Hp" as (??????) "(>-> & >-> & >-> & #Ha & #Hb)".
      wp_pures.
      wp_apply ("HserA" with "Ha").
      iIntros (sA) "(%HsA & #HserA' & #HdeserA)".
      wp_pures.
      wp_apply ("HserB" with "Hb").
      iIntros (sB) "(%HsB & #HserB' & #HdeserB)".
      wp_pures.
      iApply "HΨ".
      iModIntro. iSplit.
      { iPureIntro. do 4 eexists; split_and!; eauto. }
      iSplit.
      + iIntros (??) "!# Hv".
        v_pures. v_bind (v_sA _).
        iMod ("HserA'" with "Hv") as "Hv /= ".
        v_pures. v_bind (v_sB _).
        iMod ("HserB'" with "Hv") as "Hv /= ".
        v_pures. iModIntro. done.
      + clear tᵥ. iIntros "!#" (K tᵥ) "Hv".
        iMod (prod_deser'_complete (s_is_ser (evi_type_ser tA)) (s_is_ser (evi_type_ser tB))
                ⊤ (v2, v2') _ _ _ () %I with "[//] [] [] [] [] [$Hv //]") as (?) "[Hv H]".
        { iIntros (?? HsA') "!# H". iIntros (??) "[% Hv]".
          rewrite -(evi_type_ser_inj_str _ _ _ _ _ HsA HsA').
          iMod ("HdeserA" with "[$Hv $Ha]") as "$". iModIntro. by iApply "H". }
        { iIntros (?? HsB') "!# H". iIntros (??) "[% Hv]".
          rewrite -(evi_type_ser_inj_str _ _ _ _ _ HsB HsB').
          iMod ("HdeserB" with "[$Hv $Hb //]") as "$". iModIntro. by iApply "H". }
        { iPureIntro. do 4 eexists. split_and!; eauto. }
        { instantiate (1 := (λ v, ⌜v = SOMEV _⌝)%I). simpl. eauto. }
        by iDestruct "H" as %->.
  Qed.

  Lemma refines_Auth_sum Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆; ⋆, var2 var1 → var2 var0 → var2 (var1 + var0) ⟧
      (ext Δ lrel_evidence) p_Auth_sum v_Auth_sum i_Auth_sum.
  Proof.
    iIntros (A ???) "!# _"; rewrite -/interp.
    iIntros (????) "Hv Hi".
    rewrite /p_Auth_sum /v_Auth_sum /i_Auth_sum.
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame.
    iIntros (B ???) "!# _"; rewrite -/interp.
    iIntros (????) "Hv Hi".
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame.
    iIntros (???) "!# #HA"; rewrite -!/interp /=.
    iDestruct "HA" as (tA p_sA v_sA v_dA -> ->) "(#HinjA & #HserA)". clear.
    iIntros (????) "Hv Hi".
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame.
    iIntros (???) "!# #HB". clear.
    iDestruct "HB" as (tB p_sB v_sB v_dB -> ->) "[#HinjB #HserB]". clear.
    iIntros (????) "Hv Hi".
    v_pures; i_pures; wp_pures.
    rewrite /sum_scheme /sum_ser /sum_deser.
    v_pures. wp_pures. iModIntro. iFrame.
    iExists (tsum tA tB), _, _, _.
    do 2 (iSplit; [done|]). clear.
    iSplit.
    - iIntros (??????) "!# (% & % & % & [(% & % & % & HA)|(% & % & % & HB)])
                           (% & % & % & [(% & % & % & HA')|(% & % & % & HB')])"; simplify_eq.
      + iPoseProof ("HinjA" with "HA HA'") as "[% %]".
        iPureIntro.
        split; split; intros ?; simplify_eq; f_equal.
        * by apply H.
        * by apply H.
        * by apply H0.
        * by apply H0.
      + iPureIntro.
        split; split; intros ?; simplify_eq.
      + iPureIntro.
        split; split; intros ?; simplify_eq.
      + iPoseProof ("HinjB" with "HB HB'") as "[% %]".
        iPureIntro.
        split; split; intros ?; simplify_eq; f_equal.
        * by apply H.
        * by apply H.
        * by apply H0.
        * by apply H0.
    - iIntros (??? Ψ) "!# Hsum HΨ".
      iDestruct "Hsum" as (???) "[(>-> & >-> & >-> & #HA) | (>-> & >-> & >-> & #HB)]".
      + wp_pures.
        wp_apply ("HserA" with "HA").
        iIntros (sA) "(%HsA & #Hser' & #Hdeser)".
        wp_pures. iModIntro.
        iApply "HΨ". iSplit; [by iExists _, _; iLeft|].
        iSplit.
        * iIntros (??) "!# Hv". v_pures.
          v_bind (v_sA _).
          iMod ("Hser'" with "Hv") as "Hv /=".
          v_pures. by iModIntro.
        * iIntros (??) "!# Hv".
          iMod (sum_deser'_complete (s_is_ser (evi_type_ser tA)) (s_is_ser (evi_type_ser tB))
                  ⊤ (InjLV _) _ () with "[] [] [] [] [$Hv //]") as (?) "[Hv H]".
          { iIntros (???) "!# % %HsA' H". simplify_eq. iIntros (??) "[% Hv]".
            pose proof (evi_type_ser_inj_str _ _ _ _ _ HsA HsA'). subst.
            iMod ("Hdeser" with "[$Hv //]") as "$". iModIntro. by iApply "H". }
          { iIntros (?? [=]). }
          { iPureIntro. do 2 eexists. by left. }
          { instantiate (1 := (λ v, ⌜v = SOMEV _⌝)%I). simpl. eauto. }
          by iDestruct "H" as %->.
      + wp_pures.
        wp_apply ("HserB" with "HB").
        iIntros (sA) "(%HsA & #Hser' & #Hdeser)".
        wp_pures. iModIntro.
        iApply "HΨ". iSplit; [by iExists _, _; iRight|].
        iSplit.
        * iIntros (??) "!# Hv". v_pures.
          v_bind (v_sB _).
          iMod ("Hser'" with "Hv") as "Hv /=".
          v_pures. by iModIntro.
        * iIntros (??) "!# Hv".
          iMod (sum_deser'_complete  (s_is_ser (evi_type_ser tA)) (s_is_ser (evi_type_ser tB))
                  ⊤ (InjRV _) _ () with "[] [] [] [] [$Hv //]") as (?) "[Hv H]".
          { iIntros (?? [=]). }
          { iIntros (???) "!# % %HsA' H". simplify_eq. iIntros (??) "[% Hv]".
            pose proof (evi_type_ser_inj_str _ _ _ _ _ HsA HsA'). subst.
            iMod ("Hdeser" with "[$Hv //]") as "$". iModIntro. by iApply "H". }
          { iPureIntro. do 2 eexists. by right. }
          { instantiate (1 := (λ v, ⌜v = SOMEV _⌝)%I). simpl. eauto. }
          by iDestruct "H" as %->.
  Qed.

  Lemma refines_Auth_string :
    ⊢ lrel_evidence lrel_string p_Auth_string v_Auth_string i_Auth_string.
  Proof.
    iExists tstring, _, _, _.
    do 2 (iSplit; [done|]). iSplit.
    - iIntros (??????) "!# (% & % & %) (% & % & %)".
      destruct H0, H2; by simplify_eq.
    - iIntros (????) "!# >(% & -> & -> & ->) H".
      rewrite /p_Auth_string /string_ser.
      wp_pures. iModIntro. iApply "H".
      iSplit; [by iExists _|]. iSplit.
      + iIntros (??) "!# Hv". by v_pures.
      + iIntros (??) "!# Hv".
        iMod (string_deser_spec' ⊤ _ _ () (λ v, ⌜v = SOMEV _⌝)%I
               with "[] [] [$Hv //]") as (?) "[H ->]"; [|done|done].
        by iExists _.
  Qed.

  Lemma refines_Auth_int :
    ⊢ lrel_evidence lrel_int p_Auth_int v_Auth_int i_Auth_int.
  Proof.
    iExists tint, _, _, _.
    do 2 (iSplit; [done|]). iSplit.
    - iIntros (??????) "!# (% & % & %) (% & % & %)".
      destruct H0, H2; by simplify_eq.
    - iIntros (????) "!# >(% & -> & -> & ->) H".
      rewrite /p_Auth_int /int_ser.
      wp_pures. iModIntro. iApply "H".
      iSplit; [by iExists _|]. iSplit.
      + iIntros (??) "!# Hv". by v_pures.
      + iIntros (??) "!# Hv".
        iMod (int_deser_spec' ⊤ _ _ () (λ v, ⌜v = SOMEV _⌝)%I
               with "[] [] [$Hv //]") as (?) "[H ->]"; [|done|done].
        by iExists _.
  Qed.

  Lemma refines_Auth_mu Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆ ⇒ ⋆, var1 (var0 (μ: ⋆; var1 var0)) → var1 (μ: ⋆; var1 var0) ⟧
      (ext Δ lrel_evidence) p_Auth_mu v_Auth_mu i_Auth_mu.
  Proof.
    iIntros (A v1 v2 v3) "!# _". rewrite -/interp.
    iIntros (????) "Hv Hi".
    rewrite /p_Auth_mu /i_Auth_mu /v_Auth_mu.
    i_pures. v_pures. wp_pures.
    iFrame. iModIntro. clear. simpl.
    iIntros (???) "!# HA".
    iDestruct "HA" as (???? -> ->) "#Hser".
    iIntros (????) "Hv Hi".
    i_pures. v_pures. wp_pures.
    iFrame. iModIntro.
    iExists t, _, _, _.
    do 2 (iSplit; [done|]). clear.
    (* iIntros (a1 a2 a3 Ψ) "!# HA HΨ".
    iEval (rewrite interp_rec_unfold /lrel_car /=) in "HA".
    rewrite /rec_fold. wp_pures.
    iApply ("Hser" with "HA").
    iIntros (s) "!> (%Hs & #Hser' & #Hdeser)".
    iApply "HΨ". iSplit; [done|]. iSplit.
    - iIntros "!#" (??) "Hv". v_pures. by iApply "Hser'".
    - iIntros "!#" (??) "Hv". v_pures. by iApply "Hdeser". *)
    Admitted.


  (** Note that [hashed s] is only needed from [authentikit_buf.v] and onwards  *)
  Definition lrel_auth' (A : lrel Σ) : lrel Σ := LRel (λ v1 v2 v3,
    ∃ (t : evi_type) (a1 a2 : val) (s : string),
      ⌜v1 = (a1, #(hash s))%V⌝ ∗ ⌜s_is_ser (evi_type_ser t) a2 s⌝ ∗ ⌜v2 = #(hash s)⌝ ∗
        injective_lrel A ∗ hashed s ∗ A a1 a2 v3)%I.

  Instance : NonExpansive injective_lrel.
  Proof. Admitted.

  Program Definition lrel_auth : kindO Σ (⋆ ⇒ ⋆)%kind := λne A, lrel_auth' A.
  Next Obligation. solve_proper. Qed.

  Definition auth_ctx {Θ} (Δ : ctxO Σ Θ) (R : kindO Σ (⋆ ⇒ ⋆)) :=
    ext (ext (ext Δ lrel_auth) R) lrel_evidence.

  Lemma refines_Auth_auth Θ (Δ : ctxO Σ Θ) (R : kindO Σ (⋆ ⇒ ⋆)) :
    ⊢ ⟦ ∀: ⋆, var1 (var3 var0) ⟧
      (auth_ctx Δ R) p_Auth_auth v_Auth_auth i_Auth_auth.
  Proof.
    iIntros (A ???) "!# _"; rewrite -!/interp.
    iIntros (????) "Hv Hi".
    rewrite /p_Auth_auth /v_Auth_auth /i_Auth_auth.
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame. simpl.
    rewrite /lrel_car /=.
    iExists tstring, _, _, _.
    do 2 (iSplit; [done|]). clear. iSplit.
    - iIntros (??????) "!# (% & % & % & % & % & % & % & HinjA & Hhash & HA)
                           (% & % & % & % & % & % & % & HinjA' & Hhash' & HA')".
      iPoseProof ("HinjA" with "HA HA'") as "[% %]".
      destruct (decide (collision s s0)) as [|Hnc%not_collision].
      { iExFalso. by iApply (hashes_auth.hashed_inj_or_coll with "Hhash Hhash'"). }
      destruct Hnc as [<- |?]; simplify_eq.
      + rewrite (evi_type_ser_inj_val _ _ _ _ _ H0 H3) in H5.
        iPureIntro. split; split; intros ?; simplify_eq.
        * by apply H5.
        * done.
        * by apply H6.
        * destruct H6. destruct H1; [done|].
          done.
      + iPureIntro. split; split; intros [=]; simplify_eq.
        * destruct H5. destruct H1; [done|].
          by rewrite (evi_type_ser_inj_str _ _ _ _ _ H0 H3).
        * destruct H5. destruct H1; [done|].
          rewrite (evi_type_ser_inj_str _ _ _ _ _ H0 H3).
          destruct H6. destruct H2; done.
    - iIntros (a1 a2 a3 Ψ) "!# Hauth HΨ".
      rewrite /lrel_car /=.
      iDestruct "Hauth" as (????) "(>-> & >% & >-> & _ & #HA)".
      wp_pures. iModIntro.
      iApply "HΨ". iSplit; [by iExists _|]. iSplit.
      + iIntros "!#" (??) "Hv". rewrite /string_ser.
        v_pures. by iModIntro.
      + iIntros "!#" (??) "Hv".
        iMod (string_deser_spec' ⊤ _ _ () (λ v, ⌜v = SOMEV _⌝)%I
               with "[] [] [$Hv //]") as (?) "[H ->]"; [|done|done].
        by iExists _.
  Qed.

  Lemma refines_auth_auth Θ (Δ : ctxO Σ Θ) (R : kindO Σ (⋆ ⇒ ⋆)) :
    ⊢ ⟦ ∀: ⋆, var1 var0 → var0 → var3 var0 ⟧
      (auth_ctx Δ R) p_auth v_auth i_auth.
  Proof.
    iIntros (????) "!# _"; rewrite -/interp.
    iIntros (????) "Hv Hi".
    rewrite /p_auth /v_auth  /i_auth.
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iIntros (???) "!#"; rewrite -!/interp /=.
    iDestruct 1 as (t ??? -> ->) "#[HinjA Hser]".

    iIntros (????) "Hv Hi".
    v_pures; i_pures; wp_pures.
    iFrame.
    iIntros "!> !>" (w1 w2 w3) "#HA". clear.
    iIntros (????) "Hv Hi".
    v_pures; i_pures; wp_pures.
    v_bind (v_ser _). wp_bind (p_ser _).

    wp_apply ("Hser" with "HA").
    iIntros (s1) "(%Hs1 & #Hser' & #Hdeser)".
    iMod ("Hser'" with "Hv") as "Hv /=".
    wp_apply (wp_hash with "[$]"); iIntros "Hhash".
    wp_pures.
    iMod (step_verifier_hash with "[$]") as "Hv"; [done|].
    iFrame. iModIntro.
    by iFrame "∗ # %".
  Qed.

End authenticatable.

(** * Prophesied proof stream *)
Section proph.
  Context `{heapGS Σ}.

  Fixpoint take_until {A B : Type} (f : A → option B) (xs : list A) : list B :=
    match xs with
    | []      => []
    | x :: xs =>
      match f x with
      | Some y => y :: (take_until f xs)
      | None   => []
      end
    end.

  Definition longest_valid_prefix (us : list val) : list string :=
    take_until (λ u, match u with InjRV (LitV (LitString s)) => Some s | _ => None end) us.

  Definition proph_proof (p : proph_id) (vs : list string) : iProp Σ :=
    (∃ (us : list (val * val)), proph p us ∗ ⌜vs = longest_valid_prefix (map snd us)⌝)%I.

  Lemma wp_resolve_proph_string p vs (s : string) :
    {{{ proph_proof p vs }}}
      resolve_proph: #p to: (SOMEV #s)
    {{{ vs', RET #(); ⌜vs = s :: vs'⌝ ∗ proph_proof p vs' }}}.
  Proof.
    iIntros (Φ) "(%us & Hp & %) HΦ".
    wp_apply (wp_resolve_proph with "Hp").
    iIntros (?) "[% Hp]". iApply "HΦ".
    iFrame. by simplify_eq.
  Qed.

  Lemma wp_resolve_proph_nil p vs :
    {{{ proph_proof p vs }}} resolve_proph: #p to: NONEV {{{ RET #(); ⌜vs = []⌝ }}}.
  Proof.
    iIntros (Φ) "(%us & Hp & %) HΦ".
    wp_apply (wp_resolve_proph with "Hp").
    iIntros (?) "[% Hp]". iApply "HΦ".
    by simplify_eq.
  Qed.

  Definition is_proof (v : val) (ps : list string) : Prop :=
    is_list ps v.

  Definition is_proph_proof (v : val) (p : proph_id) (ps : list string) : iProp Σ :=
    ⌜is_proof v ps⌝ ∗ proph_proof p ps.

End proph.
