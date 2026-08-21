From auth.prelude Require Import stdpp.
From auth.rel_logic_tern_susp Require Import model interp spec_tactics.
From iris.algebra Require Import gset auth.
From auth.examples Require Import authentikit authenticatable_base_susp.
From auth.examples.susp_correctness Require Export definitions helpers.


Section authenticatable.
  Context `{!authG Σ, !seqG Σ, !correctnessG Σ}.

  Local Typeclasses Opaque susp_p_ser_spec unsusp_p_ser_spec suspend_v_deser_spec
        unsuspend_spec v_ser_spec auth_ser_spec v_count_spec.

  Lemma refines_Auth_sum Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆; ⋆, var2 var1 → var2 var0 → var2 (var1 + var0) ⟧
      (ext Δ (lrel_evidence)) p_Auth_sum v_Auth_sum i_Auth_sum.
  Proof.
    iSplit; interp_unfold!; last first.
    { (* unary  *) admit. }
    (* ternary *)
    iIntros (A v1 v2 v3) "!# _"; rewrite -/interp.
    iIntros (????) "Hv Hi Htok".
    rewrite /p_Auth_sum /v_Auth_sum /i_Auth_sum.
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iSplit; interp_unfold!; last first.
    { (* inner-after-A unary *) admit. }
    iIntros (B w1 w2 w3) "!# _"; rewrite -/interp.
    iIntros (????) "Hv Hi Htok". v_pures; i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iSplit; interp_unfold!; last first.
    { (* inner-after-B unary *) admit. }
    iIntros (vA1 vA2 vA3) "!# #HA".
    interp_unfold! in "HA".
    iDestruct "HA" as "(HA_tern & #HA_un)".
    iDestruct "HA_tern" as (tA p_ssA p_usA p_spA p_uspA v_sA v_dA v_cA -> ->) "#HrestA".
    fold v_ser_spec.
    iIntros (????) "Hv Hi Htok". v_pures; i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iSplit; interp_unfold!; last first.
    { (* inner-after-HA unary *) admit. }
    iIntros (vB1 vB2 vB3) "!# #HB".
    interp_unfold! in "HB".
    iDestruct "HB" as "(HB_tern & #HB_un)".
    iDestruct "HB_tern" as (tB p_ssB p_usB p_spB p_uspB v_sB v_dB v_cB -> ->) "#HrestB".
    iIntros (????) "Hv Hi Htok".
    rewrite /sum_ser'' /sum_ser /sum_count.
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame.
    iSplit; interp_unfold!; last first.
    { (* final unary  *) admit. }
    (* Ternary evidence for the sum. *)
    iExists (tsum tA tB), _, _, _, _, _, _, _.
    iSplit; [done|]. iSplit; [done|].
    (* Now destruct HrestA/HrestB for use in bullets *)
    iDestruct "HrestA" as "(HusserA & HsserA & HsuspvdeserA & HunsuspA & HvserA & HvauthserA & HvcountA)".
    iDestruct "HrestB" as "(HusserB & HsserB & HsuspvdeserB & HunsuspB & HvserB & HvauthserB & HvcountB)".
    iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit]]]]].
    - (* 1. unsusp_p_ser_spec *)
      rewrite /unsusp_p_ser_spec.
      iIntros (v s Ψ) "!# Hser HΨ".
      iDestruct "Hser" as (w s') "[[Husser %HeqL] | [Husser %HeqR]]".
      + destruct HeqL as [-> ->]. wp_pures.
        wp_apply ("HusserA" with "Husser"). iIntros "_". wp_pures.
        unfold inl_ser_str. iApply "HΨ". by iModIntro.
      + destruct HeqR as [-> ->]. wp_pures.
        wp_apply ("HusserB" with "Husser"). iIntros "_". wp_pures.
        unfold inr_ser_str. iApply "HΨ". by iModIntro.
    - (* 2. susp_p_ser_spec *)
      rewrite /susp_p_ser_spec.
      iIntros (E a1 s c q HE Ψ) "!# (Hser & Htok & Hintr) HΨ".
      iEval (rewrite /susp_ser_p_real /=) in "Hser".
      iDestruct "Hser" as (w s') "[[#Hser1 [-> ->]] | [#Hser1 [-> ->]]]".
      + (* InjL: A serializer runs *)
        rewrite /sum_ser''. wp_pures. rewrite /sum_ser. wp_pures.
        wp_apply ("HsserA" $! _ _ _ c q with "[//] [$Hser1 $Htok $Hintr]").
        iIntros "(Htok & Hintr & HreachA)". wp_pures.
        unfold inl_ser_str. iApply "HΨ". iModIntro. iFrame "Htok Hintr".
        iIntros (γl) "Hg Hpen %Hsz Hbig".
        (* p_sub_obj's [sv = v'] conjunct makes suspensions under a sum
           unreachable, so γl is empty and the closure is trivial. *)
        iDestruct (susp_ser_p_real_sum_γl_empty_l with "Hser1 Hbig") as %->.
        iFrame "Hg Hpen". by rewrite !big_sepS_empty.
      + (* InjR: B serializer runs *)
        rewrite /sum_ser''. wp_pures. rewrite /sum_ser. wp_pures.
        wp_apply ("HsserB" $! _ _ _ c q with "[//] [$Hser1 $Htok $Hintr]").
        iIntros "(Htok & Hintr & HreachB)". wp_pures.
        unfold inr_ser_str. iApply "HΨ". iModIntro. iFrame "Htok Hintr".
        iIntros (γl) "Hg Hpen %Hsz Hbig".
        iDestruct (susp_ser_p_real_sum_γl_empty_r with "Hser1 Hbig") as %->.
        iFrame "Hg Hpen". by rewrite !big_sepS_empty.
    - (* 3. suspend_v_deser_spec (combined) *) admit.
    - (* 4. unsuspend_spec *)
      rewrite /unsuspend_spec.
      iIntros (E a1 a2 a3 HE Ψ) "!# (HA & Htok & Hintr) HΨ".
      iEval (rewrite interp_sum_combined) in "HA".
      wp_pures.
      iDestruct "HA" as (w1 w2 w3) "[(-> & -> & -> & HA) | (-> & -> & -> & HA)]".
      + wp_pures. interp_unfold! in "HA".
        wp_apply ("HunsuspA" with "[//] [$HA $Htok $Hintr]").
        iIntros (un_v s) "(Htok & Hintr & %Hunsusp & Hser)".
        wp_pures. iApply ("HΨ" $! _ (inl_ser_str s)).
        iFrame "Htok Hintr". iModIntro. iSplit.
        { iPureIntro. simpl. left. exists w1, un_v. done. }
        simpl. iExists un_v, s. iLeft. iFrame. done.
      + wp_pures. interp_unfold! in "HA".
        wp_apply ("HunsuspB" with "[//] [$HA $Htok $Hintr]").
        iIntros (un_v s) "(Htok & Hintr & %Hunsusp & Hser)".
        wp_pures. iApply ("HΨ" $! _ (inr_ser_str s)).
        iFrame "Htok Hintr". iModIntro. iSplit.
        { iPureIntro. simpl. right. exists w1, un_v. done. }
        simpl. iExists un_v, s. iRight. iFrame. done.
    - (* 5. v_ser_spec *)
      rewrite /v_ser_spec.
      iIntros (K tᵥ3 a s id Nc v_outer) "!# Hcnt Hser Hspec".
      iDestruct "Hser" as (w s') "[[Hser1 [-> ->]] | [Hser1 [-> ->]]]".
      + (* InjL *)
        iDestruct "Hcnt" as "[(%vA & %HeqL & HcntA) | (%vB & %HeqR & _)]"; last by inversion HeqR.
        injection HeqL as ->.
        rewrite /sum_ser''. v_pures.
        v_bind tᵥ3 (v_sA _).
        iMod ("HvserA" with "HcntA Hser1 Hspec") as "(HcntA & Hser1 & Hspec) /=".
        v_pures.
        unfold inl_ser_str. iModIntro. iFrame "Hspec".
        iSplitL "HcntA"; [iLeft; iExists vA; by iFrame|].
        iExists vA, s'. iLeft. iFrame "Hser1". done.
      + (* InjR *)
        iDestruct "Hcnt" as "[(%vA & %HeqL & _) | (%vB & %HeqR & HcntB)]"; first by inversion HeqL.
        injection HeqR as ->.
        rewrite /sum_ser''. v_pures.
        v_bind tᵥ3 (v_sB _).
        iMod ("HvserB" with "HcntB Hser1 Hspec") as "(HcntB & Hser1 & Hspec) /=".
        v_pures.
        unfold inr_ser_str. iModIntro. iFrame "Hspec".
        iSplitL "HcntB"; [iRight; iExists vB; by iFrame|].
        iExists vB, s'. iRight. iFrame "Hser1". done.
    - (* 6. auth_ser_spec *)
      rewrite /auth_ser_spec.
      iIntros (K tᵥ3 a1 un_a1 a2 a3 s Ψ) "!# (%Hunsusp & HA & #Hser & Htok & Hv) HΨ".
      rewrite /sum_ser''. v_pures.
      interp_unfold! in "HA".
      iDestruct "HA" as (v1' v2' v3') "[(>-> & >-> & >-> & HrA) | (>-> & >-> & >-> & HrB)]".
      + (* InjL *)
        destruct Hunsusp as [(w1 & un_w1 & Heq & -> & Hunsusp1) | (w1 & un_w1 & Heq & -> & _)];
          last by inversion Heq.
        injection Heq as <-.
        iDestruct "Hser" as (w s') "[[#Hser1 [%Hequ %Heqs]] | [_ [%Hequ _]]]";
          last by inversion Hequ.
        injection Hequ as <-. subst s.
        wp_pures.
        v_pures. v_bind (v_sA _).
        wp_apply ("HvauthserA" with "[HrA Htok Hv]").
        { by iFrame "HrA Hser1 Htok Hv". }
        iIntros "(Htok & Hsv & Hv) /=".
        v_pures. wp_pures.
        iApply "HΨ". iModIntro.
        unfold inl_ser_str. iFrame "Htok Hv".
        iExists v2', s'. iLeft. iSplit; [iExact "Hsv"|]. done.
      + (* InjR *)
        destruct Hunsusp as [(w1 & un_w1 & Heq & -> & _) | (w1 & un_w1 & Heq & -> & Hunsusp1)];
          first by inversion Heq.
        injection Heq as <-.
        iDestruct "Hser" as (w s') "[[_ [%Hequ _]] | [#Hser1 [%Hequ %Heqs]]]";
          first by inversion Hequ.
        injection Hequ as <-. subst s.
        wp_pures.
        v_pures. v_bind (v_sB _).
        wp_apply ("HvauthserB" with "[HrB Htok Hv]").
        { by iFrame "HrB Hser1 Htok Hv". }
        iIntros "(Htok & Hsv & Hv) /=".
        v_pures. wp_pures.
        iApply "HΨ". iModIntro.
        unfold inr_ser_str. iFrame "Htok Hv".
        iExists v2', s'. iRight. iSplit; [iExact "Hsv"|]. done.
    - (* 7. v_count_spec *)
      rewrite /v_count_spec.
      iIntros (K tᵥ3 a c id Nc v_outer) "!# Hcnt Hspec".
      iDestruct "Hcnt" as "[(%vA & -> & HcntA) | (%vB & -> & HcntB)]".
      + rewrite /sum_count. v_pures.
        v_bind tᵥ3 (v_cA _).
        iMod ("HvcountA" with "HcntA Hspec") as "[HcntA Hspec]".
        v_pures. iModIntro. iFrame.
        iLeft. iExists vA. by iFrame.
      + rewrite /sum_count. v_pures.
        v_bind tᵥ3 (v_cB _).
        iMod ("HvcountB" with "HcntB Hspec") as "[HcntB Hspec]".
        v_pures. iModIntro. iFrame.
        iRight. iExists vB. by iFrame.
  Admitted.

  Lemma refines_Auth_string :
    ⊢ (lrel_evidence) (LRelTern lrel_string lrel_un_string)
        p_Auth_string v_Auth_string i_Auth_string.
  Proof.
    iSplit; last first.
    { (* unary *)
      rewrite /lrel_evidence /lrel_evidence' /=. cbv [lrel_tern_un].
      rewrite /lrel_un_evidence /=.
      iExists tstring, _, _, _, _, _, _, _.
      iSplit; [done|]. iSplit; [|iSplit; [|iSplit]].
      - rewrite /unsusp_p_ser_spec.
        iIntros (v s Ψ) "!# Hser HΨ".
        iDestruct "Hser" as %(s' & -> & ->).
        rewrite /string_ser /string_ser_str. wp_pures. by iApply "HΨ".
      - rewrite /susp_p_ser_spec.
        iIntros (E a1 s c q HE Ψ) "!# ((Hstr & %Hc) & Htok & Hintr) HΨ".
        subst c. iDestruct "Hstr" as %(s' & -> & ->).
        rewrite /string_ser. wp_pures. iApply "HΨ". iModIntro. iFrame "Htok".
        iEval (rewrite -{1}(Qp.div_2 q) intransit_split) in "Hintr".
        iDestruct "Hintr" as "[$ _]".
        iIntros (γl) "Hg Hpen %Hsz Hbig".
        apply size_empty_inv in Hsz. fold_leibniz. subst γl.
        iFrame "Hg Hpen". by rewrite big_sepS_empty.
      - rewrite /suspend_spec_bin.
        iIntros (t' v un_v Ψ) "!# (%Hunsusp & HA) HΨ".
        rewrite /id. wp_pures.
        iDestruct "HA" as %(s' & ->).
        destruct t' eqn:Ht; simpl in Hunsusp; try done.
        + destruct Hunsusp as (?&?&?&?&Heq&_). discriminate.
        + destruct Hunsusp as [(?&?&Heq&_)|(?&?&Heq&_)]; discriminate.
        + subst un_v.
          iApply ("HΨ" $! #s' (string_ser_str s') 0). simpl.
          iModIntro. iSplit; [iPureIntro; by eexists|].
          iSplit; [|done]. iExists s'. done.
        + subst un_v.
          iApply ("HΨ" $! #s' (string_ser_str s') 0). simpl.
          iModIntro. iSplit; [iPureIntro; by eexists|].
          iSplit; [|done]. iExists s'. done.
        + destruct Hunsusp as (?&?&?&?&?&Heq&_). discriminate.
      - rewrite /unsuspend_spec_bin.
        iIntros (E a1 HE Ψ) "!# (HA & Htok) HΨ".
        rewrite /id. wp_pures. iApply ("HΨ" $! a1). iFrame "Htok". done. }
    (* ternary *)
    rewrite /lrel_tern_evidence /=.
    iExists tstring, _, _, _, _, _, _, _.
    iSplit; [done|]. iSplit; [done|].
    iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit]]]]].
    - (* 1. unsusp_p_ser_spec *)
      rewrite /unsusp_p_ser_spec.
      iIntros (vstr sstr Ψ) "!# Hser HΨ".
      iDestruct "Hser" as %(s' & -> & ->).
      rewrite /p_Auth_string /string_ser' /string_ser /string_ser_str.
      wp_pures.
      by iApply "HΨ".
    - (* 2. susp_p_ser_spec *)
      rewrite /susp_p_ser_spec.
      iIntros (E a1 s c q HE Ψ) "!# ((Hstr & %Hc) & Htok & Hintr) HΨ".
      subst c. iDestruct "Hstr" as %(s' & -> & ->).
      rewrite /string_ser. wp_pures.
      iApply "HΨ". iModIntro. iFrame "Htok".
      iEval (rewrite -{1}(Qp.div_2 q) intransit_split) in "Hintr".
      iDestruct "Hintr" as "[$ _]".
      iIntros (γl) "Hg Hpen %Hsz Hbig".
      apply size_empty_inv in Hsz. fold_leibniz. subst γl.
      iFrame "Hg Hpen". by rewrite big_sepS_empty.
    - (* 3. suspend_v_deser_spec (combined) *) admit.

    - (* 4. unsuspend_spec *)
      rewrite /unsuspend_spec.
      iIntros (E a1 a2 a3 HE Ψ) "!# (HA & Htok & Hintr) HΨ".
      iDestruct "HA" as "[>HAt _]". iSimpl in "HAt".
      iDestruct "HAt" as %(s0 & -> & -> & ->).
      rewrite /id. wp_pures.
      iApply ("HΨ" $! _ (string_ser_str s0)).
      iFrame. iModIntro. iSplit; [done|]. iExists s0. done.
    - (* 5. v_ser_spec *)
      rewrite /v_ser_spec.
      iIntros (K tᵥ a s id Nc v_outer) "!# Hcnt Hser Hspec".
      iDestruct "Hser" as %(s' & -> & ->).
      rewrite /string_ser' /string_ser. v_pures. iFrame.
      iModIntro. iExists s'. done.
    - (* 6. auth_ser_spec *)
      rewrite /auth_ser_spec.
      iIntros (K tᵥ a1 un_a1 a2 a3 s Ψ) "!# (%Hunsusp & HA & #Hser & Htok & Hv) HΨ".
      simpl in Hunsusp. subst un_a1.
      iEval (rewrite /lrel_tern_tern /lrel_string /=) in "HA".
      iDestruct "HA" as ">%H". destruct H as (s' & -> & -> & ->).
      iDestruct "Hser" as %(s'' & Heq & ->). injection Heq as <-.
      rewrite /string_ser' /string_ser /string_ser_str. v_pures. wp_pures.
      iApply "HΨ". iModIntro. iFrame "Htok Hv". iExists s'. done.
    - (* 7. v_count_spec *)
      rewrite /v_count_spec.
      iIntros (K tᵥ a c id Nc v_outer) "!# Hcnt Hspec".
      iDestruct "Hcnt" as "[Hvv %Hc]". subst c.
      rewrite /string_count /int_count. v_pures.
      iModIntro. iFrame. done.
  Admitted.

  Lemma refines_Auth_int :
    ⊢ (lrel_evidence) (LRelTern lrel_int lrel_un_int)
        p_Auth_int v_Auth_int i_Auth_int.
  Proof.
    iSplit; last first.
    { (* unary *)
      rewrite /lrel_evidence /lrel_evidence' /=. cbv [lrel_tern_un].
      rewrite /lrel_un_evidence /=.
      iExists tint, _, _, _, _, _, _, _.
      iSplit; [done|]. iSplit; [|iSplit; [|iSplit]].
      - rewrite /unsusp_p_ser_spec.
        iIntros (v s Ψ) "!# Hser HΨ".
        iDestruct "Hser" as %(z & -> & ->).
        rewrite /int_ser /int_ser_str. wp_pures. by iApply "HΨ".
      - rewrite /susp_p_ser_spec.
        iIntros (E a1 s c q HE Ψ) "!# ((Hint & %Hc) & Htok & Hintr) HΨ".
        subst c. iDestruct "Hint" as %(z & -> & ->).
        rewrite /int_ser. wp_pures. iApply "HΨ". iModIntro. iFrame "Htok".
        iEval (rewrite -{1}(Qp.div_2 q) intransit_split) in "Hintr".
        iDestruct "Hintr" as "[$ _]".
        iIntros (γl) "Hg Hpen %Hsz Hbig".
        apply size_empty_inv in Hsz. fold_leibniz. subst γl.
        iFrame "Hg Hpen". by rewrite big_sepS_empty.
      - rewrite /suspend_spec_bin.
        iIntros (t' v un_v Ψ) "!# (%Hunsusp & HA) HΨ".
        rewrite /id. wp_pures.
        iDestruct "HA" as %(z & ->).
        destruct t' eqn:Ht; simpl in Hunsusp; try done.
        + destruct Hunsusp as (?&?&?&?&Heq&_). discriminate.
        + destruct Hunsusp as [(?&?&Heq&_)|(?&?&Heq&_)]; discriminate.
        + subst un_v.
          iApply ("HΨ" $! #z (int_ser_str z) 0). simpl.
          iModIntro. iSplit; [iPureIntro; by eexists|].
          iSplit; [|done]. iExists z. done.
        + subst un_v.
          iApply ("HΨ" $! #z (int_ser_str z) 0). simpl.
          iModIntro. iSplit; [iPureIntro; by eexists|].
          iSplit; [|done]. iExists z. done.
        + destruct Hunsusp as (?&?&?&?&?&Heq&_). discriminate.
      - rewrite /unsuspend_spec_bin.
        iIntros (E a1 HE Ψ) "!# (HA & Htok) HΨ".
        rewrite /id. wp_pures. iApply ("HΨ" $! a1). iFrame "Htok". done. }
    (* ternary *)
    rewrite /lrel_tern_evidence /=.
    iExists tint, _, _, _, _, _, _, _.
    iSplit; [done|]. iSplit; [done|].
    iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit]]]]].
    - (* 1. unsusp_p_ser_spec *)
      rewrite /unsusp_p_ser_spec.
      iIntros (vint sint Ψ) "!# Hser HΨ".
      iDestruct "Hser" as %(z & -> & ->).
      rewrite /p_Auth_int /int_ser' /int_ser /int_ser_str.
      wp_pures.
      by iApply "HΨ".
    - (* 2. susp_p_ser_spec *)
      rewrite /susp_p_ser_spec.
      iIntros (E a1 s c q HE Ψ) "!# ((Hint & %Hc) & Htok & Hintr) HΨ".
      subst c. iDestruct "Hint" as %(z & -> & ->).
      rewrite /int_ser. wp_pures.
      iApply "HΨ". iModIntro. iFrame "Htok".
      iEval (rewrite -{1}(Qp.div_2 q) intransit_split) in "Hintr".
      iDestruct "Hintr" as "[$ _]".
      iIntros (γl) "Hg Hpen %Hsz Hbig".
      apply size_empty_inv in Hsz. fold_leibniz. subst γl.
      iFrame "Hg Hpen". by rewrite big_sepS_empty.
    - (* 3. suspend_v_deser_spec (combined) *) admit.

    - (* 4. unsuspend_spec *)
      rewrite /unsuspend_spec.
      iIntros (E a1 a2 a3 HE Ψ) "!# (HA & Htok & Hintr) HΨ".
      iDestruct "HA" as "[>HAt _]". iSimpl in "HAt".
      iDestruct "HAt" as %(z0 & -> & -> & ->).
      rewrite /id. wp_pures.
      iApply ("HΨ" $! _ (int_ser_str z0)).
      iFrame. iModIntro. iSplit; [done|]. iExists z0. done.
    - (* 5. v_ser_spec *)
      rewrite /v_ser_spec.
      iIntros (K tᵥ a s id Nc v_outer) "!# Hcnt Hser Hspec".
      iDestruct "Hser" as %(z' & -> & ->).
      rewrite /int_ser' /int_ser. v_pures. iFrame.
      iModIntro. iExists z'. done.
    - (* 6. auth_ser_spec *)
      rewrite /auth_ser_spec.
      iIntros (K tᵥ a1 un_a1 a2 a3 s Ψ) "!# (%Hunsusp & HA & #Hser & Htok & Hv) HΨ".
      simpl in Hunsusp. subst un_a1.
      iEval (rewrite /lrel_tern_tern /lrel_int /=) in "HA".
      iDestruct "HA" as ">%H". destruct H as (z' & -> & -> & ->).
      iDestruct "Hser" as %(z'' & Heq & ->). injection Heq as <-.
      rewrite /int_ser' /int_ser /int_ser_str. v_pures. wp_pures.
      iApply "HΨ". iModIntro. iFrame "Htok Hv". iExists z'. done.
    - (* 7. v_count_spec *)
      rewrite /v_count_spec.
      iIntros (K tᵥ a c id Nc v_outer) "!# Hcnt Hspec".
      iDestruct "Hcnt" as "[Hvv %Hc]". subst c.
      rewrite /int_count. v_pures.
      iModIntro. iFrame. done.
  Admitted.

  Lemma refines_Auth_mu Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆ ⇒ ⋆, var1 (var0 (μ: ⋆; var1 var0)) → var1 (μ: ⋆; var1 var0) ⟧
      (ext Δ (lrel_evidence)) p_Auth_mu v_Auth_mu i_Auth_mu.
  Proof.
    iSplit; interp_unfold!; last first.
    { (* unary *)
      iIntros (A v) "!# _ Htok". rewrite /p_Auth_mu. wp_pures.
      iModIntro. iFrame "Htok". interp_unfold!.
      iIntros (vA) "!# #HA". interp_unfold! in "HA".
      iEval (rewrite /lrel_un_evidence /=) in "HA".
      iDestruct "HA" as (tA p_ssA p_usA p_spA p_uspA pe1 pe2 pe3 ->) "#HrestA_un".
      iIntros "Htok". wp_pures. iModIntro. iFrame "Htok".
      interp_unfold!. rewrite /lrel_un_evidence /=.
      iDestruct "HrestA_un" as "(HusserA & HsserA & HspbA & HuspbA)".
      iExists tA, _, _, _, _, _, _, _.
      iSplit; [done|]. iSplit; [|iSplit; [|iSplit]].
      - rewrite /unsusp_p_ser_spec.
        iIntros (v0 s Ψ) "!# Hser HΨ". rewrite /rec_fold. wp_pures.
        wp_apply ("HusserA" with "Hser"). iIntros "_". by iApply "HΨ".
      - rewrite /susp_p_ser_spec.
        iIntros (E a1 s c q HE Ψ) "!# (Hser & Htok & Hintr) HΨ".
        rewrite /rec_fold. wp_pures.
        wp_apply ("HsserA" $! _ _ _ c q with "[//] [$Hser $Htok $Hintr]").
        iIntros "(Htok & Hintr & HreachA)". iApply "HΨ". iFrame.
      - rewrite /suspend_spec_bin.
        iIntros (t' v0 un_v Ψ) "!# (%Hunsusp & HA) HΨ".
        rewrite /rec_fold. wp_pures.
        iEval (rewrite interp_rec_star_un_unfold) in "HA". interp_unfold! in "HA".
        wp_apply ("HspbA" $! _ _ un_v with "[HA]").
        { iSplit; first by iPureIntro. iApply "HA". }
        iIntros (v' s c) "[HA Hreal]". iApply ("HΨ" $! v' s c).
        iSplit; [|by iFrame].
        rewrite interp_rec_star_un_unfold. interp_unfold!. iApply "HA".
      - rewrite /unsuspend_spec_bin.
        iIntros (E a1 HE Ψ) "!# (HA & Htok) HΨ".
        rewrite /rec_fold. wp_pures.
        iEval (rewrite interp_rec_star_un_unfold) in "HA". interp_unfold! in "HA".
        wp_apply ("HuspbA" with "[//] [$HA $Htok]").
        iIntros (un_v) "[Htok %Hunsusp]". iApply ("HΨ" $! un_v). by iFrame. }
    (* ternary *)
    iIntros (A v1 v2 v3) "!# _"; rewrite -/interp.
    iIntros (????) "Hv Hi Htok".
    rewrite /p_Auth_mu /v_Auth_mu /i_Auth_mu.
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame.
    iSplit; interp_unfold!; last first.
    { (* inner-after-A unary *)
      iIntros (vA) "!# #HA". interp_unfold! in "HA".
      iEval (rewrite /lrel_un_evidence /=) in "HA".
      iDestruct "HA" as (tA p_ssA p_usA p_spA p_uspA pe1 pe2 pe3 ->) "#HrestA_un".
      iIntros "Htok". wp_pures. iModIntro. iFrame "Htok".
      interp_unfold!. rewrite /lrel_un_evidence /=.
      iDestruct "HrestA_un" as "(HusserA & HsserA & HspbA & HuspbA)".
      iExists tA, _, _, _, _, _, _, _.
      iSplit; [done|]. iSplit; [|iSplit; [|iSplit]].
      - rewrite /unsusp_p_ser_spec.
        iIntros (v0 s Ψ) "!# Hser HΨ". rewrite /rec_fold. wp_pures.
        wp_apply ("HusserA" with "Hser"). iIntros "_". by iApply "HΨ".
      - rewrite /susp_p_ser_spec.
        iIntros (E a1 s c q HE Ψ) "!# (Hser & Htok & Hintr) HΨ".
        rewrite /rec_fold. wp_pures.
        wp_apply ("HsserA" $! _ _ _ c q with "[//] [$Hser $Htok $Hintr]").
        iIntros "(Htok & Hintr & HreachA)". iApply "HΨ". iFrame.
      - rewrite /suspend_spec_bin.
        iIntros (t' v0 un_v Ψ) "!# (%Hunsusp & HA) HΨ".
        rewrite /rec_fold. wp_pures.
        iEval (rewrite interp_rec_star_un_unfold) in "HA". interp_unfold! in "HA".
        wp_apply ("HspbA" $! _ _ un_v with "[HA]").
        { iSplit; first by iPureIntro. iApply "HA". }
        iIntros (v' s c) "[HA Hreal]". iApply ("HΨ" $! v' s c).
        iSplit; [|by iFrame].
        rewrite interp_rec_star_un_unfold. interp_unfold!. iApply "HA".
      - rewrite /unsuspend_spec_bin.
        iIntros (E a1 HE Ψ) "!# (HA & Htok) HΨ".
        rewrite /rec_fold. wp_pures.
        iEval (rewrite interp_rec_star_un_unfold) in "HA". interp_unfold! in "HA".
        wp_apply ("HuspbA" with "[//] [$HA $Htok]").
        iIntros (un_v) "[Htok %Hunsusp]". iApply ("HΨ" $! un_v). by iFrame. }
    iIntros (vA1 vA2 vA3) "!# #HA".
    interp_unfold! in "HA".
    iDestruct "HA" as "(HA_tern & #HA_un)".
    iDestruct "HA_tern" as (tA p_ssA p_usA p_spA p_uspA v_sA v_dA v_cA -> ->) "HrestA".
    iIntros (????) "Hv Hi Htok". v_pures; i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iSplit; interp_unfold!; last first.
    { (* final unary *)
      iEval (rewrite /lrel_un_evidence /=) in "HA_un".
      iDestruct "HA_un" as (tA' p_ssA' p_usA' p_spA' p_uspA' pe1 pe2 pe3 Heqp) "#HrestA_un".
      injection Heqp as <- <- <- <-.
      interp_unfold!. rewrite /lrel_un_evidence /=.
      iDestruct "HrestA_un" as "(HusserA' & HsserA' & HspbA' & HuspbA')".
      iExists tA', _, _, _, _, _, _, _.
      iSplit; [done|]. iSplit; [|iSplit; [|iSplit]].
      - rewrite /unsusp_p_ser_spec.
        iIntros (v0 s Ψ) "!# Hser HΨ". rewrite /rec_fold. wp_pures.
        wp_apply ("HusserA'" with "Hser"). iIntros "_". by iApply "HΨ".
      - rewrite /susp_p_ser_spec.
        iIntros (E a1 s c q HE Ψ) "!# (Hser & Htok & Hintr) HΨ".
        rewrite /rec_fold. wp_pures.
        wp_apply ("HsserA'" $! _ _ _ c q with "[//] [$Hser $Htok $Hintr]").
        iIntros "(Htok & Hintr & HreachA)". iApply "HΨ". iFrame.
      - rewrite /suspend_spec_bin.
        iIntros (t' v0 un_v Ψ) "!# (%Hunsusp & HA) HΨ".
        rewrite /rec_fold. wp_pures.
        iEval (rewrite interp_rec_star_un_unfold) in "HA". interp_unfold! in "HA".
        wp_apply ("HspbA'" $! _ _ un_v with "[HA]").
        { iSplit; first by iPureIntro. iApply "HA". }
        iIntros (v' s c) "[HA Hreal]". iApply ("HΨ" $! v' s c).
        iSplit; [|by iFrame].
        rewrite interp_rec_star_un_unfold. interp_unfold!. iApply "HA".
      - rewrite /unsuspend_spec_bin.
        iIntros (E a1 HE Ψ) "!# (HA & Htok) HΨ".
        rewrite /rec_fold. wp_pures.
        iEval (rewrite interp_rec_star_un_unfold) in "HA". interp_unfold! in "HA".
        wp_apply ("HuspbA'" with "[//] [$HA $Htok]").
        iIntros (un_v) "[Htok %Hunsusp]". iApply ("HΨ" $! un_v). by iFrame. }
    iExists tA, _, _, _, _, _, _, _.
    iSplit; [done|]. iSplit; [done|].
    iDestruct "HrestA" as "(HusserA & HsserA & HsuspvdeserA & HunsuspA & HvserA & HvauthserA & HvcountA)".
    iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit]]]]].
    - (* 1. unsusp_p_ser_spec *)
      rewrite /unsusp_p_ser_spec.
      iIntros (vmu smu Ψ) "!# Hser HΨ".
      rewrite /rec_fold. wp_pures.
      wp_apply ("HusserA" with "Hser"). iIntros "_".
      by iApply "HΨ".
    - (* 2. susp_p_ser_spec *)
      rewrite /susp_p_ser_spec.
      iIntros (E a1 s c q HE Ψ) "!# (Hser & Htok & Hintr) HΨ".
      rewrite /rec_fold. wp_pures.
      wp_apply ("HsserA" $! _ _ _ c q with "[//] [$Hser $Htok $Hintr]").
      iIntros "(Htok & Hintr & HreachA)".
      iApply "HΨ". iFrame.
    - (* 3. suspend_v_deser_spec (combined) *) admit.

    - (* 4. unsuspend_spec *)
      rewrite /unsuspend_spec.
      iIntros (E a1 a2 a3 HE Ψ) "!# (#HA & Htok & Hintr) HΨ".
      rewrite /rec_fold. wp_pures.
      iEval (rewrite interp_rec_star_unfold) in "HA".
      interp_unfold! in "HA".
      wp_apply ("HunsuspA" with "[//] [$Htok $HA $Hintr]").
      iIntros (un_v s) "(Htok & Hintr & %Hunsusp & #Hser)".
      iApply ("HΨ" $! un_v s). iFrame. iFrame "#". done.
    - (* 5. v_ser_spec *)
      rewrite /v_ser_spec.
      iIntros (K tᵥ1 a s id Nc v_outer) "!# Hcnt Hser Hspec".
      v_pures.
      by iApply ("HvserA" with "Hcnt Hser Hspec").
    - (* 6. auth_ser_spec — the prover's [rec_fold] step mints the later
         credit that pays for the [interp_rec_star_tern_unfold] ▷. *)
      rewrite /auth_ser_spec.
      iIntros (K tᵥ1 a1 un_a1 a2 a3 s Ψ) "!# (%Hunsusp & HA & #Hser & Htok & Hv) HΨ".
      v_pures.
      rewrite /rec_fold. wp_pure credit:"Hlc". wp_pures.
      iEval (rewrite interp_rec_star_tern_unfold) in "HA".
      iMod (lc_fupd_elim_later with "Hlc HA") as "HA".
      interp_unfold! in "HA".
      wp_apply ("HvauthserA" with "[HA Htok Hv]").
      { by iFrame "HA Hser Htok Hv". }
      iIntros "(Htok & Hsv & Hv)".
      iApply "HΨ". by iFrame.
    - (* 7. v_count_spec *)
      rewrite /v_count_spec.
      iIntros (K tᵥ1 a c id Nc v_outer) "!# Hcnt Hspec".
      v_pures.
      by iApply ("HvcountA" with "Hcnt Hspec").
  Admitted.

  (* Definition auth_p_fill (a v : val) (s : string) (t : evi_type) : iProp Σ :=
    ⌜v = (a, #(hash s))%V⌝ ∨
    (∃ (lb lr : loc) (ps : proph_id),
      ⌜v = (#ps, #lb, #lr, a, #(hash s))%V⌝ ∗
      seq_inv (suspFill N ps) 
        (∃ (b r : bool), lb ↦ #b ∗ lb ↦ #r ∗ proph_p_susp ps false ∗
          ⌜(b = true ∧ r = true) ∨ (b = false)⌝)).

  Definition auth_v_fill (v : val) (s : string) : iProp Σ :=
    ⌜v = InjLV #(hash s1)⌝.

  Definition auth_p_unfill (a v : val) (s : string) (t : evi_type) : iProp Σ :=
    ∃ (lb lr : loc) (ps : proph_id),
      ⌜v = (#ps, #lb, #lr, a, #(hash s))%V⌝ ∗
      seq_inv (suspFill N ps)  
        (∃ (r : bool), lb ↦ #r ∗
          ((lb ↦ #false ∗ proph_p_susp ps true) ∨ (∃ b, lb ↦ #true ∗ proph_p_susp ps b))).

  Definition auth_v_unfill (v : val) (s : string) : iProp Σ :=
    (∃ (s' : string) (susp : loc),
      ⌜v = InjRV #susp⌝ ∗
      ⌜s' = some_ser_str (string_ser_str (hash s))⌝ ∗
      seq_inv (authN N susp)
        (auth_inv s' susp)). *)

  Definition auth_ctx {Θ} (Δ : ctxO Σ Θ) (R : kindO Σ (⋆ ⇒ ⋆)) :=
    ext (ext (ext Δ (lrel_auth)) R) (lrel_evidence).

  Lemma refines_Auth_auth Θ (Δ : ctxO Σ Θ) (R : kindO Σ (⋆ ⇒ ⋆)) :
    ⊢ ⟦ ∀: ⋆, var1 (var3 var0) ⟧
      (auth_ctx Δ R) p_Auth_auth v_Auth_auth i_Auth_auth.
  Proof.

  Admitted.

  Lemma refines_auth_auth Θ (Δ : ctxO Σ Θ) (R : kindO Σ (⋆ ⇒ ⋆)) :
    ⊢ ⟦ ∀: ⋆, var1 var0 → var0 → var3 var0 ⟧
      (auth_ctx Δ R) p_auth v_auth i_auth.
  Proof.
    (* iIntros (????) "!# _"; rewrite -/interp.
    iIntros (????) "Hv Hi".
    rewrite /p_auth /v_auth  /i_auth.
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iIntros (???) "!#"; rewrite -!/interp /=.
    iDestruct 1 as (t ??? -> ->) "#Hser".

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
  Qed. *)
  Admitted.

End authenticatable.