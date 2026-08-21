From auth.prelude Require Import stdpp.
From auth.rel_logic_tern_susp Require Import model interp spec_tactics.
From iris.algebra Require Import gset auth.
From auth.examples Require Import authentikit authenticatable_base_susp.
From auth.examples.susp_correctness Require Export definitions helpers.

Section authenticatable.
  Context `{!authG Σ, !seqG Σ, !correctnessG Σ}.

  Local Typeclasses Opaque susp_p_ser_spec unsusp_p_ser_spec suspend_v_deser_spec
        unsuspend_spec v_ser_spec auth_ser_spec v_count_spec.

  Lemma refines_Auth_pair Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆; ⋆, var2 var1 → var2 var0 → var2 (var1 * var0) ⟧
      (ext Δ (lrel_evidence)) p_Auth_pair v_Auth_pair i_Auth_pair.
  Proof.
    iSplit; interp_unfold!; last first.
    { (* unary  *) admit. }
    (* ternary *)
    iIntros (A v1 v2 v3) "!# _"; rewrite -/interp.
    iIntros (????) "Hv Hi Htok".
    rewrite /p_Auth_pair /v_Auth_pair /i_Auth_pair.
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
    rewrite /prod_ser'' /prod_ser /prod_count.
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame.
    (* Final 3-way split: prove only the ternary [lrel_tern_evidence]. *)
    iSplit; interp_unfold!; last first.
    { (* final unary  *) admit. }
    (* Ternary evidence for the product. *)
    iExists (tprod tA tB), _, _, _, _, _, _, _.
    iSplit; [done|]. iSplit; [done|].
    (* Now destruct HrestA/HrestB for use in bullets — keep as SPATIAL
       (no [#] markers).  Each hypothesis's body is semantically
       persistent ([□(...)]), but introducing them as spatial keeps them
       out of Iris's intuitionistic-env traversal which is what the
       [Typeclasses Opaque] dance was previously avoiding. *)
    iDestruct "HrestA" as "(HusserA & HsserA & HsuspvdeserA & HunsuspA & HvserA & HvauthserA & HvcountA)".
    iDestruct "HrestB" as "(HusserB & HsserB & HsuspvdeserB & HunsuspB & HvserB & HvauthserB & HvcountB)".
    iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit]]]]].
    - (* 1. unsusp_p_ser_spec *)
      rewrite /unsusp_p_ser_spec.
      iIntros (v s Ψ) "!# Hser HΨ".
      iDestruct "Hser" as (a1 a2 sa sb [-> ->]) "[Hussera Husserb]".
      wp_pures.
      wp_apply ("HusserA" with "Hussera"). iIntros "_". wp_pures.
      wp_apply ("HusserB" with "Husserb"). iIntros "_". wp_pures.
      unfold prod_ser_str. iApply "HΨ". by iModIntro.
    - (* 2. susp_p_ser_spec — restored from e9c0029^ with
         lg_mapg_frag → lg_mapg_p_frag and the not-loc case analyses
         factored into helpers.susp_ser_p_real_not_loc. *)
      rewrite /susp_p_ser_spec.
      iIntros (E a1 s c q HE Ψ) "!# (Hser & Htok & Hintr) HΨ".
      iEval (rewrite /susp_ser_p_real /=) in "Hser".
      iDestruct "Hser" as (c1 c2 ->) "Hser_pair".
      iDestruct "Hser_pair" as (ua ub sa sb [-> ->]) "[#Hser1 #Hser2]".
      iEval (rewrite -{1}(Qp.div_2 q) intransit_split) in "Hintr".
      iDestruct "Hintr" as "[HintrA HintrB]".
      rewrite /prod_ser''. wp_pures. rewrite /prod_ser. wp_pures.
      wp_apply ("HsserA" $! _ _ _ c1 (q/2)%Qp with "[//] [$Hser1 $Htok $HintrA]").
      iIntros "(Htok & HintrA' & HreachA)". wp_pures.
      wp_apply ("HsserB" $! _ _ _ c2 (q/2)%Qp with "[//] [$Hser2 $Htok $HintrB]").
      iIntros "(Htok & HintrB' & HreachB)". wp_pures.
      unfold prod_ser_str. iApply "HΨ". iModIntro. iFrame "Htok".
      iCombine "HintrA' HintrB'" as "Hcomb".
      replace ((q/2)/2 + (q/2)/2)%Qp with (q/2)%Qp by (symmetry; apply Qp.div_2).
      iFrame "Hcomb".
      iIntros (γl) "Hg Hpen %Hsz Hbig".
      iDestruct (susp_ser_p_real_not_loc with "Hser1") as %Hua_not_loc.
      iDestruct (susp_ser_p_real_not_loc with "Hser2") as %Hub_not_loc.
      (* Build the partition by induction on γl. Stash Hsz outside the IH. *)
      assert (size γl = c1 + c2)%nat as Hsz_keep by exact Hsz. clear Hsz.
      iAssert (∃ γlA γlB : gset gname,
                 ⌜γlA ## γlB ∧ γl = γlA ∪ γlB⌝ ∗
                 ([∗ set] γ ∈ γlA, ∃ lb, lg_mapg_p_frag lb γ ∗ ⌜p_sub_obj tA ua #lb⌝) ∗
                 ([∗ set] γ ∈ γlB, ∃ lb, lg_mapg_p_frag lb γ ∗ ⌜p_sub_obj tB ub #lb⌝))%I
        with "[Hbig]"
        as "(%γlA & %γlB & [%HdisjAB %HsplitAB] & HbigA & HbigB)".
      { clear Hsz_keep.
        iRevert "Hbig".
        iInduction γl as [|γ γl' Hnotin] "IHγl" using set_ind_L.
        - iIntros "_". iExists ∅, ∅. rewrite !big_sepS_empty.
          iSplit; [iPureIntro; set_solver|]. by iSplit.
        - iIntros "Hbig".
          iEval (rewrite big_sepS_insert; [|done]) in "Hbig".
          iDestruct "Hbig" as "[(%lb_γ & #Hfrag_γ & %Hsub_γ) Hbig']".
          iDestruct ("IHγl" with "Hbig'")
            as "(%γlA' & %γlB' & [%Hdisj' %Hsplit'] & HA' & HB')".
          destruct Hsub_γ as (x & y & Heq & Hdisj_p).
          injection Heq as -> ->.
          destruct Hdisj_p as [Heq | [Heq | [Hsub | Hsub]]].
          + exfalso. by apply (Hua_not_loc lb_γ).
          + exfalso. by apply (Hub_not_loc lb_γ).
          + iExists ({[γ]} ∪ γlA'), γlB'.
            iSplit; [iPureIntro; split; [|set_solver]|].
            { assert (γ ∉ γlA') by set_solver. set_solver. }
            iSplitL "HA'".
            * rewrite big_sepS_insert; [|set_solver].
              iSplitL ""; [iExists lb_γ; by iFrame "Hfrag_γ"|done].
            * done.
          + iExists γlA', ({[γ]} ∪ γlB').
            iSplit; [iPureIntro; split; [|set_solver]|].
            { assert (γ ∉ γlB') by set_solver. set_solver. }
            iSplitL "HA'"; [done|].
            rewrite big_sepS_insert; [|set_solver].
            iSplitL ""; [iExists lb_γ; by iFrame "Hfrag_γ"|done]. }
      (* Bounds on |γlA| ≤ c1, |γlB| ≤ c2 via susp_ser_p_real_γl_card_le *)
      iDestruct (susp_ser_p_real_γl_card_le with "Hser1 HbigA") as %HszA_le.
      iDestruct (susp_ser_p_real_γl_card_le with "Hser2 HbigB") as %HszB_le.
      assert (size γlA + size γlB = c1 + c2) as Hsz_sum.
      { rewrite HsplitAB in Hsz_keep.
        by rewrite (size_union _ _ HdisjAB) in Hsz_keep. }
      assert (size γlA = c1) as HszA by lia.
      assert (size γlB = c2) as HszB by lia.
      (* Split penset_frag γl into penset_frag γlA ∗ penset_frag γlB *)
      iAssert (penset_frag γlA ∗ penset_frag γlB)%I with "[Hpen]" as "[HpenA HpenB]".
      { rewrite /penset_frag.
        replace (◯ GSet γl) with (◯ GSet γlA ⋅ ◯ GSet γlB).
        - rewrite own_op. by iDestruct "Hpen" as "[$ $]".
        - rewrite -auth_frag_op gset_disj_union //. by rewrite -HsplitAB. }
      iSpecialize ("HreachA" $! γlA with "Hg HpenA [//] HbigA").
      iDestruct "HreachA" as "(Hg & HpenA & HbigA')".
      iSpecialize ("HreachB" $! γlB with "Hg HpenB [//] HbigB").
      iDestruct "HreachB" as "(Hg & HpenB & HbigB')".
      iFrame "Hg".
      iAssert (penset_frag (γlA ∪ γlB)) with "[HpenA HpenB]" as "Hpen".
      { rewrite /penset_frag -gset_disj_union //.
        rewrite auth_frag_op own_op. iSplitL "HpenA"; [iExact "HpenA"|iExact "HpenB"]. }
      rewrite -HsplitAB. iFrame "Hpen".
      rewrite HsplitAB.
      rewrite (big_sepS_union _ _ _ HdisjAB).
      iSplitL "HbigA'".
      { iApply (big_sepS_mono with "HbigA'").
        iIntros (γ' ?) "[Hreach Hlb]". iFrame "Hreach".
        iDestruct "Hlb" as (lb) "[Hlg %Hp]". iExists lb. iFrame "Hlg".
        iPureIntro. simpl. exists ua, ub. split; [done|].
        right. right. left. done. }
      iApply (big_sepS_mono with "HbigB'").
      iIntros (γ' ?) "[Hreach Hlb]". iFrame "Hreach".
      iDestruct "Hlb" as (lb) "[Hlg %Hp]". iExists lb. iFrame "Hlg".
      iPureIntro. simpl. exists ua, ub. split; [done|].
      right. right. right. done.

    - (* 3. suspend_v_deser_spec (combined) *) admit.

    - (* 4. unsuspend_spec — re-derived without the deleted binary
         projection, mirroring sum's case 4 via interp_prod_combined. *)
      rewrite /unsuspend_spec.
      iIntros (E a1 a2 a3 HE Ψ) "!# (HA & Htok & Hintr) HΨ".
      iEval (rewrite interp_prod_combined) in "HA".
      wp_pures.
      iDestruct "HA" as (wa1 wa2 wb1 wb2 wc1 wc2) "(-> & -> & -> & HA & HB)".
      wp_pures.
      interp_unfold! in "HA". interp_unfold! in "HB".
      wp_bind (p_uspB _).
      wp_apply ("HunsuspB" with "[//] [$HB $Htok $Hintr]").
      iIntros (un_vb sb) "(Htok & Hintr & %Hunsuspb & #Hserb)".
      wp_bind (p_uspA _).
      wp_apply ("HunsuspA" with "[//] [$HA $Htok $Hintr]").
      iIntros (un_va sa) "(Htok & Hintr & %Hunsuspa & #Hsera)".
      wp_pures. iApply ("HΨ" $! (un_va, un_vb)%V (prod_ser_str sa sb)).
      iFrame. iModIntro. iSplit.
      { iPureIntro. eexists _, _, un_va, un_vb. done. }
      iExists un_va, un_vb, sa, sb. iSplit; [done|]. iFrame "#".

    - (* 5. v_ser_spec *)
      rewrite /v_ser_spec.
      iIntros (K tᵥ3 a s id Nc v_outer) "!# Hcnt Hser Hspec".
      iDestruct "Hcnt" as (c1 c2 pv1 pv2 [-> Hsum]) "[Hcnt1 Hcnt2]".
      iDestruct "Hser" as (? ? s1 s2 [Heqv ->]) "[Hser1 Hser2]".
      injection Heqv as -> ->.
      assert (c1 = 0%nat) as -> by lia.
      assert (c2 = 0%nat) as -> by lia.
      v_pures.
      v_bind tᵥ3 (v_sA _).
      iMod ("HvserA" with "Hcnt1 Hser1 Hspec") as "(Hcnt1 & Hser1 & Hspec) /=".
      v_pures.
      v_bind tᵥ3 (v_sB _).
      iMod ("HvserB" with "Hcnt2 Hser2 Hspec") as "(Hcnt2 & Hser2 & Hspec) /=".
      simpl. v_pures.
      iModIntro. iFrame "Hspec". rewrite /prod_ser_str.
      iSplitL "Hcnt1 Hcnt2".
      { iExists 0%nat, 0%nat, _, _. iFrame. iPureIntro. done. }
      iExists _, _, s1, s2. iFrame "Hser1 Hser2". iPureIntro. done.
    - (* 6. auth_ser_spec *)
      rewrite /auth_ser_spec.
      iIntros (K tᵥ3 a1 un_a1 a2 a3 s Ψ) "!# (%Hunsusp & HA & #Hser & Htok & Hv) HΨ".
      destruct Hunsusp as (x1 & x2 & un1 & un2 & -> & -> & Hun1 & Hun2).
      iDestruct "Hser" as (w1 w2 s1 s2 [Heq ->]) "[#Hser1 #Hser2]".
      injection Heq as <- <-.
      rewrite /prod_ser''. v_pures.
      interp_unfold! in "HA".
      iDestruct "HA" as (xa1 xa2 xb1 xb2 xc1 xc2) "(>%Heqa & >-> & >-> & Ha & Hb)".
      injection Heqa as <- <-.
      rewrite /prod_ser. wp_pures.
      v_pures. v_bind (v_sA _).
      wp_apply ("HvauthserA" with "[Ha Htok Hv]").
      { by iFrame "Ha Hser1 Htok Hv". }
      iIntros "(Htok & Hsva & Hv) /=".
      v_pures. v_bind (v_sB _).
      wp_pures.
      wp_apply ("HvauthserB" with "[Hb Htok Hv]").
      { by iFrame "Hb Hser2 Htok Hv". }
      iIntros "(Htok & Hsvb & Hv) /=".
      v_pures. wp_pures.
      iApply "HΨ". iModIntro.
      unfold prod_ser_str. iFrame "Htok Hv".
      iExists _, _, s1, s2. iFrame "Hsva Hsvb". done.
    - (* 7. v_count_spec *)
      rewrite /v_count_spec.
      iIntros (K tᵥ3 a c id Nc v_outer) "!# Hcnt Hspec".
      iDestruct "Hcnt" as (c1 c2 pv1 pv2 [-> Hsum]) "[Hcnt1 Hcnt2]".
      v_pures.
      v_bind tᵥ3 (v_cB pv2).
      iMod ("HvcountB" with "Hcnt2 Hspec") as "[Hcnt2 Hspec]".
      v_bind tᵥ3 (v_cA _).
      v_pures.
      v_bind tᵥ3 (v_cA _).
      iMod ("HvcountA" with "Hcnt1 Hspec") as "[Hcnt1 Hspec]".
      simpl. v_pures.
      assert ((c1 + c2)%Z = c) as -> by lia.
      iModIntro. iFrame.
      iPureIntro. split; [reflexivity|lia].
  Admitted.

End authenticatable.
