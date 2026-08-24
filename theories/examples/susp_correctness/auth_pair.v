From auth.prelude Require Import stdpp.
From auth.rel_logic_tern_susp Require Import model interp spec_tactics.
From iris.algebra Require Import gset auth.
From auth.examples Require Import authentikit authenticatable_base_susp.
From auth.examples.susp_correctness Require Export definitions helpers.

Section authenticatable.
  Context `{!authG Σ, !seqG Σ, !correctnessG Σ}.

  Local Typeclasses Opaque susp_p_ser_spec unsusp_p_ser_spec suspend_v_deser_spec
        unsuspend_spec v_ser_spec auth_ser_spec v_count_spec.

  (** Pure parse facts about [prod_ser_str], mirroring
      [prod_deser'_sound]/[_complete]. *)
  Local Lemma prod_ser_str_index s1 s2 :
    String.index 0 "_" (prod_ser_str s1 s2)
    = Some (String.length (StringOfZ (String.length s1))).
  Proof.
    rewrite /prod_ser_str.
    eapply index_0_append_char; [done|apply valid_tag_stringOfZ].
  Qed.

  Local Lemma prod_ser_str_prefix s1 s2 :
    String.substring 0 (String.length (StringOfZ (String.length s1)))
      (prod_ser_str s1 s2)
    = StringOfZ (String.length s1).
  Proof. rewrite /prod_ser_str substring_0_length_append //. Qed.

  Local Lemma prod_ser_str_length s1 s2 :
    String.length (prod_ser_str s1 s2)
    = (String.length (StringOfZ (String.length s1)) + 1
       + String.length s1 + String.length s2)%nat.
  Proof. rewrite /prod_ser_str !strings.length_app /=. lia. Qed.

  Local Lemma prod_ser_str_sub1 s1 s2 :
    String.substring (String.length (StringOfZ (String.length s1)) + 1)
      (String.length s1) (prod_ser_str s1 s2) = s1.
  Proof.
    rewrite /prod_ser_str substring_add_length_app /=.
    apply substring_0_length_append.
  Qed.

  Local Lemma prod_ser_str_sub2 s1 s2 :
    String.substring
      (String.length (StringOfZ (String.length s1)) + 1 + String.length s1)
      (String.length s2) (prod_ser_str s1 s2) = s2.
  Proof.
    rewrite /prod_ser_str.
    replace (String.length (StringOfZ (String.length s1)) + 1
             + String.length s1)%nat
      with (String.length (StringOfZ (String.length s1))
            + (1 + String.length s1))%nat by lia.
    rewrite substring_add_length_app /=.
    rewrite -{1}(Nat.add_0_r (String.length s1)) substring_add_length_app.
    apply substring_0_length.
  Qed.

  (** Pair-level [susp_p_ser_spec_at] from the components': runs the two
      component serializations and splits the reachability closure's
      pending set by the partition argument (as in the evidence lemmas'
      case 2). Shared by all arms of the pair's [suspend_v_deser_spec]. *)
  Lemma pair_susp_p_ser_spec_at (tA tB : evi_type) (ssA ssB : val)
      (cA cB : nat) (aA aB : val) (sA sB : string) :
    susp_ser_p_real tA cA aA sA -∗
    susp_ser_p_real tB cB aB sB -∗
    susp_p_ser_spec_at ssA tA cA aA sA -∗
    susp_p_ser_spec_at ssB tB cB aB sB -∗
    susp_p_ser_spec_at
      (λ: "v",
         let: "s1" := ssA (Fst "v") in
         let: "s2" := ssB (Snd "v") in z2s (strlen "s1") ^ #"_" ^ "s1" ^ "s2")%V
      (tprod tA tB) (cA + cB) (aA, aB)%V (prod_ser_str sA sB).
  Proof.
    iIntros "#Hser1 #Hser2 #HatA #HatB".
    rewrite /susp_p_ser_spec_at.
    iIntros (E q HE Ψ) "!# (Htok & Hintr) HΨ".
    iEval (rewrite -{1}(Qp.div_2 q) intransit_split) in "Hintr".
    iDestruct "Hintr" as "[HintrA HintrB]".
    wp_pures.
    wp_apply ("HatA" $! E (q/2)%Qp with "[//] [$Htok $HintrA]").
    iIntros "(Htok & HintrA' & HreachA)". wp_pures.
    wp_apply ("HatB" $! E (q/2)%Qp with "[//] [$Htok $HintrB]").
    iIntros "(Htok & HintrB' & HreachB)". wp_pures.
    unfold prod_ser_str. iApply "HΨ". iModIntro. iFrame "Htok".
    iCombine "HintrA' HintrB'" as "Hcomb".
    replace ((q/2)/2 + (q/2)/2)%Qp with (q/2)%Qp by (symmetry; apply Qp.div_2).
    iFrame "Hcomb".
    iIntros (γl) "Hg Hpen %Hsz Hbig".
    iDestruct (susp_ser_p_real_not_loc with "Hser1") as %Hua_not_loc.
    iDestruct (susp_ser_p_real_not_loc with "Hser2") as %Hub_not_loc.
    assert (size γl = cA + cB)%nat as Hsz_keep by exact Hsz. clear Hsz.
    iAssert (∃ γlA γlB : gset gname,
               ⌜γlA ## γlB ∧ γl = γlA ∪ γlB⌝ ∗
               ([∗ set] γ ∈ γlA, ∃ lb, lg_mapg_p_frag lb γ ∗ ⌜p_sub_obj tA aA #lb⌝) ∗
               ([∗ set] γ ∈ γlB, ∃ lb, lg_mapg_p_frag lb γ ∗ ⌜p_sub_obj tB aB #lb⌝))%I
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
    iDestruct (susp_ser_p_real_γl_card_le with "Hser1 HbigA") as %HszA_le.
    iDestruct (susp_ser_p_real_γl_card_le with "Hser2 HbigB") as %HszB_le.
    assert (size γlA + size γlB = cA + cB) as Hsz_sum.
    { rewrite HsplitAB in Hsz_keep.
      by rewrite (size_union _ _ HdisjAB) in Hsz_keep. }
    assert (size γlA = cA) as HszA by lia.
    assert (size γlB = cB) as HszB by lia.
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
      iPureIntro. simpl. exists aA, aB. split; [done|].
      right. right. left. done. }
    iApply (big_sepS_mono with "HbigB'").
    iIntros (γ' ?) "[Hreach Hlb]". iFrame "Hreach".
    iDestruct "Hlb" as (lb) "[Hlg %Hp]". iExists lb. iFrame "Hlg".
    iPureIntro. simpl. exists aA, aB. split; [done|].
    right. right. right. done.
  Qed.

  (** Unary (prover-only) evidence for the product; discharges every
      tern/un split in [refines_Auth_pair]. Mirrors
      [refines_un_Auth_sum] in base_correctness.v. *)
  Lemma refines_un_Auth_pair Θ (Δ : ctxO Σ Θ) (A B : kindO Σ ⋆)
      (p_ssA p_usA p_spA p_uspA p_ssB p_usB p_spB p_uspB : val) :
    lrel_tern_un (lrel_evidence A) (p_ssA, p_usA, p_spA, p_uspA)%V -∗
    lrel_tern_un (lrel_evidence B) (p_ssB, p_usB, p_spB, p_uspB)%V -∗
    lrel_tern_un
      (lrel_evidence (⟦ var1 * var0 ⟧ (ext (ext (ext Δ lrel_evidence) A) B)))
      (λ: "v",
         let: "s1" := p_ssA (Fst "v") in
         let: "s2" := p_ssB (Snd "v") in z2s (strlen "s1") ^ #"_" ^ "s1" ^ "s2",
       λ: "v",
         let: "s1" := p_usA (Fst "v") in
         let: "s2" := p_usB (Snd "v") in z2s (strlen "s1") ^ #"_" ^ "s1" ^ "s2",
       λ: "a",
         let: "b" := "a" in
         let: "a" := Fst "b" in
         let: "b" := Snd "b" in
         let: "ra" := p_spA "a" in let: "rb" := p_spB "b" in ("ra", "rb"),
       λ: "a",
         let: "b" := "a" in
         let: "a" := Fst "b" in let: "b" := Snd "b" in
         (p_uspA "a", p_uspB "b"))%V.
  Proof.
    iIntros "#HA_un #HB_un".
    iEval (rewrite /lrel_evidence /lrel_evidence' /lrel_un_evidence /=) in "HA_un".
    iDestruct "HA_un" as (tA ssA usA spA uspA eA1 eA2 eA3)
      "(%HeqA & #HusserA & #HsserA & #HspbA & #HuspbA)".
    injection HeqA as <- <- <- <-.
    iEval (rewrite /lrel_evidence /lrel_evidence' /lrel_un_evidence /=) in "HB_un".
    iDestruct "HB_un" as (tB ssB usB spB uspB eB1 eB2 eB3)
      "(%HeqB & #HusserB & #HsserB & #HspbB & #HuspbB)".
    injection HeqB as <- <- <- <-.
    iEval (rewrite /lrel_evidence /lrel_evidence' /lrel_un_evidence /=).
    iExists (tprod tA tB), _, _, _, _, #(), #(), #().
    iSplit; [done|]. iSplit; [|iSplit; [|iSplit]].
    - (* unsusp_p_ser_spec *)
      rewrite /unsusp_p_ser_spec.
      iIntros (v s Ψ) "!# Hser HΨ".
      iDestruct "Hser" as (a1 a2 sa sb [-> ->]) "[Hussera Husserb]".
      wp_pures.
      wp_apply ("HusserA" with "Hussera"). iIntros "_". wp_pures.
      wp_apply ("HusserB" with "Husserb"). iIntros "_". wp_pures.
      unfold prod_ser_str. iApply "HΨ". by iModIntro.
    - (* susp_p_ser_spec — same partition argument as the ternary case 2 *)
      rewrite /susp_p_ser_spec.
      iIntros (E a1 s c q HE Ψ) "!# (Hser & Htok & Hintr) HΨ".
      iEval (rewrite /susp_ser_p_real /=) in "Hser".
      iDestruct "Hser" as (c1 c2 ->) "Hser_pair".
      iDestruct "Hser_pair" as (ua ub sa sb [-> ->]) "[#Hser1 #Hser2]".
      iEval (rewrite -{1}(Qp.div_2 q) intransit_split) in "Hintr".
      iDestruct "Hintr" as "[HintrA HintrB]".
      wp_pures.
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
      iDestruct (susp_ser_p_real_γl_card_le with "Hser1 HbigA") as %HszA_le.
      iDestruct (susp_ser_p_real_γl_card_le with "Hser2 HbigB") as %HszB_le.
      assert (size γlA + size γlB = c1 + c2) as Hsz_sum.
      { rewrite HsplitAB in Hsz_keep.
        by rewrite (size_union _ _ HdisjAB) in Hsz_keep. }
      assert (size γlA = c1) as HszA by lia.
      assert (size γlB = c2) as HszB by lia.
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
    - (* suspend_spec_bin *)
      rewrite /suspend_spec_bin.
      iIntros (t' v0 un_v s_def Ψ) "!# (%Hunsusp & #Hsw & HA) HΨ".
      rewrite interp_un_prod_unfold interp_var1_ext2 interp_var0_ext1.
      iDestruct "HA" as (w1 w2) "(>-> & HAw & HBw)".
      destruct t'; simpl in Hunsusp.
      + (* tprod *)
        destruct Hunsusp as (x1&x2&un1&un2&Heq&->&Hu1&Hu2).
        injection Heq as <- <-.
        iDestruct "Hsw" as (w1' w2' sw1 sw2 [Heqw _]) "[#Hsw1 #Hsw2]".
        injection Heqw as <- <-.
        wp_pures.
        wp_apply ("HspbA" $! _ _ un1 _ with "[HAw]").
        { iSplit; [by iPureIntro|]. iFrame "Hsw1". iApply "HAw". }
        iIntros (v1' s1 c1) "[HA' Hreal1]". wp_pures.
        wp_apply ("HspbB" $! _ _ un2 _ with "[HBw]").
        { iSplit; [by iPureIntro|]. iFrame "Hsw2". iApply "HBw". }
        iIntros (v2' s2 c2) "[HB' Hreal2]". wp_pures.
        iApply ("HΨ" $! (v1', v2')%V (prod_ser_str s1 s2) (c1 + c2)%nat).
        iSplitL "HA' HB'".
        { iExists v1', v2'. iModIntro. iSplit; [done|].
          iSplitL "HA'"; [iApply "HA'"|iApply "HB'"]. }
        simpl. iExists c1, c2. iModIntro. iSplit; [done|].
        iExists v1', v2', s1, s2. iSplit; [done|]. iFrame.
      + (* tsum: v0 is a pair — contradiction *)
        destruct Hunsusp as [(?&?&Hx&_)|(?&?&Hx&_)]; simplify_eq.
      + (* tstring: witness forces a tstring-shaped value — contradiction with a pair *)
        iDestruct "Hsw" as %(? & Heqv & _). simplify_eq.
      + (* tint: witness forces a tint-shaped value — contradiction with a pair *)
        iDestruct "Hsw" as %(? & Heqv & _). simplify_eq.
      + (* tauth: v0 is a Box — contradiction *)
        destruct Hunsusp as (?&?&?&?&?&Hx&_). simplify_eq.
    - (* unsuspend_spec_bin *)
      rewrite /unsuspend_spec_bin.
      iIntros (E a1 HE Ψ) "!# (HA & Htok) HΨ".
      rewrite interp_un_prod_unfold interp_var1_ext2 interp_var0_ext1.
      iDestruct "HA" as (w1 w2) "(>-> & HAw & HBw)".
      wp_pures.
      wp_apply ("HuspbB" with "[//] [$HBw $Htok]").
      iIntros (un2) "[Htok %Hu2]".
      wp_apply ("HuspbA" with "[//] [$HAw $Htok]").
      iIntros (un1) "[Htok %Hu1]".
      wp_pures. iApply ("HΨ" $! (un1, un2)%V). iFrame "Htok".
      iPureIntro. simpl. by exists w1, w2, un1, un2.
  Qed.

  Lemma refines_Auth_pair Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆; ⋆, var2 var1 → var2 var0 → var2 (var1 * var0) ⟧
      (ext Δ (lrel_evidence)) p_Auth_pair v_Auth_pair i_Auth_pair.
  Proof.
    iSplit; interp_unfold!; last first.
    { (* unary  *)
      iIntros (A' vA0) "!# _ Htok". rewrite /p_Auth_pair. wp_pures.
      iModIntro. iFrame "Htok". interp_unfold!.
      iIntros (B' vB0) "!# _ Htok". wp_pures.
      iModIntro. iFrame "Htok". interp_unfold!.
      iIntros (vA') "!# #HA' Htok".
      iPoseProof "HA'" as "HA0". interp_unfold! in "HA0".
      iEval (rewrite /lrel_evidence /lrel_evidence' /lrel_un_evidence /=) in "HA0".
      iDestruct "HA0" as (? ? ? ? ? ? ? ?) "[%HeqA' _]". subst vA'.
      wp_pures. iModIntro. iFrame "Htok". interp_unfold!.
      iIntros (vB') "!# #HB' Htok".
      iPoseProof "HB'" as "HB0". interp_unfold! in "HB0".
      iEval (rewrite /lrel_evidence /lrel_evidence' /lrel_un_evidence /=) in "HB0".
      iDestruct "HB0" as (? ? ? ? ? ? ? ?) "[%HeqB' _]". subst vB'.
      rewrite /prod_ser. wp_pures. iModIntro. iFrame "Htok". interp_unfold!.
      interp_unfold! in "HA'". interp_unfold! in "HB'".
      iApply (refines_un_Auth_pair with "HA' HB'"). }
    (* ternary *)
    iIntros (A v1 v2 v3) "!# _"; rewrite -/interp.
    iIntros (????) "Hv Hi Htok".
    rewrite /p_Auth_pair /v_Auth_pair /i_Auth_pair.
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iSplit; interp_unfold!; last first.
    { (* inner-after-A unary *)
      iIntros (B' vB0) "!# _ Htok". wp_pures.
      iModIntro. iFrame "Htok". interp_unfold!.
      iIntros (vA') "!# #HA' Htok".
      iPoseProof "HA'" as "HA0". interp_unfold! in "HA0".
      iEval (rewrite /lrel_evidence /lrel_evidence' /lrel_un_evidence /=) in "HA0".
      iDestruct "HA0" as (? ? ? ? ? ? ? ?) "[%HeqA' _]". subst vA'.
      wp_pures. iModIntro. iFrame "Htok". interp_unfold!.
      iIntros (vB') "!# #HB' Htok".
      iPoseProof "HB'" as "HB0". interp_unfold! in "HB0".
      iEval (rewrite /lrel_evidence /lrel_evidence' /lrel_un_evidence /=) in "HB0".
      iDestruct "HB0" as (? ? ? ? ? ? ? ?) "[%HeqB' _]". subst vB'.
      rewrite /prod_ser. wp_pures. iModIntro. iFrame "Htok". interp_unfold!.
      interp_unfold! in "HA'". interp_unfold! in "HB'".
      iApply (refines_un_Auth_pair with "HA' HB'"). }
    iIntros (B w1 w2 w3) "!# _"; rewrite -/interp.
    iIntros (????) "Hv Hi Htok". v_pures; i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iSplit; interp_unfold!; last first.
    { (* inner-after-B unary *)
      iIntros (vA') "!# #HA' Htok".
      iPoseProof "HA'" as "HA0". interp_unfold! in "HA0".
      iEval (rewrite /lrel_evidence /lrel_evidence' /lrel_un_evidence /=) in "HA0".
      iDestruct "HA0" as (? ? ? ? ? ? ? ?) "[%HeqA' _]". subst vA'.
      wp_pures. iModIntro. iFrame "Htok". interp_unfold!.
      iIntros (vB') "!# #HB' Htok".
      iPoseProof "HB'" as "HB0". interp_unfold! in "HB0".
      iEval (rewrite /lrel_evidence /lrel_evidence' /lrel_un_evidence /=) in "HB0".
      iDestruct "HB0" as (? ? ? ? ? ? ? ?) "[%HeqB' _]". subst vB'.
      rewrite /prod_ser. wp_pures. iModIntro. iFrame "Htok". interp_unfold!.
      interp_unfold! in "HA'". interp_unfold! in "HB'".
      iApply (refines_un_Auth_pair with "HA' HB'"). }
    iIntros (vA1 vA2 vA3) "!# #HA".
    interp_unfold! in "HA".
    iDestruct "HA" as "(HA_tern & #HA_un)".
    iDestruct "HA_tern" as (tA p_ssA p_usA p_spA p_uspA v_sA v_dA v_cA -> ->) "#HrestA".
    fold v_ser_spec.
    iIntros (????) "Hv Hi Htok". v_pures; i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iSplit; interp_unfold!; last first.
    { (* inner-after-HA unary *)
      iIntros (vB') "!# #HB' Htok".
      iPoseProof "HB'" as "HB0". interp_unfold! in "HB0".
      iEval (rewrite /lrel_evidence /lrel_evidence' /lrel_un_evidence /=) in "HB0".
      iDestruct "HB0" as (? ? ? ? ? ? ? ?) "[%HeqB' _]". subst vB'.
      rewrite /prod_ser. wp_pures. iModIntro. iFrame "Htok". interp_unfold!.
      interp_unfold! in "HB'".
      iApply (refines_un_Auth_pair with "HA_un HB'"). }
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
    { (* final unary  *) iApply (refines_un_Auth_pair with "HA_un HB_un"). }
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

    - (* 3. suspend_v_deser_spec (combined) *)
      rewrite /suspend_v_deser_spec.
      iIntros "!#" (K tᵥ3 pid) "Hv".
      v_pures.
      v_bind (v_dB _).
      iMod ("HsuspvdeserB" with "Hv") as (v_parB) "(Hv & #HinnerB) /=".
      v_bind (v_dA _).
      iMod ("HsuspvdeserA" with "Hv") as (v_parA) "(Hv & #HinnerA) /=".
      rewrite /prod_deser. v_pures.
      iModIntro. iExists _. iFrame "Hv".
      iIntros "!#" (t' a1 un_a1 a2 a3 s_def s_pred s_reg vm mp pn ctr mlg_p K' tᵥ' Ψ).
      iIntros "!# (%Hunsusp & #HA & #Hser & #Hserpred & Hvm & Hlgp & Hpenc & Hv) HΨ".
      wp_pure _.
      iPoseProof "HA" as "HA'".
      iEval (rewrite interp_prod_combined) in "HA'".
      iDestruct "HA'" as (wa1 wa2 wb1 wb2 wc1 wc2) "(-> & -> & -> & HAc & HBc)".
      destruct t' as [t1' t2'|t1' t2'| | |]; simpl in Hunsusp; first last.
      { destruct Hunsusp as (?&?&?&?&?&Heq&_). simplify_eq. }
      { iDestruct "Hser" as %(z & Heq & _). simplify_eq. }
      { iDestruct "Hser" as %(s' & Heq & _). simplify_eq. }
      { destruct Hunsusp as [(?&?&Heq&_)|(?&?&Heq&_)]; simplify_eq. }
      destruct Hunsusp as (x & y & un_x & un_y & Heq & -> & Hunx & Huny).
      simplify_eq.
      iDestruct "Hser" as (v1 v2 s1_def s2_def [Heqv Heqs]) "[#HserA' #HserB']".
      simplify_eq.
      wp_pures. wp_bind (p_spA _).
      interp_unfold! in "HAc". interp_unfold! in "HBc".
      v_pures; try solve_vals_compare_safe.
      (* the verifier's parse of the abstract s_pred *)
      destruct (String.index (Z.to_nat 0) "_" s_pred) as [i|] eqn:Hidx; last first.
      { iSimpl in "Hv". v_pures.
        iPoseProof "HA_un" as "HAu".
        iEval (rewrite /lrel_evidence /lrel_evidence' /lrel_un_evidence /=)
          in "HAu".
        iDestruct "HAu" as (tAu ssAu usAu spAu uspAu ? ? ?)
          "(%HeqAu & _ & #HsserAu & #HspbAu & _)".
        injection HeqAu as <- <- <- <-.
        iPoseProof "HB_un" as "HBu".
        iEval (rewrite /lrel_evidence /lrel_evidence' /lrel_un_evidence /=)
          in "HBu".
        iDestruct "HBu" as (tBu ssBu usBu spBu uspBu ? ? ?)
          "(%HeqBu & _ & #HsserBu & #HspbBu & _)".
        injection HeqBu as <- <- <- <-.
        iDestruct "HAc" as "[_ HAcun]".
        wp_apply ("HspbAu" $! t1' _ _ with "[HAcun]").
        { iSplit; [done|]. iSplit; [iApply "HserA'"|]. iApply "HAcun". }
        iIntros (a1A' sA cA) "[HAun' #HrealA']".
        wp_pures. wp_bind (p_spB _).
        iDestruct "HBc" as "[_ HBcun]".
        wp_apply ("HspbBu" $! t2' _ _ with "[HBcun]").
        { iSplit; [done|]. iSplit; [iApply "HserB'"|]. iApply "HBcun". }
        iIntros (a1B' sB cB) "[HBun' #HrealB']".
        wp_pures.
        iApply ("HΨ" $! (a1A', a1B')%V (prod_ser_str sA sB) (cA + cB)
                  (tprod tAu tBu)).
        iModIntro.
        iPoseProof (susp_p_ser_spec_at_intro with "HrealA' HsserAu") as "#HatA'".
        iPoseProof (susp_p_ser_spec_at_intro with "HrealB' HsserBu") as "#HatB'".
        iSplitR.
        { iApply (pair_susp_p_ser_spec_at with "HrealA' HrealB' HatA' HatB'"). }
        iSplitR.
        { iExists cA, cB. iSplit; [done|].
          iExists a1A', a1B', sA, sB. iSplit; [done|].
          iSplitR; [iApply "HrealA'"|iApply "HrealB'"]. }
        iFrame "Hserpred".
        iRight. iSplit.
        { iPureIntro. intros ->.
          replace (Z.to_nat 0) with 0%nat in Hidx by done.
          rewrite prod_ser_str_index in Hidx. done. }
        rewrite interp_un_prod_unfold. iExists a1A', a1B'. iSplit; [done|].
        iSplitL "HAun'".
        - interp_unfold!. iApply "HAun'".
        - interp_unfold!. iApply "HBun'". }
      iSimpl in "Hv". v_pures.
      destruct (ZOfString (String.substring (Z.to_nat 0) (Z.to_nat i) s_pred))
        as [Alen|] eqn:HAlen; last first.
      { iSimpl in "Hv". v_pures.
        iPoseProof "HA_un" as "HAu".
        iEval (rewrite /lrel_evidence /lrel_evidence' /lrel_un_evidence /=)
          in "HAu".
        iDestruct "HAu" as (tAu ssAu usAu spAu uspAu ? ? ?)
          "(%HeqAu & _ & #HsserAu & #HspbAu & _)".
        injection HeqAu as <- <- <- <-.
        iPoseProof "HB_un" as "HBu".
        iEval (rewrite /lrel_evidence /lrel_evidence' /lrel_un_evidence /=)
          in "HBu".
        iDestruct "HBu" as (tBu ssBu usBu spBu uspBu ? ? ?)
          "(%HeqBu & _ & #HsserBu & #HspbBu & _)".
        injection HeqBu as <- <- <- <-.
        iDestruct "HAc" as "[_ HAcun]".
        wp_apply ("HspbAu" $! t1' _ _ with "[HAcun]").
        { iSplit; [done|]. iSplit; [iApply "HserA'"|]. iApply "HAcun". }
        iIntros (a1A' sA cA) "[HAun' #HrealA']".
        wp_pures. wp_bind (p_spB _).
        iDestruct "HBc" as "[_ HBcun]".
        wp_apply ("HspbBu" $! t2' _ _ with "[HBcun]").
        { iSplit; [done|]. iSplit; [iApply "HserB'"|]. iApply "HBcun". }
        iIntros (a1B' sB cB) "[HBun' #HrealB']".
        wp_pures.
        iApply ("HΨ" $! (a1A', a1B')%V (prod_ser_str sA sB) (cA + cB)
                  (tprod tAu tBu)).
        iModIntro.
        iPoseProof (susp_p_ser_spec_at_intro with "HrealA' HsserAu") as "#HatA'".
        iPoseProof (susp_p_ser_spec_at_intro with "HrealB' HsserBu") as "#HatB'".
        iSplitR.
        { iApply (pair_susp_p_ser_spec_at with "HrealA' HrealB' HatA' HatB'"). }
        iSplitR.
        { iExists cA, cB. iSplit; [done|].
          iExists a1A', a1B', sA, sB. iSplit; [done|].
          iSplitR; [iApply "HrealA'"|iApply "HrealB'"]. }
        iFrame "Hserpred".
        iRight. iSplit.
        { iPureIntro. intros ->.
          replace (Z.to_nat 0) with 0%nat in Hidx by done.
          rewrite prod_ser_str_index in Hidx. injection Hidx as <-.
          replace (Z.to_nat 0) with 0%nat in HAlen by done.
          rewrite Nat2Z.id in HAlen.
          rewrite prod_ser_str_prefix in HAlen.
          rewrite ZOfString_inv in HAlen. done. }
        rewrite interp_un_prod_unfold. iExists a1A', a1B'. iSplit; [done|].
        iSplitL "HAun'".
        - interp_unfold!. iApply "HAun'".
        - interp_unfold!. iApply "HBun'". }
      iSimpl in "Hv". v_pures; try solve_vals_compare_safe.
      destruct (decide (StringOfZ Alen
                        = String.substring (Z.to_nat 0) (Z.to_nat i) s_pred))
        as [Hecho|Hecho]; last first.
      { assert (¬ ((#(StringOfZ Alen) : val)
                   = #(String.substring (Z.to_nat 0) (Z.to_nat i) s_pred)))
          as Hvne.
        { intros Heq. apply Hecho. by injection Heq. }
        iEval (rewrite (bool_decide_eq_false_2 _ Hvne) /=) in "Hv".
        v_pures.
        iPoseProof "HA_un" as "HAu".
        iEval (rewrite /lrel_evidence /lrel_evidence' /lrel_un_evidence /=)
          in "HAu".
        iDestruct "HAu" as (tAu ssAu usAu spAu uspAu ? ? ?)
          "(%HeqAu & _ & #HsserAu & #HspbAu & _)".
        injection HeqAu as <- <- <- <-.
        iPoseProof "HB_un" as "HBu".
        iEval (rewrite /lrel_evidence /lrel_evidence' /lrel_un_evidence /=)
          in "HBu".
        iDestruct "HBu" as (tBu ssBu usBu spBu uspBu ? ? ?)
          "(%HeqBu & _ & #HsserBu & #HspbBu & _)".
        injection HeqBu as <- <- <- <-.
        iDestruct "HAc" as "[_ HAcun]".
        wp_apply ("HspbAu" $! t1' _ _ with "[HAcun]").
        { iSplit; [done|]. iSplit; [iApply "HserA'"|]. iApply "HAcun". }
        iIntros (a1A' sA cA) "[HAun' #HrealA']".
        wp_pures. wp_bind (p_spB _).
        iDestruct "HBc" as "[_ HBcun]".
        wp_apply ("HspbBu" $! t2' _ _ with "[HBcun]").
        { iSplit; [done|]. iSplit; [iApply "HserB'"|]. iApply "HBcun". }
        iIntros (a1B' sB cB) "[HBun' #HrealB']".
        wp_pures.
        iApply ("HΨ" $! (a1A', a1B')%V (prod_ser_str sA sB) (cA + cB)
                  (tprod tAu tBu)).
        iModIntro.
        iPoseProof (susp_p_ser_spec_at_intro with "HrealA' HsserAu") as "#HatA'".
        iPoseProof (susp_p_ser_spec_at_intro with "HrealB' HsserBu") as "#HatB'".
        iSplitR.
        { iApply (pair_susp_p_ser_spec_at with "HrealA' HrealB' HatA' HatB'"). }
        iSplitR.
        { iExists cA, cB. iSplit; [done|].
          iExists a1A', a1B', sA, sB. iSplit; [done|].
          iSplitR; [iApply "HrealA'"|iApply "HrealB'"]. }
        iFrame "Hserpred".
        iRight. iSplit.
        { iPureIntro. intros ->.
          replace (Z.to_nat 0) with 0%nat in Hidx by done.
          rewrite prod_ser_str_index in Hidx. injection Hidx as <-.
          replace (Z.to_nat 0) with 0%nat in HAlen by done.
          rewrite Nat2Z.id in HAlen.
          rewrite prod_ser_str_prefix in HAlen.
          rewrite ZOfString_inv in HAlen. injection HAlen as <-.
          replace (Z.to_nat 0) with 0%nat in Hecho by done.
          apply Hecho. rewrite Nat2Z.id prod_ser_str_prefix. done. }
        rewrite interp_un_prod_unfold. iExists a1A', a1B'. iSplit; [done|].
        iSplitL "HAun'".
        - interp_unfold!. iApply "HAun'".
        - interp_unfold!. iApply "HBun'". }
      assert ((#(StringOfZ Alen) : val)
              = #(String.substring (Z.to_nat 0) (Z.to_nat i) s_pred)) as Hveq
        by (by rewrite Hecho).
      iEval (rewrite (bool_decide_eq_true_2 _ Hveq) /=) in "Hv".
      v_pures.
      case_bool_decide as Hsign; v_pures.
      { iPoseProof "HA_un" as "HAu".
        iEval (rewrite /lrel_evidence /lrel_evidence' /lrel_un_evidence /=)
          in "HAu".
        iDestruct "HAu" as (tAu ssAu usAu spAu uspAu ? ? ?)
          "(%HeqAu & _ & #HsserAu & #HspbAu & _)".
        injection HeqAu as <- <- <- <-.
        iPoseProof "HB_un" as "HBu".
        iEval (rewrite /lrel_evidence /lrel_evidence' /lrel_un_evidence /=)
          in "HBu".
        iDestruct "HBu" as (tBu ssBu usBu spBu uspBu ? ? ?)
          "(%HeqBu & _ & #HsserBu & #HspbBu & _)".
        injection HeqBu as <- <- <- <-.
        iDestruct "HAc" as "[_ HAcun]".
        wp_apply ("HspbAu" $! t1' _ _ with "[HAcun]").
        { iSplit; [done|]. iSplit; [iApply "HserA'"|]. iApply "HAcun". }
        iIntros (a1A' sA cA) "[HAun' #HrealA']".
        wp_pures. wp_bind (p_spB _).
        iDestruct "HBc" as "[_ HBcun]".
        wp_apply ("HspbBu" $! t2' _ _ with "[HBcun]").
        { iSplit; [done|]. iSplit; [iApply "HserB'"|]. iApply "HBcun". }
        iIntros (a1B' sB cB) "[HBun' #HrealB']".
        wp_pures.
        iApply ("HΨ" $! (a1A', a1B')%V (prod_ser_str sA sB) (cA + cB)
                  (tprod tAu tBu)).
        iModIntro.
        iPoseProof (susp_p_ser_spec_at_intro with "HrealA' HsserAu") as "#HatA'".
        iPoseProof (susp_p_ser_spec_at_intro with "HrealB' HsserBu") as "#HatB'".
        iSplitR.
        { iApply (pair_susp_p_ser_spec_at with "HrealA' HrealB' HatA' HatB'"). }
        iSplitR.
        { iExists cA, cB. iSplit; [done|].
          iExists a1A', a1B', sA, sB. iSplit; [done|].
          iSplitR; [iApply "HrealA'"|iApply "HrealB'"]. }
        iFrame "Hserpred".
        iRight. iSplit.
        { iPureIntro. intros ->.
          replace (Z.to_nat 0) with 0%nat in Hidx by done.
          rewrite prod_ser_str_index in Hidx. injection Hidx as <-.
          replace (Z.to_nat 0) with 0%nat in HAlen by done.
          rewrite Nat2Z.id in HAlen.
          rewrite prod_ser_str_prefix in HAlen.
          rewrite ZOfString_inv in HAlen. injection HAlen as <-.
          lia. }
        rewrite interp_un_prod_unfold. iExists a1A', a1B'. iSplit; [done|].
        iSplitL "HAun'".
        - interp_unfold!. iApply "HAun'".
        - interp_unfold!. iApply "HBun'". }
      case_bool_decide as Hbound; v_pures.
      { iPoseProof "HA_un" as "HAu".
        iEval (rewrite /lrel_evidence /lrel_evidence' /lrel_un_evidence /=)
          in "HAu".
        iDestruct "HAu" as (tAu ssAu usAu spAu uspAu ? ? ?)
          "(%HeqAu & _ & #HsserAu & #HspbAu & _)".
        injection HeqAu as <- <- <- <-.
        iPoseProof "HB_un" as "HBu".
        iEval (rewrite /lrel_evidence /lrel_evidence' /lrel_un_evidence /=)
          in "HBu".
        iDestruct "HBu" as (tBu ssBu usBu spBu uspBu ? ? ?)
          "(%HeqBu & _ & #HsserBu & #HspbBu & _)".
        injection HeqBu as <- <- <- <-.
        iDestruct "HAc" as "[_ HAcun]".
        wp_apply ("HspbAu" $! t1' _ _ with "[HAcun]").
        { iSplit; [done|]. iSplit; [iApply "HserA'"|]. iApply "HAcun". }
        iIntros (a1A' sA cA) "[HAun' #HrealA']".
        wp_pures. wp_bind (p_spB _).
        iDestruct "HBc" as "[_ HBcun]".
        wp_apply ("HspbBu" $! t2' _ _ with "[HBcun]").
        { iSplit; [done|]. iSplit; [iApply "HserB'"|]. iApply "HBcun". }
        iIntros (a1B' sB cB) "[HBun' #HrealB']".
        wp_pures.
        iApply ("HΨ" $! (a1A', a1B')%V (prod_ser_str sA sB) (cA + cB)
                  (tprod tAu tBu)).
        iModIntro.
        iPoseProof (susp_p_ser_spec_at_intro with "HrealA' HsserAu") as "#HatA'".
        iPoseProof (susp_p_ser_spec_at_intro with "HrealB' HsserBu") as "#HatB'".
        iSplitR.
        { iApply (pair_susp_p_ser_spec_at with "HrealA' HrealB' HatA' HatB'"). }
        iSplitR.
        { iExists cA, cB. iSplit; [done|].
          iExists a1A', a1B', sA, sB. iSplit; [done|].
          iSplitR; [iApply "HrealA'"|iApply "HrealB'"]. }
        iFrame "Hserpred".
        iRight. iSplit.
        { iPureIntro. intros ->.
          replace (Z.to_nat 0) with 0%nat in Hidx by done.
          rewrite prod_ser_str_index in Hidx. injection Hidx as <-.
          replace (Z.to_nat 0) with 0%nat in HAlen by done.
          rewrite Nat2Z.id in HAlen.
          rewrite prod_ser_str_prefix in HAlen.
          rewrite ZOfString_inv in HAlen. injection HAlen as <-.
          rewrite prod_ser_str_length in Hbound. lia. }
        rewrite interp_un_prod_unfold. iExists a1A', a1B'. iSplit; [done|].
        iSplitL "HAun'".
        - interp_unfold!. iApply "HAun'".
        - interp_unfold!. iApply "HBun'". }
      (* coupled path: verifier at deserA s1 *)
      v_bind (v_parA _).
      wp_apply ("HinnerA" with "[$HAc $HserA' $Hserpred $Hvm $Hlgp $Hpenc $Hv]").
      { done. }
      iIntros (a1A' s_realA cA t_realA) "(#HspecatA & #HrealA & _ & HpostA)".
      iDestruct "HpostA" as "[HmatchA | [%HnmA #HunA]]"; last first.
      { (* A mismatched: the pair mismatches on the s1 slice; B still runs
           prover-only via the unary evidence. *)
        wp_pures. wp_bind (p_spB _).
        iPoseProof "HB_un" as "HBu".
        iEval (rewrite /lrel_evidence /lrel_evidence' /lrel_un_evidence /=)
          in "HBu".
        iDestruct "HBu" as (tBu ssBu usBu spBu uspBu ? ? ?)
          "(%HeqBu & _ & #HsserBu & #HspbBu & _)".
        injection HeqBu as <- <- <- <-.
        iDestruct "HBc" as "[_ HBcun]".
        wp_apply ("HspbBu" $! t2' _ _ with "[HBcun]").
        { iSplit; [done|]. iSplit; [iApply "HserB'"|]. iApply "HBcun". }
        iIntros (a1B' sB cB) "[HBun' #HrealB']".
        wp_pures.
        iApply ("HΨ" $! (a1A', a1B')%V (prod_ser_str s_realA sB) (cA + cB)
                  (tprod t_realA tBu)).
        iModIntro.
        iPoseProof (susp_p_ser_spec_at_intro with "HrealB' HsserBu") as "#HatB'".
        iSplitR.
        { iApply (pair_susp_p_ser_spec_at with "HrealA HrealB' HspecatA HatB'"). }
        iSplitR.
        { iExists cA, cB. iSplit; [done|].
          iExists a1A', a1B', s_realA, sB. iSplit; [done|].
          iSplitR; [iApply "HrealA"|iApply "HrealB'"]. }
        iFrame "Hserpred".
        iRight. iSplit.
        { iPureIntro. intros ->.
          replace (Z.to_nat 0) with 0%nat in Hidx by done.
          rewrite prod_ser_str_index in Hidx. injection Hidx as <-.
          replace (Z.to_nat 0) with 0%nat in HAlen by done.
          rewrite Nat2Z.id in HAlen.
          rewrite prod_ser_str_prefix in HAlen.
          rewrite ZOfString_inv in HAlen. injection HAlen as <-.
          apply HnmA.
          etrans; [|apply (prod_ser_str_sub1 s_realA sB)].
          f_equal; lia. }
        rewrite interp_un_prod_unfold. iExists a1A', a1B'. iSplit; [done|].
        iSplitR.
        - interp_unfold!. iDestruct "HunA" as "HunAc". iApply "HunAc".
        - interp_unfold!. iApply "HBun'". }
      iDestruct "HmatchA" as "([%HspA %HtA] & #HunA1' & %γlA & %mlgA & %a2A' &
          HlgpA & %HszA & HpensA & #HpserpA2 & Hv & HbigA & HpencA & HvmA & HwandA)".
      destruct cA as [|cA'']; last first.
      { admit. (* cA > 0: needs the wand generalized over v_outer —
                  composition TODO, not a design exclusion. *) }
      apply size_empty_inv in HszA. fold_leibniz. subst γlA.
      wp_pures. wp_bind (p_spB _).
      iEval (rewrite /visited_map_update_pending set_fold_empty size_empty
               Nat.add_0_r) in "HvmA".
      iSimpl in "Hv". v_pures.
      v_bind (v_parB _).
      wp_apply ("HinnerB" with "[$HBc $HserB' $Hserpred $HvmA $HlgpA $HpencA $Hv]").
      { done. }
      iIntros (a1B' s_realB cB t_realB) "(#HspecatB & #HrealB & _ & HpostB)".
      iDestruct "HpostB" as "[HmatchB | [%HnmB #HunB]]"; last first.
      { (* B mismatched after A matched — pair mismatch via the s2 slice. *)
        wp_pures.
        iApply ("HΨ" $! (a1A', a1B')%V (prod_ser_str s_realA s_realB)
                  (0 + cB)%nat (tprod t_realA t_realB)).
        iModIntro.
        iSplitR.
        { iApply (pair_susp_p_ser_spec_at _ _ _ _ 0 cB
                    with "HrealA HrealB HspecatA HspecatB"). }
        iSplitR.
        { iExists 0, cB. iSplit; [done|].
          iExists a1A', a1B', s_realA, s_realB. iSplit; [done|].
          iSplitR; [iApply "HrealA"|iApply "HrealB"]. }
        iFrame "Hserpred".
        iRight. iSplit.
        { iPureIntro. intros ->.
          replace (Z.to_nat 0) with 0%nat in Hidx by done.
          rewrite prod_ser_str_index in Hidx. injection Hidx as <-.
          replace (Z.to_nat 0) with 0%nat in HAlen by done.
          rewrite Nat2Z.id in HAlen.
          rewrite prod_ser_str_prefix in HAlen.
          rewrite ZOfString_inv in HAlen. injection HAlen as <-.
          apply HnmB.
          etrans; [|apply (prod_ser_str_sub2 s_realA s_realB)].
          rewrite prod_ser_str_length.
          f_equal; lia. }
        rewrite interp_un_prod_unfold. iExists a1A', a1B'. iSplit; [done|].
        iSplitR.
        - interp_unfold!. iDestruct "HunA1'" as "HunA1c". iApply "HunA1c".
        - interp_unfold!. iDestruct "HunB" as "HunBc". iApply "HunBc". }
      iDestruct "HmatchB" as "([%HspB %HtB] & #HunB1' & %γlB & %mlgB & %a2B' &
          HlgpB & %HszB & HpensB & #HpserpB2 & Hv & HbigB & HpencB & HvmB & HwandB)".
      destruct cB as [|cB'']; last first.
      { admit. (* cB > 0 — composition TODO. *) }
      apply size_empty_inv in HszB. fold_leibniz. subst γlB.
      subst t_realA t_realB.
      wp_pures.
      iSimpl in "Hv". v_pures.
      iApply ("HΨ" $! (a1A', a1B')%V (prod_ser_str s_realA s_realB) 0
                (tprod tA tB)).
      iModIntro.
      iSplitR.
      { iApply (pair_susp_p_ser_spec_at _ _ _ _ 0 0
                  with "HrealA HrealB HspecatA HspecatB"). }
      iSplitR.
      { iExists 0, 0. iSplit; [done|].
        iExists a1A', a1B', s_realA, s_realB. iSplit; [done|].
        iSplitR; [iApply "HrealA"|iApply "HrealB"]. }
      iFrame "Hserpred".
      iLeft. iSplit.
      { iPureIntro. split; last done.
        replace (Z.to_nat 0) with 0%nat in Hidx by done.
        apply Znot_lt_ge in Hsign.
        apply Znot_lt_ge in Hbound.
        replace (Z.to_nat 0) with 0%nat in Hecho by done.
        rewrite Nat2Z.id in Hecho.
        assert (String.length
                  (String.substring (Z.to_nat (i + 1)) (Z.to_nat Alen) s_pred)
                = Z.to_nat Alen) as HlenA.
        { apply length_substring. lia. }
        rewrite -HspA -HspB /prod_ser_str HlenA.
        replace (Z.of_nat (Z.to_nat Alen)) with Alen by lia.
        rewrite Hecho.
        pose proof (String.index_correct1 _ _ _ _ Hidx) as Hus.
        simpl in Hus. rewrite -Hus.
        replace (Z.to_nat (i + 1)) with (i + 1)%nat by lia.
        replace (Z.to_nat (i + 1 + Alen)) with (i + 1 + Z.to_nat Alen)%nat
          by lia.
        replace (Z.to_nat (String.length s_pred - (i + 1 + Alen)))
          with (String.length s_pred - (i + 1) - Z.to_nat Alen)%nat by lia.
        rewrite -(substring_split (Z.to_nat Alen) s_pred
                    (String.length s_pred - (i + 1)) (i + 1)); [|lia].
        replace (String.length s_pred - (i + 1))%nat
          with (String.length s_pred - i - 1)%nat by lia.
        rewrite -(substring_split 1 s_pred (String.length s_pred - i) i);
          [|lia].
        apply substring_split_from_O. lia. }
      iSplitR.
      { rewrite interp_un_prod_unfold. iExists a1A', a1B'. iSplit; [done|].
        iSplitR.
        - interp_unfold!. iDestruct "HunA1'" as "HunA1c". iApply "HunA1c".
        - interp_unfold!. iDestruct "HunB1'" as "HunB1c". iApply "HunB1c". }
      iExists ∅, mlgB, (a2A', a2B')%V.
      iFrame "HlgpB Hv".
      iSplit; [by rewrite size_empty|].
      iSplitL "HpensA"; [by iFrame "HpensA"|].
      iSplit.
      { iExists a1A', a1B', s1_def, s2_def. iSplit; [done|].
        iSplitR; [iApply "HpserpA2"|iApply "HpserpB2"]. }
      iSplit. { by rewrite big_sepS_empty. }
      iSplitL "HpencB"; [by iFrame "HpencB"|].
      iEval (rewrite /visited_map_update_pending set_fold_empty size_empty
               Nat.add_0_r) in "HvmB".
      rewrite /visited_map_update_pending set_fold_empty size_empty Nat.add_0_r.
      iFrame "HvmB".
      (* the pair wand: compose both component wands; the shared cap_frag is
         persistent, and at c = 0 both frag inputs are emp *)
      iIntros "#Hcap _ _ #Hmint".
      iMod ("HwandA" with "Hcap [//] [//] Hmint") as "(HAf & HcntA & HservA)".
      iMod ("HwandB" with "Hcap [//] [//] Hmint") as "(HBf & HcntB & HservB)".
      iModIntro.
      iSplitL "HAf HBf".
      { iEval (rewrite interp_prod_combined).
        iExists a1A', a1B', a2A', a2B', wc1, wc2.
        do 3 (iSplit; [done|]).
        iSplitL "HAf"; [interp_unfold!; iApply "HAf"|interp_unfold!; iApply "HBf"]. }
      iDestruct "HcntA" as "(_ & _ & HcA & _)".
      iDestruct "HcntB" as "(_ & _ & HcB & _)".
      iSplitL "HcA HcB".
      { iFrame "Hcap". iSplit; [done|]. iSplitL.
        - iExists 0, 0, a2A', a2B'. iSplit; [done|].
          iSplitL "HcA"; by iApply sub_susp_count_c0_vout.
        - by iLeft. }
      iExists a2A', a2B', s1_def, s2_def. iSplit; [done|].
      iSplitL "HservA"; [iExact "HservA"|iExact "HservB"].

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
