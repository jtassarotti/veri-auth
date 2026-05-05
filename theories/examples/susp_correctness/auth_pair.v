From auth.prelude Require Import stdpp.
From auth.rel_logic_tern_susp Require Import model interp spec_tactics.
From iris.algebra Require Import gset auth.
From auth.examples Require Import authentikit authenticatable_base_susp.
From auth.examples.susp_correctness Require Export definitions helpers.

Section authenticatable.
  Context `{!authG Σ, !seqG Σ, !visited_mapG Σ, !lg_mapG Σ, !mapG Σ, !capG Σ, !intransitG Σ, !stateG Σ} (N : namespace).

  Lemma refines_Auth_pair Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆; ⋆, var2 var1 → var2 var0 → var2 (var1 * var0) ⟧
      (ext Δ (lrel_evidence N)) p_Auth_pair v_Auth_pair i_Auth_pair.
  Proof.
    iSplit; [|iSplit]; interp_unfold!; last first.
    { (* unary  *) admit. }
    { (* binary *) admit. }
    (* ternary *)
    iIntros (A v1 v2 v3) "!# _"; rewrite -/interp.
    iIntros (????) "Hv Hi Htok".
    rewrite /p_Auth_pair /v_Auth_pair /i_Auth_pair.
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iSplit; [|iSplit]; interp_unfold!; last first.
    { (* inner-after-A unary *) admit. }
    { (* inner-after-A binary *) admit. }
    iIntros (B w1 w2 w3) "!# _"; rewrite -/interp.
    iIntros (????) "Hv Hi Htok". v_pures; i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iSplit; [|iSplit]; interp_unfold!; last first.
    { (* inner-after-B unary *) admit. }
    { (* inner-after-B binary *) admit. }
    iIntros (vA1 vA2 vA3) "!# #HA".
    interp_unfold! in "HA".
    iDestruct "HA" as "(HA_tern & #HA_bin & #HA_un)".
    rewrite interp_var2_ext3 interp_var1_ext2.
    iDestruct "HA_tern" as (tA p_ssA p_usA p_spA p_uspA v_sA v_dA v_cA -> ->)
      "(#HinvA & #HusserA & #HsserA & #HsuspvdeserA & #HunsuspA & HvserA & HvauthserA & HvcountA)".
    fold v_ser_spec.
    iIntros (????) "Hv Hi Htok". v_pures; i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iSplit; [|iSplit]; interp_unfold!; last first.
    { (* inner-after-HA unary *) admit. }
    { (* inner-after-HA binary *) admit. }
    iIntros (vB1 vB2 vB3) "!# #HB".
    interp_unfold! in "HB".
    iDestruct "HB" as "(HB_tern & #HB_bin & #HB_un)".
    rewrite interp_var2_ext3 interp_var0_ext1.
    iDestruct "HB_tern" as (tB p_ssB p_usB p_spB p_uspB v_sB v_dB v_cB -> ->)
      "(#HinvB & #HusserB & #HsserB & #HsuspvdeserB & #HunsuspB & HvserB & HvauthserB & HvcountB)".
    iIntros (????) "Hv Hi Htok".
    rewrite /prod_ser'' /prod_ser /prod_count.
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame.
    (* Final 3-way split: prove only the ternary [lrel_tern_evidence]. *)
    iSplit; [|iSplit]; interp_unfold!; last first.
    { (* final unary  *) admit. }
    { (* final binary *) admit. }
    (* Ternary evidence for the product. *)
    rewrite interp_var2_ext3.
    iExists (tprod tA tB), _, _, _, _, _, _, _.
    iSplit; [done|]. iSplit; [done|].
    iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit]]]]]].
    - (* 0. invalid_val *)
      iIntros "!#" (p v2 v3) "#HA".
      rewrite interp_tern_prod_unfold.
      iDestruct "HA" as (? ? ? ? ? ? ?) "H". discriminate.
    - (* 1. unsusp_p_ser_spec *)
      iIntros (v s Ψ) "!# Hser HΨ".
      iDestruct "Hser" as (a1 a2 sa sb [-> ->]) "[Hussera Husserb]".
      wp_pures.
      wp_apply ("HusserA" with "Hussera"). iIntros "_". wp_pures.
      wp_apply ("HusserB" with "Husserb"). iIntros "_". wp_pures.
      unfold prod_ser_str. iApply "HΨ". by iModIntro.
    - (* 2. susp_p_ser_spec *)
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
      (* From Hser1, Hser2: ua and ub aren't loc literals, so each γ's lb sits
         strictly inside one half's substructure. *)
      iAssert (⌜∀ lb : loc, ua ≠ #lb⌝)%I as %Hua_not_loc.
      { iIntros (lb).
        destruct tA; simpl.
        - iDestruct "Hser1" as (??) "[_ Hser']".
          iDestruct "Hser'" as (????) "[%Hp _]".
          iPureIntro. intros Heq. by destruct Hp as [-> _].
        - iDestruct "Hser1" as (??) "[H|H]".
          + iDestruct "H" as "[_ %Hp]".
            iPureIntro. intros Heq. by destruct Hp as [-> _].
          + iDestruct "H" as "[_ %Hp]".
            iPureIntro. intros Heq. by destruct Hp as [-> _].
        - iDestruct "Hser1" as "[%Hp _]".
          iPureIntro. intros Heq. by destruct Hp as (? & -> & _).
        - iDestruct "Hser1" as "[%Hp _]".
          iPureIntro. intros Heq. by destruct Hp as (? & -> & _).
        - iDestruct "Hser1" as "[[Hf _]|[He _]]".
          + iDestruct "Hf" as (??????) "[%Hp _]".
            iPureIntro. intros Heq. by destruct Hp as [-> _].
          + iDestruct "He" as (??????) "[%Hp _]".
            iPureIntro. intros Heq. by destruct Hp as [-> _]. }
      iAssert (⌜∀ lb : loc, ub ≠ #lb⌝)%I as %Hub_not_loc.
      { iIntros (lb).
        destruct tB; simpl.
        - iDestruct "Hser2" as (??) "[_ Hser']".
          iDestruct "Hser'" as (????) "[%Hp _]".
          iPureIntro. intros Heq. by destruct Hp as [-> _].
        - iDestruct "Hser2" as (??) "[H|H]".
          + iDestruct "H" as "[_ %Hp]".
            iPureIntro. intros Heq. by destruct Hp as [-> _].
          + iDestruct "H" as "[_ %Hp]".
            iPureIntro. intros Heq. by destruct Hp as [-> _].
        - iDestruct "Hser2" as "[%Hp _]".
          iPureIntro. intros Heq. by destruct Hp as (? & -> & _).
        - iDestruct "Hser2" as "[%Hp _]".
          iPureIntro. intros Heq. by destruct Hp as (? & -> & _).
        - iDestruct "Hser2" as "[[Hf _]|[He _]]".
          + iDestruct "Hf" as (??????) "[%Hp _]".
            iPureIntro. intros Heq. by destruct Hp as [-> _].
          + iDestruct "He" as (??????) "[%Hp _]".
            iPureIntro. intros Heq. by destruct Hp as [-> _]. }
      (* Build the partition by induction on γl. Stash Hsz outside the IH. *)
      assert (size γl = c1 + c2)%nat as Hsz_keep by exact Hsz. clear Hsz.
      iAssert (∃ γlA γlB : gset gname,
                 ⌜γlA ## γlB ∧ γl = γlA ∪ γlB⌝ ∗
                 ([∗ set] γ ∈ γlA, ∃ lb, lg_mapg_frag lb γ ∗ ⌜p_sub_obj tA ua #lb⌝) ∗
                 ([∗ set] γ ∈ γlB, ∃ lb, lg_mapg_frag lb γ ∗ ⌜p_sub_obj tB ub #lb⌝))%I
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
      (* Apply HreachA's transformer with γlA *)
      iSpecialize ("HreachA" $! γlA with "Hg HpenA [//] HbigA").
      iDestruct "HreachA" as "(Hg & HpenA & HbigA')".
      (* Apply HreachB's transformer with γlB *)
      iSpecialize ("HreachB" $! γlB with "Hg HpenB [//] HbigB").
      iDestruct "HreachB" as "(Hg & HpenB & HbigB')".
      (* Recombine penset_frags *)
      iFrame "Hg".
      iAssert (penset_frag (γlA ∪ γlB)) with "[HpenA HpenB]" as "Hpen".
      { rewrite /penset_frag -gset_disj_union //.
        rewrite auth_frag_op own_op. iSplitL "HpenA"; [iExact "HpenA"|iExact "HpenB"]. }
      rewrite -HsplitAB. iFrame "Hpen".
      (* Recombine big_sepSs *)
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
      iIntros "!#" (t' a1 un_a1 a2 a3 s_def s_pred K tᵥ3 pid m d ps pn B0 mlg) "Hv".
      v_pures.
      (* HeapLang evaluation: argument first. Bind v_dB before v_dA. *)
      v_bind tᵥ3 (v_dB #pid).
      iMod ("HsuspvdeserB" $! _ _ _ _ _ _ _ _ _ pid _ _ _ _ _ _ with "Hv")
        as (v_deser_par_B) "[Hv #Hsuspvdeser_inner_B] /=".
      v_bind tᵥ3 (v_dA #pid).
      iMod ("HsuspvdeserA" $! _ _ _ _ _ _ _ _ _ pid _ _ _ _ _ _ with "Hv")
        as (v_deser_par_A) "[Hv #Hsuspvdeser_inner_A] /=".
      rewrite /prod_deser. v_pures.
      iModIntro. iExists _. iFrame "Hv".
      iIntros "!#" (K' tᵥ' Ψ) "!# (%Hunsusp & #HA & #Hser & Hvm & Hauth & Hv) HΨ".
      destruct t' as [t1 t2 | t1 t2 | | | ]; simpl in Hunsusp; try done.
      + (* tprod — the actual case *)
        destruct Hunsusp as (a1A & a1B & un_a1A & un_a1B & -> & -> & HunsuspA & HunsuspB).
        iEval (rewrite /susp_ser_p -/susp_ser_p /=) in "Hser".
        iDestruct "Hser" as (xa xb s_def_A s_def_B [Heq ->]) "[#HserA #HserB]".
        injection Heq as <- <-.
        (* Destructure HA into tern/bin/un parts (all under ▷) *)
        iDestruct "HA" as "[#HAt [#HAb #HAu]]".
        iEval (rewrite interp_tern_prod_unfold) in "HAt".
        rewrite interp_var1_ext2 interp_var0_ext1.
        (* Step prover wp through the lambda destructure to reach the Pair *)
        wp_pures.
        (* Step verifier's prod_deser body to evaluate match against strindex *)
        v_pures.
        (* Case-split on String.index 0 "_" s_pred: SOME i (parse Alen further) or NONE (malformed) *)
        destruct (String.index 0 "_" s_pred) as [i|] eqn:Hidx.
        * (* SOME case: well-formed s_pred. Continue parsing in the verifier:
             after strindex SOME i, extract Alen_str, attempt s2z, run inner
             v_deser_par_A and v_deser_par_B at re-quantified K's, build
             match if all parts agree else mismatch. *)
          rewrite Hidx /=. v_pures.
          (* After v_pures, verifier reduces strsub #0 #i s_pred to Alen_str.
             Then case-split on whether s2z Alen_str succeeds. *)
          set (Alen_str := String.substring 0 i s_pred).
          destruct (ZOfString Alen_str) as [Alen|] eqn:HAlen.
          { (* s2z succeeded with Alen *)
            (* Now at: let Alen? := SOMEV #Alen in match ... → if z2s Alen ≠ Alen_str then NONEV else ... *)
            destruct (decide (StringOfZ Alen = Alen_str)) as [Hzs|Hzs].
            - (* z2s Alen = Alen_str: continue parsing *)
              v_pures.
              destruct (decide (Alen < 0)%Z) as [Halt|Halt].
              + (* Alen < 0: NONEV mismatch *)
                v_pures.
                iEval (rewrite /lrel_evidence' /lrel_bi_evidence /=) in "HA_bin".
                iDestruct "HA_bin" as (tA' p_ssA0 p_usA0 p_spA0 p_uspA0 v_sA0 v_dA0 v_cA0)
                  "(%Heq_A & _ & #HsspecA & #HsuspbinA & _)".
                injection Heq_A as <- <- <- <-.
                iEval (rewrite /lrel_evidence' /lrel_bi_evidence /=) in "HB_bin".
                iDestruct "HB_bin" as (tB' p_ssB0 p_usB0 p_spB0 p_uspB0 v_sB0 v_dB0 v_cB0)
                  "(%Heq_B & _ & #HsspecB & #HsuspbinB & _)".
                injection Heq_B as <- <- <- <-.
                iEval (rewrite interp_bin_prod_unfold) in "HAb".
                rewrite interp_var1_ext2 interp_var0_ext1.
                iDestruct "HAb" as (a1A_v a3A a1B_v a3B) "(%Heq_pa & %Heq_a3 & #HAbA & #HAbB)".
                injection Heq_pa as -> ->. subst a3.
                wp_bind (p_spA un_a1A).
                wp_apply ("HsuspbinA" with "[]"); first by iSplit; [iPureIntro; eauto|iNext; iExact "HAbA"].
                iIntros (a1A' s_real_A c_A) "[#HAbin #HserprealA]".
                wp_pures.
                wp_bind (p_spB un_a1B).
                wp_apply ("HsuspbinB" with "[]"); first by iSplit; [iPureIntro; eauto|iNext; iExact "HAbB"].
                iIntros (a1B' s_real_B c_B) "[#HBbin #HserprealB]".
                wp_pures.
                iApply ("HΨ" $! (a1A', a1B')%V (prod_ser_str s_real_A s_real_B) (c_A + c_B)).
                iModIntro. iSplitL "".
                { iExists (tprod tA' tB').
                  iIntros (E q HE Ψ').
                  iModIntro. iIntros "[Htok Hintr] HΨ'".
                  rewrite /prod_ser. wp_pures.
                  iEval (rewrite -{1}(Qp.div_2 q) intransit_split) in "Hintr".
                  iDestruct "Hintr" as "[HintrA HintrB]".
                  wp_apply ("HsspecA" $! _ _ _ c_A (q/2)%Qp with "[//] [$HserprealA $Htok $HintrA]").
                  iIntros "(Htok & HintrA' & HreachA)". wp_pures.
                  wp_apply ("HsspecB" $! _ _ _ c_B (q/2)%Qp with "[//] [$HserprealB $Htok $HintrB]").
                  iIntros "(Htok & HintrB' & HreachB)". wp_pures.
                  unfold prod_ser_str. iApply "HΨ'". iModIntro. iFrame "Htok".
                  iCombine "HintrA' HintrB'" as "Hcomb".
                  replace ((q/2)/2 + (q/2)/2)%Qp with (q/2)%Qp by (symmetry; apply Qp.div_2).
                  iFrame "Hcomb".
                  iIntros (γl) "Hg Hpen %Hsz Hbig".
                  iAssert (⌜∀ lb : loc, a1A' ≠ #lb⌝)%I as %Ha1A_not_loc.
                  { iIntros (lb).
                    destruct tA'; simpl.
                    - iDestruct "HserprealA" as (??) "[_ HserprealA']".
                      iDestruct "HserprealA'" as (????) "[%Hp _]".
                      iPureIntro. intros Heq. by destruct Hp as [-> _].
                    - iDestruct "HserprealA" as (??) "[H|H]".
                      + iDestruct "H" as "[_ %Hp]".
                        iPureIntro. intros Heq. by destruct Hp as [-> _].
                      + iDestruct "H" as "[_ %Hp]".
                        iPureIntro. intros Heq. by destruct Hp as [-> _].
                    - iDestruct "HserprealA" as "[%Hp _]".
                      iPureIntro. intros Heq. by destruct Hp as (? & -> & _).
                    - iDestruct "HserprealA" as "[%Hp _]".
                      iPureIntro. intros Heq. by destruct Hp as (? & -> & _).
                    - iDestruct "HserprealA" as "[[Hf _]|[He _]]".
                      + iDestruct "Hf" as (??????) "[%Hp _]".
                        iPureIntro. intros Heq. by destruct Hp as [-> _].
                      + iDestruct "He" as (??????) "[%Hp _]".
                        iPureIntro. intros Heq. by destruct Hp as [-> _]. }
                  iAssert (⌜∀ lb : loc, a1B' ≠ #lb⌝)%I as %Ha1B_not_loc.
                  { iIntros (lb).
                    destruct tB'; simpl.
                    - iDestruct "HserprealB" as (??) "[_ HserprealB']".
                      iDestruct "HserprealB'" as (????) "[%Hp _]".
                      iPureIntro. intros Heq. by destruct Hp as [-> _].
                    - iDestruct "HserprealB" as (??) "[H|H]".
                      + iDestruct "H" as "[_ %Hp]".
                        iPureIntro. intros Heq. by destruct Hp as [-> _].
                      + iDestruct "H" as "[_ %Hp]".
                        iPureIntro. intros Heq. by destruct Hp as [-> _].
                    - iDestruct "HserprealB" as "[%Hp _]".
                      iPureIntro. intros Heq. by destruct Hp as (? & -> & _).
                    - iDestruct "HserprealB" as "[%Hp _]".
                      iPureIntro. intros Heq. by destruct Hp as (? & -> & _).
                    - iDestruct "HserprealB" as "[[Hf _]|[He _]]".
                      + iDestruct "Hf" as (??????) "[%Hp _]".
                        iPureIntro. intros Heq. by destruct Hp as [-> _].
                      + iDestruct "He" as (??????) "[%Hp _]".
                        iPureIntro. intros Heq. by destruct Hp as [-> _]. }
                  assert (size γl = c_A + c_B)%nat as Hsz_keep by exact Hsz. clear Hsz.
                  iAssert (∃ γlA γlB : gset gname,
                             ⌜γlA ## γlB ∧ γl = γlA ∪ γlB⌝ ∗
                             ([∗ set] γ ∈ γlA, ∃ lb, lg_mapg_frag lb γ ∗ ⌜p_sub_obj tA' a1A' #lb⌝) ∗
                             ([∗ set] γ ∈ γlB, ∃ lb, lg_mapg_frag lb γ ∗ ⌜p_sub_obj tB' a1B' #lb⌝))%I
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
                      + exfalso. by apply (Ha1A_not_loc lb_γ).
                      + exfalso. by apply (Ha1B_not_loc lb_γ).
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
                  iDestruct (susp_ser_p_real_γl_card_le with "HserprealA HbigA") as %HszA_le.
                  iDestruct (susp_ser_p_real_γl_card_le with "HserprealB HbigB") as %HszB_le.
                  assert (size γlA + size γlB = c_A + c_B) as Hsz_sum.
                  { rewrite HsplitAB in Hsz_keep.
                    by rewrite (size_union _ _ HdisjAB) in Hsz_keep. }
                  assert (size γlA = c_A) as HszA by lia.
                  assert (size γlB = c_B) as HszB by lia.
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
                    iPureIntro. simpl. exists a1A', a1B'. split; [done|].
                    right. right. left. done. }
                  iApply (big_sepS_mono with "HbigB'").
                  iIntros (γ' ?) "[Hreach Hlb]". iFrame "Hreach".
                  iDestruct "Hlb" as (lb) "[Hlg %Hp]". iExists lb. iFrame "Hlg".
                  iPureIntro. simpl. exists a1A', a1B'. split; [done|].
                  right. right. right. done. }
                iRight. iSplit.
                { (* s_pred ≠ s_real: if s_pred = prod_ser_str sA sB then
                     Alen = Z.of_nat (length sA) ≥ 0, contradicting Halt. *)
                  iPureIntro. intros Heq.
                  rewrite Heq /prod_ser_str in Hidx.
                  erewrite index_0_append_char in Hidx;
                    [|done|apply valid_tag_stringOfZ].
                  injection Hidx as <-.
                  subst Alen_str. rewrite Heq /prod_ser_str in HAlen.
                  rewrite substring_0_length_append in HAlen.
                  rewrite ZOfString_inv in HAlen.
                  injection HAlen as <-.
                  lia. }
                iEval (rewrite interp_bin_prod_unfold).
                rewrite interp_var1_ext2 interp_var0_ext1.
                iExists a1A', a3A, a1B', a3B.
                iFrame "HAbin HBbin".
                iSplit; [done|]. done.
              + (* Alen >= 0: continue parsing. Now at:
                   let slen := strlen s in if slen - i - 1 < Alen then NONEV else ... *)
                v_pures.
                destruct (decide (Z.of_nat (String.length s_pred) - Z.of_nat i - 1 < Alen)%Z) as [Hslen|Hslen].
                * (* slen - i - 1 < Alen: NONEV mismatch *)
                  v_pures.
                  iEval (rewrite /lrel_evidence' /lrel_bi_evidence /=) in "HA_bin".
                  iDestruct "HA_bin" as (tA' p_ssA0 p_usA0 p_spA0 p_uspA0 v_sA0 v_dA0 v_cA0)
                    "(%Heq_A & _ & #HsspecA & #HsuspbinA & _)".
                  injection Heq_A as <- <- <- <-.
                  iEval (rewrite /lrel_evidence' /lrel_bi_evidence /=) in "HB_bin".
                  iDestruct "HB_bin" as (tB' p_ssB0 p_usB0 p_spB0 p_uspB0 v_sB0 v_dB0 v_cB0)
                    "(%Heq_B & _ & #HsspecB & #HsuspbinB & _)".
                  injection Heq_B as <- <- <- <-.
                  iEval (rewrite interp_bin_prod_unfold) in "HAb".
                  rewrite interp_var1_ext2 interp_var0_ext1.
                  iDestruct "HAb" as (a1A_v a3A a1B_v a3B) "(%Heq_pa & %Heq_a3 & #HAbA & #HAbB)".
                  injection Heq_pa as -> ->. subst a3.
                  wp_bind (p_spA un_a1A).
                  wp_apply ("HsuspbinA" with "[]"); first by iSplit; [iPureIntro; eauto|iNext; iExact "HAbA"].
                  iIntros (a1A' s_real_A c_A) "[#HAbin #HserprealA]".
                  wp_pures.
                  wp_bind (p_spB un_a1B).
                  wp_apply ("HsuspbinB" with "[]"); first by iSplit; [iPureIntro; eauto|iNext; iExact "HAbB"].
                  iIntros (a1B' s_real_B c_B) "[#HBbin #HserprealB]".
                  wp_pures.
                  iApply ("HΨ" $! (a1A', a1B')%V (prod_ser_str s_real_A s_real_B) (c_A + c_B)).
                  iModIntro. iSplitL "".
                  { iExists (tprod tA' tB').
                    iIntros (E q HE Ψ').
                    iModIntro. iIntros "[Htok Hintr] HΨ'".
                    rewrite /prod_ser. wp_pures.
                    iEval (rewrite -{1}(Qp.div_2 q) intransit_split) in "Hintr".
                    iDestruct "Hintr" as "[HintrA HintrB]".
                    wp_apply ("HsspecA" $! _ _ _ c_A (q/2)%Qp with "[//] [$HserprealA $Htok $HintrA]").
                    iIntros "(Htok & HintrA' & HreachA)". wp_pures.
                    wp_apply ("HsspecB" $! _ _ _ c_B (q/2)%Qp with "[//] [$HserprealB $Htok $HintrB]").
                    iIntros "(Htok & HintrB' & HreachB)". wp_pures.
                    unfold prod_ser_str. iApply "HΨ'". iModIntro. iFrame "Htok".
                    iCombine "HintrA' HintrB'" as "Hcomb".
                    replace ((q/2)/2 + (q/2)/2)%Qp with (q/2)%Qp by (symmetry; apply Qp.div_2).
                    iFrame "Hcomb".
                    iIntros (γl) "Hg Hpen %Hsz Hbig".
                    iAssert (⌜∀ lb : loc, a1A' ≠ #lb⌝)%I as %Ha1A_not_loc.
                    { iIntros (lb).
                      destruct tA'; simpl.
                      - iDestruct "HserprealA" as (??) "[_ HserprealA']".
                        iDestruct "HserprealA'" as (????) "[%Hp _]".
                        iPureIntro. intros Heq. by destruct Hp as [-> _].
                      - iDestruct "HserprealA" as (??) "[H|H]".
                        + iDestruct "H" as "[_ %Hp]".
                          iPureIntro. intros Heq. by destruct Hp as [-> _].
                        + iDestruct "H" as "[_ %Hp]".
                          iPureIntro. intros Heq. by destruct Hp as [-> _].
                      - iDestruct "HserprealA" as "[%Hp _]".
                        iPureIntro. intros Heq. by destruct Hp as (? & -> & _).
                      - iDestruct "HserprealA" as "[%Hp _]".
                        iPureIntro. intros Heq. by destruct Hp as (? & -> & _).
                      - iDestruct "HserprealA" as "[[Hf _]|[He _]]".
                        + iDestruct "Hf" as (??????) "[%Hp _]".
                          iPureIntro. intros Heq. by destruct Hp as [-> _].
                        + iDestruct "He" as (??????) "[%Hp _]".
                          iPureIntro. intros Heq. by destruct Hp as [-> _]. }
                    iAssert (⌜∀ lb : loc, a1B' ≠ #lb⌝)%I as %Ha1B_not_loc.
                    { iIntros (lb).
                      destruct tB'; simpl.
                      - iDestruct "HserprealB" as (??) "[_ HserprealB']".
                        iDestruct "HserprealB'" as (????) "[%Hp _]".
                        iPureIntro. intros Heq. by destruct Hp as [-> _].
                      - iDestruct "HserprealB" as (??) "[H|H]".
                        + iDestruct "H" as "[_ %Hp]".
                          iPureIntro. intros Heq. by destruct Hp as [-> _].
                        + iDestruct "H" as "[_ %Hp]".
                          iPureIntro. intros Heq. by destruct Hp as [-> _].
                      - iDestruct "HserprealB" as "[%Hp _]".
                        iPureIntro. intros Heq. by destruct Hp as (? & -> & _).
                      - iDestruct "HserprealB" as "[%Hp _]".
                        iPureIntro. intros Heq. by destruct Hp as (? & -> & _).
                      - iDestruct "HserprealB" as "[[Hf _]|[He _]]".
                        + iDestruct "Hf" as (??????) "[%Hp _]".
                          iPureIntro. intros Heq. by destruct Hp as [-> _].
                        + iDestruct "He" as (??????) "[%Hp _]".
                          iPureIntro. intros Heq. by destruct Hp as [-> _]. }
                    assert (size γl = c_A + c_B)%nat as Hsz_keep by exact Hsz. clear Hsz.
                    iAssert (∃ γlA γlB : gset gname,
                               ⌜γlA ## γlB ∧ γl = γlA ∪ γlB⌝ ∗
                               ([∗ set] γ ∈ γlA, ∃ lb, lg_mapg_frag lb γ ∗ ⌜p_sub_obj tA' a1A' #lb⌝) ∗
                               ([∗ set] γ ∈ γlB, ∃ lb, lg_mapg_frag lb γ ∗ ⌜p_sub_obj tB' a1B' #lb⌝))%I
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
                        + exfalso. by apply (Ha1A_not_loc lb_γ).
                        + exfalso. by apply (Ha1B_not_loc lb_γ).
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
                    iDestruct (susp_ser_p_real_γl_card_le with "HserprealA HbigA") as %HszA_le.
                    iDestruct (susp_ser_p_real_γl_card_le with "HserprealB HbigB") as %HszB_le.
                    assert (size γlA + size γlB = c_A + c_B) as Hsz_sum.
                    { rewrite HsplitAB in Hsz_keep.
                      by rewrite (size_union _ _ HdisjAB) in Hsz_keep. }
                    assert (size γlA = c_A) as HszA by lia.
                    assert (size γlB = c_B) as HszB by lia.
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
                      iPureIntro. simpl. exists a1A', a1B'. split; [done|].
                      right. right. left. done. }
                    iApply (big_sepS_mono with "HbigB'").
                    iIntros (γ' ?) "[Hreach Hlb]". iFrame "Hreach".
                    iDestruct "Hlb" as (lb) "[Hlg %Hp]". iExists lb. iFrame "Hlg".
                    iPureIntro. simpl. exists a1A', a1B'. split; [done|].
                    right. right. right. done. }
                  iRight. iSplit.
                  { (* s_pred ≠ s_real: if s_pred = prod_ser_str sA sB then
                       slen = i + 1 + |sA| + |sB|, so slen - i - 1 = |sA| + |sB|
                       ≥ |sA| = Alen — contradicts Hslen. *)
                    iPureIntro. intros Heq.
                    rewrite Heq /prod_ser_str in Hidx.
                    erewrite index_0_append_char in Hidx;
                      [|done|apply valid_tag_stringOfZ].
                    injection Hidx as <-.
                    subst Alen_str. rewrite Heq /prod_ser_str in HAlen.
                    rewrite substring_0_length_append in HAlen.
                    rewrite ZOfString_inv in HAlen.
                    injection HAlen as <-.
                    rewrite Heq /prod_ser_str in Hslen.
                    rewrite !strings.length_app /= in Hslen.
                    lia. }
                  iEval (rewrite interp_bin_prod_unfold).
                  rewrite interp_var1_ext2 interp_var0_ext1.
                  iExists a1A', a3A, a1B', a3B.
                  iFrame "HAbin HBbin".
                  iSplit; [done|]. done.
                * (* slen - i - 1 >= Alen: continue parsing.
                     Now: let s1 := strsub (i+1) Alen s_pred in let s2 := ... in
                     let v1? := v_deser_par_A s1 in match v1? with SOME v1 => ... | NONE => NONEV end.
                     Apply Hsuspvdeser_inner_A then Hsuspvdeser_inner_B. *)
                  v_pures.
                  (* Extract inner relations from HAt (ternary), HAb (binary), HAu (unary). *)
                  iDestruct "HAt" as (a1A_v a2A a3A a1B_v a2B a3B) "(%HeqA1 & %HeqA2 & %HeqA3 & #HAtA & #HBtA)".
                  injection HeqA1 as -> ->. subst a2 a3.
                  iEval (rewrite interp_bin_prod_unfold) in "HAb".
                  rewrite interp_var1_ext2 interp_var0_ext1.
                  iDestruct "HAb" as (? a3A_d ? a3B_d) "(%HeqB1 & %HeqB3 & #HAbA & #HBbA)".
                  injection HeqB1 as -> ->. injection HeqB3 as -> ->.
                  iEval (rewrite interp_un_prod_unfold) in "HAu".
                  rewrite interp_var1_ext2 interp_var0_ext1.
                  iDestruct "HAu" as (? ?) "(%HeqU2 & #HAuA & #HBuA)".
                  injection HeqU2 as -> ->.
                  iEval (rewrite /lrel_evidence' /lrel_bi_evidence /=) in "HA_bin".
                  iDestruct "HA_bin" as (tA' p_ssA0 p_usA0 p_spA0 p_uspA0 v_sA0 v_dA0 v_cA0)
                    "(%Heq_A & _ & #HsspecA & #HsuspbinA & _)".
                  injection Heq_A as <- <- <- <-.
                  iEval (rewrite /lrel_evidence' /lrel_bi_evidence /=) in "HB_bin".
                  iDestruct "HB_bin" as (tB' p_ssB0 p_usB0 p_spB0 p_uspB0 v_sB0 v_dB0 v_cB0)
                    "(%Heq_B & _ & #HsspecB & #HsuspbinB & _)".
                  injection Heq_B as <- <- <- <-.
                  (* Pair eval is right-first, so prover B runs first.
                     For pair, this conflicts with the verifier order (deserA
                     first then deserB) when using Hsuspvdeser_inner_X (which
                     couples prover-X with verifier-X). The success-path proof
                     requires either:
                     1. Restructuring the prover suspend body to evaluate A first.
                     2. Applying Hsuspvdeser_inner_B at the verifier's deserB
                        position (inside deserA's SOME branch — only reachable
                        after deserA runs). v_bind at this position requires
                        the verifier expression to syntactically contain
                        v_deser_par_B #s2; since fill K is structural, this
                        works even before deserA runs. Then run prover B via
                        Hsuspvdeser_inner_B coupled with verifier-B advance.
                     This success path is left admitted pending that approach. *)
                  admit.
            - (* z2s Alen ≠ Alen_str: NONEV → mismatch *)
              v_pures.
              iEval (rewrite /lrel_evidence' /lrel_bi_evidence /=) in "HA_bin".
              iDestruct "HA_bin" as (tA' p_ssA0 p_usA0 p_spA0 p_uspA0 v_sA0 v_dA0 v_cA0)
                "(%Heq_A & _ & #HsspecA & #HsuspbinA & _)".
              injection Heq_A as <- <- <- <-.
              iEval (rewrite /lrel_evidence' /lrel_bi_evidence /=) in "HB_bin".
              iDestruct "HB_bin" as (tB' p_ssB0 p_usB0 p_spB0 p_uspB0 v_sB0 v_dB0 v_cB0)
                "(%Heq_B & _ & #HsspecB & #HsuspbinB & _)".
              injection Heq_B as <- <- <- <-.
              iEval (rewrite interp_bin_prod_unfold) in "HAb".
              rewrite interp_var1_ext2 interp_var0_ext1.
              iDestruct "HAb" as (a1A_v a3A a1B_v a3B) "(%Heq_pa & %Heq_a3 & #HAbA & #HAbB)".
              injection Heq_pa as -> ->. subst a3.
              wp_bind (p_spA un_a1A).
              wp_apply ("HsuspbinA" with "[]"); first by iSplit; [iPureIntro; eauto|iNext; iExact "HAbA"].
              iIntros (a1A' s_real_A c_A) "[#HAbin #HserprealA]".
              wp_pures.
              wp_bind (p_spB un_a1B).
              wp_apply ("HsuspbinB" with "[]"); first by iSplit; [iPureIntro; eauto|iNext; iExact "HAbB"].
              iIntros (a1B' s_real_B c_B) "[#HBbin #HserprealB]".
              wp_pures.
              iApply ("HΨ" $! (a1A', a1B')%V (prod_ser_str s_real_A s_real_B) (c_A + c_B)).
              iModIntro. iSplitL "".
              { iExists (tprod tA' tB').
                iIntros (E q HE Ψ').
                iModIntro. iIntros "[Htok Hintr] HΨ'".
                rewrite /prod_ser. wp_pures.
                iEval (rewrite -{1}(Qp.div_2 q) intransit_split) in "Hintr".
                iDestruct "Hintr" as "[HintrA HintrB]".
                wp_apply ("HsspecA" $! _ _ _ c_A (q/2)%Qp with "[//] [$HserprealA $Htok $HintrA]").
                iIntros "(Htok & HintrA' & HreachA)". wp_pures.
                wp_apply ("HsspecB" $! _ _ _ c_B (q/2)%Qp with "[//] [$HserprealB $Htok $HintrB]").
                iIntros "(Htok & HintrB' & HreachB)". wp_pures.
                unfold prod_ser_str. iApply "HΨ'". iModIntro. iFrame "Htok".
                iCombine "HintrA' HintrB'" as "Hcomb".
                replace ((q/2)/2 + (q/2)/2)%Qp with (q/2)%Qp by (symmetry; apply Qp.div_2).
                iFrame "Hcomb".
                iIntros (γl) "Hg Hpen %Hsz Hbig".
                iAssert (⌜∀ lb : loc, a1A' ≠ #lb⌝)%I as %Ha1A_not_loc.
                { iIntros (lb).
                  destruct tA'; simpl.
                  - iDestruct "HserprealA" as (??) "[_ HserprealA']".
                    iDestruct "HserprealA'" as (????) "[%Hp _]".
                    iPureIntro. intros Heq. by destruct Hp as [-> _].
                  - iDestruct "HserprealA" as (??) "[H|H]".
                    + iDestruct "H" as "[_ %Hp]".
                      iPureIntro. intros Heq. by destruct Hp as [-> _].
                    + iDestruct "H" as "[_ %Hp]".
                      iPureIntro. intros Heq. by destruct Hp as [-> _].
                  - iDestruct "HserprealA" as "[%Hp _]".
                    iPureIntro. intros Heq. by destruct Hp as (? & -> & _).
                  - iDestruct "HserprealA" as "[%Hp _]".
                    iPureIntro. intros Heq. by destruct Hp as (? & -> & _).
                  - iDestruct "HserprealA" as "[[Hf _]|[He _]]".
                    + iDestruct "Hf" as (??????) "[%Hp _]".
                      iPureIntro. intros Heq. by destruct Hp as [-> _].
                    + iDestruct "He" as (??????) "[%Hp _]".
                      iPureIntro. intros Heq. by destruct Hp as [-> _]. }
                iAssert (⌜∀ lb : loc, a1B' ≠ #lb⌝)%I as %Ha1B_not_loc.
                { iIntros (lb).
                  destruct tB'; simpl.
                  - iDestruct "HserprealB" as (??) "[_ HserprealB']".
                    iDestruct "HserprealB'" as (????) "[%Hp _]".
                    iPureIntro. intros Heq. by destruct Hp as [-> _].
                  - iDestruct "HserprealB" as (??) "[H|H]".
                    + iDestruct "H" as "[_ %Hp]".
                      iPureIntro. intros Heq. by destruct Hp as [-> _].
                    + iDestruct "H" as "[_ %Hp]".
                      iPureIntro. intros Heq. by destruct Hp as [-> _].
                  - iDestruct "HserprealB" as "[%Hp _]".
                    iPureIntro. intros Heq. by destruct Hp as (? & -> & _).
                  - iDestruct "HserprealB" as "[%Hp _]".
                    iPureIntro. intros Heq. by destruct Hp as (? & -> & _).
                  - iDestruct "HserprealB" as "[[Hf _]|[He _]]".
                    + iDestruct "Hf" as (??????) "[%Hp _]".
                      iPureIntro. intros Heq. by destruct Hp as [-> _].
                    + iDestruct "He" as (??????) "[%Hp _]".
                      iPureIntro. intros Heq. by destruct Hp as [-> _]. }
                assert (size γl = c_A + c_B)%nat as Hsz_keep by exact Hsz. clear Hsz.
                iAssert (∃ γlA γlB : gset gname,
                           ⌜γlA ## γlB ∧ γl = γlA ∪ γlB⌝ ∗
                           ([∗ set] γ ∈ γlA, ∃ lb, lg_mapg_frag lb γ ∗ ⌜p_sub_obj tA' a1A' #lb⌝) ∗
                           ([∗ set] γ ∈ γlB, ∃ lb, lg_mapg_frag lb γ ∗ ⌜p_sub_obj tB' a1B' #lb⌝))%I
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
                    + exfalso. by apply (Ha1A_not_loc lb_γ).
                    + exfalso. by apply (Ha1B_not_loc lb_γ).
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
                iDestruct (susp_ser_p_real_γl_card_le with "HserprealA HbigA") as %HszA_le.
                iDestruct (susp_ser_p_real_γl_card_le with "HserprealB HbigB") as %HszB_le.
                assert (size γlA + size γlB = c_A + c_B) as Hsz_sum.
                { rewrite HsplitAB in Hsz_keep.
                  by rewrite (size_union _ _ HdisjAB) in Hsz_keep. }
                assert (size γlA = c_A) as HszA by lia.
                assert (size γlB = c_B) as HszB by lia.
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
                  iPureIntro. simpl. exists a1A', a1B'. split; [done|].
                  right. right. left. done. }
                iApply (big_sepS_mono with "HbigB'").
                iIntros (γ' ?) "[Hreach Hlb]". iFrame "Hreach".
                iDestruct "Hlb" as (lb) "[Hlg %Hp]". iExists lb. iFrame "Hlg".
                iPureIntro. simpl. exists a1A', a1B'. split; [done|].
                right. right. right. done. }
              iRight. iSplit.
              { (* s_pred ≠ s_real: if s_pred = prod_ser_str sA sB then by
                   Hidx + index_0_append_char, i = |StringOfZ |sA||; by HAlen
                   + substring_0_length_append + ZOfString_inv, Alen = |sA|;
                   then z2s Alen = StringOfZ |sA| = Alen_str — contradicts Hzs. *)
                iPureIntro. intros Heq.
                rewrite Heq /prod_ser_str in Hidx.
                erewrite index_0_append_char in Hidx;
                  [|done|apply valid_tag_stringOfZ].
                injection Hidx as <-.
                subst Alen_str. rewrite Heq /prod_ser_str in HAlen.
                rewrite substring_0_length_append in HAlen.
                rewrite ZOfString_inv in HAlen.
                injection HAlen as <-.
                apply Hzs. by rewrite Heq /prod_ser_str substring_0_length_append. }
              iEval (rewrite interp_bin_prod_unfold).
              rewrite interp_var1_ext2 interp_var0_ext1.
              iExists a1A', a3A, a1B', a3B.
              iFrame "HAbin HBbin".
              iSplit; [done|]. done. }
          { (* s2z failed → NONEV → mismatch (s_real parses, s_pred doesn't) *)
            (* Verifier: advance through `match s2z = NONE → NONEV` and outer NONEV. *)
            v_pures.
            (* Prover: run suspend_B then suspend_A via suspend_spec_bin. *)
            iEval (rewrite /lrel_evidence' /lrel_bi_evidence /=) in "HA_bin".
            iDestruct "HA_bin" as (tA' p_ssA0 p_usA0 p_spA0 p_uspA0 v_sA0 v_dA0 v_cA0)
              "(%Heq_A & _ & #HsspecA & #HsuspbinA & _)".
            injection Heq_A as <- <- <- <-.
            iEval (rewrite /lrel_evidence' /lrel_bi_evidence /=) in "HB_bin".
            iDestruct "HB_bin" as (tB' p_ssB0 p_usB0 p_spB0 p_uspB0 v_sB0 v_dB0 v_cB0)
              "(%Heq_B & _ & #HsspecB & #HsuspbinB & _)".
            injection Heq_B as <- <- <- <-.
            iEval (rewrite interp_bin_prod_unfold) in "HAb".
            rewrite interp_var1_ext2 interp_var0_ext1.
            iDestruct "HAb" as (a1A_v a3A a1B_v a3B) "(%Heq_pa & %Heq_a3 & #HAbA & #HAbB)".
            injection Heq_pa as -> ->. subst a3.
            wp_bind (p_spA un_a1A).
            wp_apply ("HsuspbinA" with "[]"); first by iSplit; [iPureIntro; eauto|iNext; iExact "HAbA"].
            iIntros (a1A' s_real_A c_A) "[#HAbin #HserprealA]".
            wp_pures.
            wp_bind (p_spB un_a1B).
            wp_apply ("HsuspbinB" with "[]"); first by iSplit; [iPureIntro; eauto|iNext; iExact "HAbB"].
            iIntros (a1B' s_real_B c_B) "[#HBbin #HserprealB]".
            wp_pures.
            iApply ("HΨ" $! (a1A', a1B')%V (prod_ser_str s_real_A s_real_B) (c_A + c_B)).
            iModIntro. iSplitL "".
            { iExists (tprod tA' tB').
              iIntros (E q HE Ψ').
              iModIntro. iIntros "[Htok Hintr] HΨ'".
              rewrite /prod_ser. wp_pures.
              iEval (rewrite -{1}(Qp.div_2 q) intransit_split) in "Hintr".
              iDestruct "Hintr" as "[HintrA HintrB]".
              wp_apply ("HsspecA" $! _ _ _ c_A (q/2)%Qp with "[//] [$HserprealA $Htok $HintrA]").
              iIntros "(Htok & HintrA' & HreachA)". wp_pures.
              wp_apply ("HsspecB" $! _ _ _ c_B (q/2)%Qp with "[//] [$HserprealB $Htok $HintrB]").
              iIntros "(Htok & HintrB' & HreachB)". wp_pures.
              unfold prod_ser_str. iApply "HΨ'". iModIntro. iFrame "Htok".
              iCombine "HintrA' HintrB'" as "Hcomb".
              replace ((q/2)/2 + (q/2)/2)%Qp with (q/2)%Qp by (symmetry; apply Qp.div_2).
              iFrame "Hcomb".
              iIntros (γl) "Hg Hpen %Hsz Hbig".
              iAssert (⌜∀ lb : loc, a1A' ≠ #lb⌝)%I as %Ha1A_not_loc.
              { iIntros (lb).
                destruct tA'; simpl.
                - iDestruct "HserprealA" as (??) "[_ HserprealA']".
                  iDestruct "HserprealA'" as (????) "[%Hp _]".
                  iPureIntro. intros Heq. by destruct Hp as [-> _].
                - iDestruct "HserprealA" as (??) "[H|H]".
                  + iDestruct "H" as "[_ %Hp]".
                    iPureIntro. intros Heq. by destruct Hp as [-> _].
                  + iDestruct "H" as "[_ %Hp]".
                    iPureIntro. intros Heq. by destruct Hp as [-> _].
                - iDestruct "HserprealA" as "[%Hp _]".
                  iPureIntro. intros Heq. by destruct Hp as (? & -> & _).
                - iDestruct "HserprealA" as "[%Hp _]".
                  iPureIntro. intros Heq. by destruct Hp as (? & -> & _).
                - iDestruct "HserprealA" as "[[Hf _]|[He _]]".
                  + iDestruct "Hf" as (??????) "[%Hp _]".
                    iPureIntro. intros Heq. by destruct Hp as [-> _].
                  + iDestruct "He" as (??????) "[%Hp _]".
                    iPureIntro. intros Heq. by destruct Hp as [-> _]. }
              iAssert (⌜∀ lb : loc, a1B' ≠ #lb⌝)%I as %Ha1B_not_loc.
              { iIntros (lb).
                destruct tB'; simpl.
                - iDestruct "HserprealB" as (??) "[_ HserprealB']".
                  iDestruct "HserprealB'" as (????) "[%Hp _]".
                  iPureIntro. intros Heq. by destruct Hp as [-> _].
                - iDestruct "HserprealB" as (??) "[H|H]".
                  + iDestruct "H" as "[_ %Hp]".
                    iPureIntro. intros Heq. by destruct Hp as [-> _].
                  + iDestruct "H" as "[_ %Hp]".
                    iPureIntro. intros Heq. by destruct Hp as [-> _].
                - iDestruct "HserprealB" as "[%Hp _]".
                  iPureIntro. intros Heq. by destruct Hp as (? & -> & _).
                - iDestruct "HserprealB" as "[%Hp _]".
                  iPureIntro. intros Heq. by destruct Hp as (? & -> & _).
                - iDestruct "HserprealB" as "[[Hf _]|[He _]]".
                  + iDestruct "Hf" as (??????) "[%Hp _]".
                    iPureIntro. intros Heq. by destruct Hp as [-> _].
                  + iDestruct "He" as (??????) "[%Hp _]".
                    iPureIntro. intros Heq. by destruct Hp as [-> _]. }
              assert (size γl = c_A + c_B)%nat as Hsz_keep by exact Hsz. clear Hsz.
              iAssert (∃ γlA γlB : gset gname,
                         ⌜γlA ## γlB ∧ γl = γlA ∪ γlB⌝ ∗
                         ([∗ set] γ ∈ γlA, ∃ lb, lg_mapg_frag lb γ ∗ ⌜p_sub_obj tA' a1A' #lb⌝) ∗
                         ([∗ set] γ ∈ γlB, ∃ lb, lg_mapg_frag lb γ ∗ ⌜p_sub_obj tB' a1B' #lb⌝))%I
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
                  + exfalso. by apply (Ha1A_not_loc lb_γ).
                  + exfalso. by apply (Ha1B_not_loc lb_γ).
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
              iDestruct (susp_ser_p_real_γl_card_le with "HserprealA HbigA") as %HszA_le.
              iDestruct (susp_ser_p_real_γl_card_le with "HserprealB HbigB") as %HszB_le.
              assert (size γlA + size γlB = c_A + c_B) as Hsz_sum.
              { rewrite HsplitAB in Hsz_keep.
                by rewrite (size_union _ _ HdisjAB) in Hsz_keep. }
              assert (size γlA = c_A) as HszA by lia.
              assert (size γlB = c_B) as HszB by lia.
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
                iPureIntro. simpl. exists a1A', a1B'. split; [done|].
                right. right. left. done. }
              iApply (big_sepS_mono with "HbigB'").
              iIntros (γ' ?) "[Hreach Hlb]". iFrame "Hreach".
              iDestruct "Hlb" as (lb) "[Hlg %Hp]". iExists lb. iFrame "Hlg".
              iPureIntro. simpl. exists a1A', a1B'. split; [done|].
              right. right. right. done. }
            iRight. iSplit.
            { (* s_pred ≠ s_real: if s_pred = prod_ser_str sA sB then
                 strindex would point at length(StringOfZ |sA|), and Alen_str
                 would be StringOfZ |sA|, which always parses → contradiction
                 with HAlen. *)
              iPureIntro. intros Heq.
              rewrite Heq /prod_ser_str in Hidx.
              erewrite index_0_append_char in Hidx;
                [|done|apply valid_tag_stringOfZ].
              injection Hidx as <-.
              subst Alen_str. rewrite Heq /prod_ser_str in HAlen.
              rewrite substring_0_length_append in HAlen.
              rewrite ZOfString_inv in HAlen. discriminate. }
            iEval (rewrite interp_bin_prod_unfold).
            rewrite interp_var1_ext2 interp_var0_ext1.
            iExists a1A', a3A, a1B', a3B.
            iFrame "HAbin HBbin".
            iSplit; [done|]. done. }
        * (* NONE case: malformed s_pred *)
          rewrite Hidx /=. v_pures.
          (* Hv now at fill K (InjLV #()) = NONEV. Discharge prover wp via
             HA_bin's / HB_bin's suspend_spec_bin. *)
          iEval (rewrite /lrel_evidence' /lrel_bi_evidence /=) in "HA_bin".
          iDestruct "HA_bin" as (tA' p_ssA0 p_usA0 p_spA0 p_uspA0 v_sA0 v_dA0 v_cA0)
            "(%Heq_A & _ & #HsspecA & #HsuspbinA & _)".
          injection Heq_A as <- <- <- <-.
          iEval (rewrite /lrel_evidence' /lrel_bi_evidence /=) in "HB_bin".
          iDestruct "HB_bin" as (tB' p_ssB0 p_usB0 p_spB0 p_uspB0 v_sB0 v_dB0 v_cB0)
            "(%Heq_B & _ & #HsspecB & #HsuspbinB & _)".
          injection Heq_B as <- <- <- <-.
          (* HAb destruct: a3 = (a3A, a3B), lrel_tern_bin A a1A a3A, etc.
             lrel_bin_prod is `∃ v1 v2 v1' v2', ⌜w1=(v1,v1')⌝ ∧ ⌜w2=(v2,v2')⌝
             ∧ A v1 v2 ∗ B v1' v2'`. So 4 binders are v1, v2, v1', v2'. *)
          iEval (rewrite interp_bin_prod_unfold) in "HAb".
          rewrite interp_var1_ext2 interp_var0_ext1.
          iDestruct "HAb" as (a1A_v a3A a1B_v a3B) "(%Heq_pa & %Heq_a3 & #HAbA & #HAbB)".
          injection Heq_pa as -> ->. subst a3.
          (* Run prover suspend_A first (let-binding evaluates A first), then suspend_B *)
          wp_bind (p_spA un_a1A).
          wp_apply ("HsuspbinA" with "[]"); first by iSplit; [iPureIntro; eauto|iNext; iExact "HAbA"].
          iIntros (a1A' s_real_A c_A) "[#HAbin #HserprealA]".
          wp_pures.
          wp_bind (p_spB un_a1B).
          wp_apply ("HsuspbinB" with "[]"); first by iSplit; [iPureIntro; eauto|iNext; iExact "HAbB"].
          iIntros (a1B' s_real_B c_B) "[#HBbin #HserprealB]".
          wp_pures.
          iApply ("HΨ" $! (a1A', a1B')%V (prod_ser_str s_real_A s_real_B) (c_A + c_B)).
          iModIntro. iSplitL "".
          { (* (∃ t_real, susp_p_ser_spec_at (prod_ser p_ssA p_ssB) t_real
                                            (c_A+c_B) (a1A',a1B')
                                            (prod_ser_str s_real_A s_real_B)).
               Inline tprod susp_p_ser_spec proof (mirrors case 2 of refines_Auth_pair). *)
            iExists (tprod tA' tB').
            iIntros (E q HE Ψ').
            iModIntro. iIntros "[Htok Hintr] HΨ'".
            rewrite /prod_ser. wp_pures.
            iEval (rewrite -{1}(Qp.div_2 q) intransit_split) in "Hintr".
            iDestruct "Hintr" as "[HintrA HintrB]".
            wp_apply ("HsspecA" $! _ _ _ c_A (q/2)%Qp with "[//] [$HserprealA $Htok $HintrA]").
            iIntros "(Htok & HintrA' & HreachA)". wp_pures.
            wp_apply ("HsspecB" $! _ _ _ c_B (q/2)%Qp with "[//] [$HserprealB $Htok $HintrB]").
            iIntros "(Htok & HintrB' & HreachB)". wp_pures.
            unfold prod_ser_str. iApply "HΨ'". iModIntro. iFrame "Htok".
            iCombine "HintrA' HintrB'" as "Hcomb".
            replace ((q/2)/2 + (q/2)/2)%Qp with (q/2)%Qp by (symmetry; apply Qp.div_2).
            iFrame "Hcomb".
            iIntros (γl) "Hg Hpen %Hsz Hbig".
            iAssert (⌜∀ lb : loc, a1A' ≠ #lb⌝)%I as %Ha1A_not_loc.
            { iIntros (lb).
              destruct tA'; simpl.
              - iDestruct "HserprealA" as (??) "[_ HserprealA']".
                iDestruct "HserprealA'" as (????) "[%Hp _]".
                iPureIntro. intros Heq. by destruct Hp as [-> _].
              - iDestruct "HserprealA" as (??) "[H|H]".
                + iDestruct "H" as "[_ %Hp]".
                  iPureIntro. intros Heq. by destruct Hp as [-> _].
                + iDestruct "H" as "[_ %Hp]".
                  iPureIntro. intros Heq. by destruct Hp as [-> _].
              - iDestruct "HserprealA" as "[%Hp _]".
                iPureIntro. intros Heq. by destruct Hp as (? & -> & _).
              - iDestruct "HserprealA" as "[%Hp _]".
                iPureIntro. intros Heq. by destruct Hp as (? & -> & _).
              - iDestruct "HserprealA" as "[[Hf _]|[He _]]".
                + iDestruct "Hf" as (??????) "[%Hp _]".
                  iPureIntro. intros Heq. by destruct Hp as [-> _].
                + iDestruct "He" as (??????) "[%Hp _]".
                  iPureIntro. intros Heq. by destruct Hp as [-> _]. }
            iAssert (⌜∀ lb : loc, a1B' ≠ #lb⌝)%I as %Ha1B_not_loc.
            { iIntros (lb).
              destruct tB'; simpl.
              - iDestruct "HserprealB" as (??) "[_ HserprealB']".
                iDestruct "HserprealB'" as (????) "[%Hp _]".
                iPureIntro. intros Heq. by destruct Hp as [-> _].
              - iDestruct "HserprealB" as (??) "[H|H]".
                + iDestruct "H" as "[_ %Hp]".
                  iPureIntro. intros Heq. by destruct Hp as [-> _].
                + iDestruct "H" as "[_ %Hp]".
                  iPureIntro. intros Heq. by destruct Hp as [-> _].
              - iDestruct "HserprealB" as "[%Hp _]".
                iPureIntro. intros Heq. by destruct Hp as (? & -> & _).
              - iDestruct "HserprealB" as "[%Hp _]".
                iPureIntro. intros Heq. by destruct Hp as (? & -> & _).
              - iDestruct "HserprealB" as "[[Hf _]|[He _]]".
                + iDestruct "Hf" as (??????) "[%Hp _]".
                  iPureIntro. intros Heq. by destruct Hp as [-> _].
                + iDestruct "He" as (??????) "[%Hp _]".
                  iPureIntro. intros Heq. by destruct Hp as [-> _]. }
            assert (size γl = c_A + c_B)%nat as Hsz_keep by exact Hsz. clear Hsz.
            iAssert (∃ γlA γlB : gset gname,
                       ⌜γlA ## γlB ∧ γl = γlA ∪ γlB⌝ ∗
                       ([∗ set] γ ∈ γlA, ∃ lb, lg_mapg_frag lb γ ∗ ⌜p_sub_obj tA' a1A' #lb⌝) ∗
                       ([∗ set] γ ∈ γlB, ∃ lb, lg_mapg_frag lb γ ∗ ⌜p_sub_obj tB' a1B' #lb⌝))%I
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
                + exfalso. by apply (Ha1A_not_loc lb_γ).
                + exfalso. by apply (Ha1B_not_loc lb_γ).
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
            iDestruct (susp_ser_p_real_γl_card_le with "HserprealA HbigA") as %HszA_le.
            iDestruct (susp_ser_p_real_γl_card_le with "HserprealB HbigB") as %HszB_le.
            assert (size γlA + size γlB = c_A + c_B) as Hsz_sum.
            { rewrite HsplitAB in Hsz_keep.
              by rewrite (size_union _ _ HdisjAB) in Hsz_keep. }
            assert (size γlA = c_A) as HszA by lia.
            assert (size γlB = c_B) as HszB by lia.
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
              iPureIntro. simpl. exists a1A', a1B'. split; [done|].
              right. right. left. done. }
            iApply (big_sepS_mono with "HbigB'").
            iIntros (γ' ?) "[Hreach Hlb]". iFrame "Hreach".
            iDestruct "Hlb" as (lb) "[Hlg %Hp]". iExists lb. iFrame "Hlg".
            iPureIntro. simpl. exists a1A', a1B'. split; [done|].
            right. right. right. done. }
          iRight. iSplit.
          { iPureIntro. intros Heq.
            (* s_real = prod_ser_str s_real_A s_real_B contains "_"; s_pred lacks
               "_" by Hidx. So s_pred ≠ s_real. *)
            rewrite Heq /prod_ser_str in Hidx.
            erewrite index_0_append_char in Hidx;
              [discriminate|done|apply valid_tag_stringOfZ]. }
          iEval (rewrite interp_bin_prod_unfold).
          rewrite interp_var1_ext2 interp_var0_ext1.
          iExists a1A', a3A, a1B', a3B.
          iFrame "HAbin HBbin".
          iSplit; [done|]. done.
      + (* tsum: contradicts pair *)
        destruct Hunsusp as [(v1 & un_v1 & -> & -> & _) | (v2 & un_v2 & -> & -> & _)];
          wp_pures;
          iDestruct "HA" as "[#HAt _]";
          iEval (rewrite interp_tern_prod_unfold) in "HAt";
          rewrite interp_var1_ext2 interp_var0_ext1;
          iDestruct "HAt" as (??????) "(%Heq & _)"; discriminate.
      + (* tstring: a1 = #s (literal), contradicts pair *)
        wp_pures.
        iDestruct "Hser" as %(s' & -> & _).
        iDestruct "HA" as "[#HAt _]".
        iEval (rewrite interp_tern_prod_unfold) in "HAt".
        rewrite interp_var1_ext2 interp_var0_ext1.
        iDestruct "HAt" as (??????) "(%Heq & _)". discriminate.
      + (* tint: a1 = #z (literal), contradicts pair *)
        wp_pures.
        iDestruct "Hser" as %(z' & -> & _).
        iDestruct "HA" as "[#HAt _]".
        iEval (rewrite interp_tern_prod_unfold) in "HAt".
        rewrite interp_var1_ext2 interp_var0_ext1.
        iDestruct "HAt" as (??????) "(%Heq & _)". discriminate.
      + (* tauth: a1 = (lb, lr, a, h, p) — IS a pair, but v1' = #p contradicts
           B's invalid_val (no proph_id literals at B). *)
        destruct Hunsusp as (lb & lr & a_inner & h_inner & p_inner & -> & ->).
        wp_pures.
        iDestruct "HA" as "[#HAt _]".
        iEval (rewrite interp_tern_prod_unfold) in "HAt".
        rewrite interp_var1_ext2 interp_var0_ext1.
        iDestruct "HAt" as (v1 v2 v3 v1' v2' v3') "(%Heq1 & %Heq2 & %Heq3 & _ & #HBinner)".
        simplify_eq.
        iExFalso. iApply ("HinvB" with "HBinner").
    - (* 4. unsuspend_spec *)
      iIntros (E a1 a2 a3 HE Ψ) "!# (#HA & Htok & Hintr) HΨ".
      wp_pures.
      iDestruct "HA" as "[#HA1 [#HA2 #HA3]]".
      interp_unfold! in "HA1".
      iDestruct "HA1" as (wa1 wa2 wa3 wb1 wb2 wb3) "(-> & -> & -> & H1 & H2)".
      rewrite interp_bin_prod_unfold. rewrite interp_un_prod_unfold.
      iDestruct "HA2" as (? ? ? ?) "(%Heq1 & %Heq2 & #HA2a & #HA2b)".
      injection Heq1 as -> ->. injection Heq2 as -> ->.
      iDestruct "HA3" as (? ? Heq3) "[#HA3a #HA3b]". injection Heq3 as -> ->.
      wp_pures.
      wp_bind (p_uspB _).
      wp_apply ("HunsuspB" with "[//] [$Htok $Hintr]").
      { rewrite interp_var0_ext1.
        iSplit; [|iSplit]; iNext.
        - destruct B; iExact "H2".
        - destruct B; iExact "HA2b".
        - destruct B; iExact "HA3b". }
      iIntros (un_vb sb) "(Htok & Hintr & %Hunsuspb & #Hsserb)".
      wp_bind (p_uspA _).
      wp_apply ("HunsuspA" with "[//] [$Htok $Hintr]").
      { rewrite interp_var1_ext2.
        iSplit; [|iSplit]; iNext.
        - destruct A; iExact "H1".
        - destruct A; iExact "HA2a".
        - destruct A; iExact "HA3a". }
      iIntros (un_va sa) "(Htok & Hintr & %Hunsuspa & #Hssera)".
      wp_pures. iApply ("HΨ" $! (un_va, un_vb)%V (prod_ser_str sa sb)).
      iFrame. iModIntro. iSplit.
      { iPureIntro. eexists _, _, un_va, un_vb. done. }
      iExists _, _, sa, sb. iFrame "#". done.
    - (* 5. v_ser_spec *)
      iIntros (K tᵥ3 a s id Nc v_outer) "!# Hcnt #Hser Hspec".
      iDestruct "Hcnt" as (c1 c2 pv1 pv2 [-> Hsum]) "[Hcnt1 Hcnt2]".
      iDestruct "Hser" as (? ? s1 s2 [Heqv ->]) "[#Hser1 #Hser2]".
      injection Heqv as -> ->.
      assert (c1 = 0%nat) as -> by lia.
      assert (c2 = 0%nat) as -> by lia.
      v_pures.
      v_bind tᵥ3 (v_sA _).
      iMod ("HvserA" with "Hcnt1 Hser1 Hspec") as "(Hcnt1 & _ & Hspec) /=".
      v_pures.
      v_bind tᵥ3 (v_sB _).
      iMod ("HvserB" with "Hcnt2 Hser2 Hspec") as "(Hcnt2 & _ & Hspec) /=".
      simpl. v_pures.
      iModIntro. iFrame "#". rewrite /prod_ser_str.
      iSplitL "Hcnt1 Hcnt2".
      { iExists 0%nat, 0%nat, _, _. iFrame. iPureIntro. done. }
      repeat (iSplit; eauto).
    - (* 6. v_auth_ser_spec *)
      iIntros (K tᵥ3 a1 a2 a3) "!# #HA Hv".
      rewrite /prod_ser''. v_pures.
      rewrite interp_tern_prod_unfold.
      rewrite interp_var1_ext2 interp_var0_ext1.
      iDestruct "HA" as (??????) "(>-> & >-> & >-> & Ha & Hb)".
      v_pures. v_bind (v_sA _).
      iMod ("HvauthserA" with "Ha Hv") as (?) "[Hserav Hv] /=".
      v_pures. v_bind (v_sB _).
      iMod ("HvauthserB" with "Hb Hv") as (?) "[Hserbv Hv] /=".
      v_pures.
      iModIntro. iFrame.
      iSplit; eauto.
    - (* 7. v_count_spec *)
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
