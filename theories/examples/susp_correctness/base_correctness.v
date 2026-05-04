From auth.prelude Require Import stdpp.
From auth.rel_logic_tern_susp Require Import model interp spec_tactics.
From iris.algebra Require Import gset auth.
From auth.examples Require Import authentikit authenticatable_base_susp.
From auth.examples.susp_correctness Require Export definitions helpers.


Section authenticatable.
  Context `{!authG Σ, !seqG Σ, !visited_mapG Σ, !lg_mapG Σ, !mapG Σ, !capG Σ, !intransitG Σ, !stateG Σ} (N : namespace).
  

  (* refines_Auth_pair proof outline.

     The statement is the relational interpretation of
       ∀ α β, evidence α → evidence β → evidence (α * β)
     applied to the prover/verifier/ideal pair-combinators.  After the
     [lrel_tern_as_lrel] coercion the goal is a 3-way conjunction

       lrel_tern_tern (⟦…⟧ Δ) p v i
       ∧ lrel_tern_bin  (⟦…⟧ Δ) p i
       ∧ lrel_tern_un   (⟦…⟧ Δ) v

     We split these via [iSplit; [|iSplit]] and only attempt the
     ternary branch; the binary and unary branches are [admit]ed per
     the task scope.

     The ternary branch itself fans out further.  At each intermediate
     arrow (outer ∀α, inner ∀β, after introducing the evidence for α,
     after introducing the evidence for β) the return relation is
     again a [lrel_tern_as_lrel] applied to three values, producing
     another 3-way conjunction that must be split; the binary and
     unary sub-goals at each level are locally [admit]ed.

     Finally, at the innermost ternary obligation the goal is
     [lrel_tern_evidence (lrel_tern_prod A B)] applied to the
     pair-building closures, which bundles eight specs (see
     [lrel_tern_evidence] at line ~1173):

       1. unsusp_p_ser_spec  — [prod_ser''] on fully-unsuspended pair
       2. susp_p_ser_spec    — [prod_ser''] on real-suspended pair
       3. suspend_spec       — pair-[suspend] preserves A
       4. unsuspend_spec     — pair-[unsuspend] preserves A
       5. v_ser_spec         — verifier [prod_ser''] on pair after proph
       6. v_auth_ser_spec    — verifier ser from A pointer
       7. v_deser_spec       — verifier [prod_deser] reconstruction
       8. v_count_spec       — [prod_count] sums component counts

     Each sub-proof destructures a [prod_is_ser' / prod_valid_val' /
     sub_susp_count] witness at the [tprod] case, steps through the
     combinator wrapper, chains the corresponding component spec from
     [HA]/[HB], and reassembles the pair at the post-condition.  The
     deserialization obligation (7) routes through
     [prod_deser'_complete] (serialization_susp.v:837).

     This is a substantial piece of work (on the order of several
     hundred Iris tactic lines); the structure is recorded here in
     comments and in the plan file for follow-up, and the whole lemma
     stays [Admitted] for now. *)
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
      admit.
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

  Lemma refines_Auth_sum Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆; ⋆, var2 var1 → var2 var0 → var2 (var1 + var0) ⟧
      (ext Δ (lrel_evidence N)) p_Auth_sum v_Auth_sum i_Auth_sum.
  Proof.

  Admitted.

  Lemma refines_Auth_string :
    ⊢ (lrel_evidence N) (LRelTern lrel_string lrel_bin_string lrel_un_string)
        p_Auth_string v_Auth_string i_Auth_string.
  Proof.
    iSplit; [|iSplit]; last first.
    { (* unary  *) admit. }
    { (* binary *)
      rewrite /lrel_bi_evidence /=.
      iExists tstring, _, _, _, _, _, _, _.
      iSplit; [done|].
      iSplit.
      { iIntros (vstr sstr Ψ) "!# Hser HΨ".
        iDestruct "Hser" as %(s' & -> & ->).
        rewrite /p_Auth_string /string_ser' /string_ser /string_ser_str.
        wp_pures. by iApply "HΨ". }
      iSplit.
      { (* susp_p_ser_spec — spec changed (new c, good_state/false_state). *)
        admit. }
      iSplit.
      { iIntros (t v un_v a3 Ψ) "!# (%Hunsusp & HA) HΨ". wp_pures.
        iDestruct "HA" as ">HA". iSimpl in "HA".
        iDestruct "HA" as %(s0 & -> & ->).
        destruct t as [t1 t2 | t1 t2 | | | ]; simpl in Hunsusp.
        + destruct Hunsusp as (? & ? & ? & ? & Heq & _); discriminate.
        + destruct Hunsusp as [(? & ? & Heq & _ & _) | (? & ? & Heq & _ & _)]; discriminate.
        + subst un_v. rewrite /id. wp_pures. iApply "HΨ". iModIntro.
          iSplit; [iExists s0; done|].
          iSplit; [iExists s0; done|by iPureIntro].
        + subst un_v. rewrite /id. wp_pures. iApply "HΨ". iModIntro.
          iSplit; [iExists s0; done|].
          iSplit; [iExists s0; done|by iPureIntro].
        + destruct Hunsusp as (? & ? & ? & ? & ? & [Heq _]); discriminate. }
      iIntros (E a1 a3 HE Ψ) "!# [HA Htok] HΨ". wp_pures.
      iDestruct "HA" as ">HA". iSimpl in "HA".
      iDestruct "HA" as %(s0 & -> & ->).
      rewrite /id. wp_pures. iApply ("HΨ" $! _). iFrame. iModIntro. done. }
    (* ternary *)
    rewrite /lrel_tern_evidence /=.
    iExists tstring, _, _, _, _, _, _, _.
    iSplit; [done|]. iSplit; [done|].
    iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit]]]]]].
    - (* 0. invalid_val *)
      iIntros "!#" (p v2 v3) "HA".
      iDestruct "HA" as %(s' & Heq & _). discriminate.
    - (* 1. unsusp_p_ser_spec *)
      iIntros (vstr sstr Ψ) "!# Hser HΨ".
      iDestruct "Hser" as %(s' & -> & ->).
      rewrite /p_Auth_string /string_ser' /string_ser /string_ser_str.
      wp_pures.
      by iApply "HΨ".
    - (* 2. susp_p_ser_spec *)
      iIntros (E a1 s c q HE Ψ) "!# ((Hstr & %Hc) & Htok & Hintr) HΨ".
      subst c. iDestruct "Hstr" as %(s' & -> & ->).
      rewrite /string_ser. wp_pures.
      iApply "HΨ". iModIntro. iFrame "Htok".
      iEval (rewrite -{1}(Qp.div_2 q) intransit_split) in "Hintr".
      iDestruct "Hintr" as "[$ _]".
      iIntros (γl) "Hg Hpen %Hsz Hbig".
      apply size_empty_inv in Hsz. fold_leibniz. subst γl.
      iFrame "Hg Hpen". by rewrite big_sepS_empty.
    - (* 3. suspend_v_deser_spec (combined) *)
      iIntros "!#" (t' a1 un_a1 a2 a3 s_def s_pred K tᵥ pid m d ps pn mlg) "Hv".
      v_pures.
      iModIntro. iExists string_deser. iFrame "Hv".
      iIntros (Ψ) "!# (%Hunsusp & #HA & #Hser & Hvm & Hauth & Hv) HΨ".
      iDestruct "HA" as "[>HAt _]". iSimpl in "HAt".
      iDestruct "HAt" as %(s0 & -> & -> & ->).
      destruct t' as [t1 t2 | t1 t2 | | | ]; simpl in Hunsusp; try done.
      + destruct Hunsusp as (? & ? & ? & ? & Heq & _); discriminate.
      + destruct Hunsusp as [(? & ? & Heq & _ & _) | (? & ? & Heq & _ & _)]; discriminate.
      + (* tstring *) subst un_a1.
        rewrite /id. wp_pures.
        iDestruct "Hser" as %(s' & Heq & ->).
        injection Heq as Hs'. subst s'.
        (* s_def = string_ser_str s0 = s_real (since c=0, no realization shift). *)
        destruct (decide (s_pred = string_ser_str s0)) as [Heq|Hne].
        * (* Match branch *)
          subst s_pred.
          iAssert (string_is_ser' (string_ser_str s0)) as %Hsis.
          { iPureIntro. by exists s0. }
          iMod (string_deser_spec' ⊤ _ () (λ v, ⌜v = SOMEV #s0⌝)%I
                 with "[//] [] [$Hv //]") as (?) "[Hv ->]".
          { iIntros "!#" (v) "%Hv".
            destruct Hv as (s' & -> & Hs0_ss). simpl in Hs0_ss.
            injection Hs0_ss as Hs0. by subst s'. }
          iMod (own_unit pending_setUR pending_set_name) as "Hpe".
          iApply ("HΨ" $! #s0 (string_ser_str s0) 0%nat).
          iModIntro.
          iSplitL "";
            [iSplit; [iPureIntro; by exists s0|iPureIntro; eauto]|].
          iLeft. iSplit; [done|]. iExists ∅, mlg, #s0.
          iFrame "Hauth".
          iSplit; [iPureIntro; rewrite size_empty; lia|].
          iSplitL "Hpe"; [iExact "Hpe"|].
          iSplit.
          { iSplit; [iExists s0; done|].
            iSplit; [iExists s0; done|]. by iExists s0. }
          iSplit; [iPureIntro; by exists s0|].
          iFrame "Hv".
          iSplit; [rewrite big_sepS_empty; done|].
          iSplit; [iSplit; [iExists s0; done|by iPureIntro]|].
          iSplit; [iPureIntro; by exists s0|].
          rewrite visited_map_update_pending_rewrite. rewrite size_empty.
          replace (ps ∪ ∅) with ps by set_solver.
          replace (pn + 0) with pn by lia.
          rewrite (set_fold_empty (λ γ m, <[γ := pending_val]> m) m).
          iExact "Hvm".
        * (* Mismatch branch *)
          iApply ("HΨ" $! #s0 (string_ser_str s0) 0%nat).
          iModIntro.
          iSplitL "";
            [iSplit; [iPureIntro; by exists s0|iPureIntro; eauto]|].
          iRight. iSplit; [iPureIntro; auto|].
          iExists s0. done.
      + (* tint: contradicts string serialization *)
        iDestruct "Hser" as %(? & Heq & _); done.
      + destruct Hunsusp as (? & ? & ? & ? & ? & Heq & _); discriminate.
    - (* 4. unsuspend_spec *)
      iIntros (E a1 a2 a3 HE Ψ) "!# (HA & Htok & Hintr) HΨ".
      iDestruct "HA" as "[>HAt _]". iSimpl in "HAt".
      iDestruct "HAt" as %(s0 & -> & -> & ->).
      rewrite /id. wp_pures.
      iApply ("HΨ" $! _ (string_ser_str s0)).
      iFrame. iModIntro. iSplit; [done|]. iExists s0. done.
    - (* 5. v_ser_spec *)
      iIntros (K tᵥ a s id Nc v_outer) "!# Hcnt Hser Hspec".
      iDestruct "Hser" as %(s' & -> & ->).
      rewrite /string_ser' /string_ser. v_pures. iFrame.
      iModIntro. iExists s'. done.
    - (* 6. v_auth_ser_spec *)
      iIntros (K tᵥ a1 a2 a3) "!# #HA Hspec".
      iEval (rewrite /lrel_tern_tern /lrel_string /=) in "HA".
      iDestruct "HA" as ">%H". destruct H as (s' & -> & -> & ->).
      rewrite /string_ser' /string_ser. v_pures. iModIntro.
      iExists (string_ser_str s'). iFrame. iExists s'. done.
    - (* 7. v_count_spec *)
      iIntros (K tᵥ a c id Nc v_outer) "!# Hcnt Hspec".
      iDestruct "Hcnt" as "[Hvv %Hc]". subst c.
      rewrite /string_count /int_count. v_pures.
      iModIntro. iFrame. done.
  Admitted.

  Lemma refines_Auth_int :
    ⊢ (lrel_evidence N) (LRelTern lrel_int lrel_bin_int lrel_un_int)
        p_Auth_int v_Auth_int i_Auth_int.
  Proof.
    iSplit; [|iSplit]; last first.
    { (* unary  *) admit. }
    { (* binary *) admit. }
    (* ternary *)
    rewrite /lrel_tern_evidence /=.
    iExists tint, _, _, _, _, _, _, _.
    iSplit; [done|]. iSplit; [done|].
    iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit]]]]]].
    - (* 0. invalid_val *)
      iIntros "!#" (p v2 v3) "HA".
      iDestruct "HA" as %(z & Heq & _). discriminate.
    - (* 1. unsusp_p_ser_spec *) admit.
    - (* 2. susp_p_ser_spec *) admit.
    - (* 3. suspend_v_deser_spec (combined) *)
      iIntros "!#" (t' a1 un_a1 a2 a3 s_def s_pred K tᵥ pid m d ps pn mlg) "Hv".
      v_pures.
      iModIntro. iExists int_deser. iFrame "Hv".
      iIntros (Ψ) "!# (%Hunsusp & #HA & #Hser & Hvm & Hauth & Hv) HΨ".
      iDestruct "HA" as "[>HAt _]". iSimpl in "HAt".
      iDestruct "HAt" as %(z0 & -> & -> & ->).
      destruct t' as [t1 t2 | t1 t2 | | | ]; simpl in Hunsusp; try done.
      + destruct Hunsusp as (? & ? & ? & ? & Heq & _); discriminate.
      + destruct Hunsusp as [(? & ? & Heq & _ & _) | (? & ? & Heq & _ & _)]; discriminate.
      + (* tstring: contradicts int serialization *)
        iDestruct "Hser" as %(? & Heq & _); done.
      + (* tint *) subst un_a1.
        rewrite /id. wp_pures.
        iDestruct "Hser" as %(z' & Heq & ->).
        injection Heq as Hz'. subst z'.
        destruct (decide (s_pred = int_ser_str z0)) as [Heq|Hne].
        * (* Match branch *)
          subst s_pred.
          iAssert (int_is_ser' (int_ser_str z0)) as %Hsis.
          { iPureIntro. by exists z0. }
          iMod (int_deser_spec' ⊤ _ () (λ v, ⌜v = SOMEV #z0⌝)%I
                 with "[//] [] [$Hv //]") as (?) "[Hv ->]".
          { iIntros "!#" (v) "%Hv".
            destruct Hv as (z' & -> & Hz0_zs). simpl in Hz0_zs.
            unfold int_ser_str in Hz0_zs.
            apply String.app_inj in Hz0_zs.
            apply (inj StringOfZ) in Hz0_zs. by subst z'. }
          iMod (own_unit pending_setUR pending_set_name) as "Hpe".
          iApply ("HΨ" $! #z0 (int_ser_str z0) 0%nat).
          iModIntro.
          iSplitL "";
            [iSplit; [iPureIntro; by exists z0|iPureIntro; eauto]|].
          iLeft. iSplit; [done|]. iExists ∅, mlg, #z0.
          iFrame "Hauth".
          iSplit; [iPureIntro; rewrite size_empty; lia|].
          iSplitL "Hpe"; [iExact "Hpe"|].
          iSplit.
          { iSplit; [iExists z0; done|].
            iSplit; [iExists z0; done|]. by iExists z0. }
          iSplit; [iPureIntro; by exists z0|].
          iFrame "Hv".
          iSplit; [rewrite big_sepS_empty; done|].
          iSplit; [iSplit; [iExists z0; done|by iPureIntro]|].
          iSplit; [iPureIntro; by exists z0|].
          rewrite visited_map_update_pending_rewrite. rewrite size_empty.
          replace (ps ∪ ∅) with ps by set_solver.
          replace (pn + 0) with pn by lia.
          rewrite (set_fold_empty (λ γ m, <[γ := pending_val]> m) m).
          iExact "Hvm".
        * (* Mismatch branch *)
          iApply ("HΨ" $! #z0 (int_ser_str z0) 0%nat).
          iModIntro.
          iSplitL "";
            [iSplit; [iPureIntro; by exists z0|iPureIntro; eauto]|].
          iRight. iSplit; [iPureIntro; auto|].
          iExists z0. done.
      + destruct Hunsusp as (? & ? & ? & ? & ? & Heq & _); discriminate.
    - (* 4. unsuspend_spec *)
      iIntros (E a1 a2 a3 HE Ψ) "!# (HA & Htok & Hintr) HΨ".
      iDestruct "HA" as "[>HAt _]". iSimpl in "HAt".
      iDestruct "HAt" as %(z0 & -> & -> & ->).
      rewrite /id. wp_pures.
      iApply ("HΨ" $! _ (int_ser_str z0)).
      iFrame. iModIntro. iSplit; [done|]. iExists z0. done.
    - (* 5. v_ser_spec *)
      iIntros (K tᵥ a s id Nc v_outer) "!# Hcnt Hser Hspec".
      iDestruct "Hser" as %(z' & -> & ->).
      rewrite /int_ser' /int_ser. v_pures. iFrame.
      iModIntro. iExists z'. done.
    - (* 6. v_auth_ser_spec *)
      iIntros (K tᵥ a1 a2 a3) "!# #HA Hspec".
      iEval (rewrite /lrel_tern_tern /lrel_int /=) in "HA".
      iDestruct "HA" as ">%H". destruct H as (z' & -> & -> & ->).
      rewrite /int_ser' /int_ser. v_pures. iModIntro.
      iExists (int_ser_str z'). iFrame. iExists z'. done.
    - (* 7. v_count_spec *)
      iIntros (K tᵥ a c id Nc v_outer) "!# Hcnt Hspec".
      iDestruct "Hcnt" as "[Hvv %Hc]". subst c.
      rewrite /int_count. v_pures.
      iModIntro. iFrame. done.
  Admitted.

  Lemma refines_Auth_mu Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆ ⇒ ⋆, var1 (var0 (μ: ⋆; var1 var0)) → var1 (μ: ⋆; var1 var0) ⟧
      (ext Δ (lrel_evidence N)) p_Auth_mu v_Auth_mu i_Auth_mu.
  Proof.
    iSplit; [|iSplit]; interp_unfold!; last first.
    { (* unary  *) admit. }
    { (* binary *) admit. }
    (* ternary *)
    iIntros (A v1 v2 v3) "!# _"; rewrite -/interp.
    iIntros (????) "Hv Hi Htok".
    rewrite /p_Auth_mu /v_Auth_mu /i_Auth_mu.
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame.
    iSplit; [|iSplit]; interp_unfold!; last first.
    { (* inner-after-A unary *) admit. }
    { (* inner-after-A binary *) admit. }
    iIntros (vA1 vA2 vA3) "!# #HA".
    interp_unfold! in "HA".
    iDestruct "HA" as "(HA_tern & #HA_bin & #HA_un)".
    rewrite interp_var1_ext2 interp_var0_ext1.
    iDestruct "HA_tern" as (tA p_ssA p_usA p_spA p_uspA v_sA v_dA v_cA -> ->)
      "(HinvA & HusserA & HsserA & HsuspvdeserA & HunsuspA & HvserA & HvauthserA & HvcountA)".
    iIntros (????) "Hv Hi Htok". v_pures; i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iSplit; [|iSplit]; interp_unfold!; last first.
    { (* final unary  *) admit. }
    { (* final binary *) admit. }
    rewrite interp_var1_ext2.
    iExists tA, _, _, _, _, _, _, _.
    iSplit; [done|]. iSplit; [done|].
    iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit]]]]]].
    - (* 0. invalid_val *) admit.
    - (* 1. unsusp_p_ser_spec *)
      iIntros (vmu smu Ψ) "!# Hser HΨ".
      rewrite /rec_fold. wp_pures.
      wp_apply ("HusserA" with "Hser"). iIntros "_".
      by iApply "HΨ".
    - (* 2. susp_p_ser_spec *)
      iIntros (E a1 s c q HE Ψ) "!# (Hser & Htok & Hintr) HΨ".
      rewrite /rec_fold. wp_pures.
      wp_apply ("HsserA" $! _ _ _ c q with "[//] [$Hser $Htok $Hintr]").
      iIntros "(Htok & Hintr & HreachA)".
      iApply "HΨ". iFrame.
    - (* 3. suspend_v_deser_spec (combined) *)
      admit.
    - (* 4. unsuspend_spec *)
      iIntros (E a1 a2 a3 HE Ψ) "!# (#HA & Htok & Hintr) HΨ".
      rewrite /rec_fold. wp_pures.
      iEval (rewrite interp_rec_star_unfold) in "HA".
      interp_unfold! in "HA".
      rewrite interp_var1_ext2 interp_var0_ext1.
      wp_apply ("HunsuspA" with "[//] [$Htok $HA $Hintr]").
      iIntros (un_v s) "(Htok & Hintr & %Hunsusp & #Hser)".
      iApply ("HΨ" $! un_v s). iFrame. iFrame "#". done.
    - (* 5. v_ser_spec *)
      iIntros (K tᵥ1 a s id Nc v_outer) "!# Hcnt Hser Hspec".
      v_pures.
      by iApply ("HvserA" with "Hcnt Hser Hspec").
    - (* 6. v_auth_ser_spec   *) admit.
    - (* 7. v_count_spec *)
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
    ext (ext (ext Δ (lrel_auth N)) R) (lrel_evidence N).

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