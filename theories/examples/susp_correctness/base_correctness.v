From auth.prelude Require Import stdpp.
From auth.rel_logic_tern_susp Require Import model interp spec_tactics.
From auth.examples Require Import authentikit authenticatable_base_susp.
From auth.examples.susp_correctness Require Export definitions.


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
      "(#HinvA & #HusserA & #HsserA & #HsuspA & #HunsuspA & HvserA & HvauthserA & HvdeserA & HvcountA)".
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
      "(#HinvB & #HusserB & #HsserB & #HsuspB & #HunsuspB & HvserB & HvauthserB & HvdeserB & HvcountB)".
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
    iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit]]]]]]].
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
      (* Partition γl into γlA ⊎ γlB by where each γ's lb sits in (ua, ub).
         Then split penset_frag, call HreachA/HreachB transformers, recombine.
         TODO: derive the partition + size γlA = c1 ∧ size γlB = c2 + big_sepS split. *)
      admit.
    - (* 3. suspend_spec *)
      iIntros (t v un_v a2 a3 sa Ψ) "!# (%Hunsusp & #HA' & #Hser) HΨ".
      wp_pures.
      iDestruct "HA'" as "[#HA1 [#HA2 #HA3]]".
      interp_unfold! in "HA1".
      (* iEval (cbv [lrel_tern_tern lrel_tern_prod lrel_car]) in "HA1". *)
      iDestruct "HA1" as (wa1 wa2 wa3 wb1 wb2 wb3) "(-> & -> & -> & H1 & H2)".
      destruct t; simpl in Hunsusp.
      { (* tprod *)
        destruct Hunsusp as (? & ? & un_v1 & un_v2 & [= -> ->] & -> & Hunsusp1 & Hunsusp2).
        iSimpl in "Hser".
        iDestruct "Hser" as (? ? sa1 sa2 [[= -> ->] ->]) "[#Hser1 #Hser2]".
        rewrite interp_bin_prod_unfold. rewrite interp_un_prod_unfold.
        (* iEval (cbv [lrel_tern_bin lrel_tern_prod lrel_bin_car]) in "HA2".
        iEval (cbv [lrel_tern_un lrel_tern_prod lrel_un_car]) in "HA3".
        interp_unfold! in "HA2". *)
        iDestruct "HA2" as (? ? ? ?) "(%Heq1 & %Heq2 & #HA2a & #HA2b)".
        injection Heq1 as -> ->. injection Heq2 as -> ->.
        iDestruct "HA3" as (? ? Heq3) "[#HA3a #HA3b]". injection Heq3 as -> ->.
        wp_pures.
        wp_bind (p_spB _).
        wp_apply ("HsuspB" with "[]").
        { iSplit; [done|]. iFrame "Hser2". iNext.
          rewrite interp_var0_ext1.
          iSplit; [|iSplit]. 
          - destruct B; iExact "H2".
          - destruct B; iExact "HA2b".
          - destruct B; iExact "HA3b". }
        iIntros (vb') "(#HBv' & #Hserv'b & Hreal_b)".
        wp_bind (p_spA _).
        wp_apply ("HsuspA" with "[]").
        { iSplit; [done|]. iFrame "Hser1". iNext.
          rewrite interp_var1_ext2.
          iSplit; [|iSplit].
          - destruct A; iExact "H1".
          - destruct A; iExact "HA2a".
          - destruct A; iExact "HA3a". }
        iIntros (va') "(#HAv' & #Hserv'a & Hreal_a)".
        wp_pures. iApply "HΨ". iModIntro. iSplit; [|iSplit].
        - iDestruct "HAv'" as "[#Av1 [#Av2 #Av3]]".
          iDestruct "HBv'" as "[#Bv1 [#Bv2 #Bv3]]".
          iSplit; [|iSplit]; interp_unfold!;
            rewrite interp_var0_ext1; rewrite interp_var1_ext2.
          { iExists _, _, _, _, _, _. do 3 (iSplit; [done|]).
            iSplit; [destruct A; iExact "Av1"|destruct B; iExact "Bv1"]. }
          { iExists _, _, _, _. iSplit; [done|]. iSplit; [done|].
            iSplit; [destruct A; iExact "Av2"|destruct B; iExact "Bv2"]. }
          { iExists _, _. iSplit; [done|].
            iSplit; [destruct A; iExact "Av3"|destruct B; iExact "Bv3"]. }
        - iExists _, _, _, _. iSplit; [done|]. by iSplit.
        - iDestruct "Hreal_a" as (sra ca) "Hra". iDestruct "Hreal_b" as (srb cb) "Hrb".
          iExists (prod_ser_str sra srb), (ca + cb)%nat, ca, cb. iSplit; [done|].
          iExists _, _, _, _. iSplit; [done|]. by iFrame "Hra Hrb". }
      { (* tsum *)
        destruct Hunsusp as [(? & ? & Habs & _) | (? & ? & Habs & _)]; discriminate. }
      { (* tstring *)
        iDestruct "Hser" as %(? & Habs & _); discriminate. }
      { (* tint *)
        iDestruct "Hser" as %(? & Habs & _); discriminate. }
      { (* tauth *) 
        destruct! Hunsusp. simplify_eq.
        rewrite interp_var0_ext1.
        iExFalso. by iApply "HinvB". }
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
    - (* 7. v_deser_spec *)
      (* Spec was substantially rewritten (added m d ps pn c binders,
         visited_map_update_pending, penset/pencount, etc.). *)
      admit.
    - (* 8. v_count_spec *)
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
    iSplit; [|iSplit]; interp_unfold!; last first.
    { (* unary  *) admit. }
    { (* binary *) admit. }
    (* ternary *)
    iIntros (A v1 v2 v3) "!# _"; rewrite -/interp.
    iIntros (????) "Hv Hi Htok".
    rewrite /p_Auth_sum /v_Auth_sum /i_Auth_sum.
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
    rewrite interp_var2_ext3 interp_var1_ext2.
    iDestruct "HA" as "(HA_tern & #HA_bin & #HA_un)".
    iDestruct "HA_tern" as (tA p_ssA p_usA p_spA p_uspA v_sA v_dA v_cA -> ->)
      "(#HinvA & #HusserA & #HsserA & #HsuspA & #HunsuspA & HvserA & HvauthserA & HvdeserA & HvcountA)".
    iIntros (????) "Hv Hi Htok". v_pures; i_pures; wp_pures. iModIntro. iFrame.
    iSplit; [|iSplit]; interp_unfold!; last first.
    { (* inner-after-HA unary *) admit. }
    { (* inner-after-HA binary *) admit. }
    iIntros (vB1 vB2 vB3) "!# #HB".
    interp_unfold! in "HB".
    rewrite interp_var2_ext3 interp_var0_ext1.
    iDestruct "HB" as "(HB_tern & #HB_bin & #HB_un)".
    iDestruct "HB_tern" as (tB p_ssB p_usB p_spB p_uspB v_sB v_dB v_cB -> ->)
      "(#HinvB & #HusserB & #HsserB & #HsuspB & #HunsuspB & HvserB & HvauthserB & HvdeserB & HvcountB)".
    iIntros (????) "Hv Hi Htok".
    rewrite /sum_ser'' /sum_ser /sum_count.
    v_pures; i_pures; wp_pures. iModIntro. iFrame.
    iSplit; [|iSplit]; interp_unfold!; last first.
    { (* final unary  *) admit. }
    { (* final binary *) admit. }
    rewrite interp_var2_ext3.
    iExists (tsum tA tB), _, _, _, _, _, _, _.
    iSplit; [done|]. iSplit; [done|].
    iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit]]]]]]].
    - (* 0. invalid_val *)
      iIntros "!#" (p v2 v3) "HA".
      rewrite interp_tern_sum_unfold.
      iDestruct "HA" as (? ? ?) "[(%Heq & _) | (%Heq & _)]"; discriminate.
    - (* 1. unsusp_p_ser_spec *)
      iIntros (v s Ψ) "!# Hser HΨ".
      iDestruct "Hser" as (w s') "[[Hsera [-> ->]]|[Hserb [-> ->]]]".
      + wp_pures.
        wp_apply ("HusserA" with "Hsera"). iIntros "_". wp_pures.
        unfold inl_ser_str. iApply "HΨ". by iModIntro.
      + wp_pures.
        wp_apply ("HusserB" with "Hserb"). iIntros "_". wp_pures.
        unfold inr_ser_str. iApply "HΨ". by iModIntro.
    - (* 2. susp_p_ser_spec *)
      iIntros (E a1 s c q HE Ψ) "!# (Hser & Htok & Hintr) HΨ".
      iEval (rewrite /susp_ser_p_real /=) in "Hser".
      iDestruct "Hser" as (w s') "[[#Hser1 [-> ->]] | [#Hser2 [-> ->]]]".
      + (* InjL *)
        rewrite /sum_ser''. wp_pures.
        rewrite /sum_ser. wp_pures.
        wp_apply ("HsserA" $! _ _ _ c q with "[//] [$Hser1 $Htok $Hintr]").
        iIntros "(Htok & Hintr & HreachA)". wp_pures.
        rewrite /inl_ser_str. iApply "HΨ". iModIntro. iFrame "Htok Hintr".
        (* Forward γl through HreachA's transformer *)
        admit.
      + (* InjR *)
        rewrite /sum_ser''. wp_pures.
        rewrite /sum_ser. wp_pures.
        wp_apply ("HsserB" $! _ _ _ c q with "[//] [$Hser2 $Htok $Hintr]").
        iIntros "(Htok & Hintr & HreachB)". wp_pures.
        rewrite /inr_ser_str. iApply "HΨ". iModIntro. iFrame "Htok Hintr".
        admit.
    - (* 3. suspend_spec      *)
      iIntros (t v un_v a2 a3 sa Ψ) "!# (%Hunsusp & #HA' & #Hser) HΨ".
      wp_pures.
      iDestruct "HA'" as "[#HA1 [#HA2 #HA3]]".
      rewrite interp_tern_sum_unfold.
      rewrite interp_bin_sum_unfold.
      rewrite interp_un_sum_unfold.
      (* iEval (cbv [lrel_tern_tern lrel_tern_sum lrel_car]) in "HA1".
      iEval (cbv [lrel_tern_bin lrel_tern_sum lrel_bin_car]) in "HA2".
      iEval (cbv [lrel_tern_un lrel_tern_sum lrel_un_car]) in "HA3". *)
      iDestruct "HA1" as (wA wV wI) "[(-> & -> & -> & #H1) | (-> & -> & -> & #H1)]".
      + (* InjL case on v *)
        iDestruct "HA2" as (? ?) "[(%Heq1 & %Heq2 & #HA2L) | (%Heq1 & %Heq2 & _)]";
          last discriminate.
        injection Heq1 as ->. injection Heq2 as ->.
        iDestruct "HA3" as (?) "[(%Heq3 & #HA3L) | (%Heq3 & _)]";
          last discriminate.
        injection Heq3 as ->.
        destruct t; simpl in Hunsusp.
        { (* tprod *)
          destruct Hunsusp as (? & ? & ? & ? & Habs & _); discriminate. }
        { (* tsum *)
          destruct Hunsusp as [(? & un_v1 & [= ->] & -> & Hunsusp1)
                              |(? & ? & Habs & _)]; last discriminate.
          iSimpl in "Hser".
          iDestruct "Hser" as (w s') "[[#Hser1 [%Heqv ->]] | [_ [%Heqv _]]]";
            last discriminate.
          injection Heqv as ->.
          wp_pures.
          wp_apply ("HsuspA" with "[]").
          { iSplit; [done|]. iFrame "Hser1". iNext.
            iSplit; [|iSplit]; rewrite interp_var1_ext2.
            - destruct A; iExact "H1".
            - destruct A; iExact "HA2L".
            - destruct A; iExact "HA3L". }
          iIntros (va') "(#HAv' & #Hserv'a & Hreal_a)".
          wp_pures. iApply "HΨ". iModIntro. iSplit; [|iSplit].
          - iDestruct "HAv'" as "[#Av1 [#Av2 #Av3]]".
            iSplit; [|iSplit]; interp_unfold!;
              rewrite interp_var1_ext2; rewrite interp_var0_ext1.
            { iExists _, _, _. iLeft.
              do 3 (iSplit; [done|]).
              destruct A; iExact "Av1". }
            { iExists _, _. iLeft.
              do 2 (iSplit; [done|]).
              destruct A; iExact "Av2". }
            { iExists _. iLeft.
              iSplit; [done|].
              destruct A; iExact "Av3". }
          - iExists _, _. iLeft. iFrame "Hserv'a". done.
          - iDestruct "Hreal_a" as (sra ca) "Hra".
            iExists (inl_ser_str sra), ca, _, _.
            iLeft. iFrame "Hra". done. }
        { (* tstring *)
          iDestruct "Hser" as %(? & Habs & _); discriminate. }
        { (* tint *)
          iDestruct "Hser" as %(? & Habs & _); discriminate. }
        { (* tauth *)
          destruct Hunsusp as (? & ? & ? & ? & ? & Habs & _); discriminate. }
      + (* InjR case on v *)
        iDestruct "HA2" as (? ?) "[(%Heq1 & _) | (%Heq1 & %Heq2 & #HA2R)]";
          first discriminate.
        injection Heq1 as ->. injection Heq2 as ->.
        iDestruct "HA3" as (?) "[(%Heq3 & _) | (%Heq3 & #HA3R)]";
          first discriminate.
        injection Heq3 as ->.
        destruct t; simpl in Hunsusp.
        { (* tprod *)
          destruct Hunsusp as (? & ? & ? & ? & Habs & _); discriminate. }
        { (* tsum *)
          destruct Hunsusp as [(? & ? & Habs & _)
                              |(? & un_v2 & [= ->] & -> & Hunsusp2)]; first discriminate.
          iSimpl in "Hser".
          iDestruct "Hser" as (w s') "[[_ [%Heqv _]] | [#Hser2 [%Heqv ->]]]";
            first discriminate.
          injection Heqv as ->.
          wp_pures.
          wp_apply ("HsuspB" with "[]").
          { iSplit; [done|]. iFrame "Hser2". iNext.
            iSplit; [|iSplit]; rewrite interp_var0_ext1.
            - destruct B; iExact "H1".
            - destruct B; iExact "HA2R".
            - destruct B; iExact "HA3R". }
          iIntros (vb') "(#HBv' & #Hserv'b & Hreal_b)".
          wp_pures. iApply "HΨ". iModIntro. iSplit; [|iSplit].
          - iDestruct "HBv'" as "[#Bv1 [#Bv2 #Bv3]]".
            iSplit; [|iSplit]; interp_unfold!;
              rewrite interp_var1_ext2; rewrite interp_var0_ext1.
            { iExists _, _, _. iRight.
              do 3 (iSplit; [done|]).
              destruct B; iExact "Bv1". }
            { iExists _, _. iRight.
              do 2 (iSplit; [done|]).
              destruct B; iExact "Bv2". }
            { iExists _. iRight.
              iSplit; [done|].
              destruct B; iExact "Bv3". }
          - iExists _, _. iRight. iFrame "Hserv'b". done.
          - iDestruct "Hreal_b" as (srb cb) "Hrb".
            iExists (inr_ser_str srb), cb, _, _.
            iRight. iFrame "Hrb". done. }
        { (* tstring *)
          iDestruct "Hser" as %(? & Habs & _); discriminate. }
        { (* tint *)
          iDestruct "Hser" as %(? & Habs & _); discriminate. }
        { (* tauth *)
          destruct Hunsusp as (? & ? & ? & ? & ? & Habs & _); discriminate. }
    - (* 4. unsuspend_spec *)
      iIntros (E a1 a2 a3 HE Ψ) "!# (#HA & Htok & Hintr) HΨ".
      wp_pures.
      iDestruct "HA" as "[#HA1 [#HA2 #HA3]]".
      rewrite interp_tern_sum_unfold.
      rewrite interp_bin_sum_unfold.
      rewrite interp_un_sum_unfold.
      iDestruct "HA1" as (wA wV wI) "[(-> & -> & -> & #H1) | (-> & -> & -> & #H1)]".
      + (* InjL case *)
        iDestruct "HA2" as (? ?) "[(%Heq1 & %Heq2 & #HA2L) | (%Heq1 & %Heq2 & _)]";
          last discriminate.
        injection Heq1 as ->. injection Heq2 as ->.
        iDestruct "HA3" as (?) "[(%Heq3 & #HA3L) | (%Heq3 & _)]";
          last discriminate.
        injection Heq3 as ->.
        wp_pures.
        wp_bind (p_uspA _).
        wp_apply ("HunsuspA" with "[//] [$Htok $Hintr]").
        { rewrite interp_var1_ext2.
          iSplit; [|iSplit]; iNext.
          - destruct A; iExact "H1".
          - destruct A; iExact "HA2L".
          - destruct A; iExact "HA3L". }
        iIntros (un_va sa) "(Htok & Hintr & %Hunsuspa & #Hssera)".
        wp_pures. iApply ("HΨ" $! (InjLV un_va) (inl_ser_str sa)).
        iFrame. iModIntro. iSplit.
        { iPureIntro. left. eexists _, un_va. done. }
        iExists un_va, sa. iLeft. iSplit; [iExact "Hssera"|done].
      + (* InjR case *)
        iDestruct "HA2" as (? ?) "[(%Heq1 & _) | (%Heq1 & %Heq2 & #HA2R)]";
          first discriminate.
        injection Heq1 as ->. injection Heq2 as ->.
        iDestruct "HA3" as (?) "[(%Heq3 & _) | (%Heq3 & #HA3R)]";
          first discriminate.
        injection Heq3 as ->.
        wp_pures.
        wp_bind (p_uspB _).
        wp_apply ("HunsuspB" with "[//] [$Htok $Hintr]").
        { rewrite interp_var0_ext1.
          iSplit; [|iSplit]; iNext.
          - destruct B; iExact "H1".
          - destruct B; iExact "HA2R".
          - destruct B; iExact "HA3R". }
        iIntros (un_vb sb) "(Htok & Hintr & %Hunsuspb & #Hsserb)".
        wp_pures. iApply ("HΨ" $! (InjRV un_vb) (inr_ser_str sb)).
        iFrame. iModIntro. iSplit.
        { iPureIntro. right. eexists _, un_vb. done. }
        iExists un_vb, sb. iRight. iSplit; [iExact "Hsserb"|done].
    - (* 5. v_ser_spec *)
      iIntros (K tᵥ3 a s id Nc v_outer) "!# Hcnt #Hser Hspec".
      iDestruct "Hcnt" as "[Hcnt|Hcnt]".
      + iDestruct "Hcnt" as (? ->) "Hcnt".
        iDestruct "Hser" as (w s') "[(#Hser1 & %Heqv & ->) | (_ & %Heqv & _)]";
          last discriminate.
        injection Heqv as ->.
        rewrite /sum_ser'' /sum_ser. v_pures.
        v_bind tᵥ3 (v_sA _).
        iMod ("HvserA" with "Hcnt Hser1 Hspec") as "(Hcnt & _ & Hspec)".
        simpl. v_pures. iModIntro.
        iSplitL "Hcnt".
        { iLeft. iExists _. iSplit; [done|]. iFrame. }
        iFrame. rewrite /inl_ser_str. iExists _, s'. iLeft. iFrame "#". done.
      + iDestruct "Hcnt" as (? ->) "Hcnt".
        iDestruct "Hser" as (w s') "[(_ & %Heqv & _) | (#Hser2 & %Heqv & ->)]";
          first discriminate.
        injection Heqv as ->.
        rewrite /sum_ser'' /sum_ser. v_pures.
        v_bind tᵥ3 (v_sB _).
        iMod ("HvserB" with "Hcnt Hser2 Hspec") as "(Hcnt & _ & Hspec)".
        simpl. v_pures. iModIntro.
        iSplitL "Hcnt".
        { iRight. iExists _. iSplit; [done|]. iFrame. }
        iFrame. rewrite /inr_ser_str. iExists _, s'. iRight. iFrame "#". done.
    - (* 6. v_auth_ser_spec *)
      iIntros (K tᵥ3 a1 a2 a3) "!# #HA Hv".
      rewrite /sum_ser''. v_pures.
      rewrite interp_tern_sum_unfold.
      rewrite interp_var1_ext2 interp_var0_ext1.
      iDestruct "HA" as (???) "[(>-> & >-> & >-> & Ha) | (>-> & >-> & >-> & Hb)]".
      + v_pures. v_bind (v_sA _).
        iMod ("HvauthserA" with "Ha Hv") as (sa) "[Hser_a Hv] /=".
        v_pures. iModIntro. iExists (inl_ser_str sa). iFrame.
        iExists _, sa. iLeft. iFrame. done.
      + v_pures. v_bind (v_sB _).
        iMod ("HvauthserB" with "Hb Hv") as (sb) "[Hser_b Hv] /=".
        v_pures. iModIntro. iExists (inr_ser_str sb). iFrame.
        iExists _, sb. iRight. iFrame. done.
    - (* 7. v_deser_spec      *) admit.
    - (* 8. v_count_spec *)
      iIntros (K tᵥ3 a c id Nc v_outer) "!# Hcnt Hspec".
      rewrite /sum_count. v_pures.
      iDestruct "Hcnt" as "[Hcnt|Hcnt]".
      + iDestruct "Hcnt" as (? ->) "Hcnt".
        v_pures.
        iMod ("HvcountA" with "Hcnt Hspec") as "[Hcnt Hspec]".
        iModIntro. iFrame. iLeft. iExists _. iSplit; [done|]. iFrame.
      + iDestruct "Hcnt" as (? ->) "Hcnt".
        v_pures.
        iMod ("HvcountB" with "Hcnt Hspec") as "[Hcnt Hspec]".
        iModIntro. iFrame. iRight. iExists _. iSplit; [done|]. iFrame.
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
    iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit]]]]]]].
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
    - (* 3. suspend_spec *)
      iIntros (t v un_v a2 a3 sa Ψ) "!# (%Hunsusp & HA & #Hser) HΨ".
      iDestruct "HA" as "[>HAt _]". iSimpl in "HAt".
      iDestruct "HAt" as %(s0 & -> & -> & ->).
      destruct t as [t1 t2 | t1 t2 | | | ]; simpl in Hunsusp; try done.
      + destruct Hunsusp as (? & ? & ? & ? & Heq & _); discriminate.
      + destruct Hunsusp as [(? & ? & Heq & _ & _) | (? & ? & Heq & _ & _)]; discriminate.
      + subst un_v. rewrite /id. wp_pures. iApply "HΨ". iModIntro.
        iSplit; [|iSplit].
        * iSplit; [|iSplit]; iExists s0; done.
        * iExact "Hser".
        * iExists sa, 0%nat. iSplit; [iExact "Hser"|by iPureIntro].
      + iDestruct "Hser" as %(? & Heq & _); done.
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
    - (* 7. v_deser_spec *)
      (* Spec was substantially rewritten (added m d ps pn c binders,
         visited_map_update_pending, penset/pencount, etc.). *)
      admit.
    - (* 8. v_count_spec *)
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
    { (* binary *)
      rewrite /lrel_bi_evidence /=.
      iExists tint, _, _, _, _, _, _, _.
      iSplit; [done|].
      iSplit.
      { iIntros (vint sint Ψ) "!# Hser HΨ".
        iDestruct "Hser" as %(z & -> & ->).
        rewrite /p_Auth_int /int_ser' /int_ser /int_ser_str.
        wp_pures. by iApply "HΨ". }
      iSplit.
      { (* susp_p_ser_spec — spec changed (new c, good_state/bad_state). *)
        admit. }
      iSplit.
      { iIntros (t v un_v a3 Ψ) "!# (%Hunsusp & HA) HΨ". wp_pures.
        iDestruct "HA" as ">HA". iSimpl in "HA".
        iDestruct "HA" as %(z0 & -> & ->).
        destruct t as [t1 t2 | t1 t2 | | | ]; simpl in Hunsusp.
        + destruct Hunsusp as (? & ? & ? & ? & Heq & _); discriminate.
        + destruct Hunsusp as [(? & ? & Heq & _ & _) | (? & ? & Heq & _ & _)]; discriminate.
        + subst un_v. rewrite /id. wp_pures. iApply "HΨ". iModIntro.
          iSplit; [iExists z0; done|].
          iSplit; [iExists z0; done|by iPureIntro].
        + subst un_v. rewrite /id. wp_pures. iApply "HΨ". iModIntro.
          iSplit; [iExists z0; done|].
          iSplit; [iExists z0; done|by iPureIntro].
        + destruct Hunsusp as (? & ? & ? & ? & ? & [Heq _]); discriminate. }
      iIntros (E a1 a3 HE Ψ) "!# [HA Htok] HΨ". wp_pures.
      iDestruct "HA" as ">HA". iSimpl in "HA".
      iDestruct "HA" as %(z0 & -> & ->).
      rewrite /id. wp_pures. iApply ("HΨ" $! _). iFrame. iModIntro. done. }
    (* ternary *)
    rewrite /lrel_tern_evidence /=.
    iExists tint, _, _, _, _, _, _, _.
    iSplit; [done|]. iSplit; [done|].
    iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit]]]]]]].
    - (* 0. invalid_val *)
      iIntros "!#" (p v2 v3) "HA".
      iDestruct "HA" as %(s' & Heq & _). discriminate.
    - (* 1. unsusp_p_ser_spec *)
      iIntros (vint sint Ψ) "!# Hser HΨ".
      iDestruct "Hser" as %(z & -> & ->).
      rewrite /p_Auth_int /int_ser' /int_ser /int_ser_str.
      wp_pures.
      by iApply "HΨ".
    - (* 2. susp_p_ser_spec *)
      iIntros (E a1 s c q HE Ψ) "!# ((Hint & %Hc) & Htok & Hintr) HΨ".
      subst c. iDestruct "Hint" as %(z & -> & ->).
      rewrite /int_ser. wp_pures.
      iApply "HΨ". iModIntro. iFrame "Htok".
      iEval (rewrite -{1}(Qp.div_2 q) intransit_split) in "Hintr".
      iDestruct "Hintr" as "[$ _]".
      iIntros (γl) "Hg Hpen %Hsz Hbig".
      apply size_empty_inv in Hsz. fold_leibniz. subst γl.
      iFrame "Hg Hpen". by rewrite big_sepS_empty.
    - (* 3. suspend_spec *)
      iIntros (t v un_v a2 a3 sa Ψ) "!# (%Hunsusp & HA & #Hser) HΨ".
      iDestruct "HA" as "[>HAt _]". iSimpl in "HAt".
      iDestruct "HAt" as %(z0 & -> & -> & ->).
      destruct t as [t1 t2 | t1 t2 | | | ]; simpl in Hunsusp; try done.
      + destruct Hunsusp as (? & ? & ? & ? & Heq & _); discriminate.
      + destruct Hunsusp as [(? & ? & Heq & _ & _) | (? & ? & Heq & _ & _)]; discriminate.
      + iDestruct "Hser" as %(? & Heq & _); done.
      + subst un_v. rewrite /id. wp_pures. iApply "HΨ". iModIntro.
        iSplit; [|iSplit].
        * iSplit; [|iSplit]; iExists z0; done.
        * iExact "Hser".
        * iExists sa, 0%nat. iSplit; [iExact "Hser"|by iPureIntro].
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
      iDestruct "Hser" as %(z & -> & ->).
      rewrite /int_ser' /int_ser. v_pures. iFrame.
      iModIntro. iExists z. done.
    - (* 6. v_auth_ser_spec *)
      iIntros (K tᵥ a1 a2 a3) "!# #HA Hspec".
      iEval (rewrite /lrel_tern_tern /lrel_int /=) in "HA".
      iDestruct "HA" as ">%H". destruct H as (z' & -> & -> & ->).
      rewrite /int_ser' /int_ser. v_pures. iModIntro.
      iExists (int_ser_str z'). iFrame. iExists z'. done.
    - (* 7. v_deser_spec *)
      (* Spec was substantially rewritten (added m d ps pn c binders,
         visited_map_update_pending, penset/pencount, etc.). *)
      admit.
    - (* 8. v_count_spec *)
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
      "(HinvA & HusserA & HsserA & HsuspA & HunsuspA & HvserA & HvauthserA & HvdeserA & HvcountA)".
    iIntros (????) "Hv Hi Htok". v_pures; i_pures; wp_pures. 
    iModIntro. iFrame. clear.
    iSplit; [|iSplit]; interp_unfold!; last first.
    { (* final unary  *) admit. }
    { (* final binary *) admit. }
    rewrite interp_var1_ext2.
    iExists tA, _, _, _, _, _, _, _.
    iSplit; [done|]. iSplit; [done|].
    iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit]]]]]]].
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
    - (* 3. suspend_spec *)
      iIntros (t v un_v a2 a3 sa Ψ) "!# (%Hunsusp & #HA' & #Hser) HΨ".
      rewrite /rec_fold. wp_pures.
      iEval (rewrite interp_rec_star_unfold) in "HA'".
      interp_unfold! in "HA'".
      rewrite interp_var1_ext2 interp_var0_ext1.
      wp_apply ("HsuspA" with "[$Hser $HA' //]").
      iIntros (v') "(#HAv' & #Hserv' & Hreal)".
      iApply "HΨ". iFrame "# Hreal".
      iEval (rewrite interp_rec_star_unfold).
      interp_unfold!.
      rewrite interp_var1_ext2 interp_var0_ext1.
      rewrite /interp_rec1 /lrel_ktype. done.
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
    - (* 7. v_deser_spec      *) admit.
    - (* 8. v_count_spec *)
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
    iSplit; [|iSplit]; interp_unfold!; last first.
    { (* unary  *) admit. }
    { (* binary *) admit. }
    (* ternary *)
    iIntros (A v1 v2 v3) "!# _"; rewrite -/interp.
    iIntros (????) "Hv Hi Htok".
    rewrite /p_Auth_auth /v_Auth_auth /i_Auth_auth.
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame.
    iSplit; [|iSplit]; interp_unfold!; last first.
    { (* final unary  *) admit. }
    { (* final binary *) admit. }
    rewrite interp_var1_ext2.
    iExists tauth, _, _, _, _, _, _, _.
    iSplit; [done|]. iSplit; [done|].
    iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit]]]]]]].
    - (* 0. invalid_val *)
      iIntros "!#" (p w2 w3) "HA".
      rewrite interp_var3_ext4 interp_var0_ext1.
      iSimpl in "HA".
      iDestruct "HA" as (t v2' a1 a2 un_a1 s) "(_ & _ & _ & Hauth_pv)".
      iDestruct "Hauth_pv" as (lb lr ps) "[%Heq _]". discriminate.
    - (* 1. unsusp_p_ser_spec *)
      iIntros (vau sau Ψ) "!# Hser HΨ".
      iSimpl in "Hser". iDestruct "Hser" as %(a & h & -> & ->).
      rewrite /authenticatable_base_susp.auth_unsusp_ser_p. wp_pures.
      rewrite /option_serialization /s_serializer' /= /option_ser''' /string_ser' /string_ser.
      wp_pures. rewrite /simple_string /some_ser_str /string_ser_str.
      iApply "HΨ". done.
    - (* 2. susp_p_ser_spec *)
      iIntros (E a1 sa c q HE Ψ) "!# (Hser & Htok & Hintr) HΨ".
      rewrite /authenticatable_base_susp.auth_susp_ser_p.
      iEval (rewrite /susp_ser_p_real /=) in "Hser".
      iDestruct "Hser" as "[[Hfill ->]|[Hemp ->]]".
      + (* fill, c=0 *)
        iDestruct "Hfill" as (p lb lr a h r) "([-> ->] & _ & #Hinv)".
        wp_pures.
        iMod (na_inv_acc with "Hinv Htok") as "(HI & Htok & Hclose)";
          [solve_ndisj|solve_ndisj|].
        iDestruct "HI" as "(>Hlb & >HD)".
        iEval (rewrite -{1}(Qp.div_2 q) intransit_split) in "Hintr".
        iDestruct "Hintr" as "[Hkeep Hdonate]".
        iDestruct "HD" as "[(%bs1 & Hlr & Hpb) | [(%bs2 & Hlr & Hpb) | [[Hlr Hpb] | (%bs4 & %q4 & %b4 & Hlr & Hpb & Hintr4)]]]".
        * (* D1: lr false, fill_proph_bs head false — contradicts NONE resolve *)
          iDestruct "Hpb" as "[(%us & Hp & %Hbs) %Heq]".
          wp_apply (wp_resolve_proph with "Hp"). iIntros (us') "[%Husfm Hp]".
          destruct Heq as [bs' Heq].
          rewrite Husfm in Hbs. simpl in Hbs.
          rewrite Hbs in Heq. discriminate.
        * (* D2: lr true → close into D4 with lr=true *)
          iDestruct "Hpb" as (us) "[Hp %Hbs]".
          wp_apply (wp_resolve_proph with "Hp"). iIntros (us') "[%Husfm Hp]".
          subst us. simpl in Hbs. subst bs2. wp_pures.
          wp_bind (! _)%E. wp_load. wp_pures.
          rewrite /auth_scheme /option_serialization_scheme /option_serialization /s_serializer.
          rewrite /option_ser'. wp_pures.
          rewrite /string_ser. wp_pures.
          iMod ("Hclose" with "[Hlb Hlr Hp Hdonate $Htok]") as "Htok".
          { iNext. iFrame "Hlb". iRight. iRight. iRight.
            iExists (longest_valid_prefix_bool (map snd us')), (q/2)%Qp, true.
            iFrame "Hlr Hdonate". iExists us'. iFrame. done. }
          iApply "HΨ". iModIntro. iFrame "Htok Hkeep".
          iIntros (γl) "Hg Hpen %Hsz Hbig".
          apply size_empty_inv in Hsz. fold_leibniz. subst γl.
          iFrame "Hg Hpen". by rewrite big_sepS_empty.
        * (* D3: lr false, empty_proph_bs → close into D4 with lr=false *)
          iDestruct "Hpb" as (us) "[Hp %Hbs]".
          wp_apply (wp_resolve_proph with "Hp"). iIntros (us') "[%Husfm Hp]".
          subst us. wp_pures.
          wp_bind (! _)%E. wp_load. wp_pures.
          rewrite /auth_scheme /option_serialization_scheme /option_serialization /s_serializer.
          rewrite /option_ser'. wp_pures.
          rewrite /string_ser. wp_pures.
          iMod ("Hclose" with "[Hlb Hlr Hp Hdonate $Htok]") as "Htok".
          { iNext. iFrame "Hlb". iRight. iRight. iRight.
            iExists (longest_valid_prefix_bool (map snd us')), (q/2)%Qp, false.
            iFrame "Hlr Hdonate". iExists us'. iFrame. done. }
          iApply "HΨ". iModIntro. iFrame "Htok Hkeep".
          iIntros (γl) "Hg Hpen %Hsz Hbig".
          apply size_empty_inv in Hsz. fold_leibniz. subst γl.
          iFrame "Hg Hpen". by rewrite big_sepS_empty.
        * (* D4: already deposited — combine our piece with existing, preserve b4 *)
          iDestruct "Hpb" as (us) "[Hp %Hbs]".
          wp_apply (wp_resolve_proph with "Hp"). iIntros (us') "[%Husfm Hp]".
          subst us. wp_pures.
          wp_bind (! _)%E. wp_load. wp_pures.
          rewrite /auth_scheme /option_serialization_scheme /option_serialization /s_serializer.
          rewrite /option_ser'. wp_pures.
          rewrite /string_ser. wp_pures.
          iCombine "Hdonate Hintr4" as "Hcombined".
          iMod ("Hclose" with "[Hlb Hlr Hp Hcombined $Htok]") as "Htok".
          { iNext. iFrame "Hlb". iRight. iRight. iRight.
            iExists (longest_valid_prefix_bool (map snd us')), (q/2 + q4)%Qp, b4.
            iFrame "Hlr Hcombined". iExists us'. iFrame. done. }
          iApply "HΨ". iModIntro. iFrame "Htok Hkeep".
          iIntros (γl) "Hg Hpen %Hsz Hbig".
          apply size_empty_inv in Hsz. fold_leibniz. subst γl.
          iFrame "Hg Hpen". by rewrite big_sepS_empty.
      + (* emp, c=1 *)
        iDestruct "Hemp" as (p lb lr a h r) "([-> ->] & #Hinv)".
        wp_pures.
        iMod (na_inv_acc with "Hinv Htok") as "(HI & Htok & Hclose)";
          [solve_ndisj|solve_ndisj|].
        iDestruct "HI" as "[(%bs1 & >Hlb & >Hlr & >Hupb) | (%r' & %bs2 & %n & %γ & >Hlb & >Hlr & >Hpb & #Hlg & #Hgood)]".
        * (* D1: unfill_proph_bs has bs = true :: _ — contradicts NONE resolve *)
          iDestruct "Hupb" as "((%us & Hp & %Hbs) & %Heq)".
          wp_apply (wp_resolve_proph with "Hp"). iIntros (us') "[%Husfm Hp]".
          destruct Heq as [bs' Heq].
          rewrite Husfm in Hbs. simpl in Hbs.
          rewrite Hbs in Heq. discriminate.
        * (* D2: lb=true, persistent good→good*reach *)
          iDestruct "Hpb" as "(%us & Hp & %Hbs)".
          wp_apply (wp_resolve_proph with "Hp"). iIntros (us') "[%Husfm Hp]".
          subst us. simpl in Hbs. subst bs2.
          wp_pures. wp_load. wp_pures.
          rewrite /auth_scheme /option_serialization_scheme /option_serialization /s_serializer.
          rewrite /option_ser'. wp_pures.
          iMod ("Hclose" with "[Hlb Hlr Hp $Htok]") as "Htok".
          { iNext. iRight. iExists r', (longest_valid_prefix_bool (map snd us')), n, γ.
            iFrame "Hlb Hlr Hlg Hgood". iExists us'. iFrame. done. }
          iApply "HΨ". iModIntro. iFrame "Htok".
          iEval (rewrite -{1}(Qp.div_2 q) intransit_split) in "Hintr".
          iDestruct "Hintr" as "[Hkeep _]". iFrame "Hkeep".
          iIntros (γl) "Hg Hpen %Hsz Hbig".
          (* c=1 ⇒ γl is a singleton {[γ']}. Discharging size_inv via TODO. *)
          admit.
    - (* 3. suspend_spec      *) admit.
    - (* 4. unsuspend_spec    *) admit.
    - (* 5. v_ser_spec        *) admit.
    - (* 6. v_auth_ser_spec   *) admit.
    - (* 7. v_deser_spec      *) admit.
    - (* 8. v_count_spec *) admit.
      (* iIntros (K tx a c id Nc v_outer) "!# Hcnt Hspec".
      rewrite /= /auth_sub_susp_count_frags.
      iDestruct "Hcnt" as (w1 ->) "[Hvalid|Hvalid]".
      { iDestruct "Hvalid" as %(h & -> & ->).
        rewrite /auth_count. v_pures. iModIntro. iFrame.
        iExists (InjLV #h). iSplit; [done|].
        iLeft. iExists h. done. }
      iDestruct "Hvalid" as (susp ->) "[Hv|Hv]".
      { iDestruct "Hv" as (h) "[Hsusp ->]".
        rewrite /auth_count. v_pures. v_load. v_pures. iModIntro. iFrame.
        iExists (InjRV #susp).
        iSplit; [done|]. iRight. iExists susp. iSplit; [done|].
        iLeft. iExists h. iFrame. done. }
      iDestruct "Hv" as (p γ) "(Hlg & Hsusp & -> & Hmf & Hcap2 & Hos)".
      rewrite /auth_count. v_pures. v_load. v_pures. iModIntro. iFrame.
      iExists (InjRV #susp).
      iSplit; [done|]. iRight. iExists susp. iSplit; [done|].
      iRight. iExists p, γ. iFrame. done. *)
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