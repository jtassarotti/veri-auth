From auth.prelude Require Import stdpp.
From auth.rel_logic_tern_susp Require Import model interp spec_tactics.
From iris.algebra Require Import gset auth.
From auth.examples Require Import authentikit authenticatable_base_susp.
From auth.examples.susp_correctness Require Export definitions helpers.


Section authenticatable.
  Context `{!authG Σ, !seqG Σ, !correctnessG Σ}.

  Local Typeclasses Opaque susp_p_ser_spec unsusp_p_ser_spec suspend_v_deser_spec
        unsuspend_spec v_ser_spec auth_ser_spec v_count_spec.

  (** Unary (prover-only) evidence for the sum. Discharges every tern/un
      split in [refines_Auth_sum] (mirrors the security file's
      [refines_un_Auth_sum]); the conclusion's closures are what
      [p_Auth_sum]'s body reduces to on the given component values. *)
  Lemma refines_un_Auth_sum Θ (Δ : ctxO Σ Θ) (A B : kindO Σ ⋆)
      (p_ssA p_usA p_spA p_uspA p_ssB p_usB p_spB p_uspB : val) :
    lrel_tern_un (lrel_evidence A) (p_ssA, p_usA, p_spA, p_uspA)%V -∗
    lrel_tern_un (lrel_evidence B) (p_ssB, p_usB, p_spB, p_uspB)%V -∗
    lrel_tern_un
      (lrel_evidence (⟦ var1 + var0 ⟧ (ext (ext (ext Δ lrel_evidence) A) B)))
      (λ: "v",
         match: "v" with
           InjL "x" => #"L" ^ #"_" ^ p_ssA "x"
         | InjR "x" => #"R" ^ #"_" ^ p_ssB "x"
         end,
       λ: "v",
         match: "v" with
           InjL "x" => #"L" ^ #"_" ^ p_usA "x"
         | InjR "x" => #"R" ^ #"_" ^ p_usB "x"
         end,
       λ: "a",
         match: "a" with
           InjL "a" => InjL (p_spA "a")
         | InjR "b" => InjR (p_spB "b")
         end,
       λ: "a",
         match: "a" with
           InjL "a" => InjL (p_uspA "a")
         | InjR "b" => InjR (p_uspB "b")
         end)%V.
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
    iExists (tsum tA tB), _, _, _, _, #(), #(), #().
    iSplit; [done|]. iSplit; [|iSplit; [|iSplit]].
    - (* unsusp_p_ser_spec *)
      rewrite /unsusp_p_ser_spec.
      iIntros (v s Ψ) "!# Hser HΨ".
      iDestruct "Hser" as (w s') "[[Husser %HeqL] | [Husser %HeqR]]".
      + destruct HeqL as [-> ->]. wp_pures.
        wp_apply ("HusserA" with "Husser"). iIntros "_". wp_pures.
        unfold inl_ser_str. iApply "HΨ". by iModIntro.
      + destruct HeqR as [-> ->]. wp_pures.
        wp_apply ("HusserB" with "Husser"). iIntros "_". wp_pures.
        unfold inr_ser_str. iApply "HΨ". by iModIntro.
    - (* susp_p_ser_spec *)
      rewrite /susp_p_ser_spec.
      iIntros (E a1 s c q HE Ψ) "!# (Hser & Htok & Hintr) HΨ".
      iEval (rewrite /susp_ser_p_real /=) in "Hser".
      iDestruct "Hser" as (w s') "[[#Hser1 [-> ->]] | [#Hser1 [-> ->]]]".
      + wp_pures.
        wp_apply ("HsserA" $! _ _ _ c q with "[//] [$Hser1 $Htok $Hintr]").
        iIntros "(Htok & Hintr & HreachA)". wp_pures.
        unfold inl_ser_str. iApply "HΨ". iModIntro. iFrame "Htok Hintr".
        iApply (reach_closure_sum_l with "HreachA").
      + wp_pures.
        wp_apply ("HsserB" $! _ _ _ c q with "[//] [$Hser1 $Htok $Hintr]").
        iIntros "(Htok & Hintr & HreachB)". wp_pures.
        unfold inr_ser_str. iApply "HΨ". iModIntro. iFrame "Htok Hintr".
        iApply (reach_closure_sum_r with "HreachB").
    - (* suspend_spec_bin *)
      rewrite /suspend_spec_bin.
      iIntros (t' v0 un_v s_def Ψ) "!# (%Hunsusp & #Hsw & HA) HΨ".
      rewrite interp_un_sum_unfold interp_var1_ext2 interp_var0_ext1.
      iDestruct "HA" as (w) "[[>-> HAw] | [>-> HBw]]".
      + (* v0 = InjLV w *)
        destruct t'; simpl in Hunsusp.
        * destruct Hunsusp as (?&?&?&?&Hx&_). simplify_eq.
        * destruct Hunsusp as [(w1&un1&Heq&->&Hu1)|(w1&un1&Heq&->&_)];
            last by simplify_eq.
          injection Heq as <-.
          iDestruct "Hsw" as (w0 s0) "[[#Hsw1 [%HeqW _]] | [_ [%HeqW _]]]";
            last by simplify_eq.
          injection HeqW as <-. wp_pures.
          wp_apply ("HspbA" $! _ _ un1 _ with "[HAw]").
          { iSplit; [by iPureIntro|]. iFrame "Hsw1". iApply "HAw". }
          iIntros (v' s c) "[HA' Hreal]". wp_pures.
          iApply ("HΨ" $! (InjLV v')).
          iSplitL "HA'".
          { iExists v'. iLeft. iModIntro. iSplit; [done|]. iApply "HA'". }
          simpl. iExists v', s. iLeft. by iFrame "Hreal".
        * (* witness forces a tstring-shaped value — contradiction with InjL *)
          iDestruct "Hsw" as %(? & Heqv & _). simplify_eq.
        * (* witness forces a tint-shaped value — contradiction with InjL *)
          iDestruct "Hsw" as %(? & Heqv & _). simplify_eq.
        * destruct Hunsusp as (?&?&?&?&?&Hx&_). simplify_eq.
      + (* v0 = InjRV w *)
        destruct t'; simpl in Hunsusp.
        * destruct Hunsusp as (?&?&?&?&Hx&_). simplify_eq.
        * destruct Hunsusp as [(w1&un1&Heq&->&_)|(w1&un1&Heq&->&Hu1)];
            first by simplify_eq.
          injection Heq as <-.
          iDestruct "Hsw" as (w0 s0) "[[_ [%HeqW _]] | [#Hsw1 [%HeqW _]]]";
            first by simplify_eq.
          injection HeqW as <-. wp_pures.
          wp_apply ("HspbB" $! _ _ un1 _ with "[HBw]").
          { iSplit; [by iPureIntro|]. iFrame "Hsw1". iApply "HBw". }
          iIntros (v' s c) "[HB' Hreal]". wp_pures.
          iApply ("HΨ" $! (InjRV v')).
          iSplitL "HB'".
          { iExists v'. iRight. iModIntro. iSplit; [done|]. iApply "HB'". }
          simpl. iExists v', s. iRight. by iFrame "Hreal".
        * (* witness forces a tstring-shaped value — contradiction with InjR *)
          iDestruct "Hsw" as %(? & Heqv & _). simplify_eq.
        * (* witness forces a tint-shaped value — contradiction with InjR *)
          iDestruct "Hsw" as %(? & Heqv & _). simplify_eq.
        * destruct Hunsusp as (?&?&?&?&?&Hx&_). simplify_eq.
    - (* unsuspend_spec_bin *)
      rewrite /unsuspend_spec_bin.
      iIntros (E a1 HE Ψ) "!# (HA & Htok) HΨ".
      rewrite interp_un_sum_unfold interp_var1_ext2 interp_var0_ext1.
      iDestruct "HA" as (w) "[[>-> HAw] | [>-> HBw]]".
      + wp_pures.
        wp_apply ("HuspbA" with "[//] [$HAw $Htok]").
        iIntros (un_w) "[Htok %Hu]".
        wp_pures. iApply ("HΨ" $! (InjLV un_w)). iFrame "Htok".
        iPureIntro. simpl. left. by exists w, un_w.
      + wp_pures.
        wp_apply ("HuspbB" with "[//] [$HBw $Htok]").
        iIntros (un_w) "[Htok %Hu]".
        wp_pures. iApply ("HΨ" $! (InjRV un_w)). iFrame "Htok".
        iPureIntro. simpl. right. by exists w, un_w.
  Qed.

  Lemma refines_Auth_sum Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆; ⋆, var2 var1 → var2 var0 → var2 (var1 + var0) ⟧
      (ext Δ (lrel_evidence)) p_Auth_sum v_Auth_sum i_Auth_sum.
  Proof.
    iSplit; interp_unfold!; last first.
    { (* unary  *)
      iIntros (A' vA0) "!# _ Htok". rewrite /p_Auth_sum. wp_pures.
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
      rewrite /sum_ser. wp_pures. iModIntro. iFrame "Htok". interp_unfold!.
      interp_unfold! in "HA'". interp_unfold! in "HB'".
      iApply (refines_un_Auth_sum with "HA' HB'"). }
    (* ternary *)
    iIntros (A v1 v2 v3) "!# _"; rewrite -/interp.
    iIntros (????) "Hv Hi Htok".
    rewrite /p_Auth_sum /v_Auth_sum /i_Auth_sum.
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
      rewrite /sum_ser. wp_pures. iModIntro. iFrame "Htok". interp_unfold!.
      interp_unfold! in "HA'". interp_unfold! in "HB'".
      iApply (refines_un_Auth_sum with "HA' HB'"). }
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
      rewrite /sum_ser. wp_pures. iModIntro. iFrame "Htok". interp_unfold!.
      interp_unfold! in "HA'". interp_unfold! in "HB'".
      iApply (refines_un_Auth_sum with "HA' HB'"). }
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
      rewrite /sum_ser. wp_pures. iModIntro. iFrame "Htok". interp_unfold!.
      interp_unfold! in "HB'".
      iApply (refines_un_Auth_sum with "HA_un HB'"). }
    iIntros (vB1 vB2 vB3) "!# #HB".
    interp_unfold! in "HB".
    iDestruct "HB" as "(HB_tern & #HB_un)".
    iDestruct "HB_tern" as (tB p_ssB p_usB p_spB p_uspB v_sB v_dB v_cB -> ->) "#HrestB".
    iIntros (????) "Hv Hi Htok".
    rewrite /sum_ser'' /sum_ser /sum_count.
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame.
    iSplit; interp_unfold!; last first.
    { (* final unary  *) iApply (refines_un_Auth_sum with "HA_un HB_un"). }
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
        iApply (reach_closure_sum_l with "HreachA").
      + (* InjR: B serializer runs *)
        rewrite /sum_ser''. wp_pures. rewrite /sum_ser. wp_pures.
        wp_apply ("HsserB" $! _ _ _ c q with "[//] [$Hser1 $Htok $Hintr]").
        iIntros "(Htok & Hintr & HreachB)". wp_pures.
        unfold inr_ser_str. iApply "HΨ". iModIntro. iFrame "Htok Hintr".
        iApply (reach_closure_sum_r with "HreachB").
    - (* 3. suspend_v_deser_spec (combined) *)
      rewrite /suspend_v_deser_spec.
      iIntros "!#" (K tᵥ3 pid) "Hv".
      v_pures.
      v_bind (v_dB _).
      iMod ("HsuspvdeserB" with "Hv") as (v_parB) "(Hv & #HinnerB) /=".
      v_bind (v_dA _).
      iMod ("HsuspvdeserA" with "Hv") as (v_parA) "(Hv & #HinnerA) /=".
      rewrite /sum_deser. v_pures.
      iModIntro. iExists _. iFrame "Hv".
      iIntros "!#" (t' a1 un_a1 a2 a3 s_def s_pred s_reg vm mp pn ctr mlg_p K' tᵥ' Ψ).
      iIntros "!# (%Hunsusp & #HA & #Hser & #Hserpred & #Hmint & Hvm & Hlgp & Hpenc & Hv) HΨ".
      wp_pure _.
      iPoseProof "HA" as "HA'".
      iEval (rewrite interp_sum_combined) in "HA'".
      iDestruct "HA'" as (w1 w2 w3) "[(-> & -> & -> & HAc) | (-> & -> & -> & HBc)]".
      + (* prover value is InjL w1 *)
        destruct t' as [t1' t2'|t1' t2'| | |]; simpl in Hunsusp.
        { destruct Hunsusp as (?&?&?&?&Heq&_). simplify_eq. }
        2:{ iDestruct "Hser" as %(s' & Heq & _). simplify_eq. }
        2:{ iDestruct "Hser" as %(z & Heq & _). simplify_eq. }
        2:{ destruct Hunsusp as (?&?&?&?&?&Heq&_). simplify_eq. }
        destruct Hunsusp as [(x & un_x & Heq & -> & Hunx)|(? & ? & Heq & _)];
          simplify_eq.
        (* [Hser] pins the components' defined serializations *)
        iDestruct "Hser" as (w s1_def) "[[#HserA' [%HeqL %Hsdef]] | [_ [%HeqR _]]]";
          simplify_eq.
        wp_pures. wp_bind (p_spA _).
        interp_unfold! in "HAc".
        v_pures; try solve_vals_compare_safe.
        case_bool_decide as HtagL; v_pures; try solve_vals_compare_safe.
        * (* verifier parses an L-tag: couple with the A component *)
          v_bind (v_parA _).
          wp_apply ("HinnerA" with "[$HAc $HserA' $Hserpred $Hmint $Hvm $Hlgp $Hpenc $Hv]").
          { done. }
          iIntros (a1A' s_realA cA t_realA)
            "(#HspecatA & #HrealA & _ & HpostA)".
          wp_pures.
          iDestruct "HpostA" as "[HmatchA | [%HnmA #HunA]]".
          ** (* component match *)
             iDestruct "HmatchA" as "([%HspA %HtA] & #HunA1' & %γl & %mlg' & %a2A' &
                 Hlgp' & %Hsz & Hpens & #HpserpA' & Hv & Hbig & Hpenc' & Hvm' & Hwand)".
             iSimpl in "Hv". v_pures.
             subst t_realA.
             (* reconstruct s_pred = inl_ser_str s_realA *)
             injection HtagL as HtagL'.
             replace (Z.to_nat 0) with 0 in HtagL' by done.
             replace (Z.to_nat 2) with 2 in HtagL' by done.
             replace (Z.to_nat 2) with 2 in HspA by done.
             replace (Z.to_nat (String.length s_pred - 2))
               with (String.length s_pred - 2)%nat in HspA by lia.
             assert (2 ≤ String.length s_pred)%nat as Hlen2.
             { replace 2 with (String.length "L_") at 1; [|done].
               rewrite -HtagL'. apply length_substring_le. }
             assert (s_pred = inl_ser_str s_realA) as ->.
             { rewrite {1}(substring_split_from_O s_pred 2) //.
               by rewrite /inl_ser_str HtagL' HspA. }
             iApply ("HΨ" $! (InjLV a1A') (inl_ser_str s_realA) cA (tsum tA tB)).
             iModIntro.
             iSplitR.
             { rewrite /susp_p_ser_spec_at.
               iIntros (E q HE Ψ') "!# (Htok & Hintr) HΨ'".
               wp_pures.
               wp_apply ("HspecatA" $! E q with "[//] [$Htok $Hintr]").
               iIntros "(Htok & Hintr & Hreach)". wp_pures.
               unfold inl_ser_str. iApply "HΨ'". iModIntro. iFrame "Htok Hintr".
               iApply (reach_closure_sum_l with "Hreach"). }
             iSplitR.
             { iExists a1A', s_realA. iLeft. iSplit; [iApply "HrealA"|done]. }
             iFrame "Hserpred".
             iLeft. iSplit; [done|].
             iSplitR.
             { rewrite interp_un_sum_unfold. iExists a1A'. iLeft.
               iSplit; [done|]. interp_unfold!.
               iDestruct "HunA1'" as "HunA1c". iApply "HunA1c". }
             iExists γl, mlg', (InjLV a2A').
             iFrame "Hlgp' Hpens Hv".
             iSplit; [by iPureIntro|].
             iSplit.
             { iExists a1A', s1_def. iLeft. iSplit; [iApply "HpserpA'"|done]. }
             iSplitL "Hbig".
             { iApply (big_sepS_mono with "Hbig").
               iIntros (γ' Hγ') "[Hp Hv2]".
               iSplitL "Hp".
               - iDestruct "Hp" as (lb) "[Hp %Hps]". iExists lb. iFrame "Hp".
                 iPureIntro. exists a1A'. left. by split.
               - iDestruct "Hv2" as (suspx) "[Hg %Hvs]". iExists suspx.
                 iFrame "Hg". iPureIntro. exists a2A'. left. by split. }
             iSplitL "Hpenc'"; [by iFrame "Hpenc'"|].
             iFrame "Hvm'".
             iIntros (t_out v_out s_out Nt) "%Hsubpos %HcN Hcap Hmap Hsr".
             iMod ("Hwand" $! t_out v_out s_out Nt
                     with "[] [//] Hcap [Hmap] [Hsr]")
               as "(HAf & Hcnt & Hserv)".
             { iPureIntro. eapply sub_pos_trans; [exact Hsubpos|].
               by apply sub_pos_inl, sub_pos_refl. }
             { iExact "Hmap". }
             { iExact "Hsr". }
             iModIntro.
             iSplitL "HAf".
             { iEval (rewrite interp_sum_combined).
               iExists a1A', a2A', w3. iLeft.
               do 3 (iSplit; [done|]). interp_unfold!. iApply "HAf". }
             iSplitL "Hcnt".
             { iLeft. iExists a2A'. iSplit; [done|]. iExact "Hcnt". }
             iExists a2A', s1_def. iLeft. iSplit; [iExact "Hserv"|done].
          ** (* component mismatch *)
             injection HtagL as HtagL'.
             replace (Z.to_nat 0) with 0 in HtagL' by done.
             replace (Z.to_nat 2) with 2 in HtagL' by done.
             replace (Z.to_nat 2) with 2 in HnmA by done.
             replace (Z.to_nat (String.length s_pred - 2))
               with (String.length s_pred - 2)%nat in HnmA by lia.
             iApply ("HΨ" $! (InjLV a1A') (inl_ser_str s_realA) cA
                       (tsum t_realA tB)).
             iModIntro.
             iSplitR.
             { rewrite /susp_p_ser_spec_at.
               iIntros (E q HE Ψ') "!# (Htok & Hintr) HΨ'".
               wp_pures.
               wp_apply ("HspecatA" $! E q with "[//] [$Htok $Hintr]").
               iIntros "(Htok & Hintr & Hreach)". wp_pures.
               unfold inl_ser_str. iApply "HΨ'". iModIntro. iFrame "Htok Hintr".
               iApply (reach_closure_sum_l with "Hreach"). }
             iSplitR.
             { iExists a1A', s_realA. iLeft. iSplit; [iApply "HrealA"|done]. }
             iFrame "Hserpred".
             iRight. iSplit.
             { iPureIntro. intros Heqs. apply HnmA.
               rewrite Heqs /inl_ser_str /=.
               replace (String.length ("L_" +:+ s_realA) - 2)%nat
                 with (String.length s_realA) by (simpl; lia).
               by rewrite /= Nat.sub_0_r substring_0_length. }
             rewrite interp_un_sum_unfold.
             iExists a1A'. iLeft. iSplit; [done|].
             interp_unfold!. iDestruct "HunA" as "HunA'". iApply "HunA'".
        * case_bool_decide as HtagR; v_pures.
          -- (* verifier parses an R-tag while the prover is InjL *)
             iPoseProof "HA_un" as "HAu".
             iEval (rewrite /lrel_evidence /lrel_evidence' /lrel_un_evidence /=)
               in "HAu".
             iDestruct "HAu" as (tAu ssAu usAu spAu uspAu ? ? ?)
               "(%HeqAu & #HusserAu & #HsserAu & #HspbAu & _)".
             injection HeqAu as <- <- <- <-.
             iDestruct "HAc" as "[_ HAcun]".
             wp_apply ("HspbAu" $! t1' w un_x with "[HAcun]").
             { iSplit; [done|]. iSplit; [iApply "HserA'"|]. iApply "HAcun". }
             iIntros (a1A' sA cA) "[HAun' #HrealA']".
             wp_pures.
             iApply ("HΨ" $! (InjLV a1A') (inl_ser_str sA) cA (tsum tAu tB)).
             iModIntro.
             iSplitR.
             { iPoseProof (susp_p_ser_spec_at_intro with "HrealA' HsserAu")
                 as "#HatA".
               rewrite /susp_p_ser_spec_at.
               iIntros (E q HE Ψ') "!# (Htok & Hintr) HΨ'".
               wp_pures.
               wp_apply ("HatA" $! E q with "[//] [$Htok $Hintr]").
               iIntros "(Htok & Hintr & Hreach)". wp_pures.
               unfold inl_ser_str. iApply "HΨ'". iModIntro. iFrame "Htok Hintr".
               iApply (reach_closure_sum_l with "Hreach"). }
             iSplitR.
             { iExists a1A', sA. iLeft. iSplit; [iApply "HrealA'"|done]. }
             iFrame "Hserpred".
             iRight. iSplit.
             { iPureIntro. intros ->. 
               replace (Z.to_nat 0) with 0 in HtagR by done.
               replace (Z.to_nat 2) with 2 in HtagR by done.
               rewrite /inl_ser_str /= in HtagR.
               rewrite substring_n_0 in HtagR. simplify_eq. }
             rewrite interp_un_sum_unfold.
             iExists a1A'. iLeft. iSplit; [done|].
             interp_unfold!. iApply "HAun'".
          -- (* no tag parses *)
             iPoseProof "HA_un" as "HAu".
             iEval (rewrite /lrel_evidence /lrel_evidence' /lrel_un_evidence /=)
               in "HAu".
             iDestruct "HAu" as (tAu ssAu usAu spAu uspAu ? ? ?)
               "(%HeqAu & #HusserAu & #HsserAu & #HspbAu & _)".
             injection HeqAu as <- <- <- <-.
             iDestruct "HAc" as "[_ HAcun]".
             wp_apply ("HspbAu" $! t1' w un_x with "[HAcun]").
             { iSplit; [done|]. iSplit; [iApply "HserA'"|]. iApply "HAcun". }
             iIntros (a1A' sA cA) "[HAun' #HrealA']".
             wp_pures.
             iApply ("HΨ" $! (InjLV a1A') (inl_ser_str sA) cA (tsum tAu tB)).
             iModIntro.
             iSplitR.
             { iPoseProof (susp_p_ser_spec_at_intro with "HrealA' HsserAu")
                 as "#HatA".
               rewrite /susp_p_ser_spec_at.
               iIntros (E q HE Ψ') "!# (Htok & Hintr) HΨ'".
               wp_pures.
               wp_apply ("HatA" $! E q with "[//] [$Htok $Hintr]").
               iIntros "(Htok & Hintr & Hreach)". wp_pures.
               unfold inl_ser_str. iApply "HΨ'". iModIntro. iFrame "Htok Hintr".
               iApply (reach_closure_sum_l with "Hreach"). }
             iSplitR.
             { iExists a1A', sA. iLeft. iSplit; [iApply "HrealA'"|done]. }
             iFrame "Hserpred".
             iRight. iSplit.
             { iPureIntro. intros ->. 
               apply HtagL. rewrite /inl_ser_str /=.
               by rewrite substring_n_0. }
             rewrite interp_un_sum_unfold.
             iExists a1A'. iLeft. iSplit; [done|].
             interp_unfold!. iApply "HAun'".
      + (* prover value is InjR w1 *)
        destruct t' as [t1' t2'|t1' t2'| | |]; simpl in Hunsusp.
        { destruct Hunsusp as (?&?&?&?&Heq&_). simplify_eq. }
        2:{ iDestruct "Hser" as %(s' & Heq & _). simplify_eq. }
        2:{ iDestruct "Hser" as %(z & Heq & _). simplify_eq. }
        2:{ destruct Hunsusp as (?&?&?&?&?&Heq&_). simplify_eq. }
        destruct Hunsusp as [(? & ? & Heq & _)|(y & un_y & Heq & -> & Huny)];
          simplify_eq.
        iDestruct "Hser" as (w s1_def) "[[_ [%HeqL _]] | [#HserB' [%HeqR %Hsdef]]]";
          simplify_eq.
        wp_pures. wp_bind (p_spB _).
        interp_unfold! in "HBc".
        v_pures; try solve_vals_compare_safe.
        case_bool_decide as HtagL; v_pures; try solve_vals_compare_safe.
        * (* L-tag while the prover is InjR *)
             iPoseProof "HB_un" as "HBu".
             iEval (rewrite /lrel_evidence /lrel_evidence' /lrel_un_evidence /=)
               in "HBu".
             iDestruct "HBu" as (tBu ssBu usBu spBu uspBu ? ? ?)
               "(%HeqBu & #HusserBu & #HsserBu & #HspbBu & _)".
             injection HeqBu as <- <- <- <-.
             iDestruct "HBc" as "[_ HBcun]".
             wp_apply ("HspbBu" $! t2' w un_y with "[HBcun]").
             { iSplit; [done|]. iSplit; [iApply "HserB'"|]. iApply "HBcun". }
             iIntros (a1B' sB cB) "[HBun' #HrealB']".
             wp_pures.
             iApply ("HΨ" $! (InjRV a1B') (inr_ser_str sB) cB (tsum tA tBu)).
             iModIntro.
             iSplitR.
             { iPoseProof (susp_p_ser_spec_at_intro with "HrealB' HsserBu")
                 as "#HatB".
               rewrite /susp_p_ser_spec_at.
               iIntros (E q HE Ψ') "!# (Htok & Hintr) HΨ'".
               wp_pures.
               wp_apply ("HatB" $! E q with "[//] [$Htok $Hintr]").
               iIntros "(Htok & Hintr & Hreach)". wp_pures.
               unfold inr_ser_str. iApply "HΨ'". iModIntro. iFrame "Htok Hintr".
               iApply (reach_closure_sum_r with "Hreach"). }
             iSplitR.
             { iExists a1B', sB. iRight. iSplit; [iApply "HrealB'"|done]. }
             iFrame "Hserpred".
             iRight. iSplit.
             { iPureIntro. intros ->. 
               replace (Z.to_nat 0) with 0 in HtagL by done.
               replace (Z.to_nat 2) with 2 in HtagL by done.
               rewrite /inr_ser_str /= in HtagL.
               rewrite substring_n_0 in HtagL. simplify_eq. }
             rewrite interp_un_sum_unfold.
             iExists a1B'. iRight. iSplit; [done|].
             interp_unfold!. iApply "HBun'".
        * case_bool_decide as HtagR; v_pures.
          -- (* R-tag: couple with the B component *)
             v_bind (v_parB _).
             wp_apply ("HinnerB" with "[$HBc $HserB' $Hserpred $Hmint $Hvm $Hlgp $Hpenc $Hv]").
             { done. }
             iIntros (a1B' s_realB cB t_realB)
               "(#HspecatB & #HrealB & _ & HpostB)".
             wp_pures.
             iDestruct "HpostB" as "[HmatchB | [%HnmB #HunB]]".
             ** (* component match *)
                iDestruct "HmatchB" as "([%HspB %HtB] & #HunB1' & %γl & %mlg' & %a2B' &
                    Hlgp' & %Hsz & Hpens & #HpserpB' & Hv & Hbig & Hpenc' & Hvm' & Hwand)".
                iSimpl in "Hv". v_pures.
                subst t_realB.
                injection HtagR as HtagR'.
                replace (Z.to_nat 0) with 0 in HtagR' by done.
                replace (Z.to_nat 2) with 2 in HtagR' by done.
                replace (Z.to_nat 2) with 2 in HspB by done.
                replace (Z.to_nat (String.length s_pred - 2))
                  with (String.length s_pred - 2)%nat in HspB by lia.
                assert (2 ≤ String.length s_pred)%nat as Hlen2.
                { replace 2 with (String.length "R_") at 1; [|done].
                  rewrite -HtagR'. apply length_substring_le. }
                assert (s_pred = inr_ser_str s_realB) as ->.
                { rewrite {1}(substring_split_from_O s_pred 2) //.
                  by rewrite /inr_ser_str HtagR' HspB. }
                iApply ("HΨ" $! (InjRV a1B') (inr_ser_str s_realB) cB (tsum tA tB)).
                iModIntro.
                iSplitR.
                { rewrite /susp_p_ser_spec_at.
                  iIntros (E q HE Ψ') "!# (Htok & Hintr) HΨ'".
                  wp_pures.
                  wp_apply ("HspecatB" $! E q with "[//] [$Htok $Hintr]").
                  iIntros "(Htok & Hintr & Hreach)". wp_pures.
                  unfold inr_ser_str. iApply "HΨ'". iModIntro. iFrame "Htok Hintr".
                  iApply (reach_closure_sum_r with "Hreach"). }
                iSplitR.
                { iExists a1B', s_realB. iRight. iSplit; [iApply "HrealB"|done]. }
                iFrame "Hserpred".
                iLeft. iSplit; [done|].
                iSplitR.
                { rewrite interp_un_sum_unfold. iExists a1B'. iRight.
                  iSplit; [done|]. interp_unfold!.
                  iDestruct "HunB1'" as "HunB1c". iApply "HunB1c". }
                iExists γl, mlg', (InjRV a2B').
                iFrame "Hlgp' Hpens Hv".
                iSplit; [by iPureIntro|].
                iSplit.
                { iExists a1B', s1_def. iRight. iSplit; [iApply "HpserpB'"|done]. }
                iSplitL "Hbig".
                { iApply (big_sepS_mono with "Hbig").
                  iIntros (γ' Hγ') "[Hp Hv2]".
                  iSplitL "Hp".
                  - iDestruct "Hp" as (lb) "[Hp %Hps]". iExists lb. iFrame "Hp".
                    iPureIntro. exists a1B'. right. by split.
                  - iDestruct "Hv2" as (suspx) "[Hg %Hvs]". iExists suspx.
                    iFrame "Hg". iPureIntro. exists a2B'. right. by split. }
                iSplitL "Hpenc'"; [by iFrame "Hpenc'"|].
                iFrame "Hvm'".
                iIntros (t_out v_out s_out Nt) "%Hsubpos %HcN Hcap Hmap Hsr".
                iMod ("Hwand" $! t_out v_out s_out Nt
                        with "[] [//] Hcap [Hmap] [Hsr]")
                  as "(HBf & Hcnt & Hserv)".
                { iPureIntro. eapply sub_pos_trans; [exact Hsubpos|].
                  by apply sub_pos_inr, sub_pos_refl. }
                { iExact "Hmap". }
                { iExact "Hsr". }
                iModIntro.
                iSplitL "HBf".
                { iEval (rewrite interp_sum_combined).
                  iExists a1B', a2B', w3. iRight.
                  do 3 (iSplit; [done|]). interp_unfold!. iApply "HBf". }
                iSplitL "Hcnt".
                { iRight. iExists a2B'. iSplit; [done|]. iExact "Hcnt". }
                iExists a2B', s1_def. iRight. iSplit; [iExact "Hserv"|done].
             ** (* component mismatch *)
                injection HtagR as HtagR'.
                replace (Z.to_nat 0) with 0 in HtagR' by done.
                replace (Z.to_nat 2) with 2 in HtagR' by done.
                replace (Z.to_nat 2) with 2 in HnmB by done.
                replace (Z.to_nat (String.length s_pred - 2))
                  with (String.length s_pred - 2)%nat in HnmB by lia.
                iApply ("HΨ" $! (InjRV a1B') (inr_ser_str s_realB) cB
                          (tsum tA t_realB)).
                iModIntro.
                iSplitR.
                { rewrite /susp_p_ser_spec_at.
                  iIntros (E q HE Ψ') "!# (Htok & Hintr) HΨ'".
                  wp_pures.
                  wp_apply ("HspecatB" $! E q with "[//] [$Htok $Hintr]").
                  iIntros "(Htok & Hintr & Hreach)". wp_pures.
                  unfold inr_ser_str. iApply "HΨ'". iModIntro. iFrame "Htok Hintr".
                  iApply (reach_closure_sum_r with "Hreach"). }
                iSplitR.
                { iExists a1B', s_realB. iRight. iSplit; [iApply "HrealB"|done]. }
                iFrame "Hserpred".
                iRight. iSplit.
                { iPureIntro. intros Heqs. apply HnmB.
                  rewrite Heqs /inr_ser_str /=.
                  by rewrite /= Nat.sub_0_r substring_0_length. }
                rewrite interp_un_sum_unfold.
                iExists a1B'. iRight. iSplit; [done|].
                interp_unfold!. iDestruct "HunB" as "HunB'". iApply "HunB'".
          -- (* no tag parses *)
             iPoseProof "HB_un" as "HBu".
             iEval (rewrite /lrel_evidence /lrel_evidence' /lrel_un_evidence /=)
               in "HBu".
             iDestruct "HBu" as (tBu ssBu usBu spBu uspBu ? ? ?)
               "(%HeqBu & #HusserBu & #HsserBu & #HspbBu & _)".
             injection HeqBu as <- <- <- <-.
             iDestruct "HBc" as "[_ HBcun]".
             wp_apply ("HspbBu" $! t2' w un_y with "[HBcun]").
             { iSplit; [done|]. iSplit; [iApply "HserB'"|]. iApply "HBcun". }
             iIntros (a1B' sB cB) "[HBun' #HrealB']".
             wp_pures.
             iApply ("HΨ" $! (InjRV a1B') (inr_ser_str sB) cB (tsum tA tBu)).
             iModIntro.
             iSplitR.
             { iPoseProof (susp_p_ser_spec_at_intro with "HrealB' HsserBu")
                 as "#HatB".
               rewrite /susp_p_ser_spec_at.
               iIntros (E q HE Ψ') "!# (Htok & Hintr) HΨ'".
               wp_pures.
               wp_apply ("HatB" $! E q with "[//] [$Htok $Hintr]").
               iIntros "(Htok & Hintr & Hreach)". wp_pures.
               unfold inr_ser_str. iApply "HΨ'". iModIntro. iFrame "Htok Hintr".
               iApply (reach_closure_sum_r with "Hreach"). }
             iSplitR.
             { iExists a1B', sB. iRight. iSplit; [iApply "HrealB'"|done]. }
             iFrame "Hserpred".
             iRight. iSplit.
             { iPureIntro. intros ->. 
               apply HtagR. rewrite /inr_ser_str /=.
               by rewrite substring_n_0. }
             rewrite interp_un_sum_unfold.
             iExists a1B'. iRight. iSplit; [done|].
             interp_unfold!. iApply "HBun'".
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
      iIntros (K tᵥ3 a1 un_a1 a2 a3 s Ψ) "!# (%Hunsusp & HA & #Hser & #Hfw & Htok & Hv) HΨ".
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
        iDestruct "Hfw" as "[Hfwc|Hfwc]";
          iDestruct "Hfwc" as (vx) "[%Heqx #Hfwc]"; last by simplify_eq.
        injection Heqx as <-.
        wp_pures.
        v_pures. v_bind (v_sA _).
        wp_apply ("HvauthserA" with "[HrA Htok Hv]").
        { by iFrame "HrA Hser1 Hfwc Htok Hv". }
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
        iDestruct "Hfw" as "[Hfwc|Hfwc]";
          iDestruct "Hfwc" as (vx) "[%Heqx #Hfwc]"; first by simplify_eq.
        injection Heqx as <-.
        wp_pures.
        v_pures. v_bind (v_sB _).
        wp_apply ("HvauthserB" with "[HrB Htok Hv]").
        { by iFrame "HrB Hser1 Hfwc Htok Hv". }
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
        iIntros (t' v un_v s_def Ψ) "!# (%Hunsusp & #Hsw & HA) HΨ".
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
    - (* 3. suspend_v_deser_spec (combined) *)
      rewrite /suspend_v_deser_spec.
      iIntros "!#" (K tᵥ3 pid) "Hv".
      v_pures.
      iModIntro. iExists _. iFrame "Hv".
      iIntros "!#" (t' a1 un_a1 a2 a3 s_def s_pred s_reg vm mp pn ctr mlg_p K' tᵥ' Ψ).
      iIntros "!# (%Hunsusp & #HA & #Hser & #Hserpred & #Hmint & Hvm & Hlgp & Hpenc & Hv) HΨ".
      rewrite /id. wp_pure _.
      iPoseProof "HA" as "[HAt #HAun]".
      iDestruct "HAt" as %(sv & -> & -> & ->).
      (* [A] forces a string literal, so [Hser] refutes every t' ≠ tstring. *)
      destruct t'; simpl in Hunsusp.
      { iDestruct "Hser" as (v1 v2 s1 s2) "[%Hp _]".
        destruct Hp as [Hp _]. simplify_eq. }
      { iDestruct "Hser" as (w s') "[[_ %Hp] | [_ %Hp]]";
          destruct Hp as [Hp _]; simplify_eq. }
      2:{ iDestruct "Hser" as %(z & Hp & _). simplify_eq. }
      2:{ iDestruct "Hser" as %(p & lb & lr & a & h & Hp & _). simplify_eq. }
      (* t' = tstring *)
      iDestruct "Hser" as %(s' & Heq & ->). injection Heq as <-. subst un_a1.
      iMod penset_frag_empty as "Hpen0".
      (* The serializer spec at the result — shared by match and mismatch. *)
      iAssert (susp_p_ser_spec_at string_ser tstring 0 #sv
                 (string_ser_str sv)) with "[]" as "#Hspecat".
      { rewrite /susp_p_ser_spec_at.
        iIntros (E q HE Ψ') "!# (Htok & Hintr) HΨ'".
        rewrite /string_ser. wp_pures.
        iApply "HΨ'". iModIntro. iFrame "Htok".
        iEval (rewrite -{1}(Qp.div_2 q) intransit_split) in "Hintr".
        iDestruct "Hintr" as "[$ _]".
        iIntros (γl) "Hg Hpen %Hsz Hbig".
        apply size_empty_inv in Hsz. fold_leibniz. subst γl.
        iFrame "Hg Hpen". by rewrite big_sepS_empty. }
      destruct (decide (s_pred = string_ser_str sv)) as [->|Hne].
      + (* match: the verifier parses the real serialization back to #sv *)
        rewrite /string_deser. v_pures; try solve_vals_compare_safe.
        iEval (rewrite substring_n_0) in "Hv".
        iEval (rewrite bool_decide_eq_true_2 //) in "Hv".
        v_pures.
        assert (Z.to_nat (S (S (String.length sv)) - 2) = String.length sv)
          as Hlen by lia.
        iEval (rewrite Hlen substring_0_length) in "Hv".
        v_pures.
        iApply ("HΨ" $! #sv (string_ser_str sv) 0 tstring).
        iFrame "Hspecat Hserpred". iModIntro.
        iSplitR. { iPureIntro. naive_solver. }
        iLeft. iSplit; [done|].
        iSplitR; [iApply "HAun"|].
        iExists ∅, mlg_p, #sv.
        iFrame "Hlgp Hpen0 Hv".
        iSplit; [by rewrite size_empty|].
        iSplit. { iPureIntro. by exists sv. }
        iSplit. { by rewrite big_sepS_empty. }
        iSplitL "Hpenc"; [by iFrame "Hpenc"|].
        rewrite /visited_map_update_pending set_fold_empty size_empty Nat.add_0_r.
        iFrame "Hvm".
        (* the decoration wand: everything is pure at c = 0 *)
        iIntros (t_out v_out s_out Nt) "%Hsubpos %HcN #Hcap _ _". iModIntro.
        iSplit. { iSplit; [by iExists sv|]. iApply "HAun". }
        iSplit. { iSplit; [by iExists sv|done]. }
        iPureIntro. by exists sv.
      + (* mismatch: parse fails or parses to a different string *)
        rewrite /string_deser. v_pures; try solve_vals_compare_safe.
        case_bool_decide as Htag; v_pures.
        * iApply ("HΨ" $! #sv (string_ser_str sv) 0 tstring).
          iFrame "Hspecat Hserpred". iModIntro.
        iSplitR. { iPureIntro. naive_solver. }
          iRight. iSplit; [done|]. by iExists sv.
        * iApply ("HΨ" $! #sv (string_ser_str sv) 0 tstring).
          iFrame "Hspecat Hserpred". iModIntro.
        iSplitR. { iPureIntro. naive_solver. }
          iRight. iSplit; [done|]. by iExists sv.

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
      iIntros (K tᵥ a1 un_a1 a2 a3 s Ψ) "!# (%Hunsusp & HA & #Hser & #Hfw & Htok & Hv) HΨ".
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
        iIntros (t' v un_v s_def Ψ) "!# (%Hunsusp & #Hsw & HA) HΨ".
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
    - (* 3. suspend_v_deser_spec (combined) *)
      rewrite /suspend_v_deser_spec.
      iIntros "!#" (K tᵥ3 pid) "Hv".
      v_pures.
      iModIntro. iExists _. iFrame "Hv".
      iIntros "!#" (t' a1 un_a1 a2 a3 s_def s_pred s_reg vm mp pn ctr mlg_p K' tᵥ' Ψ).
      iIntros "!# (%Hunsusp & #HA & #Hser & #Hserpred & #Hmint & Hvm & Hlgp & Hpenc & Hv) HΨ".
      rewrite /id. wp_pure _.
      iPoseProof "HA" as "[HAt #HAun]".
      iDestruct "HAt" as %(zv & -> & -> & ->).
      (* [A] forces an int literal, so [Hser] refutes every t' ≠ tint. *)
      destruct t'; simpl in Hunsusp.
      { iDestruct "Hser" as (v1 v2 s1 s2) "[%Hp _]".
        destruct Hp as [Hp _]. simplify_eq. }
      { iDestruct "Hser" as (w s') "[[_ %Hp] | [_ %Hp]]";
          destruct Hp as [Hp _]; simplify_eq. }
      { iDestruct "Hser" as %(s' & Hp & _). simplify_eq. }
      2:{ iDestruct "Hser" as %(p & lb & lr & a & h & Hp & _). simplify_eq. }
      (* t' = tint *)
      iDestruct "Hser" as %(z & Heq & ->). injection Heq as <-. subst un_a1.
      iMod penset_frag_empty as "Hpen0".
      iAssert (susp_p_ser_spec_at int_ser tint 0 #zv
                 (int_ser_str zv)) with "[]" as "#Hspecat".
      { rewrite /susp_p_ser_spec_at.
        iIntros (E q HE Ψ') "!# (Htok & Hintr) HΨ'".
        rewrite /int_ser. wp_pures.
        iApply "HΨ'". iModIntro. iFrame "Htok".
        iEval (rewrite -{1}(Qp.div_2 q) intransit_split) in "Hintr".
        iDestruct "Hintr" as "[$ _]".
        iIntros (γl) "Hg Hpen %Hsz Hbig".
        apply size_empty_inv in Hsz. fold_leibniz. subst γl.
        iFrame "Hg Hpen". by rewrite big_sepS_empty. }
      destruct (decide (s_pred = int_ser_str zv)) as [->|Hne].
      + (* match: the verifier parses the real serialization back to #zv *)
        rewrite /int_deser. v_pures; try solve_vals_compare_safe.
        iEval (rewrite substring_n_0) in "Hv".
        iEval (rewrite bool_decide_eq_true_2 //) in "Hv".
        v_pures.
        assert (Z.to_nat (S (S (String.length (StringOfZ zv))) - 2)
                  = String.length (StringOfZ zv)) as Hlen by lia.
        iEval (rewrite Hlen substring_0_length) in "Hv".
        v_pures.
        iEval (rewrite ZOfString_inv) in "Hv".
        v_pures; try solve_vals_compare_safe.
        iEval (rewrite bool_decide_eq_true_2 //) in "Hv".
        v_pures.
        iApply ("HΨ" $! #zv (int_ser_str zv) 0 tint).
        iFrame "Hspecat Hserpred". iModIntro.
        iSplitR. { iPureIntro. naive_solver. }
        iLeft. iSplit; [done|].
        iSplitR; [iApply "HAun"|].
        iExists ∅, mlg_p, #zv.
        iFrame "Hlgp Hpen0 Hv".
        iSplit; [by rewrite size_empty|].
        iSplit. { iPureIntro. by exists zv. }
        iSplit. { by rewrite big_sepS_empty. }
        iSplitL "Hpenc"; [by iFrame "Hpenc"|].
        rewrite /visited_map_update_pending set_fold_empty size_empty Nat.add_0_r.
        iFrame "Hvm".
        iIntros (t_out v_out s_out Nt) "%Hsubpos %HcN #Hcap _ _". iModIntro.
        iSplit. { iSplit; [by iExists zv|]. iApply "HAun". }
        iSplit. { iSplit; [by iExists zv|done]. }
        iPureIntro. by exists zv.
      + (* mismatch: no need to step the verifier — the post drops it *)
        iApply ("HΨ" $! #zv (int_ser_str zv) 0 tint).
        iFrame "Hspecat Hserpred". iModIntro.
        iSplitR. { iPureIntro. naive_solver. }
        iRight. iSplit; [done|]. by iExists zv.

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
      iIntros (K tᵥ a1 un_a1 a2 a3 s Ψ) "!# (%Hunsusp & HA & #Hser & #Hfw & Htok & Hv) HΨ".
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
        iIntros (t' v0 un_v s_def Ψ) "!# (%Hunsusp & #Hsw & HA) HΨ".
        rewrite /rec_fold. wp_pures.
        iEval (rewrite interp_rec_star_un_unfold) in "HA". interp_unfold! in "HA".
        wp_apply ("HspbA" $! _ _ un_v _ with "[HA]").
        { iSplit; first by iPureIntro. iFrame "Hsw". iApply "HA". }
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
        iIntros (t' v0 un_v s_def Ψ) "!# (%Hunsusp & #Hsw & HA) HΨ".
        rewrite /rec_fold. wp_pures.
        iEval (rewrite interp_rec_star_un_unfold) in "HA". interp_unfold! in "HA".
        wp_apply ("HspbA" $! _ _ un_v _ with "[HA]").
        { iSplit; first by iPureIntro. iFrame "Hsw". iApply "HA". }
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
        iIntros (t' v0 un_v s_def Ψ) "!# (%Hunsusp & #Hsw & HA) HΨ".
        rewrite /rec_fold. wp_pures.
        iEval (rewrite interp_rec_star_un_unfold) in "HA". interp_unfold! in "HA".
        wp_apply ("HspbA'" $! _ _ un_v _ with "[HA]").
        { iSplit; first by iPureIntro. iFrame "Hsw". iApply "HA". }
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
    - (* 3. suspend_v_deser_spec (combined) — delegation to the component:
         the outer fupd picks the eta-wrapped deser as v_deser_par; the
         component's own outer fupd is consumed inside the inner triple at
         the extended evaluation context (fill-trick), and wp_pures' later
         stripping turns ▷⟦μ⟧ into the component's ▷⟦F μ⟧ for free. *)
      rewrite /suspend_v_deser_spec.
      iIntros "!#" (K tᵥ1 pid) "Hv".
      v_pures.
      iModIntro. iExists _. iFrame "Hv".
      iIntros "!#" (t' a1 un_a1 a2 a3 s_def s_pred s_reg vm mp pn ctr mlg_p K' tᵥ' Ψ).
      iIntros "!# (%Hunsusp & #HA & #Hser & #Hserpred & #Hmint & Hvm & Hlgp & Hpenc & Hv) HΨ".
      rewrite /rec_fold. wp_pures.
      iEval (rewrite interp_rec_star_unfold) in "HA".
      interp_unfold! in "HA".
      v_pures.
      v_bind (v_dA _).
      iMod ("HsuspvdeserA" with "Hv") as (v_parA) "(Hv & #HinnerA) /=".
      wp_apply ("HinnerA" with "[$HA $Hser $Hserpred $Hmint $Hvm $Hlgp $Hpenc $Hv]").
      { done. }
      iIntros (a1' s_real c t_real) "(#Hspecat & #Hreal & _ & Hpost)".
      iAssert (∀ (ser : val), susp_p_ser_spec_at ser t_real c a1' s_real -∗
                 susp_p_ser_spec_at (λ: "a", rec_fold ser "a")%V t_real c a1' s_real)%I
        with "[]" as "#Hwrap".
      { iIntros (ser) "#Hat".
        rewrite /susp_p_ser_spec_at.
        iIntros (E q HE Ψ') "!# (Htok & Hintr) HΨ'".
        rewrite /rec_fold. wp_pures.
        wp_apply ("Hat" $! E q with "[//] [$Htok $Hintr]").
        iIntros "(? & ? & ?)". iApply "HΨ'". iFrame. }
      iDestruct "Hpost" as "[Hmatch | [%Hnm #Hun]]".
      + iDestruct "Hmatch" as "([%Hsp %Htr] & #Hun1' & %γl & %mlg' & %a2' &
            Hlgp' & %Hsz & Hpens & Hpserp' & Hv & Hbig & Hpenc' & Hvm' & Hwand)".
        iApply ("HΨ" $! a1' s_real c t_real).
        iSplitR. { by iApply "Hwrap". }
        iFrame "Hreal Hserpred".
        iLeft. iSplit; [by iPureIntro|].
        iSplitR.
        { rewrite interp_rec_star_un_unfold. interp_unfold!. iApply "Hun1'". }
        iExists γl, mlg', a2'.
        iFrame "Hlgp' Hpens Hpserp' Hv Hbig Hpenc' Hvm'".
        iSplit; [done|].
        iIntros (t_out v_out s_out Nt) "%Hsubpos %HcN Hcap Hmap Hsr".
        iMod ("Hwand" $! t_out v_out s_out Nt
                with "[//] [//] Hcap [Hmap] [Hsr]")
          as "(HAf & Hcnt & Hserv)".
        { subst t_real. iExact "Hmap". }
        { subst t_real. iExact "Hsr". }
        iModIntro.
        iSplitL "HAf".
        { rewrite interp_rec_star_unfold. interp_unfold!. iApply "HAf". }
        subst t_real. iFrame "Hcnt Hserv".
      + iApply ("HΨ" $! a1' s_real c t_real).
        iSplitR. { by iApply "Hwrap". }
        iFrame "Hreal Hserpred".
        iRight. iSplit; [done|].
        rewrite interp_rec_star_un_unfold. interp_unfold!. iApply "Hun".

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
      iIntros (K tᵥ1 a1 un_a1 a2 a3 s Ψ) "!# (%Hunsusp & HA & #Hser & #Hfw & Htok & Hv) HΨ".
      v_pures.
      rewrite /rec_fold. wp_pure credit:"Hlc". wp_pures.
      iEval (rewrite interp_rec_star_tern_unfold) in "HA".
      iMod (lc_fupd_elim_later with "Hlc HA") as "HA".
      interp_unfold! in "HA".
      wp_apply ("HvauthserA" with "[HA Htok Hv]").
      { by iFrame "HA Hser Hfw Htok Hv". }
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