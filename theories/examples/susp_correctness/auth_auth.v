From auth.prelude Require Import stdpp.
From auth.rel_logic_tern_susp Require Import model interp spec_tactics.
From iris.algebra Require Import gset auth.
From auth.examples Require Import authentikit authenticatable_base_susp.
From auth.examples.susp_correctness Require Export definitions helpers.
From auth.examples.susp_correctness Require Import base_correctness.

Section authenticatable.
  Context `{!authG Σ, !seqG Σ, !correctnessG Σ}.

  Lemma refines_Auth_auth Θ (Δ : ctxO Σ Θ) (R : kindO Σ (⋆ ⇒ ⋆)) :
    ⊢ ⟦ ∀: ⋆, var1 (var3 var0) ⟧
      (auth_ctx Δ R) p_Auth_auth v_Auth_auth i_Auth_auth.
  Proof.
    iSplit; interp_unfold!; last first.
    { (* unary  *) admit. }
    (* ternary *)
    iIntros (A v1 v2 v3) "!# _"; rewrite -/interp.
    iIntros (????) "Hv Hi Htok".
    rewrite /p_Auth_auth /v_Auth_auth /i_Auth_auth.
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame.
    (* Final 3-way split: prove only the ternary [lrel_tern_evidence]. *)
    iSplit; interp_unfold!; last first.
    { (* final unary  *) admit. }
    (* Ternary evidence for the auth. *)
    rewrite interp_var1_ext2.
    iExists tauth, _, _, _, _, _, _, _.
    iSplit; [done|]. iSplit; [done|].
    iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit]]]]].
    - (* 1. unsusp_p_ser_spec *)
      iIntros (v s Ψ) "!# Hser HΨ".
      iDestruct "Hser" as %(a & h & [-> ->]).
      rewrite /authenticatable_base_susp.auth_unsusp_ser_p.
      wp_pures. rewrite /string_ser. wp_pures.
      rewrite /simple_string /string_ser_str.
      by iApply "HΨ".
    - (* 2. susp_p_ser_spec *)
      iIntros (E a1 s c q HE Ψ) "!# (Hser & Htok & Hintr) HΨ".
      iEval (rewrite /susp_ser_p_real /=) in "Hser".
      iDestruct "Hser" as "[[Hfill ->] | [Hemp ->]]".
      + (* Fill branch: c = 0, lb ↦ #false, serialize InjR #h → filled_string h *)
        iDestruct "Hfill" as (p lb lr a h r) "([-> ->] & #Hunalloc & #Hinv)".
        rewrite /authenticatable_base_susp.auth_susp_ser_p. wp_pures.
        wp_bind (ResolveProph _ _)%E.
        iMod (na_inv_acc with "Hinv Htok") as "(Hinvo & Htok & Hclose)";
          [solve_ndisj|solve_ndisj|].
        iDestruct "Hinvo" as "(>Hlb & Hrest)".
        iDestruct "Hrest" as "[Hd1 | [Hd2 | [Hd3 | Hd4]]]".
        * (* Disj 1: lr↦#false, fill_proph_bs ps bs (bs = false::bs') *)
          iDestruct "Hd1" as (bs) "(>Hlr & >(Hpfl & %Hbs))".
          destruct Hbs as [bs' ->].
          iDestruct "Hpfl" as (us) "[Hp %Heqbs]".
          wp_apply (wp_resolve_proph with "Hp"). iIntros (pvs') "[%Heq Hp]".
          subst us. simpl in Heqbs. discriminate.
        * (* Disj 2: lr↦#true, proph_bs ps bs *)
          iDestruct "Hd2" as (bs) "(>Hlr & >Hpb)".
          iDestruct "Hpb" as (us) "[Hp %Heqbs]".
          wp_apply (wp_resolve_proph with "Hp"). iIntros (pvs') "[%Heq Hp]".
          subst us. simpl in Heqbs.
          iMod ("Hclose" with "[$Htok Hlb Hlr Hp]") as "Htok".
          { iNext. iFrame "Hlb". iRight. iLeft. iExists (longest_valid_prefix_bool (map snd pvs')).
            iFrame "Hlr". iExists pvs'. by iFrame. }
          wp_pures. wp_bind (! _)%E.
          iMod (na_inv_acc with "Hinv Htok") as "(Hinvo & Htok & Hclose)";
            [solve_ndisj|solve_ndisj|].
          iDestruct "Hinvo" as "(>Hlb' & Hrest)".
          wp_load.
          iMod ("Hclose" with "[$Htok Hlb' Hrest]") as "Htok"; [iNext; iFrame|].
          wp_pures.
          wp_apply (s_ser_spec auth_scheme _ (InjRV #h)).
          { iRight. iExists _. iSplit; [done|]. by iExists h. }
          iIntros (sv) "#Hs".
          iDestruct "Hs" as "[[%Hbad _] | (%w & %s' & [%Heq ->] & #Hser)]";
            [done|].
          injection Heq as <-.
          iDestruct "Hser" as %(s0 & Heqw & ->). injection Heqw as <-.
          rewrite /filled_string /simple_string.
          iApply "HΨ".
          iFrame "Htok".
          iEval (rewrite -{1}(Qp.div_2 q) intransit_split) in "Hintr".
          iDestruct "Hintr" as "[$ _]".
          iIntros (γl) "Hg Hpen %Hsz Hbig".
          apply size_empty_inv in Hsz. fold_leibniz. subst γl.
          iFrame "Hg Hpen". by rewrite big_sepS_empty.
        * (* Disj 3: lr↦#false, empty_proph_bs ps. After resolve, proph_bs no longer empty.
             Close as Disj 4 (which only requires proph_bs and intransit q'), giving q/4 of q. *)
          iDestruct "Hd3" as "(>Hlr & >Hpb)".
          iDestruct "Hpb" as (us) "[Hp %Heqbs]".
          wp_apply (wp_resolve_proph with "Hp"). iIntros (pvs') "[%Hresolve Hp]".
          iEval (rewrite -{1}(Qp.div_2 q) intransit_split) in "Hintr".
          iDestruct "Hintr" as "[Hintr Hintr_keep]".
          iEval (rewrite -{1}(Qp.div_2 (q/2)) intransit_split) in "Hintr".
          iDestruct "Hintr" as "[Hintr_inv _]".
          iMod ("Hclose" with "[$Htok Hlb Hlr Hp Hintr_inv]") as "Htok".
          { iNext. iFrame "Hlb". iRight. iRight. iRight.
            iExists (longest_valid_prefix_bool (map snd pvs')), (q/2/2)%Qp, false.
            iFrame "Hlr Hintr_inv". iExists pvs'. by iFrame. }
          wp_pures. wp_bind (! _)%E.
          iMod (na_inv_acc with "Hinv Htok") as "(Hinvo & Htok & Hclose)";
            [solve_ndisj|solve_ndisj|].
          iDestruct "Hinvo" as "(>Hlb' & Hrest)".
          wp_load.
          iMod ("Hclose" with "[$Htok Hlb' Hrest]") as "Htok"; [iNext; iFrame|].
          wp_pures.
          wp_apply (s_ser_spec auth_scheme _ (InjRV #h)).
          { iRight. iExists _. iSplit; [done|]. by iExists h. }
          iIntros (sv) "#Hs".
          iDestruct "Hs" as "[[%Hbad _] | (%w & %s' & [%Heq3 ->] & #Hser)]";
            [done|].
          injection Heq3 as <-.
          iDestruct "Hser" as %(s0 & Heqw & ->). injection Heqw as <-.
          rewrite /filled_string /simple_string.
          iApply "HΨ".
          iFrame "Htok Hintr_keep".
          iIntros (γl) "Hg Hpen %Hsz Hbig".
          apply size_empty_inv in Hsz. fold_leibniz. subst γl.
          iFrame "Hg Hpen". by rewrite big_sepS_empty.
        * (* Disj 4: lr↦#b, proph_bs ps bs, intransit q' *)
          iDestruct "Hd4" as (bs q' b) "(>Hlr & >Hpb & >Hintr')".
          iDestruct "Hpb" as (us) "[Hp %Heqbs]".
          wp_apply (wp_resolve_proph with "Hp"). iIntros (pvs') "[%Heq Hp]".
          subst us.
          iMod ("Hclose" with "[$Htok Hlb Hlr Hp Hintr']") as "Htok".
          { iNext. iFrame "Hlb". iRight. iRight. iRight.
            iExists (longest_valid_prefix_bool (map snd pvs')), q', b.
            iFrame "Hlr Hintr'". iExists pvs'. by iFrame. }
          wp_pures. wp_bind (! _)%E.
          iMod (na_inv_acc with "Hinv Htok") as "(Hinvo & Htok & Hclose)";
            [solve_ndisj|solve_ndisj|].
          iDestruct "Hinvo" as "(>Hlb' & Hrest)".
          wp_load.
          iMod ("Hclose" with "[$Htok Hlb' Hrest]") as "Htok"; [iNext; iFrame|].
          wp_pures.
          wp_apply (s_ser_spec auth_scheme _ (InjRV #h)).
          { iRight. iExists _. iSplit; [done|]. by iExists h. }
          iIntros (sv) "#Hs".
          iDestruct "Hs" as "[[%Hbad _] | (%w & %s' & [%Heq ->] & #Hser)]";
            [done|].
          injection Heq as <-.
          iDestruct "Hser" as %(s0 & Heqw & ->). injection Heqw as <-.
          rewrite /filled_string /simple_string.
          iApply "HΨ".
          iFrame "Htok".
          iEval (rewrite -{1}(Qp.div_2 q) intransit_split) in "Hintr".
          iDestruct "Hintr" as "[$ _]".
          iIntros (γl) "Hg Hpen %Hsz Hbig".
          apply size_empty_inv in Hsz. fold_leibniz. subst γl.
          iFrame "Hg Hpen". by rewrite big_sepS_empty.
      + (* Emp branch: c = 1, s = suspended_string = none_ser_str *)
        iDestruct "Hemp" as (p lb lr a h r) "([-> ->] & #Hinv)".
        rewrite /authenticatable_base_susp.auth_susp_ser_p. wp_pures.
        wp_bind (ResolveProph _ _)%E.
        iMod (na_inv_acc with "Hinv Htok") as "(Hinvo & Htok & Hclose)";
          [solve_ndisj|solve_ndisj|].
        iDestruct "Hinvo" as "[>Hd1 | >Hd2]".
        * (* First disjunct: lb↦#false, lr↦#false, unfill_proph_bs ps bs *)
          iDestruct "Hd1" as (bs) "(Hlb & Hlr & Hpfl & %Heqbs)".
          destruct Heqbs as [bs' ->].
          iDestruct "Hpfl" as (us) "[Hp %Heqbs2]".
          wp_apply (wp_resolve_proph with "Hp"). iIntros (pvs') "[%Heq Hp]".
          subst us. simpl in Heqbs2. discriminate.
        * (* Second disjunct: lb↦#true, lr↦#r, proph_bs ps bs.
             Keep the invariant open across both resolve_proph and load. *)
          iDestruct "Hd2" as (r' bs n γ) "(Hlb & Hlr & Hpb & #Hlbfrag & #Htrans)".
          iDestruct "Hpb" as (us) "[Hp %Heqbs]".
          wp_apply (wp_resolve_proph with "Hp"). iIntros (pvs') "[%Heq Hp]".
          subst us.
          wp_pures.
          wp_load.
          iMod ("Hclose" with "[$Htok Hlb Hlr Hp]") as "Htok".
          { iNext. iRight. iExists r', (longest_valid_prefix_bool (map snd pvs')), n, γ.
            iFrame "Hlb Hlr Hlbfrag Htrans". iExists pvs'. by iFrame. }
          wp_pures.
          (* option_ser' applied to InjL #"" evaluates to #none_ser_str = #suspended_string *)
          rewrite /auth_scheme /option_serialization_scheme. simpl.
          rewrite /option_ser'. wp_pures.
          rewrite /suspended_string /none_ser_str.
          iApply "HΨ".
          iModIntro. iFrame "Htok".
          iEval (rewrite -{1}(Qp.div_2 q) intransit_split) in "Hintr".
          iDestruct "Hintr" as "[$ _]".
          iIntros (γl) "Hg Hpen %Hsz Hbig".
          (* size γl = 1, γl = {γ'}. We have lg_mapg_p_frag lb γ' from Hbig and #Hlbfrag for γ.
             By agreement, γ' = γ. Then apply Htrans to get visit_reached_done γ. *)
          assert (∃ γ', γl = {[ γ' ]}) as [γ' Hγl].
          { destruct (size_1_elem_of γl) as [γ' Heqv]; [done|].
            exists γ'. by fold_leibniz. }
          subst γl.
          rewrite big_sepS_singleton.
          iDestruct "Hbig" as (lb') "[Hlbfrag' %Hsub]".
          destruct Hsub as (p' & lb2 & lr2 & a2 & h2 & Heqv & Heqlb).
          injection Heqv as Hlb1 Hlr1 Ha1 Hh1 Hp1. injection Heqlb as Hlb2.
          subst lb2. assert (lb' = lb) as -> by congruence.
          iDestruct (lg_mapg_p_agree with "Hlbfrag Hlbfrag'") as "(<- & _ & Hlbfrag'')".
          iDestruct ("Htrans" with "Hg") as "[$ #Hvrd]".
          iFrame "Hpen". rewrite big_sepS_singleton. iFrame "Hvrd".
          iExists lb. iFrame "Hlbfrag''". iPureIntro.
          eexists p, lb, lr, a, h. done.
    - (* 3. suspend_v_deser_spec (combined) *)
      iIntros "!#" (t' a1 un_a1 a2 a3 s_def s_pred K tᵥ3 id m vm pn ctr mlg_p) "Hv".
      rewrite /authenticatable_base_susp.auth_deser_v. v_pures.
      iModIntro. iExists _. iFrame "Hv".
      iIntros "!#" (K' tᵥ3' Ψ).
      iIntros "!# (%Hunsusp & #HA & #Hser & Hvm & Hlgp & Hmpg & Hpenc & Hv) HΨ".
      (* Project HA = (lrel_auth A) a1 a2 a3 into its tern / un parts. *)
      iDestruct "HA" as "[HAtern #HAun]".
      iEval (rewrite interp_var3_ext4 interp_var0_ext1) in "HAtern".
      iEval (rewrite /lrel_auth /=) in "HAtern".
      (* Now [HAtern : ▷ lrel_auth_tern A_inner a1 a2 a3]. *)
      (* Run the prover-side allocation FIRST. Each wp_alloc and wp_new_proph
         takes a step which strips a [▷]; after the allocations we can
         destruct HAtern (which is currently under [▷]). The prover
         allocation doesn't depend on the case-split, so we can defer it. *)
      rewrite /authenticatable_base_susp.auth_suspend_p.
      (* unsusp t' a1 un_a1 only has the tauth-shape branch consistent with
         HAtern (which witnesses a1 is a Box via auth_pv). For Pass 1 we
         keep t' as a parameter and dispatch the non-tauth cases as separate
         pure-impossibility leaves; the tauth case is the main scaffold. *)
      destruct t' as [| | | |] eqn:Ht'.
      1-4: (* tprod / tsum / tstring / tint: a1 ≠ BoxV, but HAtern witnesses
              a1 = BoxV via auth_pv. Pass 2 will derive False uniformly. *)
           simpl in Hunsusp; admit.
      (* tauth : the substantive case. *)
      simpl in Hunsusp.
      destruct Hunsusp as (lb_p & lr_p & a_p & h_p & p_p & -> & ->).
      wp_pures.
      wp_apply wp_new_proph; first done.
      iIntros (us_new p_new) "Hp_new".
      wp_alloc lr_new as "Hlr_new". wp_alloc lb_new as "Hlb_new".
      wp_pures.
      (* The wp_pures / wp_alloc / wp_apply above each stripped a later, so
         [▷ HAtern] should be usable. Unfold lrel_auth_tern / lrel_car to
         expose the existential and conjunction structure. *)
      iEval (cbv [lrel_auth_tern lrel_car]) in "HAtern".
      iDestruct "HAtern" as (t_in v2_in a1_in a2_in un_a1_in s_in)
        "([%Ha2_eq %Hunsusp_in] & #Hser_in & #HA_in & #Hpv)".
      (* Case-split the verifier-side [auth_pv un_a1 a1 v2_in s_in]
         disjunct. *)
      iDestruct "Hpv" as (lb_pv lr_pv ps_pv Ha1_eq) "[Hpv_fill | Hpv_susp]".
      + (* Filled-side: v2_in = InjLV #(hash s_in). *)
        iDestruct "Hpv_fill" as "[%Hv2_in_eq #Hinv_fill]".
        (* Pass 2: step verifier through [s_deserializer s_pred] and
           case-split on whether s_pred parses to Some (hash s_in)
           (filled-match) or otherwise (mismatch). *)
        admit.
      + (* Suspender-side: v2_in = InjRV #susp_pv. *)
        iDestruct "Hpv_susp" as (γ_pv s'_pv susp_pv psusp_pv pid_pv Hv2_in_eq)
          "(#Hlbf_pv & #Hinv_unfill_pv & #Hpvf_pv & #Hsnap_pv &
            #Hlbv_pv & %Hs'_pv_eq & #Hinv_susp_v_pv)".
        (* Pass 2: step verifier through [s_deserializer s_pred] and
           case-split on whether s_pred parses to None
           (suspender-match) or otherwise (mismatch). *)
        admit.
    - (* 4. unsuspend_spec *) admit.
    - (* 5. v_ser_spec *) admit.
    - (* 6. v_auth_ser_spec *) admit.
    - (* 7. v_count_spec *)
      iIntros (K tᵥ7 a c id Nc v_outer) "!# Hcnt Hspec".
      iDestruct "Hcnt" as (vcnt ->) "Hbr".
      rewrite /auth_count. v_pures.
      iDestruct "Hbr" as "[(%h & [-> ->]) | (%susp & -> & Hbr)]".
      + (* InjL h, c = 0 *)
        v_pures. iModIntro. iFrame.
        iExists (InjLV #h). iSplit; [done|]. iLeft. iExists h. done.
      + (* InjR #susp *)
        v_pures.
        iDestruct "Hbr" as "[(%h & Hpts & ->) | (%p & %γ & %susp_pid & Hbr)]".
        * (* susp ↦ᵥ InjRV #h, c = 0 *)
          v_load. v_pures. iModIntro. iFrame.
          iExists (InjRV #susp). iSplit; [done|]. iRight. iExists susp.
          iSplit; [done|]. iLeft. iExists h. by iFrame.
        * (* susp ↦ᵥ InjLV ..., c = 1 *)
          iDestruct "Hbr" as
            "(Hlg & Hpts & -> & Hmpg & Hcap & Hpval & Hsnap & Hrest)".
          v_load. v_pures. iModIntro. iFrame.
          iExists (InjRV #susp). iSplit; [done|]. iRight. iExists susp.
          iSplit; [done|]. iRight. iExists p, γ, susp_pid. by iFrame.
  Admitted.

End authenticatable.
