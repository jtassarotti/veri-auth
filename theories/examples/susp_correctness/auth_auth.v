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
      { (* tprod: [Hser] gives a1 is a pair; auth_pv gives a1 = BoxV ... *)
        simpl in Hunsusp.
        destruct Hunsusp as (vp1 & vp2 & un_vp1 & un_vp2 & Ha1eq & _ & _ & _).
        wp_pure _.
        iEval (cbv [lrel_auth_tern lrel_car]) in "HAtern".
        iDestruct "HAtern" as (t_in v2_in a1_in a2_in un_a1_in s_in)
          "([%Ha2_eq %Hunsusp_in] & _ & _ & #Hpv)".
        iDestruct "Hpv" as (lb_pv lr_pv ps_pv Ha1_eq) "_".
        rewrite Ha1_eq in Ha1eq. discriminate. }
      { (* tsum: a1 is InjLV/InjRV via Hunsusp; auth_pv gives a1 = BoxV. *)
        simpl in Hunsusp.
        destruct Hunsusp as [(vp1 & un_vp1 & Ha1eq & _ & _) |
                              (vp2 & un_vp2 & Ha1eq & _ & _)];
          wp_pure _;
          iEval (cbv [lrel_auth_tern lrel_car]) in "HAtern";
          iDestruct "HAtern" as (t_in v2_in a1_in a2_in un_a1_in s_in)
            "([%Ha2_eq %Hunsusp_in] & _ & _ & #Hpv)";
          iDestruct "Hpv" as (lb_pv lr_pv ps_pv Ha1_eq) "_";
          rewrite Ha1_eq in Ha1eq; discriminate. }
      { (* tstring: [Hser : string_is_ser a1 s_def] gives a1 = #s';
           [auth_pv] in HAtern gives a1 = BoxV ... — contradiction. *)
        iEval (simpl) in "Hser".
        iDestruct "Hser" as %(s' & Ha1eq & _).
        wp_pure _.
        iEval (cbv [lrel_auth_tern lrel_car]) in "HAtern".
        iDestruct "HAtern" as (t_in v2_in a1_in a2_in un_a1_in s_in)
          "([%Ha2_eq %Hunsusp_in] & _ & _ & #Hpv)".
        iDestruct "Hpv" as (lb_pv lr_pv ps_pv Ha1_eq) "_".
        rewrite Ha1_eq in Ha1eq. discriminate. }
      { (* tint: similar to tstring. *)
        iEval (simpl) in "Hser".
        iDestruct "Hser" as %(z' & Ha1eq & _).
        wp_pure _.
        iEval (cbv [lrel_auth_tern lrel_car]) in "HAtern".
        iDestruct "HAtern" as (t_in v2_in a1_in a2_in un_a1_in s_in)
          "([%Ha2_eq %Hunsusp_in] & _ & _ & #Hpv)".
        iDestruct "Hpv" as (lb_pv lr_pv ps_pv Ha1_eq) "_".
        rewrite Ha1_eq in Ha1eq. discriminate. }
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
      + (* Filled-side: v2_in = InjLV #(hash s_in). The prover (a1) is
           [BoxV (#lb_pv, #lr_pv, a_p, #h_p, #ps_pv)]; the verifier-side
           recorded [v2_in = InjLV #(hash s_in)] under [Hinv_fill].

           Pass 2 — leaf strategy for filled-side:
           1) Step verifier through [auth_deser_v_partial s_pred]:
              after [v_pures] the verifier holds [match:
              auth_scheme.s_deserializer #s_pred with NONE => NONE |
              SOME v => match v with NONE => SOME (SOME (InjR (ref
              (#id, NewProph)))) | SOME h => SOME (SOME (InjL h)) end
              end]. The verifier wp is a [GenWp] (gwp_spec_verifier
              from spec_rules.v); apply [s_deser_sound auth_scheme] via
              [iMod] (or convert the goal to a gwp via [iApply gwp_*]
              and use [gwp_apply]) to obtain an [option val] outcome
              [o].
           2) Case [o = None]: verifier match takes NONE; final
              spec_verifier holds NONEV. MISMATCH (s_pred didn't parse
              but s_real does). Deliver right disjunct: [⌜s_pred ≠
              s_real⌝ ∗ lrel_tern_un A a1'] (note Ψ is the post
              continuation; we apply it to construct the witness).
           3) Case [o = Some v]:
              a) [v = NONEV]: verifier takes InjR branch, v_alloc a
                 fresh susp ref, step_verifier_newproph for a fresh
                 proph, final value [SOMEV (SOMEV (InjRV #susp_new))].
                 This represents the SUSPENDER form, but we're in the
                 filled-side. MISMATCH. (Note: [s_pred = some_ser_str
                 ""], not the filled string.)
              b) [v = SOMEV w]: verifier returns [SOMEV (SOMEV (InjLV
                 w))]. Need to know [w = #h] for some hash. From
                 s_deser_sound's post, [s_is_ser auth_scheme (SOMEV v)
                 s_pred] holds, and from the option/string structure,
                 [w = #h'] for some [h']. Sub-case:
                 i) [h' = hash s_in]: FILLED-MATCH. Build left
                    disjunct: c = 0, γl = ∅, mapg_auth m unchanged,
                    A a1' a2' a3 with a2' = SOMEV (InjLV #(hash s_in))
                    (recursive — needs fresh fill_inv on the new
                    BoxV).
                 ii) [h' ≠ hash s_in]: MISMATCH. Deliver
                    [lrel_tern_un A a1'].

           In ALL match/mismatch leaves, the post requires
           [susp_p_ser_spec_at ser t_real c a1' s_real]: a Hoare
           triple specifying that running [auth_susp_ser_p a1']
           returns [#s_real] (where s_real = filled_string h_p for
           filled or suspended_string for suspender form). This spec
           is provable by re-running the case-2 prover spec at the
           new BoxV — but it requires a fresh seq_inv on the new
           BoxV. We DO have a NewProph + lb_new ↦ #false +
           lr_new ↦ #false from the prover-side allocation, but the
           disjuncts of [susp_p_fill_inv] / [susp_p_unfill_inv]
           constrain the prophecy values, intransit tokens, or
           require [lg_mapg_p_frag] frags. Without these, the fresh
           seq_inv allocation is blocked.

           Leaving as admit — requires committing to a specific
           invariant disjunct + setting up matching resources. *)
        admit.
      + (* Suspender-side: v2_in = InjRV #susp_pv. *)
        iDestruct "Hpv_susp" as (γ_pv s'_pv susp_pv psusp_pv pid_pv Hv2_in_eq)
          "(#Hlbf_pv & #Hinv_unfill_pv & #Hpvf_pv & #Hsnap_pv &
            #Hlbv_pv & %Hs'_pv_eq & #Hinv_susp_v_pv)".
        (* Pass 2 — leaf strategy for suspender-side (symmetric):
           1) Step verifier through [auth_deser_v_partial s_pred].
           2) Case [o = None] (parse fail): MISMATCH. s_real here is
              [some_ser_str (string_ser_str h_p)] from the prover's
              [auth_susp_ser_p_emp] disjunct's [s = suspended_string =
              none_ser_str] — wait actually for the suspender case the
              prover serializes to [suspended_string = none_ser_str].
              So [s_real = none_ser_str = "N"], a parsable string.
              Then [o = None] means s_pred is unparsable, so
              [s_pred ≠ s_real].
           3) Case [o = Some v]:
              a) [v = SOMEV w]: verifier returns [SOMEV (SOMEV (InjL
                 w))], representing filled form. MISMATCH against the
                 prover's suspender form.
              b) [v = NONEV]: verifier takes InjR branch, allocates
                 fresh susp ref [susp_new] via [v_alloc] and fresh
                 proph via [step_verifier_newproph]. SUSPENDER-MATCH.
                 Build the match payload:
                  c = 1
                  Fresh γ_new via [lg_mapg_p_insert] (needs
                    [meta_token lb_new ⊤] — produced by [wp_alloc]).
                  γl = {γ_new}, [penset_frag] via
                    [visited_insert]
                  Fresh id_new (e.g., ctr+1) via update on
                    [visited_mapg_auth].
                  mapg_auth ← mapg_insert m id_new (SOMEV (InjRV
                    #susp_new))
                  pencount_frag (pn+1) (from [visited_insert])
                  pval_frag id_new susp_new (fresh)
                  pval_snapshot susp_new pid_existing (re-use the
                    existing pid? or build a new one — likely the new
                    susp_new gets a fresh chain entry)
                  lg_mapg_frag susp_new γ_new (paired with the
                    [lg_mapg_p_frag lb_new γ_new])
                  Allocate two seq_invs:
                    [seq_inv (prover_susp_n a1') (susp_p_unfill_inv
                       ps_new lb_new lr_new)] via [na_inv_alloc]
                       (body: lb_new ↦ #false ∗ lr_new ↦ #false ∗
                       unfill_proph_bs ps_new bs — needs bs to start
                       with true; if the freshly-allocated proph's
                       values don't satisfy this, we'd use the
                       OTHER unfill disjunct which has lb↦#true ∗ ...
                       — but we have lb↦#false. Genuinely tricky.)
                    [seq_inv (ver_susp_n susp_new) (auth_susp_v_ser_proph_inv
                       pid_new a2' s'_new)]
                  Plus all the [A a1' a2' a3], [sub_susp_count_frags],
                  [ser_v_proph], etc.

           Leaving as admit — symmetric to filled-side, same blocker. *)
        admit.
    - (* 4. unsuspend_spec *)
      iIntros (E a1 a2 a3 HE Ψ) "!# (HA & Htok & Hintr) HΨ".
      rewrite /authenticatable_base_susp.auth_unsuspend_p.
      wp_pure _. (* strips ▷ on HA *)
      iDestruct "HA" as "[HAtern _]".
      iEval (rewrite /lrel_auth /=) in "HAtern".
      iEval (cbv [lrel_auth_tern lrel_car]) in "HAtern".
      iDestruct "HAtern" as (t_in v2' a1_in a2_in un_a1_in s_in)
        "([%Ha2_eq %Hunsusp_in] & _ & _ & #Hpv)".
      iDestruct "Hpv" as (lb lr ps Ha1_eq) "[Hpv_fill | Hpv_susp]".
      + (* Fill branch — keep inv open across resolve+pure+store, close as Disj 2. *)
        iDestruct "Hpv_fill" as "[%Hv2'_eq #Hinv]".
        rewrite Ha1_eq. wp_pures.
        wp_bind (ResolveProph _ _)%E.
        iMod (na_inv_acc with "Hinv Htok") as "(Hinvo & Htok & Hclose)";
          [solve_ndisj|solve_ndisj|].
        iDestruct "Hinvo" as "(>Hlb & Hrest)".
        iDestruct "Hrest" as "[Hd1 | [Hd2 | [Hd3 | Hd4]]]".
        * (* Disj 1: lr↦#false, fill_proph_bs ps bs (bs = false::bs') — consistent. *)
          iDestruct "Hd1" as (bs) "(>Hlr & >(Hpfl & %Hbs))".
          destruct Hbs as [bs' ->].
          iDestruct "Hpfl" as (us) "[Hp %Heqbs]".
          wp_apply (wp_resolve_proph with "Hp"). iIntros (pvs') "[%Heq Hp]".
          subst us.
          wp_pures. wp_store.
          iMod ("Hclose" with "[$Htok Hlb Hlr Hp]") as "Htok".
          { iNext. iFrame "Hlb". iRight. iLeft.
            iExists (longest_valid_prefix_bool (map snd pvs')).
            iFrame "Hlr". iExists pvs'. by iFrame. }
          wp_pures. iApply "HΨ". iModIntro. iFrame "Htok Hintr". iSplit.
          { iPureIntro. simpl. by eexists lb, lr, _, (hash s_in), ps. }
          { iPureIntro. simpl. unfold authenticatable_base_susp.auth_unsusp_ser_p.
            by eexists _, (hash s_in). }
        * (* Disj 2: lr↦#true, proph_bs ps bs *)
          iDestruct "Hd2" as (bs) "(>Hlr & >Hpb)".
          iDestruct "Hpb" as (us) "[Hp %Heqbs]".
          wp_apply (wp_resolve_proph with "Hp"). iIntros (pvs') "[%Heq Hp]".
          subst us.
          wp_pures. wp_store.
          iMod ("Hclose" with "[$Htok Hlb Hlr Hp]") as "Htok".
          { iNext. iFrame "Hlb". iRight. iLeft.
            iExists (longest_valid_prefix_bool (map snd pvs')).
            iFrame "Hlr". iExists pvs'. by iFrame. }
          wp_pures. iApply "HΨ". iModIntro. iFrame "Htok Hintr". iSplit.
          { iPureIntro. simpl. by eexists lb, lr, _, (hash s_in), ps. }
          { iPureIntro. simpl. unfold authenticatable_base_susp.auth_unsusp_ser_p.
            by eexists _, (hash s_in). }
        * (* Disj 3: lr↦#false, empty_proph_bs ps — resolves contradict empty. *)
          iDestruct "Hd3" as "(>Hlr & >Hpb)".
          iDestruct "Hpb" as (us) "[Hp %Heqbs]".
          wp_apply (wp_resolve_proph with "Hp"). iIntros (pvs') "[%Heq Hp]".
          subst us. simpl in Heqbs. discriminate.
        * (* Disj 4: lr↦#b, proph_bs ps bs, intransit q' *)
          iDestruct "Hd4" as (bs q' b) "(>Hlr & >Hpb & >Hintr')".
          iDestruct "Hpb" as (us) "[Hp %Heqbs]".
          wp_apply (wp_resolve_proph with "Hp"). iIntros (pvs') "[%Heq Hp]".
          subst us.
          wp_pures. wp_store.
          iMod ("Hclose" with "[$Htok Hlb Hlr Hp Hintr']") as "Htok".
          { iNext. iFrame "Hlb". iRight. iRight. iRight.
            iExists (longest_valid_prefix_bool (map snd pvs')), q', true.
            iFrame "Hlr Hintr'". iExists pvs'. by iFrame. }
          wp_pures. iApply "HΨ". iModIntro. iFrame "Htok Hintr". iSplit.
          { iPureIntro. simpl. by eexists lb, lr, _, (hash s_in), ps. }
          { iPureIntro. simpl. unfold authenticatable_base_susp.auth_unsusp_ser_p.
            by eexists _, (hash s_in). }
      + (* Suspender branch *)
        iDestruct "Hpv_susp" as (γ_pv s'_pv susp_pv psusp_pv pid_pv Hv2'_eq)
          "(#Hlbf_pv & #Hinv_unfill & _)".
        rewrite Ha1_eq. wp_pures.
        wp_bind (ResolveProph _ _)%E.
        iMod (na_inv_acc with "Hinv_unfill Htok") as "(Hinvo & Htok & Hclose)";
          [solve_ndisj|solve_ndisj|].
        iDestruct "Hinvo" as "[>Hd1 | >Hd2]".
        * (* Disj 1: lb↦false, lr↦false, unfill_proph_bs ps bs (bs = true::bs') —
             resolve to SOMEV #false would need head false but bs head is true. *)
          iDestruct "Hd1" as (bs) "(Hlb & Hlr & Hpfl & %Heqbs)".
          destruct Heqbs as [bs' ->].
          iDestruct "Hpfl" as (us) "[Hp %Heqbs2]".
          wp_apply (wp_resolve_proph with "Hp"). iIntros (pvs') "[%Heq Hp]".
          subst us. simpl in Heqbs2. discriminate.
        * (* Disj 2: lb↦true, lr↦r, proph_bs ps bs *)
          iDestruct "Hd2" as (r bs n γ) "(Hlb & Hlr & Hpb & #Hlbfrag & #Htrans)".
          iDestruct "Hpb" as (us) "[Hp %Heqbs]".
          wp_apply (wp_resolve_proph with "Hp"). iIntros (pvs') "[%Heq Hp]".
          subst us.
          wp_pures. wp_store.
          iMod ("Hclose" with "[$Htok Hlb Hlr Hp]") as "Htok".
          { iNext. iRight. iExists true, (longest_valid_prefix_bool (map snd pvs')), n, γ.
            iFrame "Hlb Hlr Hlbfrag Htrans". iExists pvs'. by iFrame. }
          wp_pures. iApply "HΨ". iModIntro. iFrame "Htok Hintr". iSplit.
          { iPureIntro. simpl. by eexists lb, lr, _, (hash s_in), ps. }
          { iPureIntro. simpl. unfold authenticatable_base_susp.auth_unsusp_ser_p.
            by eexists _, (hash s_in). }
    - (* 5. v_ser_spec *)
      iIntros (K tᵥ5 a s id Nc v_outer) "!# Hcnt #Hser Hspec".
      iDestruct "Hcnt" as (vcnt ->) "Hbr".
      iDestruct "Hser" as (vser Hser_eq) "Hser_br".
      injection Hser_eq as <-.
      rewrite /authenticatable_base_susp.auth_ser_v. v_pures.
      iDestruct "Hbr" as "[(%h & [-> %Hc]) | (%susp & -> & Hbr)]".
      + (* InjL h, c = 0 — auth_fill_ser_v matches *)
        iDestruct "Hser_br" as "[Hfill | Hsusp]"; last first.
        { iDestruct "Hsusp" as (susp' Heqsusp) "_". done. }
        iDestruct "Hfill" as %(h' & -> & Heq). injection Heq as <-.
        v_pures.
        rewrite /auth_scheme /option_serialization_scheme /=.
        unfold s_serializer'. simpl.
        rewrite /option_ser'''. v_pures.
        rewrite /string_serialization /=.
        unfold s_serializer'. simpl.
        rewrite /string_ser' /string_ser. v_pures.
        iModIntro.
        rewrite /filled_string /simple_string /some_ser_str /string_ser_str.
        iSplitR.
        { iExists (InjLV #h). iSplit; [done|]. iLeft. iExists h. done. }
        iFrame "Hspec".
        iExists (InjLV #h). iSplit; [done|]. iLeft. iExists h. done.
      + (* InjR #susp *)
        iDestruct "Hbr" as "[(%h & Hpts & %Hc) | (%p & %γ & %susp_pid & Hbr)]"; last first.
        { (* c = 1 contradicts outer c = 0 *)
          iDestruct "Hbr" as "(_ & _ & %Hc & _)". done. }
        (* c = 0 path: susp ↦ᵥ{#1/4} InjRV #h *)
        v_pures.
        v_load. v_pures.
        (* Hser_br: auth_fill_ser_v requires v1 = InjLV — contradiction.
           So it must be auth_susp_v_ser_proph, which has a seq_inv we
           cannot open without an na_own token. Admit this sub-case. *)
        iDestruct "Hser_br" as "[Hfill | Hsusp]".
        { iDestruct "Hfill" as %(h' & _ & Heq). done. }
        admit.
    - (* 6. v_auth_ser_spec *)
      iIntros (K tᵥ6 a1 a2 a3) "!# #HA Hspec".
      iEval (rewrite /lrel_auth /=) in "HA".
      iEval (cbv [lrel_auth_tern lrel_car]) in "HA".
      iDestruct "HA" as (t_in v2' a1' a2' un_a1 s_in)
        "(>[%Hv2_eq %Hunsusp_in] & #Hser_in & #HA_in & #Hpv)".
      subst a2.
      rewrite /authenticatable_base_susp.auth_ser_v.
      v_pures.
      iDestruct "Hpv" as (lb lr ps) "[>%Ha1_eq [Hpv_fill | Hpv_susp]]".
      + (* Fill branch: v2' = InjLV #(hash s_in). *)
        iDestruct "Hpv_fill" as "[>%Hv2'_eq _]".
        subst v2'. v_pures.
        rewrite /auth_scheme /option_serialization_scheme /=.
        unfold s_serializer'. simpl.
        rewrite /option_ser'''. v_pures.
        rewrite /string_serialization /=.
        unfold s_serializer'. simpl.
        rewrite /string_ser' /string_ser. v_pures.
        iModIntro.
        rewrite /filled_string /simple_string /some_ser_str /string_ser_str.
        iExists (some_ser_str (string_ser_str (hash s_in))).
        rewrite /some_ser_str /string_ser_str.
        iFrame "Hspec".
        iExists (InjLV #(hash s_in)). iSplit; [done|].
        iExists (hash s_in). done.
      + (* Suspender branch: v2' = InjRV #susp.
           Verifier reads !susp via v_load, which requires opening
           [seq_inv (ver_susp_n susp) (auth_susp_v_ser_proph_inv pid v2' s')].
           That seq_inv is an [na_inv] needing an na_own token, which the
           [v_auth_ser_spec] signature doesn't carry. Same blocker as
           case 5's suspender sub-case. *)
        admit.
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
