From auth.prelude Require Import stdpp.
From auth.rel_logic_tern_susp Require Export model spec_rules spec_tactics.
From auth.heap_lang Require Import primitive_laws derived_laws.
From auth.heap_lang.lib Require Import list map.
From auth.examples Require Export authentikit_susp.
From auth.examples.susp_correctness Require Import definitions helpers.
From iris.base_logic.lib Require Export na_invariants fancy_updates.

Section finish_specs.
  Context `{!authG Σ, !seqG Σ, !tabseqG Σ, !correctnessG Σ}.

  Local Lemma vmauth_pn_eq vm a b ctr (Heq : a = b) :
    visited_mapg_auth vm a ctr -∗ visited_mapg_auth vm b ctr.
  Proof. iIntros "H". rewrite Heq. iExact "H". Qed.

  Local Lemma pencount_pn_eq a b (Heq : a = b) :
    pencount_frag a -∗ pencount_frag b.
  Proof. iIntros "H". rewrite Heq. iExact "H". Qed.

	Lemma v_finish_spec :
    ∀ tᵥ K (a x ser : val) (st : loc),
      inv_v_susp_table st -∗
      spec_verifier tᵥ (fill K (v_finish #st a x ser))
			={⊤}=∗ ∃ (finish : val),
				v_finish_spec' finish x a ser ∗
				spec_verifier tᵥ (fill K finish).
  Proof.
   iIntros (?? ????) "#Htab Hi".
    rewrite /v_finish. v_pures.
    iFrame. iModIntro.
    iIntros "!#" (????? id ?) "#Hnmspc Htabtok Hlc Hser Hserspec Hc Hvauth Hst Hv".

    iMod (na_inv_acc with "Htab Htabtok") as "(Htabo & Htabtok & Hclose_tab)"; try solve_ndisj.
    iMod (lc_fupd_elim_later with "Hlc Htabo") as "Htabo".
    iDestruct "Htabo" as "[(%&%&%&%& %idctr &% & Hl & %Hm &
        Hbigsep & Hmauth &% & Hvmauth & %Hidinv & Hvisinv & Hst')|Hst']";
      last first.
    { by iPoseProof (tern_state_un_state_excl with "Hst Hst'") as "?". }

    (* iAssert (|={⊤}=> v_susp_big_sep m m' ∗ mapg_auth m' ∗ visited_mapg_auth vm dm ps pn idctr gm ∗ auth_v id a s ∗ intransit 1 ∗ seq_tok (E ∪ ↑ver_susp_n a))%I with "[Hbigsep Hmauth Hvmauth Hvauth Htok]" as ">(Hbigsep & Hmauth & Hvmauth & Hvauth & Hintr & Htok)".
    { iDestruct "Hvauth" as "[(-> & Hidtok & Hintr & %)|
        (%&%&%&%&%& -> &% & #Hpvfrag & % & #Hlbfrag & #Hvisdone & Hgetidtok & -> & Hvinv & Htrvinv & % & Hclose_inv)]".
      - iFrame. admit.
      - iDestruct "Htrvinv" as "[Hinv_1|Hinv_2]".
        + iDestruct "Hinv_1" as "(%s1&%& Hintr & Hrest)".
          iMod ("Hclose_inv" with "[$Htok Hrest]") as "Htok".
          { iNext. iLeft. iFrame. eauto. }
          iFrame. iRight. iFrame "∗ #".
          eauto.
        + iDestruct "Hinv_2" as "(%&%&%& Hlbfrag' & #Hvisfin & Hintr & (%&%&%&%&%&%&%&%& Hcap &       Hunfill & Hmfrag & %Hmsub & Hsusp & Hproph))".
          iPoseProof (mapg_auth_alive with "Hmauth Hmfrag") as (y) "%Hin".
          destruct Hin as [(? & Hin & ?)%Some_equiv_eq ?].
          edestruct (mapg_alive_lookup_Cinl _ _ _ y Hin) as (y' & Halive & Hyy'); first done.
          clear Hin. rename Halive into Hin.

          iDestruct (big_sepM_lookup_acc _ (mapg_alive m') pid _ Hin with "Hbigsep") as "[Hms Hbigsep]".
          iDestruct "Hms" as (ctr ????????[Hcgt [Hin' ?]]) 
              "(Hlc & Hxser & Hxserspec & Hxauth & Hxfrag & Hxc & Hxfin)".
          iPoseProof (visit_update_finished with "Hvmauth Hvisdone Hintr Hlbfrag Hsusp Hxc") as "Hxc".
           } *)

    iDestruct "Hvauth" as "[(-> & Hidtok & Hintr & Htok)|
        (%&%&%&%&%& -> & % & #Hvfrag & #Hpvfrag & #Hpvuneq & #Hlbfrag & #Hvisdone & Hgetidtok & -> & Hvinv & Htrvinv & Htok & Hclose_inv)]".
    - v_pures. v_bind (ser _).
      iMod ("Hserspec" with "Hc Hser Hv") as "(Hc & Hser & Hv) /=".
      v_pures. v_bind (Hash _).
      iMod (step_verifier_hash with "Hv") as "Hv /="; try done.
      v_pures; try solve_vals_compare_safe.
      case_bool_decide; simplify_eq; v_pures.

      (* iPoseProof (id_token_unused with "Hvmauth Hidtok") as "(%Hidunused & Hvmauth & Hidtok)". *)
      
      (* iDestruct "Hvisinv" as "[[Hstok' Hvisinv]|(% & Hstok' & Hvisinv)]";
        iDestruct (stok_agree with "Hstok Hstok'") as "%";
        simplify_eq. *)

      (* iPoseProof (stok_combine with "Hstok Hstok'") as "[_ Hstok_comp]".
      iMod (stok_update _ None with "Hstok_comp") as "Hstok_comp".
      iPoseProof (stok_split with "Hstok_comp") as "[Hstok Hstok']". *)

      iMod ("Hclose_tab" with "[$Htabtok Hbigsep Hmauth Hl Hvmauth Hvisinv Hst']") as "Htabtok".
      { iNext. iLeft. iFrame "% ∗". }
        (* iLeft. iFrame.
        iApply (big_sepM_mono with "Hvisinv").
        iIntros (k x0 Hkx) "Hvis".
        iIntros (id_inner Heq).
        assert (id_inner ≠ id0) by
          (intros ->; destruct (Hidunused k) as [Hu _]; apply Hu; rewrite Hkx Heq; reflexivity).
        iApply "Hvis"; try done. } *)
      
      by iFrame.

    - v_pures. v_bind (ser _).
      iMod ("Hserspec" with "Hc Hser Hv") as "(Hc & Hser & Hv) /=".
      v_pures.

      iDestruct "Htrvinv" as "[Hinv_1|Hinv_2]".
      + iDestruct "Hinv_1" as "(%s1&%& Hintr & (%&%&%&%& Hsusp & #Hfilled & Hrest))".
        rewrite /filled_string /simple_string in H1 H2. destruct! H2; simplify_eq.
        (* iPoseProof (lg_mapg_agree with "Hlbfrag' Hlbfrag") as "(-> & _ & _)". *)
        (* iDestruct (visit_finished_keep with "Hvisfin") as "[_ #Hvisreach2]". *)
        (* iDestruct (visited_reached_done_agree with "Hvisreach2 Hvisdone") as %->. *)

        simplify_eq. v_load. v_pures. v_bind (Hash _).
        iMod (step_verifier_hash with "Hv") as "Hv /="; try done.
        v_pures; try solve_vals_compare_safe.
        case_bool_decide; simplify_eq.

        (* iDestruct (vm_finished_no_done with "Hvmauth Hvisfin") as "(%Hno_done & Hvmauth)". *)

        (* iDestruct "Hvisinv" as "[[Hstok' Hvisinv]|(% & Hstok' & Hvisinv)]";
          iDestruct (stok_agree with "Hstok Hstok'") as "%";
          simplify_eq. *)

        (* iPoseProof (stok_combine with "Hstok Hstok'") as "[_ Hstok_comp]".
        iMod (stok_update _ None with "Hstok_comp") as "Hstok_comp".
        iPoseProof (stok_split with "Hstok_comp") as "[Hstok Hstok']". *)

        iMod ("Hclose_tab" with "[$Htabtok Hbigsep Hmauth Hl Hvmauth Hvisinv Hst']") as "Htabtok".
        { iFrame "%". iNext. iLeft. iFrame. } 
        (* iLeft. iFrame.
          iApply (big_sepM_mono with "Hvisinv").
          iIntros (k x0 Hkx) "Hvis".
          iIntros (id_inner Heq).
          assert (id_inner ≠ id0) by
            (intros ->; apply (Hno_done k); rewrite Hkx Heq; reflexivity).
          iApply "Hvis"; try done. } *)

        iMod ("Hclose_inv" with "[$Htok Hsusp Hrest]") as "Htok".
        { iNext. iLeft. iFrame "∗ #". eauto. }

        v_pures. iFrame. eauto.
        (* iModIntro.
        iIntros (?) "Hvisit".
        iDestruct (visit_reached_done_inj with "Hvisdone Hvisit") as %->.
        iFrame "Hvisfin". *)
        
      + iDestruct "Hinv_2" as "(%&%&%& Hlbfrag' & #Hvisfin & Hintr & (%&%&%&%&%&%&%& Hcap & Hunfill & Hmfrag & %Hmsub & Hsusp & Hproph))".

        simplify_eq H1. intros <-.
        simplify_eq H2. intros <-.
        iPoseProof (lg_mapg_agree with "Hlbfrag' Hlbfrag") as "(-> & _ & _)".

        simplify_eq. v_load. v_pures. v_bind (Hash _).
        iMod (step_verifier_hash with "Hv") as "Hv /="; try done.
        v_bind (ResolveProph _ _).
        iMod (step_verifier_resolveproph with "Hv") as "Hv /="; try done.
        v_pures. v_bind (Hash _).
        iMod (step_verifier_hash with "Hv") as "Hv /="; try done.
        v_pures. v_bind (_ <- _)%E.

        iPoseProof (mapg_auth_alive with "Hmauth Hmfrag") as (y) "%Hin".
        destruct Hin as [(? & Hin & ?)%Some_equiv_eq ?].
        edestruct (mapg_alive_lookup_Cinl _ _ _ y Hin) as (y' & Halive & Hyy'); first done.
        clear Hin. rename Halive into Hin.

        iDestruct (big_sepM_delete _ (mapg_alive m') pid _ Hin with "Hbigsep") as "[Hms Hbigsep]".

        iDestruct "Hms" as (ctr ????????[Hcgt [Hin' ?]]) 
            "(Hlc & Hxser & Hxserspec & Hxauth & Hxc & Hxfin)".

        (* iDestruct (pval_frag_agree with "Hxfrag Hpvfrag") as "<-". *)

        iDestruct "Hxc" as "(Hcap' & % & Hxc & Hxagg)".
        iDestruct (cap_frag_agree with "Hcap Hcap'") as "->".
        iAssert (sub_susp_count_frags t0 x1 ctr pid Nc0) with "[$Hcap $Hxc $Hxagg //]" as "Hxc".

        iDestruct (visit_reached_done_lookup with "Hvmauth Hvisdone") as "(%Hvmγ_old & Hvmauth)".

        (* iDestruct "Hvisinv" as "[[Hstok' Hvisinv]|(% & Hstok' & Hvisinv)]";
          iDestruct (stok_agree with "Hstok Hstok'") as "%";
          simplify_eq. *)

        assert (x1 = pv) as ->.
        { rewrite Hyy' in H3. rewrite H3 in H2. simpl in H2.
          fold_leibniz. by apply (inj to_agree) in H2. }
        
        iMod (count_update with "[//] Hlbfrag Hmfrag Hvisfin Hxc Hsusp Hunfill Hv") as "(Hintr' & Hxc & Hsusp & Hv & Hfill) /=".
        (* iEval (rewrite visited_map_update_finished_rewrite) in "Hvmauth". *)

        (* iPoseProof (stok_combine with "Hstok Hstok'") as "[_ Hstok_comp]".
        iMod (stok_update _ None with "Hstok_comp") as "Hstok_comp".
        iPoseProof (stok_split with "Hstok_comp") as "[Hstok Hstok']". *)

        (* iDestruct (vm_finished_no_done with "Hvmauth Hvisfin") as "(%Hno_done & Hvmauth)". *)

        (* assert (∃ v_γ, vm !! γ = Some v_γ) as [v_γ Hvγ].
        { destruct Hvmγ_old as [H' | H']; eauto. }.
        iPoseProof (big_sepM_insert_override_2 _ _ γ v_γ 
              (finished_val id0) with "Hvisinv []") as "Hvisinv"; try done. *)
        

        (* iPoseProof (big_sepM_mono
            (vm_big_sep_lam_set m id0)
            (vm_big_sep_lam_unset m)
          with "Hvisinv") as "Hvisinv".
        { iIntros (k x0' Hkx0) "Hvis".
          iIntros (id_inner Heq).
          iApply "Hvis"; try done.
          destruct (decide (γ = k)); simplify_eq.
          { rewrite lookup_insert in Hkx0. eauto. }
          rewrite lookup_insert_ne in Hkx0; try done.
          admit. } *)

        v_pures. v_load. v_bind (map_lookup _ _).
        iMod (gwp_map_lookup #pid d m () ⊤ _
          (λ v, ⌜from_option (λ p, v = SOMEV $p) (v = NONEV) (m !! #pid)⌝)%I
          with "[//] [] [$Hv //]") as (?) "[Hv %Hlook'] /="; try by iIntros "!>" (?).
        rewrite Hin' in Hlook'. simpl in Hlook'. simplify_eq.
        v_pures; try solve_vals_compare_safe.
        Unshelve. 2: done.
          
        case_decide as Heq; simplify_eq; v_pures.
        * v_load. v_bind (map_remove _ _).
          iMod (gwp_map_remove () ⊤ #pid d m _
            (λ d', ⌜is_map d' (delete #pid m)⌝)%I
            with "[//] [] [$Hv //]") as (?) "[Hv %Hm'] /="; 
            try by iIntros "!#" (?).
          Unshelve. 2: done.
          v_store. v_pures.

          assert (ctr = 1) as ->.
          { inversion Heq. lia. }
          simpl.

          iMod (mapg_remove_count_0 with "Hxc Hmauth") as "(Hxc & Hmauth & Hxrem)".
          { lia. }
          
          rewrite -mapg_alive_remove.
          iAssert (intransit 1) with "[Hintr Hintr']" as "Hintr".
          { iCombine "Hintr Hintr'" as "Hintr". iExact "Hintr". }

          (* iDestruct ("Hnmspc" with "[//] Hpvfrag") as "%Hpnmspc". *)

          iAssert (
            |={⊤}=> ∃ E',
              ⌜E' = E ∖ ↑ver_susp_n susp⌝ ∗
              □(∀ gpid gsusp gγ, ⌜gpid < pid⌝ -∗ pval_frag gpid gsusp -∗
                lg_mapg_frag gsusp gγ -∗ visit_reached_done gγ -∗ 
                ⌜↑(ver_susp_n gsusp) ⊆ E'⌝) ∗
              auth_transit_v E' pid a s0 ∗
              ((∃ γ vm',
                  ⌜vm' = (<[ γ := finished_val ]>vm)⌝ ∗
                  vm_big_sep (delete #pid m) vm' ∗
                  visited_mapg_auth vm' pn idctr) ∨
               (vm_big_sep (delete #pid m) vm ∗
                visited_mapg_auth vm pn idctr)) ∗
              mapg_auth (<[pid:=csum.Cinr (to_agree ())]> m') ∗
              [∗ map] k↦y0 ∈ mapg_alive (<[pid:=csum.Cinr (to_agree ())]> m'), 
                    v_susp_big_sep_lam m k y0)%I
              with "[Htok Hintr Hxauth Hvisinv Hvmauth Hmauth Hbigsep]"
            as ">(%&->& #Hnmspc' & Hxauth & Hvisvm & Hmauth & Hbigsep)".
          { iDestruct "Hxauth" as "[[-> Hidtok]|
              (%&%&%&%&%& ->& %& Hpvfrag' & #Hgpfrag & #Hgpuneq & #Hxlbfrag & #Hxvisdone & Hgetidtok & -> & #Hxinv)]".
            - iPoseProof (id_token_unused with "Hvmauth Hidtok") as "(%Hidunused & Hvmauth & Hidtok)".
              iFrame. iSplitR; eauto. iSplitR.
              { do 2 iModIntro. iIntros (gpid gsusp gγ Hgpid_lt) "H1 H2 H3".
                iDestruct ("Hnmspc" with "[] H1 H2 H3") as "%Hsubset".
                { iPureIntro. lia. }
                iPoseProof (pval_snapshot_neq with "Hpvuneq H1") as "%Hneq";
                  try lia.
                iPureIntro.
                assert ((↑ver_susp_n gsusp : coPset) ## ↑ver_susp_n susp) as Hdisj.
                { apply ndot_ne_disjoint. by intros ->. }
                set_solver. }
              iSplitL "Hintr". 
              { iLeft. iFrame. eauto. }
              iRight. iApply (big_sepM_mono with "Hvisinv").
              iIntros (k x' Hkx) "Hvis".
              iIntros (id_inner Heq').
              assert (id_inner ≠ pid).
              { intros ->. specialize (Hidunused k). simplify_eq. }
              rewrite (lookup_delete_ne); last first.
              { intros ?. simplify_eq. }
              by iApply "Hvis".

            - 
              iDestruct (pval_frag_agree with "Hpvfrag' Hpvfrag") as "<-".
              iPoseProof ("Hnmspc" with "[//] Hpvfrag Hxlbfrag Hxvisdone") as "%".

              iPoseProof (pval_snapshot_neq with "Hpvuneq Hpvfrag") as "%";
                try lia.
              
              (* simplify_eq. *)
              (* assert (susp ≠ susp0).
              { intros ?. simplify_eq. }

              assert ((E ∖ ↑ver_susp_n (InjRV #susp0) ∪ ↑ver_susp_n (InjRV #susp0)) = E) as ?.
              { rewrite difference_union_L. set_solver. }

              assert (↑ver_susp_n (InjRV #susp0) ⊈ E ∖ ↑ver_susp_n (InjRV #susp0)) as Hnsubset.
              { intros Hcont. apply (nclose_infinite (ver_susp_n (InjRV #susp0))).
                assert (↑ver_susp_n (InjRV #susp0) ≡@{coPset} ∅) as ->.
                { apply set_equiv. intros yy. split; [intros Hyy; specialize (Hcont yy Hyy); set_solver|set_solver]. }
                apply empty_finite. } *)

              iMod (na_inv_acc with "Hxinv Htok") as "(Hxinvo & Htok & Hclose_inv)"; try solve_ndisj.
              iDestruct "Hxinvo" as ">[Hinv_1|Hinv_2]".
              + iDestruct "Hinv_1" as "(%s1&% & (%&%&%&%& Hxsusp & #Hfilled & #Hxlbfrag' & #Hxvisfin))".
                destruct! H9. simplify_eq.
                iPoseProof (lg_mapg_agree with "Hxlbfrag' Hxlbfrag") as "(-> & _ & _)".
                iPoseProof ("Hgetidtok" with "Hxvisfin") as "Hidtok".
                iPoseProof (id_token_unused with "Hvmauth Hidtok") as "(%Hidunused & $ & Hidtok)".
                iFrame "Hmauth Hbigsep". iModIntro.
                iExists _. iSplit; eauto.
                iSplitR.
                { iModIntro. iIntros (gpid gsusp gγ Hgpid_lt) "H1 H2 H3".
                  iDestruct ("Hnmspc" with "[] H1 H2 H3") as "%Hsubset".
                  { iPureIntro. lia. }
                  iPoseProof (pval_snapshot_neq with "Hpvuneq H1") as "%Hneq";
                    try lia.
                  iPureIntro.
                  assert ((↑ver_susp_n gsusp : coPset) ## ↑ver_susp_n susp) as Hdisj.
                  { apply ndot_ne_disjoint. by intros ->. }
                  set_solver. }
                iSplitR "Hvisinv".
                { iRight. rewrite H10.
                  iFrame "Hgpfrag Hidtok Hxinv Hxlbfrag Htok".
                  repeat (iSplit; eauto). iSplitR. { by iIntros. }
                  repeat (iSplit; eauto).
                  iSplitR "Hclose_inv".
                  { iLeft. iFrame "∗ #". iExists s1.
                    repeat (iSplit; eauto). 
                    unfold filled_string in *. 
                    unfold simple_string in *. 
                    simplify_eq. by rewrite H8. }
                  iFrame. }

                  (* iSplit. { iPureIntro. admit. }
                  admit. } *)

                iRight. iApply (big_sepM_mono with "Hvisinv").
                iIntros (k x' Hkx) "Hvis".
                iIntros (id_inner Heq').
                assert (id_inner ≠ pid).
                { intros ->. specialize (Hidunused k). simplify_eq. }
                rewrite (lookup_delete_ne); last first.
                { intros ?. simplify_eq. }
                by iApply "Hvis".

              + iDestruct "Hinv_2" as "(%&%&%&%&%&%&%& Hxcap & Hxunfill & Hxmfrag & %Hxmsub & Hxsusp & Hxproph)".

                iPoseProof (mapg_auth_alive with "Hmauth Hxmfrag") as (yx) "%Hxin".
                destruct Hxin as [(?&Hxin&?)%Some_equiv_eq ?].
                edestruct (mapg_alive_lookup_Cinl _ _ _ yx Hxin) as (yx' & Halive & Hyyx'); first done.
                clear Hxin. rename Halive into Hxin.

                iDestruct (big_sepM_lookup_acc _ (mapg_alive (<[pid:=csum.Cinr (to_agree ())]> m')) pid0 _ Hxin with "Hbigsep") as "[Hms Hbigsep]".
                iDestruct "Hms" as (ctr ????????[Hxcgt [Hxin' ?]]) 
                    "(Hlc & Hxxser & Hxxserspec & Hxxauth & Hxxc & Hxxfin)".
                
                simplify_eq.
                iMod (visit_update_finished with "Hvmauth Hxvisdone Hintr Hxlbfrag
                  Hxsusp Hxxc") as "(#Hxvisfin & Hintr & Hvmauth & Hxxc & Hxsusp)".
                { assert (x2 = pv0) as ->.
                  { rewrite Hyyx' in H11. rewrite H11 in H10. simpl in H10.
                    fold_leibniz. by apply (inj to_agree) in H10. }
                  exact Hxmsub. }

                iEval (rewrite visited_map_update_finished_rewrite) in "Hvmauth".
                iPoseProof ("Hgetidtok" with "Hxvisfin") as "Hidtok".
                iPoseProof (id_token_unused with "Hvmauth Hidtok")
                  as "(%Hidunused & Hvmauth & Hidtok)".
                iAssert (visit_finished _ -∗ id_token pid)%I with "[Hidtok]"
                  as "Hgetidtok".
                { iIntros "_". iExact "Hidtok". }

                iFrame "Hmauth".
                iPoseProof ("Hbigsep" with 
                    "[$Hlc $Hxxser $Hxxserspec $Hxxauth $Hxxc $Hxxfin]") as "$".
                { eauto. }

                iExists _. iSplitR; eauto.
                iSplitR.
                { do 2 iModIntro. iIntros (gpid gsusp gγ Hgpid_lt) "H1 H2 H3".
                  iDestruct ("Hnmspc" with "[] H1 H2 H3") as "%Hsubset".
                  { iPureIntro. lia. }
                  iPoseProof (pval_snapshot_neq with "Hpvuneq H1") as "%Hneq";
                    try lia.
                  iPureIntro.
                  assert ((↑ver_susp_n gsusp : coPset) ## ↑ver_susp_n susp) as Hdisj.
                  { apply ndot_ne_disjoint. by intros ->. }
                  set_solver. }
                iSplitR "Hvisinv Hvmauth".
                { iRight. iFrame "∗ #".
                  iModIntro. repeat (iSplit; eauto).
                  iRight. iFrame "∗ #". eauto. }
                { iModIntro. iLeft. iExists _, _.
                  iSplit; first done.
                  iFrame "Hvmauth".
                  rewrite -insert_delete_insert.
                  iApply big_sepM_insert_2.
                  - iIntros (id_x [=]).
                  - iPoseProof (big_sepM_subseteq with "Hvisinv") as "Hvisinv";
                      first apply delete_subseteq.
                    iApply (big_sepM_mono with "Hvisinv").
                    iIntros (k vk Hkv) "Hv".
                    iIntros (id_x ->).
                    apply lookup_delete_Some in Hkv as [Hkne Hkv].
                    iSpecialize ("Hv" $! id_x eq_refl).
                    iDestruct "Hv" as (v') "%Hmlookup".
                    iExists v'. iPureIntro.
                    rewrite lookup_delete_ne; first done.
                    intros Hpideq. assert (id_x = pid) by (by simplify_eq).
                    subst id_x.
                    specialize (Hidunused k).
                    rewrite lookup_insert_ne in Hidunused; last done.
                    by apply Hidunused. } }

          iPoseProof (big_sepM_mono 
              (v_susp_big_sep_lam m)
              (v_susp_big_sep_lam (delete #pid m)) 
            with "Hbigsep") as "Hbigsep".
          { iIntros (?? Hlook) "Hbigsep".
            rewrite /v_susp_big_sep_lam.
            iDestruct "Hbigsep" as (?????????[?[??]]) "($ & $ & $ & $)".
            iPureIntro. exists q0. 
            split; eauto. split; last eauto.
            rewrite mapg_alive_remove in Hlook.
            rewrite lookup_delete_Some in Hlook.
            destruct! Hlook; simplify_eq.
            rewrite lookup_delete_ne; try done.
            intros ?. by simplify_eq. }

            
          (* iPoseProof (stok_combine with "Hstok Hstok'") as "[_ Hstok_comp]".
          iMod (stok_update _ (Some pid) with "Hstok_comp") as "Hstok_comp".
          iPoseProof (stok_split with "Hstok_comp") as "[Hstok Hstok']". *)

          iMod ("Hclose_tab" with "[$Htabtok Hl Hmauth Hbigsep Hvisvm Hst']") as "Htabtok".
          { iNext. iLeft. iFrame "% ∗".
            iDestruct "Hvisvm" as "[(%&%&-> & $ & $)|[$ $]]";

            iSplit.
            1,3: iPureIntro; rewrite mapg_alive_remove;
              do 2 rewrite (map_size_delete);
              rewrite Hin Hin'; by rewrite H.
            1,2: iPureIntro; intros ??;
              rewrite lookup_delete_None;
              right; by apply Hidinv. }


              (* + iSplit; iDestruct "Hkeys" as "[Hkeysmap Hmapkeys]".
                * iPoseProof (big_sepM_lookup _ _ #pid with "Hmapkeys") as "%Hlook"; try done.
                  iPoseProof (big_sepS_delete _ _ pid with "Hkeysmap") as "[_ Hkeysmap]".
                  { destruct! Hlook. by simplify_eq. }

                  iApply (big_sepS_mono with "Hkeysmap").
                  iIntros (id_iter Hid_iter).
                  iIntros "[%v_id %Hv_id]".
                  iExists v_id. iPureIntro.
                  rewrite lookup_delete_ne; first done.
                  intros Heq'. simplify_eq.
                  apply elem_of_difference in Hid_iter as [_ Hnotin].
                  apply Hnotin. by apply elem_of_singleton.
                * iPoseProof (big_sepM_delete _ _ #pid with "Hmapkeys") as "[_ Hmapkeys]"; try done.
                  iApply (big_sepM_mono with "Hmapkeys").
                  iIntros (k v_k Hkv) "[%id_k [%Heq' %Hin_k]]".
                  iExists id_k. iPureIntro. split; first done.
                  apply elem_of_difference. split; first done.
                  intros Hsing%elem_of_singleton. subst id_k k.
                  rewrite lookup_delete in Hkv. discriminate. } *)

          iMod ("Hxfin" with "Hnmspc' Htabtok Hlc Hxser Hxserspec Hxc Hxauth Hst Hv") as "($&$&Htok&$)".

          iMod ("Hclose_inv" with "[$Htok Hsusp Hfill]") as "Htok".
          { iNext. iLeft. iFrame "∗ #". eauto. }

          by iFrame.
          
        * v_load. v_bind (map_remove _ _).
          iMod (gwp_map_remove () ⊤ #pid d m _
            (λ d', ⌜is_map d' (delete #pid m)⌝)%I
            with "[//] [] [$Hv //]") as (?) "[Hv %Hmdel] /="; 
            try by iIntros "!#" (?).
          Unshelve. 2: done.

          iPoseProof (big_sepM_mono
              (v_susp_big_sep_lam m)
              (v_susp_big_sep_lam (delete #pid m))
            with "Hbigsep") as "Hbigsep".
          { iIntros (?? Hlook) "Hbigsep".
            rewrite /v_susp_big_sep_lam.
            iDestruct "Hbigsep" as (?????????[?[??]]) "($ & $ & $ & $)".
            iPureIntro. exists q0.
            split; eauto. split; last eauto.
            rewrite lookup_delete_Some in Hlook.
            destruct! Hlook; simplify_eq.
            rewrite lookup_delete_ne; try done.
            intros ?. by simplify_eq. }

          v_store. v_pures. v_load. v_pures. v_bind (map.map_insert _ _ _).
          iMod (gwp_map_insert #pid _ v _ () ⊤ _
            (λ d', ⌜is_map d' (<[ #pid := _ ]> (delete #pid m))⌝)%I
            with "[//] [] [$Hv //]") as (?) "[Hv %Hmins] /=".
          { by iIntros "!#" (? Hins). }
          Unshelve. 2: done.
          rewrite insert_delete_insert in Hmins.

          iPoseProof (big_sepM_mono 
              (v_susp_big_sep_lam (delete #pid m)) 
              (v_susp_big_sep_lam (<[#pid:=(#(ctr - 1), finish)%V]> m))
            with "Hbigsep") as "Hbigsep".
          { iIntros (?? Hlook) "Hbigsep".
            rewrite /v_susp_big_sep_lam.
            iDestruct "Hbigsep" as (?????????[?[Hreflook ?]]) "($ & $ & $ & $)".
            iExists q0. iPureIntro. 
            split; eauto. split; last eauto.
            destruct (decide (k = pid)); simplify_eq.
            rewrite lookup_delete_Some in Hlook.
            destruct! Hlook. simplify_eq.
            rewrite lookup_delete_Some in Hreflook.
            destruct! Hreflook. 
            rewrite lookup_insert_ne; eauto. }

          iPoseProof (big_sepM_insert _ _ pid _ 
            with "[$Hbigsep $Hxfin $Hxser $Hxserspec $Hxc $Hlc $Hxauth]") as "Hbigsep".
          { by rewrite lookup_delete. }
          { iExists q. iFrame "#". iPureIntro. split. 
            { inversion Hcgt; simplify_eq; try lia. }
            split; last eauto.
            rewrite lookup_insert.
            repeat f_equal. lia. }

          rewrite (insert_delete _ _ _ Hin). v_store. v_pures.
          iMod ("Hclose_tab" with "[$Htabtok Hl Hmauth Hbigsep Hvmauth Hvisinv Hst']") as "Htabtok".
          { iNext. iLeft. iFrame "% ∗".
            iSplit; [|iSplit].
            - iPureIntro.
              rewrite map_size_insert_Some; last by exists (#ctr, finish)%V.
              done.
            - iPureIntro. intros ??.
              destruct (decide (pid = ctr')); simplify_eq.
              + specialize (Hidinv ctr' H5).
                simplify_eq.
              + rewrite lookup_insert_ne; eauto.
                intros ?. simplify_eq.
            - iApply (big_sepM_mono with "Hvisinv").
              iIntros (???) "Hvis".
              iIntros (??).

              destruct (decide (pid = id0)); simplify_eq.
              * rewrite lookup_insert. eauto.
              * rewrite lookup_insert_ne; try by (intros ?; simplify_eq).
                by iApply "Hvis". }
              
              (* + admit. } *)
          iFrame.
          iMod ("Hclose_inv" with "[$Htok Hsusp Hfill]") as "Htok".
          { iNext. iLeft. iFrame "∗ #". eauto. }

          iFrame.
          by iCombine "Hintr Hintr'" as "$".
  Qed.

	Lemma p_finish_spec' :
    ∀ ser a sprf pn,
      {{{ True }}}
          p_finish ser a
      {{{ (finish : val), RET finish; 
          p_finish_spec finish ser a sprf pn }}}.
  Proof.
    iIntros (?????) "_ HΦ".
    wp_rec. wp_pures. iApply "HΦ".
    iModIntro.
    iIntros (????? ? ?) "!# (Htok & Hintr & Hprf & #Hserspec) HΦ".
    wp_pures.
    wp_apply ("Hserspec" with "[//] [$Htok $Hintr]"); eauto.
    iIntros "(Htok & Hintr & Hgood)". wp_pures.

    destruct ls; simplify_eq.
    { wp_apply (wp_resolve_proph_string with "Hprf").
      iIntros (?) "[% Hprf]". simplify_eq. }

    wp_apply (wp_resolve_proph_string with "Hprf").
    iIntros (?) "[% Hprf]". wp_pures.
    simplify_eq.

    iApply "HΦ". iFrame.
    iModIntro. repeat (iSplit; eauto).
    iIntros (????) "Hst Hpset Hpc Hvm % #HbigL".
    
    iPoseProof ("Hgood" with "Hst Hpset [//] HbigL") as "($ & Hpset & #HbigL')".
    iPoseProof (big_sepS_sep
          (λ γ, visit_reached_done γ)%I
          (λ γ, ∃ (lb : loc), lg_mapg_p_frag lb γ ∗ ⌜p_sub_obj t a #lb⌝)%I
        with "HbigL'") as "[HbigLreached HbigL'']".

    iMod (pending_set_remove with "Hvm Hpc Hpset HbigLreached") as "[$ $]".
    done.
  Qed.

  Lemma flush_buf_stream_spec :
    ∀ (p : proph_id) (prf buf : val) (lpn : list nat) (pn : nat)
        (ps ps_real ps_proph : list string) (bufl : list val) q,
      {{{ ⌜is_list bufl buf⌝ ∗ ⌜is_proof prf ps⌝ ∗
          ⌜List.length bufl = List.length ps_real⌝ ∗
          ⌜List.length bufl = List.length lpn⌝ ∗ 
          ⌜pn = sum_list lpn⌝ ∗
          proph_proof p ps_proph ∗ 
          p_buffer (combine (combine bufl ps_real) lpn) ∗
          seq_tok ⊤ ∗ intransit q }}}
        flush_buf_stream buf prf #p
      {{{ prf' (ps' ps_proph' x : list string), RET prf';
          ⌜ps_proph = ps_proph' ++ x⌝ ∗ ⌜ps_proph' = ps_real⌝ ∗
          ⌜is_proof prf' ps'⌝ ∗ ⌜ps' = reverse ps_proph' ++ ps⌝ ∗
          proph_proof p x ∗ seq_tok ⊤ ∗
          (∀ vm ctr,
            tern_state -∗ visited_mapg_auth vm pn ctr -∗
            pencount_frag pn ==∗
            tern_state ∗ visited_mapg_auth vm 0 ctr ∗
            pencount_frag 0) }}}.
  Proof.
    iIntros (?????????? ?) 
      "(%Hbuf & %Hprf & %Hlen1 & %Hlen2 & %Hsumpn & Hproph & Hpbuffer & Htok & Hintr) HΦ".
    iInduction (bufl) as [|h_buf t_buf] "IH"
        forall (buf Hbuf ps_real Hlen1 pn lpn Hlen2 Hsumpn prf ps Hprf ps_proph q Φ) "Hpbuffer Hproph Hintr HΦ"; 
      rewrite /flush_buf_stream; wp_pures; fold flush_buf_stream.
    - wp_apply gwp_list_head; try done.
      iIntros (? H). destruct! H; simplify_eq.
      destruct ps_real; simplify_eq.
      destruct lpn; simplify_eq. simpl.
      wp_pures. iApply "HΦ".

      iFrame "∗ %". instantiate (1 := []).
      
      iModIntro. iFrame. repeat (iSplit; eauto).
      by iIntros (??) "$ $ $".
      (* iDestruct "Hvm" as "(Hms & Hd & Hps & Hpn & Hgm & Hctr & Hpvm & %Hdom & %Hdompvm & %Hgmm & %Hdid & %Hpcoh)".
      destruct Hpcoh as [Hsize Hpend].
      symmetry in Hsize. apply size_empty_inv, leibniz_equiv in Hsize as ->.
      iModIntro. iFrame.
      iPureIntro. repeat (split; eauto). *)

    - wp_apply gwp_list_head; try done.
      iIntros (? H). destruct! H; simplify_eq.
      destruct ps_real; simplify_eq.
      destruct lpn; simplify_eq.
      wp_pures. simpl.

      iPoseProof (big_sepL_cons _ (H0, s, n) (combine (combine H ps_real) lpn) with "Hpbuffer") as "[Hbuf Hpbuffer]".
      iDestruct "Hbuf" as (???????) "(Hserspec & Hpfinish & Hgoodtr1)". (* Hpset & %& HbigS & *)
      simplify_eq. iDestruct "Hintr" as "[Hintr Hintr']".

      wp_apply ("Hpfinish" $! ⊤ with "[//] [$Htok $Hproph $Hserspec $Hintr]").
      iIntros (?) "(Htok & Hproph & % & Hgoodtr2)".
      destruct ps_proph; simplify_eq.

      wp_pures. wp_bind (_ :: _)%E.
      
      wp_apply (gwp_list_cons s0 ps prf with "[//]").
      iIntros (??).

      wp_apply (gwp_list_tail ⊤ with "[//]").
      iIntros (??). simpl in H1.

      wp_apply ("IH" with "[//] [//] [//] [//] [//] Htok Hpbuffer Hproph Hintr'"); try done.
      iIntros (????) "(%&%&%&%& Hproph & Htok & Hgoodtr3)".

      iApply "HΦ". iFrame "∗ %".
      instantiate (1 := s0::ps_proph').
      rewrite reverse_cons.
      simplify_list_eq.
      repeat (iSplit; eauto).

      iIntros (??) "Hgood Hvm Hpc".

      iPoseProof ("Hgoodtr1" with "Hgood") as (?) "(Hgood & Hpset & % & HbigS)".

      assert (sum_list lpn + pn = pn + sum_list lpn) as <- by lia.
      iMod ("Hgoodtr2" $! vm (sum_list lpn + size γl) ctr with "Hgood Hpset Hpc Hvm [//] HbigS")
        as "(Hgood & Hpc & Hvm_rem)".
      
      iEval (rewrite visited_mapg_pending_remove_rewrite) in "Hvm_rem".
      assert (sum_list lpn + size γl - size γl = sum_list lpn) as Hsumeq by lia.
      iPoseProof (pencount_pn_eq _ _ Hsumeq with "Hpc") as "Hpc".
      iPoseProof (vmauth_pn_eq vm _ _ ctr Hsumeq with "Hvm_rem") as "Hvm_rem".
      iMod ("Hgoodtr3" $! vm with "Hgood Hvm_rem Hpc") as "($ & $ & $)".
  Qed.

End finish_specs.