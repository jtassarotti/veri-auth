From auth.prelude Require Import stdpp.
From auth.rel_logic_tern_susp Require Export model spec_rules spec_tactics.
From auth.heap_lang Require Import primitive_laws derived_laws.
From auth.heap_lang.lib Require Import list map.
From auth.examples Require Export authentikit_susp.
From auth.examples.susp_correctness Require Import definitions helpers.
From iris.base_logic.lib Require Export na_invariants fancy_updates.

Section finish_specs.
  Context `{!authG Σ, !seqG Σ, !visited_mapG Σ, !lg_mapG Σ,
      !mapG Σ, !capG Σ, !intransitG Σ, !stateG Σ, !stateTokG Σ}.

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
    iIntros "!#" (????? id ?[??]) "Hlc Htok Hser Hserspec Hc Hvauth Hstok Hrem Hst Hv".
    iDestruct "Hvauth" as "[(-> & Hidtok)|(%&%&%&%& -> & #Hlbfrag & #Hvisdone &% & -> & #Hinv)]".
    - v_pures. v_bind (ser _).
      iMod ("Hserspec" with "Hc Hser Hv") as "(Hc & Hser & Hv) /=".
      v_pures. v_bind (Hash _).
      iMod (step_verifier_hash with "Hv") as "Hv /="; try done.
      v_pures; try solve_vals_compare_safe.
      case_bool_decide; simplify_eq; v_pures.

      iMod (na_inv_acc with "Htab Htok") as "(Htabo & Htok & Hclose_tab)"; try solve_ndisj.
      iMod (lc_fupd_elim_later with "Hlc Htabo") as "Htabo".
      iDestruct "Htabo" as "[(%&%&%&%&%&%& %idctr &% &% & Hl & %Hm & 
          Hbigsep & Hmauth &% & Hvmauth & %Hidinv & Hvisinv & Hst')|Hst']";
        last first.
      { admit. }
        (* iPoseProof (state_agree with "Hst Hst'") as "(% & Hst & Hst')"; simplify_eq. *)

      iPoseProof (id_token_unused with "Hvmauth Hidtok") as "(%Hidunused & Hvmauth & Hidtok)".
      
      iDestruct "Hvisinv" as "[[Hstok' Hvisinv]|(% & Hstok' & Hvisinv)]";
        iDestruct (stok_agree with "Hstok Hstok'") as "%";
        simplify_eq.

      iPoseProof (stok_combine with "Hstok Hstok'") as "[_ Hstok_comp]".
      iMod (stok_update _ None with "Hstok_comp") as "Hstok_comp".
      iPoseProof (stok_split with "Hstok_comp") as "[Hstok Hstok']".

      iMod ("Hclose_tab" with "[$Htok Hbigsep Hmauth Hl Hvmauth Hvisinv Hstok Hst']") as "Htok".
      { iNext. iLeft.
        iFrame "% ∗". iLeft. iFrame.
        iApply (big_sepM_mono with "Hvisinv").
        iIntros (k x0 Hkx) "Hvis".
        iIntros (id_inner Heq).
        assert (id_inner ≠ id0) by
          (intros ->; destruct (Hidunused k) as [Hu _]; apply Hu; rewrite Hkx Heq; reflexivity).
        iApply "Hvis"; try done. }
      
      iFrame. iModIntro.
      iIntros (?) "Hvisit".
      by iPoseProof (id_token_visit_reached_done_invalid with "Hidtok Hvisit") as "Hfalse".

    - v_pures. v_bind (ser _).
      iMod ("Hserspec" with "Hc Hser Hv") as "(Hc & Hser & Hv) /=".
      v_pures.

      iMod (na_inv_acc with "Htab Htok") as "(Htabo & Htok & Hclose_tab)"; try solve_ndisj.
      iMod (na_inv_acc with "Hinv Htok") as "(Hinvo & Htok & Hclose_inv)"; try solve_ndisj.

      iDestruct "Hinvo" as ">[Hinv_1|Hinv_2]".
      + iDestruct "Hinv_1" as "(%s1&%& (%&%&%&%&%& Hsusp & #Hlbfrag' & #Hvisfin))".
        rewrite /filled_string /simple_string in H2 H3. destruct! H3; simplify_eq.
        iPoseProof (lg_mapg_agree with "Hlbfrag' Hlbfrag") as "(-> & _ & _)".
        iDestruct (visit_finished_keep with "Hvisfin") as "[_ #Hvisreach2]".
        iDestruct (visited_reached_done_agree with "Hvisreach2 Hvisdone") as %->.

        simplify_eq. v_load. v_pures. v_bind (Hash _).
        iMod (step_verifier_hash with "Hv") as "Hv /="; try done.
        v_pures; try solve_vals_compare_safe.
        case_bool_decide; simplify_eq.

        iMod (lc_fupd_elim_later with "Hlc Htabo") as "Htabo".
        iDestruct "Htabo" as "[(%&%&%&%&%&%& %idctr &% &% & Hl & %Hm & 
            Hbigsep & Hmauth &% & Hvmauth & %Hidinv & Hvisinv & Hst')|Hst']";
          last first.
        { admit. }
          (* iPoseProof (state_agree with "Hst Hst'") as "(% & Hst & Hst')"; simplify_eq. *)

        iDestruct (vm_finished_no_done with "Hvmauth Hvisfin") as "(%Hno_done & Hvmauth)".

        iDestruct "Hvisinv" as "[[Hstok' Hvisinv]|(% & Hstok' & Hvisinv)]";
          iDestruct (stok_agree with "Hstok Hstok'") as "%";
          simplify_eq.

        iPoseProof (stok_combine with "Hstok Hstok'") as "[_ Hstok_comp]".
        iMod (stok_update _ None with "Hstok_comp") as "Hstok_comp".
        iPoseProof (stok_split with "Hstok_comp") as "[Hstok Hstok']".

        iMod ("Hclose_inv" with "[$Htok Hsusp]") as "Htok".
        { iNext. iLeft. iFrame "Hvisfin". iFrame "∗ #". eauto. }

        iMod ("Hclose_tab" with "[$Htok Hbigsep Hmauth Hl Hvmauth Hvisinv Hstok Hst']") as "Htok".
        { iFrame "%". iNext. iLeft. iFrame. iLeft. iFrame.
          iApply (big_sepM_mono with "Hvisinv").
          iIntros (k x0 Hkx) "Hvis".
          iIntros (id_inner Heq).
          assert (id_inner ≠ id0) by
            (intros ->; apply (Hno_done k); rewrite Hkx Heq; reflexivity).
          iApply "Hvis"; try done. }

        v_pures. iFrame. iModIntro.
        iIntros (?) "Hvisit".
        iDestruct (visit_reached_done_inj with "Hvisdone Hvisit") as %->.
        iFrame "Hvisfin".
        
      + iDestruct "Hinv_2" as "(%&%&%&%&%&%&%&%&%& Hcap & Hlbfrag' & Hmfrag & %Hmsub & Hsusp & Hproph)".

        simplify_eq H2. intros <-.
        iPoseProof (lg_mapg_agree with "Hlbfrag' Hlbfrag") as "(-> & _ & _)".

        iMod (lc_fupd_elim_later with "Hlc Htabo") as "Htabo".
        iDestruct "Htabo" as "[(%&%&%&%&%&%& %idctr &% &% & Hl & %Hm & 
            Hbigsep & Hmauth &% & Hvmauth & %Hidinv & Hvisinv & Hst')|Hst']";
          last first.
        { admit. }
          (* iPoseProof (state_agree with "Hst Hst'") as "(% & Hst & Hst')"; simplify_eq. *)

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

        iDestruct "Hxc" as "(Hcap' & % & Hxc & Hxagg)".
        iDestruct (cap_frag_agree with "Hcap Hcap'") as "->".
        iAssert (sub_susp_count_frags t0 x1 ctr pid Nc0) with "[$Hcap $Hxc $Hxagg //]" as "Hxc".

        iDestruct (visit_reached_done_lookup with "Hvmauth Hvisdone") as "(%Hvmγ_old & Hvmauth)".

        iDestruct "Hvisinv" as "[[Hstok' Hvisinv]|(% & Hstok' & Hvisinv)]";
          iDestruct (stok_agree with "Hstok Hstok'") as "%";
          simplify_eq.

        assert (x1 = pv) as ->.
        { rewrite Hyy' in H5. rewrite H5 in H4. simpl in H4.
          fold_leibniz. by apply (inj to_agree) in H4. }

        iMod (count_update with "[//] Hvmauth Hlbfrag Hmfrag Hvisdone Hxc Hsusp Hv") as "(Hvmauth & #Hvisfin & Hxc & Hsusp & Hv) /=".
        iEval (rewrite visited_map_update_finished_rewrite) in "Hvmauth".

        iPoseProof (stok_combine with "Hstok Hstok'") as "[_ Hstok_comp]".
        iMod (stok_update _ None with "Hstok_comp") as "Hstok_comp".
        iPoseProof (stok_split with "Hstok_comp") as "[Hstok Hstok']".

        iDestruct (vm_finished_no_done with "Hvmauth Hvisfin") as "(%Hno_done & Hvmauth)".

        assert (∃ v_γ, vm !! γ = Some v_γ) as [v_γ Hvγ]
          by (destruct Hvmγ_old as [H' | H']; eauto).
        iPoseProof (big_sepM_insert_override_2 _ _ γ v_γ 
              (finished_val id0) with "Hvisinv []") as "Hvisinv"; try done.
        

        iPoseProof (big_sepM_mono
            (vm_big_sep_lam_set m id0)
            (vm_big_sep_lam_unset m)
          with "Hvisinv") as "Hvisinv".
        { iIntros (k x0' Hkx0) "Hvis".
          iIntros (id_inner Heq).
          iApply "Hvis"; try done.
          destruct (decide (γ = k)); simplify_eq.
          { rewrite lookup_insert in Hkx0. eauto. }
          rewrite lookup_insert_ne in Hkx0; try done.
          admit. }

        v_pures. v_load. v_bind (map_lookup _ _).
        iMod (gwp_map_lookup #pid d m () ⊤ _
          (λ v, ⌜from_option (λ p, v = SOMEV $p) (v = NONEV) (m !! #pid)⌝)%I
          with "[//] [] [$Hv //]") as (?) "[Hv %Hlook'] /="; try by iIntros "!>" (?).
        rewrite Hin' in Hlook'. simpl in Hlook'. simplify_eq.
        v_pures; try solve_vals_compare_safe.
        Unshelve. 2: done.

        iMod ("Hclose_inv" with "[$Htok Hsusp]") as "Htok".
        { iNext. iLeft. iFrame "∗ #". eauto. }
          
        case_decide as Heq; simplify_eq; v_pures.
        * v_load. v_bind (map_remove _ _).
          iMod (gwp_map_remove () ⊤ #pid d m _
            (λ d', ⌜is_map d' (delete #pid m)⌝)%I
            with "[//] [] [$Hv //]") as (?) "[Hv %Hm'] /="; 
            try by iIntros "!#" (?).
          Unshelve. 2: done.

          assert (ctr = 1) as ->.
          { inversion Heq. lia. }
          simpl.

          iMod (mapg_remove_count_0 with "Hxc Hmauth") as "(Hxc & Hmauth & Hxrem)".
          { lia. }

          rewrite -mapg_alive_remove.

          iPoseProof (big_sepM_mono 
              (v_susp_big_sep_lam m)
              (v_susp_big_sep_lam (delete #pid m)) 
            with "Hbigsep") as "Hbigsep".
          { iIntros (?? Hlook) "Hbigsep".
            rewrite /v_susp_big_sep_lam.
            iDestruct "Hbigsep" as (?????????[?[??]]) "($ & $ & $ & $)".
            iPureIntro. exists q1. 
            split; eauto. split; last eauto.
            rewrite mapg_alive_remove in Hlook.
            rewrite lookup_delete_Some in Hlook.
            destruct! Hlook; simplify_eq.
            rewrite lookup_delete_ne; try done.
            intros ?. by simplify_eq. }
            
          v_store. v_pures. 
          
          iPoseProof (stok_combine with "Hstok Hstok'") as "[_ Hstok_comp]".
          iMod (stok_update _ (Some pid) with "Hstok_comp") as "Hstok_comp".
          iPoseProof (stok_split with "Hstok_comp") as "[Hstok Hstok']".

          iMod ("Hclose_tab" with "[$Htok Hl Hmauth Hbigsep Hvmauth Hvisinv Hstok Hst']") as "Htok".
          { iNext. iLeft. iFrame "% ∗".
            iSplit; [|iSplit].
            - iPureIntro. rewrite mapg_alive_remove.
              do 2 rewrite (map_size_delete).
              rewrite Hin Hin'. by rewrite H3.
            - iPureIntro. intros ??.
              rewrite lookup_delete_None.
              right. by apply Hidinv.
            - iRight. iFrame.

              iApply (big_sepM_mono with "Hvisinv").
              iIntros (???) "Hvis".
              iIntros (???).

              rewrite lookup_delete_ne; last first.
              { intros ?. simplify_eq. }

              by iApply "Hvis". }

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

            iMod ("Hxfin" $! E with "[//] Hlc Htok Hxser Hxserspec Hxc Hxauth Hstok' Hxrem Hst Hv") as "($&$&$&$&Hfin)".
            iModIntro. iIntros (?) "Hvisdone'".
            iDestruct (visit_reached_done_inj with "Hvisdone Hvisdone'") as %->.
            iFrame "Hvisfin".
          
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
            iPureIntro. exists q1. 
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
            iExists q1. iPureIntro. 
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
          { iExists q0. iPureIntro. split. 
            { inversion Hcgt; simplify_eq; try lia. }
            split; last eauto.
            rewrite lookup_insert.
            repeat f_equal. lia. }

          rewrite (insert_delete _ _ _ Hin). v_store. v_pures.
          iMod ("Hclose_tab" with "[$Htok Hl Hmauth Hbigsep Hvmauth Hstok Hvisinv Hst']") as "Htok".
          { iNext. iLeft. iFrame "% ∗".
            iSplit; [|iSplit].
            - iPureIntro. admit.
            - iPureIntro. intros ??.
              destruct (decide (pid = ctr')); simplify_eq.
              + specialize (Hidinv ctr' H7).
                simplify_eq.
              + rewrite lookup_insert_ne; eauto.
                intros ?. simplify_eq.
            - iLeft. iFrame.
                
              iApply (big_sepM_mono with "Hvisinv").
              iIntros (???) "Hvis".
              iIntros (??).

              destruct (decide (pid = id)); simplify_eq.
              * rewrite lookup_insert. eauto.
              * rewrite lookup_insert_ne; try by (intros ?; simplify_eq).
                by iApply "Hvis". }
              
              (* + admit. } *)
          iFrame.

          iModIntro. iIntros (?) "_".
          by assert (γ = γ0) as -> by admit.
  Admitted.

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
    iIntros (???????) "Hst Hpset Hpc Hvm % #HbigL".
    
    iPoseProof ("Hgood" with "Hst Hpset [//] HbigL") as "($ & Hpset & #HbigL')".
    iPoseProof (big_sepS_sep
          (λ γ, ∃ n : natO, visit_reached_done γ n)%I
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
          (∀ vm d pset ctr gm,
            tern_state -∗ visited_mapg_auth vm d pset pn ctr gm -∗
            pencount_frag pn ==∗
            tern_state ∗ visited_mapg_auth vm d ∅ 0 ctr gm ∗
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
      iIntros (?????) "$ Hvm Hpenc".
      iDestruct "Hvm" as "(Hms & Hd & Hps & Hpn & Hgm & Hctr & %Hdom & %Hgmm & %Hdid & %Hpcoh)".
      destruct Hpcoh as [Hsize Hpend].
      symmetry in Hsize. apply size_empty_inv, leibniz_equiv in Hsize as ->.
      iModIntro. iFrame.
      iPureIntro. repeat (split; eauto).

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

      iIntros (?????) "Hgood Hvm Hpc".

      iPoseProof ("Hgoodtr1" with "Hgood") as (?) "(Hgood & Hpset & % & HbigS)".

      assert (sum_list lpn + pn = pn + sum_list lpn) as <- by lia.
      iMod ("Hgoodtr2" $! vm d pset (sum_list lpn + size γl) ctr gm with "Hgood Hpset Hpc Hvm [//] HbigS")
        as "(Hgood & Hpc & Hvm_rem)".
      
      iEval (rewrite visited_mapg_pending_remove_rewrite) in "Hvm_rem".
      assert (sum_list lpn + size γl - size γl = sum_list lpn) as Hsumeq by lia.

      iMod ("Hgoodtr3" $! vm d (pset ∖ γl) with "Hgood [Hvm_rem] [Hpc]") as "($ & $ & $)".
      admit.
  Admitted.

End finish_specs.