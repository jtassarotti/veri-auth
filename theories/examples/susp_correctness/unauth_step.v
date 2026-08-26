From auth.prelude Require Import stdpp.
From auth.rel_logic_tern_susp Require Export model spec_rules spec_tactics interp.
From auth.heap_lang Require Import primitive_laws derived_laws.
From auth.heap_lang.lib Require Import list map.
From auth.examples Require Export authentikit_susp.
From auth.examples.susp_correctness Require Import definitions helpers finish_specs.
From iris.base_logic.lib Require Export na_invariants fancy_updates.

(** * The shared "consume one proof-stream element" step of [refines_auth_unauth].

    This is the common tail of the suspended-auth cases: the verifier pops the
    head of its proof stream, opens the table invariant, deserializes, and both
    sides finish.  It factors out the two script-identical ~400-line blocks of
    the monolithic proof (the two [destruct r] bullets of the visited/unfilled
    branch). *)
Section unauth_step.
  Context `{!authG Σ, !seqG Σ, !tabseqG Σ, !correctnessG Σ}.

  Lemma refines_unauth_susp_consume (c : loc) (A : kindO Σ ⋆) (tA tA' : evi_type)
      (p_ser_susp p_ser_unsusp p_susp p_unsusp v_ser v_deser v_count v3 : val)
      (t2 : nat) (K2 : list (ectxi_language.ectx_item heap_ectxi_lang))
      (t3 : nat) (K3 : list (ectxi_language.ectx_item heap_ectxi_lang))
      (p : proph_id) (s0 : string) (ps1 ps2 ps_fix : list string) (lpn : list nat)
      (Ψ : val → iPropI Σ)
      (a1 a2 un_a1 : val) (s : string)
      (prf1 buf1 : val) (bufl : list val)
      (prf : val) (cntr : nat) (γ0 : gname) (susp : loc) (pid : nat)
      (H0 : unsusp tA' a1 un_a1)
      (H1 : length ps1 = length bufl)
      (H2 : length ps1 = length lpn)
      (H3 : is_proof prf1 ps_fix)
      (H4 : is_list bufl buf1)
      (Hvprf : is_proof prf (s0 :: ps2)) :
    inv_v_susp_table c -∗
    suspend_v_deser_spec p_ser_susp p_susp v_deser A tA -∗
    v_ser_spec v_ser tA -∗
    v_count_spec v_count tA -∗
    susp_ser_p tA' a1 s -∗
    A a1 a2 v3 -∗
    pval_snapshot susp pid -∗
    lg_mapg_frag susp γ0 -∗
    seq_inv (ver_susp_n susp)
      (auth_susp_v_inv pid (InjRV #susp)
         (some_ser_str (string_ser_str (hash s)))) -∗
    visit_reached_done γ0 -∗
    ( tabseq_tok ⊤ ∗
      spec_verifier t2
        (fill K2
           (match: list_head prf with
              InjL <> => InjL #()
            | InjR "p" =>
              let: "id" := #cntr in
              let: "serialize" := (v_ser, v_deser, v_count)%V in
              let: "deserialize" := Snd (Fst "serialize") in
              let: "count" := Snd "serialize" in
              let: "serialize" := Fst (Fst "serialize") in
              match: "deserialize" "id" "p" with
                InjL <> => InjL #()
              | InjR "x" =>
                let: "nchild" := "count" "x" in
                let: "finish" := v_finish #c (InjRV #susp) "x" "serialize" in
                match: if: "nchild" = #0 then "finish" #()
                       else #c <-
                            map.map_insert "id" ("nchild", "finish") ! #c;;
                            InjRV #() with
                  InjL <> => InjL #()
                | InjR <> => InjR (list_tail prf, "id" + #1, "x")
                end
              end
            end)%E) ∗
      spec_ideal t3 (fill K3 v3) ∗
      pencount_frag (definitions.sum_list lpn) ∗
      p_buffer (combine (combine bufl ps1) lpn) ∗
      id_ctr_frag cntr ∗
      proph_proof p (reverse (s0 :: ps2) ++ ps1) ∗
      intransit 1 ∗
      tern_state ∗
      seq_tok ⊤ ) -∗
    (∀ (ps1' : list string) (lpn' : list nat) (w1' a0 a3 : val),
       tabseq_tok ⊤ ∗ seq_tok ⊤ ∗ spec_ideal t3 (fill K3 a3) ∗
       intransit 1 ∗ proph_proof p (reverse (s0 :: ps2) ++ ps1) ∗
       p_proof_state w1' ps1' ps_fix lpn' ∗
       ((∃ (ps2' : list string) (w2' a4 : val),
           pencount_frag (definitions.sum_list lpn') ∗
           ⌜reverse (s0 :: ps2) ++ ps1 = reverse ps2' ++ ps1'⌝ ∗ A a0 a4 a3 ∗
           spec_verifier t2 (fill K2 (InjRV (w2', a4))) ∗
           v_proof_state w2' ps2' ∗ tern_state)
        ∨ ⌜length (reverse (s0 :: ps2) ++ ps1) < length ps1'⌝
        ∨ ⌜lastn (length ps1') (reverse (s0 :: ps2) ++ ps1) ≠ ps1'⌝ ∗
          lrel_tern_un A a0 ∗ un_state) -∗ Ψ (w1', a0)%V) -∗
    WP (let: "un_a" := un_a1 in
        let: "susp_un_a" := p_susp "un_a" in
        let: "finish" := p_finish p_ser_susp "susp_un_a" in
        let: "prf_state'" := (prf1, "finish" :: buf1) in
        ("prf_state'", "susp_un_a"))%E
    {{ v, Ψ v }}.
  Proof.
    iIntros "#Htab #Hpsuspspec #Hvserspec #Hvcountspec #Hpserp #HA
             #Hpvuneq #Hlbvfrag #Hinv_authv #Hvisit".
    iIntros "(Htabtok & Hv & Hi & Hpenc & Hbuf & Hid & Hpr & Hintr & Hst & Htok) HΨ".
    v_bind (list_head _).
          wp_pure credit:"Hlc"; wp_pure credit:"Hlctab"; wp_pures.

          iMod (gwp_list_head ⊤ _ (s0 :: ps2) () (λ v, ⌜v = SOMEV #s0⌝)%I
                with "[] [] [$Hv //]") as (?) "[Hv ->] /="; [done| |v_pures].
          { iIntros "!>" (? [[] | (?&?&?&?)]); simplify_eq. eauto. }

          iMod (na_inv_acc with "Htab Htabtok") as "(Htabo & Htabtok & Hclose_tab)"; try solve_ndisj.
          iMod (lc_fupd_elim_later with "Hlctab Htabo") as "Htabo".
          iDestruct "Htabo" as "[(%&%&%m2 &%& %idctr &%&%msp_2 & Hl & %Hm &
              Hbigsep &% & Hvmauth & %Hidinv & Hvisinv & Hst' & Hserp & %Hmspdom2) | Hst']";
            last first.
          { by iPoseProof (tern_state_un_state_excl with "Hst Hst'") as "?". }

          iDestruct (pn_agree with "Hvmauth Hpenc") as "->".
          iDestruct (id_ctr_frag_agree with "Hvmauth Hid") as "->".
          iMod (serpred_alloc msp_2 cntr s with "Hserp") as "[Hserp #Hserpfrag]".
          { apply not_elem_of_dom. intro Hin.
            apply Hmspdom2, elem_of_set_seq in Hin. lia. }

          v_bind (v_deser _).
          iMod ("Hpsuspspec" with "Hv") as (?) "(Hv & Hpsuspdeserspec) /=".

          v_bind (v_deser_par _).
          wp_apply ("Hpsuspdeserspec" with "[$HA $Hpserp $Hserpfrag $Hvmauth $Hpenc $Hv]").
          { admit. (* ⌜unsusp⌝ + lg_p_auth (Group C: prover-side lg auth has no
                      external owner yet) *) }
          iIntros (a1' s_real c' t_real) "(#Hpserspecat & #Hpreal & _ &
              [([% %] & #Hun1' & %&%&%& Hlmauth & % & Hpens & Hpserp' & Hv &
                  Hsubsep & Hpenc & Hvmauth & Hdecorate)|
              [% #HA']])"; wp_pures; last first.
          { wp_bind (p_finish _ _).

            iApply (p_finish_spec' p_ser_susp a1' s_real c' with "[//]").
            iNext. iIntros (p_finish) "Hpfinish". wp_pures.
            simplify_eq.

            iMod (state_update_bad with "Hst Hst'") as "#Hst".

            iPoseProof (big_sepL_cons (λ _, p_buffer_elem) (p_finish, s_real, c') 
                (combine (combine bufl ps1) lpn) with "[$Hbuf $Hpserspecat $Hpfinish]") as 
              "Hbuf".
            { iFrame "∗". iSplit; eauto.
              iIntros "Hst'".
              by iPoseProof (tern_state_un_state_excl with "Hst' Hst") as "?". }

            iMod ("Hclose_tab" with "[$Htabtok]") as "Htabtok".
            { iNext. by iRight. }

            wp_apply (gwp_list_cons _); [done|].
            iIntros (??). wp_pures.
            
            iApply ("HΨ"). iFrame "Htabtok Htok Hi Hintr Hpr".

            iModIntro.
            assert (
              ((p_finish, s_real, c') :: combine (combine bufl ps1) lpn) =
                combine (combine (p_finish :: bufl) (s_real :: ps1)) (c' :: lpn))
              as -> by eauto.
            iSplitL "Hbuf".
            { iFrame "∗ %".
              iPureIntro. exists (definitions.sum_list (c' :: lpn)).
              simpl. split_and!; try done; lia. }

            do 2 iRight. iFrame "#".
            iPureIntro.
            unfold lastn.
            rewrite reverse_cons -assoc /=.
            rewrite !length_app length_reverse /=.
            replace (length ps2 + S (length ps1) - S (length ps1)) with (length ps2) by lia.
            rewrite skipn_app skipn_all2; last (rewrite length_reverse; lia).
            replace (length ps2 - length (reverse ps2)) with 0 by (rewrite length_reverse; lia).
            simpl. intros [=Hne%H5]. done. }

          iPoseProof (big_sepS_sep
            (λ γ, ∃ lb, lg_mapg_p_frag lb γ ∗ ⌜p_sub_obj tA a1' #lb⌝)%I
            (λ γ, ∃ susp, lg_mapg_frag susp γ ∗ ⌜v_sub_obj tA a2' #susp⌝)%I
          with "Hsubsep") as "[Hpsubsep Hvsubsep]".

          wp_bind (p_finish _ _).

          iApply (p_finish_spec' p_ser_susp a1' s_real); try done.
          iNext. iIntros (p_finish) "Hpfinish". wp_pures.

          wp_apply (gwp_list_cons _); [done|].
          iIntros (??). wp_pures.

          iPoseProof (big_sepL_cons (λ _, p_buffer_elem) 
              with "[$Hbuf $Hpfinish $Hpserspecat Hpens Hpsubsep]")
            as "Hbuf".
          { iSplit; eauto. simplify_eq.
            iIntros "Hst". by iFrame. }

          iEval (rewrite visited_map_update_pending_rewrite) in "Hvmauth".
          iMod (visited_deser_commit _ _ _ _ susp a2' c' with "Hvmauth Hid")
            as "(Hvmauth & Hid & Hidtok & #Hvfrag & #Hcapf & Hmapf)".
          iMod ("Hdecorate" $! tA a2' s c' with "[] [//] Hcapf [Hmapf] []")
            as "(#HA' & Hc & Hvser)".
          { iPureIntro. apply sub_pos_refl. }
          { destruct c'; [done|]. rewrite Qp.div_diag. iFrame "Hmapf". }
          { by destruct c'. }

          iSimpl in "Hv". v_pures. v_bind (v_count _).
          iAssert (count_aggregator c' cntr c' a2')%I as "Hagg".
          { rewrite /count_aggregator. by iLeft. }
          iMod ("Hvcountspec" with "Hc Hv") as "[Hc Hv] /=". v_pures.

          v_bind (v_finish _ _ _ _).
          iMod (v_finish_spec with "Htab Hv") as (v_finish) "[Hvfinish Hv] /=".
          v_pures; try solve_vals_compare_safe.

          set (vm' := set_fold (λ (γ : gname) (m0 : state_mapg_type), <[γ:=pending_val]> m0) vm γl).
          set (pn' := definitions.sum_list lpn + size γl).
          set (cntr' := S cntr).
          set (mp2 := match c' with
                      | 0%nat => m2
                      | _ => mapg_insert_def m2 cntr a2'
                      end) in *.
          simplify_eq.
          assert (pn' = size γl + definitions.sum_list lpn) as <- by lia.

          iAssert (|==> ∃ m'', mapg_auth m'' ∗
              ⌜(size γl > 0 ∧ m'' = mapg_insert_def m2 cntr a2'
                ∨ size γl = 0 ∧ m'' = m2)⌝)%I
            with "[]" as "Hmint".
          { (* post-merge: mapg_auth now lives inside visited_mapg_auth
               (extract via visited_mapg_acc at mp2); reconcile when this
               region is adapted to the wand spec. *)
            admit. }
          iMod "Hmint" as (m'') "[Hmauth %]".

          (* [Hbig_assert]: outer visit-update-done iAssert. NOTE: this
             iAssert's postcondition, as written, is STRUCTURALLY UNPROVABLE
             on the Hinv_1 (filled) branch. There [Hvisfin: visit_finished γ0]
             combined with Hvmauth forces [vm !! γ0 = finished_val], and the
             postcondition's [visited_map_update_done vm' mp2 γ0 pn' cntr' :=
             ∃ n, visited_mapg_auth (<[γ0:=done_val n]>vm') mp2 pn' cntr']
             requires regressing γ0 from finished_val to done_val n — which
             Iris ghost updates disallow. Fixing this properly needs one of:
             (a) restructure the postcondition into a disjunction (done branch
                 ∨ already-finished branch) and update all callers to
                 case-analyse; or
             (b) show Hinv_1 is unreachable at this call site (derive False
                 from the fresh [Hvfrag: pval_frag cntr susp] + the prior
                 finish encoded by Hvisfin) — plausible but needs proof.
             Downstream: the [vm_big_sep] admit in the size γl > 0 caller
             below (line ~444) depends on [n0] being semantically-grounded,
             which needs this iAssert closed. See the comment there. *)
          iAssert (
            |={⊤}=>
              seq_tok ⊤ ∗ intransit 1 ∗
              auth_v cntr (InjRV #susp) s ∗
              visited_map_update_done vm' mp2 γ0 pn' cntr' ∗
              sub_susp_count tA a2' (size γl) cntr (size γl) a2' ∗
              mapg_auth m'' ∗ v_susp_big_sep m m2)%I
            with "[Htok Hintr Hidtok Hvmauth Hc Hmauth Hbigsep]"
          as "Hbig_assert"; last
            iMod "Hbig_assert"
              as "(Htok & Hintr & Hauthv & Hvmauth & Hc & Hmauth & Hbigsep)".
          { iMod (na_inv_acc with "Hinv_authv Htok") as "(>Hinvo & Htok & Hclose)";
              [solve_ndisj|solve_ndisj|].
            iDestruct "Hinvo" as "[Hinv_1|Hinv_2]".
            - iDestruct "Hinv_1" as "(%&%&%&%Hxpure1 & Hsusp & #Hfilled & #Hlbvfrag' & #Hvisfin)".
              destruct! Hxpure1. simplify_eq.
              iDestruct (lg_mapg_agree with "Hlbvfrag Hlbvfrag'") as "(<- & _ & _)".
              iPoseProof (id_token_unused with "Hvmauth Hidtok") as "(%Hidunused & Hvmauth & Hidtok)".

              iMod ("Hclose" with "[$Htok Hsusp]") as "Htok".
              { iNext. iLeft. iFrame "Hsusp Hfilled Hlbvfrag Hvisfin". eauto. }

              iModIntro. iFrame "Htok Hintr Hc".
              iAssert (⌜cntr > pid⌝)%I as %Hcntrgt.
              { destruct (le_gt_dec cntr pid) as [Hle|]; last by iPureIntro.
                iDestruct (pval_snapshot_neq _ _ _ _ Hle with "Hpvuneq Hvfrag") as %?.
                done. }
              iSplitR "Hvmauth".
              { iRight. iFrame "#".
                repeat (iSplit; eauto). }
              admit.

            - iDestruct "Hinv_2" as "(%&%&%&%&%&%&%&%& #Hcap & Hunfill & Hmfrag & %Hmsub & %Hsamser & #Hserpred & Hsusp)".

              destruct! H6. rewrite /filled_string /simple_string in H7. 
              simplify_eq.

              iPoseProof (mapg_auth_alive with "Hmauth Hmfrag") as (y) "%Hin".
              destruct Hin as [(? & Hin & Hxequiv)%Some_equiv_eq Hyequiv].
              edestruct (mapg_alive_lookup_Cinl _ _ _ y Hin) as (y' & Halive & Hyy'); first done.
              clear Hin. rename Halive into Hin.

              iDestruct (big_sepM_delete _ (mapg_alive _) pid y' _ with "Hbigsep") as "[Hms Hbigsep]".
              
              iDestruct "Hms" as (ctr ?? x1 ?????[Hcgt [Hin' Hyequiv']])
                  "(Hlc & Hxser & #Hxserpred & Hxserspec & Hxauth & Hxc & Hxfin)".

              assert (x1 = pv) as ->.
                  { rewrite Hyy' in Hyequiv'. rewrite Hyequiv' in Hyequiv. simpl in Hyequiv.
                    fold_leibniz. by apply (inj to_agree) in Hyequiv. }

              iDestruct "Hxc" as "(Hxcap & % & Hxc & Hxagg)".
              
              iAssert (⌜cntr > pid⌝)%I as %Hcntrgt.
              { destruct (le_gt_dec cntr pid) as [Hle|]; last by iPureIntro.
                iDestruct (pval_snapshot_neq _ _ _ _ Hle with "Hpvuneq Hvfrag") as %?.
                done. }
              iMod (visited_update_done with
                  "Hvmauth Hidtok Hintr Hvfrag Hlbvfrag Hsusp Hxc")
                as "(Hintr & Hvisdone & Hvmauth & Hxc & Hsusp & Hpvuneq')";
                [ done | done | ].

              iAssert (sub_susp_count_frags t pv ctr pid Nc pv) with "[$Hxcap $Hxc $Hxagg //]" as "Hxc".

              iPoseProof (big_sepM_insert _ _ pid _ 
                with "[$Hbigsep $Hxfin $Hxser $Hxserspec $Hxc $Hlc $Hxauth]") as "Hbigsep".
              { by rewrite lookup_delete. }
              { iExists q. iFrame "#". iPureIntro. split. 
                { inversion Hcgt; simplify_eq; try lia. }
                split; eauto. }

              iMod ("Hclose" with "[$Htok Hunfill Hmfrag Hsusp]") as "Htok".
              { iNext. iRight. iFrame "Hsusp Hunfill Hmfrag Hcap Hserpred". eauto. }

              iModIntro. iFrame "Htok Hintr Hc Hvmauth Hmauth".
              iSplitR "Hbigsep".
              { iRight. iFrame "#".
                repeat (iSplit; eauto). admit. }
              admit. }

          case_bool_decide; simplify_eq; v_pures.
          -- v_bind (v_finish _).
            assert (size γl = 0) as Hγl0 by lia.
            destruct! H5; simplify_eq; first lia.

            iDestruct "Hvmauth" as (n0) "Hvmauth".
            set (vm'' := (<[γ0:=done_val n0]> vm')).

            iAssert (
              |={⊤}=> ∃ E',
                ⌜E' = ⊤ ∖ ↑ver_susp_n susp⌝ ∗
                □(∀ pid psusp pγ, ⌜pid < cntr⌝ -∗ pval_frag pid psusp -∗
                  lg_mapg_frag psusp pγ -∗ visit_reached_done pγ -∗
                  ⌜↑(ver_susp_n psusp) ⊆ E'⌝) ∗
                auth_transit_v ⊤ cntr (InjRV #susp) s ∗
                visited_map_update_finished vm'' mp2 γ0 pn' cntr' ∗
                mapg_auth m2 ∗ v_susp_big_sep m m2)%I
              with "[Htok Hauthv Hintr Hvmauth Hmauth Hbigsep]"
              as ">(%&->& #Hnmspc' & Htauthv & Hvmauth & Hmauth & Hbigsep)".
            { admit. }

            rewrite /mp2 Hγl0 /=. subst vm''.
            iEval (rewrite visited_map_update_finished_rewrite insert_insert) in "Hvmauth".
            iMod ("Hclose_tab" with "[$Htabtok Hl Hbigsep Hvmauth Hvisinv Hst' Hserp]") as "Htabtok".
            { iNext. iLeft.
              iExists d, m, m2, (<[γ0:=finished_val]> vm'), cntr', pn', _.
              iFrame "Hl Hbigsep Hst' Hserp Hvmauth".
              iSplit; first done.
              iSplit; first done.
              iSplit.
              { iPureIntro. intros ctr' Hge. apply Hidinv. lia. }
              iSplit; last first.
              { iPureIntro. rewrite dom_insert set_seq_S_end_union_L. set_solver. }
              subst vm'.
              assert (γl = ∅) as ->.
              { apply size_empty_inv in Hγl0. by fold_leibniz. }
              rewrite set_fold_empty.
              iApply (big_sepM_insert_2 (vm_big_sep_lam_unset m)).
              { rewrite /vm_big_sep_lam_unset. by iIntros (id [=]). }
              iApply "Hvisinv". }

            v_bind (v_finish _).
            iMod ("Hvfinish" $! ⊤ with "[] Htabtok Hlc Hvser Hvserspec Hc
                    Htauthv Hst Hv") as "(Hv & Htabtok & Htok & Hst & Hintr) /=".
            { iModIntro. iIntros (pid' psusp pγ) "%Hlt Hpv Hlg Hvis".
              iPoseProof ("Hnmspc'" $! pid' psusp pγ with "[//] Hpv Hlg Hvis") as "%Hsub".
              iPureIntro. clear -Hsub. set_solver. }

            v_pures. v_bind (list_tail _).
            iMod (gwp_list_tail ⊤ _ (s_real :: _) () (λ v, ⌜is_proof _ ps2⌝)%I
                  with "[] [] [$Hv //]") as (u) "[Hv %Hvprf'] /="; [done| |v_pures].
            { by iIntros "!>" (?). }

            iApply ("HΨ"). iFrame "Htabtok Htok Hpr Hi Hintr".
            iModIntro. iSplitL "Hbuf".
            { iPoseProof (big_sepL_cons (λ _, p_buffer_elem) with "Hbuf") as "Hbuf".
              assert
                (((p_finish, s_real, 0) :: combine (combine bufl ps1) lpn) =
                  combine (combine (p_finish :: bufl) (s_real :: ps1)) (0 :: lpn))
                as -> by done.
              iFrame "Hbuf".
              iPureIntro. exists prf1, v, (definitions.sum_list (0 :: lpn)).
              simpl. split_and!; try done; lia. }
            iLeft. iExists ps2. iSimpl.
            assert (pn' = definitions.sum_list lpn) as <- by lia.
            iFrame "HA' Hv Hid Hpenc Hst".
            iSplit.
            { iPureIntro. by rewrite reverse_cons -assoc. }

            iPureIntro.
            eexists _. split; eauto.
            repeat f_equal. lia.

          -- assert (size γl > 0) as Hγlpos.
            { destruct (size γl); simplify_eq. lia. }
            destruct! H5; try lia; simplify_eq.

            v_load. v_pures. v_bind (map.map_insert _ _ _).
            iMod (gwp_map_insert #cntr _ _ _ () ⊤ _
              (λ d, ⌜is_map d (<[ #cntr := _ ]> m)⌝)%I
              with "[//] [] [$Hv //]") as (?) "[Hv %Hmins] /=".
            { by iIntros "!#" (? Hins). }
            (* Unshelve. 2: done. *)
            
            v_store. v_pures.

            iDestruct (v_susp_big_sep_fresh with "Hbigsep") as %Hm_cntr_none;
              first exact Hidinv.

            iDestruct (big_sepM_insert (v_susp_big_sep_lam m) (mapg_alive m2) cntr (mapg_alive_insert_val a2') Hm_cntr_none
              with "[$Hbigsep $Hvfinish $Hauthv $Hc $Hagg $Hcapf $Hvser]") as "Hbigsep".
            { iFrame "#". admit. }

            iPoseProof (big_sepM_mono
                (v_susp_big_sep_lam m)
                (v_susp_big_sep_lam (<[#cntr:=(#(size γl), v_finish)%V]> m))
              with "Hbigsep") as "Hbigsep".
            { iIntros (?? Hlook) "Hbigsep".
              rewrite /v_susp_big_sep_lam.
              iDestruct "Hbigsep" as (?????????[?[??]]) "($ & $ & $ & $)".
              iPureIntro. exists q.
              do 2 (split; eauto).
              rewrite lookup_insert_ne; eauto.
              intros ?. simplify_eq.
              specialize (Hidinv k ltac:(lia)).
              simplify_eq. }

            iEval (rewrite -mapg_alive_insert) in "Hbigsep".
            iEval (rewrite -/(mapg_insert_def m2 cntr a2')) in "Hbigsep".
            iDestruct "Hvmauth" as (n0) "Hvmauth".
            assert (mp2 = mapg_insert_def m2 cntr a2') as Hmp2eq.
            { subst mp2. destruct (size γl); [lia|done]. }
            iEval (rewrite Hmp2eq) in "Hvmauth".
            iMod ("Hclose_tab" with "[$Htabtok Hl Hbigsep Hvmauth Hvisinv Hst' Hserp]") as "Htabtok".
            { iNext. iLeft.
              iExists _, (<[#cntr:=(#(size γl), v_finish)%V]> m), (mapg_insert_def m2 cntr a2'),
                (<[γ0:=done_val n0]> vm'), cntr', pn', _.
              iFrame "Hl Hbigsep Hst' Hserp Hvmauth".
              iSplit.
              { iPureIntro. done. }
              iSplit.
              { iPureIntro.
                rewrite /mapg_insert_def mapg_alive_insert.
                rewrite map_size_insert_None; last done.
                rewrite (map_size_insert_None _ _ _ (Hidinv cntr (Nat.le_refl _))).
                by rewrite H. }
              iSplitR "".
              { iPureIntro. intros ctr'' Hge. subst cntr'.
                rewrite lookup_insert_ne;
                  last (intros [=Heq]; apply Nat2Z.inj in Heq; subst; lia).
                apply Hidinv. lia. }
              iSplitR.
              { (* vm_big_sep for the extended vm [<[γ0:=done_val n0]>vm'].
                   To discharge [vm_big_sep_lam_unset _ γ0 (done_val n0)] we
                   need [is_Some (m !! #n0)]. This is invariant (via Hvisinv:
                   [vm_big_sep m vm] whose lam_unset arm on done_val encodes
                   exactly this) BUT ONLY for γ's already in vm. Here γ0 was
                   just added by the outer [Hbig_assert] iAssert, and under
                   its current admitted body [n0] is a fresh unconstrained
                   nat — so we cannot recover [m !! #n0 = Some _].
                   Semantically [n0 = pid] (the parent id from the auth_v
                   destruct at Hauthv), and [pid < cntr] gives
                   [m !! #pid = Some _] via Hvisinv on the parent γ_parent
                   that maps to done_val pid. Closing this admit requires
                   either (a) closing the [Hbig_assert] body so its output
                   exposes [n0 = pid], which itself needs restructuring the
                   iAssert postcondition into a disjunction to handle the
                   Hinv_1 [visit_finished γ0] branch's state-regression
                   issue; or (b) adding a coupling invariant to
                   [visited_mapg_auth] relating [vm !! γ = done_val n] to
                   [n ∈ dom (mapg_alive mp)]. See prior analysis notes. *)
                admit. }
              iPureIntro. rewrite dom_insert_L. subst cntr'.
              rewrite set_seq_S_end_union_L. set_solver. }

            v_pures. v_bind (list_tail _).
            iMod (gwp_list_tail ⊤ _ (s_real :: _) () (λ v, ⌜is_proof _ ps2⌝)%I
                  with "[] [] [$Hv //]") as (u) "[Hv %Hvprf'] /="; [done| |v_pures].
            { by iIntros "!>" (?). }

            iApply ("HΨ"). iFrame "Htabtok Htok Hpr Hi Hintr".
            iModIntro. iSplitL "Hbuf".
            { iPoseProof (big_sepL_cons (λ _, p_buffer_elem) with "Hbuf") as "Hbuf".
              assert
                (((p_finish, s_real, size γl) :: combine (combine bufl ps1) lpn) =
                  combine (combine (p_finish :: bufl) (s_real :: ps1)) (size γl :: lpn))
                as -> by done.
              iFrame "Hbuf".
              iPureIntro. exists prf1, v, (definitions.sum_list (size γl :: lpn)).
              simpl. split_and!; try done; lia. }
            iLeft. iExists ps2. iSimpl.
            assert (pn' = size γl + definitions.sum_list lpn) as <- by lia.
            iFrame "HA' Hv Hid Hpenc Hst".
            iSplit.
            { iPureIntro. by rewrite reverse_cons -assoc. }

            iPureIntro.
            eexists _. split; eauto.
            repeat f_equal. lia.

  Admitted.

End unauth_step.
