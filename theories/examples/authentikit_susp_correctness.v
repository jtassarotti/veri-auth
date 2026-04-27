From auth.prelude Require Import stdpp.
From auth.rel_logic_tern_susp Require Export model spec_rules spec_tactics interp.
From auth.heap_lang Require Import primitive_laws derived_laws typedproph.
From auth.heap_lang.lib Require Import list map serialization_susp.
From auth.examples Require Export authentikit_susp authentikit_base_susp_correctness.
From iris.base_logic.lib Require Export na_invariants fancy_updates.
From iris.algebra.lib Require Import dfrac_agree.

(** We need [i_Authentikit] to be an expression since [v_Authenticable] needs to initialize its
    cache and specialize [v_unauth]. *)
Definition i_Authenticable : expr :=
  (i_Auth_auth, i_Auth_mu, i_Auth_pair, i_Auth_sum, i_Auth_string, i_Auth_int, i_auth, i_unauth).
Definition i_Authentikit : expr := (i_return, i_bind, i_Authenticable).

Definition idcntrUR := authUR nat.
Class idcntrG Σ := IdcntrG { idcntr_inG :> inG Σ idcntrUR; idcntrG_name : gname }.

Section idcntr.
  Context `{!idcntrG Σ}.

  Definition id_frag (id : nat) := own idcntrG_name (●{DfracOwn (1/2)} id).

  Lemma id_agree id id' :
    id_frag id -∗ id_frag id' -∗ ⌜id = id'⌝ ∗ id_frag id ∗ id_frag id'.
  Proof.
    rewrite /id_frag. iIntros "H1 H2". iCombine "H1 H2" as "H".
    iDestruct (own_valid with "H") as %Hv.
    apply auth_auth_dfrac_op_valid in Hv as [_ [Heq _]].
    iDestruct "H" as "[H1 H2]". iFrame.
    iPureIntro. apply leibniz_equiv. exact Heq.
  Qed.

  Lemma id_update id id' (Hle : id ≤ id') :
    id_frag id -∗ id_frag id ==∗ id_frag id' ∗ id_frag id'.
  Proof.
    rewrite /id_frag. iIntros "H1 H2". iCombine "H1 H2" as "H".
    iMod (own_update with "H") as "H".
    { apply (auth_update_auth id id' (id' - id)).
      apply (nat_local_update id 0 id' (id' - id)). lia. }
    iDestruct "H" as "[H1 H2]". iFrame. done.
  Qed.

End idcntr.

(** * Correctness proof *)
Section proof.
  Context `{!authG Σ, !seqG Σ, !oneshotG Σ, !lg_mapG Σ, !mapG Σ, !capG Σ, !idcntrG Σ}.

  Definition authBaseN : namespace := nroot .@ "susp_sec".
  Definition tableN : namespace := authBaseN .@ "table".

  Local Notation prover_susp_set := (prover_susp_set authBaseN).
  Local Notation susp_p_ser_spec := (susp_p_ser_spec authBaseN).
  Local Notation susp_ser_p_real := (susp_ser_p_real authBaseN).

  Local Notation ver_susp_set := (ver_susp_set authBaseN).
  Local Notation v_ser_spec := (v_ser_spec authBaseN).
  Local Notation ser_v_proph := (ser_v_proph authBaseN).
  Local Notation auth_v := (auth_v authBaseN).


	Definition v_finish_spec' (finish x a ser : val) : iProp Σ :=
		□(∀ (E: coPset) tᵥ K (s : string) (t : evi_type) id Nc,
      ⌜↑ver_susp_set ⊆ E ∧ ↑tableN ⊆ E⌝ -∗ £ 1 -∗
      seq_tok E -∗ ser_v_proph t x s -∗ v_ser_spec ser t -∗
			sub_susp_count t x 0 id Nc x -∗ auth_v a s -∗
			spec_verifier tᵥ (fill K (finish #()))
			={⊤}=∗ spec_verifier tᵥ (fill K (SOMEV #())) ∗ seq_tok E).

	(* Definition v_finish_spec2' (finish x a ser : val) : iProp Σ :=
    □(∀ tᵥ K (E: coPset) (s s' : string) (t : evi_type) (susp : loc),
      ⌜↑ver_susp_set ⊆ E ∧ ↑tableN ⊆ E⌝ -∗ £ 1 -∗
      seq_tok E -∗ ser_v_proph t x s -∗ v_ser_spec ser t -∗
      sub_susp_count t x 0 -∗ ⌜a = InjRV #susp⌝ -∗ hashed s -∗
			⌜s' = filled_string (hash s)⌝ -∗
			seq_inv (ver_susp_n authBaseN x) (auth_susp_v_ser_proph_inv a s') -∗
			spec_verifier tᵥ (fill K (finish #()))
			={⊤}▷=∗ spec_verifier tᵥ (fill K (SOMEV #()))). *)

	(* Definition finish_specs finish x a ser (s : string) : iProp Σ :=
    ((⌜a = InjLV #(hash s)⌝ ∗ v_finish_spec1' finish x a ser) ∨ 
      (∃ s' (susp : loc), ⌜a = InjRV #susp⌝ ∗ hashed s ∗
				⌜s' = filled_string (hash s)⌝ ∗
        seq_inv (ver_susp_n authBaseN a) (auth_susp_v_ser_proph_inv x s') ∗
        v_finish_spec2' finish x a ser)). *)

  Definition v_susp_big_sep_lam (m : gmap val val) (m' : mapg_type) k agv : iProp Σ :=
    ∃ (ctr id Nc: nat) (finish x a ser : val) (t : evi_type) (s : string) (q : Qp),
      (⌜ctr > 0 ∧ m !! k = Some (#ctr, finish)%V ∧ agv ≡ to_frac_agree q x ∧ k = #id⌝ ∗
      £ 1 ∗ ser_v_proph t x s ∗ v_ser_spec ser t ∗ auth_v a s ∗
      sub_susp_count_frags t x ctr id Nc ∗ v_finish_spec' finish x a ser)%I.

  Definition v_susp_big_sep (m : gmap val val) (m' : mapg_type) : iProp Σ :=
    [∗ map] k ↦ agv ∈ m', v_susp_big_sep_lam m m' k agv.

  Definition is_v_susp_table (l : loc) : iProp Σ :=
    ∃ (d : val) (m : gmap val val) (m' : mapg_type) (ctr : nat),
      l ↦ᵥ d ∗ ⌜is_map d m⌝ ∗ v_susp_big_sep m m' ∗ 
      mapg_auth m' ∗ id_frag ctr ∗ 
      ⌜∀ ctr', ctr' ≥ ctr → m !! #ctr' = None⌝.

  Definition inv_v_susp_table (l: loc) := seq_inv tableN (is_v_susp_table l).


	Lemma v_finish_spec :
    ∀ tᵥ K (a x ser : val) (st : loc),
      inv_v_susp_table st -∗
      spec_verifier tᵥ (fill K (v_finish #st a x ser))
			={⊤}=∗ ∃ (finish : val), 
				v_finish_spec' finish x a ser ∗
				spec_verifier tᵥ (fill K finish).
  Proof.
   (* iIntros (?? ????) "#Htab Hi".
    rewrite /v_finish. v_pures.
    iFrame. iModIntro.
    iIntros "!#" (???????[??]) "Hlc Htok Hser Hserspec Hc Hvauth Hv".
    iDestruct "Hvauth" as "[->|(%&%& -> & -> & #Hinv)]".
    - v_pures. v_bind (ser _).
      iMod ("Hserspec" with "Hc Hser Hv") as "(Hc & Hser & Hv) /=".
      v_pures. v_bind (Hash _).
      iMod (step_verifier_hash with "Hv") as "Hv /="; try done.
      v_pures; try solve_vals_compare_safe.
      case_bool_decide; simplify_eq; v_pures.
      iFrame. eauto.
    - v_pures. v_bind (ser _).
      iMod ("Hserspec" with "Hc Hser Hv") as "(Hc & Hser & Hv) /=".
      v_pures.

      iMod (na_inv_acc with "Htab Htok") as "(Htabo & Htok & Hclose_tab)"; try solve_ndisj.
      iMod (na_inv_acc with "Hinv Htok") as "(Hinvo & Htok & Hclose_inv)"; try solve_ndisj.

      iDestruct "Hinvo" as ">[Hinv_1|Hinv_2]".
      + iDestruct "Hinv_1" as "(%s1&%& %& (%&[%Heq %]& Hsusp))".
        simplify_eq. v_load. v_pures. v_bind (Hash _).
        iMod (step_verifier_hash with "Hv") as "Hv /="; try done.
        v_pures; try solve_vals_compare_safe.
        case_bool_decide; unfold filled_string in Heq; simplify_eq.
        v_pures. iFrame.
        
        iMod ("Hclose_inv" with "[$Htok Hsusp]") as "Htok".
        { iNext. iLeft. iFrame. eauto. }

        iMod ("Hclose_tab" with "[$Htok $Htabo]") as "Htok".
        by iModIntro.
        
      + iDestruct "Hinv_2" as "(%&%&%&%&%&%&%&%& Hmfrag & %Hmsub & Hsusp & Hproph)".
        iMod (lc_fupd_elim_later with "Hlc Htabo") as "Htabo".
        iDestruct "Htabo" as "(%&%&%&%idctr & Hl & %Hm & Hbigsep & Hmauth & Hidfrag & %Hidinv)".

        simplify_eq. v_load. v_pures. v_bind (Hash _).
        iMod (step_verifier_hash with "Hv") as "Hv /="; try done.
        v_bind (ResolveProph _ _).
        iMod (step_verifier_resolveproph with "Hv") as "Hv /="; try done.
        v_pures. v_bind (Hash _).
        iMod (step_verifier_hash with "Hv") as "Hv /="; try done.
        v_pures. v_bind (_ <- _)%E.

        iPoseProof (mapg_subset with "Hmauth Hmfrag") as (?) "%Hin".
        destruct Hin as [(?&Hin&?)%Some_equiv_eq ?].

        iDestruct (big_sepM_delete _ m' #pid _ Hin with "Hbigsep") as "[Hms Hbigsep]".
        iDestruct "Hms" as (ctr ?????????[Hcgt [Hin' [? ?]]]) "(Hlc & Hxser & Hxserspec & #Hauthv & Hxc & Hxfin)".
        assert (pid = id0) as <-; try by simplify_eq. simplify_eq.

        iMod (count_update authBaseN with "[] Hxc Hsusp Hv") as "(Hxc & Hsusp & Hv) /=".
        { assert (x1 = pv) by admit. by simplify_eq. }

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

          iPoseProof (big_sepM_mono 
              (v_susp_big_sep_lam m m')
              (v_susp_big_sep_lam (delete #pid m) (delete #pid m')) 
            with "Hbigsep") as "Hbigsep".
          { iIntros (?? Hlook) "Hbigsep".
            rewrite /v_susp_big_sep_lam.
            iDestruct "Hbigsep" as (??????????[?[?[??]]]) "($ & $ & $ & $)".
            iPureIntro. exists q1. 
            split; eauto. split; last eauto.
            destruct (decide (k = #pid)); simplify_eq.
            rewrite lookup_delete_Some in Hlook.
            destruct! Hlook. simplify_eq.
            rewrite lookup_delete_Some. eauto. }

          v_store. v_pures.
          assert (ctr - 1 = 0) as ->.
          { assert (ctr = 1) as ->; eauto. simplify_eq. lia. }
          iMod (mapg_remove_count_0 authBaseN with "Hxc Hmauth") as "[Hxc Hmauth]".

          iMod ("Hclose_tab" with "[$Htok $Hl $Hmauth $Hbigsep $Hidfrag]") as "Htok".
          { iNext. iFrame "%".
            iPureIntro. intros ??.
            rewrite lookup_delete_None.
            right. by apply Hidinv. }

          by iMod ("Hxfin" $! E with "[//] Hlc Htok Hxser Hxserspec Hxc Hauthv Hv") as "[$$]".
          
        * v_load. v_bind (map_remove _ _).
          iMod (gwp_map_remove () ⊤ #pid d m _
            (λ d', ⌜is_map d' (delete #pid m)⌝)%I
            with "[//] [] [$Hv //]") as (?) "[Hv %Hmdel] /="; 
            try by iIntros "!#" (?).
          Unshelve. 2: done.

          iPoseProof (big_sepM_mono 
              (v_susp_big_sep_lam m m')
              (v_susp_big_sep_lam (delete #pid m) (delete #pid m')) 
            with "Hbigsep") as "Hbigsep".
          { iIntros (?? Hlook) "Hbigsep".
            rewrite /v_susp_big_sep_lam.
            iDestruct "Hbigsep" as (??????????[?[?[??]]]) "($ & $ & $ & $)".
            iPureIntro. exists q1. 
            split; eauto. split; last eauto.
            destruct (decide (k = #pid)); simplify_eq.
            rewrite lookup_delete_Some in Hlook.
            destruct! Hlook. simplify_eq.
            rewrite lookup_delete_Some. eauto. }

          v_store. v_pures. v_load. v_pures. v_bind (map.map_insert _ _ _).
          iMod (gwp_map_insert #pid _ v _ () ⊤ _
            (λ d', ⌜is_map d' (<[ #pid := _ ]> (delete #pid m))⌝)%I
            with "[//] [] [$Hv //]") as (?) "[Hv %Hmins] /=".
          { by iIntros "!#" (? Hins). }
          Unshelve. 2: done.
          rewrite insert_delete_insert in Hmins.

          iPoseProof (big_sepM_mono 
              (v_susp_big_sep_lam (delete #pid m) (delete #pid m')) 
              (v_susp_big_sep_lam (<[#pid:=(#(ctr - 1), finish)%V]> m) m')
            with "Hbigsep") as "Hbigsep".
          { iIntros (?? Hlook) "Hbigsep".
            rewrite /v_susp_big_sep_lam.
            iDestruct "Hbigsep" as (??????????[?[Hreflook[??]]]) "($ & $ & $ & $)".
            iExists q1. iPureIntro. 
            split; eauto. split; last eauto.
            destruct (decide (k = #pid)); simplify_eq.
            rewrite lookup_delete_Some in Hlook.
            destruct! Hlook. simplify_eq.
            rewrite lookup_delete_Some in Hreflook.
            destruct! Hreflook. 
            rewrite lookup_insert_ne; eauto. }

          iPoseProof (big_sepM_insert _ _ #pid _ 
            with "[$Hbigsep $Hxfin $Hxser $Hxserspec $Hxc $Hlc $Hauthv]") as "Hbigsep".
          { by rewrite lookup_delete. }
          { iExists q0. iPureIntro. split. 
            { inversion Hcgt; simplify_eq; try lia. }
            split; last eauto.
            rewrite lookup_insert.
            repeat f_equal. lia. }

          rewrite (insert_delete _ _ _ Hin). v_store. v_pures.
          iMod ("Hclose_tab" with "[$Htok $Hl $Hmauth $Hbigsep $Hidfrag]") as "Htok".
          { iNext. iFrame "%".
            iPureIntro. intros ??.
            rewrite lookup_insert_ne.
            by apply Hidinv.
            intros ?. simplify_eq.
            specialize (Hidinv ctr' H4). simplify_eq. }
          by iFrame. *)
  Admitted.

  Definition p_finish_spec (finish ser a : val) (sprf : string) : iProp Σ :=
    ∀ E pr_s s ls t,
      ⌜↑prover_susp_set ⊆ E⌝ -∗
      {{{ seq_tok E ∗ proph_proof pr_s (sprf :: ls) ∗
          susp_p_ser_spec ser t ∗ susp_ser_p_real t a s ∗
          ⌜sprf = s⌝ }}}
          finish #pr_s
      {{{ s, RET #s; seq_tok E ∗ proph_proof pr_s ls }}}.

  Definition p_finish_spec_bad (finish ser a : val) (sprf : string) : iProp Σ :=
    ∀ E pr_s s ls t,
      ⌜↑prover_susp_set ⊆ E⌝ -∗
      {{{ seq_tok E ∗ proph_proof pr_s (sprf :: ls) ∗
          susp_p_ser_spec ser t ∗ susp_ser_p_real t a s ∗
          ⌜sprf ≠ s⌝ }}}
          finish #pr_s
      {{{ v, RET v; False }}}.

  Lemma p_finish_spec' :
    ∀ ser a sprf,
      {{{ True }}}
          p_finish ser a
      {{{ (finish : val), RET finish; 
          p_finish_spec finish ser a sprf }}}.
  Proof.
    iIntros (????) "_ HΦ".
    wp_rec. wp_pures. iApply "HΦ".
    iModIntro.
    iIntros (???????) "!# (Htok & Hprf & #Hserspec & #Hser & ->) HΦ".
    wp_pures.
    wp_apply ("Hserspec" with "[//] Hser").
    iIntros (?). wp_pures.

    wp_apply (wp_resolve_proph_string with "Hprf").
    iIntros (?) "[% Hprf]". wp_pures.
    simplify_eq.

    iApply "HΦ". by iFrame.
  Qed.

  Lemma p_finish_spec_bad' :
    ∀ ser a sprf,
      {{{ True }}}
          p_finish ser a
      {{{ (finish : val), RET finish; 
          p_finish_spec_bad finish ser a sprf }}}.
  Proof.
    iIntros (????) "_ HΦ".
    wp_rec. wp_pures. iApply "HΦ".
    iModIntro.
    iIntros (???????) "!# (Htok & Hprf & #Hserspec & #Hser & %) HΦ".
    wp_pures.
    wp_apply ("Hserspec" with "[//] Hser").
    iIntros (?). wp_pures.

    wp_apply (wp_resolve_proph_string with "Hprf").
    iIntros (?) "[% Hprf]". wp_pures.
    simplify_eq.
  Qed.

  Definition p_buffer_elem (finish_s : (val * string)) : iProp Σ :=
    ∃ (finish ser a : val) (pr_s s : string) (t : evi_type),
      ⌜finish_s = (finish, pr_s)⌝ ∗
      susp_ser_p_real t a s ∗ susp_p_ser_spec ser t ∗
      p_finish_spec finish ser a pr_s.

  Definition p_buffer_elem_bad (finish_s : (val * string)) : iProp Σ :=
    ∃ (finish ser a : val) (pr_s s : string) (t : evi_type),
      ⌜finish_s = (finish, pr_s)⌝ ∗
      susp_ser_p_real t a s ∗ susp_p_ser_spec ser t ∗
      p_finish_spec_bad finish ser a pr_s.

  Definition p_buffer (buf : list (val * string)) : iProp Σ :=
    [∗ list] k ↦ finish_s ∈ buf, p_buffer_elem finish_s.

  Definition p_buffer_bad (buf : list (val * string)) : iProp Σ :=
    ∃ buf' buf'' finish pr_s,
      ⌜buf = buf' ++ [(finish, pr_s)] ++ buf''⌝ ∗
      p_buffer_elem_bad (finish, pr_s) ∗
      [∗ list] k ↦ finish_s ∈ buf', p_buffer_elem finish_s ∗
      [∗ list] k ↦ finish_s ∈ buf'', p_buffer_elem finish_s.

  Definition p_proof_state (v : val) (ps : list string) : iProp Σ :=
    ∃ (prf1 buf1 : val) (bufl : list val) ps',
      ⌜v = (prf1, buf1)%V⌝ ∗ p_buffer (List.combine bufl ps) ∗
      ⌜is_proof prf1 ps'⌝ ∗ ⌜is_list bufl buf1⌝.

  Definition p_bad_proof_state (v : val) (ps : list string) : iProp Σ :=
    ∃ (prf1 buf1 : val) (bufl : list val) ps',
      ⌜v = (prf1, buf1)%V⌝ ∗ p_buffer_bad (List.combine bufl ps) ∗
      ⌜is_proof prf1 ps'⌝ ∗ ⌜is_list bufl buf1⌝.

  Definition v_proof_state (v : val) (ps : list string) (cntr : nat) : Prop :=
    ∃ (prf : val),
      v = (prf, #cntr)%V ∧ is_proof prf ps.

  Definition lrel_auth_comp_tern (A : lrel_tern Σ) : lrel Σ := LRel (λ v1 v2 v3,
    ∀ t2 K2 t3 K3 p (ps ps1 ps2 : list string) (w1 w2 : val) (cntr : nat),
      {{{ seq_tok ⊤ ∗ spec_verifier t2 (fill K2 (v2 w2)) ∗
          spec_ideal t3 (fill K3 (v3 #())) ∗ id_frag cntr ∗
          p_proof_state w1 ps1 ∗ ⌜v_proof_state w2 ps2 cntr⌝ ∗
          proph_proof p ps ∗ ⌜ps = reverse ps2 ++ ps1⌝
      }}}
        v1 w1
      {{{ ps1' (w1' a1 a3 : val), RET (w1', a1)%V;
          seq_tok ⊤ ∗ spec_ideal t3 (fill K3 a3) ∗
          proph_proof p ps ∗
          
          ((∃ ps2' (w2' a2 : val) cntr',
            ⌜ps = reverse ps2' ++ ps1'⌝ ∗ id_frag cntr' ∗
            A a1 a2 a3 ∗ p_proof_state w1' ps1' ∗
              spec_verifier t2 (fill K2 (SOMEV (w2', a2)%V)) ∗
              ⌜v_proof_state w2' ps2' cntr'⌝) ∨
              
            (∃ x, 
              ⌜ps = x ++ ps1'⌝ ∗
              (lrel_tern_bin A) a1 a3 ∗
              p_bad_proof_state w1' ps1'))
            
            (* (∃ K3 ps2' (v2' w2' : val),
              spec_verifier t2 (fill K3 (v2' w2')) ∗
                (lrel_tern_bin A) a1 a3 ∗
                p_bad_proof_state w1' ps1' ∗
                v_proof_state p w2' ps2' ∗
                £ (List.length ps2' + List.length ps1' - 
                    List.length ps1 - List.length ps2) ∗
                (spec_verifier t2 (fill K3 (v2' w2')) ∗
                v_proof_state p w2' ps2' ∗
                £ (List.length ps2') ∗
                seq_tok ⊤
                ={⊤}=∗
                  ((∃ a2 w2'' x ps2'',
                      spec_verifier t2 (fill K2 (SOMEV (w2'', a2)%V)) ∗
                      v_proof_state p w2'' ps2'' ∗
                      (lrel_tern_un A) a2 ∗
                      ⌜reverse ps1 ++ ps2 = reverse ps1' ++ ps2''⌝ ∗
                      ⌜ps2'' ++ x = ps2'⌝ ∗
                      £ (List.length ps2'')) ∨
                  spec_verifier t2 (fill K2 NONEV)) ∗
                  seq_tok ⊤)) ∨

            (spec_verifier t2 (fill K2 NONEV) ∗ (lrel_tern_bin A) a1 a3 ∗
                p_bad_proof_state w1' ps1')) *)
            (* Plus some postconditions to carry for bad cases *)
      }}})%I.

  Definition lrel_auth_comp_bin (A : lrel_bin Σ) : lrel_bin Σ := LRelBin (λ v1 v3,
    ∀ t3 K3 p (ps ps1 : list string) (w1 : val),
      {{{ seq_tok ⊤ ∗ spec_ideal t3 (fill K3 (v3 #())) ∗
          p_bad_proof_state w1 ps1 ∗ proph_proof p ps ∗
          (∃ x, ⌜ps = x ++ ps1⌝)
      }}}
        v1 w1
      {{{ ps1' x (w1' a1 a3 : val), RET (w1', a1)%V;
          proph_proof p ps ∗ ⌜ps = x ++ ps1'⌝ ∗
          seq_tok ⊤ ∗ p_bad_proof_state w1' ps1' ∗
          spec_ideal t3 (fill K3 a3) ∗ A a1 a3
      }}})%I.

  Definition lrel_auth_comp_un (A : lrel_un Σ) : lrel_un Σ := LRelUn (λ v2,
    (□ ∀ t2 K2 (ps2 : list string) (w2 : val),
      seq_tok ⊤ ∗ spec_verifier t2 (fill K2 (v2 w2)) ∗
      ⌜v_proof_state w2 ps2 0⌝
      ={⊤}=∗ 
        seq_tok ⊤ ∗ 
        ((∃ ps2' (w2' a2 : val), 
          ⌜v_proof_state w2' ps2' 0⌝ ∗
          spec_verifier t2 (fill K2 (SOMEV (w2', a2)%V)) ∗ A a2) ∨
          spec_verifier t2 (fill K2 NONEV))))%I.

  Definition lrel_auth_comp' (A : lrel_tern Σ) : lrel_tern Σ :=
    LRelTern (lrel_auth_comp_tern A)
             (lrel_auth_comp_bin (lrel_tern_bin A))
             (lrel_auth_comp_un (lrel_tern_un A)).

  Program Definition lrel_auth_comp : kindO Σ (⋆ ⇒ ⋆)%kind := λne A, lrel_auth_comp' A.
  Next Obligation. Admitted.

  Definition auth_ctx {Θ} (Δ : ctxO Σ Θ) := ext (ext Δ (lrel_auth authBaseN)) lrel_auth_comp.

  (* Lemma refines_auth_return Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆, var0 → var1 var0 ⟧ (auth_ctx Δ) p_return v_return i_return.
  Proof.
    iSplit; [|iSplit].
    { iIntros (A ???) "!# _"; rewrite -/interp.
      iIntros (????) "Hv Hi Htok".
      rewrite /p_return /v_return /i_return.
      wp_pures; v_pures; i_pures.
      iModIntro. iFrame.
      iSplit; [|iSplit].
      { iIntros (a1 a2 a3) "!# #HA"; rewrite -!/interp /=.
        iIntros (????) "Hv Hi Htok".
        wp_pures; v_pures; i_pures.
        iModIntro. iFrame. clear.
        iSplit; [|iSplit].
        { iIntros (?????????? Ψ) "!# (Htok & Hv & Hi & Hpw & Hvw & Hpr & %) HΨ".
          wp_pures; v_pures; i_pures.
          iModIntro. iApply "HΨ".
          iFrame "∗ #".
          iLeft. iFrame. done. }
        { iIntros (?????? Ψ) "!# (Htok & Hi & Hpw & Hpr & [%%]) HΨ".
          wp_pures; i_pures.
          iPoseProof (lc_zero) as ">Hlc".
          iModIntro. iApply "HΨ".
          iFrame "∗ #". iDestruct "HA" as "(_ & $ & _)". done. }
        { iIntros (??? Ψ) "!# (Htok & Hv & Hvw)".
          v_pures. iFrame.
          iModIntro. iLeft. iFrame. 
          iDestruct "HA" as "(_ & _ & $)". } } 
      { iIntros (a1 a3) "!# #HA"; rewrite -!/interp /=.
        iIntros (??) "[Hi Htok]".
        wp_pures; i_pures.
        iModIntro. iFrame. clear.
        iIntros (?????? Ψ) "!# (Htok & Hi & Hpw & Hpr & [%%]) HΨ".
        wp_pures; i_pures.
        iPoseProof (lc_zero) as ">Hlc".
        iModIntro. iApply "HΨ".
        iFrame "∗ #". done. }
      { iIntros (a2) "!# #HA"; rewrite -!/interp /=.
        iIntros (??) "Hv Htok".
        v_pures. iModIntro. iFrame. clear.
        iIntros (??? Ψ) "!# (Htok & Hv & Hvw)".
        v_pures. iFrame.
        iModIntro. iLeft. iFrame "∗ #". } }
    { iIntros (A ??) "!# _"; rewrite -!/interp /=.
      iIntros (??) "[Hi Htok]".
      rewrite /p_return /i_return.
      wp_pures; i_pures.
      iModIntro. iFrame. clear.
      iIntros (a1 a3) "!# #HA"; rewrite -!/interp /=.
      iIntros (??) "[Hi Htok]".
      wp_pures; i_pures.
      iModIntro. iFrame. clear.
      iIntros (?????? Ψ) "!# (Htok & Hi & Hpw & Hpr & [%%]) HΨ".
      wp_pures; i_pures.
      iPoseProof (lc_zero) as ">Hlc".
      iModIntro. iApply "HΨ". iFrame "∗ #". done. }
    { iIntros (A ?) "!# _"; rewrite -!/interp /=.
      iIntros (??) "Hv Htok".
      rewrite /v_return. v_pures.
      iModIntro. iFrame. clear.
      iIntros (a2) "!# #HA"; rewrite -!/interp /=.
      iIntros (??) "Hv Htok".
      v_pures. iModIntro. iFrame. clear.
      iIntros (??? Ψ) "!# (Htok & Hv & Hvw)".
      v_pures. iFrame.
      iModIntro. iLeft. iFrame "∗ #". }
  Qed.

  Lemma refines_auth_bind Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆; ⋆, var2 var1 → (var1 → var2 var0) → var2 var0 ⟧
      (auth_ctx Δ) p_bind v_bind i_bind.
  Proof.
    iSplit; [|iSplit].
    { iIntros (A ???) "!# _"; rewrite -/interp.
      iIntros (????) "Hv Hi Htok".
      rewrite /p_bind/v_bind/i_bind.
      wp_pures; v_pures; i_pures.
      iModIntro. iFrame. clear.
      iSplit; [|iSplit].
      { iIntros (B ???) "!# _"; rewrite -/interp.
        iIntros (????) "Hv Hi Htok".
        wp_pures; v_pures; i_pures.
        iModIntro. iFrame. clear.
        iSplit; [|iSplit].
        { iIntros (v1 v2 v3) "!# #HmA"; rewrite -!/interp.
          iIntros (????) "Hv Hi Htok /=".
          wp_pures; v_pures; i_pures.
          iModIntro. iFrame. clear.
          iSplit; [|iSplit].
          { iIntros (w1 w2 w3) "!# #HAmB".
            iIntros (????) "Hv Hi Htok".
            wp_pures; v_pures; i_pures.
            iModIntro. iFrame. clear.
            iSplit; [|iSplit].
            { iIntros (?????????? Ψ) "!# (Htok & Hv & Hi & Hpw & Hvw & Hpr & %) HΨ".
              wp_pures; v_pures; i_pures.
              
              wp_bind (v1 _); v_bind (v2 _); i_bind (v3 _).
              iDestruct "HmA" as "(HmA & _)".
              wp_apply ("HmA" with "[$Htok $Hv $Hi $Hpw $Hvw $Hpr //]").
              iIntros (ps1' w1' a1 a3) "(Htok & Hi & Hpr & Hv) /=".
              iDestruct "Hv" as 
                "[(%&%&%&% &% &#HA & Hpw & Hv & Hvw)|
                  (#HAb & Hpw)]".
              { wp_pures. v_pures. 
                iDestruct "HAmB" as "(HAmB & _)".
                wp_bind (w1 a1); v_bind (w2 a2); i_bind (w3 a3).
                iSpecialize ("HAmB" with "HA Hv Hi Htok").
                wp_apply (wp_wand with "HAmB").
                iIntros (?) "(% & % & Hv & Hi & #HmB & Htok) /=".
                
                iDestruct "HmB" as "(HmB & _)".
                wp_apply ("HmB" with "[$Htok $Hv $Hi $Hpw $Hvw $Hpr]"); first admit.
                iIntros (ps1'' w1'' a1' a3') "(Htok & Hi & Hpr & Hv)".
                iDestruct "Hv" as 
                "[(%&%&%&% &% &#HB & Hpw & Hv & Hvw)|
                  (#HAb & Hpw)]".
                { iApply "HΨ". iFrame "∗ #".
                  iLeft. iFrame. admit. }
                { iApply "HΨ". iFrame "∗ #". } }

              { iDestruct "HAmB" as "(_ & HAmBb & HAmBu)".
                wp_pures. wp_bind (w1 a1); i_bind (w3 a3).
                iSpecialize ("HAmBb" with "HAb [$Hi $Htok]").
                wp_apply (wp_wand with "HAmBb").
                iIntros (?) "(% & Hi & #HmBb & Htok) /=".

                wp_apply ("HmBb" with "[$Htok $Hi $Hpw $Hpr]"); first admit.
                iIntros (ps1'' ? w1'' a1' a3') "(Hpr & %& Htok & Hpw & Hi & #HBb) /=".
                iApply "HΨ". iFrame.
                iRight. iFrame "∗ #". } }
              
            { iIntros (?????? Ψ) "!# (Htok & Hi & Hpw & Hpr & [%%]) HΨ".
              wp_pures; i_pures.
              
              wp_bind (v1 _); i_bind (v3 _).
              iDestruct "HmA" as "(_ & HmA & _)".
              wp_apply ("HmA" with "[$Htok $Hi $Hpw $Hpr]"); eauto.
              iIntros (? ? w1' a1 a3) "(Hpr & %& Htok & Hpw & Hi & #HA) /=".
              wp_pures.

              iDestruct "HAmB" as "(_ & HAmBb & _)".
              wp_bind (w1 a1); i_bind (w3 a3).
              iSpecialize ("HAmBb" with "HA [$Hi $Htok]").
              wp_apply (wp_wand with "HAmBb").
              iIntros (?) "(% & Hi & #HmBb & Htok) /=".

              wp_apply ("HmBb" with "[$Htok $Hi $Hpw $Hpr]"); eauto. }
            { iIntros (??? Ψ) "!# (Htok & Hv & Hvw)".
              v_pures.
              
              v_bind (v2 _).
              iDestruct "HmA" as "(_ & _ & HmA)".
              iMod ("HmA" with "[$Htok $Hv $Hvw]") as "(Htok & Hv) /=".

              iDestruct "Hv" as "[(%&%&%& Hvw & Hv & #HA)|Hv]"; v_pures.
              { iDestruct "HAmB" as "(_ & _ & HAmB)".
                v_bind (w2 a2).
                iMod ("HAmB" with "HA Hv Htok") as (?) "(Hv & #HmB & Htok) /=".
                
                iMod ("HmB" with "[$Htok $Hv $Hvw]") as "($ & Hv)".
                
                iDestruct "Hv" as "[(%&%&%& Hvw & Hv & #HAu')|Hv]".
                { iLeft. by iFrame. }
                { by iRight. } }
              { by iFrame. } } }
          
          { iIntros (w1 w3) "!# #HAmB".
            iIntros (??) "[Hi Htok]".
            wp_pures; i_pures.
            iModIntro. iFrame. clear.

            iIntros (?????? Ψ) "!# (Htok & Hi & Hpw & Hpr & [%%]) HΨ".
            wp_pures; i_pures.
            
            wp_bind (v1 _); i_bind (v3 _).
            iDestruct "HmA" as "(_ & HmA & _)".
            wp_apply ("HmA" with "[$Htok $Hi $Hpw $Hpr]"); eauto.
            iIntros (? ? w1' a1 a3) "(Hpr &% & Htok & Hpw & Hi & HA) /=".
            wp_pures.

            wp_bind (w1 a1); i_bind (w3 a3).
            iSpecialize ("HAmB" with "HA [$Hi $Htok]").
            wp_apply (wp_wand with "HAmB").
            iIntros (?) "(% & Hi & #HmBb & Htok) /=".

            wp_apply ("HmBb" with "[$Htok $Hi $Hpw $Hpr]"); eauto. }

          { iIntros (w2) "!# #HAmb".
            iIntros (??) "Hv Htok".
            v_pures. iModIntro. iFrame. clear.
            
            iIntros (??? Ψ) "!# (Htok & Hv & Hvw)".
            v_pures.
            
            v_bind (v2 _).
            iDestruct "HmA" as "(_ & _ & HmA)".
            iMod ("HmA" with "[$Htok $Hv $Hvw]") as "(Htok & Hv) /=".

            iDestruct "Hv" as "[(%&%&%& Hvw & Hv & #HA)|Hv]"; v_pures.
            { v_bind (w2 a2).
              iMod ("HAmb" with "HA Hv Htok") as (?) "(Hv & #HmB & Htok) /=".
              
              iMod ("HmB" with "[$Htok $Hv $Hvw]") as "($ & Hv)".
              
              iDestruct "Hv" as "[(%&%&%& Hvw & Hv & #HAu')|Hv]".
              { iLeft. by iFrame. }
              { by iRight. } }
            { by iFrame. } } }
       
        { iIntros (v1 v3) "!# #HmA"; rewrite -!/interp.
          iIntros (??) "[Hi Htok] /=".
          wp_pures; i_pures.
          iModIntro. iFrame. clear.
          
          iIntros (w1 w3) "!# #HAmB".
          iIntros (??) "[Hi Htok]".
          wp_pures; i_pures.
          iModIntro. iFrame. clear.

          iIntros (?????? Ψ) "!# (Htok & Hi & Hpw & Hpr & [%%]) HΨ".
          wp_pures; i_pures.
          
          wp_bind (v1 _); i_bind (v3 _).
          wp_apply ("HmA" with "[$Htok $Hi $Hpw $Hpr]"); eauto.
          iIntros (? ? w1' a1 a3) "(Hpr &% & Htok & Hpw & Hi & HA) /=".
          wp_pures.

          wp_bind (w1 a1); i_bind (w3 a3).
          iSpecialize ("HAmB" with "HA [$Hi $Htok]").
          wp_apply (wp_wand with "HAmB").
          iIntros (?) "(% & Hi & #HmBb & Htok) /=".

          wp_apply ("HmBb" with "[$Htok $Hi $Hpw $Hpr]"); eauto. }

        { iIntros (v2) "!# #HmA"; rewrite -!/interp.
          iIntros (??) "Hv Htok /=".
          v_pures. iModIntro. iFrame. clear.

          iIntros (w2) "!# #HAmb".
          iIntros (??) "Hv Htok".
          v_pures. iModIntro. iFrame. clear.
          
          iIntros (??? Ψ) "!# (Htok & Hv & Hvw)".
          v_pures.
          
          v_bind (v2 _).
          iMod ("HmA" with "[$Htok $Hv $Hvw]") as "(Htok & Hv) /=".

          iDestruct "Hv" as "[(%&%&%& Hvw & Hv & #HA)|Hv]"; v_pures.
          { v_bind (w2 a2).
            iMod ("HAmb" with "HA Hv Htok") as (?) "(Hv & #HmB & Htok) /=".
            
            iMod ("HmB" with "[$Htok $Hv $Hvw]") as "($ & Hv)".
            
            iDestruct "Hv" as "[(%&%&%& Hvw & Hv & #HAu')|Hv]".
            { iLeft. by iFrame. }
            { by iRight. } }
          { by iFrame. } } }
      
      { iIntros (B ??) "!# _"; rewrite -/interp.
        iIntros (??) "[Hi Htok]".
        wp_pures; i_pures.
        iModIntro. iFrame. clear.
        
        iIntros (v1 v3) "!# #HmA"; rewrite -!/interp.
        iIntros (??) "[Hi Htok] /=".
        wp_pures; i_pures.
        iModIntro. iFrame. clear.
        
        iIntros (w1 w3) "!# #HAmB".
        iIntros (??) "[Hi Htok]".
        wp_pures; i_pures.
        iModIntro. iFrame. clear.

        iIntros (?????? Ψ) "!# (Htok & Hi & Hpw & Hpr & [%%]) HΨ".
        wp_pures; i_pures.
        
        wp_bind (v1 _); i_bind (v3 _).
        wp_apply ("HmA" with "[$Htok $Hi $Hpw $Hpr]"); eauto.
        iIntros (? ? w1' a1 a3) "(Hpr &% & Htok & Hpw & Hi & HA) /=".
        wp_pures.

        wp_bind (w1 a1); i_bind (w3 a3).
        iSpecialize ("HAmB" with "HA [$Hi $Htok]").
        wp_apply (wp_wand with "HAmB").
        iIntros (?) "(% & Hi & #HmBb & Htok) /=".

        wp_apply ("HmBb" with "[$Htok $Hi $Hpw $Hpr]"); eauto. }

      { iIntros (B ?) "!# _"; rewrite -/interp.
        iIntros (??) "Hv Htok".
        v_pures. iModIntro. iFrame. clear.
        
        iIntros (v2) "!# #HmA"; rewrite -!/interp.
        iIntros (??) "Hv Htok /=".
        v_pures. iModIntro. iFrame. clear.

        iIntros (w2) "!# #HAmb".
        iIntros (??) "Hv Htok".
        v_pures. iModIntro. iFrame. clear.
        
        iIntros (??? Ψ) "!# (Htok & Hv & Hvw)".
        v_pures.
        
        v_bind (v2 _).
        iMod ("HmA" with "[$Htok $Hv $Hvw]") as "(Htok & Hv) /=".

        iDestruct "Hv" as "[(%&%&%& Hvw & Hv & #HA)|Hv]"; v_pures.
        { v_bind (w2 a2).
          iMod ("HAmb" with "HA Hv Htok") as (?) "(Hv & #HmB & Htok) /=".
          
          iMod ("HmB" with "[$Htok $Hv $Hvw]") as "($ & Hv)".
          
          iDestruct "Hv" as "[(%&%&%& Hvw & Hv & #HAu')|Hv]".
          { iLeft. by iFrame. }
          { by iRight. } }
        { by iFrame. } } }
    
    { iIntros (A ??) "!# _"; rewrite -/interp.
      iIntros (??) "[Hi Htok]".
      rewrite /p_bind/i_bind.
      wp_pures; i_pures.
      iModIntro. iFrame. clear.
      
      iIntros (B ??) "!# _"; rewrite -/interp.
      iIntros (??) "[Hi Htok]".
      wp_pures; i_pures.
      iModIntro. iFrame. clear.
      
      iIntros (v1 v3) "!# #HmA"; rewrite -!/interp.
      iIntros (??) "[Hi Htok] /=".
      wp_pures; i_pures.
      iModIntro. iFrame. clear.
      
      iIntros (w1 w3) "!# #HAmB".
      iIntros (??) "[Hi Htok]".
      wp_pures; i_pures.
      iModIntro. iFrame. clear.

      iIntros (?????? Ψ) "!# (Htok & Hi & Hpw & Hpr & [%%]) HΨ".
      wp_pures; i_pures.
      
      wp_bind (v1 _); i_bind (v3 _).
      wp_apply ("HmA" with "[$Htok $Hi $Hpw $Hpr]"); eauto.
      iIntros (? ? w1' a1 a3) "(Hpr &% & Htok & Hpw & Hi & HA) /=".
      wp_pures.

      wp_bind (w1 a1); i_bind (w3 a3).
      iSpecialize ("HAmB" with "HA [$Hi $Htok]").
      wp_apply (wp_wand with "HAmB").
      iIntros (?) "(% & Hi & #HmBb & Htok) /=".

      wp_apply ("HmBb" with "[$Htok $Hi $Hpw $Hpr]"); eauto. }

    { iIntros (A ?) "!# _"; rewrite -/interp.
      iIntros (??) "Hv Htok".
      rewrite /v_bind. v_pures.
      iModIntro. iFrame. clear.
      
      iIntros (B ?) "!# _"; rewrite -/interp.
      iIntros (??) "Hv Htok".
      v_pures. iModIntro. iFrame. clear.
      
      iIntros (v2) "!# #HmA"; rewrite -!/interp.
      iIntros (??) "Hv Htok /=".
      v_pures. iModIntro. iFrame. clear.

      iIntros (w2) "!# #HAmb".
      iIntros (??) "Hv Htok".
      v_pures. iModIntro. iFrame. clear.
      
      iIntros (??? Ψ) "!# (Htok & Hv & Hvw)".
      v_pures.
      
      v_bind (v2 _).
      iMod ("HmA" with "[$Htok $Hv $Hvw]") as "(Htok & Hv) /=".

      iDestruct "Hv" as "[(%&%&%& Hvw & Hv & #HA)|Hv]"; v_pures.
      { v_bind (w2 a2).
        iMod ("HAmb" with "HA Hv Htok") as (?) "(Hv & #HmB & Htok) /=".
        
        iMod ("HmB" with "[$Htok $Hv $Hvw]") as "($ & Hv)".
        
        iDestruct "Hv" as "[(%&%&%& Hvw & Hv & #HAu')|Hv]".
        { iLeft. by iFrame. }
        { by iRight. } }
      { by iFrame. } }
  Admitted. *)

  Lemma refines_auth_unauth Θ (Δ : ctxO Σ Θ) c :
    inv_v_susp_table c
    ⊢ REL p_unauth << v_unauth #c << i_unauth :
      ⟦ ∀: ⋆, var1 var0 → var3 var0 → var2 var0 ⟧
      (ext (auth_ctx Δ) (lrel_evidence authBaseN)).
  Proof.
    iIntros "#Htab" (????) "Hv Hi Htok".
    rewrite /p_unauth /v_unauth /i_unauth.
    v_pures; wp_pures.
    iModIntro. iFrame. clear.
    iSplit; [|iSplit]; interp_unfold!; last first.
    { (* unary  *) admit. }
    { (* binary *) admit. }
    iIntros (????) "!# _"; rewrite -!/interp.
    iIntros (????) "Hv Hi Htok".
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iSplit; [|iSplit]; interp_unfold!; last first.
    { (* unary  *) admit. }
    { (* binary *) admit. }
    iIntros (???) "!#"; rewrite -!/interp.
    interp_unfold!.
    rewrite interp_var0_ext1 interp_var1_ext2.
    iDestruct 1 as "(#Hevi & #Hevi_bi & #Hevi_un)".
    iDestruct "Hevi" as (tA ???? ??? -> ->) "#(_ & Hpunserspec & Hpserspec & Hpsuspspec & Hpunsuspspec & Hvserspec & _ & Hvdeserspec & Hvcountspec)".
    iIntros (????) "Hv Hi Htok".
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iSplit; [|iSplit]; interp_unfold!; last first.
    { (* unary  *) admit. }
    { (* binary *) admit. }
    iIntros (???) "!# #Hauth".
    iIntros (????) "Hv Hi Htok".
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iSplit; [|iSplit]; interp_unfold!; last first.
    { (* unary  *) admit. }
    { (* binary *) admit. }
    rewrite interp_var0_ext1 interp_var2_ext3.
    iIntros (??????????? Ψ) "!# (Htok & Hv & Hi & Hid & Hpw & Hvw & Hpr & %) HΨ".
    interp_unfold! in "Hauth".
    rewrite interp_var3_ext4 interp_var0_ext1.
    iDestruct "Hauth" as "(Hauth & _ & _)".
    iDestruct "Hauth" as (tA' ? a1 a2 un_a1 s [-> ?]) "(Hpserp & #HA & Hpauth & Hvauth & Hsusplb)".
    iDestruct "Hpw" as (???? ->) "(Hbuf & % & %)".
    iDestruct "Hvw" as (? ->) "%Hvprf".
    iDestruct "Hpauth" as (??? ->) "Hinv_fill".
    v_pures; i_pures; wp_pures.
    iDestruct "Hinv_fill" as "[Hinv_fill|Hinv_unfill]".
    - iMod (na_inv_acc with "Hinv_fill Htok") as "(>Hinvo & Htok & Hclose_inv)"; try solve_ndisj.
      iDestruct "Hinvo" as "[Hlb [(% & Hlr & [Hbrproph %Hin])|[Hlr Hbrproph]]]"; wp_load; wp_pures.
      + wp_apply (wp_resolve_proph_bool with "Hbrproph").
        iIntros (?) "[% Hbrproph]". 
        simplify_eq. simpl in Hin.
        exfalso. apply Hin. eauto.
      + wp_apply ("Hpsuspspec" with "[$HA $Hpserp //]").
        iIntros (?) "[#HA' [Hpserp' [% #Hpserr]]]". 
        wp_pures.
        
        iMod ("Hclose_inv" with "[$Htok $Hlb Hlr Hbrproph]") as "Htok".
        { iNext. iRight. iFrame. }

        destruct ps2; simplify_eq; v_bind (list_head _).
        { iMod (gwp_list_head ⊤ _ [] () (λ v, ⌜v = NONEV⌝)%I
              with "[] [] [$Hv //]") as (?) "[Hv ->] /="; [done| |v_pures].
          { iIntros "!>" (? [[] | (?&?&?&?)]); simplify_eq. eauto. }

          (* What should the postcondition be in lrel_auth_comp when the list is short? *)
          admit. }

        iMod (gwp_list_head ⊤ _ (s0 :: ps2) () (λ v, ⌜v = SOMEV #s0⌝)%I
              with "[] [] [$Hv //]") as (?) "[Hv ->] /="; [done| |v_pures].
        { iIntros "!>" (? [[] | (?&?&?&?)]); simplify_eq. eauto. }

        destruct (decide (s0 = s')); last first.
        { wp_bind (p_finish _ _).

          iApply (p_finish_spec_bad' p_ser_susp v' s0 with "[//]").
          iNext. iIntros (p_finish) "Hpfinish". wp_pures.
          simplify_eq.

          wp_apply (gwp_list_cons _); [done|].
          iIntros (??). wp_pures.
          
          iApply ("HΨ"). iFrame "Htok Hi Hpr".
          iModIntro. iRight.
          iDestruct "HA'" as "(_ & $ & _)".
          iExists (reverse (ps2)).
          instantiate (1 := s0 :: ps1).
          iSplit; first admit.
          iExists prf1, v. iFrame "%".
          iSplit; eauto.
          iFrame "Hpfinish Hpserspec Hpserr".
          iExists [], (combine bufl ps1), p_finish, s0.
          iSplit; eauto. }

        wp_bind (p_finish _ _).

        iApply (p_finish_spec' p_ser_susp v' s'); try done.
        iNext. iIntros (p_finish) "Hpfinish". wp_pures.

        wp_apply (gwp_list_cons _); [done|].
        iIntros (??). 
        wp_pure credit:"Hlc".
        wp_pure credit:"Hlctab".
        wp_pures.

        iPoseProof (big_sepL_cons (λ _ buf, p_buffer_elem buf) 
            with "[$Hbuf $Hpfinish $Hpserspec $Hpserr //]")
          as "Hbuf".

        iMod (na_inv_acc with "Htab Htok") as "(Htabo & Htok & Hclose_tab)"; try solve_ndisj.
        iMod (lc_fupd_elim_later with "Hlctab Htabo") as "Htabo".
        iDestruct "Htabo" as "(%&%&%&% & Hl & %Hm & Hbigsep & Hmauth & Hid' & %Hidinv)".

        iPoseProof (id_agree with "Hid Hid'") as (->) "[Hid Hid']".
        iMod (id_update ctr (ctr+1) (ltac:(lia)) with "Hid Hid'") as "[Hid Hid']".

        v_bind (v_deser _). subst s0.
        iMod ("Hvdeserspec" with "Hv") as (?) "(Hv & Hvdeserparspec) /=".
        v_bind (v_deser_par _).
        iMod ("Hvdeserparspec" with "HA' Hpserr Hpserp' Hv Hmauth") as "Hv".
        iDestruct "Hv" as "(%&%&%& Hmauth & Hv & Hc & %Hmautheq & #HA'' & #Hvserp) /=".

        v_pures. v_bind (v_count _).
        iDestruct "Hc" as "(Hcfrag & % & Hc & Hcagg)".
        iMod ("Hvcountspec" with "Hc Hv") as "[Hc Hv] /=". v_pures.

        v_bind (v_finish _ _ _ _).
        iMod (v_finish_spec with "Htab Hv") as (v_finish) "[Hvfinish Hv] /=".
        v_pures; try solve_vals_compare_safe.

        case_bool_decide; simplify_eq; v_pures.
        * v_bind (v_finish _).
          assert (c0 = 0) as -> by lia.

          destruct! Hmautheq; simplify_eq.

          iMod ("Hclose_tab" with "[$Htok $Hl $Hbigsep $Hmauth $Hid']") as "Htok";
            try (iNext; iFrame "%"; iPureIntro; intros ??; apply Hidinv; lia).

          iMod ("Hvfinish" $! ⊤ with "[//] Hlc Htok Hvserp Hvserspec Hc Hvauth Hv")
            as "[Hv Htok] /=". v_pures.

          v_bind (list_tail _).
          iMod (gwp_list_tail ⊤ _ (s' :: _) () (λ v, ⌜is_proof _ ps2⌝)%I
                with "[] [] [$Hv //]") as (u) "[Hv %Hvprf'] /="; [done| |v_pures].
          { by iIntros "!>" (?). }

          iApply ("HΨ"). iFrame "Htok Hpr Hi".
          iModIntro. iLeft.
          iExists ps2. iFrame "HA'' Hv Hid".
          iSplit.
          { iPureIntro.
            instantiate (1 := (s' :: ps1)).
            admit. }
          iSplit.
          { iPoseProof (big_sepL_cons (λ _, p_buffer_elem) with "Hbuf") as "Hbuf". 
            assert 
              (((p_finish, s') :: combine bufl ps1) = 
                combine (p_finish :: bufl) (s' :: ps1))
              as -> by done.
            iFrame "Hbuf". iExists prf1. eauto. }

          iPureIntro.
          eexists _. split; eauto.
          repeat f_equal. lia.

        * destruct! Hmautheq; simplify_eq.
        
          v_load. v_pures. v_bind (map.map_insert _ _ _).
          iMod (gwp_map_insert #ctr _ _ _ () ⊤ _
            (λ d, ⌜is_map d (<[ #ctr := _ ]> m)⌝)%I
            with "[//] [] [$Hv //]") as (?) "[Hv %Hmins] /=".
          { by iIntros "!#" (? Hins). }
          Unshelve. 2: done.
          
          v_store.

          iMod ("Hclose_tab" with "[$Hl Hbigsep $Htok Hvfinish $Hmauth $Hid' Hc Hcagg Hcfrag Hlc]") as "Htok".
          { iNext. iFrame "%".

            iPoseProof (big_sepM_mono 
                (v_susp_big_sep_lam m m')
                (v_susp_big_sep_lam (<[#ctr:=(#c0, v_finish)%V]> m) (mapg_insert_def m' #ctr a2')) 
              with "Hbigsep") as "Hbigsep".
            { iIntros (?? Hlook) "Hbigsep".
              rewrite /v_susp_big_sep_lam.
              iDestruct "Hbigsep" as (??????????[?[?[??]]]) "($ & $ & $ & $)".
              iExists q. iPureIntro.
              do 2 (split; eauto).
              rewrite lookup_insert_ne; eauto.
              intros ?. simplify_eq.
              specialize (Hidinv id ltac:(lia)).
              simplify_eq. }

            iSplitL.
            { iApply (big_sepM_insert_2 with "[Hvfinish Hc Hcagg Hcfrag Hlc]").
              { iFrame "∗ #". iExists 1%Qp.
                iPureIntro. do 2 ( split; try lia).
                split; eauto.
                by rewrite lookup_insert. }
              iFrame. }

            iPureIntro. intros ??.
            rewrite lookup_insert_None.
            specialize (Hidinv ctr' ltac:(lia)).
            split; eauto. intros ?. simplify_eq. lia. }

          v_pures. v_bind (list_tail _).
          iMod (gwp_list_tail ⊤ _ (s' :: _) () (λ v, ⌜is_proof _ ps2⌝)%I
                with "[] [] [$Hv //]") as (u) "[Hv %Hprf'] /="; [done| |].
          { by iIntros "!>" (?). }
          v_pures.

          iApply "HΨ". iModIntro. iFrame "Htok Hi Hpr".
          iLeft. iFrame "Hv Hid HA''".
          iExists ps2. iSplit; first admit.
          iSplit; last first.
          { iPureIntro. eexists _. 
            split; eauto. repeat f_equal. lia. }

          iExists _.
          iPoseProof (big_sepL_cons (λ _, p_buffer_elem) with "Hbuf") as "Hbuf". 
          assert 
            (((p_finish, s') :: combine bufl ps1) = 
              combine (p_finish :: bufl) (s' :: ps1))
            as -> by done.
          iFrame "Hbuf". iExists v, ps'. by iFrame "%".

    - iMod (na_inv_acc with "Hinv_unfill Htok") as "(>Hinvo & Htok & Hclose_inv)"; try solve_ndisj.
      iDestruct "Hinvo" as (?) "(Hmfrag & 
            [(%& Hlb & Hlr & Hprbr & Hone)|
              (%&%&%& Hlb & Hlr & Hprbr & Hone)])";
        wp_load; wp_pures; last first.
      + destruct r; wp_pures.
        * 
          

          






    v_pures; i_pures; wp_pures.

    Print auth_p.

    v_bind (list_head _).
    iMod (gwp_list_head ⊤ _ (s' :: vs') () (λ v, ⌜v = SOMEV #s'⌝)%I
           with "[] [] [$Hv //]") as (?) "[Hv ->] /="; [done| |].
    { iIntros "!>" (? [[] | (?&?&?&?)]); simplify_eq. eauto. }


    wp_apply "Hser"; [done|].
    iIntros (s') "(%Hs' & #Hser' & #Hdeser)".
    wp_pures.
    wp_apply (wp_resolve_proph_string with "Hproph").
    iIntros (vs') "[-> Hproph]".

    wp_seq.
    wp_apply (gwp_list_cons s'); [done|].
    iIntros (??). wp_pures.
    v_bind (list_head _).
    iMod (gwp_list_head ⊤ _ (s' :: vs') () (λ v, ⌜v = SOMEV #s'⌝)%I
           with "[] [] [$Hv //]") as (?) "[Hv ->] /="; [done| |].
    { iIntros "!>" (? [[] | (?&?&?&?)]); simplify_eq. eauto. }
    v_pures.

    v_bind (Hash _).
    iMod (step_verifier_hash with "Hv") as "Hv /="; [done|].
    v_pures.
    { (* TODO: why does this case fail??? *) solve_vals_compare_safe. }

    pose proof (evi_type_ser_inj_str _ _ _ _ _ Hs2 Hs'). subst.
    iEval (rewrite bool_decide_eq_true_2 //) in "Hv".
    v_pures.

    v_bind (v_deser _).
    iMod ("Hdeser" with "[$Hv //]") as "Hv /=".
    v_pures.
    v_bind (list_tail _).
    iMod (gwp_list_tail ⊤ _ (s' :: _) () (λ v, ⌜is_proof _ vs'⌝)%I
           with "[] [] [$Hv //]") as (u) "[Hv %Hprf'] /="; [done| |].
    { by iIntros "!>" (?). }
    v_pures.

    apply is_list_inject in Hprf' as ->.
    iModIntro. iApply ("HΨ" $! (s' :: ps) vs').
    iFrame.
    iFrame "# ∗". iPureIntro.
    rewrite reverse_cons -assoc /=.
    split; [done|].
    split; [done|].
    by apply is_list_inject.
  Qed.

  Lemma refines_Authenticatable Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ Authenticatable ⟧ (auth_ctx Δ) p_Authenticable v_Authenticable i_Authenticable.
  Proof.
    iExists lrel_evidence; rewrite -/interp.
    iExists  _, _, _, _, _, _; rewrite -/interp.
    do 3 (iSplit; [done|]).
    iSplit; last first.
    { iApply refines_auth_unauth. }
    iExists _, _, _, _, _, _; rewrite -/interp.
    do 3 (iSplit; [done|]).
    iSplit; last first.
    { iApply refines_auth_auth. }
    iExists _, _, _, _, _, _; rewrite -!/interp.
    do 3 (iSplit; [done|]).
    iSplit; last first.
    { iApply refines_Auth_int. }
    iExists _, _, _, _, _, _; rewrite -!/interp.
    do 3 (iSplit; [done|]).
    iSplit; last first.
    { iApply refines_Auth_string. }
    iExists _, _, _, _, _, _; rewrite -!/interp.
    do 3 (iSplit; [done|]).
    iSplit; last first.
    { iApply refines_Auth_sum. }
    iExists _, _, _, _, _, _; rewrite -!/interp.
    do 3 (iSplit; [done|]).
    iSplit; last first.
    { iApply refines_Auth_pair. }
    iExists _, _, _, _, _, _; rewrite -!/interp.
    do 3 (iSplit; [done|]).
    iSplit; last first.
    { iApply refines_Auth_mu. }
    iApply refines_Auth_auth.
  Qed.

  Lemma refines_authentikit_func Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ Authentikit_func var1 var0 ⟧ (auth_ctx Δ) p_Authentikit v_Authentikit i_Authentikit.
  Proof.
    iExists _, _, _, _, _, _; rewrite -!/interp.
    do 3 (iSplit; [done|]).
    iSplit; last first.
    { iApply refines_Authenticatable. }
    iExists _, _, _, _, _, _; rewrite -/interp.
    do 3 (iSplit; [done|]).
    iSplit; [iApply refines_auth_return|].
    iApply refines_auth_bind.
  Qed.

  Lemma refines_authentikit Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ Authentikit ⟧ Δ p_Authentikit v_Authentikit i_Authentikit.
  Proof.
    iExists lrel_auth, lrel_auth_comp; rewrite -3!/interp.
    iApply refines_authentikit_func.
  Qed.

  Definition rel_authentikit_output (A : lrel Σ) (prf : val) (ps : list string) : lrel Σ :=
    LRel (λ v1 v2 v3, ∃ a1 a2 a3, ⌜v1 = (prf, a1)%V⌝ ∗ ⌜v2 = SOMEV a2⌝ ∗ ⌜v3 = a3⌝ ∗ A a1 a2 a3)%I.

  Lemma refines_run Θ (Δ : ctxO Σ Θ) (p : proph_id) ps (c1 c2 c3 : expr) w A :
    is_proph_proof w p ps -∗
    (REL c1 << c2 << c3 : lrel_auth_comp A) -∗
    REL p_run #~ #p c1 << v_run #~ c2 w << i_run #~ c3 : rel_authentikit_output A w ps.
  Proof.
    iIntros "[%Hprf Hproph] Hc" (????) "Hv Hi".
    rewrite /v_run /i_run /p_run.
    v_bind c2; i_bind c3; wp_bind (c1).

    iSpecialize ("Hc" with "Hv Hi").
    wp_apply (wp_wand with "Hc").
    iIntros (f1) "(%f2 & %f3 & Hv & Hi & Hc) /=".
    wp_pures; v_pures; i_pures.
    v_bind (f2 _).
    apply is_list_inject in Hprf as ->.
    iDestruct "Hproph" as (us) "[Hproph %Hps]".

    wp_apply ("Hc" $! _ _ _ _ _ [] ps with "[$Hproph $Hv $Hi]").
    { iSplit; [done|]. iPureIntro. split; [|done]. by apply is_list_inject. }
    iIntros (ps1 ps2 w1 w2 a1 a2 a3) "(%Heq & %Hprf1 & [% Hp] & Hv & Hi & HA) /=".
    v_pures.
    wp_pures.
    wp_apply (wp_resolve_proph_nil with "Hp"); iIntros (->).
    wp_pures.
    iFrame.
    wp_apply gwp_list_rev.
    { done. }
    iIntros (? Hv).
    wp_pures.
    rewrite reverse_nil app_nil_r /= in Heq.
    rewrite Heq.
    apply is_list_inject in Hv as ->.
    by iFrame.
  Qed.

  Lemma refines_instantiate (c1 c2 c3 : expr) (τ : type _ ⋆) :
    (REL c1 << c2 << c3 : ⟦ ∀: ⋆ ⇒ ⋆; ⋆ ⇒ ⋆, Authentikit_func var1 var0 → var0 τ ⟧ ∅) -∗
    REL c1 #~ #~ p_Authentikit
     << c2 #~ #~ v_Authentikit
     << c3 #~ #~ i_Authentikit : lrel_auth_comp (⟦ τ ⟧ (auth_ctx ∅)).
  Proof.
    iIntros "Hc" (????) "Hv Hi".
    wp_bind c1; v_bind c2; i_bind c3.
    iSpecialize ("Hc" with "Hv Hi").
    wp_apply (wp_wand with "Hc").
    iIntros (v1) "(%v2 & %v3 & Hv & Hi & Hcnt)".
    iSpecialize ("Hcnt" $! lrel_auth with "[//]"); rewrite -/interp.
    v_bind (v2 _); i_bind (v3 _).
    iSpecialize ("Hcnt" with "Hv Hi").
    wp_apply (wp_wand with "Hcnt").
    iIntros (v1') "(%v2' & %v3' & Hv & Hi & Hcnt)".
    iSpecialize ("Hcnt" $! lrel_auth_comp with "[//]"); rewrite -/interp.
    v_bind (v2' _); i_bind (v3' _).
    iSpecialize ("Hcnt" with "Hv Hi").
    wp_apply (wp_wand with "Hcnt").
    iIntros (v1'') "(%v2'' & %v3'' & Hv & Hi & Hcnt)".
    v_bind (v2'' _); i_bind (v3'' _).
    iSpecialize ("Hcnt" with "[] Hv Hi"); rewrite -!/interp.
    { iApply refines_authentikit_func. }
    wp_apply (wp_wand with "Hcnt").
    iIntros (v1''') "(%v2''' & %v3''' & Hv & Hi & Hcnt)".
    iFrame.
  Qed.

End proof.

Theorem authentikit_correctness Σ `{authPreG Σ}
  (A : ∀ `{authG Σ}, lrel Σ) (φ : val → val → val → Prop) (cₚ cᵥ cᵢ : expr) (σ : state) (p : proph_id) :
  p ∈ σ.(used_proph_id) →
  (∀ `{authG Σ}, ∀ vₚ vᵥ vᵢ, A vₚ vᵥ vᵢ -∗ ⌜φ vₚ vᵥ vᵢ⌝) →
  (∀ `{authG Σ}, ⊢ REL cₚ << cᵥ << cᵢ : lrel_auth_comp A) →
  adequate hash_collision NotStuck (p_run #~ #p cₚ) σ
    (λ vₚ σₚ, ∃ thpᵥ thpᵢ σᵥ σᵢ a1 a2 a3 prf,
        (** The prover outputs a proof [prf] and [a1]  *)
        vₚ = (prf, a1)%V ∧
        (** there exists a valid verifier execution with the prover's proof [prf] returning [a2] *)
        rtc erased_step ([v_run #~ cᵥ prf], σ) (of_val (SOMEV a2) :: thpᵥ, σᵥ) ∧
        (** and a valid ideal execution returning [a3] *)
        rtc erased_step ([i_run #~ cᵢ], σ) (of_val a3 :: thpᵢ, σᵢ) ∧
        (** [φ] holds *)
        φ a1 a2 a3).
Proof.
  intros Hp HA Hcomp.
  eapply (heap_adequacy_strong_proph Σ _ (λ p, p_run #~ #p cₚ)); [done|].
  clear p Hp.
  iIntros (Hinv p pvs) "_ Hp".
  iAssert (∃ v ps, ⌜is_proof v ps⌝ ∗ proph_proof p ps)%I
    with "[Hp]" as (v ps) "[% Hproph]".
  { rewrite /proph_proof /=. iFrame.
    iExists _, _. rewrite /is_proof is_list_inject //. }

  iMod (cfg_alloc (v_run #~ cᵥ v) σ) as (Hcfgᵥ) "[Hauthᵥ Heᵥ]".
  iMod (cfg_alloc (i_run #~ cᵢ) σ) as (Hcfgᵢ) "[Hauthᵢ Heᵢ]".
  set (Hcfg := AuthG _ _ Hcfgᵥ Hcfgᵢ).
  iMod (inv_alloc specN _ (spec_inv _ _) with "[Hauthᵥ Hauthᵢ]") as "#Hcfg".
  { iNext. iExists _, _, _, _. iFrame "# ∗ %". eauto. }
  iAssert (spec_ctx) as "#Hctx"; [by iExists _, _|].

  wp_apply wp_fupd.
  wp_apply (wp_wand with "[-]").
  { iPoseProof (refines_run _ ∅ with "[$Hproph //] []") as "Hrun"; [iApply Hcomp|].
    wp_apply ("Hrun" $! [] _ [] with "[$Heᵥ $Hctx] [$Heᵢ $Hctx]"). }

  iIntros (w) "(% & % & [_ Hv] & [_ Hi] & Hout)".
  iDestruct "Hout" as (??? -> -> ->) "HA".
  iDestruct (HA with "HA") as %Hφ.

  iInv specN as (tpᵥ σᵥ tpᵢ σᵢ) ">(Hauthᵥ & Hauthᵢ & %Hexecᵥ & %Hexecᵢ)" "Hclose".
  iDestruct (cfg_auth_tpool_agree with "Hauthᵥ Hv") as %?.
  iDestruct (cfg_auth_tpool_agree with "Hauthᵢ Hi") as %?.
  destruct tpᵥ as [|? tpᵥ]; [simplify_eq/=|].
  destruct tpᵢ as [|? tpᵢ]; [simplify_eq/=|].
  iMod ("Hclose" with "[-]") as "_".
  { iFrame "∗ % #". }
  iModIntro.
  simplify_list_eq.
  iIntros (σₚ ???) "(?&?&?&?) !%".
  do 8 eexists. eauto.
Qed.

Theorem authentikit_correctness_syntactic (c : expr) (σ : state) (τ : type _ ⋆) (p : proph_id) :
  p ∈ σ.(used_proph_id) →
  EqType τ →
  ε |ₜ ∅ ⊢ₜ c : (∀: ⋆ ⇒ ⋆; ⋆ ⇒ ⋆, Authentikit_func var1 var0 → var0 τ) →
  adequate hash_collision NotStuck (p_run #~ #p (c #~ #~ p_Authentikit)) σ
    (λ vₚ σₚ, ∃ thpᵥ thpᵢ σᵥ σᵢ a prf,
        (** The prover outputs a proof [prf] and [a]  *)
        vₚ = (prf, a)%V ∧
        (** there exists a valid verifier execution with the prover's proof [prf] returning [a] *)
        rtc erased_step ([v_run #~ (c #~ #~ v_Authentikit) prf], σ) (of_val (SOMEV a) :: thpᵥ, σᵥ) ∧
        (** and a valid ideal execution returning [a] *)
        rtc erased_step ([i_run #~ (c #~ #~ i_Authentikit)], σ) (of_val a :: thpᵢ, σᵢ)).
Proof.
  intros Hp Hτ Htyped.
  set (φ := λ (v1 v2 v3 : val), v1 = v2 ∧ v2 = v3).
  set (c1 := (c #~ #~ p_Authentikit)).
  set (c2 := (c #~ #~ v_Authentikit)).
  set (c3 := (c #~ #~ i_Authentikit)).
  suff: (adequate hash_collision NotStuck (p_run #~ #p c1) σ
          (λ vₚ σₚ, ∃ thpᵥ thpᵢ σᵥ σᵢ a1 a2 a3 prf,
              vₚ = (prf, a1)%V ∧
              rtc erased_step ([v_run #~ c2 prf], σ) (of_val (SOMEV a2) :: thpᵥ, σᵥ) ∧
              rtc erased_step ([i_run #~ c3], σ) (of_val a3 :: thpᵢ, σᵢ) ∧
              φ a1 a2 a3)).
  { intros []. split; [|done]. intros ?????.
    edestruct adequate_result as (?&?&?&?&?&?&?&?&?&?&?&?&?); [done|done|].
    simplify_eq. do 6 eexists. eauto. }
  apply (authentikit_correctness authΣ (λ a, ⟦ τ ⟧ (auth_ctx ∅))); [done| |].
  { iIntros (????) "Hτ". by iDestruct (eq_type_sound with "Hτ") as %[]. }
  iIntros (?).
  iApply refines_instantiate.
  by iApply refines_typed.
Qed.
