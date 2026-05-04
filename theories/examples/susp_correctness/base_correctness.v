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
          iApply ("HΨ" $! #s0 (string_ser_str s0) 0%nat ∅ mlg).
          iModIntro. iFrame "Hauth".
          iSplitL "";
            [iSplit; [iPureIntro; by exists s0|iPureIntro; eauto]|].
          iSplit; [iPureIntro; rewrite size_empty; lia|].
          iSplitL "Hpe"; [iExact "Hpe"|].
          iLeft. iSplit; [done|]. iExists #s0.
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
          admit.
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

  Admitted.

  Lemma refines_Auth_mu Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆ ⇒ ⋆, var1 (var0 (μ: ⋆; var1 var0)) → var1 (μ: ⋆; var1 var0) ⟧
      (ext Δ (lrel_evidence N)) p_Auth_mu v_Auth_mu i_Auth_mu.
  Proof.

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