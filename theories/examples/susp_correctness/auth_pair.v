From auth.prelude Require Import stdpp.
From auth.rel_logic_tern_susp Require Import model interp spec_tactics.
From iris.algebra Require Import gset auth.
From auth.examples Require Import authentikit authenticatable_base_susp.
From auth.examples.susp_correctness Require Export definitions helpers.

Section authenticatable.
  Context `{!authG Σ, !seqG Σ, !correctnessG Σ}.

  Local Typeclasses Opaque susp_p_ser_spec unsusp_p_ser_spec suspend_v_deser_spec
        unsuspend_spec v_ser_spec v_auth_ser_spec v_count_spec.

  Lemma refines_Auth_pair Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆; ⋆, var2 var1 → var2 var0 → var2 (var1 * var0) ⟧
      (ext Δ (lrel_evidence)) p_Auth_pair v_Auth_pair i_Auth_pair.
  Proof.
    iSplit; interp_unfold!; last first.
    { (* unary  *) admit. }
    (* ternary *)
    iIntros (A v1 v2 v3) "!# _"; rewrite -/interp.
    iIntros (????) "Hv Hi Htok".
    rewrite /p_Auth_pair /v_Auth_pair /i_Auth_pair.
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iSplit; interp_unfold!; last first.
    { (* inner-after-A unary *) admit. }
    iIntros (B w1 w2 w3) "!# _"; rewrite -/interp.
    iIntros (????) "Hv Hi Htok". v_pures; i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iSplit; interp_unfold!; last first.
    { (* inner-after-B unary *) admit. }
    iIntros (vA1 vA2 vA3) "!# #HA".
    interp_unfold! in "HA".
    iDestruct "HA" as "(HA_tern & #HA_un)".
    iDestruct "HA_tern" as (tA p_ssA p_usA p_spA p_uspA v_sA v_dA v_cA -> ->) "#HrestA".
    fold v_ser_spec.
    iIntros (????) "Hv Hi Htok". v_pures; i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iSplit; interp_unfold!; last first.
    { (* inner-after-HA unary *) admit. }
    iIntros (vB1 vB2 vB3) "!# #HB".
    interp_unfold! in "HB".
    iDestruct "HB" as "(HB_tern & #HB_un)".
    iDestruct "HB_tern" as (tB p_ssB p_usB p_spB p_uspB v_sB v_dB v_cB -> ->) "#HrestB".
    iIntros (????) "Hv Hi Htok".
    rewrite /prod_ser'' /prod_ser /prod_count.
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame.
    (* Final 3-way split: prove only the ternary [lrel_tern_evidence]. *)
    iSplit; interp_unfold!; last first.
    { (* final unary  *) admit. }
    (* Ternary evidence for the product. *)
    iExists (tprod tA tB), _, _, _, _, _, _, _.
    iSplit; [done|]. iSplit; [done|].
    (* Now destruct HrestA/HrestB for use in bullets — keep as SPATIAL
       (no [#] markers).  Each hypothesis's body is semantically
       persistent ([□(...)]), but introducing them as spatial keeps them
       out of Iris's intuitionistic-env traversal which is what the
       [Typeclasses Opaque] dance was previously avoiding. *)
    iDestruct "HrestA" as "(HusserA & HsserA & HsuspvdeserA & HunsuspA & HvserA & HvauthserA & HvcountA)".
    iDestruct "HrestB" as "(HusserB & HsserB & HsuspvdeserB & HunsuspB & HvserB & HvauthserB & HvcountB)".
    iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit]]]]].
    - (* 1. unsusp_p_ser_spec *)
      rewrite /unsusp_p_ser_spec.
      iIntros (v s Ψ) "!# Hser HΨ".
      iDestruct "Hser" as (a1 a2 sa sb [-> ->]) "[Hussera Husserb]".
      wp_pures.
      wp_apply ("HusserA" with "Hussera"). iIntros "_". wp_pures.
      wp_apply ("HusserB" with "Husserb"). iIntros "_". wp_pures.
      unfold prod_ser_str. iApply "HΨ". by iModIntro.
    - (* 2. susp_p_ser_spec *) admit.

    - (* 3. suspend_v_deser_spec (combined) *) admit.

    - (* 4. unsuspend_spec *) admit.

    - (* 5. v_ser_spec *)
      rewrite /v_ser_spec.
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
      rewrite /v_auth_ser_spec.
      iIntros (K tᵥ3 a1 a2 a3) "!# #HA Hv".
      rewrite /prod_ser''. v_pures.
      interp_unfold! in "HA".
      iDestruct "HA" as (??????) "(>-> & >-> & >-> & Ha & Hb)".
      v_pures. v_bind (v_sA _).
      iMod ("HvauthserA" with "Ha Hv") as (?) "[Hserav Hv] /=".
      v_pures. v_bind (v_sB _).
      iMod ("HvauthserB" with "Hb Hv") as (?) "[Hserbv Hv] /=".
      v_pures.
      iModIntro. iFrame.
      iSplit; eauto.
    - (* 7. v_count_spec *)
      rewrite /v_count_spec.
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

End authenticatable.
