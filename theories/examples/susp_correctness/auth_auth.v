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
    - (* 2. susp_p_ser_spec *) admit.
    - (* 3. suspend_v_deser_spec (combined) *) admit.
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
