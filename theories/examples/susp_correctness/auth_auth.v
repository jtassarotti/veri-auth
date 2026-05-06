From auth.prelude Require Import stdpp.
From auth.rel_logic_tern_susp Require Import model interp spec_tactics.
From iris.algebra Require Import gset auth.
From auth.examples Require Import authentikit authenticatable_base_susp.
From auth.examples.susp_correctness Require Export definitions helpers.
From auth.examples.susp_correctness Require Import base_correctness.

Section authenticatable.
  Context `{!authG Σ, !seqG Σ, !visited_mapG Σ, !lg_mapG Σ, !mapG Σ, !capG Σ, !intransitG Σ, !stateG Σ}.

  Lemma refines_Auth_auth Θ (Δ : ctxO Σ Θ) (R : kindO Σ (⋆ ⇒ ⋆)) :
    ⊢ ⟦ ∀: ⋆, var1 (var3 var0) ⟧
      (auth_ctx Δ R) p_Auth_auth v_Auth_auth i_Auth_auth.
  Proof.
    iSplit; [|iSplit]; interp_unfold!; last first.
    { (* unary  *) admit. }
    { (* binary *) admit. }
    (* ternary *)
    iIntros (A v1 v2 v3) "!# _"; rewrite -/interp.
    iIntros (????) "Hv Hi Htok".
    rewrite /p_Auth_auth /v_Auth_auth /i_Auth_auth.
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame.
    (* Final 3-way split: prove only the ternary [lrel_tern_evidence]. *)
    iSplit; [|iSplit]; interp_unfold!; last first.
    { (* final unary  *) admit. }
    { (* final binary *) admit. }
    (* Ternary evidence for the auth. *)
    rewrite interp_var1_ext2.
    iExists tauth, _, _, _, _, _, _, _.
    iSplit; [done|]. iSplit; [done|].
    iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit]]]]]].
    - (* 0. invalid_val *)
      iIntros "!#" (p v2 v3) "#HA".
      iDestruct "HA" as (t v2' a1 a2 un_a1 s) "[_ [_ [_ Hpv]]]".
      iDestruct "Hpv" as (lb lr ps) "[%Heq _]". discriminate.
    - (* 1. unsusp_p_ser_spec *) admit.
    - (* 2. susp_p_ser_spec *) admit.
    - (* 3. suspend_v_deser_spec (combined) *) admit.
    - (* 4. unsuspend_spec *) admit.
    - (* 5. v_ser_spec *) admit.
    - (* 6. v_auth_ser_spec *) admit.
    - (* 7. v_count_spec *) admit.
  Admitted.

End authenticatable.
