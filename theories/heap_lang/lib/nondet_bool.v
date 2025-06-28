From iris.base_logic Require Export invariants.
From auth.program_logic_upto_bad Require Export weakestpre.
From auth.heap_lang Require Export lang proofmode_upto_bad notation.
From iris.prelude Require Import options.

Definition nondet_bool : val :=
  λ: <>, let: "l" := ref #true in Fork ("l" <- #false);; !"l".

Section proof.
  Context `{!heapGS Σ}.

  Lemma nondet_bool_spec : {{{ True }}} nondet_bool #() {{{ (b : bool), RET #b; True }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_lam. wp_alloc l as "Hl". wp_let.
    pose proof (nroot .@ "rnd") as rndN.
    iMod (inv_alloc rndN _ (∃ (b : bool), l ↦ #b)%I with "[Hl]") as "#Hinv";
      first by eauto.
    wp_apply wp_fork.
    - iInv rndN as (?) "?". wp_store; eauto.
    - wp_seq. iInv rndN as (?) "?". wp_load.
      iSplitR "HΦ"; first by eauto.
      by iApply "HΦ".
  Qed.

End proof.
