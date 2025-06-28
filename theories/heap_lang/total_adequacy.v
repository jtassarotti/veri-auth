From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import mono_nat.
From iris.program_logic Require Export total_adequacy.
From auth.heap_lang Require Export adequacy.
From auth.heap_lang Require Import proofmode notation.
From iris.prelude Require Import options.

Definition heap_total Σ `{!heapGpreS Σ} s e σ φ :
  (∀ `{!heapGS_gen HasNoLc Σ}, ⊢ inv_heap_inv -∗ WP e @ s; ⊤ [{ v, ⌜φ v⌝ }]) →
  sn erased_step ([e], σ).
Proof.
  intros Hwp; eapply (twp_total _ _); iIntros (?) "".
  iMod (gen_heap_init σ.(heap)) as (?) "[Hh _]".
  iMod (inv_heap_init loc (option val)) as (?) ">Hi".
  iMod (proph_map_init [] σ.(used_proph_id)) as (?) "Hp".
  iMod (mono_nat_own_alloc 0) as (γ) "[Hsteps _]".
  iDestruct (Hwp (HeapGS _ _ _ _ _ _ _ _) with "Hi") as "Hwp".
  iModIntro.
  iExists (λ σ ns κs nt, (gen_heap_interp σ.(heap) ∗
                          proph_map_interp κs σ.(used_proph_id) ∗
                          mono_nat_auth_own γ 1 ns))%I,
    id, (λ _, True%I), _.
  iFrame.
Qed.
