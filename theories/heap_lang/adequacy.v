From iris.algebra Require Import auth.
From iris.base_logic.lib Require Import mono_nat ghost_map.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Export weakestpre adequacy.
From auth.heap_lang Require Import proofmode notation.
From iris.prelude Require Import options.

Class heapGpreS Σ := HeapGpreS {
  #[global] heapGpreS_iris :: invGpreS Σ;
  #[global] heapGpreS_heap :: gen_heapGpreS loc (option val) Σ;
  #[global] heapGpreS_inv_heap :: inv_heapGpreS loc (option val) Σ;
  #[global] heapGpreS_proph :: proph_mapGpreS proph_id (val * val) Σ;
  #[global] heapGS_step_cnt :: mono_natG Σ;
}.

Definition heapΣ : gFunctors :=
  #[invΣ; gen_heapΣ loc (option val); inv_heapΣ loc (option val);
    proph_mapΣ proph_id (val * val); mono_natΣ].
Global Instance subG_heapGpreS {Σ} : subG heapΣ Σ → heapGpreS Σ.
Proof. solve_inG. Qed.

Lemma heap_adequacy_strong Σ `{!heapGpreS Σ} s e σ φ :
  (∀ `{!heapGS Σ}, ⊢ inv_heap_inv -∗
                     WP e @ s; ⊤ {{ v, ∀ σ n κ m, state_interp σ n κ m -∗ ⌜φ v σ⌝ }}) →
  adequate s e σ φ.
Proof.
  intros Hwp.
  apply adequate_alt; intros t2 σ2 [n [κs ?]]%erased_steps_nsteps.
  eapply (wp_strong_adequacy Σ _); [|done].
  iIntros (Hinv).
  iMod (gen_heap_init σ.(heap)) as (?) "[Hh _]".
  iMod (inv_heap_init loc (option val)) as (?) ">Hi".
  iMod (proph_map_init κs σ.(used_proph_id)) as (?) "Hp".
  iMod (mono_nat_own_alloc) as (γ) "[Hsteps _]".
  set (Hheap := (HeapGS _ _ _ _ _ _ γ _)).
  iDestruct (Hwp Hheap with "Hi") as "Hwp".
  iModIntro.
  iExists (λ σ ns κs nt, (gen_heap_interp σ.(heap) ∗
                          proph_map_interp κs σ.(used_proph_id) ∗
                          mono_nat_auth_own γ 1 ns))%I.
  iExists [(λ v, ∀ σ n κ m, state_interp σ n κ m -∗ ⌜φ v σ⌝)%I], (λ _, True)%I, _ => /=.
  iFrame.
  iIntros (es' t2' -> ? ?) "Hsi H _".
  iDestruct (big_sepL2_cons_inv_r with "H") as (e' ? ->) "[Hwp H]".
  iDestruct (big_sepL2_nil_inv_r with "H") as %->.
  iApply fupd_mask_intro_discard; [done|]. iSplit; [|done].
  iIntros (v2 t2'' [= -> <-]) "/=".
  iApply ("Hwp" $! _ _ _ n with "Hsi").
Qed.

Lemma heap_adequacy Σ `{!heapGpreS Σ} s e σ φ :
  (∀ `{!heapGS Σ}, ⊢ inv_heap_inv -∗ WP e @ s; ⊤ {{ v, ⌜φ v⌝ }}) →
  adequate s e σ (λ v _, φ v).
Proof.
  intros Hwp.
  eapply (heap_adequacy_strong Σ).
  iIntros (?) "?".
  iApply wp_mono; last first.
  { iApply (Hwp with "[$]"). }
  eauto.
Qed.

(** Should be generalizable to [[∗ set] p ∈ ps, proph p (proph_list_resolves pvs p)], but there's
    only little theory on [set_to_map] which makes this a bit cumbersome... *)
Lemma proph_map_init_global `{Countable P, !proph_mapGpreS P V Σ} pvs ps p :
  p ∈ ps →
  ⊢ |==> ∃ _ : proph_mapGS P V Σ, (proph_map_interp pvs ps) ∗ proph p (proph_list_resolves pvs p).
Proof.
  intros Hp.
  iMod (ghost_map_alloc {[ p := proph_list_resolves pvs p ]}) as (γ) "[Hh Hp]".
  setoid_rewrite big_sepM_singleton.
  iExists (ProphMapGS P V _ _ _ _ γ).
  rewrite proph_map.proph_unseal /proph_map.proph_def /=.
  iFrame.
  iModIntro.
  iPureIntro. split; [|set_solver].
  rewrite /proph_resolves_in_list map_Forall_singleton //.
Qed.

Lemma heap_adequacy_strong_proph Σ `{!heapGpreS Σ} s (e : proph_id → expr) σ φ p :
  p ∈ σ.(used_proph_id) →
  (∀ `{!heapGS Σ} p pvs,
      ⊢ inv_heap_inv -∗ proph p pvs -∗
        WP e p @ s; ⊤ {{ v, ∀ σ n κ m, state_interp σ n κ m -∗ ⌜φ v σ⌝ }}) →
  adequate s (e p) σ φ.
Proof.
  intros Hi Hwp.
  apply adequate_alt; intros t2 σ2 [n [κs ?]]%erased_steps_nsteps.
  eapply (wp_strong_adequacy Σ _); [|done].
  iIntros (Hinv).
  iMod (gen_heap_init σ.(heap)) as (?) "[Hh _]".
  iMod (inv_heap_init loc (option val)) as (?) ">Hi".
  iMod (proph_map_init_global κs σ.(used_proph_id) p) as (?) "[Hp Hproph]"; [done|].
  iMod (mono_nat_own_alloc) as (γ) "[Hsteps _]".
  set (Hheap := (HeapGS _ _ _ _ _ _ γ _)).
  iDestruct (Hwp Hheap with "Hi Hproph") as "Hwp".
  iModIntro.
  iExists (λ σ ns κs nt, (gen_heap_interp σ.(heap) ∗
                          proph_map_interp κs σ.(used_proph_id) ∗
                          mono_nat_auth_own γ 1 ns))%I.
  iExists [(λ v, ∀ σ n κ m, state_interp σ n κ m -∗ ⌜φ v σ⌝)%I], (λ _, True)%I, _ => /=.
  iFrame.
  iIntros (es' t2' -> ? ?) "Hsi H _".
  iDestruct (big_sepL2_cons_inv_r with "H") as (e' ? ->) "[Hwp H]".
  iDestruct (big_sepL2_nil_inv_r with "H") as %->.
  iApply fupd_mask_intro_discard; [done|]. iSplit; [|done].
  iIntros (v2 t2'' [= -> <-]) "/=".
  iApply ("Hwp" $! _ _ _ n with "Hsi").
Qed.
