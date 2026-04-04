From auth.heap_lang Require Import adequacy.
From auth.rel_logic_bin_susp Require Import model.
From iris.base_logic.lib Require Export na_invariants.

Lemma refines_adequate Σ `{authPreG Σ, na_invG Σ}
  (A : ∀ `{authG Σ, seqG Σ}, lrel Σ)
  (φ : val → val → Prop) (eᵥ eᵢ : expr) σ :
  (∀ `{authG Σ, seqG Σ}, ∀ vᵥ vᵢ, A vᵥ vᵢ -∗ ⌜φ vᵥ vᵢ⌝) →
  (∀ `{authG Σ, seqG Σ}, ⊢ REL eᵥ << eᵢ : A) →
  adequate hash_collision NotStuck eᵥ σ
    (λ vᵥ σᵥ, ∃ thpᵢ hᵢ vᵢ,
        rtc erased_step ([eᵢ], σ) (of_val vᵢ :: thpᵢ, hᵢ) ∧
        φ vᵥ vᵢ).
Proof.
  intros HA Hlog.
  eapply (heap_adequacy_strong Σ).
  iIntros (Hinv) "_".
  iMod (cfg_alloc eᵢ σ) as (Hcfgᵢ) "[Hauthᵢ Heᵢ]".
  set (Hcfg := AuthG _ _ Hcfgᵢ).
  iMod (inv_alloc specN _ (spec_inv ([eᵢ], σ)) with "[Hauthᵢ]") as "#Hcfg".
  { iNext. iExists _, _. iFrame "# ∗ %". eauto. }
  iAssert (spec_ctx) as "#Hctx"; [by iExists _|].
  iMod na_alloc as (np) "Htok".
  set (Hseq := Build_seqG _ _ np).
  iApply wp_fupd.
  wp_apply (wp_wand with "[-]").
  { iApply (Hlog _ Hseq $! [] _ with "[$Heᵢ $Hctx $Htok]"). }
  iIntros (v).
  iIntros "(%vᵢ & [_ Hi] & Hinterp & Htok) /=".
  iDestruct (HA with "Hinterp") as %Hφ.
  iInv specN as (tpᵢ σᵢ) ">(Hauthᵢ & %)" "Hclose".
  iDestruct (cfg_auth_tpool_agree with "Hauthᵢ Hi") as %?.
  destruct tpᵢ as [|? tpᵢ]; simplify_eq/=.
  iMod ("Hclose" with "[-]") as "_".
  { iExists (_ :: tpᵢ), σᵢ. iFrame "∗ % #". }
  iModIntro.
  iIntros (σᵥ ???) "(?&?&?&?& Hhashes)".
  iIntros "!%". do 4 eexists; eauto.
Qed.

Lemma refines_Some_adequate Σ `{authPreG Σ, na_invG Σ}
  (A : ∀ `{authG Σ, seqG Σ}, lrel Σ)
  (φ : val → val → Prop) (eᵥ eᵢ : expr) σ :
  (∀ `{authG Σ, seqG Σ}, ∀ vᵥ vᵢ, A vᵥ vᵢ -∗ ⌜φ vᵥ vᵢ⌝) →
  (∀ `{authG Σ, seqG Σ}, ⊢ refines_Some ⊤ eᵥ eᵢ A) →
  adequate hash_collision NotStuck eᵥ σ
    (λ vᵥ σᵥ, ∃ thpᵢ hᵢ vᵢ o,
        vᵥ = $ o ∧
        if o is Some wᵥ then
          rtc erased_step ([eᵢ], σ) (of_val vᵢ :: thpᵢ, hᵢ) ∧
            φ wᵥ vᵢ
        else True).
Proof.
  intros HA Hlog.
  eapply (heap_adequacy_strong Σ).
  iIntros (Hinv) "_".
  iMod (cfg_alloc eᵢ σ) as (Hcfgᵢ) "[Hauthᵢ Heᵢ]".
  set (Hcfg := AuthG _ _ Hcfgᵢ).
  iMod (inv_alloc specN _ (spec_inv ([eᵢ], σ)) with "[Hauthᵢ]") as "#Hcfg".
  { iNext. iExists _, _. iFrame "# ∗ %". eauto. }
  iAssert (spec_ctx) as "#Hctx"; [by iExists _|].
  iMod na_alloc as (np) "Htok".
  set (Hseq := Build_seqG _ _ np).
  iApply wp_fupd. iApply wp_wand_r.
  iSplitL.
  { iApply (Hlog _ Hseq $! [] _ with "[$Heᵢ $Hctx $Htok]"). }
  iIntros (v).
  iIntros "(%o & -> & Ho)".
  destruct o; last first.
  { iIntros "!#" (????) "_". by iExists inhabitant, inhabitant, inhabitant, None. }
  iDestruct "Ho" as "(Htok & %vᵢ & [_ Hi] & Hinterp) /=".
  iDestruct (HA with "Hinterp") as %Hφ.
  iInv specN as (tpᵢ σᵢ) ">(Hauthᵢ & %)" "Hclose".
  iDestruct (cfg_auth_tpool_agree with "Hauthᵢ Hi") as %?.
  destruct tpᵢ as [|? tpᵢ]; simplify_eq/=.
  iMod ("Hclose" with "[-]") as "_".
  { iExists (_ :: tpᵢ), σᵢ. iFrame "∗ % #". }
  iModIntro.
  iIntros (σᵥ ???) "(?&?&?&?& Hhashes)".
  iIntros "!%". do 3 eexists; eexists (Some _). eauto.
Qed.

Lemma refines_un_adequate Σ `{authPreG Σ, na_invG Σ}
  (A : ∀ `{authG Σ, seqG Σ}, lrel_un Σ)
  (φ : val → Prop) (eᵥ : expr) σ :
  (∀ `{authG Σ, seqG Σ}, ∀ vᵥ, A vᵥ -∗ ⌜φ vᵥ⌝) →
  (∀ `{authG Σ, seqG Σ}, ⊢ refines_un ⊤ eᵥ A) →
  adequate hash_collision NotStuck eᵥ σ (λ vᵥ σᵥ, φ vᵥ).
Proof.
  intros HA Hlog.
  eapply (heap_adequacy_strong Σ).
  iIntros (Hinv) "_".
  iMod (cfg_alloc eᵥ σ) as (Hcfgᵢ) "_".
  set (Hcfg := AuthG _ _ Hcfgᵢ).
  iMod na_alloc as (np) "Htok".
  set (Hseq := Build_seqG _ _ np).
  iApply wp_fupd. iApply wp_wand_r.
  iSplitL.
  { iApply (Hlog _ Hseq with "[$Htok]"). }
  iIntros (v).
  iIntros "(Hv & Htok)".
  iDestruct (HA with "Hv") as %Hφ.
  iModIntro.
  iIntros (σᵥ ???) "(?&?&?&?& _)".
  iIntros "!%". exact Hφ.
Qed.
