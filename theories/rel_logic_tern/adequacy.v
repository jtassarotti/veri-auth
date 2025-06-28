From auth.heap_lang Require Import adequacy_upto_bad.
From auth.base_logic Require Import spec_ra.
From auth.rel_logic_tern Require Import model.

Lemma refines_adequate Σ `{authPreG Σ}
  (A : ∀ `{authG Σ}, lrel Σ)
  (φ : val → val → val → Prop) (eₚ eᵥ eᵢ : expr) σ :
  (∀ `{authG Σ}, ∀ vₚ vᵥ vᵢ, A vₚ vᵥ vᵢ -∗ ⌜φ vₚ vᵥ vᵢ⌝) →
  (∀ `{authG Σ}, ⊢ REL eₚ << eᵥ << eᵢ : A) →
  adequate hash_collision NotStuck eₚ σ
    (λ vₚ σₚ, ∃ thpᵥ thpᵢ σᵥ σᵢ vᵥ vᵢ,
        (** [φ] holds *)
        φ vₚ vᵥ vᵢ ∧
        (** there exists a valid verifier execution *)
        rtc erased_step ([eᵥ], σ) (of_val vᵥ :: thpᵥ, σᵥ) ∧
        (** and a valid ideal execution *)
        rtc erased_step ([eᵢ], σ) (of_val vᵢ :: thpᵢ, σᵢ)).
Proof.
  intros HA Hlog.
  eapply (heap_adequacy_strong Σ).
  iIntros (Hinv) "_".
  iMod (cfg_alloc eᵥ σ) as (Hcfgᵥ) "[Hauthᵥ Heᵥ]".
  iMod (cfg_alloc eᵢ σ) as (Hcfgᵢ) "[Hauthᵢ Heᵢ]".
  set (Hcfg := AuthG _ _ Hcfgᵥ Hcfgᵢ).
  iMod (inv_alloc specN _ (spec_inv ([eᵥ], σ) ([eᵢ], σ)) with "[Hauthᵥ Hauthᵢ]") as "#Hcfg".
  { iNext. iExists _, _, _, _. iFrame "# ∗ %". eauto. }
  iAssert (spec_ctx) as "#Hctx"; [by iExists _, _|].
  iApply wp_fupd. iApply wp_wand_r.
  iSplitL.
  { iApply (Hlog _ $! [] _ [] _ with "[$Heᵥ $Hctx] [$Heᵢ $Hctx]"). }
  iIntros (v).
  iIntros "(%vᵥ & %vᵢ & [_ Hp] & [_ Hi] & Hinterp) /=".
  iDestruct (HA with "Hinterp") as %Hφ.
  iInv specN as (tpᵥ σᵥ tpᵢ σᵢ) ">(Hauthᵥ & Hauthᵢ & %Hexecᵥ & %Hexecᵢ)" "Hclose".
  iDestruct (cfg_auth_tpool_agree with "Hauthᵥ Hp") as %?.
  iDestruct (cfg_auth_tpool_agree with "Hauthᵢ Hi") as %?.
  destruct tpᵥ as [|? tpᵥ]; simplify_eq/=.
  destruct tpᵢ as [|? tpᵢ]; simplify_eq/=.
  iMod ("Hclose" with "[-]") as "_".
  { iFrame "∗ % #". }
  iModIntro.
  iIntros (σₚ ???) "(?&?&?&?)".
  iIntros "!%". do 6 eexists; eauto.
Qed.
