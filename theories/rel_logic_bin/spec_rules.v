From iris.algebra Require Import auth excl frac agree gmap list.
From iris.proofmode Require Import proofmode.
From auth.heap_lang Require Export lang notation tactics.
From auth.base_logic Require Export spec_ra.
From auth.rel_logic_bin Require Export model.
Import uPred.

Local Set Default Proof Using "Type".

Section rules.
  Context `{authG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val → iProp Σ.
  Implicit Types σ : state.
  Implicit Types e : expr.
  Implicit Types v : val.
  Implicit Types l : loc.

  Local Hint Resolve tpool_lookup : core.
  Local Hint Resolve tpool_lookup_Some : core.
  Local Hint Resolve to_tpool_insert : core.
  Local Hint Resolve to_tpool_insert' : core.
  Local Hint Resolve tpool_singleton_included : core.

  (** * Aux. lemmas *)
  Lemma step_insert K tp j e σ κ e' σ' efs :
    tp !! j = Some (fill K e) → base_step e σ κ e' σ' efs →
    erased_step (tp, σ) (<[j:=fill K e']> tp ++ efs, σ').
  Proof.
    intros. rewrite -(take_drop_middle tp j (fill K e)) //.
    rewrite insert_app_r_alt length_take_le ?Nat.sub_diag /=;
      eauto using lookup_lt_Some, Nat.lt_le_incl.
    rewrite -(assoc_L (++)) /=. eexists.
    eapply step_atomic; eauto. by apply: Ectx_step'.
  Qed.

  Lemma step_insert_no_fork K tp j e σ κ e' σ' :
    tp !! j = Some (fill K e) → base_step e σ κ e' σ' [] →
    erased_step (tp, σ) (<[j:=fill K e']> tp, σ').
  Proof. rewrite -(right_id_L [] (++) (<[_:=_]>_)). by apply step_insert. Qed.

  Lemma rtc_erase_step_PureExec (P : Prop) n e e' σ K j tp ρ :
    P →
    PureExec P n e e' →
    tp !! j = Some (fill K e) →
    rtc erased_step ρ (tp, σ) →
    rtc erased_step ρ (<[j:=fill K e']> tp, σ).
  Proof.
    intros HP Hex Htpj Hrtc.
    apply rtc_nsteps_1 in Hrtc as [m Hrtc].
    specialize (Hex HP). apply (rtc_nsteps_2 (m + n)).
    eapply nsteps_trans; eauto.
    revert e e' Htpj Hex.
    induction n => e e' Htpj Hex.
    - inversion Hex; subst.
      rewrite list_insert_id; eauto. econstructor.
    - apply nsteps_inv_r in Hex.
      destruct Hex as [z [Hex1 Hex2]].
      specialize (IHn _ _ Htpj Hex1).
      eapply nsteps_r; eauto.
      replace (<[j:=fill K e']> tp) with
          (<[j:=fill K e']> (<[j:=fill K z]> tp)); last first.
      { clear. revert tp; induction j; intros tp.
        - destruct tp; trivial.
        - destruct tp; simpl; auto. by rewrite IHj. }
      destruct Hex2 as [Hexs Hexd].
      specialize (Hexs σ). destruct Hexs as [e'' [σ' [efs Hexs]]].
      specialize (Hexd σ [] e'' σ' efs Hexs); destruct Hexd as [? [? [? ?]]];
        subst.
      inversion Hexs; simpl in *; subst.
      rewrite -!fill_app.
      eapply step_insert_no_fork; eauto.
      { apply list_lookup_insert. apply lookup_lt_is_Some; eauto. }
  Qed.

  (** * Ideal rules *)

  (** Pure reductions *)
  Lemma step_ideal_pure E j K e e' (P : Prop) n :
    P →
    PureExec P n e e' →
    nclose specN ⊆ E →
    spec_ideal j (fill K e) ⊢ |={E}=> spec_ideal j (fill K e').
  Proof.
    iIntros (HP Hex ?) "[#Hinv Hj]". iFrame "Hinv".
    iDestruct "Hinv" as (ρᵢ) "Hspec".
    iInv specN as (tpᵢ σᵢ) ">(Hi & %)" "Hclose".
    iDestruct (cfg_auth_tpool_agree with "Hi Hj") as %Htpj.
    iMod (cfg_auth_tpool_update with "Hi Hj") as "[Hi $]".
    iApply "Hclose". iNext.
    iFrame. iFrame "%".
    iPureIntro.
    by eapply (rtc_erase_step_PureExec P).
  Qed.

  (** Prophecy variables (no-ops) *)
  Lemma step_ideal_newproph E j K :
    nclose specN ⊆ E →
    spec_ideal j (fill K NewProph) ={E}=∗
    ∃ (p : proph_id), spec_ideal j (fill K #p).
  Proof.
    iIntros (?) "[#Hinv Hj]". iFrame "Hinv".
    iDestruct "Hinv" as (ρᵢ) "Hspec".
    iInv specN as (tpᵢ σᵢ) ">(Hi & %)" "Hclose".
    iDestruct (cfg_auth_tpool_agree with "Hi Hj") as %Htpj.
    destruct (exist_fresh (used_proph_id σᵢ)) as [p Hp].
    iExists p.
    iMod (cfg_auth_tpool_update with "Hi Hj") as "[Hi $]".
    iApply "Hclose". iNext. iExists _, (state_upd_used_proph_id ({[ p ]} ∪.) σᵢ).
    iFrame. iFrame "%".
    rewrite cfg_auth_prophs_update.
    iFrame. iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto. by econstructor.
  Qed.

  Lemma step_ideal_resolveproph E j K (p : proph_id) w :
    nclose specN ⊆ E →
    spec_ideal j (fill K (ResolveProph #p (of_val w))) ={E}=∗
    spec_ideal j (fill K #()).
  Proof.
    iIntros (?) "[#Hinv Hj]". iFrame "Hinv".
    iDestruct "Hinv" as (ρᵢ) "Hspec".
    iInv specN as (tpᵢ σᵢ) ">(Hi & %)" "Hclose".
    iDestruct (cfg_auth_tpool_agree with "Hi Hj") as %Htpj.
    iMod (cfg_auth_tpool_update with "Hi Hj") as "[Hi $]".
    iApply "Hclose". iNext.
    iFrame; iFrame "%". iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto. do 2 econstructor; eauto.
  Qed.

  (** Alloc, load, and store *)
  Lemma step_ideal_alloc E j K e v :
    IntoVal e v →
    nclose specN ⊆ E →
    spec_ideal j (fill K (ref e)) ⊢ |={E}=> ∃ l, spec_ideal j (fill K (#l)) ∗ l ↦ᵢ v.
  Proof.
    iIntros (<- ?) "[#Hinv Hj]". iFrame "Hinv".
    iDestruct "Hinv" as (ρᵢ) "Hspec".
    iInv specN as (tpᵢ σᵢ) ">(Hi & %)" "Hclose".
    iDestruct (cfg_auth_tpool_agree with "Hi Hj") as %Htpj.
    iMod (cfg_auth_heap_alloc with "Hi") as (l) "(% & Hi & $)".
    iMod (cfg_auth_tpool_update with "Hi Hj") as "[Hi $]".
    iApply "Hclose". iNext.
    iFrame; iFrame "%". iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto.
    rewrite -state_init_heap_singleton. eapply AllocNS; first by lia.
    intros. assert (i = 0) as -> by lia. by rewrite Loc.add_0.
  Qed.

  Lemma step_ideal_load E j K l dq v:
    nclose specN ⊆ E →
    spec_ideal j (fill K (!#l)) ∗ l ↦ᵢ{dq} v
    ⊢ |={E}=> spec_ideal j (fill K (of_val v)) ∗ l ↦ᵢ{dq} v.
  Proof.
    iIntros (?) "([#Hinv Hj] & Hl)". iFrame "Hinv".
    iDestruct "Hinv" as (ρᵢ) "Hspec".
    iInv specN as (tpᵢ σᵢ) ">(Hi & %)" "Hclose".
    iDestruct (cfg_auth_tpool_agree with "Hi Hj") as %Htpj.
    iDestruct (cfg_auth_heap_agree with "Hi Hl") as "%".
    iMod (cfg_auth_tpool_update with "Hi Hj") as "[Hi $]".
    iFrame "Hl". iApply "Hclose". iNext.
    iFrame; iFrame "%". iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto. econstructor; eauto.
  Qed.

  Lemma step_ideal_store E j K l v' e v:
    IntoVal e v →
    nclose specN ⊆ E →
    spec_ideal j (fill K (#l <- e)) ∗ l ↦ᵢ v'
    ⊢ |={E}=> spec_ideal j (fill K #()) ∗ l ↦ᵢ v.
  Proof.
    iIntros (<-?) "([#Hinv Hj] & Hl)". iFrame "Hinv".
    iDestruct "Hinv" as (ρᵢ) "Hspec".
    iInv specN as (tpᵢ σᵢ) ">(Hi & %)" "Hclose".
    iDestruct (cfg_auth_tpool_agree with "Hi Hj") as %Htpj.
    iDestruct (cfg_auth_heap_agree with "Hi Hl") as %?.
    iMod (cfg_auth_tpool_update with "Hi Hj") as "[Hi $]".
    iMod (cfg_auth_heap_update with "Hi Hl") as "[Hi $]".
    iApply "Hclose". iNext.
    iFrame; iFrame "%". iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto. econstructor; eauto.
  Qed.

  Lemma step_ideal_xchg E j K l e (v v' : val) :
    IntoVal e v →
    nclose specN ⊆ E →
    spec_ideal j (fill K (Xchg #l e)) ∗ l ↦ᵢ v'
    ⊢ |={E}=> spec_ideal j (fill K (of_val v')) ∗ l ↦ᵢ v.
  Proof.
    iIntros (<-?) "([#Hinv Hj] & Hl)". iFrame "Hinv".
    iDestruct "Hinv" as (ρᵢ) "Hspec".
    iInv specN as (tpᵢ σᵢ) ">(Hi & %)" "Hclose".
    iDestruct (cfg_auth_tpool_agree with "Hi Hj") as %Htpj.
    iDestruct (cfg_auth_heap_agree with "Hi Hl") as %?.
    iMod (cfg_auth_tpool_update with "Hi Hj") as "[Hi $]".
    iMod (cfg_auth_heap_update with "Hi Hl") as "[Hi $]".
    iApply "Hclose". iNext.
    iFrame; iFrame "%". iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto. econstructor; eauto.
  Qed.

  (** CmpXchg & FAA *)
  Lemma step_ideal_cmpxchg_fail E j K l dq v' e1 v1 e2 v2 :
    IntoVal e1 v1 →
    IntoVal e2 v2 →
    nclose specN ⊆ E →
    vals_compare_safe v' v1 →
    v' ≠ v1 →
    spec_ideal j (fill K (CmpXchg #l e1 e2)) ∗ l ↦ᵢ{dq} v'
    ⊢ |={E}=> spec_ideal j (fill K (v', #false)%V) ∗ l ↦ᵢ{dq} v'.
  Proof.
    iIntros (<-<-???) "([#Hinv Hj] & Hl)". iFrame "Hinv".
    iDestruct "Hinv" as (ρᵢ) "Hspec".
    iInv specN as (tpᵢ σᵢ) ">(Hi & %)" "Hclose".
    iDestruct (cfg_auth_tpool_agree with "Hi Hj") as %Htpj.
    iDestruct (cfg_auth_heap_agree with "Hi Hl") as "%".
    iMod (cfg_auth_tpool_update with "Hi Hj") as "[Hi $]".
    iFrame "Hl". iApply "Hclose". iNext.
    iFrame; iFrame "%". iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto. econstructor; eauto.
    case_bool_decide; eauto.
  Qed.

  Lemma step_ideal_cmpxchg_suc E j K l e1 v1 v1' e2 v2:
    IntoVal e1 v1 →
    IntoVal e2 v2 →
    nclose specN ⊆ E →
    vals_compare_safe v1' v1 →
    v1' = v1 →
    spec_ideal j (fill K (CmpXchg #l e1 e2)) ∗ l ↦ᵢ v1'
    ⊢ |={E}=> spec_ideal j (fill K (v1', #true)%V) ∗ l ↦ᵢ v2.
  Proof.
    iIntros (<-<-???) "([#Hinv Hj] & Hl)". iFrame "Hinv".
    iDestruct "Hinv" as (ρᵢ) "Hspec".
    iInv specN as (tpᵢ σᵢ) ">(Hi & %)" "Hclose".
    iDestruct (cfg_auth_tpool_agree with "Hi Hj") as %Htpj.
    iDestruct (cfg_auth_heap_agree with "Hi Hl") as %?.
    iMod (cfg_auth_tpool_update with "Hi Hj") as "[Hi $]".
    iMod (cfg_auth_heap_update with "Hi Hl") as "[Hi $]".
    iApply "Hclose". iNext.
    iFrame "∗ %". iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto. econstructor; eauto.
    case_bool_decide; done.
  Qed.

  Lemma step_ideal_faa E j K l e1 e2 (i1 i2 : Z) :
    IntoVal e1 #i2 →
    nclose specN ⊆ E →
    spec_ideal j (fill K (FAA #l e1)) ∗ l ↦ᵢ #i1
    ⊢ |={E}=> spec_ideal j (fill K #i1) ∗ l ↦ᵢ #(i1+i2).
  Proof.
    iIntros (<-?) "([#Hinv Hj] & Hl)". iFrame "Hinv".
    iDestruct "Hinv" as (ρᵢ) "Hspec".
    iInv specN as (tpᵢ σᵢ) ">(Hi & %)" "Hclose".
    iDestruct (cfg_auth_tpool_agree with "Hi Hj") as %Htpj.
    iDestruct (cfg_auth_heap_agree with "Hi Hl") as %?.
    iMod (cfg_auth_tpool_update with "Hi Hj") as "[Hi $]".
    iMod (cfg_auth_heap_update with "Hi Hl") as "[Hi $]".
    iApply "Hclose". iNext.
    iFrame; iFrame "%". iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto. econstructor; eauto.
  Qed.

  (** Fork *)
  Lemma step_ideal_fork E j K e :
    nclose specN ⊆ E →
    spec_ideal j (fill K (Fork e)) ⊢ |={E}=>
    ∃ j', spec_ideal j (fill K #()) ∗ j' ⤇ᵢ e.
  Proof.
    iIntros (?) "[#Hinv Hj]". iFrame "Hinv".
    iDestruct "Hinv" as (ρᵢ) "Hspec".
    iInv specN as (tpᵢ σᵢ) ">(Hi & %)" "Hclose".
    iDestruct (cfg_auth_tpool_agree with "Hi Hj") as %Htpj.
    iMod (cfg_auth_tpool_update with "Hi Hj") as "[Hi $]".
    iMod (cfg_auth_tpool_fork with "Hi") as "[Hi $]".
    iApply "Hclose". iNext.
    iFrame; iFrame "%". iPureIntro.
    eapply rtc_r, step_insert; eauto. econstructor; eauto.
  Qed.

  (** Hash *)
  Lemma step_ideal_hash E j K (s : string) :
    nclose specN ⊆ E →
    spec_ideal j (fill K (Hash #(LitString s)))
    ⊢ |={E}=> spec_ideal j (fill K #(LitString (hash s))).
  Proof.
    iIntros (?) "(#Hinv & Hj)". iFrame "Hinv".
    iDestruct "Hinv" as (ρᵢ) "Hspec".
    iInv specN as (tpᵢ σᵢ) ">(Hi & %)" "Hclose".
    iDestruct (cfg_auth_tpool_agree with "Hi Hj") as %Htpj.
    iMod (cfg_auth_tpool_update with "Hi Hj") as "[Hi $]".
    iMod (cfg_auth_hash_update _ _ s with "Hi") as "Hi".
    iApply "Hclose". iNext.
    iFrame; iFrame "%".
    iPureIntro.
    eapply rtc_r, step_insert_no_fork; eauto.
    econstructor.
  Qed.

End rules.

From auth.heap_lang Require Import gen_weakestpre.

Notation spec_wp :=
  (λ _ E e Ψ, ∀ j K ,
               ⌜nclose specN ⊆ E⌝ ∗ spec_ideal j (fill K e) ={E}=∗
               ∃ (v : val), spec_ideal j (fill K v) ∗ Ψ v)%I.

Lemma gwp_mixin_spec_ideal `{!authG Σ} :
  GenWpMixin (A := ()) false spec_wp (λ l dq v, l ↦ᵢ{dq} v)%I.
Proof.
  constructor; intros.
  - apply _.
  - by iIntros "H" (??) "[% $]".
  - iIntros "H" (??) "[% Hi]". iMod ("H" with "[$Hi //]") as (?) "[$ $]".
  - iIntros "H" (? K') "[% Hi]".
    rewrite fill_comp.
    iMod ("H" with "[$Hi //]") as (?) "[Hi Hcnt]".
    rewrite -fill_comp.
    by iMod ("Hcnt" with "[$Hi //]").
  - iIntros "H" (??) "[% Hi]".
    iMod (step_ideal_pure with "Hi") as "Hi"; [done|done|].
    by iMod ("H" with "[$Hi //]").
  - iIntros "H" (??) "[% Hi]".
    iMod (step_ideal_alloc with "Hi") as (l) "($ & Hl)"; [done|].
    by iApply "H".
  - iIntros "Hl H" (??) "[% [Hctx Hi]]".
    iMod (step_ideal_load with "[$Hl $Hctx $Hi]") as "($ & Hl)"; [done|].
    by iApply "H".
  - iIntros "Hl H" (??) "[% [Hctx Hi]]".
    iMod (step_ideal_store with "[$Hl $Hctx $Hi]") as "($ & Hl)"; [done|].
    by iApply "H".
Qed.

Canonical Structure gwp_spec_ideal `{!authG Σ} := Build_GenWp gwp_mixin_spec_ideal.
