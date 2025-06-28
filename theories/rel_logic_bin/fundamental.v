(** Compatibility lemmas for the logical relation *)
From auth.heap_lang Require Import proofmode_upto_bad.
From auth.rel_logic_bin Require Import model.
From auth.rel_logic_bin Require Export compatibility interp.
From iris.proofmode Require Export proofmode.

Section fundamental.
  Context `{authG Σ}.
  Hint Resolve to_of_val : core.

  Local Ltac intro_clause := progress (iIntros (vs) "#Hvs /=").
  Local Ltac intro_clause' := intro_clause; iIntros (??) "Hi".
  Local Ltac pures :=
    wp_pures; i_pures.

  Local Tactic Notation "rel_bind_ap" uconstr(e1) uconstr(e2) constr(IH) ident(v) ident(w) constr(H) :=
    wp_bind (subst_map _ e1); i_bind (subst_map _ e2);
    iSpecialize (IH with "[$] [$]");
    iApply wp_wand_r;
    iSplitL IH; [iApply IH|];
    iIntros (v); iDestruct 1 as (w) H; simpl.

  Lemma bin_log_related_var Θ Δ Γ x τ :
    Γ !! x = Some τ →
    ⊢ {Θ;Δ;Γ} ⊨ Var x ≤log≤ Var x : τ.
  Proof.
    iIntros (Hx). intro_clause. simpl.
    rewrite (env_ltyped_lookup _ vs x); last first.
    { rewrite lookup_fmap Hx //. }
    rewrite !lookup_fmap.
    iDestruct "Hvs" as (v1 v2 ->) "HA". simpl.
    iIntros (??) "Hi".
    wp_pures. by iFrame.
  Qed.

  Lemma bin_log_related_pair Θ Δ Γ e1 e2 e1' e2' τ1 τ2 :
    ({Θ;Δ;Γ} ⊨ e1 ≤log≤ e1' : τ1) -∗
    ({Θ;Δ;Γ} ⊨ e2 ≤log≤ e2' : τ2) -∗
    {Θ;Δ;Γ} ⊨ Pair e1 e2 ≤log≤ Pair e1' e2' : t_prod τ1 τ2.
  Proof.
    iIntros "IH1 IH2".
    intro_clause.
    rewrite interp_prod_unfold.
    iApply (refines_pair with "[IH1] [IH2]").
    - by iApply "IH1".
    - by iApply "IH2".
  Qed.

  Lemma bin_log_related_fst Θ Δ Γ e e' τ1 τ2 :
    ({Θ;Δ;Γ} ⊨ e ≤log≤ e' : τ1 * τ2) -∗
    {Θ;Δ;Γ} ⊨ Fst e ≤log≤ Fst e' : τ1.
  Proof.
    iIntros "IH".
    intro_clause'.
    rel_bind_ap e e' "IH" v u "(Hi & H)".
    iDestruct "H" as (??) "(% & % & % & % & IHw & IHw')". simplify_eq/=.
    pures. by iFrame.
  Qed.

  Lemma bin_log_related_snd Θ Δ Γ e e' τ1 τ2 :
    ({Θ;Δ;Γ} ⊨ e ≤log≤ e' : τ1 * τ2) -∗
    {Θ;Δ;Γ} ⊨ Snd e ≤log≤ Snd e' : τ2.
  Proof.
    iIntros "IH".
    intro_clause'.
    rel_bind_ap e e' "IH" v u "(Hi & H)".
    iDestruct "H" as (??) "(% & % & % & % & IHw & IHw')". simplify_eq/=.
    pures. by iFrame.
  Qed.

  Lemma bin_log_related_app Θ Δ Γ e1 e2 e1' e2' τ1 τ2 :
    ({Θ;Δ;Γ} ⊨ e1 ≤log≤ e1' : τ1 → τ2) -∗
    ({Θ;Δ;Γ} ⊨ e2 ≤log≤ e2' : τ1) -∗
    {Θ;Δ;Γ} ⊨ App e1 e2 ≤log≤ App e1' e2' :  τ2.
  Proof.
    iIntros "IH1 IH2".
    intro_clause.
    iApply (refines_app _ _ _ _ (⟦ τ1 ⟧ Δ) with "[IH1] [IH2]").
    - rewrite /bin_log_related. setoid_rewrite interp_arr_unfold.
      by iApply "IH1".
    - by iApply "IH2".
  Qed.

  Lemma bin_log_related_rec Θ Δ (Γ : stringmap (typ ⋆ Θ)) (f x : binder) (e e' : expr) τ1 τ2 :
    □ ({Θ;Δ;<[f:=t_arr τ1 τ2]>(<[x:=τ1]>Γ)} ⊨ e ≤log≤ e' : τ2) -∗
    {Θ;Δ;Γ} ⊨ Rec f x e ≤log≤ Rec f x e' : τ1 → τ2.
  Proof.
    iIntros "#Ht".
    intro_clause'.
    pures.
    iFrame. iModIntro. iLöb as "IH".
    clear.
    iIntros (v1 v2) "!# #Hτ1".
    iIntros (??) "Hi". pures.
    set (r := (RecV f x (subst_map (binder_delete x (binder_delete f (fst <$> vs))) e),
               RecV f x (subst_map (binder_delete x (binder_delete f (snd <$> vs))) e')) : val * val).
    set (vvs' := binder_insert f r (binder_insert x (v1,v2) vs)).
    iSpecialize ("Ht" $! vvs' with "[#]").
    { rewrite !binder_insert_fmap.
      iApply (env_ltyped_insert with "[IH]").
      - iApply "IH".
      - iApply (env_ltyped_insert with "Hτ1").
        by iFrame. }
    unfold vvs'.
    destruct x as [|x], f as [|f];
      rewrite /= ?fmap_insert ?subst_map_insert //;
        try by iApply ("Ht" with "[$]").
    destruct (decide (x = f)) as [->|]; iSimpl in "Ht".
    - rewrite !delete_insert_delete !subst_subst !delete_idemp.
      by iApply ("Ht" with "[$]").
    - rewrite !delete_insert_ne // subst_map_insert.
      rewrite !(subst_subst_ne _ x f) // !subst_map_insert.
      by iApply ("Ht" with "[$]").
  Qed.

  Lemma bin_log_related_fork Θ Δ Γ e e' :
    ({Θ;Δ;Γ} ⊨ e ≤log≤ e' : ()) -∗
    {Θ;Δ;Γ} ⊨ Fork e ≤log≤ Fork e' : ().
  Proof.
    iIntros "IH".
    intro_clause.
    rewrite /bin_log_related.
    setoid_rewrite interp_unit_unfold.
    iApply refines_fork.
    by iApply "IH".
  Qed.

  Lemma bin_log_related_tlam Θ (Δ : ctxO Σ Θ) Γ κ (e e' : expr) τ :
    (∀ (A : kindO Σ κ),
      □ ({(Θ ▹ κ); (ext Δ A); ⤉Γ} ⊨ e ≤log≤ e' : τ)) -∗
    {Θ;Δ;Γ} ⊨ (Λ: e) ≤log≤ (Λ: e') : ∀: κ, τ.
  Proof.
    iIntros "#IH".
    intro_clause'; fold kindO.
    pures. iFrame.
    iIntros "!#" (A) "!#".
    iIntros (v1 v2 _); simplify_eq.
    iIntros (??) "Hi".
    pures.
    iDestruct ("IH" $! A) as "#H".
    iApply ("H" with "[] Hi").
    rewrite -shift_env_eq //.
  Qed.

  Lemma bin_log_related_tapp' Θ Δ κ Γ e e' τ τ' :
    ({Θ;Δ;Γ} ⊨ e ≤log≤ e' : ∀: κ, τ) -∗
    {Θ;Δ;Γ} ⊨ e #~ ≤log≤ e' #~ : τ.[τ'/].
  Proof.
    iIntros "IH".
    intro_clause'.
    rel_bind_ap e e' "IH" v v' "(Hp & IH)"; fold kindO.
    iDestruct ("IH" $! (interp τ' Δ)) as "#IH".
    iSpecialize ("IH" with "[//]").
    simpl.
    rewrite subst_eq.
    iApply ("IH" with "[$]").
  Qed.

  Lemma bin_log_related_tapp Θ Δ κ (A : kindO Σ κ) Γ e e' τ :
    ({Θ;Δ;Γ} ⊨ e ≤log≤ e' : ∀: κ, τ) -∗
    {Θ ▹ κ; ext Δ A; ⤉Γ} ⊨ e #~ ≤log≤ e' #~ : τ.
  Proof.
    iIntros "IH". intro_clause'.
    rewrite -shift_env_eq.
    rel_bind_ap e e' "IH" v v' "(Hp & IH)"; fold kindO.
    iApply ("IH" $! _ #~ #~ with "[//] Hp").
  Qed.

  Lemma bin_log_related_seq Θ κ (A : kindO Σ κ) τ1 τ2 Δ Γ e1 e2 e1' e2' :
    ({Θ ▹ κ; ext Δ A; ⤉Γ} ⊨ e1 ≤log≤ e1' : τ1) -∗
    ({Θ;Δ;Γ} ⊨ e2 ≤log≤ e2' : τ2) -∗
    {Θ;Δ;Γ} ⊨ (e1;; e2) ≤log≤ (e1';; e2') : τ2.
  Proof.
    iIntros "He1 He2".
    intro_clause.
    iApply (refines_seq (interp τ1 (ext Δ A)) with "[He1]").
    - iApply ("He1" with "[Hvs]"). rewrite -shift_env_eq //.
    - by iApply "He2".
  Qed.

  Lemma bin_log_related_seq' Θ Δ Γ e1 e2 e1' e2' τ1 τ2 :
    ({Θ;Δ;Γ} ⊨ e1 ≤log≤ e1' : τ1) -∗
    ({Θ;Δ;Γ} ⊨ e2 ≤log≤ e2' : τ2) -∗
    {Θ;Δ;Γ} ⊨ (e1;; e2) ≤log≤ (e1';; e2') : τ2.
  Proof.
    iIntros "He1 He2".
    iApply (bin_log_related_seq _ ⋆ lrel_true (Core.shift τ1 : typ _ _) with "[He1] He2").
    intro_clause.
    rewrite -shift_env_eq -shift_eq.
    by iApply "He1".
  Qed.

  Lemma bin_log_related_injl Θ Δ Γ e e' τ1 τ2 :
    ({Θ;Δ;Γ} ⊨ e ≤log≤ e' : τ1) -∗
    {Θ;Δ;Γ} ⊨ InjL e ≤log≤ InjL e' : τ1 + τ2.
  Proof.
    iIntros "IH".
    intro_clause'.
    rel_bind_ap e e' "IH" v v' "(? & H)".
    pures. iFrame. iModIntro.
    iExists _, _. eauto.
  Qed.

  Lemma bin_log_related_injr Θ Δ Γ e e' τ1 τ2 :
    ({Θ;Δ;Γ} ⊨ e ≤log≤ e' : τ2) -∗
    {Θ;Δ;Γ} ⊨ InjR e ≤log≤ InjR e' : τ1 + τ2.
  Proof.
    iIntros "IH".
    intro_clause'.
    rel_bind_ap e e' "IH" v v' "(? & Hvv)".
    pures. iFrame. iModIntro.
    iExists _, _. eauto.
  Qed.

  Lemma bin_log_related_case Θ Δ Γ e0 e1 e2 e0' e1' e2' τ1 τ2 τ3 :
    ({Θ;Δ;Γ} ⊨ e0 ≤log≤ e0' : τ1 + τ2) -∗
    ({Θ;Δ;Γ} ⊨ e1 ≤log≤ e1' : τ1 → τ3) -∗
    ({Θ;Δ;Γ} ⊨ e2 ≤log≤ e2' : τ2 → τ3) -∗
    {Θ;Δ;Γ} ⊨ Case e0 e1 e2 ≤log≤ Case e0' e1' e2' : τ3.
  Proof.
    iIntros "IH1 IH2 IH3".
    intro_clause'.
    rel_bind_ap e0 e0' "IH1" v0 v0' "(Hi & IH1)".
    iDestruct "IH1" as (w w') "[(% & % & #Hw) | (% & % & #Hw)]";
      simplify_eq/=; pures.
    - iApply (bin_log_related_app _ Δ Γ _ w _ w'  with "IH2 [] Hvs Hi").
      iIntros (?) "?". iIntros (??) "Hi".
      wp_pures. by iFrame.
    - iApply (bin_log_related_app _ Δ Γ _ w _ w' with "IH3 [] Hvs Hi").
      iIntros (?) "?"; iIntros (??) "Hi".
      wp_pures. by iFrame.
  Qed.

  Lemma bin_log_related_if Θ Δ Γ e0 e1 e2 e0' e1' e2' τ :
    ({Θ;Δ;Γ} ⊨ e0 ≤log≤ e0' : t_bool) -∗
    ({Θ;Δ;Γ} ⊨ e1 ≤log≤ e1' : τ) -∗
    ({Θ;Δ;Γ} ⊨ e2 ≤log≤ e2' : τ) -∗
    {Θ;Δ;Γ} ⊨ If e0 e1 e2 ≤log≤ If e0' e1' e2' : τ.
  Proof.
    iIntros "IH1 IH2 IH3".
    intro_clause'.
    rel_bind_ap e0 e0' "IH1" v0 v0' "(Hi & IH1)".
    iDestruct "IH1" as ([]) "(% & %)"; simplify_eq/=; pures.
    - by iApply ("IH2" with "[$] [$]") .
    - by iApply ("IH3" with "[$] [$]") .
  Qed.

  Lemma bin_log_related_load Θ Δ Γ e e' τ :
    ({Θ;Δ;Γ} ⊨ e ≤log≤ e' : ref τ) -∗
    {Θ;Δ;Γ} ⊨ Load e ≤log≤ Load e' : τ.
  Proof.
    iIntros "IH".
    intro_clause.
    iApply refines_load.
    rewrite /bin_log_related. setoid_rewrite interp_ref_unfold.
    by iApply "IH".
  Qed.

  Lemma bin_log_related_store Θ Δ Γ e1 e2 e1' e2' τ :
    ({Θ;Δ;Γ} ⊨ e1 ≤log≤ e1' : ref τ) -∗
    ({Θ;Δ;Γ} ⊨ e2 ≤log≤ e2' : τ) -∗
    {Θ;Δ;Γ} ⊨ Store e1 e2 ≤log≤ Store e1' e2' : ().
  Proof.
    iIntros "IH1 IH2".
    intro_clause.
    rewrite /bin_log_related interp_unit_unfold.
    setoid_rewrite interp_ref_unfold.
    iApply (refines_store with "[IH1] [IH2]").
    - by iApply "IH1".
    - by iApply "IH2".
  Qed.

  Lemma bin_log_related_xchg Θ Δ Γ e1 e2 e1' e2' τ :
    ({Θ;Δ;Γ} ⊨ e1 ≤log≤ e1' : ref τ) -∗
    ({Θ;Δ;Γ} ⊨ e2 ≤log≤ e2' : τ) -∗
    {Θ;Δ;Γ} ⊨ Xchg e1 e2 ≤log≤ Xchg e1' e2' : τ.
  Proof.
    iIntros "IH1 IH2".
    intro_clause.
    rewrite /bin_log_related. setoid_rewrite interp_ref_unfold.
    iApply (refines_xchg with "[IH1] [IH2]").
    - by iApply "IH1".
    - by iApply "IH2".
  Qed.

  Lemma bin_log_related_FAA Θ Δ Γ e1 e2 e1' e2' :
    ({Θ;Δ;Γ} ⊨ e1 ≤log≤ e1' : ref t_nat) -∗
    ({Θ;Δ;Γ} ⊨ e2 ≤log≤ e2' : t_nat) -∗
    {Θ;Δ;Γ} ⊨ FAA e1 e2 ≤log≤ FAA e1' e2' : t_nat.
  Proof.
    iIntros "IH1 IH2".
    intro_clause'.
    rel_bind_ap e2 e2' "IH2" v2 v2' "(Hi & IH2)".
    rel_bind_ap e1 e1' "IH1" v1 v1' "(Hi & IH1)".
    rewrite interp_ref_unfold {1}interp_nat_unfold.
    iDestruct "IH1" as (l l') "(% & % & Hinv)"; simplify_eq/=.
    iDestruct "IH2" as (n) "(% & %)"; simplify_eq.
    setoid_rewrite interp_nat_unfold.
    iInv (authN .@ "ref" .@ (l,l')) as (v1 v1') ">(Hv1 & Hv2 & (% & % & %))" "Hclose".
    simplify_eq.
    i_faa. wp_faa.
    iMod ("Hclose" with "[$Hv1 $Hv2]") as "_"; [eauto|].
    iFrame. eauto.
  Qed.

  Lemma bin_log_related_CmpXchg_EqType Θ Δ Γ e1 e2 e3 e1' e2' e3' τ
    (HEqτ : EqType τ)
    (HUbτ : UnboxedType τ) :
    ({Θ;Δ;Γ} ⊨ e1 ≤log≤ e1' : ref τ) -∗
    ({Θ;Δ;Γ} ⊨ e2 ≤log≤ e2' : τ) -∗
    ({Θ;Δ;Γ} ⊨ e3 ≤log≤ e3' : τ) -∗
    {Θ;Δ;Γ} ⊨ CmpXchg e1 e2 e3 ≤log≤ CmpXchg e1' e2' e3' : τ * t_bool.
  Proof.
    iIntros "IH1 IH2 IH3".
    intro_clause'.
    rel_bind_ap e3 e3' "IH3" v3 v3' "(? & #IH3)".
    rel_bind_ap e2 e2' "IH2" v2 v2' "(? & #IH2)".
    rel_bind_ap e1 e1' "IH1" v1 v1' "(? & #IH1)".
    iDestruct "IH1" as (l l') "(% & % & Hinv)"; simplify_eq/=.
    iDestruct (unboxed_type_sound with "IH2") as "(% & %)"; try fast_done.
    iDestruct (eq_type_sound with "IH2") as "<-"; first fast_done.
    iDestruct (eq_type_sound with "IH3") as "<-"; first fast_done.
    iInv (authN .@ "ref" .@ (l,l')) as (v v') "(>Hv & >Hv' & #H)" "Hclose".
    destruct (decide (v = v2)) as [|Hneq]; subst.
    - wp_cmpxchg_suc.
      iDestruct (eq_type_sound with "H") as %<-; first fast_done.
      i_cmpxchg_suc.
      iMod ("Hclose" with "[$]") as "_".
      iFrame.
      iExists _, _, _, _. do 3 (iSplitL; [done|]).
      iExists _. eauto.
    - wp_cmpxchg_fail.
      iDestruct (eq_type_sound with "H") as %<-; first fast_done.
      i_cmpxchg_fail.
      iMod ("Hclose" with "[$]") as "_".
      iFrame.
      iExists _, _, _, _. do 3 (iSplitL; [done|]).
      iExists _. eauto.
  Qed.

  Lemma bin_log_related_CmpXchg Θ Δ Γ e1 e2 e3 e1' e2' e3' τ
    (HUbτ : UnboxedType τ) :
    ({Θ;Δ;Γ} ⊨ e1 ≤log≤ e1' : ref τ) -∗
    ({Θ;Δ;Γ} ⊨ e2 ≤log≤ e2' : τ) -∗
    ({Θ;Δ;Γ} ⊨ e3 ≤log≤ e3' : τ) -∗
    {Θ;Δ;Γ} ⊨ CmpXchg e1 e2 e3 ≤log≤ CmpXchg e1' e2' e3' :  τ * t_bool.
  Proof.
    cut (EqType τ ∨ ∃ τ', τ = t_ref τ').
    { intros [Hτ | [τ' ->]].
      - by iApply bin_log_related_CmpXchg_EqType.
      - iIntros "H1 H2 H3". intro_clause.
        iSpecialize ("H1" with "Hvs").
        iSpecialize ("H2" with "Hvs").
        iSpecialize ("H3" with "Hvs").
        rewrite interp_unseal.
        iApply (refines_cmpxchg_ref with "H1 H2 H3"). }
    by apply unboxed_type_ref_or_eqtype.
  Qed.

  Lemma bin_log_related_alloc Θ Δ Γ e e' τ :
    ({Θ;Δ;Γ} ⊨ e ≤log≤ e' : τ) -∗
    {Θ;Δ;Γ} ⊨ Alloc e ≤log≤ Alloc e' : ref τ.
  Proof.
    iIntros "IH".
    intro_clause'.
    rel_bind_ap e e' "IH" v v' "(? & IH)".
    i_alloc as li "Hli". wp_alloc l as "Hl".
    iMod (inv_alloc (authN .@ "ref" .@ (l,li)) _ (∃ w1 w2,
            l ↦ w1 ∗ li ↦ᵢ w2 ∗ interp τ Δ w1 w2)%I with "[$Hl $Hli $IH]") as "HN".
    iFrame. iExists _. by iFrame.
  Qed.

  Lemma bin_log_related_unboxed_eq Θ Δ Γ e1 e2 e1' e2' τ :
    UnboxedType τ →
    ({Θ;Δ;Γ} ⊨ e1 ≤log≤ e1' : τ) -∗
    ({Θ;Δ;Γ} ⊨ e2 ≤log≤ e2' : τ) -∗
    {Θ;Δ;Γ} ⊨ BinOp EqOp e1 e2 ≤log≤ BinOp EqOp e1' e2' : t_bool.
  Proof.
    iIntros (Hτ) "IH1 IH2".
    intro_clause'.
    rel_bind_ap e2 e2' "IH2" v2 v2' "(? & #IH2)".
    rel_bind_ap e1 e1' "IH1" v1 v1' "(? & #IH1)".
    iAssert (⌜val_is_unboxed v1⌝ ∧ ⌜val_is_unboxed v1'⌝)%I as "(%&%)".
    { rewrite !unboxed_type_sound //.
      by iDestruct "IH1" as "(%&%)". }
    iAssert (⌜val_is_unboxed v2⌝ ∧ ⌜val_is_unboxed v2'⌝)%I as "(%&%)".
    { rewrite !unboxed_type_sound //.
      by iDestruct "IH2" as "(%&%)". }
    iMod (unboxed_type_eq with "IH1 IH2") as "%"; first done.
    i_pures; [solve_vals_compare_safe|].
    wp_pures.
    iFrame.
    rewrite interp_bool_unfold.
    do 2 case_bool_decide; naive_solver.
  Qed.

  Lemma bin_log_related_nat_binop Θ Δ Γ op e1 e2 e1' e2' τ :
    binop_nat_res_type op = Some τ →
    ({Θ;Δ;Γ} ⊨ e1 ≤log≤ e1' : t_nat) -∗
    ({Θ;Δ;Γ} ⊨ e2 ≤log≤ e2' : t_nat) -∗
    {Θ;Δ;Γ} ⊨ BinOp op e1 e2 ≤log≤ BinOp op e1' e2' : τ.
  Proof.
    iIntros (Hopτ) "IH1 IH2".
    intro_clause'.
    rel_bind_ap e2 e2' "IH2" v2 v2' "(?&IH2)".
    rel_bind_ap e1 e1' "IH1" v1 v1' "(?&IH1)".
    iDestruct "IH1" as (n) "(% & %)"; simplify_eq/=.
    iDestruct "IH2" as (n') "(% & %)"; simplify_eq/=.
    destruct (binop_nat_typed_safe _ op n n' _ Hopτ) as [v' Hopv'].
    i_pures; eauto; wp_pures.
    iFrame.
    destruct op; inversion Hopv'; simplify_eq/=;
      rewrite interp_unseal; try case_match; eauto.
  Qed.

  Lemma bin_log_related_bool_binop Θ Δ Γ op e1 e2 e1' e2' τ :
    binop_bool_res_type op = Some τ →
    ({Θ;Δ;Γ} ⊨ e1 ≤log≤ e1' : t_bool) -∗
    ({Θ;Δ;Γ} ⊨ e2 ≤log≤ e2' : t_bool) -∗
    {Θ;Δ;Γ} ⊨ BinOp op e1 e2 ≤log≤ BinOp op e1' e2' : τ.
  Proof.
    iIntros (Hopτ) "IH1 IH2".
    intro_clause'.
    rel_bind_ap e2 e2' "IH2" v2 v2' "(?&IH2)".
    rel_bind_ap e1 e1' "IH1" v1 v1' "(?&IH1)".
    iDestruct "IH1" as (n) "(% & %)"; simplify_eq/=.
    iDestruct "IH2" as (n') "(% & %)"; simplify_eq/=.
    destruct (binop_bool_typed_safe _ op n n' _ Hopτ) as [v' Hopv'].
    i_pures; eauto; wp_pures. iFrame.
    destruct op; inversion Hopv'; rewrite interp_unseal; simplify_eq/=; eauto.
  Qed.

  Lemma bin_log_related_strindex Θ Δ Γ e1 e2 e3 e1' e2' e3' :
    ({Θ;Δ;Γ} ⊨ e1 ≤log≤ e1' : t_nat) -∗
    ({Θ;Δ;Γ} ⊨ e2 ≤log≤ e2' : t_string) -∗
    ({Θ;Δ;Γ} ⊨ e3 ≤log≤ e3' : t_string) -∗
    {Θ; Δ; Γ} ⊨ strindex e1 e2 e3 ≤log≤ strindex e1' e2' e3' : t_unit + t_nat.
  Proof.
    iIntros "IH1 IH2 IH3".
    intro_clause'.
    rel_bind_ap e3 e3' "IH3" v3 v3' "(?&IH3)".
    rel_bind_ap e2 e2' "IH2" w2 w2' "(?&IH2)".
    rel_bind_ap e1 e1' "IH1" u1 u1' "(?&IH1)".
    iDestruct "IH1" as (n) "(% & %)"; simplify_eq/=.
    iDestruct "IH2" as (s) "(% & %)"; simplify_eq/=.
    iDestruct "IH3" as (s') "(% & %)"; simplify_eq/=.
    pures.
    iFrame.
    rewrite interp_unseal.
    destruct (String.index _ _ _) => /=; eauto 12.
  Qed.

  Lemma bin_log_related_strsub Θ Δ Γ e1 e2 e3 e1' e2' e3' :
    ({Θ;Δ;Γ} ⊨ e1 ≤log≤ e1' : t_nat) -∗
    ({Θ;Δ;Γ} ⊨ e2 ≤log≤ e2' : t_nat) -∗
    ({Θ;Δ;Γ} ⊨ e3 ≤log≤ e3' : t_string) -∗
    {Θ; Δ; Γ} ⊨ strsub e1 e2 e3 ≤log≤ strsub e1' e2' e3' : t_string.
  Proof.
    iIntros "IH1 IH2 IH3".
    intro_clause'.
    rel_bind_ap e3 e3' "IH3" v3 v3' "(?&IH3)".
    rel_bind_ap e2 e2' "IH2" w2 w2' "(?&IH2)".
    rel_bind_ap e1 e1' "IH1" u1 u1' "(?&IH1)".
    iDestruct "IH1" as (n) "(% & %)"; simplify_eq/=.
    iDestruct "IH2" as (s) "(% & %)"; simplify_eq/=.
    iDestruct "IH3" as (s') "(% & %)"; simplify_eq/=.
    pures. iFrame. iExists _. eauto.
  Qed.

  Lemma bin_log_related_nat_unop Θ Δ Γ op e e' τ :
    unop_nat_res_type op = Some τ →
    ({Θ;Δ;Γ} ⊨ e ≤log≤ e' : t_nat) -∗
    {Θ;Δ;Γ} ⊨ UnOp op e ≤log≤ UnOp op e' : τ.
  Proof.
    iIntros (Hopτ) "IH".
    intro_clause'.
    rel_bind_ap e e' "IH" v v' "(? & IH)".
    iDestruct "IH" as (n) "(% & %)"; simplify_eq/=.
    destruct (unop_nat_typed_safe _ op n _ Hopτ) as [v' Hopv'].
    i_pures; eauto; wp_pures. iFrame.
    destruct op; inversion Hopv'; simplify_eq/=; iExists _; try case_match; eauto.
  Qed.

  Lemma bin_log_related_bool_unop Θ Δ Γ op e e' τ :
    unop_bool_res_type op = Some τ →
    ({Θ;Δ;Γ} ⊨ e ≤log≤ e' : t_bool) -∗
    {Θ;Δ;Γ} ⊨ UnOp op e ≤log≤ UnOp op e' : τ.
  Proof.
    iIntros (Hopτ) "IH".
    intro_clause'.
    rel_bind_ap e e' "IH" v v' "(? & IH)".
    iDestruct "IH" as (n) "(% & %)"; simplify_eq/=.
    destruct (unop_bool_typed_safe _ op n _ Hopτ) as [v' Hopv'].
    eauto; i_pures; eauto; wp_pures. iFrame.
    destruct op; inversion Hopv'; simplify_eq/=; iExists _; eauto.
  Qed.

  Lemma bin_log_related_string_unop Θ Δ Γ op e e' τ :
    unop_string_res_type op = Some τ →
    ({Θ;Δ;Γ} ⊨ e ≤log≤ e' : t_string) -∗
    {Θ;Δ;Γ} ⊨ UnOp op e ≤log≤ UnOp op e' : τ.
  Proof.
    iIntros (Hopτ) "IH".
    intro_clause'.
    rel_bind_ap e e' "IH" v v' "(? & IH)".
    iDestruct "IH" as (s) "(% & %)"; simplify_eq/=.
    destruct (unop_string_typed_safe _ op s _ Hopτ) as [v' Hopv'].
    i_pures; eauto; wp_pures. iFrame.
    rewrite interp_unseal.
    destruct op; inversion Hopv'; simplify_eq/=; try case_match; iModIntro; eauto 12.
  Qed.

  Lemma bin_log_related_unfold Θ Δ Γ e e' κ (τ : typ κ (Θ ▹ κ%kind)) (T : telim_ctx Θ κ ⋆) :
    ({Θ;Δ;Γ} ⊨ e ≤log≤ e' : tfill T (μ: κ; τ)) -∗
    {Θ;Δ;Γ} ⊨ rec_unfold e ≤log≤ rec_unfold e' : tfill T (τ.[μ: κ; τ/]).
  Proof.
    iIntros "IH".
    intro_clause'.
    rel_bind_ap e e' "IH" v v' "(? & IH)".
    rewrite tfill_rec_eq. i_rec tᵢ. wp_rec.
    by iFrame.
  Qed.

  Lemma bin_log_related_fold Θ Δ Γ e e' κ (τ : typ κ (Θ ▹ κ%kind)) (T : telim_ctx Θ κ ⋆) :
    ({Θ;Δ;Γ} ⊨ e ≤log≤ e' : tfill T (τ.[μ: κ; τ/])) -∗
    {Θ;Δ;Γ} ⊨ rec_fold e ≤log≤ rec_fold e' : tfill T (μ: κ; τ).
  Proof.
    iIntros "IH".
    intro_clause'.
    rel_bind_ap e e' "IH" v v' "(?&IH)".
    i_rec tᵢ. wp_rec. iFrame.
    rewrite tfill_rec_eq //.
  Qed.

  Lemma bin_log_related_pack' Θ κ Δ Γ e e' τ τ' :
    ({Θ;Δ;Γ} ⊨ e ≤log≤ e' : τ.[τ'/]) -∗
    {Θ;Δ;Γ} ⊨ e ≤log≤ e' : ∃: κ, τ.
  Proof.
    iIntros "IH".
    intro_clause'; fold kindO.
    rel_bind_ap e e' "IH" v v' "(? & #IH)".
    iFrame.
    iExists (interp τ' Δ) => /=.
    rewrite subst_eq //.
  Qed.

  Lemma bin_log_related_pack κ (A : kindO Σ κ) Θ Δ Γ e e' τ :
    ({Θ ▹ κ; ext Δ A; ⤉ Γ} ⊨ e ≤log≤ e' : τ) -∗
    {Θ;Δ;Γ} ⊨ e ≤log≤ e' : ∃: κ, τ.
  Proof.
    iIntros "IH".
    intro_clause'.
    iSpecialize ("IH" with "[Hvs]"); fold kindO.
    { rewrite -shift_env_eq //. }
    iSpecialize ("IH" with "Hi").
    iApply wp_wand_r.
    iSplitL "IH"; [iApply "IH"|].
    iIntros (?) "(% & $ & ?)".
    by iExists _.
  Qed.

  Lemma bin_log_related_unpack Θ κ Δ Γ x e1 e1' e2 e2' τ τ2 :
    ({Θ;Δ;Γ} ⊨ e1 ≤log≤ e1' : ∃: κ, τ) -∗
    (∀ A : kindO Σ κ,
      {Θ ▹ κ; ext Δ A; <[x:=τ]>(⤉Γ)} ⊨
        e2 ≤log≤ e2' : Core.shift τ2) -∗
    {Θ;Δ;Γ} ⊨ (unpack: x := e1 in e2) ≤log≤ (unpack: x := e1' in e2') : τ2.
  Proof.
    iIntros "IH1 IH2".
    intro_clause'.
    pures.
    rewrite /bin_log_related.
    rel_bind_ap e1 e1' "IH1" v v' "(? & Hex)".
    iDestruct "Hex" as (A) "#IH1".
    rewrite /unpack; pures.
    iSpecialize ("IH2" $! A (binder_insert x (v,v') vs) with "[Hvs]").
    { rewrite (shift_env_eq Θ).
      rewrite binder_insert_fmap.
      iApply (env_ltyped_insert with "IH1 Hvs"). }
    rewrite !binder_insert_fmap !subst_map_binder_insert /=.
    rewrite -(shift_eq τ2).
    iApply ("IH2" with "[$]").
  Qed.

  Lemma bin_log_related_hash Θ Δ Γ e e' :
    ({Θ; Δ; Γ} ⊨ e ≤log≤ e' : t_string) -∗
    {Θ; Δ; Γ} ⊨ Hash e ≤log≤ Hash e' : t_string.
  Proof.
    iIntros "IH".
    intro_clause'.
    rel_bind_ap e e' "IH" v v' "([#Hctx Hi] & Hs)".
    simplify_eq.
    iDestruct "Hs" as "(% & -> & ->)".
    iMod (step_ideal_hash with "[$]") as "(_ & Hi)"; [done|].
    wp_apply (wp_hash with "[$]").
    iIntros "H". iFrame "# ∗". iExists _. eauto.
  Qed.

  Lemma bin_log_related_tequiv Θ Δ Γ e e' τ τ' :
    Θ ⊢ₑ τ ≃ τ' : ⋆ →
    ({Θ; Δ; Γ} ⊨ e ≤log≤ e' : τ) -∗
    ({Θ; Δ; Γ} ⊨ e ≤log≤ e' : τ').
  Proof.
    iIntros (?) "IH".
    iIntros (?) "?".
    rewrite tequiv_eq //.
    iApply ("IH" with "[$]").
  Qed.

  Theorem fundamental Θ Δ Γ e τ :
    Θ |ₜ Γ ⊢ₜ e : τ → ⊢ {Θ;Δ;Γ} ⊨ e ≤log≤ e : τ
  with fundamental_val Θ Δ v τ :
    Θ ⊢ᵥ v : τ → ⊢ interp τ Δ v v.
  Proof.
    - intros Ht. destruct Ht.
      + by iApply bin_log_related_var.
      + iIntros (γ) "#H /=".
        iIntros (??) "Hi". wp_pures. iFrame.
        iModIntro. by iApply fundamental_val.
      + iApply bin_log_related_nat_binop; first done;
          by iApply fundamental.
      + iApply bin_log_related_bool_binop; first done;
          by iApply fundamental.
      + iApply bin_log_related_nat_unop; first done.
        by iApply fundamental.
      + iApply bin_log_related_bool_unop; first done.
        by iApply fundamental.
      + iApply bin_log_related_string_unop; first done.
        by iApply fundamental.
      + iApply bin_log_related_unboxed_eq; try done;
          by iApply fundamental.
      + iApply bin_log_related_strindex; try done;
          by iApply fundamental.
      + iApply bin_log_related_strsub; try done;
          by iApply fundamental.
      + iApply bin_log_related_pair;
          by iApply fundamental.
      + iApply bin_log_related_fst;
          by iApply fundamental.
      + iApply bin_log_related_snd;
          by iApply fundamental.
      + iApply bin_log_related_injl;
          by iApply fundamental.
      + iApply bin_log_related_injr;
          by iApply fundamental.
      + iApply bin_log_related_case;
          by iApply fundamental.
      + iApply bin_log_related_if;
          by iApply fundamental.
      + iApply bin_log_related_rec.
        iModIntro. by iApply fundamental.
      + iApply bin_log_related_app;
          by iApply fundamental.
      + iApply bin_log_related_tlam.
        iIntros (A). iModIntro. by iApply fundamental.
      + iApply bin_log_related_tapp'; by iApply fundamental.
      + iApply bin_log_related_fold; by iApply fundamental.
      + iApply bin_log_related_unfold; by iApply fundamental.
      + iApply bin_log_related_pack'; by iApply fundamental.
      + iApply bin_log_related_unpack; try by iApply fundamental.
        iIntros (A). by iApply fundamental.
      + iApply bin_log_related_fork; by iApply fundamental.
      + iApply bin_log_related_alloc; by iApply fundamental.
      + iApply bin_log_related_load; by iApply fundamental.
      + iApply bin_log_related_store; by iApply fundamental.
      + iApply bin_log_related_xchg; by iApply fundamental.
      + iApply bin_log_related_FAA; eauto;
          by iApply fundamental.
      + iApply bin_log_related_CmpXchg; eauto;
          by iApply fundamental.
      + iApply bin_log_related_hash; by iApply fundamental.
      + iApply bin_log_related_tequiv; [done|]. by iApply fundamental.
    - intros Hv. destruct Hv; simpl.
      + rewrite interp_unseal. iSplit; eauto.
      + rewrite interp_unseal. iExists _; iSplit; eauto.
      + rewrite interp_unseal. iExists _; iSplit; eauto.
      + rewrite interp_unseal. iExists _; iSplit; eauto.
      + rewrite interp_prod_unfold. iExists _,_,_,_.
        repeat iSplit; eauto; by iApply fundamental_val.
      + rewrite interp_sum_unfold. iExists _,_. iLeft.
        repeat iSplit; eauto; by iApply fundamental_val.
      + rewrite interp_sum_unfold. iExists _,_. iRight.
        repeat iSplit; eauto; by iApply fundamental_val.
      + iLöb as "IH". iIntros (??) "!# #Hv".
        pose (Γ := (<[f:=(τ1 → τ2)%ty]> (<[x:=τ1]> ∅)):stringmap (typ ⋆ Θ)).
        pose (γ := (binder_insert f ((rec: f x := e)%V,(rec: f x := e)%V)
                      (binder_insert x (v1, v2) ∅)):stringmap (val*val)).
        iIntros (??) "Hi".
        pures.
        iPoseProof (fundamental Θ Δ Γ e τ2 $! γ with "[] ") as "H"; eauto.
        { rewrite /γ /Γ. rewrite !binder_insert_fmap fmap_empty.
          iApply (env_ltyped_insert with "IH").
          iApply (env_ltyped_insert with "Hv").
          iApply env_ltyped_empty. }
        rewrite /γ /=. rewrite !binder_insert_fmap !fmap_empty /=.
        rewrite !subst_map_binder_insert_2_empty.
        iApply ("H" with "[$]").
      + rewrite interp_forall_unfold. iIntros (A). iModIntro. iIntros (v1 v2) "_".
        iIntros (??) "Hi"; pures.
        iPoseProof (fundamental _ (ext Δ A) ∅ e τ $! ∅ with "[]") as "H"; eauto.
        { rewrite fmap_empty. iApply env_ltyped_empty. }
        rewrite !fmap_empty subst_map_empty.
        iApply ("H" with "[$]").
  Qed.

  Theorem refines_typed Θ τ Δ e :
    Θ |ₜ ∅ ⊢ₜ e : τ →
    ⊢ REL e << e : interp τ Δ.
  Proof.
    move=> /fundamental Hty.
    iPoseProof (Hty Δ with "[]") as "H".
    { rewrite fmap_empty. iApply env_ltyped_empty. }
    by rewrite !fmap_empty !subst_map_empty.
  Qed.

End fundamental.
