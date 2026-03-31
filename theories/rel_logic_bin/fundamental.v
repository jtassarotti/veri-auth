(** Compatibility lemmas for the logical relation *)
From auth.heap_lang Require Import proofmode_upto_bad.
From auth.rel_logic_bin Require Import model.
From auth.rel_logic_bin Require Export compatibility interp.
From iris.proofmode Require Export proofmode.

Section fundamental.
  Context `{authG Σ, seqG Σ}.
  Hint Resolve to_of_val : core.

  Local Ltac intro_clause := progress (iIntros (vs) "#Hvs /=").
  Local Ltac intro_clause' := intro_clause; iIntros (??) "(Hi & Htok)".
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
    iIntros (??) "(Hi & Htok)".
    wp_pures. by iFrame.
  Qed.

  Lemma bin_log_related_pair Θ Δ Γ e1 e2 e1' e2' τ1 τ2 :
    ({Θ;Δ;Γ} ⊨ e1 ≤log≤ e1' : τ1) -∗
    ({Θ;Δ;Γ} ⊨ e2 ≤log≤ e2' : τ2) -∗
    {Θ;Δ;Γ} ⊨ Pair e1 e2 ≤log≤ Pair e1' e2' : t_prod τ1 τ2.
  Proof.
    iIntros "IH1 IH2".
    intro_clause'.
    rel_bind_ap e2 e2' "IH2" v v' "(Hi & #Hv & Htok)".
    rel_bind_ap e1 e1' "IH1" w w' "(Hi & #Hw & Htok)".
    pures. iFrame. iModIntro.
    iDestruct "Hw" as "[#Hwbin #Hwun]".
    iDestruct "Hv" as "[#Hvbin #Hvun]".
    iSplit.
    - rewrite interp_prod_unfold. iExists w, w', v, v'. iFrame "#". done.
    - rewrite interp_un_prod_unfold. iExists w, v. iFrame "#". done.
  Qed.

  Lemma bin_log_related_fst Θ Δ Γ e e' τ1 τ2 :
    ({Θ;Δ;Γ} ⊨ e ≤log≤ e' : τ1 * τ2) -∗
    {Θ;Δ;Γ} ⊨ Fst e ≤log≤ Fst e' : τ1.
  Proof.
    iIntros "IH".
    intro_clause'.
    rel_bind_ap e e' "IH" v u "(Hi & H & Htok)".
    iDestruct "H" as (v1 v2 v1' v2') "(-> & -> & Ha & Hb)".
    pures. by iFrame.
  Qed.

  Lemma bin_log_related_snd Θ Δ Γ e e' τ1 τ2 :
    ({Θ;Δ;Γ} ⊨ e ≤log≤ e' : τ1 * τ2) -∗
    {Θ;Δ;Γ} ⊨ Snd e ≤log≤ Snd e' : τ2.
  Proof.
    iIntros "IH".
    intro_clause'.
    rel_bind_ap e e' "IH" v u "(Hi & H & Htok)".
    iDestruct "H" as (v1 v2 v1' v2') "(-> & -> & Ha & Hb)".
    pures. by iFrame.
  Qed.

  Lemma bin_log_related_app Θ Δ Γ e1 e2 e1' e2' τ1 τ2 :
    ({Θ;Δ;Γ} ⊨ e1 ≤log≤ e1' : τ1 → τ2) -∗
    ({Θ;Δ;Γ} ⊨ e2 ≤log≤ e2' : τ1) -∗
    {Θ;Δ;Γ} ⊨ App e1 e2 ≤log≤ App e1' e2' :  τ2.
  Proof.
    iIntros "IH1 IH2".
    intro_clause'.
    rel_bind_ap e2 e2' "IH2" v v' "(Hi & #Hv & Htok)".
    rel_bind_ap e1 e1' "IH1" f f' "(Hi & #Hf & Htok)".
    iDestruct "Hf" as "[#Hfbin _]".
    iEval (rewrite interp_arr_unfold) in "Hfbin".
    iApply ("Hfbin" with "[$Hv]"). iFrame.
  Qed.

  Lemma bin_log_related_rec Θ Δ (Γ : stringmap (typ ⋆ Θ)) (f x : binder) (e e' : expr) τ1 τ2 :
    □ ({Θ;Δ;<[f:=t_arr τ1 τ2]>(<[x:=τ1]>Γ)} ⊨ e ≤log≤ e' : τ2) -∗
    □ ({Θ;Δ;<[f:=t_arr τ1 τ2]>(<[x:=τ1]>Γ)} ⊨ᵤ e : τ2) -∗
    {Θ;Δ;Γ} ⊨ Rec f x e ≤log≤ Rec f x e' : τ1 → τ2.
  Proof.
    iIntros "#IHbin #IHun". intro_clause. iIntros (??) "(Hi & Htok)".
    wp_pures. i_pures. iFrame.
    iLöb as "IHlob".
    iModIntro. iSplit.
    - (* binary arrow *)
      rewrite interp_arr_unfold. iModIntro. iIntros (w w') "#Hw".
      iIntros (??) "(Hi' & Htok')".
      wp_pures. i_pures.
      iMod "IHlob" as "#IHlob".
      set rec1 := (RecV f x (subst_map (binder_delete x (binder_delete f (fst <$> vs))) e)).
      set rec2 := (RecV f x (subst_map (binder_delete x (binder_delete f (snd <$> vs))) e')).
      set vs' := binder_insert f (rec1, rec2) (binder_insert x (w, w') vs).
      iSpecialize ("IHbin" $! vs' with "[#]").
      { rewrite !binder_insert_fmap.
        iApply (env_ltyped_insert with "IHlob").
        iApply (env_ltyped_insert with "Hw").
        iApply "Hvs". }
      rewrite /vs' !binder_insert_fmap !subst_map_binder_insert_2.
      iApply ("IHbin" with "[$Hi' $Htok']").
    - (* unary arrow *)
      rewrite interp_un_arr_unfold. iModIntro. iIntros (w) "#Hw_un".
      iIntros "Htok'". wp_pures.
      iMod "IHlob" as "#IHlob".
      iDestruct (lrel_bi_proj_un with "IHlob") as "#IHlob_un".
      set rec1 := (RecV f x (subst_map (binder_delete x (binder_delete f (fst <$> vs))) e)).
      set vs_un := binder_insert f rec1 (binder_insert x w (fst <$> vs)).
      iSpecialize ("IHun" $! vs_un with "[#]").
      { rewrite !binder_insert_fmap.
        iApply (un_env_ltyped_insert with "IHlob_un").
        iApply (un_env_ltyped_insert with "Hw_un").
        iApply (env_bin_to_un with "Hvs"). }
      rewrite /vs_un subst_map_binder_insert_2.
      iApply ("IHun" with "Htok'").
  Qed.

(*   Lemma bin_log_related_fork Θ Δ Γ e e' :
    ({Θ;Δ;Γ} ⊨ e ≤log≤ e' : ()) -∗
    {Θ;Δ;Γ} ⊨ Fork e ≤log≤ Fork e' : ().
  Proof.
    iIntros "IH".
    intro_clause.
    rewrite /bin_log_related.
    setoid_rewrite interp_unit_unfold.
    iApply refines_fork.
    by iApply "IH".
  Qed. *)

  Lemma bin_log_related_tlam Θ (Δ : ctxO Σ Θ) Γ κ (e e' : expr) τ :
    (∀ (A : kindO Σ κ),
      □ ({(Θ ▹ κ); (ext Δ A); ⤉Γ} ⊨ e ≤log≤ e' : τ)) -∗
    (∀ (A : kindO Σ κ),
      □ ({(Θ ▹ κ); (ext Δ A); ⤉Γ} ⊨ᵤ e : τ)) -∗
    {Θ;Δ;Γ} ⊨ (Λ: e) ≤log≤ (Λ: e') : ∀: κ, τ.
  Proof.
    iIntros "#IHbin #IHun". intro_clause. iIntros (??) "(Hi & Htok)".
    wp_pures. i_pures. iFrame. iModIntro. iSplit.
    - rewrite interp_forall_unfold. iIntros (A). iModIntro. iIntros (v1 v2) "_".
      iIntros (??) "(Hi' & Htok')". wp_pures. i_pures.
      iApply ("IHbin" $! A with "[Hvs] [$Hi' $Htok']").
      rewrite -shift_env_bin_eq //.
    - rewrite interp_un_forall_unfold. iIntros (A). iModIntro. iIntros (v') "_".
      iIntros "Htok'". wp_pures.
      iApply ("IHun" $! A with "[Hvs] Htok'").
      rewrite -shift_env_un_eq.
      iApply (env_bin_to_un with "Hvs").
  Qed.

  Lemma bin_log_related_tapp' Θ Δ κ Γ e e' τ τ' :
    ({Θ;Δ;Γ} ⊨ e ≤log≤ e' : ∀: κ, τ) -∗
    {Θ;Δ;Γ} ⊨ e #~ ≤log≤ e' #~ : τ.[τ'/].
  Proof.
    iIntros "IH".
    intro_clause'.
    rel_bind_ap e e' "IH" v v' "(Hp & IH & Htok)"; fold kindO.
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
    rewrite -shift_env_bin_eq.
    rel_bind_ap e e' "IH" v v' "(Hp & IH & Htok)"; fold kindO.
    iApply ("IH" $! _ #~ #~ with "[//] [$Hp $Htok]").
  Qed.

  Lemma bin_log_related_seq Θ κ (A : kindO Σ κ) τ1 τ2 Δ Γ e1 e2 e1' e2' :
    ({Θ ▹ κ; ext Δ A; ⤉Γ} ⊨ e1 ≤log≤ e1' : τ1) -∗
    ({Θ;Δ;Γ} ⊨ e2 ≤log≤ e2' : τ2) -∗
    {Θ;Δ;Γ} ⊨ (e1;; e2) ≤log≤ (e1';; e2') : τ2.
  Proof.
    iIntros "He1 He2".
    intro_clause.
    iApply (refines_seq (interp τ1 (ext Δ A)) with "[He1]").
    - iApply ("He1" with "[Hvs]"). rewrite -shift_env_bin_eq //.
    - by iApply "He2".
  Qed.

  Lemma bin_log_related_seq' Θ Δ Γ e1 e2 e1' e2' τ1 τ2 :
    ({Θ;Δ;Γ} ⊨ e1 ≤log≤ e1' : τ1) -∗
    ({Θ;Δ;Γ} ⊨ e2 ≤log≤ e2' : τ2) -∗
    {Θ;Δ;Γ} ⊨ (e1;; e2) ≤log≤ (e1';; e2') : τ2.
  Proof.
    iIntros "He1 He2".
    iApply (bin_log_related_seq _ ⋆ (ι_bin ⋆ lrel_true) (Core.shift τ1 : typ _ _) with "[He1] He2").
    intro_clause.
    rewrite -shift_env_bin_eq -shift_eq.
    by iApply "He1".
  Qed.

  Lemma bin_log_related_injl Θ Δ Γ e e' τ1 τ2 :
    ({Θ;Δ;Γ} ⊨ e ≤log≤ e' : τ1) -∗
    {Θ;Δ;Γ} ⊨ InjL e ≤log≤ InjL e' : τ1 + τ2.
  Proof.
    iIntros "IH".
    intro_clause'.
    rel_bind_ap e e' "IH" v v' "(? & #H & Htok)".
    pures. iFrame. iModIntro.
    iDestruct "H" as "[#Hbin #Hun]".
    iSplit.
    - rewrite interp_sum_unfold. iExists v, v'. iLeft.
      iSplit; [done | iSplit; [done |]]. iApply "Hbin".
    - rewrite interp_un_sum_unfold. iExists v. iLeft.
      iSplit; [done |]. iApply "Hun".
  Qed.

  Lemma bin_log_related_injr Θ Δ Γ e e' τ1 τ2 :
    ({Θ;Δ;Γ} ⊨ e ≤log≤ e' : τ2) -∗
    {Θ;Δ;Γ} ⊨ InjR e ≤log≤ InjR e' : τ1 + τ2.
  Proof.
    iIntros "IH".
    intro_clause'.
    rel_bind_ap e e' "IH" v v' "(? & #H & Htok)".
    pures. iFrame. iModIntro.
    iDestruct "H" as "[#Hbin #Hun]".
    iSplit.
    - rewrite interp_sum_unfold. iExists v, v'. iRight.
      iSplit; [done | iSplit; [done |]]. iApply "Hbin".
    - rewrite interp_un_sum_unfold. iExists v. iRight.
      iSplit; [done |]. iApply "Hun".
  Qed.

  Lemma bin_log_related_case Θ Δ Γ e0 e1 e2 e0' e1' e2' τ1 τ2 τ3 :
    ({Θ;Δ;Γ} ⊨ e0 ≤log≤ e0' : τ1 + τ2) -∗
    ({Θ;Δ;Γ} ⊨ e1 ≤log≤ e1' : τ1 → τ3) -∗
    ({Θ;Δ;Γ} ⊨ e2 ≤log≤ e2' : τ2 → τ3) -∗
    {Θ;Δ;Γ} ⊨ Case e0 e1 e2 ≤log≤ Case e0' e1' e2' : τ3.
  Proof.
    iIntros "IH1 IH2 IH3".
    intro_clause'.
    rel_bind_ap e0 e0' "IH1" v0 v0' "(Hi & IH1 & Htok)".
    iDestruct "IH1" as (w w') "[(% & % & #Hw) | (% & % & #Hw)]";
      simplify_eq/=; pures.
    - iApply (bin_log_related_app _ Δ Γ _ w _ w'  with "IH2 [] Hvs [$]").
      iIntros (?) "?". iIntros (??) "(Hi & Htok)".
      wp_pures. by iFrame.
    - iApply (bin_log_related_app _ Δ Γ _ w _ w' with "IH3 [] Hvs [$]").
      iIntros (?) "?"; iIntros (??) "(Hi & Htok)".
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
    rel_bind_ap e0 e0' "IH1" v0 v0' "(Hi & IH1 & Htok)".
    iDestruct "IH1" as ([]) "(% & %)"; simplify_eq/=; pures.
    - by iApply ("IH2" with "[$] [$]") .
    - by iApply ("IH3" with "[$] [$]") .
  Qed.

  (* Lemma bin_log_related_load Θ Δ Γ e e' τ :
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
    rel_bind_ap e2 e2' "IH2" v2 v2' "(Hi & IH2 & Htok)".
    rel_bind_ap e1 e1' "IH1" v1 v1' "(Hi & IH1 & Htok)".
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
    rel_bind_ap e3 e3' "IH3" v3 v3' "(? & #IH3 & Htok)".
    rel_bind_ap e2 e2' "IH2" v2 v2' "(? & #IH2 & Htok)".
    rel_bind_ap e1 e1' "IH1" v1 v1' "(? & #IH1 & Htok)".
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
    rel_bind_ap e e' "IH" v v' "(? & IH & Htok)".
    i_alloc as li "Hli". wp_alloc l as "Hl".
    iMod (inv_alloc (authN .@ "ref" .@ (l,li)) _ (∃ w1 w2,
            l ↦ w1 ∗ li ↦ᵢ w2 ∗ interp τ Δ w1 w2)%I with "[$Hl $Hli $IH]") as "HN".
    iFrame. iExists _. by iFrame.
  Qed. *)

  Lemma bin_log_related_unboxed_eq Θ Δ Γ e1 e2 e1' e2' τ :
    UnboxedType τ →
    ({Θ;Δ;Γ} ⊨ e1 ≤log≤ e1' : τ) -∗
    ({Θ;Δ;Γ} ⊨ e2 ≤log≤ e2' : τ) -∗
    {Θ;Δ;Γ} ⊨ BinOp EqOp e1 e2 ≤log≤ BinOp EqOp e1' e2' : t_bool.
  Proof.
    iIntros (Hτ) "IH1 IH2".
    intro_clause'.
    rel_bind_ap e2 e2' "IH2" v2 v2' "(? & #IH2 & Htok)".
    rel_bind_ap e1 e1' "IH1" v1 v1' "(? & #IH1 & Htok)".
    iDestruct (unboxed_type_sound _ _ _ _ _ Hτ with "[IH1]") as "(% & %)".
    { iDestruct "IH1" as "[$ _]". }
    iDestruct (unboxed_type_sound _ _ _ _ _ Hτ with "[IH2]") as "(% & %)".
    { iDestruct "IH2" as "[$ _]". }
    iMod (unboxed_type_eq _ _ _ _ _ _ _ Hτ with "IH1 IH2") as "%".
    i_pures; [solve_vals_compare_safe|].
    wp_pures.
    iFrame. iModIntro.
    iSplit.
    - rewrite interp_bool_unfold /lrel_bool; cbv [lrel_car].
      do 2 case_bool_decide; naive_solver.
    - rewrite interp_unseal /= /lrel_un_bool /=.
      iExists (bool_decide (v1 = v2)). iPureIntro. done.
  Qed.

  Lemma bin_log_related_nat_binop Θ Δ Γ op e1 e2 e1' e2' τ :
    binop_nat_res_type op = Some τ →
    ({Θ;Δ;Γ} ⊨ e1 ≤log≤ e1' : t_nat) -∗
    ({Θ;Δ;Γ} ⊨ e2 ≤log≤ e2' : t_nat) -∗
    {Θ;Δ;Γ} ⊨ BinOp op e1 e2 ≤log≤ BinOp op e1' e2' : τ.
  Proof.
    iIntros (Hopτ) "IH1 IH2".
    intro_clause'.
    rel_bind_ap e2 e2' "IH2" v2 v2' "(?&IH2&Htok)".
    rel_bind_ap e1 e1' "IH1" v1 v1' "(?&IH1&Htok)".
    iDestruct "IH1" as "[Hbin1 _]". iEval (rewrite interp_nat_unfold) in "Hbin1".
    iDestruct "Hbin1" as (n) "[% %]"; simplify_eq/=.
    iDestruct "IH2" as "[Hbin2 _]". iEval (rewrite interp_nat_unfold) in "Hbin2".
    iDestruct "Hbin2" as (n') "[% %]"; simplify_eq/=.
    destruct (binop_nat_typed_safe _ op n n' _ Hopτ) as [v' Hopv'].
    i_pures; eauto; wp_pures.
    iFrame. iModIntro.
    destruct op; inversion Hopv'; simplify_eq/=;
      rewrite interp_unseal; try case_match;
      simpl; iSplit; iExists _; done.
  Qed.

  Lemma bin_log_related_bool_binop Θ Δ Γ op e1 e2 e1' e2' τ :
    binop_bool_res_type op = Some τ →
    ({Θ;Δ;Γ} ⊨ e1 ≤log≤ e1' : t_bool) -∗
    ({Θ;Δ;Γ} ⊨ e2 ≤log≤ e2' : t_bool) -∗
    {Θ;Δ;Γ} ⊨ BinOp op e1 e2 ≤log≤ BinOp op e1' e2' : τ.
  Proof.
    iIntros (Hopτ) "IH1 IH2".
    intro_clause'.
    rel_bind_ap e2 e2' "IH2" v2 v2' "(?&IH2&Htok)".
    rel_bind_ap e1 e1' "IH1" v1 v1' "(?&IH1&Htok)".
    iDestruct "IH1" as "[Hbin1 _]". iEval (rewrite interp_bool_unfold) in "Hbin1".
    iDestruct "Hbin1" as (n) "[% %]"; simplify_eq/=.
    iDestruct "IH2" as "[Hbin2 _]". iEval (rewrite interp_bool_unfold) in "Hbin2".
    iDestruct "Hbin2" as (n') "[% %]"; simplify_eq/=.
    destruct (binop_bool_typed_safe _ op n n' _ Hopτ) as [v' Hopv'].
    i_pures; eauto; wp_pures. iFrame. iModIntro.
    destruct op; inversion Hopv'; rewrite interp_unseal; simplify_eq/=;
      simpl; iSplit; iExists _; done.
  Qed.

  Lemma bin_log_related_strindex Θ Δ Γ e1 e2 e3 e1' e2' e3' :
    ({Θ;Δ;Γ} ⊨ e1 ≤log≤ e1' : t_nat) -∗
    ({Θ;Δ;Γ} ⊨ e2 ≤log≤ e2' : t_string) -∗
    ({Θ;Δ;Γ} ⊨ e3 ≤log≤ e3' : t_string) -∗
    {Θ; Δ; Γ} ⊨ strindex e1 e2 e3 ≤log≤ strindex e1' e2' e3' : t_unit + t_nat.
  Proof.
    iIntros "IH1 IH2 IH3".
    intro_clause'.
    rel_bind_ap e3 e3' "IH3" v3 v3' "(?&IH3&Htok)".
    rel_bind_ap e2 e2' "IH2" w2 w2' "(?&IH2&Htok)".
    rel_bind_ap e1 e1' "IH1" u1 u1' "(?&IH1&Htok)".
    iDestruct "IH1" as "[Hbin1 _]". iEval (rewrite interp_nat_unfold) in "Hbin1".
    iDestruct "Hbin1" as (n) "[% %]"; simplify_eq/=.
    iDestruct "IH2" as "[Hbin2 _]". iEval (rewrite interp_string_unfold) in "Hbin2".
    iDestruct "Hbin2" as (s) "[% %]"; simplify_eq/=.
    iDestruct "IH3" as "[Hbin3 _]". iEval (rewrite interp_string_unfold) in "Hbin3".
    iDestruct "Hbin3" as (s') "[% %]"; simplify_eq/=.
    pures. iFrame. rewrite interp_unseal.
    destruct (String.index _ _ _) => /=;
      iModIntro;
      cbv [lrel_bi_as_lrel lrel_bi_bin lrel_bi_un lrel_bi_sum lrel_car lrel_sum lrel_sum' lrel_un_sum lrel_un_sum' lrel_un_int lrel_un_unit];
      simpl; eauto 15.
  Qed.

  Lemma bin_log_related_strsub Θ Δ Γ e1 e2 e3 e1' e2' e3' :
    ({Θ;Δ;Γ} ⊨ e1 ≤log≤ e1' : t_nat) -∗
    ({Θ;Δ;Γ} ⊨ e2 ≤log≤ e2' : t_nat) -∗
    ({Θ;Δ;Γ} ⊨ e3 ≤log≤ e3' : t_string) -∗
    {Θ; Δ; Γ} ⊨ strsub e1 e2 e3 ≤log≤ strsub e1' e2' e3' : t_string.
  Proof.
    iIntros "IH1 IH2 IH3".
    intro_clause'.
    rel_bind_ap e3 e3' "IH3" v3 v3' "(?&IH3&Htok)".
    rel_bind_ap e2 e2' "IH2" w2 w2' "(?&IH2&Htok)".
    rel_bind_ap e1 e1' "IH1" u1 u1' "(?&IH1&Htok)".
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
    rel_bind_ap e e' "IH" v v' "(? & IH & Htok)".
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
    rel_bind_ap e e' "IH" v v' "(? & IH & Htok)".
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
    rel_bind_ap e e' "IH" v v' "(? & IH & Htok)".
    iDestruct "IH" as (s) "(% & %)"; simplify_eq/=.
    destruct (unop_string_typed_safe _ op s _ Hopτ) as [v' Hopv'].
    i_pures; eauto; wp_pures. iFrame. rewrite interp_unseal.
    destruct op; inversion Hopv'; simplify_eq/=; try case_match; iModIntro;
      try (cbv [lrel_bi_as_lrel lrel_bi_bin lrel_bi_un lrel_bi_sum lrel_car lrel_sum lrel_sum'
                lrel_un_sum lrel_un_sum' lrel_un_int lrel_un_unit]; simpl; eauto 15); eauto 12.
  Qed.

  Lemma bin_log_related_unfold Θ Δ Γ e e' κ (τ : typ κ (Θ ▹ κ%kind)) (T : telim_ctx Θ κ ⋆) :
    ({Θ;Δ;Γ} ⊨ e ≤log≤ e' : tfill T (μ: κ; τ)) -∗
    {Θ;Δ;Γ} ⊨ rec_unfold e ≤log≤ rec_unfold e' : tfill T (τ.[μ: κ; τ/]).
  Proof.
    iIntros "IH".
    intro_clause'.
    rel_bind_ap e e' "IH" v v' "(? & IH & Htok)".
    rewrite tfill_rec_eq. i_rec tᵢ. wp_rec.
    by iFrame.
  Qed.
  
  Lemma bin_log_related_fold Θ Δ Γ e e' κ (τ : typ κ (Θ ▹ κ%kind)) (T : telim_ctx Θ κ ⋆) :
    ({Θ;Δ;Γ} ⊨ e ≤log≤ e' : tfill T (τ.[μ: κ; τ/])) -∗
    {Θ;Δ;Γ} ⊨ rec_fold e ≤log≤ rec_fold e' : tfill T (μ: κ; τ).
  Proof.
    iIntros "IH".
    intro_clause'.
    rel_bind_ap e e' "IH" v v' "(?&IH&Htok)".
    i_rec tᵢ. wp_rec. iFrame.
    rewrite tfill_rec_eq //. simpl.
    iDestruct "IH" as "[IHb IHu]".
    iModIntro. iSplitL "IHb"; done.
  Qed.

  Lemma bin_log_related_pack' Θ κ Δ Γ e e' τ τ' :
    ({Θ;Δ;Γ} ⊨ e ≤log≤ e' : τ.[τ'/]) -∗
    {Θ;Δ;Γ} ⊨ e ≤log≤ e' : ∃: κ, τ.
  Proof.
    iIntros "IH".
    intro_clause'; fold kindO.
    rel_bind_ap e e' "IH" v v' "(? & #IH & Htok)".
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
    { rewrite -shift_env_bin_eq //. }
    iSpecialize ("IH" with "[$]").
    iApply wp_wand_r.
    iSplitL "IH"; [iApply "IH"|].
    iIntros (?) "(% & $ & ? & Htok)". iFrame.
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
    rel_bind_ap e1 e1' "IH1" v v' "(? & Hex & Htok)".
    iDestruct "Hex" as (A) "#IH1".
    rewrite /unpack; pures.
    iSpecialize ("IH2" $! A (binder_insert x (v,v') vs) with "[Hvs]").
    { rewrite (shift_env_bin_eq Θ).
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
    rel_bind_ap e e' "IH" v v' "([#Hctx Hi] & Hs & Htok)".
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

  (** Unary compatibility lemmas — admitted, to be proved separately *)

  Lemma un_log_related_var Θ Δ Γ x τ :
    Γ !! x = Some τ →
    ⊢ {Θ;Δ;Γ} ⊨ᵤ Var x : τ.
  Proof.
    iIntros (Hx). iIntros (vs) "#Hvs".
    iDestruct (big_sepM2_lookup_l _ _ _ x (lrel_bi_un (interp τ Δ)) with "Hvs") as (v Hv) "#Hτv".
    { rewrite lookup_fmap Hx //. }
    iIntros "Htok". simpl. rewrite Hv /=.
    wp_pures. iModIntro. iFrame "#∗".
  Qed.

  Lemma un_log_related_nat_binop Θ Δ Γ op e1 e2 τ :
    binop_nat_res_type op = Some τ →
    ({Θ;Δ;Γ} ⊨ᵤ e1 : t_nat) -∗
    ({Θ;Δ;Γ} ⊨ᵤ e2 : t_nat) -∗
    {Θ;Δ;Γ} ⊨ᵤ BinOp op e1 e2 : τ.
  Proof.
    iIntros (Hop) "IH1 IH2". iIntros (vs) "#Hvs Htok". simpl.
    wp_bind (subst_map vs e2). iApply (wp_wand with "[IH2 Htok]").
    { iApply ("IH2" $! vs with "Hvs Htok"). }
    iIntros (v2) "[#Hv2 Htok]".
    wp_bind (subst_map vs e1). iApply (wp_wand with "[IH1 Htok]").
    { iApply ("IH1" $! vs with "Hvs Htok"). }
    iIntros (v1) "[#Hv1 Htok]".
    iEval (rewrite interp_unseal /=) in "Hv1". iEval (rewrite interp_unseal /=) in "Hv2".
    iDestruct "Hv1" as (n1) "%". iDestruct "Hv2" as (n2) "%". simplify_eq.
    destruct (binop_nat_typed_safe Θ op n1 n2 τ Hop) as [v' Heval].
    wp_pures; eauto.
    iModIntro. iFrame. destruct op; inversion Heval; simplify_eq/=;
      rewrite interp_unseal; simpl; iExists _; done.
  Qed.

  Lemma un_log_related_bool_binop Θ Δ Γ op e1 e2 τ :
    binop_bool_res_type op = Some τ →
    ({Θ;Δ;Γ} ⊨ᵤ e1 : t_bool) -∗
    ({Θ;Δ;Γ} ⊨ᵤ e2 : t_bool) -∗
    {Θ;Δ;Γ} ⊨ᵤ BinOp op e1 e2 : τ.
  Proof.
    iIntros (Hop) "IH1 IH2". iIntros (vs) "#Hvs Htok". simpl.
    wp_bind (subst_map vs e2). iApply (wp_wand with "[IH2 Htok]").
    { iApply ("IH2" $! vs with "Hvs Htok"). }
    iIntros (v2) "[#Hv2 Htok]".
    wp_bind (subst_map vs e1). iApply (wp_wand with "[IH1 Htok]").
    { iApply ("IH1" $! vs with "Hvs Htok"). }
    iIntros (v1) "[#Hv1 Htok]".
    iEval (rewrite interp_unseal /=) in "Hv1". iEval (rewrite interp_unseal /=) in "Hv2".
    iDestruct "Hv1" as (b1) "%". iDestruct "Hv2" as (b2) "%". simplify_eq.
    destruct (binop_bool_typed_safe Θ op b1 b2 τ Hop) as [v' Heval].
    wp_pures; eauto.
    iModIntro. iFrame. destruct op; inversion Heval; simplify_eq/=;
      rewrite interp_unseal; simpl; iExists _; done.
  Qed.

  Lemma un_log_related_nat_unop Θ Δ Γ op e τ :
    unop_nat_res_type op = Some τ →
    ({Θ;Δ;Γ} ⊨ᵤ e : t_nat) -∗
    {Θ;Δ;Γ} ⊨ᵤ UnOp op e : τ.
  Proof.
    iIntros (Hop) "IH". iIntros (vs) "#Hvs Htok". simpl.
    wp_bind (subst_map vs e). iApply (wp_wand with "[IH Htok]").
    { iApply ("IH" $! vs with "Hvs Htok"). }
    iIntros (v) "[#Hv Htok]".
    iEval (rewrite interp_unseal /=) in "Hv". iDestruct "Hv" as (n) "%". simplify_eq.
    destruct (unop_nat_typed_safe Θ op n τ Hop) as [v' Heval].
    wp_pures; eauto. iModIntro. iFrame.
    destruct op; inversion Heval; simplify_eq/=;
      rewrite interp_unseal; simpl; iExists _; done.
  Qed.

  Lemma un_log_related_bool_unop Θ Δ Γ op e τ :
    unop_bool_res_type op = Some τ →
    ({Θ;Δ;Γ} ⊨ᵤ e : t_bool) -∗
    {Θ;Δ;Γ} ⊨ᵤ UnOp op e : τ.
  Proof.
    iIntros (Hop) "IH". iIntros (vs) "#Hvs Htok". simpl.
    wp_bind (subst_map vs e). iApply (wp_wand with "[IH Htok]").
    { iApply ("IH" $! vs with "Hvs Htok"). }
    iIntros (v) "[#Hv Htok]".
    iEval (rewrite interp_unseal /=) in "Hv". iDestruct "Hv" as (b) "%". simplify_eq.
    destruct (unop_bool_typed_safe Θ op b τ Hop) as [v' Heval].
    wp_pures; eauto. iModIntro. iFrame.
    destruct op; inversion Heval; simplify_eq/=;
      rewrite interp_unseal; simpl; iExists _; done.
  Qed.

  Lemma un_log_related_string_unop Θ Δ Γ op e τ :
    unop_string_res_type op = Some τ →
    ({Θ;Δ;Γ} ⊨ᵤ e : t_string) -∗
    {Θ;Δ;Γ} ⊨ᵤ UnOp op e : τ.
  Proof.
    iIntros (Hop) "IH". iIntros (vs) "#Hvs Htok". simpl.
    wp_bind (subst_map vs e). iApply (wp_wand with "[IH Htok]").
    { iApply ("IH" $! vs with "Hvs Htok"). }
    iIntros (v) "[#Hv Htok]".
    iEval (rewrite interp_unseal /=) in "Hv". iDestruct "Hv" as (s) "%". simplify_eq.
    destruct (unop_string_typed_safe Θ op s τ Hop) as [v' Heval].
    wp_pures; eauto. iModIntro. iFrame.
    destruct op; inversion Heval; simplify_eq/=.
    destruct (ZOfString s) eqn:Heq.
    - rewrite interp_un_sum_unfold. iExists _. iRight. iSplit; [done|].
      rewrite interp_unseal /=. iExists _. done.
    - rewrite interp_un_sum_unfold. iExists #(). iLeft. iSplit; [done|].
      rewrite interp_unseal /=. done.
    - rewrite interp_unseal /=. iExists _. done.
  Qed.

  Lemma un_log_related_unboxed_eq Θ Δ Γ e1 e2 τ :
    UnboxedType τ →
    ({Θ;Δ;Γ} ⊨ᵤ e1 : τ) -∗
    ({Θ;Δ;Γ} ⊨ᵤ e2 : τ) -∗
    {Θ;Δ;Γ} ⊨ᵤ BinOp EqOp e1 e2 : t_bool.
  Proof.
    iIntros (Hunboxed) "IH1 IH2". iIntros (vs) "#Hvs Htok". simpl.
    wp_bind (subst_map vs e2). iApply (wp_wand with "[IH2 Htok]").
    { iApply ("IH2" $! vs with "Hvs Htok"). }
    iIntros (v2) "[#Hv2 Htok]".
    wp_bind (subst_map vs e1). iApply (wp_wand with "[IH1 Htok]").
    { iApply ("IH1" $! vs with "Hvs Htok"). }
    iIntros (v1) "[#Hv1 Htok]".
    inversion Hunboxed; subst.
    - iEval (rewrite interp_unseal /=) in "Hv1".
      iEval (rewrite interp_unseal /=) in "Hv2".
      iEval (cbv [lrel_bi_un lrel_un_unit]) in "Hv1".
      iEval (cbv [lrel_bi_un lrel_un_unit]) in "Hv2".
      iDestruct "Hv1" as "%". iDestruct "Hv2" as "%". simplify_eq.
      wp_pures. iModIntro. iFrame. rewrite interp_unseal /=. iExists _. done.
    - iEval (rewrite interp_unseal /=) in "Hv1".
      iEval (rewrite interp_unseal /=) in "Hv2".
      iEval (cbv [lrel_bi_un lrel_un_int]) in "Hv1".
      iEval (cbv [lrel_bi_un lrel_un_int]) in "Hv2".
      iDestruct "Hv1" as (n1) "%". iDestruct "Hv2" as (n2) "%". simplify_eq.
      wp_pures. iModIntro. iFrame. rewrite interp_unseal /=. iExists _. done.
    - iEval (rewrite interp_unseal /=) in "Hv1".
      iEval (rewrite interp_unseal /=) in "Hv2".
      iEval (cbv [lrel_bi_un lrel_un_bool]) in "Hv1".
      iEval (cbv [lrel_bi_un lrel_un_bool]) in "Hv2".
      iDestruct "Hv1" as (b1) "%". iDestruct "Hv2" as (b2) "%". simplify_eq.
      wp_pures. iModIntro. iFrame. rewrite interp_unseal /=. iExists _. done.
  Qed.

  Lemma un_log_related_strindex Θ Δ Γ e1 e2 e3 :
    ({Θ;Δ;Γ} ⊨ᵤ e1 : t_nat) -∗
    ({Θ;Δ;Γ} ⊨ᵤ e2 : t_string) -∗
    ({Θ;Δ;Γ} ⊨ᵤ e3 : t_string) -∗
    {Θ;Δ;Γ} ⊨ᵤ strindex e1 e2 e3 : t_unit + t_nat.
  Proof.
    iIntros "IH1 IH2 IH3". iIntros (vs) "#Hvs Htok". simpl.
    wp_bind (subst_map vs e3). iApply (wp_wand with "[IH3 Htok]").
    { iApply ("IH3" $! vs with "Hvs Htok"). }
    iIntros (v3) "[#Hv3 Htok]".
    wp_bind (subst_map vs e2). iApply (wp_wand with "[IH2 Htok]").
    { iApply ("IH2" $! vs with "Hvs Htok"). }
    iIntros (v2) "[#Hv2 Htok]".
    wp_bind (subst_map vs e1). iApply (wp_wand with "[IH1 Htok]").
    { iApply ("IH1" $! vs with "Hvs Htok"). }
    iIntros (v1) "[#Hv1 Htok]".
    iEval (rewrite interp_unseal /=) in "Hv1".
    iEval (rewrite interp_unseal /=) in "Hv2".
    iEval (rewrite interp_unseal /=) in "Hv3".
    iDestruct "Hv1" as (n) "%". iDestruct "Hv2" as (s2) "%". iDestruct "Hv3" as (s3) "%".
    simplify_eq. wp_pures. iModIntro. iFrame.
    rewrite interp_un_sum_unfold.
    destruct (String.index (Z.to_nat n) s2 s3) eqn:Heq.
    - iExists _. iRight. iSplit; [done|]. rewrite interp_unseal /=. iExists _. done.
    - iExists #(). iLeft. iSplit; [done|]. rewrite interp_unseal /=. done.
  Qed.

  Lemma un_log_related_strsub Θ Δ Γ e1 e2 e3 :
    ({Θ;Δ;Γ} ⊨ᵤ e1 : t_nat) -∗
    ({Θ;Δ;Γ} ⊨ᵤ e2 : t_nat) -∗
    ({Θ;Δ;Γ} ⊨ᵤ e3 : t_string) -∗
    {Θ;Δ;Γ} ⊨ᵤ strsub e1 e2 e3 : t_string.
  Proof.
    iIntros "IH1 IH2 IH3". iIntros (vs) "#Hvs Htok". simpl.
    wp_bind (subst_map vs e3). iApply (wp_wand with "[IH3 Htok]").
    { iApply ("IH3" $! vs with "Hvs Htok"). }
    iIntros (v3) "[#Hv3 Htok]".
    wp_bind (subst_map vs e2). iApply (wp_wand with "[IH2 Htok]").
    { iApply ("IH2" $! vs with "Hvs Htok"). }
    iIntros (v2) "[#Hv2 Htok]".
    wp_bind (subst_map vs e1). iApply (wp_wand with "[IH1 Htok]").
    { iApply ("IH1" $! vs with "Hvs Htok"). }
    iIntros (v1) "[#Hv1 Htok]".
    iEval (rewrite interp_unseal /=) in "Hv1".
    iEval (rewrite interp_unseal /=) in "Hv2".
    iEval (rewrite interp_unseal /=) in "Hv3".
    iDestruct "Hv1" as (n1) "%". iDestruct "Hv2" as (n2) "%". iDestruct "Hv3" as (s) "%".
    simplify_eq. wp_pures.
    iModIntro. iFrame. rewrite interp_unseal /=. iExists _. done.
  Qed.

  Lemma un_log_related_pair Θ Δ Γ e1 e2 τ1 τ2 :
    ({Θ;Δ;Γ} ⊨ᵤ e1 : τ1) -∗
    ({Θ;Δ;Γ} ⊨ᵤ e2 : τ2) -∗
    {Θ;Δ;Γ} ⊨ᵤ Pair e1 e2 : t_prod τ1 τ2.
  Proof.
    iIntros "IH1 IH2". iIntros (vs) "#Hvs Htok". simpl.
    wp_bind (subst_map vs e2). iApply (wp_wand with "[IH2 Htok]").
    - iApply ("IH2" $! vs with "Hvs Htok").
    - iIntros (v2) "[#Hv2 Htok]".
      wp_bind (subst_map vs e1). iApply (wp_wand with "[IH1 Htok]").
      + iApply ("IH1" $! vs with "Hvs Htok").
      + iIntros (v1) "[#Hv1 Htok]".
        wp_pures. iModIntro. iFrame.
        rewrite interp_un_prod_unfold. iExists v1, v2. iFrame "#". done.
  Qed.

  Lemma un_log_related_fst Θ Δ Γ e τ1 τ2 :
    ({Θ;Δ;Γ} ⊨ᵤ e : t_prod τ1 τ2) -∗
    {Θ;Δ;Γ} ⊨ᵤ Fst e : τ1.
  Proof.
    iIntros "IH". iIntros (vs) "#Hvs Htok". simpl.
    wp_bind (subst_map vs e). iApply (wp_wand with "[IH Htok]").
    - iApply ("IH" $! vs with "Hvs Htok").
    - iIntros (v) "[#Hv Htok]".
      iEval (rewrite interp_un_prod_unfold) in "Hv".
      iDestruct "Hv" as (v1 v2 ->) "[#H1 #H2]".
      wp_pures. iModIntro. iFrame "#∗".
  Qed.

  Lemma un_log_related_snd Θ Δ Γ e τ1 τ2 :
    ({Θ;Δ;Γ} ⊨ᵤ e : t_prod τ1 τ2) -∗
    {Θ;Δ;Γ} ⊨ᵤ Snd e : τ2.
  Proof.
    iIntros "IH". iIntros (vs) "#Hvs Htok". simpl.
    wp_bind (subst_map vs e). iApply (wp_wand with "[IH Htok]").
    - iApply ("IH" $! vs with "Hvs Htok").
    - iIntros (v) "[#Hv Htok]".
      iEval (rewrite interp_un_prod_unfold) in "Hv".
      iDestruct "Hv" as (v1 v2 ->) "[#H1 #H2]".
      wp_pures. iModIntro. iFrame "#∗".
  Qed.

  Lemma un_log_related_injl Θ Δ Γ e τ1 τ2 :
    ({Θ;Δ;Γ} ⊨ᵤ e : τ1) -∗
    {Θ;Δ;Γ} ⊨ᵤ InjL e : t_sum τ1 τ2.
  Proof.
    iIntros "IH". iIntros (vs) "#Hvs Htok". simpl.
    wp_bind (subst_map vs e). iApply (wp_wand with "[IH Htok]").
    - iApply ("IH" $! vs with "Hvs Htok").
    - iIntros (v) "[#Hv Htok]".
      wp_pures. iModIntro. iFrame.
      rewrite interp_un_sum_unfold. iExists v. iLeft. iSplit; [done|iApply "Hv"].
  Qed.

  Lemma un_log_related_injr Θ Δ Γ e τ1 τ2 :
    ({Θ;Δ;Γ} ⊨ᵤ e : τ2) -∗
    {Θ;Δ;Γ} ⊨ᵤ InjR e : t_sum τ1 τ2.
  Proof.
    iIntros "IH". iIntros (vs) "#Hvs Htok". simpl.
    wp_bind (subst_map vs e). iApply (wp_wand with "[IH Htok]").
    - iApply ("IH" $! vs with "Hvs Htok").
    - iIntros (v) "[#Hv Htok]".
      wp_pures. iModIntro. iFrame.
      rewrite interp_un_sum_unfold. iExists v. iRight. iSplit; [done|iApply "Hv"].
  Qed.

  Lemma un_log_related_case Θ Δ Γ e0 e1 e2 τ1 τ2 τ3 :
    ({Θ;Δ;Γ} ⊨ᵤ e0 : t_sum τ1 τ2) -∗
    ({Θ;Δ;Γ} ⊨ᵤ e1 : t_arr τ1 τ3) -∗
    ({Θ;Δ;Γ} ⊨ᵤ e2 : t_arr τ2 τ3) -∗
    {Θ;Δ;Γ} ⊨ᵤ Case e0 e1 e2 : τ3.
  Proof.
    iIntros "IH0 IH1 IH2". iIntros (vs) "#Hvs Htok". simpl.
    wp_bind (subst_map vs e0). iApply (wp_wand with "[IH0 Htok]").
    { iApply ("IH0" $! vs with "Hvs Htok"). }
    iIntros (v) "[#Hv Htok]".
    iEval (rewrite interp_un_sum_unfold) in "Hv".
    iDestruct "Hv" as (w) "[(-> & #Hw)|(-> & #Hw)]"; wp_pures.
    - wp_bind (subst_map vs e1). iApply (wp_wand with "[IH1 Htok]").
      { iApply ("IH1" $! vs with "Hvs Htok"). }
      iIntros (f) "[#Hf Htok]".
      iEval (rewrite interp_un_arr_unfold) in "Hf".
      iApply ("Hf" with "Hw Htok").
    - wp_bind (subst_map vs e2). iApply (wp_wand with "[IH2 Htok]").
      { iApply ("IH2" $! vs with "Hvs Htok"). }
      iIntros (f) "[#Hf Htok]".
      iEval (rewrite interp_un_arr_unfold) in "Hf".
      iApply ("Hf" with "Hw Htok").
  Qed.

  Lemma un_log_related_if Θ Δ Γ e0 e1 e2 τ :
    ({Θ;Δ;Γ} ⊨ᵤ e0 : t_bool) -∗
    ({Θ;Δ;Γ} ⊨ᵤ e1 : τ) -∗
    ({Θ;Δ;Γ} ⊨ᵤ e2 : τ) -∗
    {Θ;Δ;Γ} ⊨ᵤ If e0 e1 e2 : τ.
  Proof.
    iIntros "IH0 IH1 IH2". iIntros (vs) "#Hvs Htok". simpl.
    wp_bind (subst_map vs e0). iApply (wp_wand with "[IH0 Htok]").
    - iApply ("IH0" $! vs with "Hvs Htok").
    - iIntros (v) "[#Hv Htok]".
      iEval (rewrite interp_unseal /=) in "Hv".
      iDestruct "Hv" as (b) "%". simplify_eq. destruct b; wp_pures.
      + iApply ("IH1" $! vs with "Hvs Htok").
      + iApply ("IH2" $! vs with "Hvs Htok").
  Qed.

  Lemma un_log_related_rec Θ Δ (Γ : stringmap (typ ⋆ Θ)) (f x : binder) (e : expr) τ1 τ2 :
    □ ({Θ;Δ;<[f:=t_arr τ1 τ2]>(<[x:=τ1]>Γ)} ⊨ᵤ e : τ2) -∗
    {Θ;Δ;Γ} ⊨ᵤ Rec f x e : t_arr τ1 τ2.
  Proof.
    iIntros "#IHun". iIntros (vs) "#Hvs Htok". simpl.
    wp_pures. iFrame.
    iLöb as "IHlob".
    iModIntro. rewrite interp_un_arr_unfold. iModIntro.
    iIntros (w) "#Hw Htok". wp_pures.
    iMod "IHlob" as "#IHlob".
    set rec1 := (rec: f x := subst_map (binder_delete x (binder_delete f vs)) e)%V.
    iSpecialize ("IHun" $! (binder_insert f rec1 (binder_insert x w vs))).
    rewrite -subst_map_binder_insert_2.
    iApply ("IHun" with "[#] Htok").
    rewrite !binder_insert_fmap.
    iApply (un_env_ltyped_insert with "[IHlob]").
    { rewrite interp_un_arr_unfold //. }
    iApply (un_env_ltyped_insert with "Hw Hvs").
  Qed.

  Lemma un_log_related_app Θ Δ Γ e1 e2 τ1 τ2 :
    ({Θ;Δ;Γ} ⊨ᵤ e1 : t_arr τ1 τ2) -∗
    ({Θ;Δ;Γ} ⊨ᵤ e2 : τ1) -∗
    {Θ;Δ;Γ} ⊨ᵤ App e1 e2 : τ2.
  Proof.
    iIntros "IH1 IH2". iIntros (vs) "#Hvs Htok". simpl.
    wp_bind (subst_map vs e2). iApply (wp_wand with "[IH2 Htok]").
    - iApply ("IH2" $! vs with "Hvs Htok").
    - iIntros (v2) "[#Hv2 Htok]".
      wp_bind (subst_map vs e1). iApply (wp_wand with "[IH1 Htok]").
      + iApply ("IH1" $! vs with "Hvs Htok").
      + iIntros (f) "[#Hf Htok]".
        iEval (rewrite interp_un_arr_unfold) in "Hf".
        iApply ("Hf" with "Hv2 Htok").
  Qed.

  Lemma un_log_related_tlam Θ (Δ : ctxO Σ Θ) Γ κ (e : expr) τ :
    (∀ A : kindO Σ κ, □ ({(Θ ▹ κ); (ext Δ A); ⤉Γ} ⊨ᵤ e : τ)) -∗
    {Θ;Δ;Γ} ⊨ᵤ (Λ: e) : ∀: κ, τ.
  Proof.
    iIntros "#IHun". iIntros (vs) "#Hvs Htok". simpl.
    wp_pures. iFrame. iModIntro.
    rewrite interp_un_forall_unfold. iIntros (A). iModIntro. iIntros (v) "_".
    iIntros "Htok". wp_pures.
    iSpecialize ("IHun" $! A).
    iApply ("IHun" $! vs with "[Hvs] Htok").
    rewrite -shift_env_un_eq. iApply "Hvs".
  Qed.

  Lemma un_log_related_tapp' Θ Δ κ Γ e τ τ' :
    ({Θ;Δ;Γ} ⊨ᵤ e : ∀: κ, τ) -∗
    {Θ;Δ;Γ} ⊨ᵤ e #~ : τ.[τ'/].
  Proof.
    iIntros "IH". iIntros (vs) "#Hvs Htok". simpl.
    wp_bind (subst_map vs e). iApply (wp_wand with "[IH Htok]").
    { iApply ("IH" $! vs with "Hvs Htok"). }
    iIntros (v) "[#Hv Htok]". fold kindO.
    iEval (rewrite interp_un_forall_unfold) in "Hv".
    iDestruct ("Hv" $! (interp τ' Δ)) as "#Hv'".
    iSpecialize ("Hv'" $! #~ with "[//]"). simpl. rewrite subst_eq.
    iApply ("Hv'" with "Htok").
  Qed.

  Lemma un_log_related_fold Θ Δ Γ e κ (τ : typ κ (Θ ▹ κ%kind)) (T : telim_ctx Θ κ ⋆) :
    ({Θ;Δ;Γ} ⊨ᵤ e : tfill T (τ.[μ: κ; τ/])) -∗
    {Θ;Δ;Γ} ⊨ᵤ rec_fold e : tfill T (μ: κ; τ).
  Proof.
    iIntros "IH". iIntros (vs) "#Hvs Htok". simpl.
    wp_bind (subst_map vs e). iApply (wp_wand with "[IH Htok]").
    { iApply ("IH" $! vs with "Hvs Htok"). }
    iIntros (v) "[#Hv Htok]". wp_rec. iFrame. rewrite tfill_rec_eq. iApply "Hv".
  Qed.

  Lemma un_log_related_unfold Θ Δ Γ e κ (τ : typ κ (Θ ▹ κ%kind)) (T : telim_ctx Θ κ ⋆) :
    ({Θ;Δ;Γ} ⊨ᵤ e : tfill T (μ: κ; τ)) -∗
    {Θ;Δ;Γ} ⊨ᵤ rec_unfold e : tfill T (τ.[μ: κ; τ/]).
  Proof.
    iIntros "IH". iIntros (vs) "#Hvs Htok". simpl.
    wp_bind (subst_map vs e). iApply (wp_wand with "[IH Htok]").
    { iApply ("IH" $! vs with "Hvs Htok"). }
    iIntros (v) "[#Hv Htok]". iEval (rewrite tfill_rec_eq) in "Hv". wp_rec. iFrame. iApply "Hv".
  Qed.

  Lemma un_log_related_pack' Θ κ Δ Γ e τ τ' :
    ({Θ;Δ;Γ} ⊨ᵤ e : τ.[τ'/]) -∗
    {Θ;Δ;Γ} ⊨ᵤ e : ∃: κ, τ.
  Proof.
    iIntros "IH". iIntros (vs) "#Hvs Htok". simpl.
    iApply (wp_wand with "[IH Htok]").
    - iApply ("IH" $! vs with "Hvs Htok").
    - iIntros (v) "[#Hv Htok]". fold kindO. iFrame.
      rewrite interp_un_exists_unfold. iExists (interp τ' Δ). simpl. rewrite subst_eq. iApply "Hv".
  Qed.

  Lemma un_log_related_unpack Θ κ Δ Γ x e1 e2 τ τ2 :
    ({Θ;Δ;Γ} ⊨ᵤ e1 : ∃: κ, τ) -∗
    (∀ A : kindO Σ κ,
      {Θ ▹ κ; ext Δ A; <[x:=τ]>(⤉Γ)} ⊨ᵤ e2 : Core.shift τ2) -∗
    {Θ;Δ;Γ} ⊨ᵤ (unpack: x := e1 in e2) : τ2.
  Proof.
    iIntros "IH1 IH2". iIntros (vs) "#Hvs Htok". simpl.
    rewrite /unpack. wp_pures.
    wp_bind (subst_map vs e1). iApply (wp_wand with "[IH1 Htok]").
    { iApply ("IH1" $! vs with "Hvs Htok"). }
    iIntros (v1) "[#Hex Htok]".
    iEval (rewrite interp_un_exists_unfold) in "Hex".
    iDestruct "Hex" as (A) "#HτA".
    wp_pures.
    iSpecialize ("IH2" $! A (binder_insert x v1 vs) with "[#]").
    { rewrite binder_insert_fmap -shift_env_un_eq.
      iApply (un_env_ltyped_insert with "HτA Hvs"). }
    rewrite subst_map_binder_insert /=.
    rewrite -(shift_eq τ2).
    iApply ("IH2" with "Htok").
  Qed.

  Lemma un_log_related_hash Θ Δ Γ e :
    ({Θ;Δ;Γ} ⊨ᵤ e : t_string) -∗
    {Θ;Δ;Γ} ⊨ᵤ Hash e : t_string.
  Proof.
    iIntros "IH". iIntros (vs) "#Hvs Htok". simpl.
    wp_bind (subst_map vs e). iApply (wp_wand with "[IH Htok]").
    - iApply ("IH" $! vs with "Hvs Htok").
    - iIntros (v) "[#Hv Htok]".
      iEval (rewrite interp_unseal /=) in "Hv".
      iDestruct "Hv" as (s) "%". simplify_eq.
      wp_apply wp_hash. done.
      iIntros "_". iFrame. iEval (rewrite interp_unseal /=). iExists (hash s). done.
  Qed.

  Lemma un_log_related_tequiv Θ Δ Γ e τ τ' :
    Θ ⊢ₑ τ ≃ τ' : ⋆ →
    ({Θ;Δ;Γ} ⊨ᵤ e : τ) -∗
    {Θ;Δ;Γ} ⊨ᵤ e : τ'.
  Proof.
    iIntros (Heq) "IH". iIntros (vs) "#Hvs".
    rewrite -(tequiv_eq _ _ _ Heq).
    iApply ("IH" with "Hvs").
  Qed.

  Theorem fundamental Θ Δ Γ e τ :
    Θ |ₜ Γ ⊢ₜ e : τ → ⊢ {Θ;Δ;Γ} ⊨ e ≤log≤ e : τ
    with fundamental_val Θ Δ v τ :
      Θ ⊢ᵥ v : τ → ⊢ interp τ Δ v v
    with fundamental_un Θ Δ Γ e τ :
      Θ |ₜ Γ ⊢ₜ e : τ → ⊢ {Θ;Δ;Γ} ⊨ᵤ e : τ.
  Proof.
    - intros Ht. destruct Ht.
      + by iApply bin_log_related_var.
      + iIntros (γ) "#H /=".
        iIntros (??) "(Hi & Htok)". wp_pures. iFrame.
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
        * iModIntro. by iApply fundamental.
        * iModIntro. by iApply fundamental_un.
      + iApply bin_log_related_app;
          by iApply fundamental.
      + iApply bin_log_related_tlam.
        * iIntros (A). iModIntro. by iApply fundamental.
        * iIntros (A). iModIntro. by iApply fundamental_un.
      + iApply bin_log_related_tapp'; by iApply fundamental.
      + iApply bin_log_related_fold; by iApply fundamental.
      + iApply bin_log_related_unfold; by iApply fundamental.
      + iApply bin_log_related_pack'; by iApply fundamental.
      + iApply bin_log_related_unpack; try by iApply fundamental.
        iIntros (A). by iApply fundamental.
      (* + iApply bin_log_related_fork; by iApply fundamental.
      + iApply bin_log_related_alloc; by iApply fundamental.
      + iApply bin_log_related_load; by iApply fundamental.
      + iApply bin_log_related_store; by iApply fundamental.
      + iApply bin_log_related_xchg; by iApply fundamental.
      + iApply bin_log_related_FAA; eauto;
          by iApply fundamental.
      + iApply bin_log_related_CmpXchg; eauto;
          by iApply fundamental. *)
      + iApply bin_log_related_hash; by iApply fundamental.
      + iApply bin_log_related_tequiv; [done|]. by iApply fundamental.
    - intros Hv. destruct Hv; simpl.
      (* VUnit *)
      + rewrite interp_unseal. iSplit; eauto.
      (* VBool *)
      + rewrite interp_unseal. iSplit; iExists _; eauto.
      (* VNat *)
      + rewrite interp_unseal. iSplit; iExists _; eauto.
      (* VString *)
      + rewrite interp_unseal. iSplit; iExists _; eauto.
      (* VPair: use from_exist_interp_t_prod (body contains full conjunction ⟦τi⟧Δ) *)
      + iExists v1, v1, v2, v2.
        iSplit; first done. iSplit; first done.
        iSplit; by iApply fundamental_val.
      (* VInjL *)
      + iExists v, v. iLeft.
        iSplit; first done. iSplit; first done.
        by iApply fundamental_val.
      (* VInjR *)
      + iExists v, v. iRight.
        iSplit; first done. iSplit; first done.
        by iApply fundamental_val.
      (* VRec: needs simultaneous Löb over binary + unary parts *)
      + (* TODO: the Löb env insert needs the full conjunction for the self-ref,
           requiring simultaneous binary + unary Löb. Needs unary FT. *)
        iLöb as "IH". iSplit.
        * rewrite interp_arr_unfold. iModIntro.
          iIntros (v1 v2) "#Hv".
          pose (Γ := (<[f:=(τ1 → τ2)%ty]> (<[x:=τ1]> ∅)):stringmap (typ ⋆ Θ)).
          pose (γ := (binder_insert f ((rec: f x := e)%V,(rec: f x := e)%V)
                      (binder_insert x (v1, v2) ∅)):stringmap (val*val)).
          iIntros (??) "[Hi Htok]". pures.
          iPoseProof (fundamental Θ Δ Γ e τ2 $! γ with "[] ") as "H"; eauto.
          { rewrite /γ /Γ. rewrite !binder_insert_fmap fmap_empty.
            iApply (env_ltyped_insert with "IH").
            iApply (env_ltyped_insert with "Hv").
            iApply env_ltyped_empty. }
          rewrite /γ /=. rewrite !binder_insert_fmap !fmap_empty /=.
          rewrite !subst_map_binder_insert_2_empty.
          iApply ("H" with "[$]").
        * iDestruct (lrel_bi_proj_un with "IH") as "#IH_un".
          rewrite interp_un_arr_unfold. iModIntro.
          iIntros (v1) "#Hv".
          pose (Γ := (<[f:=(τ1 → τ2)%ty]> (<[x:=τ1]> ∅)):stringmap (typ ⋆ Θ)).
          pose (γ := (binder_insert f ((rec: f x := e)%V)
                      (binder_insert x (v1) ∅)):stringmap (val)).
          iIntros "Htok". wp_pures.
          iPoseProof (fundamental_un Θ Δ Γ e τ2 $! γ with "[] ") as "H"; eauto.
          { rewrite /γ /Γ. rewrite !binder_insert_fmap fmap_empty.
            iApply (un_env_ltyped_insert with "[IH_un]").
            { by rewrite interp_un_arr_unfold. }
            iApply (un_env_ltyped_insert with "Hv").
            iApply un_env_ltyped_empty. }
          rewrite /γ /=.
          rewrite !subst_map_binder_insert_2_empty.
          iApply ("H" with "[$]").
      + iSplit.
        * rewrite interp_forall_unfold.
          iIntros (A). iModIntro. iIntros (v1 v2) "_".
          iIntros (??) "[Hi Htok]"; pures.
          iPoseProof (fundamental _ (ext Δ A) ∅ e τ $! ∅ with "[]") as "H"; eauto.
          { rewrite fmap_empty. iApply env_ltyped_empty. }
          rewrite !fmap_empty subst_map_empty.
          iApply ("H" with "[$]").
        * rewrite interp_un_forall_unfold.
          iIntros (A). iModIntro. iIntros (v1) "_".
          iIntros "Htok"; wp_pures.
          iPoseProof (fundamental_un _ (ext Δ A) ∅ e τ $! ∅ with "[]") as "H"; eauto.
          { rewrite fmap_empty. iApply un_env_ltyped_empty. }
          rewrite subst_map_empty.
          iApply ("H" with "[$]").
    - intros Ht. destruct Ht.
      (* Var *)
      + by iApply un_log_related_var.
      (* Val: project unary component from fundamental_val *)
      + iIntros (vs) "#Hvs". iIntros "Htok". simpl. wp_pures. iFrame.
        iApply (lrel_bi_proj_un with "[]"). by iApply fundamental_val.
      (* NatBinop *)
      + iApply un_log_related_nat_binop; first done; by iApply fundamental_un.
      (* BoolBinop *)
      + iApply un_log_related_bool_binop; first done; by iApply fundamental_un.
      (* NatUnop *)
      + iApply un_log_related_nat_unop; first done. by iApply fundamental_un.
      (* BoolUnop *)
      + iApply un_log_related_bool_unop; first done. by iApply fundamental_un.
      (* StringUnop *)
      + iApply un_log_related_string_unop; first done. by iApply fundamental_un.
      (* UnboxedEq *)
      + iApply un_log_related_unboxed_eq; try done; by iApply fundamental_un.
      (* Strindex *)
      + iApply un_log_related_strindex; try done; by iApply fundamental_un.
      (* Strsub *)
      + iApply un_log_related_strsub; try done; by iApply fundamental_un.
      (* Pair *)
      + iApply un_log_related_pair; by iApply fundamental_un.
      (* Fst *)
      + iApply un_log_related_fst; by iApply fundamental_un.
      (* Snd *)
      + iApply un_log_related_snd; by iApply fundamental_un.
      (* InjL *)
      + iApply un_log_related_injl; by iApply fundamental_un.
      (* InjR *)
      + iApply un_log_related_injr; by iApply fundamental_un.
      (* Case *)
      + iApply un_log_related_case; by iApply fundamental_un.
      (* If *)
      + iApply un_log_related_if; by iApply fundamental_un.
      (* Rec *)
      + iApply un_log_related_rec. iModIntro. by iApply fundamental_un.
      (* App *)
      + iApply un_log_related_app; by iApply fundamental_un.
      (* TLam *)
      + iApply un_log_related_tlam. iIntros (A). iModIntro. by iApply fundamental_un.
      (* TApp' *)
      + iApply un_log_related_tapp'; by iApply fundamental_un.
      (* Fold *)
      + iApply un_log_related_fold; by iApply fundamental_un.
      (* Unfold *)
      + iApply un_log_related_unfold; by iApply fundamental_un.
      (* Pack' *)
      + iApply un_log_related_pack'; by iApply fundamental_un.
      (* Unpack *)
      + iApply un_log_related_unpack; try by iApply fundamental_un.
        iIntros (A). by iApply fundamental_un.
      (* Hash *)
      + iApply un_log_related_hash; by iApply fundamental_un.
      (* TEquiv *)
      + iApply un_log_related_tequiv; [done|]. by iApply fundamental_un.
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
