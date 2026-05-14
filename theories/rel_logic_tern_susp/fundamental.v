(** Compatibility lemmas for the logical relation *)
From auth.heap_lang Require Import proofmode.
From auth.rel_logic_tern_susp Require Import model.
From auth.rel_logic_tern_susp Require Export compatibility interp.
From iris.proofmode Require Export proofmode.

Section fundamental.
  Context `{authG Σ, seqG Σ}.
  Hint Resolve to_of_val : core.

  Local Ltac intro_clause := progress (iIntros (vs) "#Hvs /=").
  Local Ltac intro_clause' := intro_clause; iIntros (????) "Hp Hi Htok".
  Local Ltac pures :=
    wp_pures; v_pures; i_pures.

  Local Tactic Notation "rel_bind_ap" uconstr(e1) uconstr(e2) uconstr(e3) constr(IH) ident(v) ident(w) ident(u) constr(H) :=
    wp_bind (subst_map _ e1); v_bind (subst_map _ e2); i_bind (subst_map _ e3);
    iSpecialize (IH with "[$] [$] [$] [$]");
    iApply wp_wand_r;
    iSplitL IH; [iApply IH|];
    iIntros (v); iDestruct 1 as (w u) H; simpl.

  Lemma tern_log_related_var Θ Δ Γ x τ :
    Γ !! x = Some τ →
    ⊢ {Θ;Δ;Γ} ⊨ Var x ≤log≤ Var x ≤log≤ Var x : τ.
  Proof.
    iIntros (Hx). intro_clause. simpl.
    rewrite (env_ltyped_lookup _ vs x); last first.
    { rewrite lookup_fmap Hx //. }
    rewrite !lookup_fmap.
    iDestruct "Hvs" as (v1 v2 v3 ->) "HA". simpl.
    iIntros (????) "Hp Hi Htok".
    wp_pures. by iFrame.
  Qed.

  Lemma tern_log_related_pair Θ Δ Γ e1 e2 e1' e2' e1'' e2'' τ1 τ2 :
    ({Θ;Δ;Γ} ⊨ e1 ≤log≤ e1' ≤log≤ e1'' : τ1) -∗
    ({Θ;Δ;Γ} ⊨ e2 ≤log≤ e2' ≤log≤ e2'' : τ2) -∗
    {Θ;Δ;Γ} ⊨ Pair e1 e2 ≤log≤ Pair e1' e2' ≤log≤ Pair e1'' e2'' : t_prod τ1 τ2.
  Proof.
    iIntros "IH1 IH2".
    intro_clause'.
    rel_bind_ap e2 e2' e2'' "IH2" v2 v2' v2'' "(Hp & Hi & #Hv & Htok)".
    rel_bind_ap e1 e1' e1'' "IH1" v1 v1' v1'' "(Hp & Hi & #Hw & Htok)".
    pures. iFrame. iModIntro.
    iDestruct "Hw" as "[#Hwtern [#Hwbin #Hwun]]".
    iDestruct "Hv" as "[#Hvtern [#Hvbin #Hvun]]".
    iSplit; [|iSplit].
    - rewrite interp_tern_prod_unfold. iExists v1, v1', v1'', v2, v2', v2''.
      do 3 (iSplit; [done|]). iFrame "#".
    - rewrite interp_bin_prod_unfold. iExists v1, v1'', v2, v2''.
      do 2 (iSplit; [done|]). iFrame "#".
    - rewrite interp_un_prod_unfold. iExists v1', v2'.
      iSplit; [done|]. iFrame "#".
  Qed.

  (* Lemma tern_log_related_fst Θ Δ Γ e e' e'' τ1 τ2 :
    ({Θ;Δ;Γ} ⊨ e ≤log≤ e' ≤log≤ e'' : τ1 * τ2) -∗
    {Θ;Δ;Γ} ⊨ Fst e ≤log≤ Fst e' ≤log≤ Fst e'' : τ1.
  Proof.
    iIntros "IH".
    intro_clause'.
    rel_bind_ap e e' e'' "IH" v w u "(Hp & Hi & H & Htok)".
    iDestruct "H" as "[Htern [Hbin Hun]]".
    iDestruct "Htern" as (a1 b1 c1 a2 b2 c2) "(-> & -> & -> & Ha & _)".
    iDestruct "Hbin" as (? ? ? ?) "(% & % & Habin & _)". simplify_eq.
    iDestruct "Hun" as (? ?) "(% & Haun & _)". simplify_eq.
    pures. by iFrame.
  Qed.

  Lemma tern_log_related_snd Θ Δ Γ e e' e'' τ1 τ2 :
    ({Θ;Δ;Γ} ⊨ e ≤log≤ e' ≤log≤ e'': τ1 * τ2) -∗
    {Θ;Δ;Γ} ⊨ Snd e ≤log≤ Snd e' ≤log≤ Snd e'' : τ2.
  Proof.
    iIntros "IH".
    intro_clause'.
    rel_bind_ap e e' e'' "IH" v w u "(Hp & Hi & H & Htok)".
    iDestruct "H" as "[Htern [Hbin Hun]]".
    iDestruct "Htern" as (a1 b1 c1 a2 b2 c2) "(-> & -> & -> & _ & Hb)".
    iDestruct "Hbin" as (? ? ? ?) "(% & % & _ & Hbbin)". simplify_eq.
    iDestruct "Hun" as (? ?) "(% & _ & Hbun)". simplify_eq.
    pures. by iFrame.
  Qed.

  Lemma tern_log_related_app Θ Δ Γ e1 e2 e1' e2' e1'' e2'' τ1 τ2 :
    ({Θ;Δ;Γ} ⊨ e1 ≤log≤ e1' ≤log≤ e1'' : τ1 → τ2) -∗
    ({Θ;Δ;Γ} ⊨ e2 ≤log≤ e2' ≤log≤ e2'' : τ1) -∗
    {Θ;Δ;Γ} ⊨ App e1 e2 ≤log≤ App e1' e2' ≤log≤ App e1'' e2'' :  τ2.
  Proof.
    iIntros "IH1 IH2".
    intro_clause'.
    rel_bind_ap e2 e2' e2'' "IH2" v v' v'' "(Hp & Hi & #Hv & Htok)".
    rel_bind_ap e1 e1' e1'' "IH1" f f' f'' "(Hp & Hi & #Hf & Htok)".
    iDestruct "Hf" as "[#Hftern _]".
    iApply ("Hftern" with "[$Hv] [$Hp] [$Hi] [$Htok]").
  Qed.

  Lemma tern_log_related_rec Θ Δ (Γ : stringmap (typ ⋆ Θ)) (f x : binder) (e e' e'' : expr) τ1 τ2 :
    □ ({Θ;Δ;<[f:=t_arr τ1 τ2]>(<[x:=τ1]>Γ)} ⊨ e ≤log≤ e' ≤log≤ e'' : τ2) -∗
    {Θ;Δ;Γ} ⊨ Rec f x e ≤log≤ Rec f x e' ≤log≤ Rec f x e'' : τ1 → τ2.
  Proof.
    iIntros "#Ht".
    intro_clause'.
    pures.
    iFrame. iModIntro. iLöb as "IH". iSplit; [|iSplit].
    - iIntros (v1 v2 v3) "!# #Hτ1".
      iIntros (????) "Hp Hi Htok". pures.
      set (r := (RecV f x (subst_map (binder_delete x (binder_delete f (fst ∘ fst <$> vs))) e),
                 RecV f x (subst_map (binder_delete x (binder_delete f (snd ∘ fst <$> vs))) e'),
                 RecV f x (subst_map (binder_delete x (binder_delete f (snd <$> vs))) e'')) : val * val * val).
      set (vvs' := binder_insert f r (binder_insert x (v1,v2,v3) vs)).
      iSpecialize ("Ht" $! vvs' with "[#]").
      { rewrite !binder_insert_fmap.
        iApply (env_ltyped_insert with "[IH]").
        - iApply "IH".
        - iApply (env_ltyped_insert with "Hτ1").
          by iFrame. }
      unfold vvs'.
      destruct x as [|x], f as [|f];
        rewrite /= ?fmap_insert ?subst_map_insert //;
          try by iApply ("Ht" with "[$] [$]").
      destruct (decide (x = f)) as [->|]; iSimpl in "Ht".
      + rewrite !delete_insert_delete !subst_subst !delete_idemp.
        by iApply ("Ht" with "[$] [$]").
      + rewrite !delete_insert_ne // subst_map_insert.
        rewrite !(subst_subst_ne _ x f) // !subst_map_insert.
        by iApply ("Ht" with "[$] [$]").
    - (* binary arrow: will be filled by fundamental_bin *) admit.
    - (* unary arrow: will be filled by fundamental_un *) admit.
  Admitted.

  (* Lemma tern_log_related_fork Θ Δ Γ e e' e'' :
    ({Θ;Δ;Γ} ⊨ e ≤log≤ e' ≤log≤ e'' : ()) -∗
    {Θ;Δ;Γ} ⊨ Fork e ≤log≤ Fork e' ≤log≤ Fork e'' : ().
  Proof.
    iIntros "IH".
    intro_clause.
    iApply refines_fork.
    by iApply "IH".
  Qed. *)

  Lemma tern_log_related_tlam Θ (Δ : ctxO Σ Θ) Γ κ (e e' e'' : expr) τ :
    (∀ (A : kindO Σ κ),
      □ ({(Θ ▹ κ); (ext Δ A); ⤉Γ} ⊨ e ≤log≤ e' ≤log≤ e'' : τ)) -∗
    {Θ;Δ;Γ} ⊨ (Λ: e) ≤log≤ (Λ: e') ≤log≤ (Λ: e'') : ∀: κ, τ.
  Proof.
    iIntros "#IH".
    intro_clause'; fold kindO.
    pures. iFrame. iModIntro.
    iSplit; [|iSplit].
    - iIntros (A) "!#". iIntros (v1 v2 v3) "_".
      iIntros (????) "Hp Hi Htok". pures.
      iDestruct ("IH" $! A) as "#H".
      iApply ("H" with "[Hvs] [$Hp] [$Hi] [$Htok]").
      rewrite -shift_env_eq_as_lrel //.
    - admit.
    - admit.
  Admitted.

  Lemma tern_log_related_tapp' Θ Δ κ Γ e e' e'' τ τ' :
    ({Θ;Δ;Γ} ⊨ e ≤log≤ e' ≤log≤ e'' : ∀: κ, τ) -∗
    {Θ;Δ;Γ} ⊨ e #~ ≤log≤ e' #~ ≤log≤ e'' #~ : τ.[τ'/].
  Proof.
    iIntros "IH".
    intro_clause'.
    rel_bind_ap e e' e'' "IH" v v' v'' "(Hp & Hi & IH & Htok)"; fold kindO.
    iDestruct "IH" as "[IHtern _]".
    iDestruct ("IHtern" $! (interp τ' Δ)) as "#IH".
    iSpecialize ("IH" $! #~ #~ #~ with "[//]").
    simpl.
    rewrite subst_eq.
    iApply ("IH" with "[$] [$] [$]").
  Qed.

  Lemma tern_log_related_tapp Θ Δ κ (A : kindO Σ κ) Γ e e' e'' τ :
    ({Θ;Δ;Γ} ⊨ e ≤log≤ e' ≤log≤ e'': ∀: κ, τ) -∗
    {Θ ▹ κ; ext Δ A; ⤉Γ} ⊨ e #~ ≤log≤ e' #~ ≤log≤ e'' #~ : τ.
  Proof.
    iIntros "IH". intro_clause'.
    rewrite -shift_env_eq_as_lrel /=.
    rel_bind_ap e e' e'' "IH" v v' v'' "(Hp & Hi & IH & Htok)"; fold kindO.
    iDestruct "IH" as "[IHtern _]".
    wp_apply ("IHtern" $! _ #~ #~ #~ with "[//] Hp Hi Htok").
  Qed.

  Lemma tern_log_related_seq Θ κ (A : kindO Σ κ) τ1 τ2 Δ Γ e1 e2 e1' e2' e1'' e2'' :
    ({Θ ▹ κ; ext Δ A; ⤉Γ} ⊨ e1 ≤log≤ e1' ≤log≤ e1'': τ1) -∗
    ({Θ;Δ;Γ} ⊨ e2 ≤log≤ e2' ≤log≤ e2'' : τ2) -∗
    {Θ;Δ;Γ} ⊨ (e1;; e2) ≤log≤ (e1';; e2') ≤log≤ (e1'';; e2'') : τ2.
  Proof.
    iIntros "He1 He2".
    intro_clause.
    iApply (refines_seq (lrel_tern_as_lrel (interp τ1 (ext Δ A))) with "[He1]").
    - iApply ("He1" with "[Hvs]"). rewrite -shift_env_eq_as_lrel //.
    - by iApply "He2".
  Qed.

  Lemma tern_log_related_seq' Θ Δ Γ e1 e2 e1' e2' e1'' e2'' τ1 τ2 :
    ({Θ;Δ;Γ} ⊨ e1 ≤log≤ e1' ≤log≤ e1'' : τ1) -∗
    ({Θ;Δ;Γ} ⊨ e2 ≤log≤ e2' ≤log≤ e2'' : τ2) -∗
    {Θ;Δ;Γ} ⊨ (e1;; e2) ≤log≤ (e1';; e2') ≤log≤ (e1'';; e2'') : τ2.
  Proof.
    iIntros "He1 He2".
    iApply (tern_log_related_seq _ ⋆ lrel_tern_true (Core.shift τ1 : typ _ _) with "[He1] He2").
    intro_clause.
    rewrite -shift_env_eq_as_lrel -shift_eq.
    by iApply "He1".
  Qed.

  Lemma tern_log_related_injl Θ Δ Γ e e' e'' τ1 τ2 :
    ({Θ;Δ;Γ} ⊨ e ≤log≤ e' ≤log≤ e'' : τ1) -∗
    {Θ;Δ;Γ} ⊨ InjL e ≤log≤ InjL e' ≤log≤ InjL e'' : τ1 + τ2.
  Proof.
    iIntros "IH".
    intro_clause'.
    rel_bind_ap e e' e'' "IH" v v' v'' "(? & ? & #H & Htok)".
    pures. iFrame. iModIntro.
    iDestruct "H" as "[#Htern [#Hbin #Hun]]".
    iSplit; [|iSplit].
    - rewrite interp_tern_sum_unfold. iExists v, v', v''. iLeft. do 3 (iSplit; [done|]). iFrame "#".
    - rewrite interp_bin_sum_unfold. iExists v, v''. iLeft. do 2 (iSplit; [done|]). iFrame "#".
    - rewrite interp_un_sum_unfold. iExists v'. iLeft. iSplit; [done|]. iFrame "#".
  Qed.

  Lemma tern_log_related_injr Θ Δ Γ e e' e'' τ1 τ2 :
    ({Θ;Δ;Γ} ⊨ e ≤log≤ e' ≤log≤ e'' : τ2) -∗
    {Θ;Δ;Γ} ⊨ InjR e ≤log≤ InjR e' ≤log≤ InjR e'' : τ1 + τ2.
  Proof.
    iIntros "IH".
    intro_clause'.
    rel_bind_ap e e' e'' "IH" v v' v'' "(? & ? & #Hvv & Htok)".
    pures. iFrame. iModIntro.
    iDestruct "Hvv" as "[#Htern [#Hbin #Hun]]".
    iSplit; [|iSplit].
    - rewrite interp_tern_sum_unfold. iExists v, v', v''. iRight. do 3 (iSplit; [done|]). iFrame "#".
    - rewrite interp_bin_sum_unfold. iExists v, v''. iRight. do 2 (iSplit; [done|]). iFrame "#".
    - rewrite interp_un_sum_unfold. iExists v'. iRight. iSplit; [done|]. iFrame "#".
  Qed.

  Lemma tern_log_related_case Θ Δ Γ e0 e1 e2 e0' e1' e2' e0'' e1'' e2'' τ1 τ2 τ3 :
    ({Θ;Δ;Γ} ⊨ e0 ≤log≤ e0' ≤log≤ e0'' : τ1 + τ2) -∗
    ({Θ;Δ;Γ} ⊨ e1 ≤log≤ e1' ≤log≤ e1'' : τ1 → τ3) -∗
    ({Θ;Δ;Γ} ⊨ e2 ≤log≤ e2' ≤log≤ e2'' : τ2 → τ3) -∗
    {Θ;Δ;Γ} ⊨ Case e0 e1 e2 ≤log≤ Case e0' e1' e2' ≤log≤ Case e0'' e1'' e2'' : τ3.
  Proof.
    iIntros "IH1 IH2 IH3".
    intro_clause'.
    rel_bind_ap e0 e0' e0'' "IH1" v0 v0' v'' "(Hp & Hi & IH1 & Htok)".
    rewrite interp_sum_combined.
    iDestruct "IH1" as (w w' w'') "[(% & % & % & #Hw) | (% & % & % & #Hw)]";
      simplify_eq/=; pures.
    - iApply (tern_log_related_app _ Δ Γ _ w _ w' _ w'' with "IH2 [] Hvs Hp Hi Htok").
      iIntros (?) "?". iIntros (????) "Hp Hi Htok".
      wp_pures. by iFrame.
    - iApply (tern_log_related_app _ Δ Γ _ w _ w' _ w'' with "IH3 [] Hvs Hp Hi Htok").
      iIntros (?) "?"; iIntros (????) "Hp Hi Htok".
      wp_pures. by iFrame.
  Qed.

  Lemma tern_log_related_if Θ Δ Γ e0 e1 e2 e0' e1' e2' e0'' e1'' e2'' τ :
    ({Θ;Δ;Γ} ⊨ e0 ≤log≤ e0' ≤log≤ e0'' : t_bool) -∗
    ({Θ;Δ;Γ} ⊨ e1 ≤log≤ e1' ≤log≤ e1'' : τ) -∗
    ({Θ;Δ;Γ} ⊨ e2 ≤log≤ e2' ≤log≤ e2'' : τ) -∗
    {Θ;Δ;Γ} ⊨ If e0 e1 e2 ≤log≤ If e0' e1' e2' ≤log≤ If e0'' e1'' e2'' : τ.
  Proof.
    iIntros "IH1 IH2 IH3".
    intro_clause'.
    rel_bind_ap e0 e0' e0'' "IH1" v0 v0' v0'' "(Hp & Hi & IH1 & Htok)".
    iDestruct "IH1" as "[IH1tern _]".
    iDestruct "IH1tern" as ([]) "(% & % & %)"; simplify_eq/=; pures.
    - by iApply ("IH2" with "[$] [$] [$]") .
    - by iApply ("IH3" with "[$] [$] [$]") .
  Qed.

  (* Lemma tern_log_related_load Θ Δ Γ e e' e'' τ :
    ({Θ;Δ;Γ} ⊨ e ≤log≤ e' ≤log≤ e'' : (ref τ)) -∗
    {Θ;Δ;Γ} ⊨ Load e ≤log≤ Load e' ≤log≤ Load e'' : τ.
  Proof.
    iIntros "IH".
    intro_clause.
    iApply refines_load.
    by iApply "IH".
  Qed.

  Lemma tern_log_related_store Θ Δ Γ e1 e2 e1' e2' e1'' e2'' τ :
    ({Θ;Δ;Γ} ⊨ e1 ≤log≤ e1' ≤log≤ e1'' : ref τ) -∗
    ({Θ;Δ;Γ} ⊨ e2 ≤log≤ e2' ≤log≤ e2'' : τ) -∗
    {Θ;Δ;Γ} ⊨ Store e1 e2 ≤log≤ Store e1' e2' ≤log≤ Store e1'' e2'' : ().
  Proof.
    iIntros "IH1 IH2".
    intro_clause.
    iApply (refines_store with "[IH1] [IH2]").
    - by iApply "IH1".
    - by iApply "IH2".
  Qed.

  Lemma tern_log_related_xchg Θ Δ Γ e1 e2 e1' e2' e1'' e2'' τ :
    ({Θ;Δ;Γ} ⊨ e1 ≤log≤ e1' ≤log≤ e1'' : ref τ) -∗
    ({Θ;Δ;Γ} ⊨ e2 ≤log≤ e2' ≤log≤ e2'' : τ) -∗
    {Θ;Δ;Γ} ⊨ Xchg e1 e2 ≤log≤ Xchg e1' e2' ≤log≤ Xchg e1'' e2'' : τ.
  Proof.
    iIntros "IH1 IH2".
    intro_clause.
    iApply (refines_xchg with "[IH1] [IH2]").
    - by iApply "IH1".
    - by iApply "IH2".
  Qed.

  Lemma tern_log_related_FAA Θ Δ Γ e1 e2 e1' e2' e1'' e2'' :
    ({Θ;Δ;Γ} ⊨ e1 ≤log≤ e1' ≤log≤ e1'' : ref t_nat) -∗
    ({Θ;Δ;Γ} ⊨ e2 ≤log≤ e2' ≤log≤ e2'' : t_nat) -∗
    {Θ;Δ;Γ} ⊨ FAA e1 e2 ≤log≤ FAA e1' e2' ≤log≤ FAA e1'' e2'' : t_nat.
  Proof.
    iIntros "IH1 IH2".
    intro_clause'.
    rel_bind_ap e2 e2' e2'' "IH2" v2 v2' v2'' "(Hp & Hi & IH2)".
    rel_bind_ap e1 e1' e1'' "IH1" v1 v1' v1'' "(Hp & Hi & IH1)".
    iDestruct "IH1" as (l l' l'') "(% & % & % & Hinv)"; simplify_eq/=.
    iDestruct "IH2" as (n) "(% & % & %)"; simplify_eq.
    iInv (authN .@ "ref" .@ (l,l',l'')) as (v1 v1' v1'') ">(Hv1 & Hv2 & Hv3 & (% & % & % & %))" "Hclose".
    simplify_eq.
    v_faa; i_faa. wp_faa.
    iMod ("Hclose" with "[$Hv1 $Hv2 $Hv3]") as "_"; [eauto|].
    iFrame. eauto.
  Qed.

  Lemma tern_log_related_CmpXchg_EqType Θ Δ Γ e1 e2 e3 e1' e2' e3' e1'' e2'' e3'' τ
    (HEqτ : EqType τ)
    (HUbτ : UnboxedType τ) :
    ({Θ;Δ;Γ} ⊨ e1 ≤log≤ e1' ≤log≤ e1'' : ref τ) -∗
    ({Θ;Δ;Γ} ⊨ e2 ≤log≤ e2' ≤log≤ e2'' : τ) -∗
    ({Θ;Δ;Γ} ⊨ e3 ≤log≤ e3' ≤log≤ e3'' : τ) -∗
    {Θ;Δ;Γ} ⊨ CmpXchg e1 e2 e3 ≤log≤ CmpXchg e1' e2' e3' ≤log≤ CmpXchg e1'' e2'' e3'' : τ * t_bool.
  Proof.
    iIntros "IH1 IH2 IH3".
    intro_clause'.
    rel_bind_ap e3 e3' e3'' "IH3" v3 v3' v3'' "(? & ? & #IH3)".
    rel_bind_ap e2 e2' e2'' "IH2" v2 v2' v2'' "(? & ? & #IH2)".
    rel_bind_ap e1 e1' e1'' "IH1" v1 v1' v1'' "(? & ? & #IH1)".
    iDestruct "IH1" as (l l' l'') "(% & % & % & Hinv)"; simplify_eq/=.
    iDestruct (unboxed_type_sound with "IH2") as "(% & % & %)"; try fast_done.
    iDestruct (eq_type_sound with "IH2") as "[<- <-]"; first fast_done.
    iDestruct (eq_type_sound with "IH3") as "[<- <-]"; first fast_done.
    iInv (authN .@ "ref" .@ (l,l',l'')) as (v v' v'') "(>Hv & >Hv' & >Hv'' & #H)" "Hclose".
    destruct (decide (v = v2)) as [|Hneq]; subst.
    - wp_cmpxchg_suc.
      iDestruct (eq_type_sound with "H") as "[<- <-]"; first fast_done.
      v_cmpxchg_suc; i_cmpxchg_suc.
      iMod ("Hclose" with "[$]") as "_".
      iFrame. iExists _, _, _, _, _, _. do 3 (iSplitL; [done|]).
      iSplitL; [done|]. eauto.
    - wp_cmpxchg_fail.
      iDestruct (eq_type_sound with "H") as "[<- <-]"; first fast_done.
      v_cmpxchg_fail; i_cmpxchg_fail.
      iMod ("Hclose" with "[$]") as "_".
      iFrame. iExists _, _, _, _, _, _. do 3 (iSplitL; [done|]).
      iSplitL; [done|]. eauto.
  Qed.

  Lemma tern_log_related_CmpXchg Θ Δ Γ e1 e2 e3 e1' e2' e3' e1'' e2'' e3'' τ
    (HUbτ : UnboxedType τ) :
    ({Θ;Δ;Γ} ⊨ e1 ≤log≤ e1' ≤log≤ e1'' : ref τ) -∗
    ({Θ;Δ;Γ} ⊨ e2 ≤log≤ e2' ≤log≤ e2'' : τ) -∗
    ({Θ;Δ;Γ} ⊨ e3 ≤log≤ e3' ≤log≤ e3'' : τ) -∗
    {Θ;Δ;Γ} ⊨ CmpXchg e1 e2 e3 ≤log≤ CmpXchg e1' e2' e3' ≤log≤ CmpXchg e1'' e2'' e3'' :  τ * t_bool.
  Proof.
    cut (EqType τ ∨ ∃ τ', τ = t_ref τ').
    { intros [Hτ | [τ' ->]].
      - by iApply tern_log_related_CmpXchg_EqType.
      - iIntros "H1 H2 H3". intro_clause.
        iSpecialize ("H1" with "Hvs").
        iSpecialize ("H2" with "Hvs").
        iSpecialize ("H3" with "Hvs").
        iApply (refines_cmpxchg_ref with "H1 H2 H3"). }
    by apply unboxed_type_ref_or_eqtype.
  Qed.

  Lemma tern_log_related_alloc Θ Δ Γ e e' e'' τ :
    ({Θ;Δ;Γ} ⊨ e ≤log≤ e' ≤log≤ e'' : τ) -∗
    {Θ;Δ;Γ} ⊨ Alloc e ≤log≤ Alloc e' ≤log≤ Alloc e'' : ref τ.
  Proof.
    iIntros "IH".
    intro_clause'.
    rel_bind_ap e e' e'' "IH" v v' v'' "(? & ? & IH)".
    v_alloc as lp "Hlp"; i_alloc as li "Hli"; wp_alloc l as "Hl".
    iMod (inv_alloc (authN .@ "ref" .@ (l,lp, li)) _ (∃ w1 w2 w3,
       l ↦ w1 ∗ lp ↦ᵥ w2 ∗ li ↦ᵢ w3 ∗ interp τ Δ w1 w2 w3)%I with "[$Hl $Hlp $Hli $IH]") as "HN".
    by iFrame.
  Qed. *)

  Lemma tern_log_related_unboxed_eq Θ Δ Γ e1 e2 e1' e2' e1'' e2'' τ :
    UnboxedType τ →
    ({Θ;Δ;Γ} ⊨ e1 ≤log≤ e1' ≤log≤ e1'' : τ) -∗
    ({Θ;Δ;Γ} ⊨ e2 ≤log≤ e2' ≤log≤ e2'' : τ) -∗
    {Θ;Δ;Γ} ⊨ BinOp EqOp e1 e2 ≤log≤ BinOp EqOp e1' e2' ≤log≤ BinOp EqOp e1'' e2'' : t_bool.
  Proof.
    iIntros (Hτ) "IH1 IH2".
    intro_clause'.
    rel_bind_ap e2 e2' e2'' "IH2" v2 v2' v2'' "(? & ? & #IH2 & Htok)".
    rel_bind_ap e1 e1' e1'' "IH1" v1 v1' v1'' "(? & ? & #IH1 & Htok)".
    iAssert (⌜val_is_unboxed v1⌝ ∧ ⌜val_is_unboxed v1'⌝ ∧ ⌜val_is_unboxed v1''⌝)%I as "(%&%&%)".
    { rewrite !unboxed_type_sound //.
      by iDestruct "IH1" as "(%&%&%)". }
    iAssert (⌜val_is_unboxed v2⌝ ∧ ⌜val_is_unboxed v2'⌝ ∧ ⌜val_is_unboxed v2''⌝)%I as "(%&%&%)".
    { rewrite !unboxed_type_sound //.
      by iDestruct "IH2" as "(%&%&%)". }
    iMod (unboxed_type_eq_1_2 with "IH1 IH2") as "%"; first done.
    iMod (unboxed_type_eq_2_3 with "IH1 IH2") as "%"; first done.
    v_pures; [solve_vals_compare_safe|].
    i_pures; [solve_vals_compare_safe|].
    wp_pures.
    iFrame. iModIntro.
    iSplit; [|iSplit].
    - do 3 case_bool_decide; naive_solver.
    - do 2 case_bool_decide; naive_solver.
    - case_bool_decide; naive_solver.
  Qed.

  Lemma tern_log_related_nat_binop Θ Δ Γ op e1 e2 e1' e2' e1'' e2'' τ :
    binop_nat_res_type op = Some τ →
    ({Θ;Δ;Γ} ⊨ e1 ≤log≤ e1' ≤log≤ e1'' : t_nat) -∗
    ({Θ;Δ;Γ} ⊨ e2 ≤log≤ e2' ≤log≤ e2'' : t_nat) -∗
    {Θ;Δ;Γ} ⊨ BinOp op e1 e2 ≤log≤ BinOp op e1' e2' ≤log≤ BinOp op e1'' e2'' : τ.
  Proof.
    iIntros (Hopτ) "IH1 IH2".
    intro_clause'.
    rel_bind_ap e2 e2' e2'' "IH2" v2 v2' v2'' "(?&?&IH2&Htok)".
    rel_bind_ap e1 e1' e1'' "IH1" v1 v1' v1'' "(?&?&IH1&Htok)".
    iDestruct "IH1" as "[IH1 _]".
    iDestruct "IH2" as "[IH2 _]".
    iDestruct "IH1" as (n) "(% & % & %)"; simplify_eq/=.
    iDestruct "IH2" as (n') "(% & % & %)"; simplify_eq/=.
    destruct (binop_nat_typed_safe _ op n n' _ Hopτ) as [v' Hopv'].
    v_pures; eauto; i_pures; eauto; wp_pures.
    iFrame. iModIntro.
    iSplit; [|iSplit];
      destruct op; inversion Hopv'; simplify_eq/=; try case_match; eauto.
  Qed.

  Lemma tern_log_related_bool_binop Θ Δ Γ op e1 e2 e1' e2' e1'' e2'' τ :
    binop_bool_res_type op = Some τ →
    ({Θ;Δ;Γ} ⊨ e1 ≤log≤ e1' ≤log≤ e1'' : t_bool) -∗
    ({Θ;Δ;Γ} ⊨ e2 ≤log≤ e2' ≤log≤ e2'' : t_bool) -∗
    {Θ;Δ;Γ} ⊨ BinOp op e1 e2 ≤log≤ BinOp op e1' e2' ≤log≤ BinOp op e1'' e2'' : τ.
  Proof.
    iIntros (Hopτ) "IH1 IH2".
    intro_clause'.
    rel_bind_ap e2 e2' e2'' "IH2" v2 v2' v3'' "(?&?&IH2&Htok)".
    rel_bind_ap e1 e1' e1'' "IH1" v1 v1' v1'' "(?&?&IH1&Htok)".
    iDestruct "IH1" as "[IH1 _]".
    iDestruct "IH2" as "[IH2 _]".
    iDestruct "IH1" as (n) "(% & % & %)"; simplify_eq/=.
    iDestruct "IH2" as (n') "(% & % & %)"; simplify_eq/=.
    destruct (binop_bool_typed_safe _ op n n' _ Hopτ) as [v' Hopv'].
    v_pures; eauto; i_pures; eauto; wp_pures. iFrame. iModIntro.
    iSplit; [|iSplit];
      destruct op; inversion Hopv'; simplify_eq/=; eauto.
  Qed.

  Lemma tern_log_related_strindex Θ Δ Γ e1 e2 e3 e1' e2' e3' e1'' e2'' e3'' :
    ({Θ;Δ;Γ} ⊨ e1 ≤log≤ e1' ≤log≤ e1'' : t_nat) -∗
    ({Θ;Δ;Γ} ⊨ e2 ≤log≤ e2' ≤log≤ e2'' : t_string) -∗
    ({Θ;Δ;Γ} ⊨ e3 ≤log≤ e3' ≤log≤ e3'' : t_string) -∗
    {Θ; Δ; Γ} ⊨ strindex e1 e2 e3 ≤log≤ strindex e1' e2' e3' ≤log≤ strindex e1'' e2'' e3'' : t_unit + t_nat.
  Proof.
    iIntros "IH1 IH2 IH3".
    intro_clause'.
    rel_bind_ap e3 e3' e3'' "IH3" v3 v3' v3'' "(?&?&IH3&Htok)".
    rel_bind_ap e2 e2' e2'' "IH2" w2 w2' w3'' "(?&?&IH2&Htok)".
    rel_bind_ap e1 e1' e1'' "IH1" u1 u1' u1'' "(?&?&IH1&Htok)".
    iDestruct "IH1" as "[IH1 _]".
    iDestruct "IH2" as "[IH2 _]".
    iDestruct "IH3" as "[IH3 _]".
    iDestruct "IH1" as (n) "(% & % & %)"; simplify_eq/=.
    iDestruct "IH2" as (s) "(% & % & %)"; simplify_eq/=.
    iDestruct "IH3" as (s') "(% & % & %)"; simplify_eq/=.
    pures.
    iFrame. iModIntro.
    iSplit; [|iSplit];
      destruct (String.index _ _ _) => /=; eauto 12.
  Qed.

  Lemma tern_log_related_strsub Θ Δ Γ e1 e2 e3 e1' e2' e3' e1'' e2'' e3'' :
    ({Θ;Δ;Γ} ⊨ e1 ≤log≤ e1' ≤log≤ e1'' : t_nat) -∗
    ({Θ;Δ;Γ} ⊨ e2 ≤log≤ e2' ≤log≤ e2'' : t_nat) -∗
    ({Θ;Δ;Γ} ⊨ e3 ≤log≤ e3' ≤log≤ e3'' : t_string) -∗
    {Θ; Δ; Γ} ⊨ strsub e1 e2 e3 ≤log≤ strsub e1' e2' e3' ≤log≤ strsub e1'' e2'' e3'' : t_string.
  Proof.
    iIntros "IH1 IH2 IH3".
    intro_clause'.
    rel_bind_ap e3 e3' e3'' "IH3" v3 v3' v3'' "(?&?&IH3&Htok)".
    rel_bind_ap e2 e2' e2'' "IH2" w2 w2' w3'' "(?&?&IH2&Htok)".
    rel_bind_ap e1 e1' e1'' "IH1" u1 u1' u1'' "(?&?&IH1&Htok)".
    iDestruct "IH1" as "[IH1 _]".
    iDestruct "IH2" as "[IH2 _]".
    iDestruct "IH3" as "[IH3 _]".
    iDestruct "IH1" as (n) "(% & % & %)"; simplify_eq/=.
    iDestruct "IH2" as (s) "(% & % & %)"; simplify_eq/=.
    iDestruct "IH3" as (s') "(% & % & %)"; simplify_eq/=.
    pures. iFrame. iModIntro. iSplit; [|iSplit]; eauto.
  Qed.

  Lemma tern_log_related_nat_unop Θ Δ Γ op e e' e'' τ :
    unop_nat_res_type op = Some τ →
    ({Θ;Δ;Γ} ⊨ e ≤log≤ e' ≤log≤ e'' : t_nat) -∗
    {Θ;Δ;Γ} ⊨ UnOp op e ≤log≤ UnOp op e' ≤log≤ UnOp op e'' : τ.
  Proof.
    iIntros (Hopτ) "IH".
    intro_clause'.
    rel_bind_ap e e' e'' "IH" v v' v'' "(? & ? & IH & Htok)".
    iDestruct "IH" as "[IH _]".
    iDestruct "IH" as (n) "(% & % & %)"; simplify_eq/=.
    destruct (unop_nat_typed_safe _ op n _ Hopτ) as [v' Hopv'].
    v_pures; eauto; i_pures; eauto; wp_pures. iFrame. iModIntro.
    iSplit; [|iSplit];
      destruct op; inversion Hopv'; simplify_eq/=; try case_match; eauto.
  Qed.

  Lemma tern_log_related_bool_unop Θ Δ Γ op e e' e'' τ :
    unop_bool_res_type op = Some τ →
    ({Θ;Δ;Γ} ⊨ e ≤log≤ e' ≤log≤ e'' : t_bool) -∗
    {Θ;Δ;Γ} ⊨ UnOp op e ≤log≤ UnOp op e' ≤log≤ UnOp op e'' : τ.
  Proof.
    iIntros (Hopτ) "IH".
    intro_clause'.
    rel_bind_ap e e' e'' "IH" v v' v'' "(? & ? & IH & Htok)".
    iDestruct "IH" as "[IH _]".
    iDestruct "IH" as (n) "(% & % & %)"; simplify_eq/=.
    destruct (unop_bool_typed_safe _ op n _ Hopτ) as [v' Hopv'].
    v_pures; eauto; i_pures; eauto; wp_pures. iFrame. iModIntro.
    iSplit; [|iSplit];
      destruct op; inversion Hopv'; simplify_eq/=; try case_match; eauto.
  Qed.

  Lemma tern_log_related_string_unop Θ Δ Γ op e e' e'' τ :
    unop_string_res_type op = Some τ →
    ({Θ;Δ;Γ} ⊨ e ≤log≤ e' ≤log≤ e'' : t_string) -∗
    {Θ;Δ;Γ} ⊨ UnOp op e ≤log≤ UnOp op e' ≤log≤ UnOp op e'' : τ.
  Proof.
    iIntros (Hopτ) "IH".
    intro_clause'.
    rel_bind_ap e e' e'' "IH" v v' v'' "(? & ? & IH & Htok)".
    iDestruct "IH" as "[IH _]".
    iDestruct "IH" as (s) "(% & % & %)"; simplify_eq/=.
    destruct (unop_string_typed_safe _ op s _ Hopτ) as [v' Hopv'].
    v_pures; eauto; i_pures; eauto; wp_pures. iFrame. iModIntro.
    iSplit; [|iSplit];
      destruct op; inversion Hopv'; simplify_eq/=; try case_match; eauto 12.
  Qed.

  Lemma tern_log_related_unfold Θ Δ Γ e e' e'' κ (τ : typ κ (Θ ▹ κ%kind)) (T : telim_ctx Θ κ ⋆) :
    ({Θ;Δ;Γ} ⊨ e ≤log≤ e' ≤log≤ e'' : tfill T (μ: κ; τ)) -∗
    {Θ;Δ;Γ} ⊨ rec_unfold e ≤log≤ rec_unfold e' ≤log≤ rec_unfold e'' : tfill T τ.[μ: κ; τ/].
  Proof.
    iIntros "IH".
    intro_clause'.
    rel_bind_ap e e' e'' "IH" v v' v'' "(? & ? & IH & Htok)".
    rewrite tfill_rec_eq.
    rewrite /rec_unfold. pures. simpl.
    by iFrame.
  Qed.

  Lemma tern_log_related_fold Θ Δ Γ e e' e'' κ (τ : typ κ (Θ ▹ κ%kind)) (T : telim_ctx Θ κ ⋆) :
    ({Θ;Δ;Γ} ⊨ e ≤log≤ e' ≤log≤ e'' : tfill T (τ.[μ: κ; τ/])) -∗
    {Θ;Δ;Γ} ⊨ rec_fold e ≤log≤ rec_fold e' ≤log≤ rec_fold e'' : tfill T (μ: κ; τ).
  Proof.
    iIntros "IH".
    intro_clause'.
    rel_bind_ap e e' e'' "IH" v v' v'' "(?&?&IH&Htok)".
    rewrite /rec_fold.
    wp_pures. v_pures. i_pures.
    iFrame.
    rewrite tfill_rec_eq /=.
    iModIntro. iDestruct "IH" as "[IH1 [IH2 IH3]]".
    iSplit; [|iSplit]; iNext; iFrame.
  Qed.

  Lemma tern_log_related_pack' Θ κ Δ Γ e e' e'' τ τ' :
    ({Θ;Δ;Γ} ⊨ e ≤log≤ e' ≤log≤ e'' : τ.[τ'/]) -∗
    {Θ;Δ;Γ} ⊨ e ≤log≤ e' ≤log≤ e'' : ∃: κ, τ.
  Proof.
    iIntros "IH".
    intro_clause'; fold kindO.
    rel_bind_ap e e' e'' "IH" v v' v'' "(? & ? & #IH & Htok)".
    iFrame.
    iDestruct "IH" as "[IH1 [IH2 IH3]]".
    iSplit; [|iSplit]; iExists (interp τ' Δ) => /=; rewrite subst_eq //;
      iSplit; [|iSplit]; iFrame "#".
  Qed.

  Lemma tern_log_related_pack κ (A : kindO Σ κ) Θ Δ Γ e e' e'' τ :
    ({Θ ▹ κ; ext Δ A; ⤉ Γ} ⊨ e ≤log≤ e' ≤log≤ e'' : τ) -∗
    {Θ;Δ;Γ} ⊨ e ≤log≤ e' ≤log≤e'' : ∃: κ, τ.
  Proof.
    iIntros "IH".
    intro_clause'.
    iSpecialize ("IH" with "[Hvs]"); fold kindO.
    { rewrite -shift_env_eq_as_lrel //. }
    iSpecialize ("IH" with "Hp Hi Htok").
    iApply wp_wand_r.
    iSplitL "IH"; [iApply "IH"|].
    iIntros (?) "(% & % & $ & $ & IH & $)".
    iDestruct "IH" as "[IH1 [IH2 IH3]]".
    iSplit; [|iSplit]; iExists A => /=; iFrame "#∗".
  Qed.

  Lemma tern_log_related_unpack Θ κ Δ Γ x e1 e1' e2 e2' e1'' e2'' τ τ2 :
    ({Θ;Δ;Γ} ⊨ e1 ≤log≤ e1' ≤log≤ e1'' : ∃: κ, τ) -∗
    (∀ A : kindO Σ κ,
      {Θ ▹ κ; ext Δ A; <[x:=τ]>(⤉Γ)} ⊨
        e2 ≤log≤ e2' ≤log≤ e2'' : Core.shift τ2) -∗
    {Θ;Δ;Γ} ⊨ (unpack: x := e1 in e2) ≤log≤ (unpack: x := e1' in e2') ≤log≤ (unpack: x := e1'' in e2'') : τ2.
  Proof.
    iIntros "IH1 IH2".
    intro_clause'.
    pures.
    rel_bind_ap e1 e1' e1'' "IH1" v v' v'' "(? & ? & #IH1 & Htok)"; rewrite -/interp.
    iDestruct "IH1" as "[IH1 _]". iDestruct "IH1" as (A) "#IH1".
    rewrite /unpack; pures.
    iSpecialize ("IH2" $! A (binder_insert x (v,v', v'') vs) with "[Hvs]").
    { rewrite shift_env_eq_as_lrel.
      rewrite binder_insert_fmap.
      iApply (env_ltyped_insert with "IH1 Hvs"). }
    rewrite !binder_insert_fmap !subst_map_binder_insert /=.
    rewrite -(shift_eq τ2).
    iApply ("IH2" with "[$] [$] [$]").
  Qed.

  Lemma tern_log_related_hash Θ Δ Γ e e' e'' :
    ({Θ; Δ; Γ} ⊨ e ≤log≤ e' ≤log≤ e'' : t_string) -∗
    {Θ; Δ; Γ} ⊨ Hash e ≤log≤ Hash e' ≤log≤ Hash e'' : t_string.
  Proof.
    iIntros "IH".
    intro_clause'.
    rel_bind_ap e e' e'' "IH" v v' v'' "([#Hctx Hp] & [_ Hi] & IH & Htok)".
    iDestruct "IH" as "[Htern _]". iDestruct "Htern" as (?) "(%&%&%)". simplify_eq.
    iMod (step_verifier_hash with "[$]") as "Hv"; [done|].
    iMod (step_ideal_hash with "[$]") as "Hi"; [done|].
    wp_apply (wp_hash with "[$]").
    iIntros "_". iFrame. iSplit; [|iSplit]; iExists _; eauto.
  Qed.

  Lemma tern_log_related_tequiv Θ Δ Γ e e' e'' τ τ' :
    Θ ⊢ₑ τ ≃ τ' : ⋆ →
    ({Θ; Δ; Γ} ⊨ e ≤log≤ e' ≤log≤ e'' : τ) -∗
    ({Θ; Δ; Γ} ⊨ e ≤log≤ e' ≤log≤ e'' : τ').
  Proof.
    iIntros (?) "IH".
    iIntros (?) "?".
    rewrite tequiv_eq //.
    iApply ("IH" with "[$]").
  Qed.

  (** * Unary compatibility lemmas (verifier) *)

  Lemma un_log_related_var Θ Δ Γ x τ :
    Γ !! x = Some τ →
    ⊢ {Θ;Δ;Γ} ⊨ᵤ Var x : τ.
  Proof.
    iIntros (Hx). iIntros (vs) "#Hvs".
    iDestruct (big_sepM2_lookup_l _ _ _ x (lrel_tern_un (interp τ Δ)) with "Hvs") as (v Hvl) "#Hτv".
    { rewrite lookup_fmap Hx //. }
    iIntros (??) "Hvst Htok". simpl. rewrite Hvl /=.
    iModIntro. iExists v. iFrame "# ∗".
  Qed.

  Lemma un_log_related_nat_binop Θ Δ Γ op e1 e2 τ :
    binop_nat_res_type op = Some τ →
    ({Θ;Δ;Γ} ⊨ᵤ e1 : t_nat) -∗
    ({Θ;Δ;Γ} ⊨ᵤ e2 : t_nat) -∗
    {Θ;Δ;Γ} ⊨ᵤ BinOp op e1 e2 : τ.
  Proof.
    iIntros (Hop) "IH1 IH2". iIntros (vs) "#Hvs". iIntros (??) "Hv Htok". simpl.
    v_bind (subst_map vs e2).
    iMod ("IH2" $! vs with "Hvs Hv Htok") as (v2) "(Hv & #Hv2 & Htok)". simpl.
    v_bind (subst_map vs e1).
    iMod ("IH1" $! vs with "Hvs Hv Htok") as (v1) "(Hv & #Hv1 & Htok)". simpl.
    iDestruct "Hv1" as (n1) "%". iDestruct "Hv2" as (n2) "%". simplify_eq.
    destruct (binop_nat_typed_safe Θ op n1 n2 τ Hop) as [v' Heval].
    v_pures; eauto. iModIntro. iExists _. iFrame.
    destruct op; inversion Heval; simplify_eq/=; iExists _; done.
  Qed.

  Lemma un_log_related_bool_binop Θ Δ Γ op e1 e2 τ :
    binop_bool_res_type op = Some τ →
    ({Θ;Δ;Γ} ⊨ᵤ e1 : t_bool) -∗
    ({Θ;Δ;Γ} ⊨ᵤ e2 : t_bool) -∗
    {Θ;Δ;Γ} ⊨ᵤ BinOp op e1 e2 : τ.
  Proof.
    iIntros (Hop) "IH1 IH2". iIntros (vs) "#Hvs". iIntros (??) "Hv Htok". simpl.
    v_bind (subst_map vs e2).
    iMod ("IH2" $! vs with "Hvs Hv Htok") as (v2) "(Hv & #Hv2 & Htok)". simpl.
    v_bind (subst_map vs e1).
    iMod ("IH1" $! vs with "Hvs Hv Htok") as (v1) "(Hv & #Hv1 & Htok)". simpl.
    iDestruct "Hv1" as (b1) "%". iDestruct "Hv2" as (b2) "%". simplify_eq.
    destruct (binop_bool_typed_safe Θ op b1 b2 τ Hop) as [v' Heval].
    v_pures; eauto. iModIntro. iExists _. iFrame.
    destruct op; inversion Heval; simplify_eq/=; iExists _; done.
  Qed.

  Lemma un_log_related_nat_unop Θ Δ Γ op e τ :
    unop_nat_res_type op = Some τ →
    ({Θ;Δ;Γ} ⊨ᵤ e : t_nat) -∗
    {Θ;Δ;Γ} ⊨ᵤ UnOp op e : τ.
  Proof.
    iIntros (Hop) "IH". iIntros (vs) "#Hvs". iIntros (??) "Hv Htok". simpl.
    v_bind (subst_map vs e).
    iMod ("IH" $! vs with "Hvs Hv Htok") as (v) "(Hv & #Hval & Htok)". simpl.
    iDestruct "Hval" as (n) "%". simplify_eq.
    destruct (unop_nat_typed_safe Θ op n τ Hop) as [v' Heval].
    v_pures; eauto. iModIntro. iExists _. iFrame.
    destruct op; inversion Heval; simplify_eq/=; iExists _; done.
  Qed.

  Lemma un_log_related_bool_unop Θ Δ Γ op e τ :
    unop_bool_res_type op = Some τ →
    ({Θ;Δ;Γ} ⊨ᵤ e : t_bool) -∗
    {Θ;Δ;Γ} ⊨ᵤ UnOp op e : τ.
  Proof.
    iIntros (Hop) "IH". iIntros (vs) "#Hvs". iIntros (??) "Hv Htok". simpl.
    v_bind (subst_map vs e).
    iMod ("IH" $! vs with "Hvs Hv Htok") as (v) "(Hv & #Hval & Htok)". simpl.
    iDestruct "Hval" as (b) "%". simplify_eq.
    destruct (unop_bool_typed_safe Θ op b τ Hop) as [v' Heval].
    v_pures; eauto. iModIntro. iExists _. iFrame.
    destruct op; inversion Heval; simplify_eq/=; iExists _; done.
  Qed.

  Lemma un_log_related_string_unop Θ Δ Γ op e τ :
    unop_string_res_type op = Some τ →
    ({Θ;Δ;Γ} ⊨ᵤ e : t_string) -∗
    {Θ;Δ;Γ} ⊨ᵤ UnOp op e : τ.
  Proof.
    iIntros (Hop) "IH". iIntros (vs) "#Hvs". iIntros (??) "Hv Htok". simpl.
    v_bind (subst_map vs e).
    iMod ("IH" $! vs with "Hvs Hv Htok") as (v) "(Hv & #Hval & Htok)". simpl.
    iDestruct "Hval" as (s) "%". simplify_eq.
    destruct (unop_string_typed_safe Θ op s τ Hop) as [v' Heval].
    v_pures; eauto. iModIntro. iExists _. iFrame.
    destruct op; inversion Heval; simplify_eq/=.
    destruct (ZOfString s) eqn:Heq.
    - rewrite interp_un_sum_unfold. iExists _. iRight. iSplit; [done|].
      iExists _. done.
    - rewrite interp_un_sum_unfold. iExists #(). iLeft. iSplit; [done|]. done.
    - iExists _. done.
  Qed.

  Lemma un_log_related_unboxed_eq Θ Δ Γ e1 e2 τ :
    UnboxedType τ →
    ({Θ;Δ;Γ} ⊨ᵤ e1 : τ) -∗
    ({Θ;Δ;Γ} ⊨ᵤ e2 : τ) -∗
    {Θ;Δ;Γ} ⊨ᵤ BinOp EqOp e1 e2 : t_bool.
  Proof.
    iIntros (Hunboxed) "IH1 IH2". iIntros (vs) "#Hvs". iIntros (??) "Hv Htok". simpl.
    v_bind (subst_map vs e2).
    iMod ("IH2" $! vs with "Hvs Hv Htok") as (v2) "(Hv & #Hv2 & Htok)". simpl.
    v_bind (subst_map vs e1).
    iMod ("IH1" $! vs with "Hvs Hv Htok") as (v1) "(Hv & #Hv1 & Htok)". simpl.
    inversion Hunboxed; subst.
    - iDestruct "Hv1" as "%". iDestruct "Hv2" as "%". simplify_eq.
      v_pures. iModIntro. iExists _. iFrame. iExists _. done.
    - iDestruct "Hv1" as (n1) "%". iDestruct "Hv2" as (n2) "%". simplify_eq.
      v_pures. iModIntro. iExists _. iFrame. iExists _. done.
    - iDestruct "Hv1" as (b1) "%". iDestruct "Hv2" as (b2) "%". simplify_eq.
      v_pures. iModIntro. iExists _. iFrame. iExists _. done.
  Qed.

  Lemma un_log_related_strindex Θ Δ Γ e1 e2 e3 :
    ({Θ;Δ;Γ} ⊨ᵤ e1 : t_nat) -∗
    ({Θ;Δ;Γ} ⊨ᵤ e2 : t_string) -∗
    ({Θ;Δ;Γ} ⊨ᵤ e3 : t_string) -∗
    {Θ;Δ;Γ} ⊨ᵤ strindex e1 e2 e3 : t_unit + t_nat.
  Proof.
    iIntros "IH1 IH2 IH3". iIntros (vs) "#Hvs". iIntros (??) "Hv Htok". simpl.
    v_bind (subst_map vs e3).
    iMod ("IH3" $! vs with "Hvs Hv Htok") as (v3) "(Hv & #Hv3 & Htok)". simpl.
    v_bind (subst_map vs e2).
    iMod ("IH2" $! vs with "Hvs Hv Htok") as (v2) "(Hv & #Hv2 & Htok)". simpl.
    v_bind (subst_map vs e1).
    iMod ("IH1" $! vs with "Hvs Hv Htok") as (v1) "(Hv & #Hv1 & Htok)". simpl.
    iDestruct "Hv1" as (n) "%". iDestruct "Hv2" as (s2) "%". iDestruct "Hv3" as (s3) "%".
    simplify_eq. v_pures. iModIntro. iExists _. iFrame.
    rewrite interp_un_sum_unfold.
    destruct (String.index (Z.to_nat n) s2 s3) eqn:Heq.
    - iExists _. iRight. iSplit; [done|]. iExists _. done.
    - iExists #(). iLeft. iSplit; [done|]. done.
  Qed.

  Lemma un_log_related_strsub Θ Δ Γ e1 e2 e3 :
    ({Θ;Δ;Γ} ⊨ᵤ e1 : t_nat) -∗
    ({Θ;Δ;Γ} ⊨ᵤ e2 : t_nat) -∗
    ({Θ;Δ;Γ} ⊨ᵤ e3 : t_string) -∗
    {Θ;Δ;Γ} ⊨ᵤ strsub e1 e2 e3 : t_string.
  Proof.
    iIntros "IH1 IH2 IH3". iIntros (vs) "#Hvs". iIntros (??) "Hv Htok". simpl.
    v_bind (subst_map vs e3).
    iMod ("IH3" $! vs with "Hvs Hv Htok") as (v3) "(Hv & #Hv3 & Htok)". simpl.
    v_bind (subst_map vs e2).
    iMod ("IH2" $! vs with "Hvs Hv Htok") as (v2) "(Hv & #Hv2 & Htok)". simpl.
    v_bind (subst_map vs e1).
    iMod ("IH1" $! vs with "Hvs Hv Htok") as (v1) "(Hv & #Hv1 & Htok)". simpl.
    rewrite interp_un_nat_unfold interp_un_string_unfold.
    iDestruct "Hv1" as (n1) "%". iDestruct "Hv2" as (n2) "%". iDestruct "Hv3" as (s) "%".
    simplify_eq. v_pures. iModIntro. iExists _. iFrame.
    rewrite interp_un_string_unfold. iExists _. done.
  Qed.

  Lemma un_log_related_pair Θ Δ Γ e1 e2 τ1 τ2 :
    ({Θ;Δ;Γ} ⊨ᵤ e1 : τ1) -∗
    ({Θ;Δ;Γ} ⊨ᵤ e2 : τ2) -∗
    {Θ;Δ;Γ} ⊨ᵤ Pair e1 e2 : t_prod τ1 τ2.
  Proof.
    iIntros "IH1 IH2". iIntros (vs) "#Hvs". iIntros (??) "Hv Htok". simpl.
    v_bind (subst_map vs e2).
    iMod ("IH2" $! vs with "Hvs Hv Htok") as (v2) "(Hv & #Hv2 & Htok)". simpl.
    v_bind (subst_map vs e1).
    iMod ("IH1" $! vs with "Hvs Hv Htok") as (v1) "(Hv & #Hv1 & Htok)". simpl.
    v_pures. iModIntro. iExists _. iFrame.
    rewrite interp_un_prod_unfold. iExists v1, v2. iSplit; [done|]. iFrame "#".
  Qed.

  Lemma un_log_related_fst Θ Δ Γ e τ1 τ2 :
    ({Θ;Δ;Γ} ⊨ᵤ e : t_prod τ1 τ2) -∗
    {Θ;Δ;Γ} ⊨ᵤ Fst e : τ1.
  Proof.
    iIntros "IH". iIntros (vs) "#Hvs". iIntros (??) "Hv Htok". simpl.
    v_bind (subst_map vs e).
    iMod ("IH" $! vs with "Hvs Hv Htok") as (v) "(Hv & #Hval & Htok)". simpl.
    rewrite interp_un_prod_unfold. iDestruct "Hval" as (v1 v2 ->) "[#H1 #H2]".
    v_pures. iModIntro. iExists _. iFrame "#∗".
  Qed.

  Lemma un_log_related_snd Θ Δ Γ e τ1 τ2 :
    ({Θ;Δ;Γ} ⊨ᵤ e : t_prod τ1 τ2) -∗
    {Θ;Δ;Γ} ⊨ᵤ Snd e : τ2.
  Proof.
    iIntros "IH". iIntros (vs) "#Hvs". iIntros (??) "Hv Htok". simpl.
    v_bind (subst_map vs e).
    iMod ("IH" $! vs with "Hvs Hv Htok") as (v) "(Hv & #Hval & Htok)". simpl.
    rewrite interp_un_prod_unfold. iDestruct "Hval" as (v1 v2 ->) "[#H1 #H2]".
    v_pures. iModIntro. iExists _. iFrame "#∗".
  Qed.

  Lemma un_log_related_injl Θ Δ Γ e τ1 τ2 :
    ({Θ;Δ;Γ} ⊨ᵤ e : τ1) -∗
    {Θ;Δ;Γ} ⊨ᵤ InjL e : t_sum τ1 τ2.
  Proof.
    iIntros "IH". iIntros (vs) "#Hvs". iIntros (??) "Hv Htok". simpl.
    v_bind (subst_map vs e).
    iMod ("IH" $! vs with "Hvs Hv Htok") as (v) "(Hv & #Hval & Htok)". simpl.
    v_pures. iModIntro. iExists _. iFrame.
    rewrite interp_un_sum_unfold. iExists v. iLeft. iSplit; [done|iApply "Hval"].
  Qed.

  Lemma un_log_related_injr Θ Δ Γ e τ1 τ2 :
    ({Θ;Δ;Γ} ⊨ᵤ e : τ2) -∗
    {Θ;Δ;Γ} ⊨ᵤ InjR e : t_sum τ1 τ2.
  Proof.
    iIntros "IH". iIntros (vs) "#Hvs". iIntros (??) "Hv Htok". simpl.
    v_bind (subst_map vs e).
    iMod ("IH" $! vs with "Hvs Hv Htok") as (v) "(Hv & #Hval & Htok)". simpl.
    v_pures. iModIntro. iExists _. iFrame.
    rewrite interp_un_sum_unfold. iExists v. iRight. iSplit; [done|iApply "Hval"].
  Qed.

  Lemma un_log_related_case Θ Δ Γ e0 e1 e2 τ1 τ2 τ3 :
    ({Θ;Δ;Γ} ⊨ᵤ e0 : t_sum τ1 τ2) -∗
    ({Θ;Δ;Γ} ⊨ᵤ e1 : t_arr τ1 τ3) -∗
    ({Θ;Δ;Γ} ⊨ᵤ e2 : t_arr τ2 τ3) -∗
    {Θ;Δ;Γ} ⊨ᵤ Case e0 e1 e2 : τ3.
  Proof.
    iIntros "IH0 IH1 IH2". iIntros (vs) "#Hvs". iIntros (??) "Hv Htok". simpl.
    v_bind (subst_map vs e0).
    iMod ("IH0" $! vs with "Hvs Hv Htok") as (v) "(Hv & #Hval & Htok)". simpl.
    rewrite interp_un_sum_unfold.
    iDestruct "Hval" as (w) "[(-> & #Hw)|(-> & #Hw)]"; v_pures.
    - v_bind (subst_map vs e1).
      iMod ("IH1" $! vs with "Hvs Hv Htok") as (f) "(Hv & #Hf & Htok)". simpl.
      rewrite interp_un_arr_unfold.
      iApply ("Hf" with "Hw Hv Htok").
    - v_bind (subst_map vs e2).
      iMod ("IH2" $! vs with "Hvs Hv Htok") as (f) "(Hv & #Hf & Htok)". simpl.
      rewrite interp_un_arr_unfold.
      iApply ("Hf" with "Hw Hv Htok").
  Qed.

  Lemma un_log_related_if Θ Δ Γ e0 e1 e2 τ :
    ({Θ;Δ;Γ} ⊨ᵤ e0 : t_bool) -∗
    ({Θ;Δ;Γ} ⊨ᵤ e1 : τ) -∗
    ({Θ;Δ;Γ} ⊨ᵤ e2 : τ) -∗
    {Θ;Δ;Γ} ⊨ᵤ If e0 e1 e2 : τ.
  Proof.
    iIntros "IH0 IH1 IH2". iIntros (vs) "#Hvs". iIntros (??) "Hv Htok". simpl.
    v_bind (subst_map vs e0).
    iMod ("IH0" $! vs with "Hvs Hv Htok") as (v) "(Hv & #Hval & Htok)". simpl.
    rewrite interp_un_bool_unfold. iDestruct "Hval" as (b) "%". simplify_eq.
    destruct b; v_pures.
    - iApply ("IH1" $! vs with "Hvs Hv Htok").
    - iApply ("IH2" $! vs with "Hvs Hv Htok").
  Qed.

  Lemma un_log_related_rec Θ Δ (Γ : stringmap (typ ⋆ Θ)) (f x : binder) (e : expr) τ1 τ2 :
    □ ({Θ;Δ;<[f:=t_arr τ1 τ2]>(<[x:=τ1]>Γ)} ⊨ᵤ e : τ2) -∗
    {Θ;Δ;Γ} ⊨ᵤ Rec f x e : t_arr τ1 τ2.
  Proof.
    iIntros "#IHun". iIntros (vs) "#Hvs". iIntros (??) "Hv Htok". simpl.
    v_pures. iModIntro. iExists _. iFrame.
    iLöb as "IHlob".
    rewrite interp_un_arr_unfold. iModIntro.
    iIntros (w) "#Hw". iIntros (??) "Hv Htok". v_pures.
    iMod "IHlob" as "#IHlob".
    set rec1 := (rec: f x := subst_map (binder_delete x (binder_delete f vs)) e)%V.
    iSpecialize ("IHun" $! (binder_insert f rec1 (binder_insert x w vs))).
    rewrite -subst_map_binder_insert_2.
    iApply ("IHun" with "[#] Hv Htok").
    rewrite !binder_insert_fmap.
    iApply (env_ltyped_un_insert with "[IHlob]").
    { rewrite interp_un_arr_unfold //. }
    iApply (env_ltyped_un_insert with "Hw Hvs").
  Qed.

  Lemma un_log_related_app Θ Δ Γ e1 e2 τ1 τ2 :
    ({Θ;Δ;Γ} ⊨ᵤ e1 : t_arr τ1 τ2) -∗
    ({Θ;Δ;Γ} ⊨ᵤ e2 : τ1) -∗
    {Θ;Δ;Γ} ⊨ᵤ App e1 e2 : τ2.
  Proof.
    iIntros "IH1 IH2". iIntros (vs) "#Hvs". iIntros (??) "Hv Htok". simpl.
    v_bind (subst_map vs e2).
    iMod ("IH2" $! vs with "Hvs Hv Htok") as (v2) "(Hv & #Hv2 & Htok)". simpl.
    v_bind (subst_map vs e1).
    iMod ("IH1" $! vs with "Hvs Hv Htok") as (f) "(Hv & #Hf & Htok)". simpl.
    rewrite interp_un_arr_unfold.
    iApply ("Hf" with "Hv2 Hv Htok").
  Qed.

  Lemma un_log_related_tlam Θ (Δ : ctxO Σ Θ) Γ κ (e : expr) τ :
    (∀ A : kindO Σ κ, □ ({(Θ ▹ κ); (ext Δ A); ⤉Γ} ⊨ᵤ e : τ)) -∗
    {Θ;Δ;Γ} ⊨ᵤ (Λ: e) : ∀: κ, τ.
  Proof.
    iIntros "#IHun". iIntros (vs) "#Hvs". iIntros (??) "Hv Htok". simpl.
    v_pures. iModIntro. iExists _. iFrame. iModIntro.
    rewrite interp_un_forall_unfold. iIntros (A). iModIntro. iIntros (v) "_".
    iIntros (??) "Hv Htok". v_pures.
    iSpecialize ("IHun" $! A).
    iApply ("IHun" $! vs with "[Hvs] Hv Htok").
    rewrite -shift_env_un_eq. iApply "Hvs".
  Qed.

  Lemma un_log_related_tapp' Θ Δ κ Γ e τ τ' :
    ({Θ;Δ;Γ} ⊨ᵤ e : ∀: κ, τ) -∗
    {Θ;Δ;Γ} ⊨ᵤ e #~ : τ.[τ'/].
  Proof.
    iIntros "IH". iIntros (vs) "#Hvs". iIntros (??) "Hv Htok". simpl.
    v_bind (subst_map vs e).
    iMod ("IH" $! vs with "Hvs Hv Htok") as (v) "(Hv & #Hval & Htok)". simpl. fold kindO.
    rewrite interp_un_forall_unfold.
    iDestruct ("Hval" $! (interp τ' Δ)) as "#Hv'".
    iSpecialize ("Hv'" $! #~ with "[//]"). simpl. rewrite subst_eq.
    iApply ("Hv'" with "Hv Htok").
  Qed.

  Lemma un_log_related_fold Θ Δ Γ e κ (τ : typ κ (Θ ▹ κ%kind)) (T : telim_ctx Θ κ ⋆) :
    ({Θ;Δ;Γ} ⊨ᵤ e : tfill T (τ.[μ: κ; τ/])) -∗
    {Θ;Δ;Γ} ⊨ᵤ rec_fold e : tfill T (μ: κ; τ).
  Proof.
    iIntros "IH". iIntros (vs) "#Hvs". iIntros (??) "Hv Htok". simpl.
    v_bind (subst_map vs e).
    iMod ("IH" $! vs with "Hvs Hv Htok") as (v) "(Hv & #Hval & Htok)". simpl.
    v_pures. iModIntro. iExists _. iFrame. rewrite tfill_rec_eq /=. iApply "Hval".
  Qed.

  Lemma un_log_related_unfold Θ Δ Γ e κ (τ : typ κ (Θ ▹ κ%kind)) (T : telim_ctx Θ κ ⋆) :
    ({Θ;Δ;Γ} ⊨ᵤ e : tfill T (μ: κ; τ)) -∗
    {Θ;Δ;Γ} ⊨ᵤ rec_unfold e : tfill T (τ.[μ: κ; τ/]).
  Proof.
    iIntros "IH". iIntros (vs) "#Hvs". iIntros (??) "Hv Htok". simpl.
    v_bind (subst_map vs e).
    iMod ("IH" $! vs with "Hvs Hv Htok") as (v) "(Hv & #Hval & Htok)". simpl.
    iEval (rewrite tfill_rec_eq /=) in "Hval". v_pures. iModIntro. iExists _. iFrame. iApply "Hval".
  Qed.

  Lemma un_log_related_pack' Θ κ Δ Γ e τ τ' :
    ({Θ;Δ;Γ} ⊨ᵤ e : τ.[τ'/]) -∗
    {Θ;Δ;Γ} ⊨ᵤ e : ∃: κ, τ.
  Proof.
    iIntros "IH". iIntros (vs) "#Hvs". iIntros (??) "Hv Htok". simpl.
    iMod ("IH" $! vs with "Hvs Hv Htok") as (v) "(Hv & #Hval & Htok)". simpl. fold kindO.
    iModIntro. iExists _. iFrame.
    rewrite interp_un_exists_unfold. iExists (interp τ' Δ). simpl. rewrite subst_eq. iApply "Hval".
  Qed.

  Lemma un_log_related_unpack Θ κ Δ Γ x e1 e2 τ τ2 :
    ({Θ;Δ;Γ} ⊨ᵤ e1 : ∃: κ, τ) -∗
    (∀ A : kindO Σ κ,
      {Θ ▹ κ; ext Δ A; <[x:=τ]>(⤉Γ)} ⊨ᵤ e2 : Core.shift τ2) -∗
    {Θ;Δ;Γ} ⊨ᵤ (unpack: x := e1 in e2) : τ2.
  Proof.
    iIntros "IH1 IH2". iIntros (vs) "#Hvs". iIntros (??) "Hv Htok". simpl.
    rewrite /unpack. v_pures.
    v_bind (subst_map vs e1).
    iMod ("IH1" $! vs with "Hvs Hv Htok") as (v1) "(Hv & #Hex & Htok)". simpl.
    rewrite interp_un_exists_unfold.
    iDestruct "Hex" as (A) "#HτA".
    v_pures.
    iSpecialize ("IH2" $! A (binder_insert x v1 vs) with "[#]").
    { rewrite binder_insert_fmap -shift_env_un_eq.
      iApply (env_ltyped_un_insert with "HτA Hvs"). }
    rewrite subst_map_binder_insert /=.
    rewrite -(shift_eq τ2).
    iApply ("IH2" with "Hv Htok").
  Qed.

  Lemma un_log_related_hash Θ Δ Γ e :
    ({Θ;Δ;Γ} ⊨ᵤ e : t_string) -∗
    {Θ;Δ;Γ} ⊨ᵤ Hash e : t_string.
  Proof.
    iIntros "IH". iIntros (vs) "#Hvs". iIntros (??) "[#Hctx Hv] Htok". simpl.
    v_bind (subst_map vs e).
    iMod ("IH" $! vs with "Hvs [$Hctx $Hv] Htok") as (v) "([_ Hv] & #Hval & Htok)". simpl.
    rewrite interp_un_string_unfold.
    iDestruct "Hval" as (s) "%". simplify_eq.
    iMod (step_verifier_hash with "[$Hctx $Hv]") as "Hv"; [done|].
    iModIntro. iExists _. iFrame "# ∗". rewrite interp_un_string_unfold. iExists _. done.
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
    Θ |ₜ Γ ⊢ₜ e : τ → ⊢ {Θ;Δ;Γ} ⊨ e ≤log≤ e ≤log≤ e : τ
  with fundamental_val Θ Δ v τ :
    Θ ⊢ᵥ v : τ → ⊢ interp τ Δ v v v.
  Proof.
    - intros Ht. destruct Ht.
      + by iApply tern_log_related_var.
      + iIntros (γ) "#H /=".
        iIntros (????) "Hp Hi Htok". wp_pures. iFrame.
        iModIntro. by iApply fundamental_val.
      + iApply tern_log_related_nat_binop; first done;
          by iApply fundamental.
      + iApply tern_log_related_bool_binop; first done;
          by iApply fundamental.
      + iApply tern_log_related_nat_unop; first done.
        by iApply fundamental.
      + iApply tern_log_related_bool_unop; first done.
        by iApply fundamental.
      + iApply tern_log_related_string_unop; first done.
        by iApply fundamental.
      + iApply tern_log_related_unboxed_eq; try done;
          by iApply fundamental.
      + iApply tern_log_related_strindex; try done;
          by iApply fundamental.
      + iApply tern_log_related_strsub; try done;
          by iApply fundamental.
      + iApply tern_log_related_pair;
          by iApply fundamental.
      + iApply tern_log_related_fst;
          by iApply fundamental.
      + iApply tern_log_related_snd;
          by iApply fundamental.
      + iApply tern_log_related_injl;
          by iApply fundamental.
      + iApply tern_log_related_injr;
          by iApply fundamental.
      + iApply tern_log_related_case;
          by iApply fundamental.
      + iApply tern_log_related_if;
          by iApply fundamental.
      + iApply tern_log_related_rec.
        iModIntro. by iApply fundamental.
      + iApply tern_log_related_app;
          by iApply fundamental.
      + iApply tern_log_related_tlam.
        iIntros (A). iModIntro. by iApply fundamental.
      + iApply tern_log_related_tapp'; by iApply fundamental.
      + iApply tern_log_related_fold; by iApply fundamental.
      + iApply tern_log_related_unfold; by iApply fundamental.
      + iApply tern_log_related_pack'; by iApply fundamental.
      + iApply tern_log_related_unpack; try by iApply fundamental.
        iIntros (A). by iApply fundamental.
      (* + iApply tern_log_related_fork; by iApply fundamental.
      + iApply tern_log_related_alloc; by iApply fundamental.
      + iApply tern_log_related_load; by iApply fundamental.
      + iApply tern_log_related_store; by iApply fundamental.
      + iApply tern_log_related_xchg; by iApply fundamental.
      + iApply tern_log_related_FAA; eauto;
          by iApply fundamental.
      + iApply tern_log_related_CmpXchg; eauto;
          by iApply fundamental. *)
      + iApply tern_log_related_hash; by iApply fundamental.
      + iApply tern_log_related_tequiv; [done|]. by iApply fundamental.
    - intros Hv. destruct Hv as
        [ | | | | v1 v2 ? ? Hv1 Hv2
        | v' ? ? Hv'
        | v' ? ? Hv' | | ]; simpl.
      + iSplit; [|iSplit]; done.
      + iSplit; [|iSplit]; iExists _; done.
      + iSplit; [|iSplit]; iExists _; done.
      + iSplit; [|iSplit]; iExists _; done.
      + iDestruct (fundamental_val _ Δ _ _ Hv1) as "#H1".
        iDestruct (fundamental_val _ Δ _ _ Hv2) as "#H2".
        iDestruct "H1" as "[H1t [H1b H1u]]". iDestruct "H2" as "[H2t [H2b H2u]]".
        iSplit; [|iSplit].
        * iExists _,_,_,_,_,_. iSplit; [done|]. iSplit; [done|]. iSplit; [done|]. iFrame "#".
        * iExists _,_,_,_. iSplit; [done|]. iSplit; [done|]. iFrame "#".
        * iExists _,_. iSplit; [done|]. iFrame "#".
      + iDestruct (fundamental_val _ Δ _ _ Hv') as "#Hv".
        iDestruct "Hv" as "[Ht [Hb Hu]]".
        iSplit; [|iSplit].
        * iExists _,_,_. iLeft. iSplit; [done|]. iSplit; [done|]. iSplit; [done|]. iFrame "#".
        * iExists _,_. iLeft. iSplit; [done|]. iSplit; [done|]. iFrame "#".
        * iExists _. iLeft. iSplit; [done|]. iFrame "#".
      + iDestruct (fundamental_val _ Δ _ _ Hv') as "#Hv".
        iDestruct "Hv" as "[Ht [Hb Hu]]".
        iSplit; [|iSplit].
        * iExists _,_,_. iRight. iSplit; [done|]. iSplit; [done|]. iSplit; [done|]. iFrame "#".
        * iExists _,_. iRight. iSplit; [done|]. iSplit; [done|]. iFrame "#".
        * iExists _. iRight. iSplit; [done|]. iFrame "#".
      + admit.
      + admit.
  Admitted.

  Theorem refines_typed Θ τ Δ e :
    Θ |ₜ ∅ ⊢ₜ e : τ →
    ⊢ REL e << e << e : interp τ Δ.
  Proof.
    move=> /fundamental Hty.
    iPoseProof (Hty Δ with "[]") as "H".
    { rewrite fmap_empty. iApply env_ltyped_empty. }
    by rewrite !fmap_empty !subst_map_empty.
  Qed. *)

End fundamental.

