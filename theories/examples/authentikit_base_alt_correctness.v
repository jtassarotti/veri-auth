From auth.prelude Require Import stdpp.
From auth.rel_logic_tern Require Export model interp spec_tactics.
From auth.heap_lang.lib Require Import serialization list.
From auth.examples Require Export authentikit authentikit_base_correctness authenticatable_base_alt.

Section authenticatable.
  Context `{!authG Σ}.

  Definition v_ser_spec (v_ser a2 : val) (s : string) : iProp Σ :=
    (□ ∀ K tᵥ, spec_verifier tᵥ (fill K (v_ser a2)) ={⊤}=∗ spec_verifier tᵥ (fill K #s)).

  Definition ser_spec (p_ser v_ser : val) (t : evi_type) (A : lrel Σ) : iProp Σ :=
    ∀ (a1 a2 a3 : val),
      {{{ ▷ A a1 a2 a3 }}}
        p_ser a1
      {{{ s, RET #s; s_is_ser (g := gwp_upto_bad) (evi_type_ser t) a2 s ∗ v_ser_spec v_ser a2 s }}}.

  Definition v_deser_spec (v_deser : val) (t : evi_type) (a2 : val) (s : string) : iProp Σ :=
    (□ ∀ K tᵥ, spec_verifier tᵥ (fill K (v_deser #s)) ={⊤}=∗ spec_verifier tᵥ (fill K (SOMEV a2))).

  Definition deser_spec (p_deser v_deser : val) (A : lrel Σ) : iProp Σ :=
    {{{ True }}} p_deser #() {{{ RET #(); True }}} ∗
    ∀ (a1 a2 a3 : val) (t : evi_type) (s : string),
      {{{ s_is_ser (g := gwp_upto_bad) (evi_type_ser t) a2 s ∗ ▷ A a1 a2 a3 }}}
        p_deser #()
      {{{ RET #(); v_deser_spec v_deser t a2 s }}}.

  Definition lrel_serialization (A : lrel Σ) : lrel Σ := LRel (λ v1 v2 _,
    ∃ (t : evi_type) (p_ser p_deser v_ser v_deser  : val),
      ⌜v1 = (p_ser, p_deser)%V⌝ ∗ ⌜v2 = (v_ser, v_deser)%V⌝ ∗
      ser_spec p_ser v_ser t A ∗ deser_spec p_deser v_deser A)%I.

  Program Definition lrel_evidence : kindO Σ (⋆ ⇒ ⋆)%kind := λne A, lrel_serialization A.
  Next Obligation.
    intros ???????. rewrite /lrel_car/= /ser_spec /deser_spec. solve_proper.
  Qed.

  Lemma refines_Auth_pair Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆; ⋆, var2 var1 → var2 var0 → var2 (var1 * var0) ⟧
      (ext Δ lrel_evidence) p_Auth_pair v_Auth_pair i_Auth_pair.
  Proof.
    iIntros (A ???) "!# _"; rewrite -/interp.
    iIntros (????) "Hv Hi".
    rewrite /p_Auth_pair /v_Auth_pair /i_Auth_pair.
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame.
    iIntros (B ???) "!# _"; rewrite -/interp.
    iIntros (????) "Hv Hi".
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame.
    iIntros (???) "!# #HA"; rewrite -!/interp /=.
    iDestruct "HA" as (tA p_sA p_dA v_sA v_dA -> ->) "[#HserA [#HdeserA' #HdeserA]]". clear.
    iIntros (????) "Hv Hi".
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame.
    iIntros (???) "!# #HB". clear.
    iDestruct "HB" as (tB p_sB p_dB v_sB v_dB -> ->) "[#HserB [#HdeserB' #HdeserB]]". clear.
    iIntros (????) "Hv Hi".
    v_pures; i_pures; wp_pures.
    rewrite /prod_scheme /prod_ser /prod_deser.
    v_pures. wp_pures. iModIntro. iFrame.
    iExists (tprod tA tB), _, _, _, _.
    do 2 (iSplit; [done|]). clear.
    repeat iSplit.
    - iIntros (a1 a2 a3 Ψ) "!# Hp HΨ".
      iDestruct "Hp" as (??????) "(>-> & >-> & >-> & #Ha & #Hb)".
      wp_pures.
      wp_apply ("HserA" with "Ha").
      iIntros (sA) "(#HsA & #HserA')".
      wp_pures.
      wp_apply ("HserB" with "Hb").
      iIntros (sB) "(#HsB & #HserB')".
      wp_pures.
      iApply "HΨ".
      iModIntro. iSplit.
      { iPureIntro. do 4 eexists; split_and!; eauto. }
      iIntros (??) "!# Hv".
      v_pures. v_bind (v_sA _).
      iMod ("HserA'" with "Hv") as "Hv /= ".
      v_pures. v_bind (v_sB _).
      iMod ("HserB'" with "Hv") as "Hv /= ".
      v_pures. iModIntro. done.
    - iIntros (?) "!# _ H". wp_pures.
      wp_apply "HdeserA'"; [done|]. iIntros "_". wp_pures.
      wp_apply "HdeserB'"; [done|]. iIntros "_". by iApply "H".
    - iIntros (???? ??) "!# [%Hser #Hp] H".
      wp_pures.
      iDestruct "Hp" as (? v2 ? ? v2' ????) "[#HA #HB]". simplify_eq.
      destruct t; destruct! Hser; simplify_eq.
      wp_apply ("HdeserA" with "[$HA //]"). iIntros "#Hv_deserA".
      wp_pures.
      wp_apply ("HdeserB" with "[$HB //]"). iIntros "#Hv_deserB".
      iApply "H".
      iIntros "!#" (??) "Hv".
      iMod (prod_deser'_complete (s_is_ser (evi_type_ser t1)) (s_is_ser (evi_type_ser t2))
              ⊤ _ _ _ _ () %I with "[//] [] [] [] [] [$Hv //]") as (?) "[Hv H]".
      { iIntros (?? HsA') "!# H". iIntros (??) "[% Hv]".
        pose proof (evi_type_ser_inj_str _ _ _ _ _ H4 HsA'). subst.
        iMod ("Hv_deserA" with "[$Hv //]") as "$". iModIntro. by iApply "H". }
      { iIntros (?? HsB') "!# H". iIntros (??) "[% Hv]".
        pose proof (evi_type_ser_inj_str _ _ _ _ _ H5 HsB'). subst.
        iMod ("Hv_deserB" with "[$Hv //]") as "$".
        iModIntro. by iApply "H". }
      { iPureIntro. do 4 eexists. split_and!; eauto. }
      { instantiate (1 := (λ v, ⌜v = SOMEV _⌝)%I). simpl. eauto. }
      by iDestruct "H" as %->.
  Qed.

  Lemma refines_Auth_sum Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆; ⋆, var2 var1 → var2 var0 → var2 (var1 + var0) ⟧
      (ext Δ lrel_evidence) p_Auth_sum v_Auth_sum i_Auth_sum.
  Proof.
    iIntros (A ???) "!# _"; rewrite -/interp.
    iIntros (????) "Hv Hi".
    rewrite /p_Auth_sum /v_Auth_sum /i_Auth_sum.
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame.
    iIntros (B ???) "!# _"; rewrite -/interp.
    iIntros (????) "Hv Hi".
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame.
    iIntros (???) "!# #HA"; rewrite -!/interp /=.
    iDestruct "HA" as (tA p_sA p_dA v_sA v_dA -> ->) "[#HserA [#HdeserA' #HdeserA]]". clear.
    iIntros (????) "Hv Hi".
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame.
    iIntros (???) "!# #HB". clear.
    iDestruct "HB" as (tB p_sB p_dB v_sB v_dB -> ->) "[#HserB [#HdeserB' #HdeserB]]". clear.
    iIntros (????) "Hv Hi".
    v_pures; i_pures; wp_pures.
    rewrite /sum_scheme /sum_ser /sum_deser.
    v_pures. wp_pures. iModIntro. iFrame.
    iExists (tsum tA tB), _, _, _, _.
    do 2 (iSplit; [done|]). clear. repeat iSplit.
    - iIntros (??? Ψ) "!# Hsum HΨ".
      iDestruct "Hsum" as (???) "[(>-> & >-> & >-> & #HA) | (>-> & >-> & >-> & #HB)]".
      + wp_pures.
        wp_apply ("HserA" with "HA").
        iIntros (sA) "(%HsA & #Hser')".
        wp_pures. iModIntro.
        iApply "HΨ". iSplit; [by iExists _, _; iLeft|].
        iIntros (??) "!# Hv". v_pures.
        v_bind (v_sA _).
        iMod ("Hser'" with "Hv") as "Hv /=".
        v_pures. by iModIntro.
      + wp_pures.
        wp_apply ("HserB" with "HB").
        iIntros (sB) "(%HsB & #Hser')".
        wp_pures. iModIntro.
        iApply "HΨ". iSplit; [by iExists _, _; iRight|].
        iIntros (??) "!# Hv". v_pures.
        v_bind (v_sB _).
        iMod ("Hser'" with "Hv") as "Hv /=".
        v_pures. by iModIntro.
    - iIntros (?) "!# _ H". wp_pures.
      wp_apply "HdeserA'"; [done|]. iIntros "_". wp_pures.
      wp_apply "HdeserB'"; [done|]. iIntros "_". by iApply "H".
    - iIntros (????? Ψ) "!# (%Hser & Hsum) HΨ".
      wp_pures.
      rewrite -/(sum_deser' _ _).
      iDestruct "Hsum" as (???) "[(% & % & % & #HA) | (% & % & % & #HB)]".
      + destruct t; destruct! Hser; simplify_eq.
        wp_apply ("HdeserA" with "[$HA //]").
        iIntros "#Hv_deserA". wp_pures.
        wp_apply ("HdeserB'" with "[//]"). iIntros "_".
        iApply "HΨ".
        iIntros (??) "!# Hv".
        iMod (sum_deser'_complete (s_is_ser (evi_type_ser t1)) (s_is_ser (evi_type_ser t2))
                ⊤ (InjLV _) _ () with "[] [] [] [] [$Hv //]") as (?) "[Hv H]".
        { iIntros (???) "!# % %HsA' H". simplify_eq. iIntros (??) "[% Hv]".
          pose proof (evi_type_ser_inj_str _ _ _ _ _ H5 HsA'). subst.
          iMod ("Hv_deserA" with "[$Hv //]") as "$". iModIntro. by iApply "H". }
        { iIntros (?? [=]). }
        { iPureIntro. do 2 eexists. by left. }
        { instantiate (1 := (λ v, ⌜v = SOMEV _⌝)%I). simpl. eauto. }
        by iDestruct "H" as %->.
      + destruct t; destruct! Hser; simplify_eq.
        wp_apply ("HdeserA'" with "[//]"). iIntros "_".
        wp_pures.
        wp_apply ("HdeserB" with "[$HB //]").
        iIntros "#Hv_deserB".
        iApply "HΨ".
        iIntros (??) "!# Hv".
        iMod (sum_deser'_complete (s_is_ser (evi_type_ser t1)) (s_is_ser (evi_type_ser t2))
                ⊤ (InjRV _) _ () with "[] [] [] [] [$Hv //]") as (?) "[Hv H]".
        { iIntros (?? [=]). }
        { iIntros (???) "!# % %HsB' H". simplify_eq. iIntros (??) "[% Hv]".
          pose proof (evi_type_ser_inj_str _ _ _ _ _ H5 HsB'). subst.
          iMod ("Hv_deserB" with "[$Hv //]") as "$". iModIntro. by iApply "H". }
        { iPureIntro. do 2 eexists. by right. }
        { instantiate (1 := (λ v, ⌜v = SOMEV _⌝)%I). simpl. eauto. }
        by iDestruct "H" as %->.
  Qed.

  Lemma refines_Auth_string :
    ⊢ lrel_evidence lrel_string p_Auth_string v_Auth_string i_Auth_string.
  Proof.
    iExists tstring, _, _, _, _.
    do 2 (iSplit; [done|]).
    repeat iSplit.
    - iIntros (????) "!# >(% & -> & -> & ->) H".
      rewrite /p_Auth_string /string_ser.
      wp_pures. iModIntro. iApply "H".
      iSplit; [by iExists _|].
      iIntros (??) "!# Hv". by v_pures.
    - iIntros (?) "!# _ H". wp_pures. iModIntro. by iApply "H".
    - iIntros (??????) "!# [%Hser >(% & % & % & %)] HΨ".
      simplify_eq.
      destruct t; destruct! Hser; simplify_eq.
      wp_pures. iModIntro. iApply "HΨ".
      iIntros (??) "!# Hv".
      iMod (string_deser_spec' ⊤ _ _ () (λ v, ⌜v = SOMEV _⌝)%I
             with "[] [] [$Hv //]") as (?) "[H ->]"; [|done|done].
      by iExists _.
  Qed.

  Lemma refines_Auth_int :
    ⊢ lrel_evidence lrel_int p_Auth_int v_Auth_int i_Auth_int.
  Proof.
    iExists tint, _, _, _, _.
    do 2 (iSplit; [done|]). repeat iSplit.
    - iIntros (????) "!# >(% & -> & -> & ->) H".
      rewrite /p_Auth_int /int_ser.
      wp_pures. iModIntro. iApply "H".
      iSplit; [by iExists _|].
      iIntros (??) "!# Hv". by v_pures.
    - iIntros (?) "!# _ H". wp_pures. iModIntro. by iApply "H".
    - iIntros (??????) "!# [%Hser >(% & % & % & %)] HΨ".
      simplify_eq. destruct t; destruct! Hser; simplify_eq.
      wp_pures. iModIntro. iApply "HΨ".
      iIntros (??) "!# Hv".
      iMod (int_deser_spec' ⊤ _ _ () (λ v, ⌜v = SOMEV _⌝)%I
        with "[] [] [$Hv //]") as (?) "[H ->]"; [|done|done].
      by iExists _.
  Qed.

  Lemma refines_Auth_mu Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆ ⇒ ⋆, var1 (var0 (μ: ⋆; var1 var0)) → var1 (μ: ⋆; var1 var0) ⟧
      (ext Δ lrel_evidence) p_Auth_mu v_Auth_mu i_Auth_mu.
  Proof.
    iIntros (A v1 v2 v3) "!# _". rewrite -/interp.
    iIntros (????) "Hv Hi".
    rewrite /p_Auth_mu /i_Auth_mu /v_Auth_mu.
    i_pures. v_pures. wp_pures.
    iFrame. iModIntro. clear. simpl.
    iIntros (???) "!# HA".
    iDestruct "HA" as (????? -> ->) "[#Hser [#Hdeser' #Hdeser]]".
    iIntros (????) "Hv Hi".
    i_pures. v_pures. wp_pures.
    iFrame. iModIntro.
    iExists t, _, _, _, _.
    do 2 (iSplit; [done|]). clear.
    repeat iSplit.
    - iIntros (a1 a2 a3 Ψ) "!# HA HΨ".
      iEval (rewrite interp_rec_unfold /lrel_car /=) in "HA".
      wp_pures.
      iApply ("Hser" with "HA").
      iIntros (s) "!> (%Hs & #Hser')".
      iApply "HΨ". iSplit; [done|].
      iIntros "!#" (??) "Hv". v_pures. by iApply "Hser'".
    - iIntros (?) "!# _ H". wp_pures. by wp_apply "Hdeser'".
    - iIntros (????? ?) "!# (%Hser & #HA) H".
      iEval (rewrite interp_rec_unfold /lrel_car /=) in "HA".
      wp_pures.
      wp_apply ("Hdeser" with "[$HA //]").
      iIntros "#Hv_deser". iApply "H".
      iIntros (??) "!# Hv". v_pures.
      by iMod ("Hv_deser" with "Hv") as "$".
  Qed.

  (** Note that [hashed s] is only needed from [authentikit_buf.v] and onwards  *)
  Definition lrel_auth' (A : lrel Σ) : lrel Σ := LRel (λ v1 v2 v3,
    ∃ (t : evi_type) (a1 a2 : val) (s : string),
      ⌜v1 = (a1, #(hash s))%V⌝ ∗
      ⌜s_is_ser (evi_type_ser t) a2 s⌝ ∗ ⌜v2 = #(hash s)⌝ ∗
      hashed s ∗ A a1 a2 v3)%I.

  Program Definition lrel_auth : kindO Σ (⋆ ⇒ ⋆)%kind := λne A, lrel_auth' A.
  Next Obligation. solve_proper. Qed.

  Definition auth_ctx {Θ} (Δ : ctxO Σ Θ) (R : kindO Σ (⋆ ⇒ ⋆)) :=
    ext (ext (ext Δ lrel_auth) R) lrel_evidence.

  Lemma refines_Auth_auth Θ (Δ : ctxO Σ Θ) (R : kindO Σ (⋆ ⇒ ⋆)) :
    ⊢ ⟦ ∀: ⋆, var1 (var3 var0) ⟧
      (auth_ctx Δ R) p_Auth_auth v_Auth_auth i_Auth_auth.
  Proof.
    iIntros (A ???) "!# _"; rewrite -!/interp.
    iIntros (????) "Hv Hi".
    rewrite /p_Auth_auth /v_Auth_auth /i_Auth_auth.
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame. simpl.
    rewrite /lrel_car /=.
    iExists tstring, _, _, _, _.
    do 2 (iSplit; [done|]). clear.
    repeat iSplit.
    - iIntros (a1 a2 a3 Ψ) "!# Hauth HΨ".
      rewrite /lrel_car /=.
      iDestruct "Hauth" as (????) "(>-> & >% & >-> & #HA & _)".
      wp_pures. iModIntro.
      iApply "HΨ". iSplit; [by iExists _|].
      iIntros "!#" (??) "Hv". rewrite /string_ser.
      v_pures. by iModIntro.
    - iIntros (?) "!# _ H". wp_pures. iModIntro. by iApply "H".
    - iIntros (??????) "!# [%Hser Hauth] H". wp_pures.
      iDestruct "Hauth" as (???? -> ? ->) "Hfo".
      iModIntro. iApply "H".
      iIntros (??) "!# Hv".
      iMod (string_deser_spec' ⊤ _ _ () (λ v, ⌜v = SOMEV _⌝)%I
             with "[] [] [$Hv //]") as (?) "[H ->]"; [|done|done].
      destruct t; destruct! Hser; simplify_eq; by iExists _.
  Qed.

  Lemma refines_auth_auth Θ (Δ : ctxO Σ Θ) (R : kindO Σ (⋆ ⇒ ⋆)) :
    ⊢ ⟦ ∀: ⋆, var1 var0 → var0 → var3 var0 ⟧
      (auth_ctx Δ R) p_auth v_auth i_auth.
  Proof.
    iIntros (????) "!# _"; rewrite -/interp.
    iIntros (????) "Hv Hi".
    rewrite /p_auth /v_auth  /i_auth.
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iIntros (???) "!#"; rewrite -!/interp /=.
    iDestruct 1 as (t ???? -> ->) "[#Hser #Hdeser]".

    iIntros (????) "Hv Hi".
    v_pures; i_pures; wp_pures.
    iFrame.
    iIntros "!> !>" (w1 w2 w3) "#HA". clear.
    iIntros (????) "Hv Hi".
    v_pures; i_pures; wp_pures.
    v_bind (v_ser _). wp_bind (p_ser _).
    wp_apply ("Hser" with "HA").
    iIntros (s1) "(%Hs1 & #Hser')".
    iMod ("Hser'" with "Hv") as "Hv /=".
    wp_apply (wp_hash with "[$]"); iIntros "Hhash".
    wp_pures.
    iMod (step_verifier_hash with "[$]") as "Hv"; [done|].
    iFrame. iModIntro.
    by iFrame "∗ # %".
  Qed.

End authenticatable.

(** * Prophesied proof stream *)
Section proph.
  Context `{heapGS Σ}.

  Fixpoint take_until {A B : Type} (f : A → option B) (xs : list A) : list B :=
    match xs with
    | []      => []
    | x :: xs =>
      match f x with
      | Some y => y :: (take_until f xs)
      | None   => []
      end
    end.

  Definition longest_valid_prefix (us : list val) : list string :=
    take_until (λ u, match u with InjRV (LitV (LitString s)) => Some s | _ => None end) us.

  Definition proph_proof (p : proph_id) (vs : list string) : iProp Σ :=
    (∃ (us : list (val * val)), proph p us ∗ ⌜vs = longest_valid_prefix (map snd us)⌝)%I.

  Lemma wp_resolve_proph_string p vs (s : string) :
    {{{ proph_proof p vs }}}
      resolve_proph: #p to: (SOMEV #s)
    {{{ vs', RET #(); ⌜vs = s :: vs'⌝ ∗ proph_proof p vs' }}}.
  Proof.
    iIntros (Φ) "(%us & Hp & %) HΦ".
    wp_apply (wp_resolve_proph with "Hp").
    iIntros (?) "[% Hp]". iApply "HΦ".
    iFrame. by simplify_eq.
  Qed.

  Lemma wp_resolve_proph_nil p vs :
    {{{ proph_proof p vs }}} resolve_proph: #p to: NONEV {{{ RET #(); ⌜vs = []⌝ }}}.
  Proof.
    iIntros (Φ) "(%us & Hp & %) HΦ".
    wp_apply (wp_resolve_proph with "Hp").
    iIntros (?) "[% Hp]". iApply "HΦ".
    by simplify_eq.
  Qed.

  Definition is_proof (v : val) (ps : list string) : Prop :=
    is_list ps v.

  Definition is_proph_proof (v : val) (p : proph_id) (ps : list string) : iProp Σ :=
    ⌜is_proof v ps⌝ ∗ proph_proof p ps.

End proph.
