From auth.rel_logic_tern Require Export model spec_rules spec_tactics interp fundamental.
From auth.heap_lang Require Import primitive_laws derived_laws.
From auth.heap_lang.lib Require Import list serialization.
From auth.examples Require Export authentikit_list authentikit_base_correctness.

(** * Correctness proof *)
Section proof.
  Context `{!authG Σ}.

  Definition lrel_auth_comp' (A : lrel Σ) : lrel Σ := LRel (λ v1 v2 v3,
    ∀ t2 K2 t3 K3 (p : proph_id) (ps : list string) (w : val),
      {{{ spec_verifier t2 (fill K2 (v2 w)) ∗
          spec_ideal t3 (fill K3 (v3 #())) ∗
          is_proph_proof w p ps
      }}}
        v1 #p #()
      {{{ ps1 ps2 (w1 w2 a1 a2 a3 : val), RET (w1, a1)%V;
          ⌜ps = ps1 ++ ps2⌝ ∗
          ⌜is_proof w1 ps1⌝ ∗ is_proph_proof w2 p ps2 ∗
          spec_verifier t2 (fill K2 (SOMEV (w2, a2)%V)) ∗
          spec_ideal t3 (fill K3 a3) ∗ A a1 a2 a3
      }}})%I.

  Program Definition lrel_auth_comp : kindO Σ (⋆ ⇒ ⋆)%kind := λne A, lrel_auth_comp' A.
  Next Obligation. solve_proper. Qed.

  Definition auth_ctx {Θ} (Δ : ctxO Σ Θ) := ext (ext Δ lrel_auth) lrel_auth_comp.

  Lemma refines_auth_return Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆, var0 → var1 var0 ⟧ (auth_ctx Δ) p_return v_return i_return.
  Proof.
    iIntros (A ???) "!# _"; rewrite -/interp.
    iIntros (????) "Hv Hi".
    rewrite /p_return /v_return /i_return.
    wp_pures; v_pures; i_pures.
    iModIntro. iFrame.
    iIntros (a1 a2 a3) "!# #HA"; rewrite -!/interp /=.
    iIntros (????) "Hv Hi".
    wp_pures; v_pures; i_pures.
    iModIntro. iFrame. clear.
    iIntros (??????? Ψ) "!# (Hv & Hi & Hproph) HΨ".
    v_pures; i_pures; wp_pures.
    iModIntro.
    iApply ("HΨ" $! []).
    by iFrame "∗ #".
  Qed.

  Lemma vals_compare_safe_admit :
    ∀ v w, vals_compare_safe v w.
  Proof. Admitted.

  Lemma injective_lrel (A: lrel Σ) :
    ∀ v1 v2 w1 w2 x1 x2, A x1 v1 w1 -∗ A x2 v2 w2 -∗ ⌜(v1 = v2 ↔ w1 = w2) ∧ (x1 = x2 ↔ w1 = w2)⌝.
  Proof. Admitted.

  Lemma refines_auth_eqauth Θ (Δ: ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆, var2 var0 → var2 var0 → var1 t_bool ⟧
      (auth_ctx Δ) p_eqauth v_eqauth i_eqauth.
  Proof.
    iIntros (A ???) "!# _"; rewrite -/interp.
    iIntros (????) "Hv Hi".
    rewrite /p_eqauth/v_eqauth/i_eqauth.
    wp_pures; v_pures; i_pures.
    iModIntro. iFrame. clear.
    iIntros (v1 v2 v3) "!# #HmA"; rewrite -!/interp.
    iIntros (????) "Hv Hi /=".
    wp_pures; v_pures; i_pures.
    iModIntro. iFrame. clear.
    iIntros (w1 w2 w3) "!# #HmB".
    iIntros (????) "Hv Hi".
    wp_pures; v_pures; i_pures.
    iModIntro. iFrame. clear.
    iIntros (??????? Ψ) "!# (Hv & Hi & Hproph) HΨ".
    wp_pures; v_pures; i_pures.
    { apply vals_compare_safe_admit. }
    { apply vals_compare_safe_admit. }
    Unshelve. 3: done.
    iDestruct "HmA" as (tA' a1 a2 sa -> Hsa ->) "(Hsa & #HA)".
    iDestruct "HmB" as (tB' b1 b2 sb -> Hsb ->) "(Hsb & #HB)".
    wp_pures.
    case_bool_decide.
    - case_bool_decide.
      + subst.
        destruct (decide (collision sa sb)) as [|Hnc%not_collision].
        { iExFalso. by iApply (hashes_auth.hashed_inj_or_coll with "Hsa Hsb"). }
        destruct Hnc as [<- |?]; simplify_eq.
        pose proof (evi_type_ser_inj_val tA' tB' a2 b2 sa Hsa Hsb) as Hs.
        subst.
        iPoseProof (injective_lrel A with "HA HB") as "%H".
        destruct H as [_ H].
        destruct H as [_ H].
        destruct H; [done|].
        wp_pure.
        { apply vals_compare_safe_admit. }
        case_bool_decide; [|done].
        wp_pures.
        iModIntro.
        iApply ("HΨ" $! []).
        iFrame "∗ # %".
        do 2 (iSplit; [iPureIntro; done|]).
        iExists _. done.
      + destruct (decide (collision sa sb)) as [|Hnc%not_collision].
        { iExFalso. by iApply (hashes_auth.hashed_inj_or_coll with "Hsa Hsb"). }
        destruct Hnc as [<- |?]; simplify_eq.
        pose proof (evi_type_ser_inj_val tA' tB' a2 b2 sa Hsa Hsb) as Hs.
        subst.
        iPoseProof (injective_lrel A with "HA HB") as "%H".
        destruct H as [H _].
        destruct H.
        destruct H; done.
    - case_bool_decide.
      + iPoseProof (injective_lrel A with "HA HB") as "%H1".
        iAssert (⌜sa = sb → False⌝)%I as "%H2".
        { iIntros (?).
          destruct (decide (collision sa sb)) as [|Hnc%not_collision].
          { by iApply (hashes_auth.hashed_inj_or_coll with "Hsa Hsb"). }
          destruct Hnc as [<- |?]; simplify_eq. }
        assert (H3 : a2 ≠ b2).
        { intros ?.
          subst.
          pose proof (evi_type_ser_inj_str tA' tB' b2 sa sb Hsa Hsb) as Hs.
          done. }
        destruct H1 as [H1 _].
        destruct H1 as [_ H1].
        pose proof (H1 H0) as H4.
        done.
      + iPoseProof (injective_lrel A with "HA HB") as "%H1".
        assert (a1 ≠ b1).
        { destruct H1 as [_ H1].
          intros ?.
          destruct H1 as [H1 _].
          pose proof (H1 H2) as H3.
          done. }
        wp_pure.
        { apply vals_compare_safe_admit. }
        case_bool_decide.
        { by inversion H3. }
        wp_pures.
        iModIntro.
        iApply ("HΨ" $! []).
        iFrame "∗ # %".
        do 2 (iSplit; [iPureIntro; done|]).
        iExists _. done.
  Qed.

  Lemma refines_auth_bind Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆; ⋆, var2 var1 → (var1 → var2 var0) → var2 var0 ⟧
      (auth_ctx Δ) p_bind v_bind i_bind.
  Proof.
    iIntros (A ???) "!# _"; rewrite -/interp.
    iIntros (????)  "Hv Hi".
    rewrite /p_bind/v_bind/i_bind.
    wp_pures; v_pures; i_pures.
    iModIntro. iFrame. clear.
    iIntros (B ???) "!# _"; rewrite -/interp.
    iIntros (????) "Hv Hi".
    wp_pures; v_pures; i_pures.
    iModIntro. iFrame. clear.
    iIntros (v1 v2 v3) "!# #HmA"; rewrite -!/interp.
    iIntros (????) "Hv Hi /=".
    wp_pures; v_pures; i_pures.
    iModIntro. iFrame. clear.
    iIntros (w1 w2 w3) "!# #HAmB".
    iIntros (????) "Hv Hi".
    wp_pures; v_pures; i_pures.
    iModIntro. iFrame. clear.
    iIntros (??????? Ψ) "!# (Hv & Hi & Hproph) HΨ".
    wp_pures; v_pures; i_pures.

    wp_bind (v1 #p #()); v_bind (v2 _); i_bind (v3 _).
    wp_apply ("HmA" with "[$Hv $Hi $Hproph]").
    iIntros (ps1 ps2 prf1 prf2 a1 a2 a3) "(%Hps & % & Hprf2 & Hv & Hi & #HA) /=".
    wp_pures. v_pures.

    wp_bind (w1 a1); v_bind (w2 a2); i_bind (w3 a3).
    iSpecialize ("HAmB" with "HA Hv Hi").
    wp_apply (wp_wand with "HAmB").
    iIntros (?) "(% & % & Hv & Hi & #HmB) /=".

    wp_apply ("HmB" with "[$Hv $Hi $Hprf2]").
    iIntros (ps3 ps4 ?????) "(%Hps' & % & Hprf4 & Hv & Hi & HB)".
    wp_pures.

    wp_apply gwp_list_append; [done|].
    iIntros (? Hprf). wp_pures.
    iModIntro. iApply ("HΨ" $! (ps1 ++ ps3) ps4).
    iFrame.
    rewrite Hps Hps' -assoc //.
  Qed.

  Lemma refines_auth_unauth Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆, var1 var0 → var3 var0 → var2 var0 ⟧
      (ext (auth_ctx Δ) lrel_evidence) p_unauth v_unauth i_unauth.
  Proof.
    iIntros (A ???) "!# _"; rewrite -/interp.
    iIntros (????) "Hv Hi".
    rewrite /p_unauth /v_unauth /i_unauth.
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iIntros (???) "!#"; rewrite -!/interp /=.
    iDestruct 1 as (tA p_ser v_ser v_deser -> ->) "#Hser".
    iIntros (????) "Hv Hi".
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iIntros (???) "!# #Hauth /=".
    iIntros (????) "Hv Hi".
    v_pures; i_pures; wp_pures.
    iDestruct "Hauth" as (tA' a1 a2 s -> Hs ->) "(Hs & #HA)".

    iModIntro. iFrame.
    iIntros (??????? Ψ) "!# (Hv & Hi & [%Hprf Hproph]) HΨ".
    v_pures; i_pures; wp_pures.

    wp_apply ("Hser" with "HA").
    iIntros (s') "(%Hs' & #Hser' & #Hdeser)".
    wp_pures.
    wp_apply (wp_resolve_proph_string with "Hproph").
    iIntros (vs') "[% Hproph]".
    destruct ps; simplify_eq/=.
    destruct Hprf as (v & -> & ?).
    wp_seq.

    v_bind (list_head _).
    iMod (gwp_list_head (A := string) ⊤ _ (_ :: _) () (λ v, ⌜v = SOMEV #s'⌝)%I
           with "[] [] [$Hv //]") as (?) "[Hv ->] /="; [by iExists _| |].
    { iIntros "!>" (? [[] | (?&?&?&?)]); simplify_eq. eauto. }
    v_pures.

    v_bind (Hash _).
    iMod (step_verifier_hash with "Hv") as "Hv /="; [done|].
    v_pures.
    { (* TODO: why does this case fail??? *) solve_vals_compare_safe. }

    pose proof (evi_type_ser_inj_str _ _ _ _ _ Hs Hs'). subst.
    iEval (rewrite bool_decide_eq_true_2 //) in "Hv".
    v_pures.
    v_bind (v_deser _).
    iMod ("Hdeser" with "[$Hv $HA //]") as "Hv /=".

    wp_apply (gwp_list_singleton _ s' with "[//]").
    iIntros (??). wp_pures.

    v_pures.
    v_bind (list_tail _).
    iMod (gwp_list_tail (A := string) ⊤ _ (_ :: _) () (λ v, ⌜is_list vs' v⌝)%I
           with "[] [] [$Hv //]") as (w') "[Hv %Hprf'] /="; [by iExists _| |].
    { by iIntros "!>" (?). }
    v_pures.

    assert (v = w') as -> by by eapply (is_list_eq (A := string)).
    iModIntro. iApply ("HΨ" $! [_]).
    by iFrame "# ∗ %".
  Qed.

  Lemma refines_Authenticatable Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ Authenticatable ⟧ (auth_ctx Δ) p_Authenticable v_Authenticable i_Authenticable.
  Proof.
    iExists lrel_evidence; rewrite -/interp.
    iExists  _, _, _, _, _, _; rewrite -/interp.
    do 3 (iSplit; [done|]).
    iSplit; last first.
    { iApply refines_auth_unauth. }
    iExists _, _, _, _, _, _; rewrite -/interp.
    do 3 (iSplit; [done|]).
    iSplit; last first.
    { iApply refines_auth_auth. }
    iExists _, _, _, _, _, _; rewrite -!/interp.
    do 3 (iSplit; [done|]).
    iSplit; last first.
    { iApply refines_Auth_int. }
    iExists _, _, _, _, _, _; rewrite -!/interp.
    do 3 (iSplit; [done|]).
    iSplit; last first.
    { iApply refines_Auth_string. }
    iExists _, _, _, _, _, _; rewrite -!/interp.
    do 3 (iSplit; [done|]).
    iSplit; last first.
    { iApply refines_Auth_sum. }
    iExists _, _, _, _, _, _; rewrite -!/interp.
    do 3 (iSplit; [done|]).
    iSplit; last first.
    { iApply refines_Auth_pair. }
    iExists _, _, _, _, _, _; rewrite -!/interp.
    do 3 (iSplit; [done|]).
    iSplit; last first.
    { iApply refines_Auth_mu. }
    iApply refines_Auth_auth.
  Qed.

  Lemma refines_authentikit_func Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ Authentikit_func var1 var0 ⟧ (auth_ctx Δ) p_Authentikit v_Authentikit i_Authentikit.
  Proof.
    iExists _, _, _, _, _, _; rewrite -!/interp.
    do 3 (iSplit; [done|]).
    iSplit; last first.
    { iApply refines_Authenticatable. }
    iExists _, _, _, _, _, _; rewrite -/interp.
    do 3 (iSplit; [done|]).
    iSplit; [iApply refines_auth_return|].
    iApply refines_auth_bind.
  Qed.

  Lemma refines_authentikit_func_eq Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ Authentikit_func_eq var1 var0 ⟧ (auth_ctx Δ) p_Authentikit_eq v_Authentikit_eq i_Authentikit_eq.
  Proof.
    iExists _, _, _, _, _, _; rewrite -!/interp.
    do 3 (iSplit; [done|]).
    iSplit; last first.
    { iApply refines_Authenticatable. }
    iExists _, _, _, _, _, _; rewrite -/interp.
    do 3 (iSplit; [done|]).
    iSplit; last first.
    { iApply refines_auth_eqauth. }
    iExists _, _, _, _, _, _; rewrite -/interp.
    do 3 (iSplit; [done|]).
    iSplit; [iApply refines_auth_return|].
    iApply refines_auth_bind.
  Qed.

  Lemma refines_authentikit Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ Authentikit ⟧ Δ p_Authentikit v_Authentikit i_Authentikit.
  Proof.
    iExists lrel_auth, lrel_auth_comp; rewrite -3!/interp.
    iApply refines_authentikit_func.
  Qed.

  Lemma refines_authentikit_eq Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ Authentikit_eq ⟧ Δ p_Authentikit_eq v_Authentikit_eq i_Authentikit_eq.
  Proof.
    iExists lrel_auth, lrel_auth_comp; rewrite -3!/interp.
    iApply refines_authentikit_func_eq.
  Qed.

  Definition rel_authentikit_output (A : lrel Σ) (prf : val) (ps : list string) : lrel Σ :=
    LRel (λ v1 v2 v3, ∃ a1 a2 a3, ⌜v1 = (prf, a1)%V⌝ ∗ ⌜v2 = SOMEV a2⌝ ∗ ⌜v3 = a3⌝ ∗ A a1 a2 a3)%I.

  Lemma refines_run Θ (Δ : ctxO Σ Θ) (p : proph_id) ps (c1 c2 c3 : expr) w A :
    is_proph_proof w p ps -∗
    (REL c1 << c2 << c3 : lrel_auth_comp A) -∗
    REL p_run #~ #p c1 << v_run #~ c2 w << i_run #~ c3 : rel_authentikit_output A w ps.
  Proof.
    iIntros "[%Hprf Hproph] Hc" (????) "Hv Hi".
    rewrite /v_run /i_run /p_run.
    v_bind c2; i_bind c3; wp_bind (c1).

    iSpecialize ("Hc" with "Hv Hi").
    wp_apply (wp_wand with "Hc").
    iIntros (f1) "(%f2 & %f3 & Hv & Hi & Hc) /=".
    wp_pures; v_pures; i_pures.
    v_bind (f2 w).
    wp_apply ("Hc" with "[$Hproph $Hv $Hi //]").
    iIntros (ps1 ps2 w1 w2 a1 a2 a3) "(-> & %Hprf1 & [% Hp] & Hv & Hi & HA) /=".
    v_pures.
    wp_pures.
    wp_apply (wp_resolve_proph_nil with "Hp"); iIntros (->).
    wp_pures.
    iFrame.
    apply is_list_inject in Hprf1 as ->, Hprf as ->.
    rewrite app_nil_r //.
  Qed.

  Lemma refines_instantiate (c1 c2 c3 : expr) (τ : type _ ⋆) :
    (REL c1 << c2 << c3 : ⟦ ∀: ⋆ ⇒ ⋆; ⋆ ⇒ ⋆, Authentikit_func var1 var0 → var0 τ ⟧ ∅) -∗
    REL c1 #~ #~ p_Authentikit
     << c2 #~ #~ v_Authentikit
     << c3 #~ #~ i_Authentikit : lrel_auth_comp (⟦ τ ⟧ (auth_ctx ∅)).
  Proof.
    iIntros "Hc" (????) "Hv Hi".
    wp_bind c1; v_bind c2; i_bind c3.
    iSpecialize ("Hc" with "Hv Hi").
    wp_apply (wp_wand with "Hc").
    iIntros (v1) "(%v2 & %v3 & Hv & Hi & Hcnt)".
    iSpecialize ("Hcnt" $! lrel_auth with "[//]"); rewrite -/interp.
    v_bind (v2 _); i_bind (v3 _).
    iSpecialize ("Hcnt" with "Hv Hi").
    wp_apply (wp_wand with "Hcnt").
    iIntros (v1') "(%v2' & %v3' & Hv & Hi & Hcnt)".
    iSpecialize ("Hcnt" $! lrel_auth_comp with "[//]"); rewrite -/interp.
    v_bind (v2' _); i_bind (v3' _).
    iSpecialize ("Hcnt" with "Hv Hi").
    wp_apply (wp_wand with "Hcnt").
    iIntros (v1'') "(%v2'' & %v3'' & Hv & Hi & Hcnt)".
    v_bind (v2'' _); i_bind (v3'' _).
    iSpecialize ("Hcnt" with "[] Hv Hi"); rewrite -!/interp.
    { iApply refines_authentikit_func. }
    wp_apply (wp_wand with "Hcnt").
    iIntros (v1''') "(%v2''' & %v3''' & Hv & Hi & Hcnt)".
    iFrame.
  Qed.

  Lemma refines_instantiate_eq (c1 c2 c3 : expr) (τ : type _ ⋆) :
    (REL c1 << c2 << c3 : ⟦ ∀: ⋆ ⇒ ⋆; ⋆ ⇒ ⋆, Authentikit_func_eq var1 var0 → var0 τ ⟧ ∅) -∗
    REL c1 #~ #~ p_Authentikit_eq
     << c2 #~ #~ v_Authentikit_eq
     << c3 #~ #~ i_Authentikit_eq : lrel_auth_comp (⟦ τ ⟧ (auth_ctx ∅)).
  Proof.
    iIntros "Hc" (????) "Hv Hi".
    wp_bind c1; v_bind c2; i_bind c3.
    iSpecialize ("Hc" with "Hv Hi").
    wp_apply (wp_wand with "Hc").
    iIntros (v1) "(%v2 & %v3 & Hv & Hi & Hcnt)".
    iSpecialize ("Hcnt" $! lrel_auth with "[//]"); rewrite -/interp.
    v_bind (v2 _); i_bind (v3 _).
    iSpecialize ("Hcnt" with "Hv Hi").
    wp_apply (wp_wand with "Hcnt").
    iIntros (v1') "(%v2' & %v3' & Hv & Hi & Hcnt)".
    iSpecialize ("Hcnt" $! lrel_auth_comp with "[//]"); rewrite -/interp.
    v_bind (v2' _); i_bind (v3' _).
    iSpecialize ("Hcnt" with "Hv Hi").
    wp_apply (wp_wand with "Hcnt").
    iIntros (v1'') "(%v2'' & %v3'' & Hv & Hi & Hcnt)".
    v_bind (v2'' _); i_bind (v3'' _).
    iSpecialize ("Hcnt" with "[] Hv Hi"); rewrite -!/interp.
    { iApply refines_authentikit_func_eq. }
    wp_apply (wp_wand with "Hcnt").
    iIntros (v1''') "(%v2''' & %v3''' & Hv & Hi & Hcnt)".
    iFrame.
  Qed.

End proof.

Theorem authentikit_correctness Σ `{authPreG Σ}
  (A : ∀ `{authG Σ}, lrel Σ) (φ : val → val → val → Prop) (cₚ cᵥ cᵢ : expr) (σ : state) (p : proph_id) :
  p ∈ σ.(used_proph_id) →
  (∀ `{authG Σ}, ∀ vₚ vᵥ vᵢ, A vₚ vᵥ vᵢ -∗ ⌜φ vₚ vᵥ vᵢ⌝) →
  (∀ `{authG Σ}, ⊢ REL cₚ << cᵥ << cᵢ : lrel_auth_comp A) →
  adequate hash_collision NotStuck (p_run #~ #p cₚ) σ
    (λ vₚ σₚ, ∃ thpᵥ thpᵢ σᵥ σᵢ a1 a2 a3 prf,
        (** The prover outputs a proof [prf] and [a1]  *)
        vₚ = (prf, a1)%V ∧
        (** there exists a valid verifier execution with the prover's proof [prf] returning [a2] *)
        rtc erased_step ([v_run #~ cᵥ prf], σ) (of_val (SOMEV a2) :: thpᵥ, σᵥ) ∧
        (** and a valid ideal execution returning [a3] *)
        rtc erased_step ([i_run #~ cᵢ], σ) (of_val a3 :: thpᵢ, σᵢ) ∧
        (** [φ] holds *)
        φ a1 a2 a3).
Proof.
  intros Hp HA Hcomp.
  eapply (heap_adequacy_strong_proph Σ _ (λ p, p_run #~ #p cₚ)); [done|].
  clear p Hp.
  iIntros (Hinv p pvs) "_ Hp".
  iAssert (∃ v ps, ⌜is_proof v ps⌝ ∗ proph_proof p ps)%I
    with "[Hp]" as (v ps) "[% Hproph]".
  { rewrite /proph_proof /=. iFrame.
    iExists _, _. rewrite /is_proof is_list_inject //. }

  iMod (cfg_alloc (v_run #~ cᵥ v) σ) as (Hcfgᵥ) "[Hauthᵥ Heᵥ]".
  iMod (cfg_alloc (i_run #~ cᵢ) σ) as (Hcfgᵢ) "[Hauthᵢ Heᵢ]".
  set (Hcfg := AuthG _ _ Hcfgᵥ Hcfgᵢ).
  iMod (inv_alloc specN _ (spec_inv _ _) with "[Hauthᵥ Hauthᵢ]") as "#Hcfg".
  { iNext. iExists _, _, _, _. iFrame "# ∗ %". eauto. }
  iAssert (spec_ctx) as "#Hctx"; [by iExists _, _|].

  wp_apply wp_fupd.
  wp_apply (wp_wand with "[-]").
  { iPoseProof (refines_run _ ∅ with "[$Hproph //] []") as "Hrun"; [iApply Hcomp|].
    wp_apply ("Hrun" $! [] _ [] with "[$Heᵥ $Hctx] [$Heᵢ $Hctx]"). }

  iIntros (w) "(% & % & [_ Hv] & [_ Hi] & Hout)".
  iDestruct "Hout" as (??? -> -> ->) "HA".
  iDestruct (HA with "HA") as %Hφ.

  iInv specN as (tpᵥ σᵥ tpᵢ σᵢ) ">(Hauthᵥ & Hauthᵢ & %Hexecᵥ & %Hexecᵢ)" "Hclose".
  iDestruct (cfg_auth_tpool_agree with "Hauthᵥ Hv") as %?.
  iDestruct (cfg_auth_tpool_agree with "Hauthᵢ Hi") as %?.
  destruct tpᵥ as [|? tpᵥ]; [simplify_eq/=|].
  destruct tpᵢ as [|? tpᵢ]; [simplify_eq/=|].
  iMod ("Hclose" with "[-]") as "_".
  { iFrame "∗ % #". }
  iModIntro.
  simplify_list_eq.
  iIntros (σₚ ???) "(?&?&?&?) !%".
  do 8 eexists. eauto.
Qed.

Theorem authentikit_correctness_syntactic (c : expr) (σ : state) (τ : type _ ⋆) (p : proph_id) :
  p ∈ σ.(used_proph_id) →
  EqType τ →
  ε |ₜ ∅ ⊢ₜ c : (∀: ⋆ ⇒ ⋆; ⋆ ⇒ ⋆, Authentikit_func var1 var0 → var0 τ) →
  adequate hash_collision NotStuck (p_run #~ #p (c #~ #~ p_Authentikit)) σ
    (λ vₚ σₚ, ∃ thpᵥ thpᵢ σᵥ σᵢ a prf,
        (** The prover outputs a proof [prf] and [a]  *)
        vₚ = (prf, a)%V ∧
        (** there exists a valid verifier execution with the prover's proof [prf] returning [a] *)
        rtc erased_step ([v_run #~ (c #~ #~ v_Authentikit) prf], σ) (of_val (SOMEV a) :: thpᵥ, σᵥ) ∧
        (** and a valid ideal execution returning [a] *)
        rtc erased_step ([i_run #~ (c #~ #~ i_Authentikit)], σ) (of_val a :: thpᵢ, σᵢ)).
Proof.
  intros Hp Hτ Htyped.
  set (φ := λ (v1 v2 v3 : val), v1 = v2 ∧ v2 = v3).
  set (c1 := (c #~ #~ p_Authentikit)).
  set (c2 := (c #~ #~ v_Authentikit)).
  set (c3 := (c #~ #~ i_Authentikit)).
  suff: (adequate hash_collision NotStuck (p_run #~ #p c1) σ
          (λ vₚ σₚ, ∃ thpᵥ thpᵢ σᵥ σᵢ a1 a2 a3 prf,
              vₚ = (prf, a1)%V ∧
              rtc erased_step ([v_run #~ c2 prf], σ) (of_val (SOMEV a2) :: thpᵥ, σᵥ) ∧
              rtc erased_step ([i_run #~ c3], σ) (of_val a3 :: thpᵢ, σᵢ) ∧
              φ a1 a2 a3)).
  { intros []. split; [|done]. intros ?????.
    edestruct adequate_result as (?&?&?&?&?&?&?&?&?&?&?&?&?); [done|done|].
    simplify_eq. do 6 eexists. eauto. }
  apply (authentikit_correctness authΣ (λ a, ⟦ τ ⟧ (auth_ctx ∅))); [done| |].
  { iIntros (????) "Hτ". by iDestruct (eq_type_sound with "Hτ") as %[]. }
  iIntros (?).
  iApply refines_instantiate.
  by iApply refines_typed.
Qed.

Theorem authentikit_eq_correctness_syntactic (c : expr) (σ : state) (τ : type _ ⋆) (p : proph_id) :
  p ∈ σ.(used_proph_id) →
  EqType τ →
  ε |ₜ ∅ ⊢ₜ c : (∀: ⋆ ⇒ ⋆; ⋆ ⇒ ⋆, Authentikit_func_eq var1 var0 → var0 τ) →
  adequate hash_collision NotStuck (p_run #~ #p (c #~ #~ p_Authentikit_eq)) σ
    (λ vₚ σₚ, ∃ thpᵥ thpᵢ σᵥ σᵢ a prf,
        (** The prover outputs a proof [prf] and [a]  *)
        vₚ = (prf, a)%V ∧
        (** there exists a valid verifier execution with the prover's proof [prf] returning [a] *)
        rtc erased_step ([v_run #~ (c #~ #~ v_Authentikit_eq) prf], σ) (of_val (SOMEV a) :: thpᵥ, σᵥ) ∧
        (** and a valid ideal execution returning [a] *)
        rtc erased_step ([i_run #~ (c #~ #~ i_Authentikit_eq)], σ) (of_val a :: thpᵢ, σᵢ)).
Proof.
  intros Hp Hτ Htyped.
  set (φ := λ (v1 v2 v3 : val), v1 = v2 ∧ v2 = v3).
  set (c1 := (c #~ #~ p_Authentikit_eq)).
  set (c2 := (c #~ #~ v_Authentikit_eq)).
  set (c3 := (c #~ #~ i_Authentikit_eq)).
  suff: (adequate hash_collision NotStuck (p_run #~ #p c1) σ
          (λ vₚ σₚ, ∃ thpᵥ thpᵢ σᵥ σᵢ a1 a2 a3 prf,
              vₚ = (prf, a1)%V ∧
              rtc erased_step ([v_run #~ c2 prf], σ) (of_val (SOMEV a2) :: thpᵥ, σᵥ) ∧
              rtc erased_step ([i_run #~ c3], σ) (of_val a3 :: thpᵢ, σᵢ) ∧
              φ a1 a2 a3)).
  { intros []. split; [|done]. intros ?????.
    edestruct adequate_result as (?&?&?&?&?&?&?&?&?&?&?&?&?); [done|done|].
    simplify_eq. do 6 eexists. eauto. }
  apply (authentikit_correctness authΣ (λ a, ⟦ τ ⟧ (auth_ctx ∅))); [done| |].
  { iIntros (????) "Hτ". by iDestruct (eq_type_sound with "Hτ") as %[]. }
  iIntros (?).
  iApply refines_instantiate_eq.
  by iApply refines_typed.
Qed.
