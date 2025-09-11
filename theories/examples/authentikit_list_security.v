From auth.prelude Require Import stdpp.
From auth.rel_logic_bin Require Export model spec_rules spec_tactics interp lib adequacy fundamental.
From auth.heap_lang.lib Require Import list serialization.
From auth.examples Require Export authentikit_list authentikit_base_security.

(** * Proof *)
Section proof.
  Context `{!authG Σ}.

  Definition lrel_auth_comp_post (A : lrel Σ) : lrel Σ :=
    LRel (λ v1 a2, ∃ a1 prf1, ⌜v1 = (prf1, a1)%V⌝ ∗ is_proof prf1 ∗ A a1 a2)%I.

  Definition lrel_auth_comp' (A : lrel Σ) : lrel Σ := LRel (λ v1 v2,
     □ ∀ p, is_proof p -∗ refines_Some ⊤ (v1 p) (v2 #()) (lrel_auth_comp_post A))%I.

  Program Definition lrel_auth_comp : kindO Σ (⋆ ⇒ ⋆)%kind := λne A, lrel_auth_comp' A.
  Next Obligation.
    intros ??? ???.
    rewrite {1 2}/lrel_car /=.
    rewrite /refines_Some.
    do 19 f_equiv.
    solve_proper.
  Qed.

  Definition auth_ctx {Θ} (Δ : ctxO Σ Θ) := ext (ext Δ lrel_auth) lrel_auth_comp.

  Lemma refines_auth_return Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆, var0 → var1 var0 ⟧ (auth_ctx Δ) v_return i_return.
  Proof.
    iIntros (A ??) "!# _".
    iIntros (??) "Hi".
    rewrite /v_return /i_return.
    i_pures; wp_pures.
    iModIntro. iFrame.
    iIntros (??) "!# #HA".
    iIntros (??) "Hi".
    i_pures; wp_pures.
    iModIntro. iFrame. clear.
    rewrite /auth_ctx.
    interp_unfold!.
    iIntros "!#" (??).
    iIntros (??) "Hi".
    i_pures; wp_pures.
    iModIntro. iExists (Some _).
    iFrame "Hi". iSplit; [done|].
    iExists _, _.
    interp_unfold! in "HA".
    eauto.
  Qed.

  Lemma refines_auth_bind Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆; ⋆, var2 var1 → (var1 → var2 var0) → var2 var0 ⟧
      (auth_ctx Δ) v_bind i_bind.
  Proof.
    iIntros (A ??) "!# _".
    iIntros (??) "Hi".
    rewrite /v_bind/i_bind.
    i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iIntros (B ??) "!# _".
    iIntros (??) "Hi".
    i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iIntros (v1 v2) "!# #HmA".
    iIntros (??) "Hi".
    simpl.
    i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iIntros (w1 w2) "!# #HmB".
    iIntros (??) "Hi".
    i_pures; wp_pures.
    iModIntro. iFrame. clear.
    interp_unfold!.
    iIntros "!# % Hprf1".
    iIntros (??)  "Hi".
    i_pures; wp_pures.
    i_bind (v2 _)%I; wp_bind (v1 _)%I.
    interp_unfold! in "HmA".
    iSpecialize ("HmA" with "Hprf1 Hi").
    wp_apply (wp_wand with "HmA").
    iIntros (v) "(% & -> & H)".
    destruct o; last first.
    { wp_pures. by iExists None. }
    iDestruct "H" as (?) "[Hi Ho] /=".
    iDestruct "Ho" as (a1 prf1 ->) "[#Hprf1' #HA]".
    wp_pures.
    wp_bind (w1 _)%E; i_bind (w2 _ )%E.
    iSpecialize ("HmB" $! _ with "[HA] Hi").
    { by interp_unfold. }
    wp_apply (wp_wand with "HmB").
    iIntros (v) "(% & Hi & H) /=".
    interp_unfold in "H".
    iSpecialize ("H" with "[$Hprf1' //] Hi").
    wp_apply wp_fupd.
    iApply wp_wand_l; iFrame.
    iIntros (w) "(% & -> & H) /=".
    iModIntro. by iFrame "∗ #".
  Qed.

  Lemma vals_compare_safe_admit :
    ∀ v w, vals_compare_safe v w.
  Proof. Admitted.

  Lemma refines_auth_eqauth Θ (Δ: ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆, var2 var0 → var2 var0 → var1 t_bool ⟧
      (auth_ctx Δ) v_eqauth i_eqauth.
  Proof.
    iIntros (A ??) "!# _".
    iIntros (??) "Hi".
    rewrite /v_eqauth/i_eqauth.
    i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iIntros (v1 v2) "!# #HmA".
    iIntros (??) "Hi".
    i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iIntros (w1 w2) "!# #HmB".
    iIntros (??) "Hi".
    i_pures; wp_pures.
    iModIntro. iFrame. clear.
    interp_unfold!.
    iIntros (x1 x2) "!#".
    iIntros (??) "Hi".
    i_pures.
    { apply vals_compare_safe_admit. }
    interp_unfold! in "HmA"; interp_unfold! in "HmB".
    iDestruct "HmA" as (???? ->) "(HinjA & HA & HashA)".
    iDestruct "HmB" as (???? ->) "(HinjA' & HA' & HashA')".

    case_bool_decide.
    - wp_pures. iModIntro.
      iExists (Some _). iFrame. clear.
      iSplit. { eauto. }
      iDestruct ("HinjA"  with "HA HA'") as %[H21 H22].
      pose proof (H22 H1) as H2.
      subst.
      pose proof (evi_type_ser_inj_str t t0 a0 s1 s0 H H0) as Hs.
      subst.
      case_bool_decide.
      + iExists _, _.
        iSplit; [done|].
        iSplit; [done|].
        iExists _. iPureIntro; done.
      + done.
    - wp_pures. iModIntro.
      iExists (Some _). iFrame.
      iSplit. { eauto. }
      iDestruct ("HinjA"  with "HA HA'") as %[H21 H22].
      subst.
      case_bool_decide.
      + destruct (decide (collision s1 s0)) as [|Hnc%not_collision].
        { iExFalso. by iApply (hashes_auth.hashed_inj_or_coll with "HashA HashA'"). }
        destruct Hnc as [<- |?]; simplify_eq.
        exfalso.
        apply H1.
        apply H21.
        apply (evi_type_ser_inj_val t t0 _ _ s1); done.
      + iExists _, _.
        iSplit; [done|].
        iSplit; [done|].
        iExists _. iPureIntro; done.
  Qed.

  Lemma refines_auth_unauth Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆, var1 var0 → var3 var0 → var2 var0 ⟧
      (ext (auth_ctx Δ) lrel_evidence) v_unauth i_unauth.
  Proof.
    iIntros (A v1 v2) "!# _".
    iIntros (??) "Hi".
    rewrite /v_unauth /i_unauth.
    i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iIntros (??) "!# #Hevi".
    iIntros (??) "Hi".
    i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iIntros (w1 w2) "!# #Hauth /=".
    iIntros (??) "Hi".
    i_pures.
    interp_unfold! in "Hauth".
    iDestruct "Hauth" as (a1 tA s1 Hs1 ->) "(#HinjA & #HA & #Hs1)".
    interp_unfold! in "Hevi".
    iDestruct "Hevi" as (tA' ser deser ->) "(#Hinj & #Hser & #Hdeser)".
    wp_pures. iFrame. iModIntro.
    interp_unfold!.
    iIntros "!#" (? [? ?]).
    iIntros (??) "Hi".
    i_pures; wp_pures.
    wp_apply gwp_list_head; [done|].
    iIntros "/=" (vl [[-> ->] | (s1' &?& -> & -> )]).
    { wp_pures. by iExists None. }
    wp_pures.
    wp_apply (wp_hash with "[$]").
    iIntros "#Hs1'".
    wp_pures.
    case_bool_decide; simplify_eq; wp_pures; last first.
    { by iExists None. }
    wp_apply "Hdeser"; [done|].
    iIntros ([w|] Hs1'); wp_pures; last first.
    { by iExists None. }
    wp_apply gwp_list_tail; [done|].
    iIntros (tl Htl). wp_pures.
    iExists (Some _). iModIntro. iSplit; [done|].
    destruct (decide (collision s1 s1')) as [|Hnc%not_collision].
    { iExFalso. by iApply (hashes_auth.hashed_inj_or_coll with "Hs1 Hs1'"). }
    destruct Hnc as [<- |?]; [|simplify_eq].
    assert (a1 = w) as <- by by eapply (evi_type_ser_inj_val tA tA').
    iFrame. iExists _, _. by iFrame "HA %".
  Qed.

  Lemma refines_Authenticatable Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ Authenticatable ⟧ (auth_ctx Δ) v_Authenticable i_Authenticable.
  Proof.
    iExists lrel_evidence.
    iExists  _, _, _, _.
    do 2 (iSplit; [done|]).
    iSplit; last first.
    { iApply refines_auth_unauth. }
    iExists _, _, _, _.
    do 2 (iSplit; [done|]).
    iSplit; last first.
    { iApply refines_auth_auth. }
    iExists _, _, _, _.
    do 2 (iSplit; [done|]).
    iSplit; last first.
    { interp_unfold!. iApply refines_Auth_int. }
    iExists _, _, _, _.
    do 2 (iSplit; [done|]).
    iSplit; last first.
    { interp_unfold!. iApply refines_Auth_string. }
    iExists _, _, _, _.
    do 2 (iSplit; [done|]).
    iSplit; last first.
    { iApply refines_Auth_sum. }
    iExists _, _, _, _.
    do 2 (iSplit; [done|]).
    iSplit; last first.
    { iApply refines_Auth_pair. }
    iExists _, _, _, _.
    do 2 (iSplit; [done|]).
    iSplit; last first.
    { iApply refines_Auth_mu. }
    iApply refines_Auth_auth.
  Qed.

  Lemma refines_authentikit_func Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ Authentikit_func var1 var0 ⟧ (auth_ctx Δ) v_Authentikit i_Authentikit.
  Proof.
    rewrite interp_unseal -/interp.interp_def.
    iExists _, _, _, _. rewrite -!/interp.interp_def.
    do 2 (iSplit; [done|]).
    iSplit; last first.
    { iPoseProof refines_Authenticatable as "H". rewrite interp_unseal //. }
    iExists _, _, _, _. rewrite -!/interp.interp_def.
    do 2 (iSplit; [done|]).
    iSplit.
    { iPoseProof refines_auth_return as "H". rewrite interp_unseal //. }
    iPoseProof refines_auth_bind as "?".
    rewrite interp_unseal //.
  Qed.

  Lemma refines_authentikit_func_eq Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ Authentikit_func_eq var1 var0 ⟧ (auth_ctx Δ) v_Authentikit_eq i_Authentikit_eq.
  Proof.
    rewrite interp_unseal -/interp.interp_def.
    iExists _, _, _, _. rewrite -!/interp.interp_def.
    do 2 (iSplit; [done|]).
    iSplit; last first.
    { iPoseProof refines_Authenticatable as "H". rewrite interp_unseal //. }
    iExists _, _, _, _. rewrite -!/interp.interp_def.
    do 2 (iSplit; [done|]).
    iSplit; last first.
    { iPoseProof refines_auth_eqauth as "?". rewrite interp_unseal //. }
    iExists _, _, _, _. rewrite -!/interp.interp_def.
    do 2 (iSplit; [done|]).
    iSplit.
    { iPoseProof refines_auth_return as "H". rewrite interp_unseal //. }
    iPoseProof refines_auth_bind as "?".
    rewrite interp_unseal //.
  Qed.

  Lemma refines_authentikit Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ Authentikit ⟧ Δ v_Authentikit i_Authentikit.
  Proof.
    iExists lrel_auth, lrel_auth_comp.
    iApply refines_authentikit_func.
  Qed.

  Lemma refines_authentikit_eq Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ Authentikit_eq ⟧ Δ v_Authentikit_eq i_Authentikit_eq.
  Proof.
    iExists lrel_auth, lrel_auth_comp.
    iApply refines_authentikit_func_eq.
  Qed.

  Lemma refines_run w (c1 c2 : expr) A :
    is_proof w -∗
    (REL c1 << c2 : lrel_auth_comp A) -∗
    refines_Some ⊤ (v_run #~ c1 w) (i_run #~ c2) A.
  Proof.
    iIntros "#Hprf Hc" (??) "Hi".
    rewrite /v_run /i_run.
    wp_bind c1; i_bind c2.
    iSpecialize ("Hc" with "Hi").
    wp_apply (wp_wand with "Hc").
    iIntros (f1) "(%f2 & Hi & Hc) /=".
    wp_pures; i_pures.
    iSpecialize ("Hc" with "Hprf Hi").
    wp_apply (wp_wand with "Hc").
    iIntros (?) "(%o & -> & Ho)".
    destruct o; last first.
    { wp_pures. by iExists None. }
    iDestruct "Ho" as (?) "[Hi Hpost]".
    iDestruct "Hpost" as (?? ->) "[Hprf' HA]".
    wp_pures. iFrame. iModIntro.
    iExists (Some _). by iFrame.
  Qed.

  Lemma refines_instantiate (c1 c2 : expr) (τ : type _ ⋆) :
    (REL c1 << c2 : ⟦ ∀: ⋆ ⇒ ⋆; ⋆ ⇒ ⋆, Authentikit_func var1 var0 → var0 τ ⟧ ∅) -∗
    REL c1 #~ #~ v_Authentikit
     << c2 #~ #~ i_Authentikit : lrel_auth_comp (⟦ τ ⟧ (auth_ctx ∅)).
  Proof.
    iIntros "Hc" (??) "Hi".
    wp_bind c1; i_bind c2.
    iSpecialize ("Hc" with "Hi").
    wp_apply (wp_wand with "Hc").
    iIntros (v1) "(%v2 & Hi & Hcnt)".
    iSpecialize ("Hcnt" $! lrel_auth with "[//]").
    i_bind (v2 _).
    iSpecialize ("Hcnt" with "Hi").
    wp_apply (wp_wand with "Hcnt").
    iIntros (v1') "(%v2' & Hi & Hcnt)".
    iSpecialize ("Hcnt" $! lrel_auth_comp with "[//]").
    i_bind (v2' _).
    iSpecialize ("Hcnt" with "Hi").
    wp_apply (wp_wand with "Hcnt").
    iIntros (v1'') "(%v2'' & Hi & Hcnt)".
    i_bind (v2'' _).
    iSpecialize ("Hcnt" $! _ with "[] Hi").
    { iApply refines_authentikit_func. }
    wp_apply (wp_wand with "Hcnt").
    iIntros (v1''') "(%v2'''& Hi & Hcnt)".
    rewrite interp_app_unfold.
    interp_unfold.
    iFrame.
  Qed.

  Lemma refines_instantiate_eq (c1 c2 : expr) (τ : type _ ⋆) :
    (REL c1 << c2 : ⟦ ∀: ⋆ ⇒ ⋆; ⋆ ⇒ ⋆, Authentikit_func_eq var1 var0 → var0 τ ⟧ ∅) -∗
    REL c1 #~ #~ v_Authentikit_eq
     << c2 #~ #~ i_Authentikit_eq : lrel_auth_comp (⟦ τ ⟧ (auth_ctx ∅)).
  Proof.
    iIntros "Hc" (??) "Hi".
    wp_bind c1; i_bind c2.
    iSpecialize ("Hc" with "Hi").
    wp_apply (wp_wand with "Hc").
    iIntros (v1) "(%v2 & Hi & Hcnt)".
    iSpecialize ("Hcnt" $! lrel_auth with "[//]").
    i_bind (v2 _).
    iSpecialize ("Hcnt" with "Hi").
    wp_apply (wp_wand with "Hcnt").
    iIntros (v1') "(%v2' & Hi & Hcnt)".
    iSpecialize ("Hcnt" $! lrel_auth_comp with "[//]").
    i_bind (v2' _).
    iSpecialize ("Hcnt" with "Hi").
    wp_apply (wp_wand with "Hcnt").
    iIntros (v1'') "(%v2'' & Hi & Hcnt)".
    i_bind (v2'' _).
    iSpecialize ("Hcnt" $! _ with "[] Hi").
    { iApply refines_authentikit_func_eq. }
    wp_apply (wp_wand with "Hcnt").
    iIntros (v1''') "(%v2'''& Hi & Hcnt)".
    rewrite interp_app_unfold.
    interp_unfold.
    iFrame.
  Qed.

End proof.

Theorem authentikit_security Σ `{authPreG Σ} (A : ∀ `{authG Σ}, lrel Σ)
  (φ : val → val → Prop) (cᵥ cᵢ : expr) (σ : state) (l : list string) (prf : val) :
  (∀ `{authG Σ}, ∀ vᵥ vᵢ, A vᵥ vᵢ -∗ ⌜φ vᵥ vᵢ⌝) →
  (∀ `{authG Σ}, ⊢ REL cᵥ << cᵢ : lrel_auth_comp A) →
  is_list l prf →
  adequate hash_collision NotStuck (v_run #~ cᵥ prf) σ
    (λ vᵥ σᵥ, ∃ thpᵢ σᵢ vᵢ o,
        vᵥ = $o ∧
        if o is Some wᵥ then
          (** a valid ideal execution *)
          rtc erased_step ([i_run #~ cᵢ], σ) (of_val vᵢ :: thpᵢ, σᵢ) ∧
          (** [φ] holds *)
            φ wᵥ vᵢ
        else True).
Proof.
  intros HA Hcomp Hprf.
  eapply (refines_Some_adequate Σ); [done|].
  iIntros (???) "Hi".
  wp_apply (wp_wand with "[Hi]").
  { wp_apply (refines_run prf with "[] [] Hi"); [eauto|]. iApply Hcomp. }
  iIntros (?) "(% & Hv & Hout)". iFrame.
Qed.

Theorem authentikit_security_syntactic (c : expr) (σ : state) (τ : type _ ⋆) prf (l : list string) :
  EqType τ →
  ε |ₜ ∅ ⊢ₜ c : (∀: ⋆ ⇒ ⋆; ⋆ ⇒ ⋆, Authentikit_func var1 var0 → var0 τ) →
  is_list l prf →
  adequate hash_collision NotStuck (v_run #~ (c #~ #~ v_Authentikit) prf) σ
    (λ vᵥ σᵥ, ∃ thpᵢ σᵢ vᵢ o,
        vᵥ = $o ∧
        if o is Some wᵥ then
          (** a valid ideal execution *)
          rtc erased_step ([i_run #~ (c #~ #~ i_Authentikit)], σ) (of_val vᵢ :: thpᵢ, σᵢ) ∧
          (** and they return the same value *)
          wᵥ = vᵢ
        else True).
Proof.
  intros Hτ Htyped Hprf.
  eapply (authentikit_security authΣ (λ a, ⟦ τ ⟧ (auth_ctx ∅))); [| |done].
  { iIntros (???) "Hτ". by iDestruct (eq_type_sound with "Hτ") as %->. }
  iIntros (?).
  iApply refines_instantiate.
  by iApply refines_typed.
Qed.

Theorem authentikit_eq_security_syntactic (c : expr) (σ : state) (τ : type _ ⋆) prf (l : list string) :
  EqType τ →
  ε |ₜ ∅ ⊢ₜ c : (∀: ⋆ ⇒ ⋆; ⋆ ⇒ ⋆, Authentikit_func_eq var1 var0 → var0 τ) →
  is_list l prf →
  adequate hash_collision NotStuck (v_run #~ (c #~ #~ v_Authentikit_eq) prf) σ
    (λ vᵥ σᵥ, ∃ thpᵢ σᵢ vᵢ o,
        vᵥ = $o ∧
        if o is Some wᵥ then
          (** a valid ideal execution *)
          rtc erased_step ([i_run #~ (c #~ #~ i_Authentikit_eq)], σ) (of_val vᵢ :: thpᵢ, σᵢ) ∧
          (** and they return the same value *)
          wᵥ = vᵢ
        else True).
Proof.
  intros Hτ Htyped Hprf.
  eapply (authentikit_security authΣ (λ a, ⟦ τ ⟧ (auth_ctx ∅))); [| |done].
  { iIntros (???) "Hτ". by iDestruct (eq_type_sound with "Hτ") as %->. }
  iIntros (?).
  iApply refines_instantiate_eq.
  by iApply refines_typed.
Qed.
