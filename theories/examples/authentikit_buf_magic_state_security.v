From auth.prelude Require Import stdpp.
From iris.base_logic.lib Require Import na_invariants.
From auth.rel_logic_bin Require Export model spec_rules spec_tactics interp lib adequacy fundamental.
From auth.heap_lang.lib Require Import list table serialization.
From auth.examples Require Export authentikit_buf_magic_state authentikit_base_security.

Class seqG (Σ: gFunctors) := {
  seqG_na_invG :: na_invG Σ;
  seqG_name: gname;
}.

Definition seq_inv `{!invGS_gen hlc Σ} `{!seqG Σ} (N : namespace) (P : iProp Σ) :=
  na_inv seqG_name N P.
Definition seq_tok `{!invGS_gen hlc Σ} `{!seqG Σ} (E : coPset) :=
  na_own seqG_name E.

(** We need [i_Authentikit] to be an expression since [v_Authenticable] needs to initialize its
    cache and specialize [v_unauth]. *)
Definition i_Authenticable : expr :=
  (i_Auth_auth, i_Auth_mu, i_Auth_pair, i_Auth_sum, i_Auth_string, i_Auth_int, i_auth, i_unauth).
Definition i_Authentikit : expr := (i_return, i_bind, i_Authenticable).

(** * Proof *)
Section proof.
  Context `{!authG Σ, !seqG Σ}.

  Definition is_cache (v : val) : iProp Σ :=
    ∃ (m : gmap string val),
      is_table (g := gwp_upto_bad) v m ∗
      ([∗ map] h ↦ a ∈ m, ∃ (s : string) (t : evi_type),
          ⌜s_is_ser (evi_type_ser t) a s⌝ ∗ ⌜h = hash s⌝ ∗ hashed s).

  Definition Nauth := nroot .@ "authentikit".
  Definition inv_cache (v : val) := seq_inv Nauth (is_cache v).

  Definition lrel_auth_comp_post (A : lrel Σ) : lrel Σ :=
    LRel (λ v1 a2, ∃ a1 prf1, ⌜v1 = (prf1, a1)%V⌝ ∗ is_proof prf1 ∗ A a1 a2)%I.

  (** [lrel_auth_comp] has to be a bit more complicated than the non-stateful version because we
      need to thread through [seq_token]. Alternatively, [refines_Some] should thread it through.
      This is a minimum effort solution. *)
  Definition lrel_auth_comp' (A : lrel Σ) : lrel Σ := LRel (λ v1 v2,
    ∀ t K (w w' : val),
      {{{ spec_ideal t (fill K (v2 w')) ∗ seq_tok ⊤ ∗ is_proof w }}}
        v1 w
      {{{ (o1 : option val), RET $o1;
          seq_tok ⊤ ∗
          if o1 is Some w1 then
            ∃ (w2 : val), spec_ideal t (fill K w2) ∗ lrel_auth_comp_post A w1 w2
          else True }}})%I.

  Program Definition lrel_auth_comp : kindO Σ (⋆ ⇒ ⋆)%kind := λne A, lrel_auth_comp' A.
  Next Obligation.
    intros ??? ???. rewrite /lrel_car /=.
    do 22 f_equiv. solve_proper.
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
    interp_unfold!.
    iIntros (???? Ψ) "!# (Hi & Htok & %) HΨ".
    i_pures; wp_pures.
    iModIntro. iApply ("HΨ" $! (Some _)).
    iFrame "Hi Htok".
    iExists _, _.
    interp_unfold in "HA".
    by iFrame "HA".
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
    i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iIntros (w1 w2) "!# #HmB".
    iIntros (??) "Hi".
    i_pures; wp_pures.
    iModIntro. iFrame. clear.
    interp_unfold!.
    iIntros (u1 u2 ?? Ψ) "!# (Hi & Htok & Hprf) HΨ".
    i_pures; wp_pures.
    i_bind (v2 _)%I; wp_bind (v1 _)%I.
    interp_unfold in "HmA".
    wp_apply ("HmA" with "[$Hi $Htok $Hprf]").
    iIntros (o) "[Htok Ho]".
    destruct o; last first.
    { wp_pures. iApply ("HΨ" $! None). by iFrame. }
    iDestruct "Ho" as (?) "[Hi H]".
    iDestruct "H" as (a1 a2 ->) "[Hprf #HA]".
    wp_pures.
    wp_bind (w1 _)%E; i_bind (w2 _ )%E.
    interp_unfold in "HmB".
    iSpecialize ("HmB" with "HA Hi").
    wp_apply (wp_wand with "HmB").
    iIntros (v) "(% & Hi & H) /=".
    interp_unfold in "H".
    wp_apply ("H" with "[$Htok $Hi $Hprf]").
    iIntros (?) "(Htok & Ho) /=".
    iApply "HΨ". iFrame.
  Qed.

  Lemma refines_auth_unauth Θ (Δ : ctxO Σ Θ) c :
    inv_cache c
    ⊢ REL v_unauth c << i_unauth :
      ⟦ ∀: ⋆, var1 var0 → var3 var0 → var2 var0 ⟧ (ext (auth_ctx Δ) lrel_evidence) .
  Proof.
    iIntros "#Hc" (??) "Hi".
    rewrite /v_unauth /i_unauth.
    wp_pures.
    iFrame. iModIntro.
    iIntros (A v1 v2) "!# _".
    iIntros (??) "Hi".
    i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iIntros (??) "!# #Hevi".
    iIntros (??) "Hi".
    i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iIntros (w1 w2) "!# #Hauth /=".
    iIntros (??) "Hi".
    i_pures.
    interp_unfold in "Hevi Hauth".
    iDestruct "Hauth" as (a1 tA s1 Hs1 ->) "(#HA & #Hs1)".
    iDestruct "Hevi" as (tA' ?? ->) "[#Hser #Hdeser]".
    wp_pures. iFrame. iModIntro.
    interp_unfold!.
    iIntros (???? Ψ) "!# (Hi & Htok & Hprf) HΨ".
    i_pures; wp_pures.

    iMod (na_inv_acc with "Hc Htok") as "(>Hcache & Htok & Hclose)"; [done|done|].
    iDestruct "Hcache" as (?) "(Htable & #Hm)".
    wp_apply (gwp_table_lookup with "Htable"); [done|].
    iIntros "Htable".
    destruct (m !! hash s1) as [a|] eqn:Hlookup.
    - iDestruct (big_sepM_lookup with "Hm") as (s1' t' ??) "Hs1'"; [done|subst].
      wp_pures.

      destruct (decide (collision s1 s1')) as [|Hnc%not_collision].
      { iExFalso. by iApply (hashes_auth.hashed_inj_or_coll with "Hs1 Hs1'"). }
      destruct Hnc as [<- |?]; [|simplify_eq].
      assert (a1 = a) as <- by by eapply (evi_type_ser_inj tA t').

      iMod ("Hclose" with "[$Htok $Hm $Htable]") as "Htok".
      iModIntro. iApply ("HΨ" $! (Some _)). iFrame.
      iExists  _. by iFrame "HA".
    - wp_pures.
      iDestruct "Hprf" as (?) "%".
      wp_apply gwp_list_head; [done|].
      iIntros (vl [[-> ->] | (s1' &?& -> & -> )]).
      { wp_pures.
        iMod ("Hclose" with "[$Htok $Hm $Htable]") as "Htok".
        iModIntro. iApply ("HΨ" $! None). iFrame. }
      wp_pures.
      wp_apply (wp_hash with "[$]").
      iIntros "#Hs1'".
      wp_pures.

      case_bool_decide; simplify_eq; wp_pures; last first.
      { iMod ("Hclose" with "[$Htok $Hm $Htable]") as "Htok".
        iModIntro. iApply ("HΨ" $! None). iFrame. }

      wp_apply "Hdeser"; [done|].
      iIntros ([r|] Hs1'); wp_pures; last first.
      { iMod ("Hclose" with "[$Htok $Hm $Htable]") as "Htok".
        iModIntro. iApply ("HΨ" $! None). iFrame. }

      wp_apply (gwp_table_insert with "Htable"); [done|].
      iIntros "Htable".
      wp_pures.
      wp_apply (gwp_list_tail with "[//]").
      iIntros "/=" (tl Htl). wp_pures.

      destruct (decide (collision s1 s1')) as [|Hnc%not_collision].
      { iExFalso. by iApply (hashes_auth.hashed_inj_or_coll with "Hs1 Hs1'"). }
      destruct Hnc as [<- |?]; [|simplify_eq].
      assert (a1 = r) as <- by by eapply (evi_type_ser_inj tA tA').

      iMod ("Hclose" with "[$Htok Hm Htable]") as "Htok".
      { iModIntro. iFrame "Htable".
        iApply big_sepM_insert; [done|]. iFrame "# %". }
      iModIntro.
      iApply ("HΨ" $! (Some _)).
      iFrame.
      iExists _, _.
      by iFrame "HA %".
  Qed.

  Lemma refines_Authenticatable Θ (Δ : ctxO Σ Θ) :
    ⊢ REL v_Authenticable << i_Authenticable : ⟦ Authenticatable ⟧ (auth_ctx Δ).
  Proof.
    iIntros (??) "Hi".
    rewrite /i_Authenticable /v_Authenticable.
    wp_apply gwp_table_empty; [done|].
    iIntros (d) "Hd". wp_pures.
    iMod (na_inv_alloc seqG_name ⊤ Nauth (is_cache d) with "[$Hd]") as "#Hc".
    { iModIntro. done. }
    i_bind (i_unauth).
    iPoseProof (refines_auth_unauth with "Hc Hi") as "Hwp".
    wp_apply (wp_wand with "Hwp").
    iIntros (?) "(% & Hi & #Hauth)".
    iSimpl in "Hi".
    i_pures. wp_pures.
    iModIntro. iFrame.
    rewrite /Authenticatable.
    interp_unfold!.
    iExists lrel_evidence.
    interp_unfold.
    iExists  _, _, _, _.
    do 2 (iSplit; [done|]).
    iSplit; [|done].
    interp_unfold.
    iExists _, _, _, _.
    do 2 (iSplit; [done|]).
    iSplit; last first.
    { iApply refines_auth_auth. }
    interp_unfold.
    iExists _, _, _, _.
    do 2 (iSplit; [done|]).
    iSplit; last first.
    { interp_unfold!. iApply refines_Auth_int. }
    interp_unfold!.
    iExists _, _, _, _.
    do 2 (iSplit; [done|]).
    iSplit; last first.
    { interp_unfold!. iApply refines_Auth_string. }
    interp_unfold!.
    iExists _, _, _, _.
    do 2 (iSplit; [done|]).
    iSplit; last first.
    { iApply refines_Auth_sum. }
    interp_unfold!.
    iExists _, _, _, _.
    do 2 (iSplit; [done|]).
    iSplit; last first.
    { iApply refines_Auth_pair. }
    interp_unfold.
    iExists _, _, _, _.
    do 2 (iSplit; [done|]).
    iSplit; last first.
    { iApply refines_Auth_mu. }
    iApply refines_Auth_auth.
  Qed.

  Lemma refines_authentikit_func Θ (Δ : ctxO Σ Θ) :
    ⊢ REL v_Authentikit << i_Authentikit : ⟦ Authentikit_func var1 var0 ⟧ (auth_ctx Δ).
  Proof.
    iIntros (??) "Hi".
    rewrite /i_Authentikit /v_Authentikit.
    i_bind (i_Authenticable).
    iPoseProof (refines_Authenticatable with "Hi") as "H".
    wp_apply (wp_wand with "H").
    iIntros (?) "(% & Hv & #Hauth)".
    iSimpl in "Hv".
    i_pures. wp_pures.
    iModIntro. iFrame.
    rewrite interp_unseal -/interp.interp_def.
    iExists _, _, _, _; rewrite -!/interp.interp_def.
    do 2 (iSplit; [done|]).
    iSplit; [|done].
    iExists _, _, _, _; rewrite -!/interp.interp_def.
    do 2 (iSplit; [done|]).
    iSplit.
    { iPoseProof refines_auth_return as "H". rewrite interp_unseal //. }
    iPoseProof refines_auth_bind as "?".
    rewrite interp_unseal //.
  Qed.

  Lemma refines_authentikit Θ (Δ : ctxO Σ Θ) :
    ⊢ REL v_Authentikit << i_Authentikit : ⟦ Authentikit ⟧ Δ .
  Proof.
    iIntros (??) "Hi".
    iPoseProof (refines_authentikit_func with "Hi") as "H".
    wp_apply (wp_wand  with "H").
    iIntros (?) "(% & $ & #Hauth)".
    do 2 setoid_rewrite interp_exists_unfold.
    by iExists lrel_auth, lrel_auth_comp.
  Qed.

  Lemma refines_run w (c1 c2 : expr) A :
    seq_tok ⊤ -∗
    is_proof w -∗
    (REL c1 << c2 : lrel_auth_comp A) -∗
    refines_Some ⊤ (v_run #~ c1 w) (i_run #~ c2) A.
  Proof.
    iIntros "Htok #Hprf Hc" (??) "Hi".
    rewrite /v_run /i_run.
    wp_bind c1; i_bind c2.
    iSpecialize ("Hc" with "Hi").
    wp_apply (wp_wand with "Hc").
    iIntros (f1) "(%f2 & Hi & Hc) /=".
    wp_pures; i_pures.
    wp_apply ("Hc" with "[$Hi $Htok $Hprf]").
    iIntros (?) "(Htok & Ho)".
    destruct o1; last first.
    { wp_pures. by iExists None. }
    iDestruct "Ho" as (?) "[Hi H]".
    wp_pures.
    iDestruct "H" as (?? ->) "[% HA]".
    wp_pures. iModIntro. iExists (Some _). eauto.
  Qed.

  Lemma refines_instantiate (c1 c2 : expr) (τ : type _ ⋆) :
    (REL c1 << c2 : ⟦ ∀: ⋆ ⇒ ⋆; ⋆ ⇒ ⋆, Authentikit_func var1 var0 → var0 τ ⟧ ∅) -∗
    REL c1 #~ #~ v_Authentikit
     << c2 #~ #~ i_Authentikit : lrel_auth_comp (⟦ τ ⟧ (auth_ctx ∅)).
  Proof.
    iIntros "Hc" (??) "Hi".
    wp_bind v_Authentikit. i_bind i_Authentikit.
    iPoseProof (refines_authentikit_func with "Hi") as "H".
    wp_apply (wp_wand with "H").
    iIntros (?) "(% & Hi & #Hauth)".
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
    interp_unfold! in "Hcnt".
    iSpecialize ("Hcnt" with "[] Hi"); rewrite -!/interp; [done|].
    wp_apply (wp_wand with "Hcnt").
    iIntros (v1''') "(%v2'''& Hi & Hcnt)".
    iEval (rewrite interp_app_unfold) in "Hcnt".
    interp_unfold in "Hcnt".
    iFrame.
  Qed.

End proof.

Theorem authentikit_security Σ `{authPreG Σ, na_invG Σ} (A : ∀ `{authG Σ, seqG Σ}, lrel Σ)
  (φ : val → val → Prop) (cᵥ cᵢ : expr) (σ : state) (l : list string) (prf : val) :
  (∀ `{authG Σ, seqG Σ}, ∀ vᵥ vᵢ, A vᵥ vᵢ -∗ ⌜φ vᵥ vᵢ⌝) →
  (∀ `{authG Σ, seqG Σ}, ⊢ REL cᵥ << cᵢ : lrel_auth_comp A) →
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
  eapply (heap_adequacy_strong Σ).
  iIntros (Hinv) "_".
  iMod (cfg_alloc (i_run #~ cᵢ) σ) as (Hcfgᵢ) "[Hauthᵢ Heᵢ]".
  set (Hcfg := AuthG _ _ Hcfgᵢ).
  iMod (inv_alloc specN _ (spec_inv ([(i_run #~ cᵢ)], σ)) with "[Hauthᵢ]") as "#Hcfg".
  { iNext. iExists _, _. iFrame "# ∗ %". eauto. }
  iAssert (spec_ctx) as "#Hctx"; [by iExists _|].
  iMod na_alloc as (np) "Htok".
  set (Hseq := Build_seqG _ _ np).

  wp_apply wp_fupd.
  wp_apply (wp_wand with "[-]").
  { iPoseProof (refines_run (seqG0 := Hseq) prf with "Htok [] []") as "Hrun".
    - by iExists _.
    - iApply Hcomp.
    - wp_apply ("Hrun" $! empty_ectx with "[$Hctx $Heᵢ]"). }
  iIntros (v) "(%o & -> & Ho)".
  destruct o; last first.
  { iIntros "!#" (????) "_". by iExists inhabitant, inhabitant, inhabitant, None. }
  iDestruct "Ho" as "(%vᵢ & [_ Hi] & Hinterp) /=".

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
  set Σ := (#[authΣ; na_invΣ]).
  eapply (authentikit_security Σ (λ _ _, ⟦ τ ⟧ (auth_ctx ∅))); [| |done].
  { iIntros (????) "Hτ". by iDestruct (eq_type_sound with "Hτ") as %->. }
  iIntros (??).
  iApply refines_instantiate.
  by iApply refines_typed.
Qed.
