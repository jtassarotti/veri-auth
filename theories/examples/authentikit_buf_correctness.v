From auth.rel_logic_tern Require Export model spec_rules spec_tactics interp fundamental.
From auth.heap_lang Require Import primitive_laws derived_laws.
From auth.heap_lang.lib Require Import list set serialization.
From auth.examples Require Export authentikit_buf authentikit_base_alt_correctness.

(** * Correctness proof *)
Section proof.
  Context `{!authG Σ}.

  Definition is_proof_state (p : proph_id) (v1 v2 : val) (ps ps' : list string) : iProp Σ :=
    ∃ (prf1 cache1 prf2 cache2 : val) (m : gmap string string),
      ⌜v1 = (prf1, cache1)%V⌝ ∗ ⌜v2 = (prf2, cache2)%V⌝ ∗
      ⌜is_set (dom m) cache1⌝ ∗ ⌜is_map cache2 m⌝ ∗
      ⌜is_proof prf1 ps⌝ ∗ is_proph_proof prf2 p ps' ∗
      ([∗ map] h ↦ s ∈ m, ∃ (a : val) (t : evi_type),
          ⌜s_is_ser (evi_type_ser t) a s⌝ ∗ ⌜h = hash s⌝ ∗ hashed s).

  Definition lrel_auth_comp' (A : lrel Σ) : lrel Σ := LRel (λ v1 v2 v3,
    ∀ t2 K2 t3 K3 (p : proph_id) (ps ps' : list string) (w1 w2 : val),
      {{{ spec_verifier t2 (fill K2 (v2 w2)) ∗
          spec_ideal t3 (fill K3 (v3 #())) ∗
          is_proof_state p w1 w2 ps ps'
      }}}
        v1 #p w1
      {{{ ps1 ps2 (w1 w2 a1 a2 a3 : val), RET (w1, a1)%V;
          ⌜reverse ps ++ ps' = reverse ps1 ++ ps2⌝ ∗
          is_proof_state p w1 w2 ps1 ps2 ∗
          spec_verifier t2 (fill K2 (SOMEV (w2, a2)%V)) ∗
          spec_ideal t3 (fill K3 a3) ∗ A a1 a2 a3
      }}})%I.

  Program Definition lrel_auth_comp : kindO Σ (⋆ ⇒ ⋆)%kind := λne A, lrel_auth_comp' A.
  Next Obligation. intros ???????. rewrite /lrel_car/= /is_proof_state. solve_proper. Qed.

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
    iIntros (????????? Ψ) "!# (Hv & Hi & Hprf) HΨ".
    v_pures; i_pures; wp_pures.
    iModIntro.
    iApply "HΨ".
    iFrame "∗ #". done.
  Qed.

  Lemma refines_auth_bind Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆; ⋆, var2 var1 → (var1 → var2 var0) → var2 var0 ⟧
      (auth_ctx Δ) p_bind v_bind i_bind.
  Proof.
    iIntros (A ???) "!# _"; rewrite -/interp.
    iIntros (????) "Hv Hi".
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
    iIntros (????????? Ψ) "!# (Hv & Hi & Hprf) HΨ".
    wp_pures; v_pures; i_pures.

    wp_bind (v1 #p _); v_bind (v2 _); i_bind (v3 _).
    wp_apply ("HmA" with "[$Hv $Hi $Hprf]").
    iIntros (ps1 ps2 u1 u1' a1 a2 a3) "(%Heq1 & Hprf & Hv & Hi & #HA) /=".
    wp_pures. v_pures.

    wp_bind (w1 a1); v_bind (w2 a2); i_bind (w3 a3).
    iSpecialize ("HAmB" with "HA Hv Hi").
    wp_apply (wp_wand with "HAmB").
    iIntros (?) "(% & % & Hv & Hi & #HmB) /=".

    wp_apply ("HmB" with "[$Hv $Hi $Hprf]").
    iIntros (ps3 ps4 x1 x2 ???) "(%Heq2 & Hprf & Hv & Hi & #HB)".

    iApply "HΨ". iFrame "∗ #".
    rewrite Heq1 Heq2 //.
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
    iDestruct 1 as (tA ???? -> ->) "[#Hser [_ #Hdeser]]".
    iIntros (????) "Hv Hi".
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iIntros (???) "!# #Hauth /=".
    iIntros (????) "Hv Hi".
    v_pures; i_pures; wp_pures.
    iDestruct "Hauth" as (tA' a1 a2 s -> Hs ->) "(#Hs & #HA)".

    iModIntro. iFrame.
    iIntros (????????? Ψ) "!# (Hv & Hi & Hprf) HΨ".
    iDestruct "Hprf" as (prf1 c1 prf2 c2 m -> -> ???) "([% Hproph] & #Hhash)".
    wp_pures. v_pures. i_pures.
    wp_apply ("Hdeser" with "[$HA //]"). iIntros "#Hv_deser".
    wp_pures.
    wp_apply (gwp_set_mem (hash _) with "[//]"); [done|].
    iIntros ([] Hb).
    - apply elem_of_dom in Hb as [s' Hs'].

      v_bind (map_lookup _ _).
      iMod (gwp_map_lookup (K := string) _ _ _ () ⊤ _
                  (λ v, ⌜from_option (λ p, v = SOMEV $p) (v = NONEV) (m !! _)⌝)%I
                 with "[% //] [] [$Hv //]") as (x) "[Hv %Hx] /=".
      { by iIntros (?). }
      Unshelve. 2 : { done. }
      simplify_map_eq.
      wp_pures.
      v_pures.
      iDestruct (big_sepM_lookup with "Hhash") as (a t) "(%Ha & % & #Hs') "; [done|].

      destruct (decide (collision s s')) as [|Hnc%not_collision].
      { iExFalso. by iApply (hashes_auth.hashed_inj_or_coll with "Hs Hs'"). }
      destruct Hnc as [<- |?]; [|by simplify_eq].

      v_bind (v_deser _).
      pose proof (evi_type_ser_inj_val _ _ _ _ _ Hs Ha). subst.

      iMod ("Hv_deser" with "Hv") as "Hv /=".
      v_pures.

      iModIntro. iApply "HΨ".
      iFrame "# ∗". iSplit; [done|].
      iExists _, _, _,_.
      do 2 (iSplit; [done|]). iFrame "%".
    - rewrite /p_add_obj. wp_pures.
      wp_apply "Hser"; [done|].
      iIntros (s') "(%Hs' & #Hser')".
      wp_pures.

      wp_apply (wp_resolve_proph_string with "Hproph").
      iIntros (vs') "[-> Hproph]".

      wp_seq.
      wp_apply (gwp_list_cons s'); [done|].
      iIntros (??). wp_pures.
      wp_apply (gwp_set_add (hash s)); [done|done|].
      iIntros (c1' Hc1'). wp_pures.

      v_bind (map_lookup _ _).
      iMod (gwp_map_lookup (K := string) _ _ _ () ⊤ _
                  (λ v, ⌜from_option (λ p, v = SOMEV $p) (v = NONEV) (m !! _)⌝)%I
                 with "[% //] [] [$Hv //]") as (x) "[Hv %Hx] /=".
      { by iIntros (?). }
      Unshelve. 2 : { done. }
      apply not_elem_of_dom in Hb.
      simplify_map_eq.
      v_pures.

      v_bind (list_head _).
      iMod (gwp_list_head ⊤ _ (s' :: vs') () (λ v, ⌜v = SOMEV #s'⌝)%I
             with "[] [] [$Hv //]") as (?) "[Hv ->] /="; [done| |].
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
      iMod ("Hv_deser" with "Hv") as "Hv /=".
      v_pures.

      v_bind (map.map_insert _ _ _).
      iMod (gwp_map_insert (K := string) (V := string) _ _ _ _ () ⊤
                  _ (λ v, ⌜is_map v (<[hash s':=s']> m)⌝)%I
                 with "[//] [] [$Hv //]") as (x) "[Hv %] /=".
      { by iIntros (?). }
      Unshelve. 2 : { done. }

      v_bind (list_tail _).
      iMod (gwp_list_tail ⊤ _ (s' :: _) () (λ v, ⌜is_proof _ vs'⌝)%I
             with "[] [] [$Hv //]") as (u) "[Hv %Hprf'] /="; [done| |].
      { by iIntros "!>" (?). }
      v_pures.

      apply is_list_inject in Hprf' as ->.
      iModIntro. iApply ("HΨ" $! (s' :: ps) vs').
      rewrite reverse_cons -assoc /=.
      iSplit; [done|].
      iFrame "Hproph Hv Hi HA".
      iExists _, _, _, _, (<[hash s':=s']> m).
      iFrame "%".
      do 2 (iSplit; [done|]).
      iSplit; [iPureIntro|].
      { rewrite /is_set. destruct Hc1' as (?&?&?&?&?). set_solver. }
      iSplit; [iPureIntro|].
      { by apply is_list_inject. }
      iApply big_sepM_insert; [done|].
      by iFrame "Hhash Hs %".
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

  Lemma refines_authentikit Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ Authentikit ⟧ Δ p_Authentikit v_Authentikit i_Authentikit.
  Proof.
    iExists lrel_auth, lrel_auth_comp; rewrite -3!/interp.
    iApply refines_authentikit_func.
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

    v_bind (map.map_empty _).
    iMod (gwp_map_empty string string _ () ⊤ (λ v, ⌜is_map v (∅ : gmap string string)⌝)%I
           with "[% //] [] [$Hv //]") as (x) "[Hv %Hx] /=".
    { by iIntros "!#" (??). }
    v_pures.

    wp_apply (gwp_set_empty string with "[//]").
    iIntros (??).
    wp_pures.

    v_bind (f2 _).
    apply is_list_inject in Hprf as ->.
    iDestruct "Hproph" as (us) "[Hproph %Hps]".

    wp_apply ("Hc" $! _ _ _ _ _ [] ps with "[$Hproph $Hv $Hi]").
    { iExists _, _, _, _, ∅. do 5 (iSplit; [done|]).
      do 2 (iSplit; [|done]). iPureIntro. by apply is_list_inject. }
    iIntros (ps1 ps2 w1 w2 a1 a2 a3) "(%Heq & Hprf & Hv & Hi & HA) /=".
    iDestruct "Hprf" as (??????????) "((% & Hp) & ?)". simplify_eq.
    v_pures.
    wp_pures.
    wp_apply (wp_resolve_proph_nil with "Hp"); iIntros (->).
    wp_pures.
    iFrame.
    wp_apply gwp_list_rev.
    { done. }
    iIntros (? Hv).
    wp_pures.
    rewrite reverse_nil app_nil_r /= in Heq.
    rewrite Heq.
    apply is_list_inject in Hv as ->.
    by iFrame.
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
