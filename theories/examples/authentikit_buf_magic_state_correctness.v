From iris.base_logic.lib Require Import na_invariants.
From auth.rel_logic_tern Require Export model spec_rules spec_tactics interp fundamental.
From auth.heap_lang Require Import primitive_laws derived_laws.
From auth.heap_lang.lib Require Import linked_list table set serialization.
From auth.examples Require Export authentikit_base_correctness authentikit_buf_magic_state.

Class seqG (Σ: gFunctors) := {
  seqG_na_invG :: na_invG Σ;
  seqG_name: gname;
}.

Definition seq_inv `{!invGS_gen hlc Σ} `{!seqG Σ} (N : namespace) (P : iProp Σ) :=
  na_inv seqG_name N P.
Definition seq_tok `{!invGS_gen hlc Σ} `{!seqG Σ} (E : coPset) :=
  na_own seqG_name E.

(** We need [i_Authentikit] to be an expression since [p_Authenticable] and [v_Authenticable] need
    to initialize their caches and [x_unauth] specialized. *)
  Definition i_unauth : expr := Λ: λ: <> "a" <>, "a".
Definition i_Authenticable : expr :=
  (i_Auth_auth, i_Auth_mu, i_Auth_pair, i_Auth_sum, i_Auth_string, i_Auth_int, i_auth, i_unauth).
Definition i_Authentikit : expr := (i_return, i_bind, i_Authenticable).

(** * Correctness proof *)
Section proof.
  Context `{!authG Σ, !seqG Σ}.

  Definition is_cache (c1 c2 : val) : iProp Σ :=
    ∃ (l1 : loc) (v : val) (m : gmap string val),
      ⌜c1 = #l1⌝ ∗ l1 ↦ v ∗ ⌜is_set (dom m) v⌝ ∗ is_table (g := gwp_spec_verifier) c2 m ∗
      ([∗ map] h ↦ a ∈ m, ∃ (s : string) (t : evi_type),
          ⌜s_is_ser (evi_type_ser t) a s⌝ ∗ ⌜h = hash s⌝ ∗ hashed s).

  Definition Nauth := nroot .@ "authentikit".

  Definition inv_cache (v1 v2 : val) : iProp Σ := seq_inv Nauth (is_cache v1 v2).

  Definition lrel_auth_comp' (A : lrel Σ) : lrel Σ := LRel (λ v1 v2 v3,
    ∀ t2 K2 t3 K3 (p : proph_id) (ps ps' : list string) (w w' : val),
      {{{ spec_verifier t2 (fill K2 (v2 w')) ∗
          spec_ideal t3 (fill K3 (v3 #())) ∗
          ⌜is_proof w ps⌝ ∗ is_proph_proof w' p ps' ∗ seq_tok ⊤
      }}}
        v1 #p w
      {{{ ps1 ps2 (w1 w2 a1 a2 a3 : val), RET (w1, a1)%V;
          ⌜reverse ps ++ ps' = reverse ps1 ++ ps2⌝ ∗
          ⌜is_proof w1 ps1⌝ ∗ is_proph_proof w2 p ps2 ∗ seq_tok ⊤ ∗
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
    iIntros (????????? Ψ) "!# (Hv & Hi & Hprf & Hpprf & Htok) HΨ".
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
    iIntros (????????? Ψ) "!# (Hv & Hi & Hprf & Htok) HΨ".
    wp_pures; v_pures; i_pures.

    wp_bind (v1 #p _); v_bind (v2 _); i_bind (v3 _).
    wp_apply ("HmA" with "[$Hv $Hi $Hprf $Htok]").
    iIntros (ps1 ps2 u1 u1' a1 a2 a3) "(%Heq1 & Hprf & Hpprf & Htok & Hv & Hi & #HA) /=".
    wp_pures. v_pures.

    wp_bind (w1 a1); v_bind (w2 a2); i_bind (w3 a3).
    iSpecialize ("HAmB" with "HA Hv Hi").
    wp_apply (wp_wand with "HAmB").
    iIntros (?) "(% & % & Hv & Hi & #HmB) /=".

    wp_apply ("HmB" with "[$Hv $Hi $Hprf $Hpprf $Htok]").
    iIntros (ps3 ps4 x1 x2 ???) "(%Heq2 & Hprf & Hpprf & Htok & Hv & Hi & #HB)".

    iApply "HΨ". iFrame "∗ #".
    rewrite Heq1 Heq2 //.
  Qed.

  Lemma refines_auth_unauth Θ (Δ : ctxO Σ Θ) c1 c2 :
    inv_cache c1 c2
    ⊢ REL p_unauth c1 << v_unauth c2 << i_unauth :
      ⟦ ∀: ⋆, var1 var0 → var3 var0 → var2 var0 ⟧ (ext (auth_ctx Δ) lrel_evidence).
  Proof.
    iIntros "#Hc" (????) "Hv Hi".
    rewrite /p_unauth /v_unauth.
    v_pures. i_pures. wp_pures.
    iModIntro. iFrame. clear.
    iIntros (A ???) "!# _"; rewrite -/interp.
    iIntros (????) "Hv Hi".
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iIntros (???) "!#"; rewrite -!/interp.
    iDestruct 1 as (tA ??? -> ->) "#Hser".
    iIntros (????) "Hv Hi".
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iIntros (???) "!# #Hauth /=".
    iIntros (????) "Hv Hi".
    v_pures; i_pures; wp_pures.
    iDestruct "Hauth" as (tA' a1 a2 s -> Hs2 ->) "(#Hs & #HA)".

    iModIntro. iFrame.
    iIntros (????????? Ψ) "!# (Hv & Hi & %Hprf & [%Hprf' Hproph] & Htok) HΨ".
    wp_pures. v_pures. i_pures.
    iMod (na_inv_acc with "Hc Htok") as "(Hcache & Htok & Hclose)"; [done|done|].
    iDestruct "Hcache" as (???) ">(-> & Hc1 & % & Hc2 & Hm)".
    wp_load.

    v_bind (Table.lookup _ _).
    iMod (gwp_table_lookup _ _ _ () ⊤ _
            (λ v, ⌜v = $(m !! hash s)⌝ ∗ is_table c2 m)%I
           with "Hc2 [] [$Hv //]") as (?) "(Hv & -> & Hc2) /=".
    { by iIntros "!# $".  }
    Unshelve. 2 : { done. }

    wp_apply (gwp_set_mem (hash _) with "[//]"); [done|].
    iIntros ([] Hb).
    - apply elem_of_dom in Hb as [a Ha].
      simplify_map_eq.
      wp_pures. v_pures.

      iDestruct (big_sepM_lookup with "Hm") as (s' t Hs' ?) "#Hs'"; [done|].
      destruct (decide (collision s s')) as [|Hnc%not_collision].
      { iExFalso. by iApply (hashes_auth.hashed_inj_or_coll with "Hs Hs'"). }
      destruct Hnc as [<- |?]; [|by simplify_eq].

      rewrite -(evi_type_ser_inj_val _ _ _ _ _ Hs2 Hs').

      iMod ("Hclose" with "[$Hc1 $Hc2 $Hm $Htok //]").
      iModIntro. iApply "HΨ".
      by iFrame "# ∗".
    - rewrite /p_add_obj. wp_pures.
      wp_apply "Hser"; [done|].
      iIntros (s') "(%Hs' & #Hser' & #Hdeser)".
      wp_pures.

      wp_apply (wp_resolve_proph_string with "Hproph").
      iIntros (vs') "[-> Hproph]".

      wp_seq.
      wp_apply (gwp_list_cons s'); [done|].
      iIntros (??). wp_pures.

      wp_load.
      wp_apply (gwp_set_add (hash s)); [done|done|].
      iIntros (c1' Hc1').
      wp_store.
      wp_pures.

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

      pose proof (evi_type_ser_inj_str _ _ _ _ _ Hs2 Hs'). subst.
      iEval (rewrite bool_decide_eq_true_2 //) in "Hv".
      v_pures.
      v_bind (v_deser _).
      iMod ("Hdeser" with "[$Hv //]") as "Hv /=".
      v_pures.

      v_bind (Table.insert _ _ _).
      iMod (gwp_table_insert (K := string) (V := val) _ _ _ _ () ⊤
                  _ (λ _, is_table c2 (<[hash _:=a2]> m))%I
                 with "Hc2 [] [$Hv //]") as (x) "[Hv Hc2] /=".
      { by iIntros "!# $". }
      Unshelve. 2 : { done. }
      v_pures.

      v_bind (list_tail _).
      iMod (gwp_list_tail ⊤ _ (s' :: _) () (λ v, ⌜is_proof _ vs'⌝)%I
             with "[] [] [$Hv //]") as (u) "[Hv %] /="; [done| |].
      { by iIntros "!>" (?). }
      v_pures.

      iMod ("Hclose" with "[$Hc1 $Hc2 Hm $Htok]") as "Htok".
      { iModIntro. rewrite dom_insert_L. do 2 (iSplit; [done|]).
        iApply big_sepM_insert; [done|]. iFrame "Hm Hs". eauto. }
      iModIntro. iApply ("HΨ" $! (_ :: ps) vs').
      rewrite reverse_cons -assoc /=.
      iSplit; [done|].
      iFrame "Hproph Hv Hi HA Htok %".
  Qed.

  Lemma refines_Authenticatable Θ (Δ : ctxO Σ Θ) :
    ⊢ REL p_Authenticable << v_Authenticable << i_Authenticable : ⟦ Authenticatable ⟧ (auth_ctx Δ) .
  Proof.
    (* N.B. a [simpl] in the goal will make the [Qed.] spin for some God forsaken reason... *)
    iIntros (????) "Hv Hi".
    rewrite /p_Authenticable /v_Authenticable /i_Authenticable.

    v_bind (Table.empty _).
    iMod (gwp_table_empty (g := gwp_spec_verifier) (K := string) (V := val) () ⊤
                (λ d, is_table (K := string) (V := val) d ∅)%I
           with "[//] [] [$Hv //]") as (c2) "[Hv Hc2]".
    { by iIntros "!>" (?) "$". }
    iSimpl in "Hv".
    v_pures.
    wp_apply (gwp_set_empty string); [done|]. iIntros (??).
    wp_alloc c1 as "Hc1".
    wp_pures.
    iMod (na_inv_alloc seqG_name ⊤ Nauth (is_cache #c1 c2) with "[$Hc1 $Hc2]") as "#Hc".
    { iModIntro. auto. }

    i_bind (i_unauth). v_bind (v_unauth _). wp_bind (p_unauth _).
    wp_apply (wp_wand with "[Hi Hv]").
    { wp_apply (refines_auth_unauth _ Δ with "Hc Hv Hi"). }
    iIntros (?) "(% & % & Hv & Hi & #Hunauth)".
    iSimpl in "Hv Hi".
    v_pures. i_pures. wp_pures.
    iModIntro. iFrame "Hv Hi".
    iExists lrel_evidence; rewrite -/interp.
    iExists  _, _, _, _, _, _; rewrite -/interp.
    do 3 (iSplit; [done|]).
    iSplit; [|iApply "Hunauth"].
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
    ⊢ REL p_Authentikit << v_Authentikit << i_Authentikit : ⟦ Authentikit_func var1 var0 ⟧ (auth_ctx Δ).
  Proof.
    iIntros (????) "Hv Hi".
    rewrite /v_Authentikit /p_Authentikit /i_Authentikit.
    v_bind (v_Authenticable). i_bind (i_Authenticable). wp_bind (p_Authenticable).
    iPoseProof (refines_Authenticatable with "Hv Hi") as "Hwp".
    wp_apply (wp_wand with "Hwp").
    iIntros (?) "(% & % & Hv & Hi & Hauth)".
    iSimpl in "Hv Hi".
    v_pures. i_pures. wp_pures.
    iModIntro. iFrame "Hv Hi".
    iExists _, _, _, _, _, _; rewrite -!/interp.
    do 3 (iSplit; [done|]).
    iSplit; [|done].
    iExists _, _, _, _, _, _; rewrite -/interp.
    do 3 (iSplit; [done|]).
    iSplit; [iApply refines_auth_return|].
    iApply refines_auth_bind.
  Qed.

  Lemma refines_authentikit Θ (Δ : ctxO Σ Θ) :
    ⊢ REL p_Authentikit << v_Authentikit << i_Authentikit : ⟦ Authentikit ⟧ Δ.
  Proof.
    iIntros (????) "Hv Hi".
    iPoseProof (refines_authentikit_func with "Hv Hi") as "Hwp".
    wp_apply (wp_wand with "Hwp").
    iIntros (?) "(% & % & $ & $ & H)".
    by iExists lrel_auth, lrel_auth_comp.
  Qed.

  Definition rel_authentikit_output (A : lrel Σ) (prf : val) (ps : list string) : lrel Σ :=
    LRel (λ v1 v2 v3, ∃ a1 a2 a3, ⌜v1 = (prf, a1)%V⌝ ∗ ⌜v2 = SOMEV a2⌝ ∗ ⌜v3 = a3⌝ ∗ A a1 a2 a3)%I.

  Lemma refines_run Θ (Δ : ctxO Σ Θ) (p : proph_id) ps (c1 c2 c3 : expr) w A :
    seq_tok ⊤ -∗
    is_proph_proof w p ps -∗
    (REL c1 << c2 << c3 : lrel_auth_comp A) -∗
    REL p_run #~ #p c1 << v_run #~ c2 w << i_run #~ c3 : rel_authentikit_output A w ps.
  Proof.
    iIntros "Htok [%Hprf Hproph] Hc" (????) "Hv Hi".
    rewrite /v_run /i_run /p_run.
    v_bind c2; i_bind c3; wp_bind (c1).

    iSpecialize ("Hc" with "Hv Hi").
    wp_apply (wp_wand with "Hc").
    iIntros (f1) "(%f2 & %f3 & Hv & Hi & Hc) /=".
    wp_pures; v_pures; i_pures.

    v_bind (f2 _).
    apply is_list_inject in Hprf as ->.
    iDestruct "Hproph" as (us) "[Hproph %Hps]".

    wp_bind (f1 _ _).
    wp_apply ("Hc" $! _ _ _ _ _ [] ps with "[$Hproph $Hv $Hi $Htok]").
    { iFrame "%". iSplit; [done|]. iPureIntro. by apply is_list_inject. }
    iIntros (ps1 ps2 w1 w2 a1 a2 a3) "(%Heq & % & [% Hp] & Hv & Htok & Hi & HA) /=".
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
    v_bind (v_Authentikit). i_bind (i_Authentikit). wp_bind (p_Authentikit).
    iPoseProof (refines_authentikit_func with "Hv Hi") as "Hwp".
    wp_apply (wp_wand with "Hwp").
    iIntros (?) "(% & % & Hv & Hi & #Hauth)".
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
    iSpecialize ("Hcnt" with "[] Hv Hi"); rewrite -!/interp; [done|].
    wp_apply (wp_wand with "Hcnt").
    iIntros (v1''') "(%v2''' & %v3''' & Hv & Hi & Hcnt)".
    iFrame.
  Qed.

End proof.

Theorem authentikit_correctness Σ `{authPreG Σ, na_invG Σ}
  (A : ∀ `{authG Σ, seqG Σ}, lrel Σ) (φ : val → val → val → Prop) (cₚ cᵥ cᵢ : expr) (σ : state) (p : proph_id) :
  p ∈ σ.(used_proph_id) →
  (∀ `{authG Σ, seqG Σ}, ∀ vₚ vᵥ vᵢ, A vₚ vᵥ vᵢ -∗ ⌜φ vₚ vᵥ vᵢ⌝) →
  (∀ `{authG Σ, seqG Σ}, ⊢ REL cₚ << cᵥ << cᵢ : lrel_auth_comp A) →
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

  iMod na_alloc as (np) "Htok".
  set (Hseq := Build_seqG _ _ np).

  wp_apply wp_fupd.
  wp_apply (wp_wand with "[-]").
  { iPoseProof (refines_run (seqG0 := Hseq) _ ∅ with "Htok [$Hproph //] []")
      as "Hrun"; [iApply Hcomp|].
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

  set Σ := (#[authΣ; na_invΣ]).
  eapply (authentikit_correctness Σ (λ a _, ⟦ τ ⟧ (auth_ctx ∅))); [done| |].
  { iIntros (?????) "Hτ". by iDestruct (eq_type_sound with "Hτ") as %[]. }
  iIntros (??).
  iApply refines_instantiate.
  by iApply refines_typed.
Qed.
