From auth.prelude Require Import stdpp.
From auth.rel_logic_tern_susp Require Export model spec_rules spec_tactics interp.
From auth.heap_lang Require Import primitive_laws derived_laws.
From auth.heap_lang.lib Require Import list map.
From auth.examples Require Export authentikit_susp.
From auth.examples.susp_correctness Require Import definitions helpers finish_specs unauth_step.
From auth.examples.susp_correctness Require Import base_correctness auth_pair auth_auth.
From iris.base_logic.lib Require Export na_invariants fancy_updates.

(** We need [i_Authentikit] to be an expression since [v_Authenticable] needs to initialize its
    cache and specialize [v_unauth]. *)
Definition i_Authenticable : expr :=
  (i_Auth_auth, i_Auth_mu, i_Auth_pair, i_Auth_sum, i_Auth_string, i_Auth_int, i_auth, i_unauth).
Definition i_Authentikit : expr := (i_return, i_bind, i_Authenticable).

(** The closure [v_unauth #c] reduces to; naming it lets [refines_auth_unauth]
    be stated as a value interpretation, so [refines_Authenticatable] can apply
    it after the verifier's cache allocation has been executed. *)
Definition v_unauth_cl (c : loc) : val :=
  (λ: <> "evi" "a" "proof",
     match: "a" with
       InjL <> => InjL #()
     | InjR "a" =>
       let: "counter" := "proof" in
       let: "pf_stream" := Fst "counter" in
       let: "counter" := Snd "counter" in
       match: list_head "pf_stream" with
         InjL <> => InjL #()
       | InjR "p" =>
         let: "id" := "counter" in
         let: "serialize" := "evi" in
         let: "deserialize" := Snd (Fst "serialize") in
         let: "count" := Snd "serialize" in
         let: "serialize" := Fst (Fst "serialize") in
         match: "deserialize" "id" "p" with
           InjL <> => InjL #()
         | InjR "x" =>
           let: "nchild" := "count" "x" in
           let: "finish" := v_finish #c "a" "x" "serialize" in
           match: if: "nchild" = #0 then "finish" #()
                  else #c <- map.map_insert "id" ("nchild", "finish") ! #c;;
                       InjRV #() with
             InjL <> => InjL #()
           | InjR <> => InjR (list_tail "pf_stream", "id" + #1, "x")
           end
         end
       end
     end)%V.

(** * Correctness proof *)
Section proof.
  Context `{!authG Σ, !seqG Σ, !tabseqG Σ, !correctnessG Σ}.

  Lemma refines_auth_return Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆, var0 → var1 var0 ⟧ (auth_ctx Δ) p_return v_return i_return.
  Proof.
    rewrite /p_return /v_return /i_return.
    iSplit; interp_unfold!; last first.
    { iIntros (A). iModIntro. iIntros (?) "_ Htok".
      wp_pures. iModIntro. iFrame "Htok".
      interp_unfold!.
      iModIntro. iIntros (a1) "#HAu Htok".
      wp_pures. iModIntro. iFrame "Htok".
      interp_unfold!.
      iIntros (p' ps ps1 ps_fix lpn w1 Ψ) "!# (Htok & Hpw & Hpr & %Hlast) HΨ".
      wp_pures.
      iModIntro. iApply "HΨ". by iFrame "∗ % #". }
    iIntros (A ???) "!# _"; rewrite -!/interp.
    iIntros (????) "Hv Hi Htok".
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iSplit; interp_unfold!; last first.
    { iModIntro. iIntros (a1') "#HAu Htok".
      wp_pures. iModIntro. iFrame "Htok".
      interp_unfold!.
      iIntros (p' ps ps1 ps_fix lpn w1 Ψ) "!# (Htok & Hpw & Hpr & %Hlast) HΨ".
      wp_pures.
      iModIntro. iApply "HΨ". by iFrame "∗ % #". }
    iIntros (a1 a2 a3) "!# #HA"; rewrite -!/interp.
    iIntros (????) "Hv Hi Htok".
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame.
    iSplit; interp_unfold!; last first.
    { iDestruct "HA" as "(_ & HAu)".
      iIntros (p' ps ps1 ps_fix lpn w1 Ψ) "!# (Htok & Hpw & Hpr & %Hlast) HΨ".
      wp_pures.
      iModIntro. iApply "HΨ". by iFrame "∗ % #". }
    iIntros (t2 K2 t3 K3 p' ps ps1 ps2 ps_fix lpn w1 w2 Ψ)
      "!# (Htabtok & Htok & Hv & Hi & Hpenc & Hpw & Hvw & Hpr & % & Hintr & Hst) HΨ".
    wp_pures; v_pures; i_pures.
    iModIntro. iApply "HΨ".
    iFrame "∗ #".
    iLeft. iExists ps2. iFrame "∗ #". done.
  Qed.

  Lemma refines_auth_bind Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆; ⋆, var2 var1 → (var1 → var2 var0) → var2 var0 ⟧
      (auth_ctx Δ) p_bind v_bind i_bind.
  Proof.
    rewrite /p_bind /v_bind /i_bind.
    iSplit; interp_unfold!; last first.
    { iIntros (A2). iModIntro. iIntros (?) "_ Htok".
      wp_pures. iModIntro. iFrame "Htok". interp_unfold!.
      iIntros (B2). iModIntro. iIntros (?) "_ Htok".
      wp_pures. iModIntro. iFrame "Htok". interp_unfold!.
      iModIntro. iIntros (v1u) "#HmAu Htok".
      wp_pures. iModIntro. iFrame "Htok". interp_unfold!.
      iModIntro. iIntros (w1u) "#HAmBu Htok".
      wp_pures. iModIntro. iFrame "Htok". interp_unfold!.
      interp_unfold! in "HmAu".
      iEval (unfold lrel_tern_un, lrel_auth_comp, lrel_auth_comp', lrel_auth_comp_un, lrel_un_car) in "HmAu".
      iIntros (pp ps ps1 ps_fix lpn u1 Ψ) "!# (Htok & Hpw & Hpr & %Hlast) HΨ".
      wp_pures.
      wp_bind (v1u _).
      wp_apply ("HmAu" with "[$Htok $Hpw $Hpr //]").
      iIntros (ps1x u1x a1) "(%Hlastx & Hpr & Htok & Hpw & #HAu) /=".
      wp_pures.
      interp_unfold! in "HAmBu".
      iEval (unfold lrel_tern_un, lrel_un_arr, lrel_un_car) in "HAmBu".
      wp_bind (w1u a1).
      iSpecialize ("HAmBu" $! a1 with "HAu").
      iSpecialize ("HAmBu" with "Htok").
      wp_apply (wp_wand with "HAmBu").
      iIntros (?) "(#HmBu & Htok) /=".
      iEval (rewrite interp_unseal /=) in "HmBu".
      iEval (unfold lrel_tern_un, lrel_auth_comp, lrel_auth_comp', lrel_auth_comp_un, lrel_un_car) in "HmBu".
      wp_apply ("HmBu" with "[$Htok $Hpw $Hpr //]").
      iIntros (ps1y u1y a1y) "(%Hlasty & Hpr & Htok & Hpw & #HBu)".
      iApply "HΨ". by iFrame "∗ % #". }
    iIntros (A ???) "!# _"; rewrite -!/interp.
    iIntros (????) "Hv Hi Htok".
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iSplit; interp_unfold!; last first.
    { iIntros (B2). iModIntro. iIntros (?) "_ Htok".
      wp_pures. iModIntro. iFrame "Htok". interp_unfold!.
      iModIntro. iIntros (v1u) "#HmAu Htok".
      wp_pures. iModIntro. iFrame "Htok". interp_unfold!.
      iModIntro. iIntros (w1u) "#HAmBu Htok".
      wp_pures. iModIntro. iFrame "Htok". interp_unfold!.
      interp_unfold! in "HmAu".
      iEval (unfold lrel_tern_un, lrel_auth_comp, lrel_auth_comp', lrel_auth_comp_un, lrel_un_car) in "HmAu".
      iIntros (pp ps ps1 ps_fix lpn u1 Ψ) "!# (Htok & Hpw & Hpr & %Hlast) HΨ".
      wp_pures.
      wp_bind (v1u _).
      wp_apply ("HmAu" with "[$Htok $Hpw $Hpr //]").
      iIntros (ps1x u1x a1) "(%Hlastx & Hpr & Htok & Hpw & #HAu) /=".
      wp_pures.
      interp_unfold! in "HAmBu".
      iEval (unfold lrel_tern_un, lrel_un_arr, lrel_un_car) in "HAmBu".
      wp_bind (w1u a1).
      iSpecialize ("HAmBu" $! a1 with "HAu").
      iSpecialize ("HAmBu" with "Htok").
      wp_apply (wp_wand with "HAmBu").
      iIntros (?) "(#HmBu & Htok) /=".
      iEval (rewrite interp_unseal /=) in "HmBu".
      iEval (unfold lrel_tern_un, lrel_auth_comp, lrel_auth_comp', lrel_auth_comp_un, lrel_un_car) in "HmBu".
      wp_apply ("HmBu" with "[$Htok $Hpw $Hpr //]").
      iIntros (ps1y u1y a1y) "(%Hlasty & Hpr & Htok & Hpw & #HBu)".
      iApply "HΨ". by iFrame "∗ % #". }
    iIntros (B ???) "!# _"; rewrite -!/interp.
    iIntros (????) "Hv Hi Htok".
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iSplit; interp_unfold!; last first.
    { iModIntro. iIntros (v1u) "#HmAu Htok".
      wp_pures. iModIntro. iFrame "Htok". interp_unfold!.
      iModIntro. iIntros (w1u) "#HAmBu Htok".
      wp_pures. iModIntro. iFrame "Htok". interp_unfold!.
      interp_unfold! in "HmAu".
      iEval (unfold lrel_tern_un, lrel_auth_comp, lrel_auth_comp', lrel_auth_comp_un, lrel_un_car) in "HmAu".
      iIntros (pp ps ps1 ps_fix lpn u1 Ψ) "!# (Htok & Hpw & Hpr & %Hlast) HΨ".
      wp_pures.
      wp_bind (v1u _).
      wp_apply ("HmAu" with "[$Htok $Hpw $Hpr //]").
      iIntros (ps1x u1x a1) "(%Hlastx & Hpr & Htok & Hpw & #HAu) /=".
      wp_pures.
      interp_unfold! in "HAmBu".
      iEval (unfold lrel_tern_un, lrel_un_arr, lrel_un_car) in "HAmBu".
      wp_bind (w1u a1).
      iSpecialize ("HAmBu" $! a1 with "HAu").
      iSpecialize ("HAmBu" with "Htok").
      wp_apply (wp_wand with "HAmBu").
      iIntros (?) "(#HmBu & Htok) /=".
      iEval (rewrite interp_unseal /=) in "HmBu".
      iEval (unfold lrel_tern_un, lrel_auth_comp, lrel_auth_comp', lrel_auth_comp_un, lrel_un_car) in "HmBu".
      wp_apply ("HmBu" with "[$Htok $Hpw $Hpr //]").
      iIntros (ps1y u1y a1y) "(%Hlasty & Hpr & Htok & Hpw & #HBu)".
      iApply "HΨ". by iFrame "∗ % #". }
    iIntros (v1 v2 v3) "!# #HmA"; rewrite -!/interp.
    iIntros (????) "Hv Hi Htok".
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iSplit; interp_unfold!; last first.
    { iModIntro. iIntros (w1u) "#HAmBu Htok".
      wp_pures. iModIntro. iFrame "Htok". interp_unfold!.
      iDestruct "HmA" as "(_ & HmAu)".
      interp_unfold! in "HmAu".
      iEval (unfold lrel_tern_un, lrel_auth_comp, lrel_auth_comp', lrel_auth_comp_un, lrel_un_car) in "HmAu".
      iIntros (pp ps ps1 ps_fix lpn u1 Ψ) "!# (Htok & Hpw & Hpr & %Hlast) HΨ".
      wp_pures.
      wp_bind (v1 _).
      wp_apply ("HmAu" with "[$Htok $Hpw $Hpr //]").
      iIntros (ps1x u1x a1) "(%Hlastx & Hpr & Htok & Hpw & #HAu) /=".
      wp_pures.
      interp_unfold! in "HAmBu".
      iEval (unfold lrel_tern_un, lrel_un_arr, lrel_un_car) in "HAmBu".
      wp_bind (w1u a1).
      iSpecialize ("HAmBu" $! a1 with "HAu").
      iSpecialize ("HAmBu" with "Htok").
      wp_apply (wp_wand with "HAmBu").
      iIntros (?) "(#HmBu & Htok) /=".
      iEval (rewrite interp_unseal /=) in "HmBu".
      iEval (unfold lrel_tern_un, lrel_auth_comp, lrel_auth_comp', lrel_auth_comp_un, lrel_un_car) in "HmBu".
      wp_apply ("HmBu" with "[$Htok $Hpw $Hpr //]").
      iIntros (ps1y u1y a1y) "(%Hlasty & Hpr & Htok & Hpw & #HBu)".
      iApply "HΨ". by iFrame "∗ % #". }
    iIntros (w1 w2 w3) "!# #HAmB"; rewrite -!/interp.
    iIntros (????) "Hv Hi Htok".
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iSplit; interp_unfold!; last first.
    { iDestruct "HmA" as "(_ & HmAu)".
      iDestruct "HAmB" as "(_ & HAmBu)".
      interp_unfold! in "HmAu".
      iEval (unfold lrel_tern_un, lrel_auth_comp, lrel_auth_comp', lrel_auth_comp_un, lrel_un_car) in "HmAu".
      iIntros (pp ps ps1 ps_fix lpn u1 Ψ) "!# (Htok & Hpw & Hpr & %Hlast) HΨ".
      wp_pures.
      wp_bind (v1 _).
      wp_apply ("HmAu" with "[$Htok $Hpw $Hpr //]").
      iIntros (ps1x u1x a1) "(%Hlastx & Hpr & Htok & Hpw & #HAu) /=".
      wp_pures.
      interp_unfold! in "HAmBu".
      iEval (unfold lrel_tern_un, lrel_un_arr, lrel_un_car) in "HAmBu".
      wp_bind (w1 a1).
      iSpecialize ("HAmBu" $! a1 with "HAu").
      iSpecialize ("HAmBu" with "Htok").
      wp_apply (wp_wand with "HAmBu").
      iIntros (?) "(#HmBu & Htok) /=".
      iEval (rewrite interp_unseal /=) in "HmBu".
      iEval (unfold lrel_tern_un, lrel_auth_comp, lrel_auth_comp', lrel_auth_comp_un, lrel_un_car) in "HmBu".
      wp_apply ("HmBu" with "[$Htok $Hpw $Hpr //]").
      iIntros (ps1y u1y a1y) "(%Hlasty & Hpr & Htok & Hpw & #HBu)".
      iApply "HΨ". by iFrame "∗ % #". }
    iIntros (t2 K2 t3 K3 pp ps ps1 ps2 ps_fix lpn u1 u2 Ψ)
      "!# (Htabtok & Htok & Hv & Hi & Hpenc & Hpw & Hvw & Hpr & %Hps & Hintr & Hst) HΨ".
    wp_pures; v_pures; i_pures.
    wp_bind (v1 _); v_bind (v2 _); i_bind (v3 _).
    iDestruct "HmA" as "(HmA & _)".
    interp_unfold! in "HmA".
    iEval (rewrite /lrel_auth_comp /lrel_auth_comp' /=) in "HmA".
    iEval (unfold lrel_tern_tern, lrel_auth_comp_tern, lrel_car) in "HmA".
    idtac "===APP===". Show.
    wp_apply ("HmA" with
      "[$Htabtok $Htok $Hv $Hi $Hpenc $Hpw $Hvw $Hpr $Hintr $Hst //]").
    iIntros (ps1x lpnx u1x a1 a3)
      "(Htabtok & Htok & Hi & Hintr & Hpr & Hpw & Hres) /=".
    iDestruct "Hres" as
      "[(%ps2x &%u2x &%a2 & Hpenc & %Hpsx & #HA & Hv & Hvw & Hst)| Hbad]".
    - wp_pures. v_pures.
      iDestruct "HAmB" as "(HAmB2 & _)".
      interp_unfold! in "HAmB2".
      iEval (unfold lrel_tern_tern, lrel_arr, lrel_arr', lrel_car) in "HAmB2".
      wp_bind (w1 a1); v_bind (w2 a2); i_bind (w3 a3).
      iSpecialize ("HAmB2" $! a1 a2 a3 with "HA Hv Hi Htok").
      wp_apply (wp_wand with "HAmB2").
      iIntros (?) "(% & % & Hv & Hi & #HmB & Htok) /=".
      iDestruct "HmB" as "(HmB2 & _)".
      interp_unfold! in "HmB2".
      iEval (unfold lrel_tern_tern, lrel_auth_comp, lrel_auth_comp', lrel_auth_comp_tern, lrel_car) in "HmB2".
      wp_apply ("HmB2" with
        "[$Htabtok $Htok $Hv $Hi $Hpenc $Hpw $Hvw $Hpr $Hintr $Hst //]").
      iIntros (ps1y lpny u1y a1y a3y)
        "(Htabtok & Htok & Hi & Hintr & Hpr & Hpw & Hres)".
      iApply "HΨ". iFrame "∗ #".
    - (* the first computation went bad: the prover must still run (f a1)
         alongside the ideal, which needs the removed binary (prover-ideal)
         fragment of the relation — same gap as the "step prover using binary
         suspend" admits in refines_auth_unauth. *)
      admit.
  Admitted.

  (* Lemma refines_auth_return Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆, var0 → var1 var0 ⟧ (auth_ctx Δ) p_return v_return i_return.
  Proof.
    iSplit; [|iSplit].
    { iIntros (A ???) "!# _"; rewrite -/interp.
      iIntros (????) "Hv Hi Htok".
      rewrite /p_return /v_return /i_return.
      wp_pures; v_pures; i_pures.
      iModIntro. iFrame.
      iSplit; [|iSplit].
      { iIntros (a1 a2 a3) "!# #HA"; rewrite -!/interp /=.
        iIntros (????) "Hv Hi Htok".
        wp_pures; v_pures; i_pures.
        iModIntro. iFrame. clear.
        iSplit; [|iSplit].
        { iIntros (?????????? Ψ) "!# (Htok & Hv & Hi & Hpw & Hvw & Hpr & %) HΨ".
          wp_pures; v_pures; i_pures.
          iModIntro. iApply "HΨ".
          iFrame "∗ #".
          iLeft. iFrame. done. }
        { iIntros (?????? Ψ) "!# (Htok & Hi & Hpw & Hpr & [%%]) HΨ".
          wp_pures; i_pures.
          iPoseProof (lc_zero) as ">Hlc".
          iModIntro. iApply "HΨ".
          iFrame "∗ #". iDestruct "HA" as "(_ & $ & _)". done. }
        { iIntros (??? Ψ) "!# (Htok & Hv & Hvw)".
          v_pures. iFrame.
          iModIntro. iLeft. iFrame. 
          iDestruct "HA" as "(_ & _ & $)". } } 
      { iIntros (a1 a3) "!# #HA"; rewrite -!/interp /=.
        iIntros (??) "[Hi Htok]".
        wp_pures; i_pures.
        iModIntro. iFrame. clear.
        iIntros (?????? Ψ) "!# (Htok & Hi & Hpw & Hpr & [%%]) HΨ".
        wp_pures; i_pures.
        iPoseProof (lc_zero) as ">Hlc".
        iModIntro. iApply "HΨ".
        iFrame "∗ #". done. }
      { iIntros (a2) "!# #HA"; rewrite -!/interp /=.
        iIntros (??) "Hv Htok".
        v_pures. iModIntro. iFrame. clear.
        iIntros (??? Ψ) "!# (Htok & Hv & Hvw)".
        v_pures. iFrame.
        iModIntro. iLeft. iFrame "∗ #". } }
    { iIntros (A ??) "!# _"; rewrite -!/interp /=.
      iIntros (??) "[Hi Htok]".
      rewrite /p_return /i_return.
      wp_pures; i_pures.
      iModIntro. iFrame. clear.
      iIntros (a1 a3) "!# #HA"; rewrite -!/interp /=.
      iIntros (??) "[Hi Htok]".
      wp_pures; i_pures.
      iModIntro. iFrame. clear.
      iIntros (?????? Ψ) "!# (Htok & Hi & Hpw & Hpr & [%%]) HΨ".
      wp_pures; i_pures.
      iPoseProof (lc_zero) as ">Hlc".
      iModIntro. iApply "HΨ". iFrame "∗ #". done. }
    { iIntros (A ?) "!# _"; rewrite -!/interp /=.
      iIntros (??) "Hv Htok".
      rewrite /v_return. v_pures.
      iModIntro. iFrame. clear.
      iIntros (a2) "!# #HA"; rewrite -!/interp /=.
      iIntros (??) "Hv Htok".
      v_pures. iModIntro. iFrame. clear.
      iIntros (??? Ψ) "!# (Htok & Hv & Hvw)".
      v_pures. iFrame.
      iModIntro. iLeft. iFrame "∗ #". }
  Qed.

  Lemma refines_auth_bind Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆; ⋆, var2 var1 → (var1 → var2 var0) → var2 var0 ⟧
      (auth_ctx Δ) p_bind v_bind i_bind.
  Proof.
    iSplit; [|iSplit].
    { iIntros (A ???) "!# _"; rewrite -/interp.
      iIntros (????) "Hv Hi Htok".
      rewrite /p_bind/v_bind/i_bind.
      wp_pures; v_pures; i_pures.
      iModIntro. iFrame. clear.
      iSplit; [|iSplit].
      { iIntros (B ???) "!# _"; rewrite -/interp.
        iIntros (????) "Hv Hi Htok".
        wp_pures; v_pures; i_pures.
        iModIntro. iFrame. clear.
        iSplit; [|iSplit].
        { iIntros (v1 v2 v3) "!# #HmA"; rewrite -!/interp.
          iIntros (????) "Hv Hi Htok /=".
          wp_pures; v_pures; i_pures.
          iModIntro. iFrame. clear.
          iSplit; [|iSplit].
          { iIntros (w1 w2 w3) "!# #HAmB".
            iIntros (????) "Hv Hi Htok".
            wp_pures; v_pures; i_pures.
            iModIntro. iFrame. clear.
            iSplit; [|iSplit].
            { iIntros (?????????? Ψ) "!# (Htok & Hv & Hi & Hpw & Hvw & Hpr & %) HΨ".
              wp_pures; v_pures; i_pures.
              
              wp_bind (v1 _); v_bind (v2 _); i_bind (v3 _).
              iDestruct "HmA" as "(HmA & _)".
              wp_apply ("HmA" with "[$Htok $Hv $Hi $Hpw $Hvw $Hpr //]").
              iIntros (ps1' w1' a1 a3) "(Htok & Hi & Hpr & Hv) /=".
              iDestruct "Hv" as 
                "[(%&%&%&% &% &#HA & Hpw & Hv & Hvw)|
                  (#HAb & Hpw)]".
              { wp_pures. v_pures. 
                iDestruct "HAmB" as "(HAmB & _)".
                wp_bind (w1 a1); v_bind (w2 a2); i_bind (w3 a3).
                iSpecialize ("HAmB" with "HA Hv Hi Htok").
                wp_apply (wp_wand with "HAmB").
                iIntros (?) "(% & % & Hv & Hi & #HmB & Htok) /=".
                
                iDestruct "HmB" as "(HmB & _)".
                wp_apply ("HmB" with "[$Htok $Hv $Hi $Hpw $Hvw $Hpr]"); first done.
                iIntros (ps1'' w1'' a1' a3') "(Htok & Hi & Hpr & Hv)".
                iDestruct "Hv" as 
                "[(%&%&%&% &% &#HB & Hpw & Hv & Hvw)|
                  (#HAb & Hpw)]".
                { iApply "HΨ". iFrame "∗ #".
                  iLeft. iFrame. done. }
                { iApply "HΨ". iFrame "∗ #". } }

              { iDestruct "HAmB" as "(_ & HAmBb & HAmBu)".
                wp_pures. wp_bind (w1 a1); i_bind (w3 a3).
                iSpecialize ("HAmBb" with "HAb [$Hi $Htok]").
                wp_apply (wp_wand with "HAmBb").
                iIntros (?) "(% & Hi & #HmBb & Htok) /=".

                wp_apply ("HmBb" with "[$Htok $Hi $Hpw $Hpr]"); first done.
                iIntros (ps1'' ? w1'' a1' a3') "(Hpr & %& Htok & Hpw & Hi & #HBb) /=".
                iApply "HΨ". iFrame.
                iRight. iFrame "∗ #". } }
              
            { iIntros (?????? Ψ) "!# (Htok & Hi & Hpw & Hpr & [%%]) HΨ".
              wp_pures; i_pures.
              
              wp_bind (v1 _); i_bind (v3 _).
              iDestruct "HmA" as "(_ & HmA & _)".
              wp_apply ("HmA" with "[$Htok $Hi $Hpw $Hpr]"); eauto.
              iIntros (? ? w1' a1 a3) "(Hpr & %& Htok & Hpw & Hi & #HA) /=".
              wp_pures.

              iDestruct "HAmB" as "(_ & HAmBb & _)".
              wp_bind (w1 a1); i_bind (w3 a3).
              iSpecialize ("HAmBb" with "HA [$Hi $Htok]").
              wp_apply (wp_wand with "HAmBb").
              iIntros (?) "(% & Hi & #HmBb & Htok) /=".

              wp_apply ("HmBb" with "[$Htok $Hi $Hpw $Hpr]"); eauto. }
            { iIntros (??? Ψ) "!# (Htok & Hv & Hvw)".
              v_pures.
              
              v_bind (v2 _).
              iDestruct "HmA" as "(_ & _ & HmA)".
              iMod ("HmA" with "[$Htok $Hv $Hvw]") as "(Htok & Hv) /=".

              iDestruct "Hv" as "[(%&%&%& Hvw & Hv & #HA)|Hv]"; v_pures.
              { iDestruct "HAmB" as "(_ & _ & HAmB)".
                v_bind (w2 a2).
                iMod ("HAmB" with "HA Hv Htok") as (?) "(Hv & #HmB & Htok) /=".
                
                iMod ("HmB" with "[$Htok $Hv $Hvw]") as "($ & Hv)".
                
                iDestruct "Hv" as "[(%&%&%& Hvw & Hv & #HAu')|Hv]".
                { iLeft. by iFrame. }
                { by iRight. } }
              { by iFrame. } } }
          
          { iIntros (w1 w3) "!# #HAmB".
            iIntros (??) "[Hi Htok]".
            wp_pures; i_pures.
            iModIntro. iFrame. clear.

            iIntros (?????? Ψ) "!# (Htok & Hi & Hpw & Hpr & [%%]) HΨ".
            wp_pures; i_pures.
            
            wp_bind (v1 _); i_bind (v3 _).
            iDestruct "HmA" as "(_ & HmA & _)".
            wp_apply ("HmA" with "[$Htok $Hi $Hpw $Hpr]"); eauto.
            iIntros (? ? w1' a1 a3) "(Hpr &% & Htok & Hpw & Hi & HA) /=".
            wp_pures.

            wp_bind (w1 a1); i_bind (w3 a3).
            iSpecialize ("HAmB" with "HA [$Hi $Htok]").
            wp_apply (wp_wand with "HAmB").
            iIntros (?) "(% & Hi & #HmBb & Htok) /=".

            wp_apply ("HmBb" with "[$Htok $Hi $Hpw $Hpr]"); eauto. }

          { iIntros (w2) "!# #HAmb".
            iIntros (??) "Hv Htok".
            v_pures. iModIntro. iFrame. clear.
            
            iIntros (??? Ψ) "!# (Htok & Hv & Hvw)".
            v_pures.
            
            v_bind (v2 _).
            iDestruct "HmA" as "(_ & _ & HmA)".
            iMod ("HmA" with "[$Htok $Hv $Hvw]") as "(Htok & Hv) /=".

            iDestruct "Hv" as "[(%&%&%& Hvw & Hv & #HA)|Hv]"; v_pures.
            { v_bind (w2 a2).
              iMod ("HAmb" with "HA Hv Htok") as (?) "(Hv & #HmB & Htok) /=".
              
              iMod ("HmB" with "[$Htok $Hv $Hvw]") as "($ & Hv)".
              
              iDestruct "Hv" as "[(%&%&%& Hvw & Hv & #HAu')|Hv]".
              { iLeft. by iFrame. }
              { by iRight. } }
            { by iFrame. } } }
       
        { iIntros (v1 v3) "!# #HmA"; rewrite -!/interp.
          iIntros (??) "[Hi Htok] /=".
          wp_pures; i_pures.
          iModIntro. iFrame. clear.
          
          iIntros (w1 w3) "!# #HAmB".
          iIntros (??) "[Hi Htok]".
          wp_pures; i_pures.
          iModIntro. iFrame. clear.

          iIntros (?????? Ψ) "!# (Htok & Hi & Hpw & Hpr & [%%]) HΨ".
          wp_pures; i_pures.
          
          wp_bind (v1 _); i_bind (v3 _).
          wp_apply ("HmA" with "[$Htok $Hi $Hpw $Hpr]"); eauto.
          iIntros (? ? w1' a1 a3) "(Hpr &% & Htok & Hpw & Hi & HA) /=".
          wp_pures.

          wp_bind (w1 a1); i_bind (w3 a3).
          iSpecialize ("HAmB" with "HA [$Hi $Htok]").
          wp_apply (wp_wand with "HAmB").
          iIntros (?) "(% & Hi & #HmBb & Htok) /=".

          wp_apply ("HmBb" with "[$Htok $Hi $Hpw $Hpr]"); eauto. }

        { iIntros (v2) "!# #HmA"; rewrite -!/interp.
          iIntros (??) "Hv Htok /=".
          v_pures. iModIntro. iFrame. clear.

          iIntros (w2) "!# #HAmb".
          iIntros (??) "Hv Htok".
          v_pures. iModIntro. iFrame. clear.
          
          iIntros (??? Ψ) "!# (Htok & Hv & Hvw)".
          v_pures.
          
          v_bind (v2 _).
          iMod ("HmA" with "[$Htok $Hv $Hvw]") as "(Htok & Hv) /=".

          iDestruct "Hv" as "[(%&%&%& Hvw & Hv & #HA)|Hv]"; v_pures.
          { v_bind (w2 a2).
            iMod ("HAmb" with "HA Hv Htok") as (?) "(Hv & #HmB & Htok) /=".
            
            iMod ("HmB" with "[$Htok $Hv $Hvw]") as "($ & Hv)".
            
            iDestruct "Hv" as "[(%&%&%& Hvw & Hv & #HAu')|Hv]".
            { iLeft. by iFrame. }
            { by iRight. } }
          { by iFrame. } } }
      
      { iIntros (B ??) "!# _"; rewrite -/interp.
        iIntros (??) "[Hi Htok]".
        wp_pures; i_pures.
        iModIntro. iFrame. clear.
        
        iIntros (v1 v3) "!# #HmA"; rewrite -!/interp.
        iIntros (??) "[Hi Htok] /=".
        wp_pures; i_pures.
        iModIntro. iFrame. clear.
        
        iIntros (w1 w3) "!# #HAmB".
        iIntros (??) "[Hi Htok]".
        wp_pures; i_pures.
        iModIntro. iFrame. clear.

        iIntros (?????? Ψ) "!# (Htok & Hi & Hpw & Hpr & [%%]) HΨ".
        wp_pures; i_pures.
        
        wp_bind (v1 _); i_bind (v3 _).
        wp_apply ("HmA" with "[$Htok $Hi $Hpw $Hpr]"); eauto.
        iIntros (? ? w1' a1 a3) "(Hpr &% & Htok & Hpw & Hi & HA) /=".
        wp_pures.

        wp_bind (w1 a1); i_bind (w3 a3).
        iSpecialize ("HAmB" with "HA [$Hi $Htok]").
        wp_apply (wp_wand with "HAmB").
        iIntros (?) "(% & Hi & #HmBb & Htok) /=".

        wp_apply ("HmBb" with "[$Htok $Hi $Hpw $Hpr]"); eauto. }

      { iIntros (B ?) "!# _"; rewrite -/interp.
        iIntros (??) "Hv Htok".
        v_pures. iModIntro. iFrame. clear.
        
        iIntros (v2) "!# #HmA"; rewrite -!/interp.
        iIntros (??) "Hv Htok /=".
        v_pures. iModIntro. iFrame. clear.

        iIntros (w2) "!# #HAmb".
        iIntros (??) "Hv Htok".
        v_pures. iModIntro. iFrame. clear.
        
        iIntros (??? Ψ) "!# (Htok & Hv & Hvw)".
        v_pures.
        
        v_bind (v2 _).
        iMod ("HmA" with "[$Htok $Hv $Hvw]") as "(Htok & Hv) /=".

        iDestruct "Hv" as "[(%&%&%& Hvw & Hv & #HA)|Hv]"; v_pures.
        { v_bind (w2 a2).
          iMod ("HAmb" with "HA Hv Htok") as (?) "(Hv & #HmB & Htok) /=".
          
          iMod ("HmB" with "[$Htok $Hv $Hvw]") as "($ & Hv)".
          
          iDestruct "Hv" as "[(%&%&%& Hvw & Hv & #HAu')|Hv]".
          { iLeft. by iFrame. }
          { by iRight. } }
        { by iFrame. } } }
    
    { iIntros (A ??) "!# _"; rewrite -/interp.
      iIntros (??) "[Hi Htok]".
      rewrite /p_bind/i_bind.
      wp_pures; i_pures.
      iModIntro. iFrame. clear.
      
      iIntros (B ??) "!# _"; rewrite -/interp.
      iIntros (??) "[Hi Htok]".
      wp_pures; i_pures.
      iModIntro. iFrame. clear.
      
      iIntros (v1 v3) "!# #HmA"; rewrite -!/interp.
      iIntros (??) "[Hi Htok] /=".
      wp_pures; i_pures.
      iModIntro. iFrame. clear.
      
      iIntros (w1 w3) "!# #HAmB".
      iIntros (??) "[Hi Htok]".
      wp_pures; i_pures.
      iModIntro. iFrame. clear.

      iIntros (?????? Ψ) "!# (Htok & Hi & Hpw & Hpr & [%%]) HΨ".
      wp_pures; i_pures.
      
      wp_bind (v1 _); i_bind (v3 _).
      wp_apply ("HmA" with "[$Htok $Hi $Hpw $Hpr]"); eauto.
      iIntros (? ? w1' a1 a3) "(Hpr &% & Htok & Hpw & Hi & HA) /=".
      wp_pures.

      wp_bind (w1 a1); i_bind (w3 a3).
      iSpecialize ("HAmB" with "HA [$Hi $Htok]").
      wp_apply (wp_wand with "HAmB").
      iIntros (?) "(% & Hi & #HmBb & Htok) /=".

      wp_apply ("HmBb" with "[$Htok $Hi $Hpw $Hpr]"); eauto. }

    { iIntros (A ?) "!# _"; rewrite -/interp.
      iIntros (??) "Hv Htok".
      rewrite /v_bind. v_pures.
      iModIntro. iFrame. clear.
      
      iIntros (B ?) "!# _"; rewrite -/interp.
      iIntros (??) "Hv Htok".
      v_pures. iModIntro. iFrame. clear.
      
      iIntros (v2) "!# #HmA"; rewrite -!/interp.
      iIntros (??) "Hv Htok /=".
      v_pures. iModIntro. iFrame. clear.

      iIntros (w2) "!# #HAmb".
      iIntros (??) "Hv Htok".
      v_pures. iModIntro. iFrame. clear.
      
      iIntros (??? Ψ) "!# (Htok & Hv & Hvw)".
      v_pures.
      
      v_bind (v2 _).
      iMod ("HmA" with "[$Htok $Hv $Hvw]") as "(Htok & Hv) /=".

      iDestruct "Hv" as "[(%&%&%& Hvw & Hv & #HA)|Hv]"; v_pures.
      { v_bind (w2 a2).
        iMod ("HAmb" with "HA Hv Htok") as (?) "(Hv & #HmB & Htok) /=".
        
        iMod ("HmB" with "[$Htok $Hv $Hvw]") as "($ & Hv)".
        
        iDestruct "Hv" as "[(%&%&%& Hvw & Hv & #HAu')|Hv]".
        { iLeft. by iFrame. }
        { by iRight. } }
      { by iFrame. } }
  Admitted. *)

  Lemma refines_auth_unauth Θ (Δ : ctxO Σ Θ) c :
    inv_v_susp_table c
    ⊢ ⟦ ∀: ⋆, var1 var0 → var3 var0 → var2 var0 ⟧
      (ext (auth_ctx Δ) lrel_evidence) p_unauth (v_unauth_cl c) i_unauth.
  Proof.
    iIntros "#Htab".
    rewrite /p_unauth /i_unauth /v_unauth_cl.
    iSplit; interp_unfold!; last first.
    { (* unary  *) admit. }
    iIntros (????) "!# _"; rewrite -!/interp.
    iIntros (????) "Hv Hi Htok".
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iSplit; interp_unfold!; last first.
    { (* unary  *) admit. }
    iIntros (???) "!#"; rewrite -!/interp.
    interp_unfold!.
    iDestruct 1 as "(#Hevi & #Hevi_un)".
    iDestruct "Hevi" as (tA ???? ??? -> ->) "#(Hpunserspec & Hpserspec & Hpsuspspec & Hpunsuspspec & Hvserspec & _ & Hvcountspec)".
    iIntros (????) "Hv Hi Htok".
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iSplit; interp_unfold!; last first.
    { (* unary  *) admit. }
    iIntros (???) "!# #Hauth".
    iIntros (????) "Hv Hi Htok".
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iSplit; interp_unfold!; last first.
    { (* unary  *) admit. }
    iIntros (???????????? Ψ)
        "!# (Htabtok & Htok & Hv & Hi & Hpenc & Hpw & Hvw & Hpr & % & Hintr & Hst) HΨ".
    interp_unfold! in "Hauth".
    iDestruct "Hauth" as "(Hauth & _)".
    iDestruct "Hauth" as (tA' ? a1 a2 un_a1 s [-> ?]) "(Hpserp & #HA & Hpvauth)".
    iDestruct "Hpw" as (????) "(% & % & -> & -> & Hbuf & % & %)".
    iDestruct "Hvw" as (??) "([-> %Hvprf] & Hid)".
    iDestruct "Hpvauth" as (??? ->) "Hvinv".
    v_pures; i_pures; wp_pures.
    iDestruct "Hvinv" as "[[-> Hinv_fill]|(%&%&%&%& -> & #Hlbpfrag & Hinv_unfill & #Hpvuneq & #Hlbvfrag & -> & Hinv_authv)]".
    - iMod (na_inv_acc with "Hinv_fill Htok") as "(>Hinvo & Htok & Hclose_inv)"; try solve_ndisj.
      iDestruct "Hinvo" as "[Hlb [(% & Hlr & (Hbrproph & %))|
          [(% & Hlr & Hbrproph)|[(Hlr & Hbrproph)|(%&%&%& Hlr & Hbrproph & Hintr')]]]]";
          wp_load.
    
      + wp_pures.
        wp_apply (wp_resolve_proph_bool with "Hbrproph").
        iIntros (?) "[% Hbrproph]". 
        simplify_eq. by destruct! H5.
    
      + iMod ("Hclose_inv" with "[$Htok $Hlb Hlr Hbrproph]") as "Htok".
        { iNext. iRight. iLeft. iFrame. }
      
        destruct ps2; simplify_eq; v_bind (list_head _).
        { iMod (gwp_list_head ⊤ _ [] () (λ v, ⌜v = NONEV⌝)%I
              with "[] [] [$Hv //]") as (?) "[Hv ->] /="; [done| |v_pures].
          { iIntros "!>" (? [[] | (?&?&?&?)]); simplify_eq. eauto. }

          (* step prover using binary suspend *)
          admit. }

        wp_pure credit:"Hlc"; wp_pure credit:"Hlctab"; wp_pures.

        iMod (gwp_list_head ⊤ _ (s0 :: ps2) () (λ v, ⌜v = SOMEV #s0⌝)%I
              with "[] [] [$Hv //]") as (?) "[Hv ->] /="; [done| |v_pures].
        { iIntros "!>" (? [[] | (?&?&?&?)]); simplify_eq. eauto. }

        iMod (na_inv_acc with "Htab Htabtok") as "(Htabo & Htabtok & Hclose_tab)"; try solve_ndisj.
        iMod (lc_fupd_elim_later with "Hlctab Htabo") as "Htabo".
        iDestruct "Htabo" as "[(%&%&%&%& %idctr &%&%msp_ & Hl & %Hm &
            Hbigsep &% & Hvmauth & %Hidinv & Hvisinv & Hst' & Hserp & %Hmspdom) | Hst']";
          last first.
        { by iPoseProof (tern_state_un_state_excl with "Hst Hst'") as "?". }
          (* iPoseProof (state_agree with "Hst Hst'") as "(% & Hst & Hst')"; simplify_eq. *)
        iDestruct (pn_agree with "Hvmauth Hpenc") as "->".
        iDestruct (id_ctr_frag_agree with "Hvmauth Hid") as "->".
        iMod (serpred_alloc msp_ cntr s with "Hserp") as "[Hserp #Hserpfrag]".
        { apply not_elem_of_dom. intro Hin.
          apply Hmspdom, elem_of_set_seq in Hin. lia. }

        v_bind (v_deser _).
        iMod ("Hpsuspspec" with "Hv") as (?) "(Hv & Hpsuspdeserspec) /=".

        v_bind (v_deser_par _).
        wp_apply ("Hpsuspdeserspec" with "[$HA $Hpserp $Hserpfrag $Hvmauth $Hpenc $Hv]").
        { admit. (* ⌜unsusp⌝ + lg_p_auth (Group C: prover-side lg auth has no
                    external owner yet) *) }
        iIntros (a1' s_real c' t_real) "(#Hpserspecat & #Hpreal & _ &
              [([% %] & #Hun1' & %&%&%& Hlmauth & % & Hpens & Hpserp' & Hv &
                  Hsubsep & Hpenc & Hvmauth & Hdecorate)|
              [% #HA']])"; wp_pures; last first.
        { wp_bind (p_finish _ _).

          iApply (p_finish_spec' p_ser_susp a1' s_real c' with "[//]").
          iNext. iIntros (p_finish) "Hpfinish". wp_pures.
          simplify_eq.

          iMod (state_update_bad with "Hst Hst'") as "#Hst".

          iPoseProof (big_sepL_cons (λ _, p_buffer_elem) (p_finish, s_real, c') 
              (combine (combine bufl ps1) lpn) with "[$Hbuf $Hpserspecat $Hpfinish]") as 
            "Hbuf".
          { iFrame "∗". iSplit; eauto.
            iIntros "Hst'".
            by iPoseProof (tern_state_un_state_excl with "Hst' Hst") as "?". }

          iMod ("Hclose_tab" with "[$Htabtok]") as "Htabtok".
          { iNext. by iRight. }

          wp_apply (gwp_list_cons _); [done|].
          iIntros (??). wp_pures.
          
          iApply ("HΨ"). iFrame "Htabtok Htok Hi Hintr Hpr".

          iModIntro.
          assert (
            ((p_finish, s_real, c') :: combine (combine bufl ps1) lpn) =
              combine (combine (p_finish :: bufl) (s_real :: ps1)) (c' :: lpn))
            as -> by eauto.
          iSplitL "Hbuf".
          { iFrame "∗ %".
            iPureIntro. exists (definitions.sum_list (c' :: lpn)).
            simpl. split_and!; try done; lia. }

          do 2 iRight. iFrame "#".
          iPureIntro.
          unfold lastn.
          rewrite reverse_cons -assoc /=.
          rewrite !length_app length_reverse /=.
          replace (length ps2 + S (length ps1) - S (length ps1)) with (length ps2) by lia.
          rewrite skipn_app skipn_all2; last (rewrite length_reverse; lia).
          replace (length ps2 - length (reverse ps2)) with 0 by (rewrite length_reverse; lia).
          simpl. intros [=Hne%H5]. done. }

        iPoseProof (big_sepS_sep
          (λ γ, ∃ lb, lg_mapg_p_frag lb γ ∗ ⌜p_sub_obj tA a1' #lb⌝)%I
          (λ γ, ∃ susp, lg_mapg_frag susp γ ∗ ⌜v_sub_obj tA a2' #susp⌝)%I
        with "Hsubsep") as "[Hpsubsep Hvsubsep]".

        wp_bind (p_finish _ _).

        iApply (p_finish_spec' p_ser_susp a1' s_real); try done.
        iNext. iIntros (p_finish) "Hpfinish". wp_pures.

        wp_apply (gwp_list_cons _); [done|].
        iIntros (??). wp_pures.

        iPoseProof (big_sepL_cons (λ _, p_buffer_elem) 
            with "[$Hbuf $Hpfinish $Hpserspecat Hpens Hpsubsep]")
          as "Hbuf".
        { iSplit; eauto. simplify_eq.
          iIntros "Hst". by iFrame. }

        iEval (rewrite visited_map_update_pending_rewrite) in "Hvmauth".
        iMod (visited_deser_commit _ _ _ _ _ a2' c' with "Hvmauth Hid")
          as "(Hvmauth & Hid & Hidtok & Hpvfrag & #Hcapf & Hmapf)".
        iMod ("Hdecorate" $! tA a2' s c' with "[] [//] Hcapf [Hmapf] []")
            as "(#HA' & Hc & Hvser)".
          { iPureIntro. apply sub_pos_refl. }
        { destruct c'; [done|]. rewrite Qp.div_diag. iFrame "Hmapf". }
        { by destruct c'. }

        (* iPoseProof (big_sepM_mono
            (vm_big_sep_lam_unset m)
            (vm_big_sep_lam_set m cntr)
          with "Hvisinv") as "Hvisinv".
        { iIntros (k x0' Hkx0) "Hvis".
          iIntros (id_inner Heq ->).
          iApply "Hvis"; try done. } *)

        iSimpl in "Hv". v_pures. v_bind (v_count _).
        iPoseProof "Hcapf" as "Hcap".
        iAssert (count_aggregator c' cntr c' a2')%I as "Hagg".
        { rewrite /count_aggregator. by iLeft. }
        iMod ("Hvcountspec" with "Hc Hv") as "[Hc Hv] /=". v_pures.

        v_bind (v_finish _ _ _ _).
        iMod (v_finish_spec with "Htab Hv") as (v_finish) "[Hvfinish Hv] /=".
        v_pures; try solve_vals_compare_safe.

        case_bool_decide; simplify_eq; v_pures.
        * v_bind (v_finish _).
          assert (size γl = 0) as Hγl0 by lia.
          iEval (rewrite Hγl0 /=) in "Hvmauth".
          rewrite Hγl0.

          iMod ("Hclose_tab" with "[$Htabtok Hl Hbigsep Hvmauth Hvisinv Hst' Hserp]") as "Htabtok".
          { iNext. iLeft. iFrame "Hvmauth". iFrame "∗ %".
            iSplit. { iPureIntro; intros ??; apply Hidinv; lia. }

            apply size_empty_inv in Hγl0. fold_leibniz. rewrite Hγl0.
            rewrite set_fold_empty. iFrame.
            iPureIntro. rewrite dom_insert set_seq_S_end_union_L.
            set_solver. }

          iMod ("Hvfinish" $! ⊤ with "[] Htabtok Hlc Hvser Hvserspec Hc [Htok Hidtok Hintr Hpvfrag]
                Hst Hv") as "(Hv & Htabtok & Htok & Hst & Hintr) /=".
          { iModIntro. iIntros (???) "_ _ _ _". set_solver. }
          { iLeft. by iFrame. }
          
          v_pures. v_bind (list_tail _).
          iMod (gwp_list_tail ⊤ _ (s_real :: _) () (λ v, ⌜is_proof _ ps2⌝)%I
                with "[] [] [$Hv //]") as (u) "[Hv %Hvprf'] /="; [done| |v_pures].
          { by iIntros "!>" (?). }

          iApply ("HΨ"). iFrame "Htabtok Htok Hpr Hi Hintr".
          iModIntro. iSplitL "Hbuf".
          { iPoseProof (big_sepL_cons (λ _, p_buffer_elem) with "Hbuf") as "Hbuf".
            assert
              (((p_finish, s_real, 0) :: combine (combine bufl ps1) lpn) =
                combine (combine (p_finish :: bufl) (s_real :: ps1)) (0 :: lpn))
              as -> by done.
            iFrame "Hbuf".
            iPureIntro. exists prf1, v, (definitions.sum_list (0 :: lpn)).
            simpl. split_and!; try done; lia. }
          iLeft. iExists ps2. simpl.
          iFrame "HA' Hv Hid Hpenc Hst".
          iSplit.
          { iPureIntro. by rewrite reverse_cons -assoc. }

          iPureIntro.
          eexists _. split; eauto.
          repeat f_equal. lia.

        * assert (size γl > 0).
          { destruct (size γl); simplify_eq. lia. }
          assert (∃ n', size γl = S n') as [n' Hszpos].
          { destruct (size γl); [lia|eauto]. }
          iEval (rewrite Hszpos /=) in "Hvmauth".

          iAssert (sub_susp_count_frags tA a2' (size γl) cntr (size γl) a2')%I
            with "[$Hcap $Hc $Hagg //]" as "Hc".
        
          v_load. v_pures. v_bind (map.map_insert _ _ _).
          iMod (gwp_map_insert #cntr _ _ _ () ⊤ _
            (λ d, ⌜is_map d (<[ #cntr := _ ]> m)⌝)%I
            with "[//] [] [$Hv //]") as (?) "[Hv %Hmins] /=".
          { by iIntros "!#" (? Hins). }
          (* Unshelve. 2: done. *)
          
          v_store.

          iDestruct (v_susp_big_sep_fresh with "Hbigsep") as %Hcntr_fresh;
            first exact Hidinv.
          iMod ("Hclose_tab" with "[$Htabtok Hl Hbigsep Hvmauth Hvisinv Hst' Hc Hlc Hvfinish Hvser Hidtok Hserp]") as "Htabtok".
          { iNext. iLeft. iFrame "Hvmauth". iFrame "∗ %".

            iPoseProof (big_sepM_mono
                (v_susp_big_sep_lam m)
                (v_susp_big_sep_lam (<[#cntr:=(#(size γl), v_finish)%V]> m))
              with "Hbigsep") as "Hbigsep".
            { iIntros (?? Hlook) "Hbigsep".
              rewrite /v_susp_big_sep_lam.
              iDestruct "Hbigsep" as (?????????[?[??]]) "($ & $ & $ & $)".
              iPureIntro. exists q.
              do 2 (split; eauto).
              rewrite lookup_insert_ne; eauto.
              intros ?. simplify_eq.
              specialize (Hidinv k ltac:(lia)).
              simplify_eq. }

            iSplitR "Hvisinv".
            { rewrite /v_susp_big_sep /mapg_insert_def mapg_alive_insert.
              iApply (big_sepM_insert_2 with "[Hvfinish Hc Hlc Hvser Hidtok]").
              { iFrame "∗ #". iExists 1%Qp.
                iSplit. iPureIntro. split; try lia.
                by rewrite lookup_insert.
                iLeft. by iFrame. }
              iFrame. }

            iSplit.
            { iPureIntro.
              rewrite /mapg_insert_def mapg_alive_insert.
              rewrite (map_size_insert_None _ _ _ Hcntr_fresh).
              pose proof (Hidinv cntr ltac:(lia)) as Hm_none.
              rewrite (map_size_insert_None _ _ _ Hm_none).
              by rewrite H. }
            iSplit.
            { iPureIntro. intros ??.
              rewrite lookup_insert_None.
              specialize (Hidinv ctr' ltac:(lia)).
              split; eauto. intros ?. simplify_eq. lia. }

            iSplit; last first.
            { iPureIntro. rewrite dom_insert set_seq_S_end_union_L.
              set_solver. }
            iApply (vm_big_sep_transport with "Hvisinv"); done. }

          v_pures. v_bind (list_tail _).
          iMod (gwp_list_tail ⊤ _ (s_real :: _) () (λ v, ⌜is_proof _ ps2⌝)%I
                with "[] [] [$Hv //]") as (u) "[Hv %Hprf'] /="; [done| |].
          { by iIntros "!>" (?). }
          v_pures.

          iApply "HΨ". iFrame "Htok Htabtok Hintr Hi Hpr".
          iModIntro. iSplitL "Hbuf".
          { iPoseProof (big_sepL_cons (λ _, p_buffer_elem) with "Hbuf") as "Hbuf". 
            assert 
              (((p_finish, s_real, size γl) :: combine (combine bufl ps1) lpn) = 
                combine (combine (p_finish :: bufl) (s_real :: ps1)) (size γl :: lpn))
              as -> by done.
            iFrame "Hbuf".
            iPureIntro. exists prf1, v, (definitions.sum_list (size γl :: lpn)).
            simpl. split_and!; try done; lia. }

          iLeft. iExists ps2. iFrame "HA' Hv Hid Hst Hpenc".
          simpl. iSplit. { iPureIntro. by rewrite reverse_cons -assoc. }
          
          iPureIntro.
          eexists _. split; eauto.
          repeat f_equal. lia.

      + wp_pures.
        wp_apply (wp_resolve_proph_bool with "Hbrproph").
        iIntros (?) "[% Hbrproph]". 
        simplify_eq.

      + by iPoseProof (intransit_excl_full with "Hintr Hintr'") as "?".

    - iMod (na_inv_acc with "Hinv_unfill Htok") as "(>Hinvo & Htok & Hclose_inv)"; try solve_ndisj.
      iDestruct "Hinvo" as "[(%& Hlb & Hlr & Hbrproph)|
              (%&%&%&%& Hlb & Hlr & Hbrproph & #Hlbpfrag' & #Hgetvisit)]";
        wp_load; last first.
      + iDestruct ("Hgetvisit" with "Hst") as "[Hst #Hvisit]".
        iDestruct (lg_mapg_p_agree with "Hlbpfrag Hlbpfrag'") as "(% & _ & _)".
        destruct r;
          [do 3 wp_pure| wp_pures; wp_apply (wp_resolve_proph_bool with "Hbrproph"); iIntros (?) "[% Hbrproph]"; simplify_eq; wp_pures; wp_store].
        
        * iMod ("Hclose_inv" with "[$Htok Hlb Hlr Hbrproph]") as "Htok".
          { iNext. iRight. iFrame "∗ #". eauto. }
        
          destruct ps2; simplify_eq.
          { v_bind (list_head _).
            iMod (gwp_list_head ⊤ _ [] () (λ v, ⌜v = NONEV⌝)%I
                  with "[] [] [$Hv //]") as (?) "[Hv ->] /="; [done| |v_pures].
            { iIntros "!>" (? [[] | (?&?&?&?)]); simplify_eq. eauto. }

            (* step prover using binary suspend *)
            admit. }

          iApply (refines_unauth_susp_consume with
              "Htab Hpsuspspec Hvserspec Hvcountspec Hpserp HA Hpvuneq Hlbvfrag
               Hinv_authv Hvisit
               [$Htabtok $Hv $Hi $Hpenc $Hbuf $Hid $Hpr $Hintr $Hst $Htok]
               HΨ"); eauto.

        * iMod ("Hclose_inv" with "[$Htok Hlb Hlr Hbrproph]") as "Htok".
          { iNext. iRight. iFrame "∗ #". eauto. }
        
          destruct ps2; simplify_eq.
          { v_bind (list_head _).
            iMod (gwp_list_head ⊤ _ [] () (λ v, ⌜v = NONEV⌝)%I
                  with "[] [] [$Hv //]") as (?) "[Hv ->] /="; [done| |v_pures].
            { iIntros "!>" (? [[] | (?&?&?&?)]); simplify_eq. eauto. }

            (* step prover using binary suspend *)
            admit. }

          iApply (refines_unauth_susp_consume with
              "Htab Hpsuspspec Hvserspec Hvcountspec Hpserp HA Hpvuneq Hlbvfrag
               Hinv_authv Hvisit
               [$Htabtok $Hv $Hi $Hpenc $Hbuf $Hid $Hpr $Hintr $Hst $Htok]
               HΨ"); eauto.

      + iDestruct "Hbrproph" as "(Hbrproph & %&%)".
        wp_pures; wp_apply (wp_resolve_proph_bool with "Hbrproph").
        iIntros (?) "[% Hbrproph]"; simplify_eq; wp_pures; wp_store.

        destruct ps2; simplify_eq; v_bind (list_head _).
        { iMod (gwp_list_head ⊤ _ [] () (λ v, ⌜v = NONEV⌝)%I
              with "[] [] [$Hv //]") as (?) "[Hv ->] /="; [done| |v_pures].
          { iIntros "!>" (? [[] | (?&?&?&?)]); simplify_eq. eauto. }

          (* step prover using binary suspend *)
          admit. }

        wp_pure credit:"Hlc"; wp_pure credit:"Hlctab"; wp_pures.

        iMod (gwp_list_head ⊤ _ (s0 :: ps2) () (λ v, ⌜v = SOMEV #s0⌝)%I
              with "[] [] [$Hv //]") as (?) "[Hv ->] /="; [done| |v_pures].
        { iIntros "!>" (? [[] | (?&?&?&?)]); simplify_eq. eauto. }

        iMod (na_inv_acc with "Htab Htabtok") as "(Htabo & Htabtok & Hclose_tab)"; try solve_ndisj.
        iMod (lc_fupd_elim_later with "Hlctab Htabo") as "Htabo".
        iDestruct "Htabo" as "[(%&%&%m2 &%& %idctr &%&%msp_2 & Hl & %Hm &
            Hbigsep &% & Hvmauth & %Hidinv & Hvisinv & Hst' & Hserp2 & %Hmspdom2) | Hst']";
          last first.
        { by iPoseProof (tern_state_un_state_excl with "Hst Hst'") as "?". }

        iDestruct (id_ctr_frag_agree with "Hvmauth Hid") as "->".
        iMod (serpred_alloc msp_2 cntr s with "Hserp2") as "[Hserp2 #Hserpfrag]".
        { apply not_elem_of_dom. intro Hin. apply Hmspdom2 in Hin.
          apply elem_of_set_seq in Hin. lia. }

        iDestruct (pn_agree with "Hvmauth Hpenc") as "->".

        v_bind (v_deser _).
        iMod ("Hpsuspspec" with "Hv") as (?) "(Hv & Hpsuspdeserspec) /=".

        v_bind (v_deser_par _).
        wp_apply ("Hpsuspdeserspec" with "[$HA $Hpserp $Hserpfrag $Hvmauth $Hpenc $Hv]").
        { admit. (* ⌜unsusp⌝ + lg_p_auth (Group C: prover-side lg auth has no
                    external owner yet) *) }
        iIntros (a1' s_real c' t_real) "(#Hpserspecat & #Hpreal & _ &
            [([% %] & #Hun1' & %&%&%& Hlmauth & % & Hpens & Hpserp' & Hv &
                Hsubsep & Hpenc & Hvmauth & Hdecorate)|
            [% #HA']])"; wp_pures; last first.
        { wp_bind (p_finish _ _).

          iApply (p_finish_spec' p_ser_susp a1' s_real c' with "[//]").
          iNext. iIntros (p_finish) "Hpfinish". wp_pures.
          simplify_eq.

          iMod (state_update_bad with "Hst Hst'") as "#Hst".

          iPoseProof (big_sepL_cons (λ _, p_buffer_elem) (p_finish, s_real, c') 
              (combine (combine bufl ps1) lpn) with "[$Hbuf $Hpserspecat $Hpfinish]") as 
            "Hbuf".
          { iFrame "∗". iSplit; eauto.
            iIntros "Hst'".
            by iPoseProof (tern_state_un_state_excl with "Hst' Hst") as "?". }

          iMod ("Hclose_tab" with "[$Htabtok]") as "Htabtok".
          { iNext. by iRight. }

          iMod ("Hclose_inv" with "[$Htok Hlb Hlr Hbrproph]") as "Htok".
          { iNext. iRight. iFrame "∗ #". iExists _. iModIntro.
            iIntros "Hst'".
            by iPoseProof (tern_state_un_state_excl with "Hst' Hst") as "?". }

          wp_apply (gwp_list_cons _); [done|].
          iIntros (??). wp_pures.
          
          iApply ("HΨ"). iFrame "Htabtok Htok Hi Hintr Hpr".

          iModIntro. 
          assert (
            ((p_finish, s_real, c') :: combine (combine bufl ps1) lpn) =
              combine (combine (p_finish :: bufl) (s_real :: ps1)) (c' :: lpn))
            as -> by eauto.
          iSplitL "Hbuf".
          { iFrame "∗ %".
            iPureIntro. exists (definitions.sum_list (c' :: lpn)).
            simpl. split_and!; try done; lia. }

          do 2 iRight. iFrame "#".
          iPureIntro.
          unfold lastn.
          rewrite reverse_cons -assoc /=.
          rewrite !length_app length_reverse /=.
          replace (length ps2 + S (length ps1) - S (length ps1)) with (length ps2) by lia.
          rewrite skipn_app skipn_all2; last (rewrite length_reverse; lia).
          replace (length ps2 - length (reverse ps2)) with 0 by (rewrite length_reverse; lia).
          simpl. intros [=Hne%H5]. done. }

        iPoseProof (big_sepS_sep
          (λ γ, ∃ lb, lg_mapg_p_frag lb γ ∗ ⌜p_sub_obj tA a1' #lb⌝)%I
          (λ γ, ∃ susp, lg_mapg_frag susp γ ∗ ⌜v_sub_obj tA a2' #susp⌝)%I
        with "Hsubsep") as "[Hpsubsep Hvsubsep]".

        wp_bind (p_finish _ _).

        iApply (p_finish_spec' p_ser_susp a1' s_real); try done.
        iNext. iIntros (p_finish) "Hpfinish". wp_pures.

        wp_apply (gwp_list_cons _); [done|].
        iIntros (??). wp_pures.

        iPoseProof (big_sepL_cons (λ _, p_buffer_elem) 
            with "[$Hbuf $Hpfinish $Hpserspecat Hpens Hpsubsep]")
          as "Hbuf".
        { iSplit; eauto. simplify_eq.
          iIntros "Hst". by iFrame. }

        iEval (rewrite visited_map_update_pending_rewrite) in "Hvmauth".
        iMod (visited_deser_commit _ _ _ _ susp a2' c' with "Hvmauth Hid")
          as "(Hvmauth & Hid & Hidtok & #Hvfrag & #Hcapf & Hmapf)".
        iMod ("Hdecorate" $! tA a2' s c' with "[] [//] Hcapf [Hmapf] []")
          as "(#HA' & Hc & Hvser)".
        { iPureIntro. apply sub_pos_refl. }
        { destruct c'; [done|]. rewrite Qp.div_diag. iFrame "Hmapf". }
        { by destruct c'. }

        iSimpl in "Hv". v_pures. v_bind (v_count _).
        iAssert (count_aggregator c' cntr c' a2')%I as "Hagg".
        { rewrite /count_aggregator. by iLeft. }
        iMod ("Hvcountspec" with "Hc Hv") as "[Hc Hv] /=". v_pures.

        v_bind (v_finish _ _ _ _).
        iMod (v_finish_spec with "Htab Hv") as (v_finish) "[Hvfinish Hv] /=".
        v_pures; try solve_vals_compare_safe.

        set (vm' := set_fold (λ (γ : gname) (m0 : state_mapg_type), <[γ:=pending_val]> m0) vm γl).
        set (pn' := definitions.sum_list lpn + size γl).
        set (cntr' := S cntr).
        set (mp2 := match c' with
                    | 0%nat => m2
                    | _ => mapg_insert_def m2 cntr a2'
                    end) in *.
        simplify_eq.
        assert (pn' = size γl + definitions.sum_list lpn) as <- by lia.

        iAssert (|==> ∃ m'', mapg_auth m'' ∗
            ⌜(size γl > 0 ∧ m'' = mapg_insert_def m2 cntr a2'
              ∨ size γl = 0 ∧ m'' = m2)⌝)%I
          with "[]" as "Hmint";
          last iMod "Hmint" as (m'') "[Hmauth %]".
        { admit. }

        iAssert (
          |={⊤}=>
            seq_tok ⊤ ∗ intransit 1 ∗
            auth_v cntr (InjRV #susp) s ∗
            visited_map_update_done vm' mp2 γ pn' cntr' ∗
            sub_susp_count tA a2' (size γl) cntr (size γl) a2' ∗
            mapg_auth m'' ∗ v_susp_big_sep m m2 ∗ visit_reached_done γ)%I
          with "[Htok Hintr Hidtok Hvmauth Hc Hmauth Hbigsep Hlb Hlr Hbrproph Hclose_inv]"
        as "Hbig_assert"; last
          iMod "Hbig_assert"
            as "(Htok & Hintr & Hauthv & Hvmauth & Hc & Hmauth & Hbigsep & #Hvisdone)".
        { iMod (na_inv_acc with "Hinv_authv Htok") as "(>Hinvo & Htok & Hclose)";
            [solve_ndisj|solve_ndisj|].
          iDestruct "Hinvo" as "[Hinv_1|Hinv_2]".
          - iDestruct "Hinv_1" as "(%&%&%&%Hxpure1 & Hsusp & #Hfilled & #Hlbvfrag' & #Hvisfin)".
            destruct! Hxpure1. simplify_eq.
            iDestruct (lg_mapg_agree with "Hlbvfrag Hlbvfrag'") as "(<- & _ & _)".
            iPoseProof (id_token_unused with "Hvmauth Hidtok") as "(%Hidunused & Hvmauth & Hidtok)".

            iMod ("Hclose" with "[$Htok Hsusp]") as "Htok".
            { iNext. iLeft. iFrame "Hsusp Hfilled Hlbvfrag Hvisfin". eauto. }

            iAssert (visit_reached_done γ)%I as "#Hvisdone".
            { iDestruct (visit_finished_keep with "Hvisfin") as "[_ $]". }

            iMod ("Hclose_inv" with "[$Htok Hlb Hlr Hbrproph]") as "Htok".
            { iNext. iRight. iFrame "∗ #". iExists _.
              iModIntro. iIntros "$". }

            iModIntro. iFrame "Htok Hintr Hc".
            iAssert (⌜cntr > pid⌝)%I as %Hcntrgt.
            { destruct (le_gt_dec cntr pid) as [Hle|]; last by iPureIntro.
              iDestruct (pval_snapshot_neq _ _ _ _ Hle with "Hpvuneq Hvfrag") as %?.
              done. }
            iAssert (visit_finished γ -∗ id_token cntr)%I with "[Hidtok]"
              as "Hgetidtok".
            { iIntros "_". iExact "Hidtok". }
            iSplitR "Hvmauth".
            { iRight. iExists _, susp0, pid, γ.
              iFrame "Hvfrag Hpvuneq Hlbvfrag Hvisdone Hgetidtok Hinv_authv".
              repeat (iSplit; eauto). }
            admit.

          - iDestruct "Hinv_2" as "(%&%&%&%&%&%&%&%& #Hcap & Hunfill & Hmfrag & %Hmsub & %Hsamser & #Hserpred & Hsusp)".

            destruct! H6. rewrite /filled_string /simple_string in H7. 
            simplify_eq.

            iPoseProof (mapg_auth_alive with "Hmauth Hmfrag") as (y) "%Hin".
            destruct Hin as [(? & Hin & Hxequiv)%Some_equiv_eq Hyequiv].
            edestruct (mapg_alive_lookup_Cinl _ _ _ y Hin) as (y' & Halive & Hyy'); first done.
            clear Hin. rename Halive into Hin.

            iDestruct (big_sepM_delete _ (mapg_alive _) pid y' _ with "Hbigsep") as "[Hms Hbigsep]".
            
            iDestruct "Hms" as (ctr ?? x1 ?????[Hcgt [Hin' Hyequiv']])
                "(Hlc & Hxser & #Hxserpred & Hxserspec & Hxauth & Hxc & Hxfin)".

            assert (x1 = pv) as ->.
                { rewrite Hyy' in Hyequiv'. rewrite Hyequiv' in Hyequiv. simpl in Hyequiv.
                  fold_leibniz. by apply (inj to_agree) in Hyequiv. }

            iDestruct "Hxc" as "(Hxcap & % & Hxc & Hxagg)".
            
            iAssert (⌜cntr > pid⌝)%I as %Hcntrgt.
            { destruct (le_gt_dec cntr pid) as [Hle|]; last by iPureIntro.
              iDestruct (pval_snapshot_neq _ _ _ _ Hle with "Hpvuneq Hvfrag") as %?.
              done. }
            iMod (visited_update_done with
                "Hvmauth Hidtok Hintr Hvfrag Hlbvfrag Hsusp Hxc")
              as "(Hintr & #Hvisdone & Hvmauth & Hxc & Hsusp & Hpvuneq')";
              [ done | done | ].

            iAssert (sub_susp_count_frags t pv ctr pid Nc pv) with "[$Hxcap $Hxc $Hxagg //]" as "Hxc".

            iPoseProof (big_sepM_insert _ _ pid _ 
              with "[$Hbigsep $Hxfin $Hxser $Hxserspec $Hxc $Hlc $Hxauth]") as "Hbigsep".
            { by rewrite lookup_delete. }
            { iExists q. iFrame "#". iPureIntro. split. 
              { inversion Hcgt; simplify_eq; try lia. }
              split; eauto. }

            iMod ("Hclose" with "[$Htok Hunfill Hmfrag Hsusp]") as "Htok".
            { iNext. iRight. iFrame "Hsusp Hunfill Hmfrag Hcap Hserpred". eauto. }

            iMod ("Hclose_inv" with "[$Htok Hlb Hlr Hbrproph]") as "Htok".
            { iNext. iRight. iFrame "∗ #". iExists _.
              iModIntro. iIntros "$". }

            iModIntro. iFrame "Htok Hintr Hc Hvmauth Hmauth".
            iSplitR "Hbigsep".
            { iRight. iFrame "#".
              repeat (iSplit; eauto). admit. }
            admit. }

        case_bool_decide; simplify_eq; v_pures.
        -- v_bind (v_finish _).
          assert (size γl = 0) as Hγl0 by lia.
          destruct! H5; simplify_eq; first lia.

          iDestruct "Hvmauth" as (n0) "Hvmauth".
          set (vm'' := (<[γ:=done_val n0]> vm')).

          iAssert (
            |={⊤}=> ∃ E',
              ⌜E' = ⊤ ∖ ↑ver_susp_n susp⌝ ∗
              □(∀ pid psusp pγ, ⌜pid < cntr⌝ -∗ pval_frag pid psusp -∗
                lg_mapg_frag psusp pγ -∗ visit_reached_done pγ -∗ 
                ⌜↑(ver_susp_n psusp) ⊆ E'⌝) ∗
              auth_transit_v ⊤ cntr (InjRV #susp) s ∗
              visited_map_update_finished vm'' mp2 γ pn' cntr' ∗
              mapg_auth m2 ∗ v_susp_big_sep m m2)%I
            with "[Htok Hauthv Hintr Hvmauth Hmauth Hbigsep]"
            as ">(%&->& #Hnmspc' & Htauthv & Hvmauth & Hmauth & Hbigsep)".
          { iDestruct "Hauthv" as "[[-> Hidtok]|
              (%&%&%&%& ->& %& #Hpvfrag' & #Hpvuneq' & 
                #Hlbvfrag' & #Hvisdone' & Hgetidtok & -> & #_)]".
            
            - iMod (na_inv_acc with "Hinv_authv Htok") as "(>Hinvo & Htok & Hclose)";
                [solve_ndisj|solve_ndisj|].
              iDestruct "Hinvo" as "[Hinv_1|Hinv_2]".
              + iDestruct "Hinv_1" as "(%&%&%&%Hpure & Hsusp & #Hfilled & #Hlbvfrag' & #Hvisfin)".
                destruct! Hpure. simplify_eq.

              + iDestruct "Hinv_2" as "(%&%&%&%&%&%&%&%& Hxcap & Hxunfill & Hxmfrag & %Hxmsub & Hxsusp & Hxproph)".
                destruct! H5; simplify_eq.
            
            - iAssert (⌜cntr > pid⌝)%I as %Hcntrgt.
              { destruct (le_gt_dec cntr pid) as [Hle|]; last by iPureIntro.
                iDestruct (pval_snapshot_neq _ _ _ _ Hle with "Hpvuneq Hvfrag") as %?.
                done. }
              iAssert (⌜pid0 = pid⌝)%I as "->". { admit. }
              iDestruct (pval_frag_agree with "Hvfrag Hpvfrag'") as %<-.
              iDestruct (lg_mapg_agree with "Hlbvfrag Hlbvfrag'") as "(<- & _ & _)".
              iMod (na_inv_acc with "Hinv_authv Htok") as "(>Hinvo & Htok & Hclose)";
                [solve_ndisj|solve_ndisj|].
              iDestruct "Hinvo" as "[Hinv_1|Hinv_2]".
              + iDestruct "Hinv_1" as "(%&%&%&%Hpure & Hsusp & #Hfilled & #Hlbvfrag'' & #Hvisfin)".
                destruct! Hpure. simplify_eq.

                iModIntro. iExists (⊤ ∖ ↑ver_susp_n susp0). iSplit; first done.
                iSplitR.
                { iModIntro. iIntros (pid' psusp pγ Hpidlt) "H1 H2 H3".
                  admit. }
                iDestruct (lg_mapg_agree with "Hlbvfrag Hlbvfrag''") as "(<- & _ & _)".
                iSplitR "Hvmauth"; last admit.
                iRight.
                iFrame "Hvfrag Hpvuneq Hlbvfrag Hvisdone' Hinv_authv Hgetidtok".
                repeat (iSplit; eauto).
                iSplitL "Hintr Hsusp". { iLeft. iFrame "∗ #". admit. }
                admit.

              + iDestruct "Hinv_2" as "(%&%&%&%&%&%&%&%Hpure& Hcap & Hunfill & Hmfrag & %Hmsub & %Hssf & #Hserpred_emp & Hsusp)".
                destruct! Hpure. simplify_eq.

                iPoseProof (mapg_auth_alive with "Hmauth Hmfrag") as (y) "%Hin".
                destruct Hin as [(? & Hin & Hxequiv)%Some_equiv_eq Hyequiv].
                edestruct (mapg_alive_lookup_Cinl _ _ _ y Hin) as (y' & Halive & Hyy'); first done.
                clear Hin. rename Halive into Hin.

                iDestruct (big_sepM_delete _ (mapg_alive _) pid y' _ with "Hbigsep") as "[Hms Hbigsep]".
                
                iDestruct "Hms" as (ctr ?? x1 ?????[Hcgt [Hin' Hy'equiv]])
                    "(Hlc & Hxser & #Hxserpred & Hxserspec & Hxauth & Hxc & Hxfin)".

                assert (x1 = pv) as ->.
                { rewrite Hyy' in Hy'equiv. rewrite Hy'equiv in Hyequiv. simpl in Hyequiv.
                  fold_leibniz. by apply (inj to_agree) in Hyequiv. }

                iMod (visit_update_finished with "Hvmauth Hvisdone' Hintr Hlbvfrag Hsusp Hxc") as "(#Hvisfin & Hintr & Hvmauth & Hxc & Hsusp)".
                { done. }

                iPoseProof (big_sepM_insert _ _ pid _ 
                  with "[$Hbigsep $Hxfin $Hxser $Hxserspec $Hxc $Hlc $Hxauth]") as "Hbigsep".
                { by rewrite lookup_delete. }
                { iExists q. iFrame "#". iPureIntro. split. 
                  { inversion Hcgt; simplify_eq; try lia. }
                  split; eauto. }

                iModIntro. iExists (⊤ ∖ ↑ver_susp_n susp0). iSplit; first done.
                iSplitR.
                { iModIntro. iIntros (pid' psusp pγ Hpidlt) "H1 H2 H3".
                  admit. }

                iFrame "Hvmauth Hmauth".
                iSplitR "Hbigsep"; last admit.
                iRight.
                iFrame "Hvfrag Hpvuneq Hlbvfrag Hvisdone Hinv_authv Hgetidtok".
                repeat (iSplit; eauto).
                iSplitL "Hintr Hsusp". { iLeft. iFrame "∗ #". admit. }
                admit. }

          rewrite /mp2 Hγl0 /=. subst vm''.
          iEval (rewrite visited_map_update_finished_rewrite insert_insert) in "Hvmauth".
          iMod ("Hclose_tab" with "[$Htabtok Hl Hbigsep Hvmauth Hvisinv Hst' Hserp2]") as "Htabtok".
          { iNext. iLeft.
            iExists d, m, m2, (<[γ:=finished_val]> vm'), cntr', pn', _.
            iFrame "Hl Hbigsep Hst' Hserp2 Hvmauth".
            iSplit; first done.
            iSplit; first done.
            iSplit.
            { iPureIntro. intros ctr' Hge. apply Hidinv. lia. }
            iSplit; last first.
            { iPureIntro. rewrite dom_insert set_seq_S_end_union_L. set_solver. }
            subst vm'.
            assert (γl = ∅) as ->.
            { apply size_empty_inv in Hγl0. by fold_leibniz. }
            rewrite set_fold_empty.
            iApply (big_sepM_insert_2 (vm_big_sep_lam_unset m)).
            { rewrite /vm_big_sep_lam_unset. by iIntros (id [=]). }
            iApply "Hvisinv". }

          v_bind (v_finish _).
          iMod ("Hvfinish" $! ⊤ with "[] Htabtok Hlc Hvser Hvserspec Hc
                  Htauthv Hst Hv") as "(Hv & Htabtok & Htok & Hst & Hintr) /=".
          { iModIntro. iIntros (pid' psusp pγ) "%Hlt Hpv Hlg Hvis".
            iPoseProof ("Hnmspc'" $! pid' psusp pγ with "[//] Hpv Hlg Hvis") as "%Hsub".
            iPureIntro. clear -Hsub. set_solver. }

          v_pures. v_bind (list_tail _).
          iMod (gwp_list_tail ⊤ _ (s_real :: _) () (λ v, ⌜is_proof _ ps2⌝)%I
                with "[] [] [$Hv //]") as (u) "[Hv %Hvprf'] /="; [done| |v_pures].
          { by iIntros "!>" (?). }

          iApply ("HΨ"). iFrame "Htabtok Htok Hpr Hi Hintr".
          iModIntro. iSplitL "Hbuf".
          { iPoseProof (big_sepL_cons (λ _, p_buffer_elem) with "Hbuf") as "Hbuf".
            assert
              (((p_finish, s_real, 0) :: combine (combine bufl ps1) lpn) =
                combine (combine (p_finish :: bufl) (s_real :: ps1)) (0 :: lpn))
              as -> by done.
            iFrame "Hbuf".
            iPureIntro. exists prf1, v, (definitions.sum_list (0 :: lpn)).
            simpl. split_and!; try done; lia. }
          iLeft. iExists ps2. iSimpl.
          assert (pn' = definitions.sum_list lpn) as <- by lia.
          iFrame "HA' Hv Hid Hpenc Hstok Hst".
          iSplit.
          { iPureIntro. by rewrite reverse_cons -assoc. }

          iPureIntro.
          eexists _. split; eauto.
          repeat f_equal. lia.

        -- assert (size γl > 0).
          { destruct (size γl); simplify_eq. lia. }
          destruct! H5; try lia; simplify_eq.

          v_load. v_pures. v_bind (map.map_insert _ _ _).
          iMod (gwp_map_insert #cntr _ _ _ () ⊤ _
            (λ d, ⌜is_map d (<[ #cntr := _ ]> m)⌝)%I
            with "[//] [] [$Hv //]") as (?) "[Hv %Hmins] /=".
          { by iIntros "!#" (? Hins). }
          (* Unshelve. 2: done. *)
          
          v_store. v_pures.

          iDestruct (v_susp_big_sep_fresh with "Hbigsep") as %Hm_cntr_none;
            first exact Hidinv.

          iDestruct (big_sepM_insert (v_susp_big_sep_lam m) (mapg_alive m2) cntr (mapg_alive_insert_val a2') Hm_cntr_none
            with "[$Hbigsep $Hvfinish $Hauthv $Hc $Hagg $Hcapf $Hvser]") as "Hbigsep".
          { iFrame "#". admit. }

          iMod ("Hclose_tab" with "[$Htabtok Hl Hbigsep Hmauth Hvmauth Hvisinv Hst' Hlc]") as "Htabtok".
          { iNext. iLeft.

            iPoseProof (big_sepM_mono 
                (v_susp_big_sep_lam m)
                (v_susp_big_sep_lam (<[#cntr:=(#(size γl), v_finish)%V]> m)) 
              with "Hbigsep") as "Hbigsep".
            { iIntros (?? Hlook) "Hbigsep".
              rewrite /v_susp_big_sep_lam.
              iDestruct "Hbigsep" as (?????????[?[??]]) "($ & $ & $ & $)".
              iPureIntro. exists q.
              do 2 (split; eauto).
              rewrite lookup_insert_ne; eauto.
              intros ?. simplify_eq.
              specialize (Hidinv k ltac:(lia)).
              simplify_eq. }

            iEval (rewrite -mapg_alive_insert) in "Hbigsep".
            iFrame "Hl Hmauth Hst' Hbigsep".

            (* framing the giant [visited_mapg_auth] into the table's
                existential diverges; block was admitted anyway. *)
            admit. }

          v_pures. v_bind (list_tail _).
          iMod (gwp_list_tail ⊤ _ (s_real :: _) () (λ v, ⌜is_proof _ ps2⌝)%I
                with "[] [] [$Hv //]") as (u) "[Hv %Hvprf'] /="; [done| |v_pures].
          { by iIntros "!>" (?). }

          iApply ("HΨ"). iFrame "Htabtok Htok Hpr Hi Hintr".
          iModIntro. iSplitL "Hbuf".
          { iPoseProof (big_sepL_cons (λ _, p_buffer_elem) with "Hbuf") as "Hbuf".
            assert
              (((p_finish, s_real, size γl) :: combine (combine bufl ps1) lpn) =
                combine (combine (p_finish :: bufl) (s_real :: ps1)) (size γl :: lpn))
              as -> by done.
            iFrame "Hbuf".
            iPureIntro. exists prf1, v, (definitions.sum_list (size γl :: lpn)).
            simpl. split_and!; try done; lia. }
          iLeft. iExists ps2. iSimpl.
          assert (pn' = size γl + definitions.sum_list lpn) as <- by lia.
          iFrame "HA' Hv Hid Hpenc Hstok Hst".
          iSplit.
          { iPureIntro. by rewrite reverse_cons -assoc. }

          iPureIntro.
          eexists _. split; eauto.
          repeat f_equal. lia.
  Admitted.

  Lemma refines_Authenticatable Θ (Δ : ctxO Σ Θ) :
    ⊢ REL p_Authenticatable << v_Authenticable << i_Authenticable : ⟦ Authenticatable ⟧ (auth_ctx Δ).
  Proof.
    iIntros (????) "Hv Hi Htok".
    rewrite /i_Authenticable /v_Authenticable /v_Authenticable_run.
    v_bind (map.map_empty _).
    iMod (gwp_map_empty val val _ () ⊤ (λ v, ⌜is_map v (∅ : gmap val val)⌝)%I
           with "[% //] [] [$Hv //]") as (x) "[Hv %Hx] /=".
    { by iIntros "!#" (??). }

    v_alloc as l "Hl". v_pures.
    wp_pures.
    iEval (rewrite /v_unauth /v_run_def) in "Hv".
    v_pures. i_pures.
    iDestruct "Hl" as "[Hl _]".
    iMod (na_inv_alloc tabseqG_name ⊤ tableN (is_v_susp_table l)
      with "[Hl]") as "#Htab".
    { iNext. iLeft.
      iExists x, ∅, ∅, ∅, 0, 0, ∅. iFrame "Hl".
      (* initial ghost state for the fixed correctnessG gnames — must be
         allocated where the instance is created (adequacy theorem) *)
      admit. }
    iModIntro. iExists _, _. iFrame "Hv Hi Htok".
    iExists lrel_evidence; rewrite -!/interp.
    iExists _, _, _, _, _, _; rewrite -!/interp.
    do 3 (iSplit; [done|]).
    iSplit; last first.
    { iApply (refines_auth_unauth with "Htab"). }
    iExists _, _, _, _, _, _; rewrite -!/interp.
    do 3 (iSplit; [done|]).
    iSplit; last first.
    { iApply refines_auth_auth. }
    iExists _, _, _, _, _, _; rewrite -!/interp.
    do 3 (iSplit; [done|]).
    iSplit; last first.
    { interp_unfold!.
      replace (⟦ t_nat ⟧ (ext (auth_ctx Δ) lrel_evidence))
        with (LRelTern lrel_int lrel_un_int : lrel_tern Σ)
        by (rewrite interp_unseal; reflexivity).
      iApply refines_Auth_int. }
    iExists _, _, _, _, _, _; rewrite -!/interp.
    do 3 (iSplit; [done|]).
    iSplit; last first.
    { interp_unfold!.
      replace (⟦ t_string ⟧ (ext (auth_ctx Δ) lrel_evidence))
        with (LRelTern lrel_string lrel_un_string : lrel_tern Σ)
        by (rewrite interp_unseal; reflexivity).
      iApply refines_Auth_string. }
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
    iApply auth_auth.refines_Auth_auth.
  Admitted.
    

    (* iExists lrel_evidence; rewrite -/interp.
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
  Qed. *)

  Lemma refines_authentikit_func Θ (Δ : ctxO Σ Θ) :
    ⊢ REL p_Authentikit << v_Authentikit << i_Authentikit :
      ⟦ Authentikit_func var1 var0 ⟧ (auth_ctx Δ).
  Proof.
    iIntros (????) "Hv Hi Htok".
    rewrite /p_Authentikit /v_Authentikit /i_Authentikit.
    v_bind (v_Authenticable); i_bind (i_Authenticable).
    iPoseProof (refines_Authenticatable _ (auth_ctx Δ)) as "HAc".
    iSpecialize ("HAc" with "Hv Hi Htok").
    iEval (rewrite wp_value_fupd') in "HAc".
    iMod "HAc" as "(%vv & %vi & Hv & Hi & #HAc' & Htok)".
    iEval (simpl) in "Hv". iEval (simpl) in "Hi".
    v_pures; i_pures; wp_pures.
    iModIntro. iExists _, _. iFrame "Hv Hi Htok".
    rewrite /Authentikit_func.
    iEval (rewrite !interp_app_unfold).
    assert (⟦ (Λ: (Λ: (∀: ⋆, var0 → var1 var0) *
               (∀: ⋆; ⋆, var2 var1 → (var1 → var2 var0) → var2 var0) *
               Authenticatable)) var1 ⟧ (auth_ctx Δ) (⟦ var0 ⟧ (auth_ctx Δ))
            = ⟦ (∀: ⋆, var0 → var1 var0) *
                (∀: ⋆; ⋆, var2 var1 → (var1 → var2 var0) → var2 var0) *
                Authenticatable ⟧ (auth_ctx (auth_ctx Δ))) as ->
      by (rewrite interp_unseal; reflexivity).
    interp_unfold!.
    iExists _, _, _, _, _, _; rewrite -!/interp.
    do 3 (iSplit; [done|]).
    iSplit; last first.
    { iApply "HAc'". }
    iExists _, _, _, _, _, _; rewrite -!/interp.
    do 3 (iSplit; [done|]).
    iSplit; [iApply refines_auth_return|].
    iApply refines_auth_bind.
  Qed.

  (* Lemma refines_authentikit_func Θ (Δ : ctxO Σ Θ) :
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
  Qed. *)

  (* Lemma refines_authentikit Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ Authentikit ⟧ Δ p_Authentikit v_Authentikit i_Authentikit.
  Proof.
    iExists lrel_auth, lrel_auth_comp; rewrite -3!/interp.
    iApply refines_authentikit_func.
  Qed. *)


  Definition rel_authentikit_output (A : lrel Σ) (prf : val) (ps : list string) : lrel Σ :=
    LRel (λ v1 v2 v3, ∃ a1 a2 a3, ⌜v1 = (prf, a1)%V⌝ ∗ ⌜v2 = SOMEV a2⌝ ∗ ⌜v3 = a3⌝ ∗ A a1 a2 a3)%I.

  Lemma refines_run Θ (Δ : ctxO Σ Θ) (p : proph_id) ps (c1 c2 c3 : expr) w A :
    is_proph_reverse_proof w p ps -∗
    (REL c1 << c2 << c3 : lrel_auth_comp A) -∗
    REL p_run #~ #p c1 << v_run #~ c2 w << i_run #~ c3 : rel_authentikit_output A w ps.
  Proof.
    iIntros "[%Hprf Hproph] Hc" (????) "Hv Hi Htok".
    rewrite /v_run /i_run /p_run.
    v_bind c2; i_bind c3; wp_bind (c1).

    iSpecialize ("Hc" with "Hv Hi Htok").
    wp_apply (wp_wand with "Hc").
    iIntros (f1) "(%f2 & %f3 & Hv & Hi & Hc & Htok) /=".
    rewrite /v_Authenticable_run.
    v_bind (map.map_empty _).
    iMod (gwp_map_empty val val _ () ⊤ (λ v, ⌜is_map v (∅ : gmap val val)⌝)%I
           with "[% //] [] [$Hv //]") as (x) "[Hv %Hx] /=".
    { by iIntros "!#" (??). }

    v_alloc as l "[Hl _]". v_pures.
    rewrite /v_run_def. v_pures.
    rewrite /v_unauth.

    wp_pures; v_pures; i_pures.
    apply is_list_inject in Hprf as ->.
    iDestruct "Hproph" as (us) "[Hproph %Hps]".

    iAssert (|==> tabseq_tok ⊤ ∗ intransit 1 ∗ tern_state ∗ tern_state ∗
        visited_mapg_auth ∅ ∅ 0 0 ∗ pencount_frag 0 ∗ id_ctr_frag 0 ∗
        serpred_auth ∅)%I
      as ">(Htabtok & Hintr & Hst & Hst2 & Hvmauth & Hpc & Hid & Hserp)".
    { (* ghost init for the fixed correctnessG/tabseqG gnames — belongs at
         the adequacy theorem where the instances are allocated *) admit. }

    iMod (na_inv_alloc tabseqG_name ⊤ tableN (is_v_susp_table l)
      with "[Hl Hvmauth Hst2 Hserp]") as "#Htab".
    { iNext. iLeft. iExists x, ∅, ∅, ∅, 0, 0, ∅.
      iFrame "Hl Hvmauth Hst2 Hserp".
      rewrite /v_susp_big_sep /vm_big_sep /mapg_alive omap_empty.
      rewrite !big_sepM_empty.
      iPureIntro. split_and!; done. }

    iDestruct "Hc" as "(Hc & _)".
    v_bind (f2 _).

    (* wp_apply ("Hc" with "[$Htok $Hproph $Hv $Hi]"). *)
    wp_apply ("Hc" $! _ _ _ _ _ ps [] (reverse ps) [] []
        with "[$Htabtok $Hproph $Hv $Hi $Htok $Hintr $Hst Hpc $Hid]").
    { simpl.
      iSplitL "Hpc"; [by iFrame "Hpc"|].
      iSplitL.
      { iExists (InjLV #()), (InjLV #()), [], 0.
        rewrite /p_buffer big_sepL_nil.
        repeat (iSplit; eauto). }
      iSplit.
      { iExists (inject_list (reverse ps)). iPureIntro.
        split; first done. rewrite /is_proof ?is_list_inject //. }
      iSplit; iPureIntro; eauto.
      rewrite reverse_involutive app_nil_r //. }
      
    iIntros (ps1' lpn' w1 a1 a3) "(Htabtok & Htok & Hi & Hintr & Hproph & Hpw & Hv) /=".
    wp_pures.
    iDestruct "Hpw" as (??????) "(% & -> & Hbuf & % & %Hbuf)".
    wp_pures.
    iAssert (intransit (3/4) ∗ intransit (1/4))%I with "[Hintr]" as "[Hintr34 Hintr14]".
    { rewrite -intransit_split.
      replace (3/4 + 1/4)%Qp with 1%Qp by compute_done. iFrame. }
    wp_apply (flush_buf_stream_spec with "[$Hproph $Hbuf $Htok $Hintr14]").
    { instantiate (1 := pn). instantiate (1 := []).
      repeat (iSplit; eauto). iPureIntro.
      rewrite -H. done. }

    iIntros (????) "(%&%&%&%& Hproph & Htok & Hgoodtr)".
    wp_pures.
    
    wp_apply (wp_resolve_proph_nil_string with "Hproph").
    iIntros (->). simplify_list_eq. wp_pures.

    iDestruct "Hv" as "[(%ps2' &%w2' &%a2 & Hpc' & %Heqrev & HA & Hv & Hvw & Hst)|[%|(%Hne & HA & Hst)]]"; last first.
    { unfold lastn in Hne.
      assert (∀ {A} (x : list A), (length x) - (length x) = 0) by lia.
      specialize (H1 _ (longest_valid_prefix_string (map snd us))).
      rewrite H1 in Hne. simplify_list_eq. }
    { lia. }

    assert (ps2' = []) as ->.
    { assert (length (reverse ps2') = 0) as Hlen.
      { apply (f_equal (@length _)) in Heqrev. rewrite app_length in Heqrev. lia. }
      apply length_zero_iff_nil in Hlen.
      apply (f_equal (@reverse _)) in Hlen. by rewrite reverse_involutive in Hlen. }
    simplify_list_eq.

    iMod (na_inv_acc with "Htab Htabtok") as "(Htabo & Htabtok & Htab_close)"; try solve_ndisj.
    wp_rec.
    iDestruct "Htabo" as "[(%d &%m &%m' &%vm &%idctr &%pn &%msp & Hl & %Hm &
          Hbigsep & %Hszeq & Hvmauth & %Hidinv & Hvisinv & Hst' & Hserp & %Hmspdom) | Hstbad]";
      last first.
    { by iPoseProof (tern_state_un_state_excl with "Hst Hstbad") as "?". }

    iDestruct (pn_agree with "Hvmauth Hpc'") as %<-.

    iDestruct "Hvw" as (??) "[[-> %] Hid']".
    iDestruct (id_ctr_frag_agree with "Hvmauth Hid'") as %->.

    v_pures. v_load.

    destruct (size m) eqn:Hmsize; last first.
    { assert (size m ≠ 0) as Hmnonemp by lia.
      assert (size (mapg_alive m') ≠ 0) as Hm'nonemp by lia.

      iAssert (⌜∀ (id : nat), id ∈ dom (mapg_alive m') → ∃ v, m !! #id = Some v⌝)%I
        as %Hbigsepdom.
      { iIntros (id Hin).
        apply elem_of_dom in Hin as [agv Hagv].
        iPoseProof (big_sepM_lookup _ _ id agv Hagv with "Hbigsep") as "Hms".
        iDestruct "Hms" as (?????????) "[(% & %Hmid & _) _]".
        iPureIntro. eauto. }

      set (keys := dom (mapg_alive m')).
      set (max_id := set_fold Nat.max 0 keys).
      assert (max_id ∈ keys) as Hmaxin.
      { apply gset_max_elem_of. intros Hempty. apply Hm'nonemp.
        rewrite -size_dom. unfold keys in Hempty. rewrite Hempty size_empty //. }
      assert (∃ v, (mapg_alive m') !! max_id = Some v) as [vmax Hvmax]
        by (apply elem_of_dom; exact Hmaxin).

      iPoseProof (big_sepM_lookup_acc _ (mapg_alive m') max_id vmax Hvmax with "Hbigsep") as "[Hms Hbigsep]".
      iDestruct "Hms" as (ctr_v Nc_v finish_v xv av serv tv sv qv)
        "((%Hctr_v & %Hmid_v & %Hagv_v) & _ & _ & _ & _ & _ & Hxc & _)".

      iMod ("Hgoodtr" with "Hst Hvmauth Hpc'") as "(Hst & Hvmauth & Hpc')".

      assert ((1/2 < 3/4)%Qp) as Hhalf by compute_done.
      iPoseProof (gt_child _ _ _ _ _ _ _ _ _ _ (3/4)%Qp
          with "[%] [%] Hvisinv Hintr34 Hpc' Hxc Hvmauth")
        as "[%Hpn|%Hex]"; try lia; try exact Hhalf.
      destruct Hex as (id' & v' & Hgt & Hlookup); simplify_eq.

      assert (id' ∈ keys) as Hid'in.
      { apply (id_in_alive_dom m keys id').
        - unfold keys. rewrite size_dom. by rewrite Hszeq.
        - exact Hbigsepdom.
        - eauto. }

      assert (id' ≤ max_id) by (apply gset_max_ge; exact Hid'in).
      exfalso. lia. }

    v_bind (map_is_empty d).
    iMod (gwp_map_is_empty () ⊤ d m 
        (λ v, ∃ (b : bool), ⌜v = #b ∧ b = Nat.eqb 0 (size m)⌝)%I
      with "[//] [] [$Hv //]") as (?) "[Hv %Hmemp] /=".
    { iIntros "!#" (??). eauto. }

    iMod ("Htab_close" with "[$Htabtok Hl Hvmauth Hbigsep Hvisinv Hst' Hserp]") as "Htabtok".
    { iNext. iLeft. iFrame "Hl Hvmauth Hbigsep Hvisinv Hst' Hserp".
      iFrame "%". iPureIntro. lia. }

    destruct! Hmemp. simplify_eq. rewrite Hmsize.
    v_pures.

    wp_pures. wp_rec. wp_pures. wp_rec. wp_pures.
    iFrame. 
    apply is_list_inject in H5 as ->.
    iModIntro. eauto.
  Admitted.


  Lemma refines_instantiate (c1 c2 c3 : expr) (τ : type _ ⋆) :
    (REL c1 << c2 << c3 : ⟦ ∀: ⋆ ⇒ ⋆; ⋆ ⇒ ⋆, Authentikit_func var1 var0 → var0 τ ⟧ ∅) -∗
    REL c1 #~ #~ p_Authentikit
     << c2 #~ #~ v_Authentikit
     << c3 #~ #~ i_Authentikit : lrel_auth_comp (⟦ τ ⟧ (auth_ctx ∅)).
  Proof.
    iIntros "Hc" (????) "Hv Hi Htok".
    v_bind (v_Authentikit); i_bind (i_Authentikit).
    iPoseProof (refines_authentikit_func _ ∅) as "Hfunc".
    iSpecialize ("Hfunc" with "Hv Hi Htok").
    iEval (rewrite wp_value_fupd') in "Hfunc".
    iMod "Hfunc" as "(%vv & %vi & Hv & Hi & #Hfunc' & Htok)".
    iEval (simpl) in "Hv". iEval (simpl) in "Hi".
    wp_bind c1; v_bind c2; i_bind c3.
    iSpecialize ("Hc" with "Hv Hi Htok").
    wp_apply (wp_wand with "Hc").
    iIntros (v1) "(%v2 & %v3 & Hv & Hi & Hcnt & Htok)".
    iDestruct "Hcnt" as "(Hcnt & _)".
    interp_unfold! in "Hcnt".
    iEval (unfold lrel_tern_tern, lrel_forall, lrel_forall', lrel_arr, lrel_arr', lrel_car) in "Hcnt".
    idtac "===L1===". Show.
    iSpecialize ("Hcnt" $! lrel_auth).
    iSpecialize ("Hcnt" $! #~ #~ #~ with "[//]").
    v_bind (v2 _); i_bind (v3 _).
    iSpecialize ("Hcnt" with "Hv Hi Htok").
    wp_apply (wp_wand with "Hcnt").
    iIntros (v1') "(%v2' & %v3' & Hv & Hi & Hcnt & Htok)".
    iDestruct "Hcnt" as "(Hcnt & _)".
    interp_unfold! in "Hcnt".
    iEval (unfold lrel_tern_tern, lrel_forall, lrel_forall', lrel_arr, lrel_arr', lrel_car) in "Hcnt".
    iSpecialize ("Hcnt" $! lrel_auth_comp).
    iSpecialize ("Hcnt" $! #~ #~ #~ with "[//]").
    v_bind (v2' _); i_bind (v3' _).
    iSpecialize ("Hcnt" with "Hv Hi Htok").
    wp_apply (wp_wand with "Hcnt").
    iIntros (v1'') "(%v2'' & %v3'' & Hv & Hi & Hcnt & Htok)".
    iDestruct "Hcnt" as "(Hcnt & _)".
    interp_unfold! in "Hcnt".
    iEval (unfold lrel_tern_tern, lrel_arr, lrel_arr', lrel_car) in "Hcnt".
    iSpecialize ("Hcnt" $! p_Authentikit vv vi with "Hfunc'").
    iSpecialize ("Hcnt" with "Hv Hi Htok").
    wp_apply (wp_wand with "Hcnt").
    iIntros (r1) "(%r2 & %r3 & Hv & Hi & Hres & Htok)".
    iExists _, _. iFrame "Hv Hi Htok".
    assert (⟦ var0 τ ⟧ (ext (ext ∅ lrel_auth) lrel_auth_comp)
            = lrel_auth_comp (⟦ τ ⟧ (auth_ctx ∅))) as Hconv
      by (rewrite interp_unseal; reflexivity).
    iEval (rewrite Hconv) in "Hres".
    iExact "Hres".
  Qed.


End proof.

(*
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
*)
