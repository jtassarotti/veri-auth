From auth.prelude Require Import stdpp.
From auth.rel_logic_tern_susp Require Export model spec_rules spec_tactics interp.
From auth.heap_lang Require Import primitive_laws derived_laws.
From auth.heap_lang.lib Require Import list map.
From auth.examples Require Export authentikit_susp.
From auth.examples.susp_correctness Require Import definitions helpers finish_specs unauth_step.
From iris.base_logic.lib Require Export na_invariants fancy_updates.

(** We need [i_Authentikit] to be an expression since [v_Authenticable] needs to initialize its
    cache and specialize [v_unauth]. *)
Definition i_Authenticable : expr :=
  (i_Auth_auth, i_Auth_mu, i_Auth_pair, i_Auth_sum, i_Auth_string, i_Auth_int, i_auth, i_unauth).
Definition i_Authentikit : expr := (i_return, i_bind, i_Authenticable).

(** * Correctness proof *)
Section proof.
  Context `{!authG Σ, !seqG Σ, !tabseqG Σ, !correctnessG Σ}.

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
    ⊢ REL p_unauth << v_unauth #c << i_unauth :
      ⟦ ∀: ⋆, var1 var0 → var3 var0 → var2 var0 ⟧
      (ext (auth_ctx Δ) lrel_evidence).
  Proof.
    iIntros "#Htab" (????) "Hv Hi Htok".
    rewrite /p_unauth /v_unauth /i_unauth.
    v_pures; wp_pures.
    iModIntro. iFrame. clear.
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
        "!# (Htabtok & Htok & Hv & Hi & Hpenc & Hpw & Hvw & Hpr & % & Hintr & Hst & Hstok) HΨ".
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
          admit. }

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
          as "(Hvmauth & Hid & Hidtok & Hpvfrag & Hcapf & Hmapf)".
        iMod ("Hdecorate" with "Hcapf Hmapf [] []") as "(#HA' & Hc & Hvser)".
        { by destruct c'. }
        { admit. (* pval_snapshot minting for the fresh verifier locs at the
                    just-committed id — pending the general apartness lemma. *) }

        (* iPoseProof (big_sepM_mono
            (vm_big_sep_lam_unset m)
            (vm_big_sep_lam_set m cntr)
          with "Hvisinv") as "Hvisinv".
        { iIntros (k x0' Hkx0) "Hvis".
          iIntros (id_inner Heq ->).
          iApply "Hvis"; try done. } *)

        iSimpl in "Hv". v_pures. v_bind (v_count _).
        iDestruct "Hc" as "(Hcap & % & Hc & Hagg)".
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
          iFrame "HA' Hv Hid Hpenc Hstok Hst".
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

          iAssert (sub_susp_count_frags tA a2' (size γl) cntr (size γl))%I
            with "[$Hcap $Hc $Hagg //]" as "Hc".
        
          v_load. v_pures. v_bind (map.map_insert _ _ _).
          iMod (gwp_map_insert #cntr _ _ _ () ⊤ _
            (λ d, ⌜is_map d (<[ #cntr := _ ]> m)⌝)%I
            with "[//] [] [$Hv //]") as (?) "[Hv %Hmins] /=".
          { by iIntros "!#" (? Hins). }
          (* Unshelve. 2: done. *)
          
          v_store.

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

            iSplit; first admit.
            iSplit.
            { iPureIntro. intros ??.
              rewrite lookup_insert_None.
              specialize (Hidinv ctr' ltac:(lia)).
              split; eauto. intros ?. simplify_eq. lia. }

            iSplit; last first.
            { iPureIntro. rewrite dom_insert set_seq_S_end_union_L.
              set_solver. }
            admit. }

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

          iLeft. iExists ps2. iFrame "HA' Hv Hid Hstok Hst Hpenc".
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
               [$Htabtok $Hv $Hi $Hpenc $Hbuf $Hid $Hpr $Hintr $Hstok $Hst $Htok]
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
               [$Htabtok $Hv $Hi $Hpenc $Hbuf $Hid $Hpr $Hintr $Hstok $Hst $Htok]
               HΨ"); eauto.

      + iDestruct "Hbrproph" as "(Hbrproph & %&%)".
        wp_pures; wp_apply (wp_resolve_proph_bool with "Hbrproph").
        iIntros (?) "[% Hbrproph]"; simplify_eq; wp_pures; wp_store.

        iAssert (visit_reached_done γ)%I as "#Hvisit".
        { (* pending: visit fact for the unfill first-disjunct branch — the old
             inline block admitted this at three sites while the invariant was
             still open *) admit. }
        iMod ("Hclose_inv" with "[$Htok Hlb Hlr Hbrproph]") as "Htok".
        { iNext. iRight. iFrame "∗ #". iExists _. iModIntro. iIntros "$". }

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
             [$Htabtok $Hv $Hi $Hpenc $Hbuf $Hid $Hpr $Hintr $Hstok $Hst $Htok]
             HΨ"); eauto.
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
    Admitted.
  (*
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

    iAssert (mapg_auth ∅) as "Hmauth"; first admit.
    iAssert (intransit 1) as "Hintr"; first admit.
    iAssert (tern_state) as "Hst"; first admit.
    iAssert (visited_mapg_auth ∅ ∅ ∅ 0 0 ∅) as "Hvmauth"; first admit.
    iAssert (pencount_frag 0) as "Hpc"; first admit.
    iAssert (id_ctr_frag 0) as "Hid"; first admit.
    iAssert (stok_comp None) as "Hstok"; first admit.
    iPoseProof (stok_split with "Hstok") as "[Hstok'' Hstok']".
    iClear "Hstok".

    iMod (na_inv_alloc seqG_name ⊤ tableN (is_v_susp_table l) 
      with "[$Hl $Hmauth]") as "#Htab".
    { admit. }

    iDestruct "Hc" as "(Hc & _ & _)".
    v_bind (f2 _).

    (* wp_apply ("Hc" with "[$Htok $Hproph $Hv $Hi]"). *)
    wp_apply ("Hc" $! _ _ _ _ _ ps [] (reverse ps) _ [] 
        with "[$Hproph $Hv $Hi $Htok $Hintr $Hst $Hstok'' Hpc $Hid]").
    { simpl. iFrame "#".
      iSplitL.
      { repeat iExists _.
        repeat instantiate (2 := []).
        repeat (iSplit; eauto).
        simpl. unfold p_buffer.
        by iApply big_sepL_nil. }
      repeat (iSplit; eauto); last first.
      { admit. }
      iPureIntro.
      eexists _. split; eauto. admit. }
      
    iClear "Hid Hmauth Hintr Hst Hvmauth Hpc".
    iIntros (ps1' lpn' w1 a1 a3) "(Htok & Hi & Hintr & Hproph & Hpw & Hpc & Hstok & Hv) /=".
    wp_pures.
    iDestruct "Hpw" as (??????) "(% & -> & Hbuf & % & %Hbuf)".
    wp_pures.
    wp_apply (flush_buf_stream_spec with "[$Hproph $Hbuf $Htok $Hintr]").
    { instantiate (1 := pn). instantiate (1 := []).
      repeat (iSplit; eauto). iPureIntro.
      rewrite -H. done. }

    iIntros (????) "(%&%&%&%& Hproph & Htok & Hgoodtr)".
    wp_pures.
    
    wp_apply (wp_resolve_proph_nil_string with "Hproph").
    iIntros (->). simplify_list_eq. wp_pures.

    iDestruct "Hv" as "[(%&%&%& % & HA & Hv & Hvw & Hst)|[%|(%Hne & HA & Hst)]]"; last first.
    { unfold lastn in Hne. 
      assert (∀ {A} (x : list A), (length x) - (length x) = 0) by lia.
      specialize (H1 _ (longest_valid_prefix_string (map snd us))).
      rewrite H1 in Hne. simplify_list_eq. }
    { lia. }

    assert (ps2' = []) as -> by admit.
    simplify_list_eq.

    iMod (na_inv_acc with "Htab Htok") as "(Htabo & Htok & Htab_close)"; try solve_ndisj.
    wp_rec.
    iDestruct "Htabo" as "(%&%&%&%&%&%& %idctr &% &% & Hl & %Hm &
          Hbigsep & Hmauth & %Hszeq & Hvmauth & %Hidinv & Hvisinv)".

    assert (pn = sum_list lpn') as -> by admit.
    
    iDestruct "Hvw" as (??) "[[-> %] Hid']".
    assert (cntr = idctr) as -> by admit.

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
        "((%Hctr_v & %Hmid_v & %Hagv_v) & _ & _ & _ & _ & Hxc & _)".

      iMod ("Hgoodtr" with "Hst Hvmauth Hpc") as "(Hst & Hvmauth & Hpc)".

      iPoseProof (gt_child with "[%//] Hvisinv Hstok Hpc Hxc Hvmauth")
        as "[%Hpn|%Hex]"; try lia.
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

    iMod ("Htab_close" with "[$Htok $Hl $Hvmauth $Hmauth $Hbigsep $Hvisinv]") as "Htok".
    { iFrame "%". iNext. iPureIntro. lia. }

    destruct! Hmemp. simplify_eq. rewrite Hmsize.
    v_pures.

    wp_pures. wp_rec. wp_pures. wp_rec. wp_pures.
    iFrame. 
    apply is_list_inject in H5 as ->.
    iModIntro. eauto. *)

  Lemma refines_instantiate (c1 c2 c3 : expr) (τ : type _ ⋆) :
    (REL c1 << c2 << c3 : ⟦ ∀: ⋆ ⇒ ⋆; ⋆ ⇒ ⋆, Authentikit_func var1 var0 → var0 τ ⟧ ∅) -∗
    REL c1 #~ #~ p_Authentikit
     << c2 #~ #~ v_Authentikit
     << c3 #~ #~ i_Authentikit : lrel_auth_comp (⟦ τ ⟧ (auth_ctx ∅)).
  Proof. Admitted. (*
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
    iFrame. *)

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
