(** Compataibility rules *)
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import list.
From iris.program_logic Require Import ectx_lifting.
From auth.heap_lang Require Import proofmode_upto_bad.
From auth.rel_logic_tern Require Export model spec_rules spec_tactics.

Section compatibility.
  Context `{!authG Σ}.
  Implicit Types e : expr.

  Local Ltac value_case :=
    wp_pures; v_pures; i_pures.

  Local Tactic Notation "rel_bind_ap" uconstr(e1) uconstr(e2) uconstr(e3) constr(IH) ident(v) ident(w) ident(u) constr(H) :=
    wp_bind e1; v_bind e2; i_bind e3;
    iSpecialize (IH with "[$] [$]");
    iApply wp_wand_r;
    iSplitL IH; [iApply IH|];
    iIntros (v); iDestruct 1 as (w u) H; simpl.

  Lemma refines_pair e1 e2 e1' e2' e1'' e2'' A B :
    (REL e1 << e1' << e1'' : A) -∗
    (REL e2 << e2' << e2'' : B) -∗
    REL (e1, e2) << (e1', e2') << (e1'', e2'') : A * B.
  Proof.
    iIntros "IH1 IH2" (????) "Hv Hi".
    rel_bind_ap e2 e2' e2'' "IH2" v1 v2 v3 "(Hw & Hi & HB)".
    rel_bind_ap e1 e1' e1'' "IH1" w1 w2 w3 "(Hw & Hi & HA)".
    value_case.
    iModIntro. iExists _, _. by iFrame.
  Qed.

  Lemma refines_app e1 e2 e1' e2' e1'' e2'' A B :
    (REL e1 << e1' << e1'' : A → B) -∗
    (REL e2 << e2' << e2'' : A) -∗
    REL App e1 e2 << App e1' e2' << App e1'' e2'' : B.
  Proof.
    iIntros "IH1 IH2" (????) "Hv Hi".
    rel_bind_ap e2 e2' e2'' "IH2" v v' v'' "(Hv & Hi & HA)".
    rel_bind_ap e1 e1' e1'' "IH1" f f' f'' "(Hv & Hi & HAB)".
    iApply ("HAB" with "HA Hv Hi").
  Qed.

  Lemma refines_seq A e1 e2 e1' e2' e1'' e2'' B :
    (REL e1 << e1' << e1'' : A) -∗
    (REL e2 << e2' << e2'' : B) -∗
    REL (e1;; e2) << (e1';; e2') << (e1'';; e2'') : B.
  Proof.
    iIntros "IH1 IH2" (????) "Hv Hi".
    rel_bind_ap e1 e1' e1'' "IH1" v v' v'' "(Hv & Hi &Hvv)".
    v_pures. i_pures. wp_pures.
    iApply ("IH2" with "[$] [$]").
  Qed.

  #[local] Existing Instance ofe_ne_eta.

  Lemma refines_pack A e e' e'' (C : A -n> lrel Σ) :
    (∃ (a : A), REL e << e' << e'' : C a) -∗
    REL e << e' << e'' : ∃; (a : A), C a.
  Proof.
    iIntros "[%a H]" (????) "Hv Hi".
    rel_bind_ap e e' e'' "H" v v' v'' "($ & $ & $)".
  Qed.

  Lemma refines_forall A e e' e'' (C : A -n> lrel Σ) :
    □ (∀ (a : A), REL e << e' << e'' : C a) -∗
    REL (λ: <>, e)%V << (λ: <>, e')%V << (λ: <>, e'')%V : ∀; (a : A), C a.
  Proof.
    iIntros "#H" (????) "Hv Hi".
    wp_pures.
    iFrame.
    iIntros "!#" (a ?) "!#".
    iIntros (??) "_". iIntros (????) "Hv Hi".
    v_pures; i_pures; wp_pures.
    iApply ("H" with "[$] [$]").
  Qed.

  Lemma refines_store e1 e2 e1' e2' e1'' e2'' A :
    (REL e1 << e1' << e1'' : ref A) -∗
    (REL e2 << e2' << e2'' : A) -∗
    REL e1 <- e2 << e1' <- e2' << e1'' <- e2'' : ().
  Proof.
    iIntros "IH1 IH2" (Kₚ tₚ Kᵢ tᵢ) "Hv Hi".
    rel_bind_ap e2 e2' e2'' "IH2" w w' w'' "(Hv & Hi & #HAw)".
    rel_bind_ap e1 e1' e1'' "IH1" v v' v'' "(Hv & Hi & #Hr)".
    iDestruct "Hr" as (l l' l'') "(-> & -> & -> & Hr)".
    iInv (authN .@ "ref" .@ (l,l',l'')) as
      (u u' u'') "(>Hu & >Hu' & >Hu'' & #HAu)" "Hclose".
    wp_store.
    v_store.
    i_store.
    iMod ("Hclose" with "[$Hu $Hu' $Hu'' $HAw]") as "_".
    by iFrame.
  Qed.

  Lemma refines_xchg e1 e2 e1' e2' e1'' e2'' A :
    (REL e1 << e1' << e1'' : ref A) -∗
    (REL e2 << e2' << e2'' : A) -∗
    REL Xchg e1 e2 << Xchg e1' e2' << Xchg e1'' e2'' : A.
  Proof.
    iIntros "IH1 IH2" (????) "Hv Hi".
    rel_bind_ap e2 e2' e2'' "IH2" w w' w'' "(Hv & Hi & #HAw)".
    rel_bind_ap e1 e1' e1'' "IH1" v v' v'' "(Hv & Hi & #Hr)".
    iDestruct "Hr" as (l l' l'') "(-> & -> & -> & Hr)".
    iInv (authN .@ "ref" .@ (l,l',l'')) as
      (u u' u'') "(>Hu & >Hu' & >Hu'' & #HAv)" "Hclose".
    wp_xchg.
    v_xchg.
    i_xchg.
    iMod ("Hclose" with "[$Hu $Hu' $Hu'' $HAw]") as "_".
    by iFrame.
  Qed.

  Lemma refines_load e e' e'' A :
    (REL e << e' << e'' : ref A) -∗
    REL !e << !e' << !e'' : A.
  Proof.
    iIntros "IH" (????) "Hv Hi".
    rel_bind_ap e e' e'' "IH" v v' v'' "(Hv & Hi & #Hr)".
    iDestruct "Hr" as (l l' l'' -> -> ->) "#H".
    iInv (authN .@ "ref" .@ (l,l',l'')) as
          (u u' u'') "(>Hu & >Hu' & >Hu'' & #HAv)" "Hclose".
    wp_load.
    v_load.
    i_load.
    iMod ("Hclose" with "[$Hu $Hu' $Hu'' $HAv]") as "_".
    by iFrame.
  Qed.

  Lemma refines_fork e e' e'' :
    (REL e << e' << e'' : ()%lrel) -∗
    REL Fork e << Fork e' << Fork e'' : ().
  Proof.
    iIntros "IH" (????) " Hv Hi".
    v_fork as tₚ' "Hv'".
    i_fork as tᵢ' "Hi'".
    iSpecialize ("IH" $! [] _ [] with "Hv' Hi'").
    iApply (wp_fork with "[IH]"); [|by iFrame].
    iModIntro.
    iApply (wp_wand with "IH").
    by iIntros (?) "_".
  Qed.

  Lemma refines_cmpxchg_ref A e1 e2 e3 e1' e2' e3' e1'' e2'' e3'' :
    (REL e1 << e1' << e1'' : ref (ref A))%lrel -∗
    (REL e2 << e2' << e2'' : ref A) -∗
    (REL e3 << e3' << e3'' : ref A) -∗
    REL (CmpXchg e1 e2 e3) << (CmpXchg e1' e2' e3') << (CmpXchg e1'' e2'' e3'') : (ref A * lrel_bool)%lrel.
  Proof.
    iIntros "IH1 IH2 IH3" (????) " Hv Hi".
    rel_bind_ap e3 e3' e3'' "IH3" u u' u'' "(Hv & Hi & #IH3)".
    rel_bind_ap e2 e2' e2'' "IH2" v2 v2' v2'' "(Hv & Hi & #IH2)".
    rel_bind_ap e1 e1' e1'' "IH1" v1 v1' v1'' "(Hv & Hi & #IH1)".
    iDestruct "IH1" as (l1 l2 l3 -> -> ->) "Hinv".
    iDestruct "IH2" as (r1 r2 r3 -> -> ->) "Hr".
    iInv (authN .@ "ref" .@ (l1,l2,l3)) as (x1 x2 x3) "(>Hl1 & >Hl2 & >Hl3 & #Hx)" "Hclose".
    destruct (decide ((x1, x2, x3) = (#r1, #r2, #r3))); simplify_eq/=.
    { wp_cmpxchg_suc; v_cmpxchg_suc; i_cmpxchg_suc.
      iMod ("Hclose" with "[$Hl1 $Hl2 $Hl3 $IH3]") as "_".
      iModIntro. iFrame. iExists _, _, _, _, _, _.
      do 3 (iSplitL; [done|]).
      iFrame "Hx". eauto. }
    iDestruct "Hx" as (r1' r2' r3') "(>-> & >-> & >-> & #Hx)".
    destruct (decide (r1 = r1')); simplify_eq.
    - wp_cmpxchg_suc.
      destruct (decide ((l1, l2, l3) = (r1', r2', r3'))); simplify_eq/=.
      { iInv (authN .@ "ref" .@ (r1',r2,r3)) as (???) "(>Hr1 & >Hr2 & >Hr3 & _)".
        iExFalso. by iCombine "Hr1 Hl1" gives %[]. }
      destruct (decide ((l1, l2, l3) = (r1', r2, r3))); simplify_eq/=.
      { iInv (authN .@ "ref" .@ (r1',r2',r3')) as (???) "(>Hr1 & >Hr2 & >Hr3 & _)".
        iExFalso. by iCombine "Hr1 Hl1" gives %[]. }
      iInv (authN .@ "ref" .@ (r1',r2,r3)) as (???) "(>Hr1 & >Hr2 & >Hr3 & _)".
      iInv (authN .@ "ref" .@ (r1',r2',r3')) as (???) "(>Hr1' & >Hr2' & >Hr3' & _)".
      iExFalso. by iCombine "Hr1 Hr1'" gives %[].
    - wp_cmpxchg_fail.
      destruct (decide (r2 = r2')); simplify_eq.
      + destruct (decide ((l1, l2, l3) = (r1', r2', r3'))); simplify_eq/=.
        { iInv (authN .@ "ref" .@ (r1,r2',r3)) as (???) "(>Hr1 & >Hr2 & >Hr3 & _)".
          iExFalso. by iCombine "Hr2 Hl2" gives %[]. }
        destruct (decide ((l1, l2, l3) = (r1, r2', r3))); simplify_eq/=.
        { iInv (authN .@ "ref" .@ (r1',r2',r3')) as (???) "(>Hr1 & >Hr2 & >Hr3 & _)".
          iExFalso. by iCombine "Hr2 Hl2" gives %[]. }
        iInv (authN .@ "ref" .@ (r1,r2',r3)) as (???) "(>Hr1 & >Hr2 & >Hr3 & _)".
        iInv (authN .@ "ref" .@ (r1',r2',r3')) as (???) "(>Hr1' & >Hr2' & >Hr3' & _)".
        iExFalso. by iCombine "Hr2 Hr2'" gives %[].
      + destruct (decide (r3 = r3')); simplify_eq.
        * destruct (decide ((l1, l2, l3) = (r1', r2', r3'))); simplify_eq/=.
          { iInv (authN .@ "ref" .@ (r1,r2,r3')) as (???) "(>Hr1 & >Hr2 & >Hr3 & _)".
            iExFalso. by iCombine "Hr3 Hl3" gives %[]. }
          destruct (decide ((l1, l2, l3) = (r1, r2, r3'))); simplify_eq/=.
          { iInv (authN .@ "ref" .@ (r1',r2',r3')) as (???) "(>Hr1 & >Hr2 & >Hr3 & _)".
            iExFalso. by iCombine "Hr3 Hl3" gives %[]. }
          iInv (authN .@ "ref" .@ (r1,r2,r3')) as (???) "(>Hr1 & >Hr2 & >Hr3 & _)".
          iInv (authN .@ "ref" .@ (r1',r2',r3')) as (???) "(>Hr1' & >Hr2' & >Hr3' & _)".
          iExFalso. by iCombine "Hr3 Hr3'" gives %[].
        * v_cmpxchg_fail; i_cmpxchg_fail.
          iMod ("Hclose" with "[$Hl1 $Hl2 $Hl3]") as "_".
          { iModIntro. iExists _, _, _. eauto. }
          iFrame. iModIntro. iExists _, _, _, _, _, _.
          do 3 (iSplitL; [done|]). iSplit; [|eauto].
          iExists _, _, _; eauto.
  Qed.

End compatibility.
