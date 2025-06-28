(** Compataibility rules *)
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import list.
From auth.heap_lang Require Import proofmode_upto_bad.
From auth.rel_logic_bin Require Export model spec_rules spec_tactics.

Section compatibility.
  Context `{!authG Σ}.
  Implicit Types e : expr.

  Local Ltac value_case :=
    wp_pures; i_pures.

  Local Tactic Notation "rel_bind_ap" uconstr(e1) uconstr(e2) constr(IH) ident(v) ident(w) constr(H) :=
    wp_bind e1; i_bind e2;
    iSpecialize (IH with "[$]");
    iApply wp_wand_r;
    iSplitL IH; [iApply IH|];
    iIntros (v); iDestruct 1 as (w) H; simpl.

  Lemma refines_val e1 e2 v1 v2 (A : lrel Σ) :
    IntoVal e1 v1 →
    IntoVal e2 v2 →
    A v1 v2 -∗ REL e1 << e2 : A.
  Proof.
    iIntros (<- <-) "HA % % ?".
    wp_pures. by iFrame.
  Qed.

  Lemma refines_pair e1 e2 e1' e2' A B :
    (REL e1 << e1' : A) -∗
    (REL e2 << e2' : B) -∗
    REL (e1, e2) << (e1', e2') : A * B.
  Proof.
    iIntros "IH1 IH2" (??) "Hi".
    rel_bind_ap e2 e2' "IH2" v1 v2 "(Hi & HB)".
    rel_bind_ap e1 e1' "IH1" w1 w2 "(Hi & HA)".
    value_case.
    iModIntro. by iFrame.
  Qed.

  Lemma refines_app e1 e2 e1' e2' A B :
    (REL e1 << e1' : A → B) -∗
    (REL e2 << e2' : A) -∗
    REL App e1 e2 << App e1' e2' : B.
  Proof.
    iIntros "IH1 IH2" (??) "Hi".
    rel_bind_ap e2 e2' "IH2" v v' "(Hi & HA)".
    rel_bind_ap e1 e1' "IH1" f f' "(Hi & HAB)".
    iApply ("HAB" with "HA Hi").
  Qed.

  Lemma refines_seq A e1 e2 e1' e2' B :
    (REL e1 << e1' : A) -∗
    (REL e2 << e2' : B) -∗
    REL (e1;; e2) << (e1';; e2') : B.
  Proof.
    iIntros "IH1 IH2" (??) "Hi".
    rel_bind_ap e1 e1' "IH1" v v' "(Hi & Hvv)".
    i_pures. wp_pures.
    iApply ("IH2" with "[$]").
  Qed.

  #[local] Existing Instance ofe_ne_eta.

  Lemma refines_pack A e e' (C : A -n> lrel Σ) :
    (∃ (a : A), REL e << e' : C a) -∗
    REL e << e' : ∃; (a : A), C a.
  Proof.
    iIntros "[%a H]" (??) "Hi".
    rel_bind_ap e e' "H" v v' "($ & $)".
  Qed.

  Lemma refines_forall A e e' (C : A -n> lrel Σ) :
    □ (∀ (a : A), REL e << e' : C a) -∗
    REL (λ: <>, e)%V << (λ: <>, e')%V : ∀; (a : A), C a.
  Proof.
    iIntros "#H" (??) "Hi".
    wp_pures.
    iFrame.
    iIntros "!#" (a ?) "!#".
    iIntros (????) "Hi".
    i_pures; wp_pures.
    iApply ("H" with "[$]").
  Qed.

  Lemma refines_store e1 e2 e1' e2' A :
    (REL e1 << e1' : ref A) -∗
    (REL e2 << e2' : A) -∗
    REL e1 <- e2 << e1' <- e2' : ().
  Proof.
    iIntros "IH1 IH2" (??) "Hi".
    rel_bind_ap e2 e2' "IH2" w w' "(Hi & #HAw)".
    rel_bind_ap e1 e1' "IH1" v v' "(Hi & #Hr)".
    iDestruct "Hr" as (l l') "(-> & -> & Hr)".
    iInv (authN .@ "ref" .@ (l,l')) as (v v') "(>Hv & >Hv' & #HAv)" "Hclose".
    wp_store.
    i_store.
    iMod ("Hclose" with "[$Hv $Hv' $HAw]") as "_".
    by iFrame.
  Qed.

  Lemma refines_xchg e1 e2 e1' e2' A :
    (REL e1 << e1' : ref A) -∗
    (REL e2 << e2' : A) -∗
    REL Xchg e1 e2 << Xchg e1' e2' : A.
  Proof.
    iIntros "IH1 IH2" (??) "Hi".
    rel_bind_ap e2 e2' "IH2" w w' "(Hi & #HAw)".
    rel_bind_ap e1 e1' "IH1" v v' "(Hi & #Hr)".
    iDestruct "Hr" as (l l') "(-> & -> & Hr)".
    iInv (authN .@ "ref" .@ (l,l')) as (v v') "(>Hv & >Hv' & #HAv)" "Hclose".
    wp_xchg.
    i_xchg.
    iMod ("Hclose" with "[$Hv $Hv' $HAw]") as "_".
    by iFrame.
  Qed.

  Lemma refines_load e e' A :
    (REL e << e' : ref A) -∗
    REL !e << !e' : A.
  Proof.
    iIntros "IH" (??) "Hi".
    rel_bind_ap e e' "IH" v v' "(Hi & #Hr)".
    iDestruct "Hr" as (l l' -> ->) "#H".
    iInv (authN .@ "ref" .@ (l,l')) as (v v') "(>Hv & >Hv' & #HAv)" "Hclose".
    wp_load.
    i_load.
    iMod ("Hclose" with "[$Hv $Hv' $HAv]") as "_".
    by iFrame.
  Qed.

  Lemma refines_fork e e' :
    (REL e << e' : ()%lrel) -∗
    REL Fork e << Fork e' : ().
  Proof.
    iIntros "IH" (??) "Hi".
    i_fork as tᵢ' "Hi'".
    iSpecialize ("IH" $! [] _ with "Hi'").
    iApply (wp_fork with "[IH]"); [|by iFrame].
    iModIntro.
    iApply (wp_wand with "IH").
    by iIntros (?) "_".
  Qed.

  Lemma refines_cmpxchg_ref A e1 e2 e3 e1' e2' e3' :
    (REL e1 << e1' : ref (ref A))%lrel -∗
    (REL e2 << e2' : ref A) -∗
    (REL e3 << e3' : ref A) -∗
    REL (CmpXchg e1 e2 e3) << (CmpXchg e1' e2' e3') : (ref A * lrel_bool)%lrel.
  Proof.
    iIntros "IH1 IH2 IH3" (??) "Hi".
    rel_bind_ap e3 e3' "IH3" u u' "(Hi & #IH3)".
    rel_bind_ap e2 e2' "IH2" v2 v2' "(Hi & #IH2)".
    rel_bind_ap e1 e1' "IH1" v1 v1' "(Hi & #IH1)".
    iDestruct "IH1" as (l1 l2 -> ->) "Hinv".
    iDestruct "IH2" as (r1 r2 -> ->) "Hr".
    iInv (authN .@ "ref" .@ (l1,l2)) as (v1 v2) "(>Hl1 & >Hl2 & #Hv)" "Hclose".
    destruct (decide ((v1, v2) = (#r1, #r2))); simplify_eq/=.
    { wp_cmpxchg_suc; i_cmpxchg_suc.
      iMod ("Hclose" with "[$Hl1 $Hl2 $IH3]") as "_".
      iModIntro. iFrame. iExists _, _, _, _.
      do 3 (iSplitL; [done|]). eauto. }
    iDestruct "Hv" as (r1' r2') "(>-> & >-> & #Hv)".
    destruct (decide (r1 = r1')); simplify_eq.
    - wp_cmpxchg_suc.
      destruct (decide ((l1, l2) = (r1', r2'))); simplify_eq/=.
      { iInv (authN .@ "ref" .@ (r1',r2)) as (??) "(>Hr1 & >Hr2 & _)".
        iExFalso. by iCombine "Hr1 Hl1" gives %[]. }
      destruct (decide ((l1, l2) = (r1', r2))); simplify_eq/=.
      { iInv (authN .@ "ref" .@ (r1',r2')) as (??) "(>Hr1 & >Hr2 & _)".
        iExFalso. by iCombine "Hr1 Hl1" gives %[]. }
      iInv (authN .@ "ref" .@ (r1',r2)) as (??) "(>Hr1 & >Hr2 & _)".
      iInv (authN .@ "ref" .@ (r1',r2')) as (??) "(>Hr1' & >Hr2' & _)".
      iExFalso. by iCombine "Hr1 Hr1'" gives %[].
    - wp_cmpxchg_fail.
      destruct (decide (r2 = r2')); simplify_eq.
      + destruct (decide ((l1, l2) = (r1', r2'))); simplify_eq/=.
        { iInv (authN .@ "ref" .@ (r1,r2')) as (??) "(>Hr1 & >Hr2 & _)".
          iExFalso. by iCombine "Hr2 Hl2" gives %[]. }
        destruct (decide ((l1, l2) = (r1, r2'))); simplify_eq/=.
        { iInv (authN .@ "ref" .@ (r1',r2')) as (??) "(>Hr1 & >Hr2 & _)".
          iExFalso. by iCombine "Hr2 Hl2" gives %[]. }
        iInv (authN .@ "ref" .@ (r1,r2')) as (??) "(>Hr1 & >Hr2 & _)".
        iInv (authN .@ "ref" .@ (r1',r2')) as (??) "(>Hr1' & >Hr2' & _)".
        iExFalso. by iCombine "Hr2 Hr2'" gives %[].
      + i_cmpxchg_fail.
        iMod ("Hclose" with "[$Hl1 $Hl2]") as "_".
        { iModIntro. iExists _, _. eauto. }
        iFrame. iModIntro. iExists _, _, _, _.
        do 2 (iSplitL; [done|]). iSplit; [|eauto].
        iExists _, _; eauto.
  Qed.

End compatibility.
