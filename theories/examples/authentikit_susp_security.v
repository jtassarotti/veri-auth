From auth.prelude Require Import stdpp.
From auth.rel_logic_bin Require Export model spec_rules spec_tactics interp lib adequacy fundamental.
From auth.heap_lang Require Import gen_weakestpre.
From auth.heap_lang.lib Require Import list serialization.
From auth.examples Require Export authentikit_susp authenticatable_base_susp.
From iris.base_logic.lib Require Export invariants.

Section auth_serialization.
  Context `{invGS_gen hlc Σ} `{g : !GenWp Σ} (N : namespace).

  Implicit Types c : gwp_type g.

  Definition auth_valid_val (v : val) : iProp Σ :=
    (∃ (h : string), ⌜v = InjLV #h⌝) ∨
      (∃ (susp : loc), ⌜v = InjRV #susp⌝ ∗
        ((∃ (h : string), gwp_pointsto g susp DfracDiscarded (InjRV #h)) ∨
          (∃ (pid : nat), gwp_pointsto g susp (DfracOwn 1) (InjLV #pid)))).

  Definition auth_is_ser (v : val) (s : string) : iProp Σ :=
    (∃ (h : string), ⌜v = InjLV #h⌝ ∗ s_is_ser (g:=g) auth_scheme (SOMEV #h) s) ∨
       (∃ (susp : loc), ⌜v = InjRV #susp⌝ ∗
         ((∃ (h : string), gwp_pointsto g susp DfracDiscarded (InjRV #h) ∗ s_is_ser (g:=g) auth_scheme (SOMEV #h) s) ∨
            (∃ (pid : nat), gwp_pointsto g susp (DfracOwn 1) (InjLV #pid) ∗ s_is_ser (g:=g) auth_scheme NONEV s))).

  Lemma auth_is_ser_inj v s1 s2 :
    auth_is_ser v s1 -∗ auth_is_ser v s2 -∗ ⌜s1 = s2⌝.
  Proof.
    iIntros "[(% & % & Hs1)|(% & % & [(% & Hl1 & Hs1)|(% & Hl1 & %)])] [(% & % & Hs2)|(% & % & [(% & Hl2 & Hs2)|(% & Hl2 & %)])]"; simplify_eq.
    - iEval (simpl) in "Hs1 Hs2".
      by iApply (option_is_ser_inj with "[Hs1] [Hs2]").
    - iEval (simpl) in "Hs1 Hs2".
      iPoseProof (gwp_pointsto_agree with "[Hl1] [Hl2]") as "%"; [done|done|]. simplify_eq.
      by iApply (option_is_ser_inj with "[Hs1] [Hs2]").
    - iPoseProof (gwp_pointsto_agree with "[Hl1] [Hl2]") as "%"; [done|done|]. simplify_eq.
    - iPoseProof (gwp_pointsto_agree with "[Hl1] [Hl2]") as "%"; [done|done|]. simplify_eq.
    - by iPoseProof (gwp_pointsto_valid_2 with "Hl1 Hl2") as "%".
  Qed.

  Lemma auth_is_ser_valid v s : auth_is_ser v s ⊢ auth_valid_val v.
  Proof.
    iIntros "[(% & % & Hs1)|(% & % & [(% & Hl1 & Hs1)|(% & Hl1 & %)])]".
    - iLeft. iFrame "%".
    - iRight. iFrame "%".
      iLeft. iFrame.
    - iRight. iFrame "%".
      iRight. iFrame.
  Qed.

  Lemma auth_ser_spec E v c :
    G{{{ ▷?(gwp_laters g) auth_valid_val v }}}
      auth_ser_v v @ c; E
    {{{ (w: val), RET w; (∃ (s: string), ⌜w=#s⌝ ∗ auth_is_ser v s) }}} ? gwp_laters g.
  Proof.
    iIntros (?) "H1 H2".
    rewrite /auth_ser_v. gwp_pures.
    iDestruct "H1" as "[(% & ->)|(% & -> & [(% & Hl1)|(% & Hl1)])]".
    - gwp_pures.
      gwp_apply s_ser_spec.
      { iRight. iExists _. iSplit; [done|].
        iExists _. done. }
      iIntros (s Hser).
      destruct Hser as [(? & Hser)|Hser]; [done|].
      destruct Hser as (? & ? & (H1 & ->) & (s' & -> & ->)).
      inversion H1. subst.
      iApply "H2".
      iExists _. iSplit; [done|].
      rewrite /auth_is_ser /auth_scheme. iLeft.
      iExists _. iSplit; [done|].
      simpl. rewrite /option_is_ser.
      iRight.
      iExists _, _.
      eauto.
    - gwp_pures. gwp_load. gwp_pures.
      gwp_apply (s_ser_spec).
      { iRight. eauto. }
      iIntros (?) "Hser".
      iApply "H2". 
      iExists _. iSplit; [done|].
      rewrite /auth_is_ser //.
      iRight. iExists _. iSplit; [done|].
      iLeft. iFrame.
    - gwp_pures. gwp_load. gwp_pures.
      gwp_apply (s_ser_spec).
      { iLeft. eauto. }
      iIntros (?) "Hser".
      iApply "H2". 
      iExists _. iSplit; [done|].
      rewrite /auth_is_ser //.
      iRight. iExists _. iSplit; [done|].
      iRight. iFrame.
  Qed.

End auth_serialization.

Program Definition auth_serialization : serialization :=
  {| s_valid_val := λ _ Σ, @auth_valid_val _ Σ;
    s_serializer := auth_ser_v;
    s_is_ser := λ _ _ Σ, @auth_is_ser _ _ Σ;
    s_is_ser_inj := λ _ Σ, @auth_is_ser_inj _ Σ;
    s_is_ser_valid := λ _ Σ, @auth_is_ser_valid _ Σ;
    s_ser_spec := @auth_ser_spec; |}.

Section auth_deserialization.
  Context `(pid : nat).
  Context `{invGS_gen hlc Σ} `{g : !GenWp Σ} (N : namespace).

  Implicit Types c : gwp_type g.

  Definition auth_is_ser' (v : val) (s : string) : iProp Σ :=
    (∃ (h : string), ⌜v = InjLV #h⌝ ∗ string_is_ser #h s) ∨
       (∃ (susp : loc), ⌜v = InjRV #susp⌝ ∗
         ((∃ (h : string), gwp_pointsto g susp (DfracOwn (1/2)) (InjRV #h) ∗ string_is_ser #h s) ∨
            (∃ (pid : nat), gwp_pointsto g susp (DfracOwn (1/2)) (InjLV #pid) ∗ ⌜s = ""⌝))).

  Lemma auth_deser_sound E s c:
    G{{{ True }}}
      auth_deser_v #pid #s @ c; E
    {{{ o, RET $o; if o is Some v then auth_is_ser (g:=g) v s else ⌜True⌝ }}} ? gwp_laters g.
  Proof.
    iIntros (Φ _) "HΦ".
    rewrite /auth_deser_v.
    gwp_pures.
    gwp_apply (s_deser_sound); [done|].
    iIntros ([a|]) "Hser"; gwp_pures; [|by iApply ("HΦ" $! None)].
    iDestruct "Hser" as "[(% & %)|(% & % & (% & %) & (% & % & %))]";
      simplify_eq; gwp_pures; last first.
    { iModIntro. iApply ("HΦ" $! (Some _)).
      iLeft. iExists _. iSplit; [done|].
      iRight. iExists _, _. iSplit; eauto. }
    gwp_alloc susp. gwp_pures.
    iModIntro. iApply ("HΦ" $! (Some _)).
    iRight. iExists _. iSplit; [done|].
    iRight. iFrame.
    iLeft. done.
  Qed.

  Lemma auth_deser_complete E v s c:
    G{{{ auth_is_ser (g := g) v s }}}
      auth_deser_v #pid #s @ c; E
    {{{ RET (SOMEV v); True }}} ? gwp_laters g.
  Proof.
    iIntros (?) "Hser H".
    iDestruct "Hser" as "[(% & % & Hs1)|(% & % & [(% & Hl1 & Hs1)|(% & Hl1 & %)])]"; 
      rewrite /auth_deser_v; gwp_pures.
    Focus 3.
    destruct H1 as [(? & ?)|(? & ? & (? & ?) & ? & ? & ?)]; [|done].
    simplify_eq. rewrite /s_deserializer. 
    gwp_pures. rewrite /option_deser'. gwp_pures.
    
End auth_deserialization.

Program Definition auth_deserialization : deserialization :=
  {| s_deserializer := auth_deser_v;
    s_deser_sound := ;
    s_deser_complete := ;
  |}.
  
  Definition equivalent (t : evi_type) (v1 : val) (v2 : val) : val :=
    match t with
    | tprod t1 t2 => 
    | tsum t1 t2 =>
        (match: val with
           InjLV "lv" => InjLV (make_serializable "lv")
         | InjRV "rv" => InjRV (make_serializable "rv"))%I
    | tstring => v
    | tint => v
    | tauth =>
        (
        
  Fixpoint s_is_ser' (t : evi_type) (v : val) (s : string) : iProp Σ :=
    match t with
    | tprod t1 t2 => prod_is_ser' v s (s_is_ser' t1) (s_is_ser' t2)
    | tsum t1 t2 => sum_is_ser' v s (s_is_ser' t1) (s_is_ser' t2)
    | tstring => string_is_ser v s
    | tint => int_is_ser v s
    | tauth =>
        (∃ (h : string), ⌜v = InjLV #h⌝ ∗ s_is_ser (g := gwp_upto_bad) auth_serialization_scheme (InjRV #h) s) ∨
          (∃ (susp : loc), ⌜v = InjRV #susp⌝ ∗
            ((∃ (h : string), susp ↦ (InjRV #h) ∗ s_is_ser (g := gwp_upto_bad) auth_serialization_scheme (InjRV #h) s) ∨
               (∃ (v : val), susp ↦ InjLV v)))
    end.

  Inductive evi_type : Type :=
  | tprod (t1 t2 : evi_type)
  | tsum (t1 t2 : evi_type)
  | tstring
  | tint
  | tauth.

  #[global] Instance : Inhabited evi_type.
  Proof. constructor. apply tstring. Qed.

  Fixpoint evi_type_ser (t : evi_type) : serialization_scheme :=
    match t with
    | tprod t1 t2 => prod_serialization_scheme (evi_type_ser t1) (evi_type_ser t2)
    | tsum t1 t2 => sum_serialization_scheme (evi_type_ser t1) (evi_type_ser t2)
    | tstring => string_serialization_scheme
    | tint => int_serialization_scheme
    | tauth => auth_serialization_scheme
    end.
  
  Fixpoint evi_type_count (t : evi_type) : expr :=
    match t with
    | tprod t1 t2 => prod_count (evi_type_count t1) (evi_type_count t2)
    | tsum t1 t2 => sum_count (evi_type_count t1) (evi_type_count t2)
    | tstring => string_count
    | tint => int_count
    | tauth => auth_count
    end.

  Fixpoint count_is_correct (t : evi_type) (v : val) (c : val) : iProp Σ :=
    match t with
    | tprod t1 t2 =>
        ∃ (c1 c2 : nat) (v1 v2 : val),
          count_is_correct t1 v1 #c1 ∗ count_is_correct t2 v2 #c2 ∗ ⌜#(c1 + c2) = c⌝
    | tsum t1 t2 =>
        (∃ (v1 : val), count_is_correct t1 v1 c) ∨ (∃ (v2 : val), count_is_correct t2 v2 c)
    | tstring | tint => ⌜c = #0⌝                                                 
    | tauth =>
        (∃ (l : val), ⌜v = InjLV l ∧ c = #1⌝) ∨ (∃ (r : val), ⌜v = InjRV r ∧ c = #0⌝)
    end.
                                                 
  Definition ser_spec (ser : val) (t : evi_type) (A : lrel Σ) : iProp Σ :=
    ∀ (v1 v2 : val),
      {{{ ▷ A v1 v2 }}} ser v1 {{{ s, RET #s; s_is_ser (g := gwp_upto_bad) (evi_type_ser t) v1 s }}}.

  Definition deser_spec (deser : val) (t : evi_type) : iProp Σ :=
    ∀ (pid : nat) (s : string),
      {{{ True }}}
        deser #pid #s
        {{{ o, RET $o; if o is Some v then s_is_ser (g := gwp_upto_bad) (evi_type_ser t) v s else True }}}.

  Definition count_spec (count : val) (t : evi_type) : iProp Σ :=
    ∀ (v : val),
      {{{ True }}}
        count v
        {{{ o, RET $o; if o is Some c then count_is_correct t v c else True }}}.

  Definition lrel_evidence' (A : lrel Σ) : lrel Σ :=
    LRel (λ v1 v2,
        ∃ (t : evi_type) (ser deser count : val),
          ⌜v1 = (ser, deser, count)%V⌝ ∗ ser_spec ser t A ∗ deser_spec deser t ∗ count_spec count t)%I.

  Program Definition lrel_evidence : kindO Σ (⋆ ⇒ ⋆)%kind := λne A, lrel_evidence' A.
  Next Obligation.
    intros ??????.
    rewrite /lrel_car/= /ser_spec.
    solve_proper.
  Qed.
  
End authenticatable.

Section proof.
  Context `{!authG Σ}.

  Lemma refines_Auth_pair Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆; ⋆, var2 var1 → var2 var0 → var2 (var1 * var0) ⟧
      (ext Δ lrel_evidence) v_Auth_pair i_Auth_pair.
  Proof.
    interp_unfold.
    iIntros (A ??) "!# _".
    iIntros (??) "Hi".
    rewrite /v_Auth_pair /i_Auth_pair.
    i_pures; wp_pures.
    iModIntro. iFrame.
    iIntros (B ??) "!# _".
    iIntros (??) "Hi".
    i_pures; wp_pures.
    iModIntro. iFrame.
    iIntros (??) "!# HA".
    interp_unfold! in "HA".
    iDestruct "HA" as (tA serA deserA countA ->) "(#HserA & #HdeserA & #HcountA)". clear.
    iIntros (??) "Hi".
    i_pures; wp_pures.
    iModIntro. iFrame.
    iIntros (??) "!# HB".
    interp_unfold! in "HB".
    iDestruct "HB" as (tB serB deserB countB ->) "(#HserB & #HdeserB & #HcountB)". clear.
    iIntros (??) "Hi".
    i_pures; wp_pures.
    rewrite /prod_scheme /prod_ser /prod_deser /prod_count.
    wp_pures. iFrame. iModIntro.
    interp_unfold!.
    iExists (tprod tA tB), _, _, _.
    iSplit; [done|]. clear. iSplit; [|iSplit].
    - iIntros (v1 v2 ?) "!# Hp H".
      iDestruct "Hp" as (w1 w2 u1 u2) "(>-> & >-> & #HA & #HB)".
      wp_apply (prod_ser'_spec (evi_type_ser tA) (evi_type_ser tB)
                  (λ v1, A v1 w2)%I (λ v1, B v1 u2)%I) => /=; [done| | | |done]. 
      { iIntros (?) "!# _ H". by wp_apply ("HserA" with "HA"). }
      { iIntros (?) "!# _ H". by wp_apply ("HserB" with "HB"). }
      iExists _, _.  eauto.
    - iIntros (pid s Ψ) "!# _ HΨ". by wp_apply prod_deser'_sound.
  Qed.
  
  
  

End proof.
