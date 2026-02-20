From auth.prelude Require Import stdpp.
From auth.rel_logic_bin Require Export model spec_rules spec_tactics interp lib adequacy fundamental.
From auth.heap_lang Require Import gen_weakestpre.
From auth.heap_lang.lib Require Import list serialization.
From auth.examples Require Export authentikit_susp authenticatable_base_susp.
From iris.base_logic.lib Require Export invariants na_invariants.
  
(* Section auth_serialization.
  Context `{invGS_gen hlc Σ} `{g : !GenWp Σ} (N : namespace).

  Implicit Types c : gwp_type g.

  Definition authSerBaseN : namespace := N .@ "auth_ser".
  Definition authSerN (v : val) : namespace := N .@ v.

  Definition auth_valid_val (v : val) : iProp Σ :=
    ((∃ (h : string), ⌜v = InjLV #h⌝) ∨
      (∃ (susp : loc), ⌜v = InjRV #susp⌝ ∗
        ((∃ (h : string), gwp_pointsto g susp DfracDiscarded (InjRV #h)) ∨
          (∃ (pid : nat), gwp_pointsto g susp (DfracOwn 1) (InjLV #pid))))).

  Definition auth_is_ser (v : val) (s : string) : iProp Σ :=
    inv (authSerN v) ((∃ (h : string), ⌜v = InjLV #h⌝ ∗ s_is_ser (g:=g) auth_scheme (SOMEV #h) s) ∨
       (∃ (susp : loc), ⌜v = InjRV #susp⌝ ∗
         ((∃ (h : string), gwp_pointsto g susp DfracDiscarded (InjRV #h) ∗ s_is_ser (g:=g) auth_scheme (SOMEV #h) s) ∨
            (∃ (pid : nat), gwp_pointsto g susp (DfracOwn 1) (InjLV #pid) ∗ s_is_ser (g:=g) auth_scheme NONEV s)))).

  Definition auth_is_ser' (s : string) : iProp Σ :=
    ∃ (h : string), s_is_ser (g:=g) auth_scheme (SOMEV #h) s ∨
       s_is_ser (g:=g) auth_scheme NONEV s.

  Instance gwp_pointsto_persistent l v :
    Persistent (gwp_pointsto g l DfracDiscarded v).
  Proof. Admitted.

  Instance gwp_pointsto_timeless l v :
    Timeless (gwp_pointsto g l DfracDiscarded v).
  Proof. Admitted.
  
  Lemma auth_is_ser_inj v s1 s2 :
    auth_is_ser v s1 -∗ auth_is_ser v s2 ={⊤}=∗ ⌜s1 = s2⌝.
  Proof.
    iIntros "#Hs1 #Hs2". 
    iInv "Hs1" as "[>(%&%&#H1)|(%&>%&[(%&>#H1&>#Hser1)|(%&H1&>#Hser1)])]"; iModIntro.
    - iSplitL.
      { iLeft. iFrame "% #". }
      iInv "Hs2" as "[>(%&%&#H2)|(%&>%&[(%&H2&>#Hser2)|H2])]"; iModIntro; simplify_eq.
      iSplitL.
      { iLeft. by iFrame "# %". }
      simplify_eq. iApply s_is_ser_inj; by iFrame "#".
    - iSplitL.
      { iRight. iExists _. iFrame "%". iLeft. by iFrame "# ∗". }
      iInv "Hs2" as "[>(%&%&#H2)|(%&>%&[(%&>#H2&>#Hser2)|(%&H2&>#Hser2)])]" "Hclose";
        simplify_eq; last first.
      + iPoseProof (gwp_pointsto_agree with "H1 H2") as "H". simplify_eq.
        iMod "H" as "%". simplify_eq.
      + iPoseProof (gwp_pointsto_agree with "H1 H2") as "%". simplify_eq.
        iPoseProof (s_is_ser_inj with "Hser1 Hser2") as "%". simplify_eq.
        iMod ("Hclose" with "[]") as "_".
        { iRight. iExists _. iSplit; [done|]. iLeft. iFrame "#". }
        done.
    - iSplitL.
      { iRight. iExists _. iSplit; [done|]. iRight. by iFrame. }
      iInv "Hs2" as "[>(%&%&#H2)|(%&>%&[(%&>#H2&>#Hser2)|(%&H2&>#Hser2)])]" "Hclose";
        simplify_eq.
      + iPoseProof (gwp_pointsto_agree with "H1 H2") as "H". simplify_eq.
        iMod "H" as "%". simplify_eq.
      
    
    iModIntro. iFrame. iIntros "H2".
    iInv "Hs1" as "[(% & % & Hs1)|(% & % & [(% & Hl1 & Hs1)|(% & Hl1 & %)])]".
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
  Proof. Admitted.
(*    iIntros "[(% & % & Hs1)|(% & % & [(% & Hl1 & Hs1)|(% & Hl1 & %)])]".
    - iLeft. iFrame "%".
    - iRight. iFrame "%".
      iLeft. iFrame.
    - iRight. iFrame "%".
      iRight. iFrame.
  Qed. *)

  Lemma auth_is_ser_eq v s :
    auth_is_ser v s -∗ auth_is_ser' s.
  Proof. Admitted.
(*    iIntros "[(%&->&#Hser)|(%&->&[(%&Ho&#Hser)|(%&Ho&#Hser)])]"; rewrite /auth_is_ser';
      iPoseProof (s_is_ser_eq with "Hser") as "Hser'".
    - iLeft. eauto.
    - iLeft. eauto.
    - iRight. eauto.
  Qed. *)
      
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
    s_is_ser' := λ _ _ Σ, @auth_is_ser' _ _ Σ;
    s_is_ser_inj := λ _ Σ, @auth_is_ser_inj _ Σ;
    s_is_ser_valid := λ _ Σ, @auth_is_ser_valid _ Σ;
    s_is_ser_eq := @auth_is_ser_eq;
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
  |}. *)

Section authenticatable.
  Context `{!heapGS_gen hlc Σ, !seqG Σ} (N : namespace).

  Definition authSerN (v: val) : namespace := N .@ "auth_ser" .@ v.
  Definition authValidN (v: val) : namespace := N .@ "auth_valid" .@ v.
  Definition authCountN (v: val) : namespace := N .@ "auth_count" .@ v.
  
  Inductive evi_type : Type :=
  | tprod (t1 t2 : evi_type)
  | tsum (t1 t2 : evi_type)
  | tstring
  | tint
  | tauth.

  Definition auth_is_ser_1 (v : val) (s : string) : iProp Σ :=
    ∃ (h : string), ⌜v = InjLV #h⌝ ∗ s_is_ser (g:=gwp_upto_bad) auth_scheme (SOMEV #h) s.

  Definition auth_is_ser_2 (v : val) (s : string) : iProp Σ :=
    ∃ (susp : loc) (h : string),
      ⌜v = InjRV #susp⌝ ∗ susp ↦□ InjRV #h ∗ s_is_ser (g:=gwp_upto_bad) auth_scheme (SOMEV #h) s.

  Definition auth_is_ser_3 (v : val) (s : string) : iProp Σ :=
    ∃ (susp : loc) (pid: nat), ⌜v = InjRV #susp⌝ ∗ susp ↦ (InjLV #pid) ∗ s_is_ser (g:=gwp_upto_bad) auth_scheme NONEV s.

  (* Definition auth_is_ser (v : val) (s : string) : iProp Σ :=
    auth_is_ser_1 v s ∨ auth_is_ser_2 v s. *)

  Definition valid_auth_inv (susp : loc) : iProp Σ :=
    ((∃ (h : string), susp ↦□ InjRV #h) ∨
       (∃ (pid : nat), susp ↦ (InjLV #pid))).

  Definition auth_valid_val (v1 : val) : iProp Σ :=
    ∃ v, ⌜v1 = SOMEV v⌝ ∧
           ((∃ (h : string), ⌜v = InjLV #h⌝) ∨
              (∃ (susp : loc),
                  ⌜v = InjRV #susp⌝ ∗ seq_inv (authValidN #susp) (valid_auth_inv susp))).

  Definition auth_deser_valid_val (v1 : val) : iProp Σ :=
    ∃ v, ⌜v1 = SOMEV v⌝ ∧
           ((∃ (h : string), ⌜v = InjLV #h⌝) ∨
              (∃ (susp : loc),
                  ⌜v = InjRV #susp⌝ ∗ (∃ (pid : nat), susp ↦ (InjLV #pid)))).
             
  
  (* Fixpoint s_is_ser_ser (t : evi_type) (v : val) (s : string) : iProp Σ :=
    match t with
    | tprod t1 t2 => prod_is_ser' v s (s_is_ser_ser t1) (s_is_ser_ser t2)
    | tsum t1 t2 => sum_is_ser' v s (s_is_ser_ser t1) (s_is_ser_ser t2)
    | toption t1 => option_is_ser' v s (s_is_ser_ser t1)
    | tstring => string_is_ser v s
    | tint => int_is_ser v s
    | tauth => auth_is_ser v s
    end. *)

  Fixpoint s_is_ser_deser (t : evi_type) (v : val) (s : string) : iProp Σ :=
    match t with
    | tprod t1 t2 => prod_is_ser' v s (s_is_ser_deser t1) (s_is_ser_deser t2)
    | tsum t1 t2 => sum_is_ser' v s (s_is_ser_deser t1) (s_is_ser_deser t2)
    | tstring => string_is_ser v s
    | tint => int_is_ser v s
    | tauth => ∃ v1, ⌜v = SOMEV v1⌝ ∗ (auth_is_ser_1 v1 s ∨ auth_is_ser_3 v1 s)
    end.

  Fixpoint s_is_ser'' (t : evi_type) (v : val) (s : string) : iProp Σ :=
    match t with
    | tprod t1 t2 => prod_is_ser' v s (s_is_ser'' t1) (s_is_ser'' t2)
    | tsum t1 t2 => sum_is_ser' v s (s_is_ser'' t1) (s_is_ser'' t2)
    | tstring => string_is_ser v s
    | tint => int_is_ser v s
    | tauth => ∃ v1, ⌜v = SOMEV v1⌝ ∗ (auth_is_ser_1 v1 s ∨ auth_is_ser_2 v1 s)
    end.

  Fixpoint s_valid_val (t: evi_type) (v: val) : iProp Σ :=
    match t with
    | tprod t1 t2 => prod_valid_val' v (s_valid_val t1) (s_valid_val t2)
    | tsum t1 t2 => sum_valid_val' v (s_valid_val t1) (s_valid_val t2)
    | tstring => string_valid_val v
    | tint => int_valid_val v
    | tauth => auth_valid_val v
    end.

  Fixpoint s_deser_valid_val (t : evi_type) (v : val) : iProp Σ :=
    match t with
    | tprod t1 t2 => prod_valid_val' v (s_deser_valid_val t1) (s_deser_valid_val t2)
    | tsum t1 t2 => sum_valid_val' v (s_deser_valid_val t1) (s_deser_valid_val t2)
    | tstring => string_valid_val v
    | tint => int_valid_val v
    | tauth => auth_deser_valid_val v
    end.

  #[global] Instance s_valid_val_persistent t v: Persistent (s_valid_val t v).
  Proof. revert v; induction t => v; simpl; apply _. Qed.

  Fixpoint val_eq (t : evi_type) (v1 v2 : val) : iProp Σ :=
    match t with
    | tprod t1 t2 =>
        ∃ v11 v12 v21 v22,
          ⌜v1 = (v11, v12)%V ∧ v2 = (v21, v22)%V⌝ ∗ val_eq t1 v11 v21 ∗ val_eq t2 v12 v22
    | tsum t1 t2 => 
        ∃ v1' v2',
          (⌜v1 = InjLV v1' ∧ v2 = InjLV v2'⌝ ∗ val_eq t1 v1' v2') ∨
            (⌜v1 = InjRV v1' ∧ v2 = InjRV v2'⌝ ∗ val_eq t2 v1' v2')
    | tstring => ∃ (s: string), ⌜v1 = #s ∧ v2 = #s⌝
    | tint => ∃ (i: nat), ⌜v1 = #i ∧ v2 = #i⌝
    | tauth =>
        ⌜v1 = NONEV ∧ v2 = NONEV⌝ ∨
          (∃ (h: string), (⌜v1 = SOMEV (InjLV #h)⌝ ∨
                   (∃ (susp : loc), ⌜v1 = SOMEV (InjRV #susp)⌝ ∗ susp ↦□ InjRV #h)) ∧
                  (⌜v2 = SOMEV (InjLV #h)⌝ ∨
                     (∃ (susp : loc), ⌜v2 = SOMEV (InjRV #susp)⌝ ∗ susp ↦□ InjRV #h)))
    end.
        
  Lemma evi_type_ser''_inj (t1 t2 : evi_type) v1 v2 s :
    (s_is_ser'' t1 v1 s ∨ s_is_ser_deser t1 v1 s) -∗ s_is_ser'' t2 v2 s -∗ val_eq t1 v1 v2.
  Proof. 
    iInduction t1 as [| | | |] forall (t2 v1 v2 s).
    - iIntros "Ht1 Ht2".
      iDestruct "Ht1" as "[Ht1|Ht1]".
      + iDestruct "Ht1" as (?????) "(Ht11 & Ht12)".
        destruct H as [-> ->].
        destruct t2 => /=; simplify_eq.
        * iDestruct "Ht2" as (?????) "(Ht21 & Ht22)".
          destruct H as [-> H]. simplify_eq.
          iExists _, _, _, _. iSplit; [eauto|].
          iPoseProof ("IHt1_2" with "[Ht12] Ht22") as "Ht32".
          { by iLeft. }
          iPoseProof ("IHt1_1" with "[Ht11] Ht21") as "Ht31".
          { by iLeft. }
          iFrame.
        * iDestruct "Ht2" as (??) "[(Ht2&%)|(Ht2&%)]";
            destruct H; simplify_eq.
          { exfalso. by eapply prod_ser_inl_ser_neq. }
          { exfalso. by eapply prod_ser_inr_ser_neq. }
        * iDestruct "Ht2" as (?) "(%&%)".
          iExFalso. by eapply prod_ser_string_ser_neq in H0.
        * iDestruct "Ht2" as (?) "(%&%)".
          iExFalso. by eapply prod_ser_int_ser_neq in H0.
        * admit.
      + iDestruct "Ht1" as (?????) "(Ht11 & Ht12)".
        destruct H as [-> ->].
        destruct t2 => /=; simplify_eq.
        * iDestruct "Ht2" as (?????) "(Ht21 & Ht22)".
          destruct H as [-> H]. simplify_eq.
          iExists _, _, _, _. iSplit; [eauto|].
          iPoseProof ("IHt1_2" with "[Ht12] Ht22") as "Ht32".
          { by iRight. }
          iPoseProof ("IHt1_1" with "[Ht11] Ht21") as "Ht31".
          { by iRight. }
          iFrame.
        * iDestruct "Ht2" as (??) "[(Ht2&%)|(Ht2&%)]";
            destruct H; simplify_eq.
          { exfalso. by eapply prod_ser_inl_ser_neq. }
          { exfalso. by eapply prod_ser_inr_ser_neq. }
        * iDestruct "Ht2" as (?) "(%&%)".
          iExFalso. by eapply prod_ser_string_ser_neq in H0.
        * iDestruct "Ht2" as (?) "(%&%)".
          iExFalso. by eapply prod_ser_int_ser_neq in H0.
        * admit.
    - admit.
    - admit.
    - admit.
    - iIntros "Ht1 Ht2".
      iDestruct "Ht1" as "[Ht1|Ht1]".
      + iDestruct "Ht1" as (?->) "[Ht1|Ht1]".
        * iDestruct "Ht1" as (?) "(-> & Ht1)".
          destruct t2 => /=; simplify_eq.
          -- iDestruct "Ht1" as "[(% & ->)|(% & % & (% & %) & Hser)]"; [done|].
             simplify_eq.
             iDestruct "Ht2" as (?????) "(Ht21 & Ht22)".
             destruct H as [-> H].
             simplify_eq.
             exfalso. by eapply prod_ser_some_ser_neq.
          -- iDestruct "Ht1" as "[(% & ->)|(% & % & (% & %) & Hser)]"; [done|].
             simplify_eq.
             iDestruct "Ht2" as (??) "[(Ht2&%)|(Ht2&%)]";
               destruct H; simplify_eq.
          -- iDestruct "Ht1" as "[(% & ->)|(% & % & (% & %) & (% & -> & ->))]"; [done|].
             simplify_eq.
             iDestruct "Ht2" as (?) "(%&%)". simplify_eq.
          -- iDestruct "Ht1" as "[(% & ->)|(% & % & (% & %) & (% & -> & ->))]"; [done|].
             simplify_eq.
             iDestruct "Ht2" as (?) "(%&%)". simplify_eq.
          -- iDestruct "Ht1" as "[(% & ->)|(% & % & (% & %) & (% & -> & ->))]"; [done|].
             simplify_eq.
             iDestruct "Ht2" as (?->) "[(% & -> & Ht2)|(% & % & -> & #Hloc & Ht2)]"; iFrame.
             { iDestruct "Ht2" as "[(% & %)|(% & % & (% & %) & (% & -> & ->))]"; [done|].
               simplify_eq. iRight. iExists _. iSplit; iLeft; eauto. }            
             iRight. iExists _. iSplit.
             { iLeft. eauto. }
             iDestruct "Ht2" as "[(% & %)|(% & % & (% & %) & (% & % & %))]"; simplify_eq.
             iRight. iExists _. eauto.
        * iDestruct "Ht1" as (??->) "(Hloc & Ht1)".
          destruct t2 => /=; simplify_eq.
          -- iDestruct "Ht1" as "[(% & ->)|(% & % & (% & %) & Hser)]"; [done|].
             simplify_eq.
             iDestruct "Ht2" as (?????) "(Ht21 & Ht22)".
             destruct H as [-> H].
             simplify_eq.
             exfalso. by eapply prod_ser_some_ser_neq.
          -- iDestruct "Ht1" as "[(% & ->)|(% & % & (% & %) & Hser)]"; [done|].
             simplify_eq.
             iDestruct "Ht2" as (??) "[(Ht2&%)|(Ht2&%)]";
               destruct H; simplify_eq.
          -- iDestruct "Ht1" as "[(% & ->)|(% & % & (% & %) & (% & -> & ->))]"; [done|].
             simplify_eq.
             iDestruct "Ht2" as (?) "(%&%)". simplify_eq.
          -- iDestruct "Ht1" as "[(% & ->)|(% & % & (% & %) & (% & -> & ->))]"; [done|].
             simplify_eq.
             iDestruct "Ht2" as (?) "(%&%)". simplify_eq.
          -- iDestruct "Ht1" as "[(% & ->)|(% & % & (% & %) & (% & -> & ->))]"; [done|].
             simplify_eq.
             iDestruct "Ht2" as (?->) "[(% & -> & Ht2)|(% & % & -> & #Hloc1 & Ht2)]"; iFrame.
             { iDestruct "Ht2" as "[(% & %)|(% & % & (% & %) & (% & -> & ->))]"; [done|].
               simplify_eq. iRight. iExists _. iSplit; [iRight|iLeft]; eauto. }
             iRight. iExists _. iSplit.
             { iRight. eauto. }
             iDestruct "Ht2" as "[(% & %)|(% & % & (% & %) & (% & % & %))]"; simplify_eq.
             iRight. iExists _. eauto.
      + iDestruct "Ht1" as (?->) "[Ht1|Ht1]".
        * iDestruct "Ht1" as (?) "(-> & Ht1)".
          destruct t2 => /=; simplify_eq.
          -- iDestruct "Ht1" as "[(% & ->)|(% & % & (% & %) & Hser)]"; [done|].
             simplify_eq.
             iDestruct "Ht2" as (?????) "(Ht21 & Ht22)".
             destruct H as [-> H].
             simplify_eq.
             exfalso. by eapply prod_ser_some_ser_neq.
          -- iDestruct "Ht1" as "[(% & ->)|(% & % & (% & %) & Hser)]"; [done|].
             simplify_eq.
             iDestruct "Ht2" as (??) "[(Ht2&%)|(Ht2&%)]";
               destruct H; simplify_eq.
          -- iDestruct "Ht1" as "[(% & ->)|(% & % & (% & %) & (% & -> & ->))]"; [done|].
             simplify_eq.
             iDestruct "Ht2" as (?) "(%&%)". simplify_eq.
          -- iDestruct "Ht1" as "[(% & ->)|(% & % & (% & %) & (% & -> & ->))]"; [done|].
             simplify_eq.
             iDestruct "Ht2" as (?) "(%&%)". simplify_eq.
          -- iDestruct "Ht1" as "[(% & ->)|(% & % & (% & %) & (% & -> & ->))]"; [done|].
             simplify_eq.
             iDestruct "Ht2" as (?->) "[(% & -> & Ht2)|(% & % & -> & #Hloc & Ht2)]"; iFrame.
             { iDestruct "Ht2" as "[(% & %)|(% & % & (% & %) & (% & -> & ->))]"; [done|].
               simplify_eq. iRight. iExists _. iSplit; iLeft; eauto. }            
             iRight. iExists _. iSplit.
             { iLeft. eauto. }
             iDestruct "Ht2" as "[(% & %)|(% & % & (% & %) & (% & % & %))]"; simplify_eq.
             iRight. iExists _. eauto.
        * iDestruct "Ht1" as (??->) "(Hloc & Ht1)".
          destruct t2 => /=; simplify_eq.
          -- iDestruct "Ht1" as "[(% & ->)|(% & % & (% & %) & Hser)]"; [|done].
             simplify_eq.
             iDestruct "Ht2" as (?????) "(Ht21 & Ht22)".
             destruct H as [-> H].
             exfalso. by eapply prod_ser_none_ser_neq.
          -- iDestruct "Ht1" as "[(% & ->)|(% & % & (% & %) & Hser)]"; [|done].
             simplify_eq.
             iDestruct "Ht2" as (??) "[(Ht2&%)|(Ht2&%)]";
               destruct H; simplify_eq.
          -- iDestruct "Ht1" as "[(% & ->)|(% & % & (% & %) & (% & -> & ->))]"; [|done].
             simplify_eq.
             iDestruct "Ht2" as (?) "(%&%)". simplify_eq.
          -- iDestruct "Ht1" as "[(% & ->)|(% & % & (% & %) & (% & -> & ->))]"; [|done].
             simplify_eq.
             iDestruct "Ht2" as (?) "(%&%)". simplify_eq.
          -- iDestruct "Ht1" as "[(% & ->)|(% & % & (% & %) & (% & -> & ->))]"; [|done].
             simplify_eq.
             iDestruct "Ht2" as (?->) "[(% & -> & Ht2)|(% & % & -> & #Hloc1 & Ht2)]"; iFrame;
               iDestruct "Ht2" as "[(% & %)|(% & % & (% & %) & (% & -> & ->))]"; done.
  Admitted.

  Lemma deser_valid :
    ∀ t v s, s_is_ser_deser t v s -∗ s_deser_valid_val t v.
  Proof.
    iIntros (???) "Hser".
    iInduction t as [| | | |] forall (v s); iSimpl; iSimpl in "Hser".
    - iDestruct "Hser" as (????) "((-> & ->) & H1 & H2)".
      iPoseProof ("IHt1" with "H1") as "H1".
      iPoseProof ("IHt2" with "H2") as "H2".
      iExists v1, v2.
      iSplit; [done|iFrame].
    - iDestruct "Hser" as (??) "[(H & %)|(H & %)]".
      + destruct H as [-> _]. iExists _. iLeft. iSplit; [done|].
        iApply ("IHt1" with "H").
      + destruct H as [-> _]. iExists _. iRight. iSplit; [done|].
        iApply ("IHt2" with "H").
    - iDestruct "Hser" as "%Hser". destruct Hser as (? & -> & _). iExists _. done.
    - iDestruct "Hser" as "%Hser". destruct Hser as (? & -> & _). iExists _. done.
    - iDestruct "Hser" as (? ->) "[(% & -> & Hser)|(% & % & -> & Hsusp & Hser)]".
      + iExists _. iSplit; [done|].
        iLeft. eauto.
      + iExists _.
        iSplit; [done|].
        iRight. iExists _. iSplit; [done|]. iExists _. iFrame.
  Qed.            

  Lemma deser_valid_weak E :
    ∀ t v, s_deser_valid_val t v ⊢ |={E}=> s_valid_val t v.
  Proof.
    iIntros (??) "Hdvalid".
    iInduction t as [| | | |] forall (v); iSimpl; iSimpl in "Hdvalid".
    - iDestruct "Hdvalid" as (??->) "[H1 H2]".
      iPoseProof ("IHt1" with "H1") as "H1".
      iPoseProof ("IHt2" with "H2") as "H2".
      iExists v1, v2.
      iMod "H1". iMod "H2".
      iModIntro. iSplit; [done|iFrame].
    - iDestruct "Hdvalid" as (?) "[[-> H]|[-> H]]".
      + iPoseProof ("IHt1" with "H") as "H". iMod "H".
        iModIntro. iExists _. iLeft. iSplit; [done|iExact "H"].
      + iPoseProof ("IHt2" with "H") as "H". iMod "H".
        iModIntro. iExists _. iRight. iSplit; [done|iExact "H"].
    - by iModIntro.
    - by iModIntro.
    - iDestruct "Hdvalid" as (? ->) "[(% & ->)|(% & -> & % & Hsusp)]".
      + iExists _. iModIntro. iSplit; [done|].
        iLeft. eauto.
      + iExists _.
        iMod (na_inv_alloc seqG_name E (authValidN #susp) (valid_auth_inv susp) with "[Hsusp]") as "Hinv".
        { iNext. iRight. eauto. }
        iModIntro.
        iSplit; [done|].
        iRight. eauto.
  Qed.
        
  #[global] Instance : Inhabited evi_type.
  Proof. constructor. apply tstring. Qed.

  (* Fixpoint evi_type_ser (t : evi_type) : serialization_scheme :=
    match t with
    | tprod t1 t2 => prod_serialization_scheme (evi_type_ser t1) (evi_type_ser t2)
    | tsum t1 t2 => sum_serialization_scheme (evi_type_ser t1) (evi_type_ser t2)
    | tstring => string_serialization_scheme
    | tint => int_serialization_scheme
    | tauth => auth_serialization_scheme
    end. *)
  
  Fixpoint evi_type_count (t : evi_type) : expr :=
    match t with
    | tprod t1 t2 => prod_count (evi_type_count t1) (evi_type_count t2)
    | tsum t1 t2 => sum_count (evi_type_count t1) (evi_type_count t2)
    | tstring => string_count
    | tint => int_count
    | tauth => auth_count
    end.

  Definition count_auth_inv (susp: loc) (c: nat) : iProp Σ :=
     ((∃ (h : string), susp ↦□ (InjRV #h) ∗ ⌜c = 0⌝) ∨
        (∃ (pid : nat), susp ↦ (InjLV #pid) ∗ ⌜c = 1⌝)).

  Fixpoint count_is_correct (t : evi_type) (v : val) (c : nat) : iProp Σ :=
    match t with
    | tprod t1 t2 =>
        ∃ (c1 c2 : nat) (v1 v2 : val),
          ⌜v = (v1, v2)%V⌝ ∗ count_is_correct t1 v1 c1 ∗ count_is_correct t2 v2 c2 ∗ ⌜(c1 + c2)%nat = c⌝
    | tsum t1 t2 =>
        (∃ (v1 : val), ⌜v = InjLV v1⌝ ∗ count_is_correct t1 v1 c) ∨
          (∃ (v2 : val), ⌜v = InjRV v2⌝ ∗ count_is_correct t2 v2 c)
    | tstring => string_valid_val v ∧ ⌜c = 0⌝
    | tint => int_valid_val v ∧ ⌜c = 0⌝
    | tauth =>
        (∃ v1, ⌜v = SOMEV v1⌝ ∧
                 ((∃ (h : string), ⌜v1 = InjLV #h ∧ c = 0⌝) ∨ 
                    (∃ (susp : loc),
                        ⌜v1 = InjRV #susp⌝ ∗ seq_inv (authCountN #susp) (count_auth_inv susp c))))
  end.

  #[global] Instance count_is_correct_persistent t v c: Persistent (count_is_correct t v c).
  Proof. revert v c; induction t => v c; simpl; apply _. Qed.

(*  Lemma count_valid t v :
    ∀ E1 c, ∃ E2, seq_tok E1 ∗ count_is_correct t v c  ={E1,E2}=∗ seq_tok E2 ∗ s_valid_val t v.
  Proof.
    iIntros (?). eexists _. iIntros "(Htok & Hcount)".
    iInduction t as [| | | |] forall (E1 v c); iSimpl; iSimpl in "Hcount".
    - iDestruct "Hcount" as (???? -> ) "(Hcount1 & Hcount2 & %)". simplify_eq.
      iPoseProof ("IHt1" with "Htok Hcount1") as "H1".
      iMod "H1" as "(Htok & H1)".
      iPoseProof ("IHt2" with "Htok Hcount2") as "H2".
      iMod "H2" as "(Htok & H2)". iFrame.
      iModIntro. iFrame. eauto.
    - iDestruct "Hcount" as "[(%&->&Hcount)|(%&->&Hcount)]".
      + iPoseProof ("IHt1" with "Htok Hcount") as "H".
        iMod "H" as "(Htok & H)". iFrame.
        iModIntro. iExists _. iLeft. eauto.
      + iPoseProof ("IHt2" with "Htok Hcount") as "H".
        iMod "H" as "(Htok & H)". iFrame.
        iModIntro. iExists _. iRight. eauto.
    - iFrame. by iDestruct "Hcount" as "(H&%)".
    - iFrame. by iDestruct "Hcount" as "(H&%)".
    - iFrame. iDestruct "Hcount" as (??) "[(%&->&->)|(%&->&Hsusp)]".
      + iModIntro. iExists _. iSplit; [done|]. eauto.
      + iExists _.
        iMod (na_inv_acc with "Hsusp") as "Hinv". *)
        
                                                 
  Definition ser_spec_3 (ser : val) (t : evi_type) : iProp Σ :=
    ∀ (v1 : val) (c: nat),
      {{{ ▷ (count_is_correct t v1 c ∗ seq_tok ⊤) }}}
        ser v1
        {{{ o, RET $o; seq_tok ⊤ ∗ if o is Some s then s_is_ser'' t v1 s else True }}}.
        
                                                 
  Definition ser_spec_2 (ser : val) (t : evi_type) : iProp Σ :=
    ∀ (v1 : val),
      {{{ ▷ (s_valid_val t v1 ∗ seq_tok ⊤) }}}
        ser v1
        {{{ o, RET $o; seq_tok ⊤ ∗ if o is Some s then s_is_ser'' t v1 s else True }}}.

  Definition ser_spec (A : lrel Σ) (ser : val) (t : evi_type) : iProp Σ :=
    ∀ (v1 v2 : val),
      {{{ ▷ (A v1 v2 ∗ seq_tok ⊤) }}}
        ser v1
      {{{ o, RET $o; seq_tok ⊤ ∗ if o is Some s then s_is_ser'' t v1 s else True }}}.

  Definition deser_spec (deser : val) (t : evi_type) : iProp Σ :=
    ∀ (pid : nat),
      {{{ True }}}
      deser #pid
      {{{ (deser_partial : val), RET deser_partial;
          ∀ (s : string),
            {{{ True }}}
              deser_partial #s
              {{{ o, RET $o; if o is Some v then s_is_ser_deser t v s else True }}}
      }}}.
  
  Definition deser1_spec (deser_partial : val) (t : evi_type) : iProp Σ :=
    ∀ (s : string),
      ({{{ True }}}
         deser_partial #s
      {{{ o, RET $o; if o is Some v then s_is_ser_deser t v s else True }}}).

  Definition count_spec (count : val) (t : evi_type): iProp Σ :=
    ∀ (v1 : val),
      {{{ ▷ s_deser_valid_val t v1 }}}
        count v1
      {{{ v, RET v; ∃ (c : nat), ⌜v = #c⌝ ∧ count_is_correct t v1 c }}}.

  Definition lrel_evidence' (A : lrel Σ) : lrel Σ :=
    LRel (λ v1 v2,
        ∃ (t : evi_type) (ser deser count : val),
          ⌜v1 = (ser, deser, count)%V⌝ ∗ ser_spec A ser t ∗ ser_spec_2 ser t ∗ ser_spec_3 ser t ∗ count_spec count t ∗
            deser_spec deser t)%I.

  Program Definition lrel_evidence : kindO Σ (⋆ ⇒ ⋆)%kind := λne A, lrel_evidence' A.
  Next Obligation.
    intros ??????.
    rewrite /lrel_car/= /ser_spec /count_spec /deser_spec.
    solve_proper.
  Qed.

  Lemma prod_ser'_spec_ser (HA HB : val → iProp Σ) (tA tB : evi_type) (serA serB v vA vB : val) :
    (▷ ⌜v = (vA, vB)%V⌝) -∗
    ({{{ ▷ (HA vA ∗ seq_tok ⊤) }}}
        serA vA
      {{{ o, RET $o; seq_tok ⊤ ∗ if o is Some s then s_is_ser'' tA vA s else True }}}) -∗
    ({{{ ▷ (HB vB ∗ seq_tok ⊤) }}}
        serB vB
      {{{ o, RET $o; seq_tok ⊤ ∗ if o is Some s then s_is_ser'' tB vB s else True }}}) -∗
    {{{ ▷ (prod_valid_val' v HA HB ∗ seq_tok ⊤) }}}
      prod_ser''' serA serB v
      {{{ o, RET $o; seq_tok ⊤ ∗ if o is Some s then prod_is_ser' v s (s_is_ser'' tA) (s_is_ser'' tB) else True }}}.
  Proof.
    iIntros "#Hv #HA #HB % !# (Hp & Htok) HΦ".
    rewrite /prod_ser''' /prod_is_ser.
    wp_pures.
    iDestruct "Hp" as (???) "[H1 H2]". iSimplifyEq.
    wp_pures.
    wp_apply ("HA" with "[$H1 $Htok]").
    iIntros ([]); last first.
    { iIntros "(Htok & _)". wp_pures. iApply ("HΦ" $! None). by iFrame. }
    iIntros "(Htok & HserA)".
    wp_pures.
    wp_apply ("HB" with "[$H2 $Htok]").
    iIntros ([]); last first.
    { iIntros "(Htok & _)". wp_pures. iApply ("HΦ" $! None). by iFrame. }
    iIntros "(Htok & HserB)".
    wp_pures.
    iApply ("HΦ" $! (Some _)).
    iModIntro. iFrame. eauto.
  Qed.
  
End authenticatable.

Instance s_is_ser''_persistent `{heapGS_gen hlc Σ, seqG Σ} t v s: Persistent (s_is_ser'' t v s).
Proof. revert v s; induction t => v s; simpl; apply _. Qed.

Section proof.
  Context `{!authG Σ, !seqG Σ} (N : namespace).

  Definition authSerProofN (v : val) : namespace := N .@ "auth_ser_proof" .@ v.

  Lemma refines_Auth_pair Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆; ⋆, var2 var1 → var2 var0 → var2 (var1 * var0) ⟧
      (ext Δ (lrel_evidence N)) v_Auth_pair i_Auth_pair.
  Proof.
    interp_unfold.
    iIntros (A ??) "!# _".
    iIntros (??) "(Hi & Htok)".
    rewrite /v_Auth_pair /i_Auth_pair.
    i_pures; wp_pures.
    iModIntro. iFrame.
    iIntros (B ??) "!# _".
    iIntros (??) "(Hi & Htok)".
    i_pures; wp_pures.
    iModIntro. iFrame.
    iIntros (??) "!# HA".
    interp_unfold! in "HA".
    iDestruct "HA" as (tA serA deserA countA ->) "(#HserA & #Hser2A & #Hser3A & #HcountA & #HdeserA)". clear.
    iIntros (??) "(Hi & Htok)".
    i_pures; wp_pures.
    iModIntro. iFrame.
    iIntros (??) "!# HB".
    interp_unfold! in "HB".
    iDestruct "HB" as (tB serB deserB countB ->) "(#HserB & #Hser2B & #Hser3B & #HcountB & #HdeserB)". clear.
    iIntros (??) "(Hi & Htok)".
    i_pures; wp_pures. clear.
    rewrite /prod_scheme /prod_ser'' /prod_deser /prod_count.
    wp_pures. iFrame. iModIntro.
    interp_unfold!.
    iExists (tprod tA tB), _, _, _.
    iSplit; [done|]. clear. iSplit; [|iSplit; [|iSplit; [|iSplit]]].
    - iIntros (v1 v2 ?) "!# (Hp & Htok) H".
      iDestruct "Hp" as (w1 w2 u1 u2) "(>-> & >-> & #HA & #HB)".
      iSimpl in "H".
      wp_apply (prod_ser'_spec_ser (λ v1, A v1 w2) (λ v1, B v1 u2) with "[] [] [] [$Htok]") => /=; [done| | | |done].  
      { iIntros (?) "!# Hp H". by wp_apply ("HserA" with "Hp"). }
      { iIntros (?) "!# Hp H". by wp_apply ("HserB" with "Hp"). }
      iExists _, _. eauto.
    - iIntros (v1 ?) "!# (Hp & Htok) H". iSimpl in "Hp".
      iDestruct "Hp" as (w1 w2) "(>-> & HA & HB)".
      wp_apply (prod_ser'_spec_ser (s_valid_val _ tA) (s_valid_val _ tB) with "[] [] [] [HA HB $Htok]") => /=; [done| | | |done].  
      { iIntros (?) "!# Hp H". by wp_apply ("Hser2A" with "Hp"). }
      { iIntros (?) "!# Hp H". by wp_apply ("Hser2B" with "Hp"). }
      iNext. iFrame. eauto.
    - iIntros (v1 c ?) "!# (Hc & Htok) H".
      iDestruct "Hc" as (????) "(>-> & HA & HB & >%)".
      iSimpl in "H".
      wp_apply (prod_ser'_spec_ser (λ v1, count_is_correct _ tA v1 c1) (λ v2, count_is_correct _ tB v2 c2) with "[] [] [] [HA HB $Htok]") => /=; [done| | | |done].
      { iIntros (?) "!# Hc H". by wp_apply ("Hser3A" with "Hc"). }
      { iIntros (?) "!# Hc H". by wp_apply ("Hser3B" with "Hc"). }
      iNext. iFrame. eauto.
    - iIntros (??) "!# Hp HΨ". wp_pures.
      iDestruct "Hp" as (?? ->) "(HA & HB)".
      wp_pures. rewrite /count_spec.
      wp_bind (countB _).
      wp_apply ("HcountB" $! v2 with "HB").
      iIntros (?) "(% & -> & HcountsB)".
      wp_pures.
      wp_apply ("HcountA" $! v0 with "HA").
      iIntros (?) "(% & -> & HcountsA)".
      wp_pures. iModIntro.
      iApply "HΨ".
      iExists (c0+c). iSplit; [iPureIntro; f_equal|].
      { by rewrite Nat2Z.inj_add. }
      iExists _, _, _, _.
      iSplit; iFrame; done.
    - iIntros (pid ?) "!# _ HΨ".
      wp_pures.
      wp_apply "HdeserB"; [done|]. iIntros "%deparB #HdeparB".
      wp_apply "HdeserA"; [done|]. iIntros "%deparA #HdeparA".
      wp_pures. iModIntro. iApply "HΨ".
      iIntros (s ?) "!# _ HΨ".
      wp_apply prod_deser'_sound; auto.
  Qed.
  
  Lemma refines_Auth_sum Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆; ⋆, var2 var1 → var2 var0 → var2 (var1 + var0) ⟧
      (ext Δ (lrel_evidence N)) v_Auth_sum i_Auth_sum.
  Proof. Admitted.

  Lemma refines_Auth_string :
    ⊢ (lrel_evidence N) lrel_string v_Auth_string i_Auth_string.
  Proof. Admitted.

  Lemma refines_Auth_int :
    ⊢ (lrel_evidence N) lrel_int v_Auth_int i_Auth_int.
  Proof. Admitted.

  Lemma refines_Auth_mu Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆ ⇒ ⋆, var1 (var0 (μ: ⋆; var1 var0)) → var1 (μ: ⋆; var1 var0) ⟧
      (ext Δ (lrel_evidence N)) v_Auth_mu i_Auth_mu.
  Proof.
    rewrite /lrel_car/=.
    iIntros (A v1 v2) "!# _". iIntros (??) "(Hi & Htok)".
    rewrite /i_Auth_mu /v_Auth_mu.
    i_pures. wp_pures.
    iFrame. iModIntro. clear.
    interp_unfold!.
    iIntros (??) "!# H".
    iIntros (??) "(Hi & Htok)".
    interp_unfold! in "H".
    iDestruct "H" as "(%t & %ser & %deser & %count & -> & #Hser & #Hser2 & #Hser3 & #Hcount & #Hdeser)".
    i_pures. wp_pures.
    iFrame. iModIntro.
    interp_unfold!.
    iExists t, _, _, _. iSplit; [done|].
    clear. iSplit; [|iSplit]; [| |iSplit; [|iSplit]].
    - iIntros (v1 v2 Ψ) "!# (#Hs & Htok) HΨ".
      wp_pures.
      rewrite interp_rec_star_unfold.
      rewrite interp_unseal /=.
      wp_apply ("Hser" with "[Htok]"); [by iFrame|done].
    - iIntros (v1 Ψ) "!# (Hs & Htok) HΨ".
      wp_pures.
      wp_apply ("Hser2" with "[Hs Htok]"); [by iFrame|done].
    - iIntros (v1 c Ψ) "!# (Hs & Htok) HΨ".
      wp_pures.
      wp_apply ("Hser3" with "[Hs Htok]"); [by iFrame|done].
    - iIntros (??) "!# Hp HΨ". wp_pures.
      by iApply ("Hcount" with "Hp").
    - iIntros (pid Ψ) "!# _ HΨ". wp_pures.
      iApply "HΨ". iModIntro.
      iIntros (s ?) "!# _ HΨ". wp_pures.
      wp_apply "Hdeser"; [done|].
      iIntros (depar) "HΨ1".
      iApply "HΨ1"; [done|].
      iModIntro.
      iIntros ([]) "H"; last first.
      { by iApply "HΨ". }
      by iApply "HΨ".
  Qed.

  Definition auth_inv (susp : loc) :=
    ((∃ (s1 : string), hashed s1 ∗ susp ↦□ InjRV #(hash s1)) ∨
       ∃ (pid : nat), susp ↦ (InjLV #pid))%I.

  Definition auth_some (A : lrel Σ) (v1 v2 : val) : iProp Σ :=
    (∃ (a1 : val) (t : evi_type) (s1 : string),
        s_is_ser'' t a1 s1 ∗ A a1 v2 ∗
          ((hashed s1 ∗ ⌜v1 = InjLV #(hash s1)⌝) ∨
             (∃ (susp : loc),
                 ⌜v1 = InjRV #susp⌝ ∗ seq_inv (authSerProofN #susp) (auth_inv susp)))).

  #[global] Instance auth_some_persistent A v1 v2 : Persistent (auth_some A v1 v2).
  Proof. unfold auth_some. apply _. Qed.
  
  Definition lrel_auth_some (A : lrel Σ) : lrel Σ :=
    LRel (λ v1 v2, auth_some A v1 v2)%I.

  Definition lrel_auth' (A : lrel Σ) : lrel Σ :=
    LRel (λ a1 v2, (∃ v1, ⌜a1 = SOMEV v1⌝ ∗ lrel_auth_some A v1 v2) ∨ ⌜a1 = NONEV⌝)%I.
  
  Program Definition lrel_auth : kindO Σ (⋆ ⇒ ⋆)%kind := λne A, lrel_auth' A.
  Next Obligation.
    intros ??????.
    rewrite /lrel_car/= /lrel_auth' /lrel_auth_some /auth_some.
  Admitted.
  

  Definition is_proof (v : val) : iProp Σ :=
    ∃ (l : list string), ⌜is_list l v⌝.

  Definition lrel_proof : lrel Σ :=
    LRel (λ v1 _, is_proof v1 )%I.

  Definition auth_ctx {Θ} (Δ : ctxO Σ Θ) (R : kindO Σ (⋆ ⇒ ⋆)) :=
    ext (ext (ext Δ lrel_auth) R) (lrel_evidence N).

  Lemma refines_Auth_auth Θ (Δ : ctxO Σ Θ) R :
    ⊢ ⟦ ∀: ⋆, var1 (var3 var0) ⟧
      (auth_ctx Δ R) v_Auth_auth i_Auth_auth.
  Proof.
    iIntros (A ??) "!# _"; rewrite -!/interp.
    iIntros (??) "(Hi & Htok)".
    rewrite /v_Auth_auth /i_Auth_auth.
    i_pures; wp_pures.
    iModIntro. iFrame.
    rewrite /auth_ctx.
    interp_unfold!.
    iExists tauth, _, _, _.
    iSplit; [done|]. clear. iSplit; [|iSplit]; [| |iSplit; [|iSplit]].
    - iIntros (???) "!# (#Hauth & Htok) H".
      rewrite /auth_ser_v. wp_pure.
      iDestruct "Hauth" as "[(% & -> & Hauth)|->]"; wp_pures; last first.
      { iApply ("H" $! None). by iFrame. }
      iDestruct "Hauth" as "(%&%&%&Hser&HA&[(Hhash&%)|(%&%&Hinv)])";
        simplify_eq; wp_pures.
      + wp_apply s_ser_spec'.
        { iRight. eauto. }
        iIntros (o) "#Ho". destruct o; last first.
        { iApply ("H"  $! None). by iFrame. }
        iApply ("H" $! (Some _)). iFrame.
        iExists _. iSplit; [done|].
        iLeft. iExists _. eauto.
      + wp_bind (!_)%E.
        iMod (na_inv_acc with "Hinv Htok") as "(Hinv1 & Htok & Hclose)"; [done|done|].
        iDestruct "Hinv1" as "[(%&#Hhash&#Hsusp)|(%&Hsusp)]".
        * (* iMod ("Hclose" with "[Htok]") as "Htok".
          { iFrame. iNext. iLeft. iFrame "∗ #". }
          wp_pures.
          iMod ("Hclose" with "[Htok]") as "Htok".
          { iFrame. iNext. iLeft. iFrame "∗ #". }
          wp_apply s_ser_spec'.
          { iRight. eauto. }
          iIntros (o) "#Ho". destruct o; last first.
          { by iApply ("H" $! None). }
          iApply ("H" $! (Some _)).
          iFrame.
          iExists _. iSplit; [done|].
          iRight. iExists _, _.
          iSplit; [done|]. iFrame "#". *)
          wp_load.
          iDestruct "Hser" as "#Hser".
          iMod ("Hclose" with "[Hser HA Hhash Hsusp Htok]") as "Htok".
          { iFrame. iLeft. iFrame "#∗". }
          wp_pures.
          wp_apply s_ser_spec'.
          { iRight. eauto. }
          iIntros (o) "#Ho". destruct o; last first.
          { iApply ("H" $! None). iFrame. }
          iApply ("H" $! (Some _)). iFrame.
          iExists _. iSplit; [done|].
          iRight. iExists _, _. eauto.
        * wp_load.
          iMod ("Hclose" with "[$Hsusp $Htok]") as "Htok".
          wp_pures.
          iApply ("H" $! None). by iFrame.
    - iIntros (??) "!# (#Hauth & Htok) H".
      rewrite /auth_ser_v. wp_pure. iSimpl in "Hauth".
      iDestruct "Hauth" as "(% & -> & [(% & ->)|(%&%&Hinv)])".
      + wp_pures. wp_apply s_ser_spec'.
        { iRight. eauto. }
        iIntros (o) "#Ho". destruct o; last first.
        { iApply ("H"  $! None). by iFrame. }
        iApply ("H" $! (Some _)). iFrame.
        iExists _. iSplit; [done|].
        iLeft. iExists _. eauto.
      + simplify_eq. wp_pures. wp_bind (!_)%E.
        iMod (na_inv_acc with "Hinv Htok") as "([(%&#Hsusp)|(%&Hsusp)] & Htok & Hclose)"; [done|done| |]; wp_load.
        * iMod ("Hclose" with "[$Htok]") as "Htok".
          { iLeft. iFrame "#∗". }
          wp_pures.
          wp_apply s_ser_spec'.
          { iRight. eauto. }
          iIntros (o) "#Ho". destruct o; last first.
          { iApply ("H" $! None). by iFrame. }
          iApply ("H" $! (Some _)). iFrame.
          iExists _. iSplit; [done|].
          iRight. iExists _, _.
          eauto.
        * iMod ("Hclose" with "[Hsusp $Htok]") as "Htok".
          { iRight. eauto. }
          wp_pures.
          iApply ("H" $! None). by iFrame.

    - iIntros (???) "!# (#Hc & Htok) H".
      rewrite /auth_ser_v. wp_pure. iSimpl in "Hc".
      iDestruct "Hc" as (?->) "[(% & -> & ->)|(% & -> & Hinv)]".
      + wp_pures. wp_apply s_ser_spec'.
        { iRight. eauto. }
        iIntros (o) "#Ho". destruct o; last first.
        { iApply ("H"  $! None). by iFrame. }
        iApply ("H" $! (Some _)). iFrame.
        iExists _. iSplit; [done|].
        iLeft. iExists _. eauto.
      + simplify_eq. wp_pures. wp_bind (!_)%E.
        iMod (na_inv_acc with "Hinv Htok") as "([(%&#Hsusp&>%)|(%&Hsusp&>%)] & Htok & Hclose)"; [done|done| |]; wp_load.
        * iMod ("Hclose" with "[$Htok]") as "Htok".
          { iLeft. by iFrame "#∗". }
          wp_pures.
          wp_apply s_ser_spec'.
          { iRight. eauto. }
          iIntros (o) "#Ho". destruct o; last first.
          { iApply ("H" $! None). by iFrame. }
          iApply ("H" $! (Some _)). iFrame.
          iExists _. iSplit; [done|].
          iRight. iExists _, _.
          eauto.
        * iMod ("Hclose" with "[Hsusp $Htok]") as "Htok".
          { iRight. eauto. }
          wp_pures.
          iApply ("H" $! None). by iFrame.
        
    - iIntros (??) "!# Hauth H".
      rewrite /auth_count. wp_pures.
      iDestruct "Hauth" as "(% & -> & [(% & ->)|(%&%&%&Hsusp)])"; simplify_eq; wp_pures.
      { iApply "H". iExists 0. iModIntro. iSplit; [done|].
        iExists _. eauto. }
      wp_load. wp_pures.
      iMod (na_inv_alloc seqG_name ⊤ (authCountN N #susp) (count_auth_inv susp 1) with "[Hsusp]") as "Hinv".
      { iRight. iExists _. iModIntro. by iFrame. }
      iApply "H". iExists 1. iModIntro.
      iSplit; [iPureIntro; f_equal|].
      iExists _. iSplit; [done|]. iRight. iExists susp. by iFrame.
      
      (* iDestruct "Hauth" as "(% & -> & [(% & ->)|(%&%&#Hinv)])"; simplify_eq; wp_pures.
      { iApply "H". iExists 0. iModIntro. iSplit; [done|].
        iRight. iExists _. eauto. }
      wp_bind (!_)%E.
      iInv "Hinv" as "[(%&#Hsusp)|(%&Hsusp)]" "Hclose"; wp_load.
      + iMod ("Hclose" with "[]") as "_".
        { iLeft. eauto. }
        iModIntro. wp_pures.
        iApply "H". iExists 0. iModIntro.
        iSplit; [iPureIntro; f_equal|].
        iRight. iExists _. iRight.
        iExists _. iSplit; [done|].
        iLeft. eauto.
      + iMod ("Hclose" with "[Hsusp]") as "_".
        { iRight. eauto. }
        iModIntro. wp_pures.
        iApply "H". iExists 1. iModIntro.
        iSplit; [iPureIntro; f_equal|].
        iRight. iExists _. iRight. iExists susp.
        iSplit; [done|]. by iRight. *)
        
          
    - iIntros (??) "!# _ H".
      rewrite /auth_deser_v. wp_pures.
      iModIntro. iApply "H".
      iIntros (s?) "!# _ H".
      wp_pures. wp_apply s_deser_sound; [done|].
      iIntros ([] ?); wp_pures.
      + destruct H as [(->&H)|(?&?&(->&H)&?)]; wp_pures.
        * wp_alloc susp as "Hsusp".
(*          iMod(inv_alloc (authSerN #susp) _ (auth_inv A susp) with "[Hsusp]") as "#Hinv".
          { iModIntro. iRight. eauto. } *)
          wp_pures.
          iApply ("H" $! (Some _)).
          iModIntro. iExists _. iSplit; [done|].
(*          { simpl. iExists _. iSplit; [done|].
            iRight. rewrite /auth_is_ser_3.
            iExists _, _. iSplit; [done|].
            iInv "Hinv" as "[(%&%&%&%&Hser&HA&Hhash&#Hsusp)|(%&Hsusp)]" "Hclose".
            iInv 
            eauto. } *)
          iRight. iExists _, _. iSplit; [done|].
          iFrame. iSimpl. iLeft. done.
        * iModIntro. iApply ("H" $! (Some _)).
          iExists _. iSplit; [done|].
          iLeft. rewrite /auth_is_ser_1.
          destruct! H0. simplify_eq.          
          iExists _. iSplit; [done|].
          iRight. iExists _, _.
          eauto.
      + by iApply ("H" $! None).
  Qed.

  Lemma refines_auth_auth Θ (Δ : ctxO Σ Θ) R:
    ⊢ ⟦ ∀: ⋆, var1 var0 → var0 → var3 var0 ⟧
      (auth_ctx Δ R) v_auth i_auth.
  Proof.
    iIntros (???) "!# _"; rewrite -/interp.
    iIntros (??) "(Hi & Htok)".
    rewrite /v_auth  /i_auth.
    i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iIntros (??) "!# #HeviA".
    rewrite /auth_ctx.
    interp_unfold! in "HeviA".
    iDestruct "HeviA" as (tA ser count deser ->) "(#Hser & #Hser2 & #Hser3 & #Hcount & #Hdeser)".
    iIntros (??) "(Hi & Htok)".
    i_pures; wp_pures.
    iFrame.
    interp_unfold.
    iIntros "!> !>" (w1 w2) "#HA". clear.
    iIntros (??) "(Hi & Htok)".
    i_pures; wp_pures.
    interp_unfold! in "HA".
    wp_apply ("Hser" with "[$Htok]"); [done|].
    iIntros ([]) "(Htok & Hs1)"; wp_pures; last first.
    { iFrame. interp_unfold!. by iRight. }
    wp_apply (wp_hash with "[$]"). iIntros "#Hh1".
    wp_pures.
    iFrame.
    interp_unfold!.
    iLeft. iExists _.
    iModIntro. iSplit; [done|].
    iExists _, _, _. iFrame "# ∗ %".
    by iLeft.
  Qed.

End proof.

