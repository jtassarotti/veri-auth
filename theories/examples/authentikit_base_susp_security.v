From auth.prelude Require Import stdpp.
From auth.rel_logic_bin Require Export model spec_rules spec_tactics interp lib adequacy fundamental.
From auth.heap_lang Require Import gen_weakestpre typedproph.
From auth.heap_lang.lib Require Import list serialization.
From auth.examples Require Export authentikit_susp authenticatable_base_susp.
From iris.base_logic.lib Require Export invariants na_invariants.
From iris.algebra Require Import gmap agree.

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
  
Inductive evi_type : Type :=
| tprod (t1 t2 : evi_type)
| tsum (t1 t2 : evi_type)
| tstring
| tint
| tauth.

Definition mapUR := gmapUR nat (agreeR (prodO
                                          (prodO
                                             (prodO
                                                (prodO (leibnizO evi_type) valO)
                                                valO)
                                             (optionO locO))
                                          (leibnizO bool))).

Definition locPidMapUR := gmapUR locO nat.

Definition stateUR := authUR (prodUR mapUR locPidMapUR).
Class stateG Σ := StateG { state_inG :> inG Σ stateUR; stateG_name : gname }.

(* Definition counterUR := gmapUR nat (authR natUR).
Class counterG Σ := CounterG { counter_inG :> inG Σ counterUR; counterG_name : gname }. *)

Definition authSerProofSet (N : namespace) : namespace := N .@ "auth_ser_proof".
Definition authSerProofN (N : namespace) (v : val) : namespace := (authSerProofSet N) .@ v.

Section authenticatable.
  Context `{!stateG Σ, !heapGS_gen hlc Σ, !seqG Σ} (N : namespace).

  (* Definition authSerSet : namespace := N .@ "auth_ser".
  Definition authSerN (v: val) : namespace := authSerSet .@ v.
  Definition authValidSet : namespace := N .@ "auth_valid".
  Definition authValidN (v: val) : namespace := authValidSet .@ v.
  Definition authCountSet : namespace := N .@ "auth_count".
  Definition authCountN (l: loc) : namespace := authCountSet .@ l.
  Definition authInSet : namespace := N .@ "auth_in".
  Definition authInN (l : loc) : namespace := authInSet .@ l. *)

  Definition single_instance (id : nat) (t : evi_type) (x vᵥ : val) (susp_option : option loc) (b : bool)  : iProp Σ :=
    own stateG_name (◯ ({[ id := to_agree (t, x, vᵥ, susp_option, b) ]} : mapUR,
                         (if susp_option is Some susp then {[ susp := id ]} else ∅) : locPidMapUR)).

  (* Definition count (pid c : nat) : iProp Σ :=
    own counterG_name ({[ pid := ● c ]}).

  Definition token (pid : nat) : iProp Σ :=
    own counterG_name ({[ pid := ◯ 1 ]}).

  Definition used_token (pid : nat) : iProp Σ :=
    □ (own counterG_name ({[ pid := ◯ 1 ]})). *)

  (* Definition suspended_loc (susp : loc) : iProp Σ :=
    ∀ (h: string), susp ↦□ InjRV #h -∗ False.

  (* Definition count_auth_inv (susp : loc) (c : nat) : iProp Σ :=
    ((∃ (h : string), susp ↦□ (InjRV #h) ∗ ⌜c = 0⌝) ∨
       (suspended_loc susp ∗ ⌜c = 1⌝)). *)
  
  Fixpoint count_is_correct (t : evi_type) (v : val) (c : nat) : iProp Σ :=
    match t with
    | tprod t1 t2 =>
        ∃ (c1 c2 : nat) (v1 v2 : val),
          ⌜v = (v1, v2)%V ∧ (c1 + c2)%nat = c⌝ ∗ count_is_correct t1 v1 c1 ∗ count_is_correct t2 v2 c2
    | tsum t1 t2 =>
        (∃ (v1 : val), ⌜v = InjLV v1⌝ ∗ count_is_correct t1 v1 c) ∨
          (∃ (v2 : val), ⌜v = InjRV v2⌝ ∗ count_is_correct t2 v2 c)
    | tstring => string_valid_val v ∧ ⌜c = 0⌝
    | tint => int_valid_val v ∧ ⌜c = 0⌝
    | tauth =>
        (∃ v1, ⌜v = SOMEV v1⌝ ∧
                 ((∃ (h : string), ⌜v1 = InjLV #h ∧ c = 0⌝) ∨ 
                    (∃ (susp : loc),
                        ⌜v1 = InjRV #susp⌝ ∗
                          ((∃ (h : string), susp ↦□ (InjRV #h) ∗ ⌜c = 0⌝) ∨
                             (∃ (pid : nat), susp ↦{#1/4} InjLV #pid ∗ ⌜c = 1⌝)))))
  end.

  #[global] Instance count_is_correct_timeless t v c: Timeless (count_is_correct t v c).
  Proof. revert v c; induction t => v c; simpl; apply _. Qed.

  Fixpoint susp_in_v (t : evi_type) (v : val) (susp : loc) : iProp Σ :=
    match t with
    | tprod t1 t2 =>
        ∃ (v1 v2 : val), ⌜v = (v1, v2)%V⌝ ∧ (susp_in_v t1 v1 susp ∨ susp_in_v t2 v2 susp)
    | tsum t1 t2 =>
        ∃ (v' : val), (⌜v = InjLV v'⌝ ∧ susp_in_v t1 v' susp) ∨ (⌜v = InjRV v'⌝ ∧ susp_in_v t2 v' susp)
    | tstring | tint => False
    | tauth => ∃ v1, ⌜v = SOMEV v1 ∧ v1 = InjRV #susp⌝ ∗
                       ((∃ (pid : nat), susp ↦{#1/4} InjLV #pid) ∨ False)
  end.

  Fixpoint sub_obj (v sv: val) (t : evi_type) :=
    match t with
    | tprod t1 t2 =>
        ∃ v1 v2, v = (v1, v2)%V ∧ (sv = v1 ∨ sv = v2 ∨ sub_obj v1 sv t1 ∨ sub_obj v2 sv t2)
    | tsum t1 t2 =>
        ∃ v', ((v = InjLV v' ∧ sub_obj v' sv t1 ∧ v = v') ∨
                 (v = InjRV v' ∧ sub_obj v' sv t2 ∧ v = v'))
    | tstring => False
    | tint => False
    | tauth =>
        ∃ v', (v = SOMEV (InjLV v') ∨ (v = SOMEV (InjRV v'))) ∧ v' = sv
  end.

  Definition subeq_obj (v sv: val) :=
    (∃ t, sub_obj v sv t) ∨ v = sv.

  Lemma subeq_obj_trans (v sv ssv : val) :
    subeq_obj v sv → subeq_obj sv ssv → subeq_obj v ssv.
  Proof. Admitted.

  Fixpoint sub_obj_bin (v1 v2 sv1 sv2 : val) (t : evi_type) :=
    match t with
    | tprod t1 t2 =>
        ∃ v11 v12 v21 v22, v1 = (v11, v12)%V ∧ v2 = (v21, v22)%V ∧
                             ((sv1 = v11 ∧ sv2 = v21) ∨ (sv1 = v12 ∧ sv2 = v22) ∨
                                (sub_obj_bin v11 v21 sv1 sv2 t1) ∨
                                (sub_obj_bin v12 v22 sv1 sv2 t2))
    | tsum t1 t2 =>
        ∃ v1' v2', ((v1 = InjLV v1' ∧ v2 = InjLV v2' ∧
                       sub_obj_bin v1' v2' sv1 sv2 t1) ∨
                      (v1 = InjRV v1' ∧ v2 = InjRV v2' ∧
                         sub_obj_bin v1' v2' sv1 sv2 t2))
    | tstring => False
    | tint => False
    | tauth => False
  end.

  Definition subeq_obj_bin (v1 v2 sv1 sv2 : val) :=
    (∃ t, sub_obj_bin v1 v2 sv1 sv2 t) ∨ (v1 = sv1 ∧ v2 = sv2).

  Lemma subeq_obj_bin_trans (v1 v2 sv1 sv2 ssv1 ssv2 : val) :
    subeq_obj_bin v1 v2 sv1 sv2 → subeq_obj_bin sv1 sv2 ssv1 ssv2 → subeq_obj_bin v1 v2 ssv1 ssv2.
  Proof. Admitted.
    
  Lemma subeq_obj_bin_to_unary (v1 v2 sv1 sv2 : val) :
    subeq_obj_bin v1 v2 sv1 sv2 → subeq_obj v1 sv1 ∧ subeq_obj v2 sv2.
  Proof. Admitted. *)
                                                        
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

  #[global] Instance val_eq_persistent t v1 v2 : Persistent (val_eq t v1 v2).
  Proof. revert v1 v2. induction t => v1 v2; simpl; apply _. Qed.

  Lemma val_eq_sym t v1 v2 :
    val_eq t v1 v2 ⊣⊢ val_eq t v2 v1.
  Proof. Admitted.

  Lemma val_eq_trans t1 t2 v1 v2 v3 :
    val_eq t1 v1 v2 ∗ val_eq t2 v2 v3 -∗ val_eq t1 v1 v3.
  Proof. Admitted.

  Lemma val_eq_inj_t t1 t2 v1 v2 :
    val_eq v1 v2 t1 ∗ val_eq v1 v2 t2 -∗ ⌜t1 = t2⌝.
  Proof. Admitted.

  (* Lemma sub_obj_bin_val_eq_agree_t (v1 v2 sv1 sv2 : val) (t1 t2 : evi_type) :
    ⌜sub_obj_bin v1 v2 sv1 sv2 t1⌝ ∗ val_eq t2 v1 v2 -∗ ⌜t1 = t2⌝.
  Proof.
    iIntros "[%Hbinsub #Heq]".
    destruct t1, t2; simpl in Hbinsub; iSimpl in "Heq".
  Admitted.

  Lemma val_eq_sub_eq (v1 v2 sv1 sv2 : val) (t : evi_type) :
    ⌜subeq_obj_bin v1 v2 sv1 sv2⌝ ∗ val_eq t v1 v2 -∗ ∃ st, val_eq st sv1 sv2.
  Proof.
    iInduction t as [| | | |]
                      forall (v1 v2 sv1 sv2);
                             iIntros "[%Hbinsubeq #Heq]";
                             simpl in Hbinsubeq.
      - destruct Hbinsubeq as [[t Hbinsub]|Hbineq];
          iPoseProof "Heq" as (?????) "(#Heq1 & #Heq2)"; last first.
        { destruct! H. destruct! Hbineq. simplify_eq.
          iExists (tprod t1 t2). by iFrame "#". }
        destruct! H. simplify_eq.
        iPoseProof (sub_obj_bin_val_eq_agree_t with "[$Heq //]") as "->".
        destruct Hbinsub as (?&?&?&? & ?&? & [[-> ->]|[[-> ->]|[Hbinsub1|Hbinsub2]]]).
        + simplify_eq. iFrame "#".
        + simplify_eq. iFrame "#".
        + simplify_eq. iApply "IHt1". iFrame "#".
          iPureIntro. left. eauto.
        + simplify_eq. iApply "IHt2". iFrame "#".
          iPureIntro. left. eauto.
      - destruct Hbinsubeq as [[t Hbinsub]|Hbineq]; last first;
          iPoseProof "Heq" as (??) "[(% & Heq1)|(% & Heq2)]".
        { destruct! Hbineq. destruct! H. simplify_eq.
          iExists (tsum t1 t2). iExists _, _.
          iLeft. iFrame "#". eauto. }
        { destruct! Hbineq. destruct! H. simplify_eq.
          iExists (tsum t1 t2). iExists _, _.
          iRight. iFrame "#". eauto. }
        + iPoseProof (sub_obj_bin_val_eq_agree_t with "[$Heq //]") as "->".
          destruct Hbinsub as (?&? & [(-> & -> & Hbinsub1)|(-> & -> & Hbinsub2)]);
            destruct! H; simplify_eq.
          iApply "IHt1". iFrame "#".
          iPureIntro. left. eauto.
        + iPoseProof (sub_obj_bin_val_eq_agree_t with "[$Heq //]") as "->".
          destruct Hbinsub as (?&? & [(-> & -> & Hbinsub1)|(-> & -> & Hbinsub2)]);
            destruct! H; simplify_eq.
          iApply "IHt2". iFrame "#".
          iPureIntro. left. eauto.
      - destruct Hbinsubeq as [[t Hbinsub]|Hbineq]; last first.
        { destruct! Hbineq. simplify_eq. iFrame "#". }
        by iPoseProof (sub_obj_bin_val_eq_agree_t with "[$Heq //]") as "->".
      - destruct Hbinsubeq as [[t Hbinsub]|Hbineq]; last first.
        { destruct! Hbineq. simplify_eq. iFrame "#". }
        by iPoseProof (sub_obj_bin_val_eq_agree_t with "[$Heq //]") as "->".
      - destruct Hbinsubeq as [[t Hbinsub]|Hbineq]; last first.
        { destruct! Hbineq. simplify_eq. iFrame "#". }
        by iPoseProof (sub_obj_bin_val_eq_agree_t with "[$Heq //]") as "->".
  Qed.

  Lemma sub_obj_susp_in (v : val) (susp : loc) (pid : nat) (t : evi_type) :
    ⌜sub_obj v (InjRV (InjRV #susp)) t⌝ ∗ susp ↦{#1/4} (InjLV #pid) -∗ susp_in_v t v susp.
  Proof. Admitted.

  #[global] Instance susp_in_v_timeless t v l: Timeless (susp_in_v t v l).
  Proof. revert v l; induction t => v l; simpl; apply _. Qed.

  Lemma count_gt0 (t : evi_type) (v : val) (susp : loc) (c : nat) :
    susp_in_v t v susp ∗ count_is_correct t v c -∗ ⌜c > 0⌝ ∗ susp_in_v t v susp ∗ count_is_correct t v c.
  Proof.
    iIntros "[Hin Hcount]".
    iInduction t as [| | | |] forall (v c).
    - iDestruct "Hin" as (???) "[Hin|Hin]";
        iDestruct "Hcount" as (????[??]) "(Hcount1 & Hcount2)";
        simplify_eq.
      + iPoseProof ("IHt1" with "Hin Hcount1") as "(%&Hin1&Hcount1)".
        iFrame. iSplit; [|eauto]. iPureIntro. lia.
      + iPoseProof ("IHt2" with "Hin Hcount2") as "(%&Hin2&Hcount2)".
        iFrame. iSplit; [|eauto]. iPureIntro. lia.
    - iDestruct "Hin" as (?) "[(%&Hin)|(%&Hin)]";
        iDestruct "Hcount" as "[(%&%&Hcount)|(%&%&Hcount)]";
        simplify_eq.
      + iPoseProof ("IHt1" with "Hin Hcount") as "(%&Hin&Hcount)".
        iSplit; [done|]. iSplitL "Hin".
        { iExists _. iLeft. eauto. }
        { iLeft. eauto. }
      + iPoseProof ("IHt2" with "Hin Hcount") as "(%&Hin&Hcount)".
        iSplit; [done|]. iSplitL "Hin".
        { iExists _. iRight. eauto. }
        { iRight. eauto. }
    - done.
    - done.
    - iDestruct "Hin" as (?[??]) "Hin";
        iDestruct "Hcount" as (??) "[(%&%&%)|(%&%&Hcount)]";
        simplify_eq.
      iDestruct "Hin" as "[(% & Hin)|Hin]";
        iDestruct "Hcount"  as "[(%&Hcount&%)|(%&Hcount&%)]";
        eauto; simplify_eq.
      + by iPoseProof (pointsto_agree with "Hin Hcount") as "%Hf".
      + iSplit; [iPureIntro; lia|].
        iSplitL "Hin".
        { iExists _. eauto. }
        { iExists _. iSplit; [done|].
          iRight. iExists _. iSplit; [done|]. iRight. eauto. }
  Qed. *)
    
  (* Lemma count_update (v : val) (t : evi_type) (susp : loc) (c : nat) (h : string):
    susp ↦□ InjRV #h -∗ susp_in_v t v susp -∗ count_is_correct t v c -∗ count_is_correct t v (c-1).
  Proof.
    iIntros "#Hsusp Hin Hcount".
    iPoseProof (count_gt0 with "[$Hin $Hcount]") as "(%Hc&Hin&Hcount)".
    iInduction t as [| | | |] forall (v c Hc).
    - iDestruct "Hcount" as (????[??]) "(Hcount1 & Hcount2)".
      iDestruct "Hin" as (v1' v2' ?)  "[Hin|Hin]"; simplify_eq.
      + iPoseProof (count_gt0 with "[$Hin $Hcount1]") as (?) "[Hin Hcount1]".
        iPoseProof ("IHt1" with "[//] Hin Hcount1") as "Hcount1'".
        iFrame "∗ #". iPureIntro. split; [done|lia].
      + iPoseProof (count_gt0 with "[$Hin $Hcount2]") as (?) "[Hin Hcount2]".
        iPoseProof ("IHt2" with "[//] Hin Hcount2") as "Hcount2'".
        iFrame "∗ #". iPureIntro. split; [done|lia].
    - iDestruct "Hin" as (?) "[(%&Hin)|(%&Hin)]";
        iDestruct "Hcount" as "[(%&%&Hcount)|(%&%&Hcount)]";
        simplify_eq.
      + iPoseProof ("IHt1" with "[//] Hin Hcount") as "Hcount'".
        iFrame. iLeft. eauto.
      + iPoseProof ("IHt2" with "[//] Hin Hcount") as "Hcount'".
        iFrame. iRight. eauto.
    - done.
    - done.
    - iDestruct "Hin" as (?[??]) "Hin";
        iDestruct "Hcount" as (??) "[(%&%&%)|(%&%&Hcount)]";
        simplify_eq.
      iDestruct "Hin" as "[Hin|Hin]";
        iDestruct "Hcount" as "[(%&Hinvc'&%)|(Hinvc'&%)]";
        simplify_eq; try lia.
      + iExists _. iSplit; [done|].
        iRight. iExists _. iSplit; [done|]. eauto.
      + iExFalso. by iApply "Hin".
  Qed. *)

  Definition proph_susp (p : proph_id) (h : string) : iProp Σ :=
    (typed_proph1_prop StringTypedProph) p h.
                                             
  Definition auth_is_ser_1 (v : val) (s : string) : iProp Σ :=
    ∃ (h : string), ⌜v = InjLV #h⌝ ∗ s_is_ser (g:=gwp_upto_bad) auth_scheme (SOMEV #h) s.

  Definition auth_is_ser_2 (s : string) (susp : loc) : iProp Σ :=
    ∃ (h : string), susp ↦□ InjRV #h ∗ 
      s_is_ser (g:=gwp_upto_bad) auth_scheme (SOMEV #h) s.

  Definition auth_is_ser_3 (s : string) (susp : loc) : iProp Σ :=
    ∃ (pid: nat) (p : proph_id) (h : string),
      susp ↦ InjLV (#pid, #p) ∗ proph_susp p h ∗
        s_is_ser (g:=gwp_upto_bad) auth_scheme NONEV s.

  Definition auth_is_ser_3_proph (s : string) (susp : loc) : iProp Σ :=
    ∃ (pid: nat) (p : proph_id) (h : string),
      susp ↦ InjLV (#pid, #p) ∗ proph_susp p h ∗
        s_is_ser (g:=gwp_upto_bad) auth_scheme (SOMEV #h) s.

  Definition auth_ser_inv (s : string) (susp : loc) : iProp Σ :=
    auth_is_ser_2 s susp ∨ auth_is_ser_3_proph s susp.
  
  (* Definition auth_is_ser (v : val) (s : string) : iProp Σ :=
    auth_is_ser_1 v s ∨ auth_is_ser_2 v s. *)

  (* Definition auth_valid_val_2 (susp : loc) : iProp Σ :=
    ∃ (h : string) (t : evi_type) (ax avᵥ : val),
      susp ↦□ InjRV #h ∗
        ((∃ aid, single_instance aid t ax avᵥ None true ∗ val_eq t ax avᵥ)  (* Most recent pre-filled ancestor *)
         -∗ (∃ vᵥ, (∃ px pvᵥ, ⌜subeq_obj_bin px pvᵥ (SOMEV (InjRV #susp)) vᵥ⌝) -∗ val_eq tauth (SOMEV (InjRV #susp)) vᵥ)).                         
  Definition auth_valid_val_3 (susp : loc) (dq : dfrac) : iProp Σ :=
    (∃ (pid : nat) (p : proph_id) (pt t : evi_type) (px pvᵥ ax avᵥ : val),
        susp ↦{dq} (InjLV #pid) ∗
          ((∃ b so, single_instance pid pt px pvᵥ so b) -∗ susp_in_v pt px susp) ∗ (* Parent's instance *)
          ((∃ aid, single_instance aid t ax avᵥ None true ∗ val_eq t ax avᵥ )  (* Most recent pre-filled ancestor *)
           -∗ (∃ vᵥ, ⌜subeq_obj_bin px pvᵥ (SOMEV (InjRV #susp)) vᵥ⌝ -∗ val_eq tauth (SOMEV (InjRV #susp)) vᵥ))).

  Definition valid_auth_inv (susp : loc) : iProp Σ :=
    (auth_valid_val_2 susp ∨ auth_valid_val_3 susp (DfracOwn (1/2))).

  Definition auth_valid_val (v1 : val) : iProp Σ :=
    ∃ v, ⌜v1 = SOMEV v⌝ ∧
           ((∃ (h : string), ⌜v = InjLV #h⌝) ∨
              (∃ (susp : loc),
                  ⌜v = InjRV #susp⌝ ∗ seq_inv (authValidN #susp) (valid_auth_inv susp))).

  Definition auth_deser_valid_val (dq : dfrac) (v1 : val) : iProp Σ :=
    ∃ v, ⌜v1 = SOMEV v⌝ ∧
           ((∃ (h : string), ⌜v = InjLV #h⌝) ∨
              (∃ (susp : loc),
                  ⌜v = InjRV #susp⌝ ∗ auth_valid_val_3 susp dq)). *)

  (* Definition auth_deser_valid_val_tok (v1 : val) : iProp Σ :=
    ∃ v, ⌜v1 = SOMEV v⌝ ∧
           ((∃ (h : string), ⌜v = InjLV #h⌝) ∨
              (∃ (susp : loc),
                  ⌜v = InjRV #susp⌝ ∗
                    (∃ (pid : nat), susp ↦ (InjLV #pid) ∗ token pid))). *)
             
  
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
    | tauth => ∃ v1, ⌜v = SOMEV v1⌝ ∗ (auth_is_ser_1 v1 s ∨ 
                                        (∃ (susp : loc), ⌜v1 = InjRV #susp⌝ ∗ auth_is_ser_3 s susp))
    end.

  Fixpoint s_is_ser'' (t : evi_type) (v : val) (s : string) : iProp Σ :=
    match t with
    | tprod t1 t2 => prod_is_ser' v s (s_is_ser'' t1) (s_is_ser'' t2)
    | tsum t1 t2 => sum_is_ser' v s (s_is_ser'' t1) (s_is_ser'' t2)
    | tstring => string_is_ser v s
    | tint => int_is_ser v s
    | tauth => ∃ v1, ⌜v = SOMEV v1⌝ ∗ (auth_is_ser_1 v1 s ∨ 
                                        (∃ (susp : loc), ⌜v1 = InjRV #susp⌝ ∗ auth_is_ser_2 s susp))
  end.

  Fixpoint s_is_ser_proph (t : evi_type) (v : val) (s : string) : iProp Σ :=
    match t with
    | tprod t1 t2 => prod_is_ser' v s (s_is_ser_proph t1) (s_is_ser_proph t2)
    | tsum t1 t2 => sum_is_ser' v s (s_is_ser_proph t1) (s_is_ser_proph t2)
    | tstring => string_is_ser v s
    | tint => int_is_ser v s
    | tauth => ∃ v1, ⌜v = SOMEV v1⌝ ∗
                       (auth_is_ser_1 v1 s ∨
                          (∃ (susp : loc), ⌜v1 = InjRV #susp⌝ ∗ 
                            seq_inv (authSerProofN N #susp) (auth_ser_inv s susp)))
  end.

  #[global] Instance s_is_ser_proph_persistent t v s : Persistent (s_is_ser_proph t v s).
  Proof. revert v s. induction t => v s; simpl; apply _. Qed.

  (* Fixpoint s_valid_val (t: evi_type) (v: val) : iProp Σ :=
    match t with
    | tprod t1 t2 => prod_valid_val' v (s_valid_val t1) (s_valid_val t2)
    | tsum t1 t2 => sum_valid_val' v (s_valid_val t1) (s_valid_val t2)
    | tstring => string_valid_val v
    | tint => int_valid_val v
    | tauth => auth_valid_val v
    end.

  #[global] Instance s_valid_val_persistent t v : Persistent (s_valid_val t v).
  Proof. revert v. induction t => v; simpl; apply _. Qed.

  Fixpoint s_deser_valid_val (dq : dfrac) (t : evi_type) (v : val) : iProp Σ :=
    match t with
    | tprod t1 t2 => prod_valid_val' v (s_deser_valid_val dq t1) (s_deser_valid_val dq t2)
    | tsum t1 t2 => sum_valid_val' v (s_deser_valid_val dq t1) (s_deser_valid_val dq t2)
    | tstring => string_valid_val v
    | tint => int_valid_val v
    | tauth => auth_deser_valid_val dq v
    end.

  Definition s_deser_valid_val_bef := s_deser_valid_val (DfracOwn (3/4)).

  Definition s_deser_valid_val_aft := s_deser_valid_val (DfracOwn (1/2)). *)

  (* Fixpoint s_deser_valid_val_tok (t : evi_type) (v : val) : iProp Σ :=
    match t with
    | tprod t1 t2 => prod_valid_val' v (s_deser_valid_val t1) (s_deser_valid_val t2)
    | tsum t1 t2 => sum_valid_val' v (s_deser_valid_val t1) (s_deser_valid_val t2)
    | tstring => string_valid_val v
    | tint => int_valid_val v
    | tauth => auth_deser_valid_val_tok v
    end. *)

  (* #[global] Instance s_valid_val_persistent t v: Persistent (s_valid_val t v).
  Proof. revert v; induction t => v; simpl; apply _. Qed. *)

  #[global] Instance s_is_ser''_persistent t v s: Persistent (s_is_ser'' t v s).
  Proof. revert v s; induction t => v s; simpl; apply _. Qed.

  (* Fixpoint susp_list (t : evi_type) (v : val) (susp_l : list loc) : iProp Σ :=
    match t with
    | tprod t1 t2 =>
        ∃ v1 v2 susp_v1 susp_v2,
          ⌜v = (v1, v2)%V ∧ susp_l = susp_v1 ++ susp_v2⌝ ∗ susp_list t1 v1 susp_v1 ∗ susp_list t2 v2 susp_v2
    | tsum t1 t2 =>
        ∃ v',
          (⌜v = InjLV v'⌝ ∗ susp_list t1 v' susp_l) ∨ (⌜v = InjRV v'⌝ ∗ susp_list t2 v' susp_l) 
    | tstring => ∃ (s: string), ⌜v = #s ∧ susp_l = []⌝
    | tint => ∃ (i: nat), ⌜v = #i ∧ susp_l = []⌝
    | tauth =>
        (∃ v', ⌜v = SOMEV v'⌝ ∧
                 ((∃ (h : string), ⌜v' = InjLV #h ∧ susp_l = []⌝) ∨ 
                    (∃ (susp : loc), ⌜v' = InjRV #susp ∧ susp_l = [susp]⌝)))
    end. *)

  (* ((∃ b so, single_instance pid pt px pvᵥ so b) -∗ susp_in_v pt px susp) ∗ (* Parent's instance *)
                          ((∃ aid ax avᵥ t, single_instance aid t ax avᵥ None true ∗ val_eq t ax avᵥ) -∗ (* Most recent pre-filled ancestor *)
                             (∃ aid cx cvᵥ ct, single_instance aid ct cx cvᵥ (Some susp) false -∗ val_eq ct cx cvᵥ)) *)
  
  (* Lemma deser_valid :
    ∀ ct v vᵥ s ax avᵥ t px pvᵥ pt,
      ⌜subeq_obj_bin px pvᵥ v vᵥ ⌝ -∗ □(val_eq t ax avᵥ -∗ val_eq pt px pvᵥ) -∗ s_is_ser_deser ct v s -∗ s_deser_valid_val_bef ct v.
  Proof.
    iIntros (??????????) "%Hsubeqbin #Heq_trans Hser".
    pose proof (subeq_obj_bin_to_unary _ _ _ _ Hsubeqbin) as [Hsubeqx Hsubeqv].
    iInduction ct as [| | | |] forall (v vᵥ s Hsubeqx Hsubeqv Hsubeqbin); iSimpl; iSimpl in "Hser".
    - iDestruct "Hser" as (????) "((-> & ->) & H1 & H2)".
      assert (H1: subeq_obj (v1, v2) v1).
      { left. eexists (tprod ct1 ct2).
        exists v1, v2. eauto. }
      assert (H1': subeq_obj px v1).
      { by apply (subeq_obj_trans px (v1, v2) v1). }
      assert (H2: subeq_obj (v1, v2) v2).
      { left. eexists (tprod ct1 ct2).
        exists v1, v2. eauto. }
      assert (H2': subeq_obj px v2).
      { by apply (subeq_obj_trans px (v1, v2) v2). }
      iPoseProof ("IHct1" with "[] [] [] H1") as "H1"; [done|done|admit| ].
      iPoseProof ("IHct2" with "[] [] [] H2") as "H2"; [done|done|admit| ].
      iExists v1, v2. by iFrame.
    - iDestruct "Hser" as (??) "[(H & %)|(H & %)]".
      + destruct H as [-> _]. iExists _. iLeft. iSplit; first done.
        iPoseProof ("IHct1" with "[] [] [] H") as "H"; admit.
      + destruct H as [-> _]. iExists _. iRight. iSplit; first done.
        iPoseProof ("IHct2" with "[] [] [] H") as "H"; admit.
    - iDestruct "Hser" as "%Hser". destruct Hser as (? & -> & _). iExists _. done.
    - iDestruct "Hser" as "%Hser". destruct Hser as (? & -> & _). iExists _. done.
    - iDestruct "Hser" as (? ->) "[(% & -> & Hser)|(%&% & -> & Hsusp & Hser)]".
      + iExists _. iSplit; [done|].
        iLeft. eauto.
      + iExists _. iSplit; [done|].
        iRight. iExists _. iSplit; [done|].
        iDestruct (fractional_split _ (λ q, susp ↦{DfracOwn q} InjLV #pid)%I (3/4) (1/4) with "Hsusp") as "[Hsusp1 Hsusp2]".
        { admit. }
        iExists pid.
        destruct Hsubeqx as [[ct Hsub]|Heq]; last first.
        * iExists tauth, t, px, pvᵥ, ax, avᵥ. iFrame. iSplitL.
          { iIntros "_". iExists _. iSplit; eauto. }
          iIntros "(%ancid & _ & Hanceq)".
          iExists vᵥ. iIntros "_".
          iPoseProof ("Heq_trans" with "Hanceq") as "#Hpeq".
          iPoseProof (val_eq_sub_eq with "[$Hpeq //]") as "#Heq".
          iDestruct "Heq" as (?) "Heq".
          destruct st.
          { by iDestruct "Heq" as (????[? ->]) "_". }
          { iDestruct "Heq" as (??) "[([%  %] & _)|([%  %] & Heq)]"; try done.
            simplify_eq.
            destruct st2.
            { by iDestruct "Heq" as (????[? ->]) "_". }
            { iDestruct "Heq" as (??) "[([%  %] & _)|([%  %] & Heq)]"; try done.
              simplify_eq.
              destruct st2_2; iSimpl in "Heq".
              { by iDestruct "Heq" as (????[? ->]) "_". }
              { by iDestruct "Heq" as (??) "[([%  %] & _)|([%  %] & Heq)]". }
              { by iDestruct "Heq" as (?) "[% %]". }
              { by iDestruct "Heq" as (?) "[% %]". }
              { admit. } }
            { by iDestruct "Heq" as (?) "[% %]". }
            { by iDestruct "Heq" as (?) "[% %]". }
            { iDestruct "Heq" as "[[% %]|(% & H)]"; try done.
              admit. } }
          { by iDestruct "Heq" as (?) "[% %]". }
          { by iDestruct "Heq" as (?) "[% %]". }
          { iFrame "#". }
        * iExists pt, t, px, pvᵥ, ax, avᵥ. iFrame. iSplitL.
          { iIntros "_". iApply (sub_obj_susp_in with "[$Hsusp2]"). admit. }
          iIntros "Heq". iDestruct "Heq" as (?) "[_ Hanceq]".
          iPoseProof ("Heq_trans" with "Hanceq") as "#Hpeq".
          iPoseProof (val_eq_sub_eq with "[$Hpeq //]") as "#Heq".
          iExists vᵥ. iIntros "_".
          iDestruct "Heq" as (?) "Heq".
          destruct st.
          { by iDestruct "Heq" as (????[? ->]) "_". }
          { iDestruct "Heq" as (??) "[([%  %] & _)|([%  %] & Heq)]"; try done.
            simplify_eq.
            destruct st2.
            { by iDestruct "Heq" as (????[? ->]) "_". }
            { iDestruct "Heq" as (??) "[([%  %] & _)|([%  %] & Heq)]"; try done.
              simplify_eq.
              destruct st2_2; iSimpl in "Heq".
              { by iDestruct "Heq" as (????[? ->]) "_". }
              { by iDestruct "Heq" as (??) "[([%  %] & _)|([%  %] & Heq)]". }
              { by iDestruct "Heq" as (?) "[% %]". }
              { by iDestruct "Heq" as (?) "[% %]". }
              { admit. } }
            { by iDestruct "Heq" as (?) "[% %]". }
            { by iDestruct "Heq" as (?) "[% %]". }
            { iDestruct "Heq" as "[[% %]|(% & H)]"; try done.
              admit. } }
          { by iDestruct "Heq" as (?) "[% %]". }
          { by iDestruct "Heq" as (?) "[% %]". }
          { iFrame "#". }
  Admitted. *)
      
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
             iDestruct "Ht2" as (?->) "[(% & -> & Ht2)|(%& ->& %& #Hloc & Ht2)]"; iFrame.
             { iDestruct "Ht2" as "[(% & %)|(% & % & (% & %) & (% & -> & ->))]"; [done|].
               simplify_eq. iRight. iExists _. iSplit; iLeft; eauto. }            
             iRight. iExists _. iSplit.
             { iLeft. eauto. }
             iDestruct "Ht2" as "[(% & %)|(% & % & (% & %) & (% & % & %))]"; simplify_eq.
             iRight. iExists _. eauto.
        * iDestruct "Ht1" as (?->?) "(Hloc & Ht1)".
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
             iDestruct "Ht2" as (?->) "[(% & -> & Ht2)|(%& -> & %& #Hloc1 & Ht2)]"; iFrame.
             { iDestruct "Ht2" as "[(% & %)|(% & % & (% & %) & (% & -> & ->))]"; [done|].
               simplify_eq. iRight. iExists _. iSplit; [iRight|iLeft]; eauto. }
             iRight. iExists _. iSplit.
             { iRight. eauto. }
             iRight. iExists _. iSplit; first done.
             iDestruct "Ht2" as "[(% & %)|(% & % & (% & %) & (% & % & %))]"; by simplify_eq.
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
             iDestruct "Ht2" as (?->) "[(% & -> & Ht2)|(%& ->& %& #Hloc & Ht2)]"; iFrame.
             { iDestruct "Ht2" as "[(% & %)|(% & % & (% & %) & (% & -> & ->))]"; [done|].
               simplify_eq. iRight. iExists _. iSplit; iLeft; eauto. }            
             iRight. iExists _. iSplit.
             { iLeft. eauto. }
             iDestruct "Ht2" as "[(% & %)|(% & % & (% & %) & (% & % & %))]"; simplify_eq.
             iRight. iExists _. eauto.
        * iDestruct "Ht1" as (? -> ???) "(Hloc & Hproph & Ht1)".
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
             iDestruct "Ht2" as (?->) "[(% & -> & Ht2)|(%& -> & %& #Hloc1 & Ht2)]"; iFrame;
               iDestruct "Ht2" as "[(% & %)|(% & % & (% & %) & (% & -> & ->))]"; done.
  Admitted.

  (* Lemma deser_valid_weak :
    ∀ t v, s_deser_valid_val_aft t v ⊢ |={⊤}=> s_valid_val t v.
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
    - iDestruct "Hdvalid" as (? ->) "[(% & ->)|(%&-> & %&%&%&%&%&%&% & Hsusp & Hsuspin & Heq)]".
      + iExists _. iModIntro. iSplit; [done|].
        iLeft. eauto.
      + iExists _.
        iMod (na_inv_alloc seqG_name _ (authValidN #susp) (valid_auth_inv susp) with "[Hsusp Hsuspin Heq]") as "Hinv".
        { iNext. iRight. iFrame. }
        iModIntro.
        iSplit; [done|].
        iRight. eauto.
  Qed. *)
        
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
  
  (* Fixpoint evi_type_count (t : evi_type) : expr :=
    match t with
    | tprod t1 t2 => prod_count (evi_type_count t1) (evi_type_count t2)
    | tsum t1 t2 => sum_count (evi_type_count t1) (evi_type_count t2)
    | tstring => string_count
    | tint => int_count
    | tauth => auth_count
    end. *)

  (* Definition count_auth_inv (susp: loc) (c: nat) : iProp Σ :=
     ((∃ (h : string), susp ↦□ (InjRV #h) ∗ ⌜c = 0⌝) ∨
        (∃ (pid : nat), susp ↦ (InjLV #pid) ∗ ⌜c = 1⌝)). *)

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

  (* Definition count_update (t : evi_type) : iProp Σ :=
    ∀ (v : val) (susp : loc) (c pid : nat) (h : string),
      {{{ susp ↦{#1/2} InjLV #pid ∗ susp_in_v t v susp ∗ count_is_correct t v c }}}
        #susp <- InjR #h
        {{{ RET #(); count_is_correct t v (c-1) ∗ susp ↦□ InjRV #h }}}. *)
                                                 
  Definition ser_spec_3 (ser : val) (t : evi_type) : iProp Σ :=
    ∀ (v1 : val) (s : string) E,
      ⌜↑authSerProofSet N ⊆ E⌝ -∗
      {{{ ▷ (s_is_ser_proph t v1 s ∗ seq_tok E) }}}
        ser v1
        {{{ o, RET $o; seq_tok E ∗ if o is Some s then s_is_ser'' t v1 s else True }}}.
        
                                                 
  (* Definition ser_spec_2 (ser : val) (t : evi_type) : iProp Σ :=
    ∀ (v1 : val),
      {{{ ▷ (s_valid_val t v1 ∗ seq_tok ⊤) }}}
        ser v1
        {{{ o, RET $o; seq_tok ⊤ ∗ if o is Some s then s_is_ser'' t v1 s else True }}}. *)
  
  Definition ser_spec_un (A : lrel_un Σ) (ser : val) (t : evi_type) : iProp Σ :=
    ∀ (v : val) E,
      ⌜↑authSerProofSet N ⊆ E⌝ -∗
      {{{ ▷ (A v ∗ seq_tok E) }}}
        ser v
      {{{ o, RET $o; seq_tok E ∗ if o is Some s then s_is_ser'' t v s else True }}}.
  
  Definition ser_spec (A : lrel Σ) (ser : val) (t : evi_type) : iProp Σ :=
    ∀ (v1 v2 : val) E,
      ⌜↑authSerProofSet N ⊆ E⌝ -∗
      {{{ ▷ (A v1 v2 ∗ seq_tok E) }}}
        ser v1
      {{{ o, RET $o; seq_tok E ∗ if o is Some s then s_is_ser'' t v1 s else True }}}.

  (* Pass single_instance through here, and set it in s_is_ser_deser. Or maybe do it in count. *)
  Definition deser_spec (deser : val) (t : evi_type) : iProp Σ :=
    ∀ (pid : nat),
      {{{ True }}}
      deser #pid
      {{{ (deser_partial : val), RET deser_partial;
          ∀ (s : string),
            {{{ True }}}
              deser_partial #s
              {{{ o, RET $o;
                  if o is Some v then
                    s_is_ser_deser t v s (*∗ (∃ s', s_is_ser_proph t v s') *)
                  else True }}}
      }}}.
  
  (* Definition deser1_spec (deser_partial : val) (t : evi_type) : iProp Σ :=
    ∀ (s : string),
      ({{{ True }}}
         deser_partial #s
      {{{ o, RET $o; if o is Some v then s_is_ser_deser t v s else True }}}). *)

  Definition count_spec (count : val) (t : evi_type) : iProp Σ :=
    ∀ (x : val) (s : string) E,
      ⌜↑authSerProofSet N ⊆ E⌝ -∗
      {{{ ▷ (s_is_ser_proph t x s ∗ seq_tok E) }}}
        count x
        {{{ (c : nat), RET #c; seq_tok E }}}.

  Definition val_eq_rel (A : lrel Σ) (t: evi_type) : iProp Σ :=
    ∀ (a1 a2 b1: val) (E : coPset),
      ⌜↑authSerProofSet N ⊆ E⌝ →
      □ (seq_tok E ∗ val_eq t a1 a2 ∗ A a1 b1 ={⊤}=∗ A a2 b1 ∗ seq_tok E).

  Definition lrel_un_evidence' (A : lrel_un Σ) : lrel_un Σ :=
    LRelUn (λ v,
        ∃ (t : evi_type) (ser deser count : val),
          ⌜v = (ser, deser, count)%V⌝ ∗ ser_spec_un A ser t ∗ ser_spec_3 ser t ∗
            count_spec count t ∗ deser_spec deser t)%I.
  
  Definition lrel_bin_evidence' (A : lrel Σ) : lrel Σ :=
    LRel (λ v1 v2,
        ∃ (t : evi_type) (ser deser count : val),
          ⌜v1 = (ser, deser, count)%V⌝ ∗ ser_spec A ser t ∗ ser_spec_3 ser t ∗
            count_spec count t ∗ deser_spec deser t ∗ val_eq_rel A t)%I.

  Definition lrel_bi_evidence' (A : lrel_bi Σ) : lrel_bi Σ :=
    LRelBi (lrel_un_evidence' (lrel_bi_un A))
      (lrel_bin_evidence' (lrel_bi_bin A)).

  Program Definition lrel_evidence : kindO Σ (⋆ ⇒ ⋆)%kind := λne A, lrel_bi_evidence' A.
  Next Obligation.
    intros ????.
    rewrite /lrel_bi_evidence' /=.
    split; [intros ?|intros ??];
      rewrite /lrel_car/= /lrel_un_car/= /ser_spec_un /ser_spec /count_spec /deser_spec /val_eq_rel;
      solve_proper.
  Qed.

  Lemma prod_ser'_spec_ser (HA HB : val → iProp Σ) (tA tB : evi_type) (serA serB v vA vB : val) :
    ∀ E,
    (▷ ⌜v = (vA, vB)%V⌝) -∗
    ({{{ ▷ (HA vA ∗ seq_tok E) }}}
       serA vA
       {{{ o, RET $o; seq_tok E ∗ if o is Some s then s_is_ser'' tA vA s else True }}}) -∗
    ({{{ ▷ (HB vB ∗ seq_tok E) }}}
       serB vB
       {{{ o, RET $o; seq_tok E ∗ if o is Some s then s_is_ser'' tB vB s else True }}}) -∗
    {{{ ▷ (prod_valid_val' v HA HB ∗ seq_tok E) }}}
    prod_ser''' serA serB v
    {{{ o, RET $o; seq_tok E ∗ if o is Some s then prod_is_ser' v s (s_is_ser'' tA) (s_is_ser'' tB) else True }}}.
  Proof.
    iIntros (?) "#Hv #HA #HB % !# (Hp & Htok) HΦ".
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
    iIntros "(Hotk & HserB)".
    wp_pures.
    iApply ("HΦ" $! (Some _)).
    iModIntro. iFrame. eauto.
  Qed.
  
End authenticatable.

Section proof.
  Context `{!stateG Σ, !authG Σ, !seqG Σ} (N : namespace).

  Lemma refines_un_Auth_pair Θ (Δ : ctxO Σ Θ) (A B : kindO Σ ⋆) serA serB deserA deserB countA countB :
    lrel_bi_un (lrel_evidence N A) (serA, deserA, countA)%V -∗
    lrel_bi_un (lrel_evidence N B) (serB, deserB, countB)%V -∗
    lrel_bi_un (⟦ var2 (var1 * var0)%ty ⟧ (ext (ext (ext Δ (lrel_evidence N)) A) B))
      (prod_ser''' serA serB, λ: "pid", prod_deser (deserA "pid") (deserB "pid"), λ: "v", countA (Fst "v") + countB (Snd "v"))%V.
  Proof.
    iIntros "HA_un HB_un".
    rewrite /prod_ser''' /prod_deser.
    iDestruct "HA_un" as (tA_un serA_un deserA_un countA_un ?) "(#HserA_un & #Hser3A_un & #HcountA_un & #HdeserA_un)".
    iDestruct "HB_un" as (tB_un serB_un deserB_un countB_un ?) "(#HserB_un & #Hser3B_un & #HcountB_un & #HdeserB_un)".
    iEval (rewrite interp_app_unfold; interp_unfold_tac).
    iExists (tprod tA_un tB_un), _, _, _. simplify_eq.
    iSplit; [done|]. clear. iSplit; [|iSplit; [|iSplit]].
    + iIntros (v ???) "!# (Hp & Htok) H". rewrite interp_un_prod_unfold.
      iDestruct "Hp" as (w u) "(>-> & #HA & #HB)".
      rewrite interp_tvar_unfold. iSimpl in "HA".
      rewrite interp_tvar_unfold. iSimpl in "HB".
      iSimpl in "H".
      wp_apply (prod_ser'_spec_ser (λ v, lrel_bi_un A v) (λ v, lrel_bi_un B v) with "[] [] [] [$Htok]") => /=; [done| | | |done].
      { iIntros (?) "!# Hp H". by wp_apply ("HserA_un" with "[//] Hp"). }
      { iIntros (?) "!# Hp H". by wp_apply ("HserB_un" with "[//] Hp"). }
      iExists _, _. iModIntro.
      eauto.
    + iIntros (v ????) "!# (Hser & Htok) H".
      iDestruct "Hser" as (????) "((>-> & >->) & HA & HB)".
      wp_apply (prod_ser'_spec_ser (λ v1, s_is_ser_proph N tA_un v1 s1) (λ v2, s_is_ser_proph N tB_un v2 s2) with "[] [] [] [HA HB $Htok]") => /=; [done| | | |done].
      { iIntros (?) "!# Hser H". by wp_apply ("Hser3A_un" with "[//] Hser"). }
      { iIntros (?) "!# Hser H". by wp_apply ("Hser3B_un" with "[//] Hser"). }
      iNext. iFrame. eauto.
    + iIntros (?????) "!# (Hser & Htok) HΨ".  wp_pures.
      iDestruct "Hser" as (????) "((-> & ->) & HA & HB)".
      wp_pures. rewrite /count_spec.
      wp_bind (countB_un _).
      wp_apply ("HcountB_un" $! v2 with "[//] [$HB $Htok]").
      iIntros (?) "Htok".
      wp_pures.
      wp_apply ("HcountA_un" $! v1 with "[//] [$HA $Htok]").
      iIntros (?) "Htok".
      simplify_eq. wp_pures. iModIntro.
      iSpecialize ("HΨ" $! (c0+c)).
      assert (#(c0 + c) = #(c0 + c)%nat).
      { by rewrite Nat2Z.inj_add. }
      rewrite H0. iApply "HΨ".
      by iFrame.
    + iIntros (pid ?) "!# _ HΨ".
      wp_pures.
      wp_apply "HdeserB_un"; [done|]. iIntros "%deparB #HdeparB".
      wp_apply "HdeserA_un"; [done|]. iIntros "%deparA #HdeparA".
      wp_pures. iModIntro. iApply "HΨ".
      iIntros (s ?) "!# _ HΨ".
      wp_apply prod_deser'_sound; try auto.
  Qed.

  Lemma refines_Auth_pair Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆; ⋆, var2 var1 → var2 var0 → var2 (var1 * var0) ⟧
      (ext Δ (lrel_evidence N)) v_Auth_pair i_Auth_pair.
  Proof.
    iSplit.
    - interp_unfold.
      iIntros (A ??) "!# _".
      iIntros (??) "(Hi & Htok)".
      rewrite /v_Auth_pair /i_Auth_pair.
      i_pures; wp_pures.
      iModIntro. iFrame.
      iSplit.
      { interp_unfold.
        iIntros (B ??) "!# _".
        iIntros (??) "(Hi & Htok)".
        i_pures; wp_pures.
        iModIntro. iFrame.
        iSplit.
        { interp_unfold.
          iIntros (??) "!# #HA".
          iEval (rewrite interp_app_unfold; interp_unfold_tac; interp_unfold_tac) in "HA".
          iDestruct "HA" as "[HA HA_un]".
          iDestruct "HA" as (tA serA deserA countA ->) "(#HserA & #Hser3A & #HcountA & #HdeserA & #HrelA)".
          clear. iIntros (??) "(Hi & Htok)".
          i_pures; wp_pures.
          iModIntro. iFrame.
          iSplit.
          { interp_unfold.
            iIntros (??) "!# #HB".
            iEval (rewrite interp_app_unfold; interp_unfold_tac; interp_unfold_tac) in "HB".
            iDestruct "HB" as "[HB HB_un]".
            iDestruct "HB" as (tB serB deserB countB ->) "(#HserB & #Hser3B & #HcountB & #HdeserB & #HrelB)".
            clear. iIntros (??) "(Hi & Htok)".
            i_pures; wp_pures. clear.
            rewrite /prod_scheme /prod_ser'' /prod_deser /prod_count.
            wp_pures. iFrame. iModIntro.
            iSplit.
            { interp_unfold!.
              iExists (tprod tA tB), _, _, _.
              iSplit; [done|]. clear. iSplit; [|iSplit; [|iSplit; [|iSplit]]].
              + iIntros (v1 v2 ???) "!# (Hp & Htok) H". interp_unfold.
                iDestruct "Hp" as (w1 w2 u1 u2) "(>-> & >-> & #HA & #HB)".
                rewrite interp_tvar_unfold. iSimpl in "HA".
                rewrite interp_tvar_unfold. iSimpl in "HB".
                iSimpl in "H".
                wp_apply (prod_ser'_spec_ser (λ v1, lrel_bi_bin A v1 w2) (λ v1, lrel_bi_bin B v1 u2) with "[] [] [] [$Htok]") => /=; [done| | | |done].  
                { iIntros (?) "!# Hp H". by wp_apply ("HserA" with "[//] Hp"). }
                { iIntros (?) "!# Hp H". by wp_apply ("HserB" with "[//] Hp"). }
                iExists _, _. iModIntro.
                eauto.
              (* - iIntros (v1 ?) "!# (Hp & Htok) H". iSimpl in "Hp".
      iDestruct "Hp" as (w1 w2) "(>-> & HA & HB)".
      wp_apply (prod_ser'_spec_ser (s_valid_val _ tA) (s_valid_val _ tB) with "[] [] [] [HA HB $Htok]") => /=; [done| | | |done].  
      { iIntros (?) "!# Hp H". by wp_apply ("Hser2A" with "Hp"). }
      { iIntros (?) "!# Hp H". by wp_apply ("Hser2B" with "Hp"). }
      iNext. iFrame. eauto. *)
              + iIntros (v ????) "!# (Hser & Htok) H".
                iDestruct "Hser" as (????) "((>-> & >->) & HA & HB)".
                wp_apply (prod_ser'_spec_ser (λ v1, s_is_ser_proph N tA v1 s1) (λ v2, s_is_ser_proph N tB v2 s2) with "[] [] [] [HA HB $Htok]") => /=; [done| | | |done].
                { iIntros (?) "!# Hser H". by wp_apply ("Hser3A" with "[//] Hser"). }
                { iIntros (?) "!# Hser H". by wp_apply ("Hser3B" with "[//] Hser"). }
                iNext. iFrame. eauto.
              + iIntros (?????) "!# (Hser & Htok) HΨ".  wp_pures.
                iDestruct "Hser" as (????) "((-> & ->) & HA & HB)".
                wp_pures. rewrite /count_spec.
                wp_bind (countB _).
                wp_apply ("HcountB" $! v2 with "[//] [$HB $Htok]").
                iIntros (?) "Htok".
                wp_pures.
                wp_apply ("HcountA" $! v1 with "[//] [$HA $Htok]").
                iIntros (?) "Htok".
                simplify_eq. wp_pures. iModIntro.
                iSpecialize ("HΨ" $! (c0+c)).
                assert (#(c0 + c) = #(c0 + c)%nat).
                { by rewrite Nat2Z.inj_add. }
                rewrite H0. iApply "HΨ".
                by iFrame.
              + iIntros (pid ?) "!# _ HΨ".
                wp_pures.
                wp_apply "HdeserB"; [done|]. iIntros "%deparB #HdeparB".
                wp_apply "HdeserA"; [done|]. iIntros "%deparA #HdeparA".
                wp_pures. iModIntro. iApply "HΨ".
                iIntros (s ?) "!# _ HΨ".
                wp_apply prod_deser'_sound; try auto.
              (* iIntros ([]); last first.
      { iIntros "_". by iApply ("HΨ" $! None). }
      iIntros "(%&%&%&%&[-> ->] & (Hsera & (% & Hserpa)) & Hserb & (% & Hserpb))".
      iApply ("HΨ" $! (Some _)). iFrame. eauto. *)
              + iIntros (?????) "!# (Htok & Heq & HA)". interp_unfold.
                iDestruct "HA" as (w1 w2 u1 u2) "(-> & -> & #HA & #HB)".
                (* rewrite interp_tvar_unfold. iSimpl in "HA".
                rewrite interp_tvar_unfold. iSimpl in "HB". *)
                iSimpl in "Heq".
                iDestruct "Heq" as (???? H1) "(HeqA & HeqB)".
                destruct H1. simplify_eq.
                iPoseProof ("HrelA" with "[//] [$HeqA HA $Htok]") as "> (HArel & Htok)"; first admit.
                iPoseProof ("HrelB" with "[//] [$HeqB HB $Htok]") as "> (HBrel & $)"; first admit.
                do 4 iExists _. iModIntro. do 2 (iSplit; [eauto|]).
                do 2 (rewrite interp_tvar_unfold; iSimpl).      
                iFrame. }
            { iApply (refines_un_Auth_pair with "HA_un HB_un"). }
          }
          { iPoseProof "HA_un" as (tA_un serA_un deserA_un countA_un ?) "(#HserA_un & #Hser3A_un & #HcountA_un & #HdeserA_un)".
            rewrite interp_un_arr_unfold.
            iIntros (?) "!# #HB_un".
            iEval (rewrite interp_app_unfold; interp_unfold_tac; interp_unfold_tac) in "HB_un".
            iPoseProof "HB_un" as (tB_un serB_un deserB_un countB_un ?) "(#HserB_un & #Hser3B_un & #HcountB_un & #HdeserB_un)".
            simplify_eq. iIntros "Htok".
            wp_pures.
            rewrite /prod_scheme /prod_ser'' /prod_deser /prod_count.
            wp_pures. iFrame. iModIntro.
            iApply (refines_un_Auth_pair with "HA_un HB_un"). }
        }
        { rewrite interp_un_arr_unfold.
          iIntros (?) "!# #HA_un".
          iEval (rewrite interp_app_unfold; interp_unfold_tac; interp_unfold_tac) in "HA_un".
          iPoseProof "HA_un" as (tA_un serA_un deserA_un countA_un ->) "(#HserA_un & #Hser3A_un & #HcountA_un & #HdeserA_un)".
          iIntros "Htok".
          wp_pures.
          iModIntro. iFrame.
          rewrite interp_un_arr_unfold.
          iIntros (?) "!# #HB_un".
          iEval (rewrite interp_app_unfold; interp_unfold_tac; interp_unfold_tac) in "HB_un".
          iPoseProof "HB_un" as (tB_un serB_un deserB_un countB_un ->) "(#HserB_un & #Hser3B_un & #HcountB_un & #HdeserB_un)".
          iIntros "Htok".
          wp_pures.
          rewrite /prod_scheme /prod_ser'' /prod_deser /prod_count.
          wp_pures. iFrame. iModIntro.
          iApply (refines_un_Auth_pair with "HA_un HB_un"). }
      }
      { rewrite interp_un_forall_unfold.
        iIntros (B ??) "!# Htok".
        wp_pures.
        iModIntro. iFrame.
        rewrite interp_un_arr_unfold.
        iIntros (?) "!# #HA_un".
        iEval (rewrite interp_app_unfold; interp_unfold_tac; interp_unfold_tac) in "HA_un".
        iPoseProof "HA_un" as (tA_un serA_un deserA_un countA_un ->) "(#HserA_un & #Hser3A_un & #HcountA_un & #HdeserA_un)".
        iIntros "Htok".
        wp_pures.
        iModIntro. iFrame.
        rewrite interp_un_arr_unfold.
        iIntros (?) "!# #HB_un".
        iEval (rewrite interp_app_unfold; interp_unfold_tac; interp_unfold_tac) in "HB_un".
        iPoseProof "HB_un" as (tB_un serB_un deserB_un countB_un ->) "(#HserB_un & #Hser3B_un & #HcountB_un & #HdeserB_un)".
        iIntros "Htok".
        wp_pures.
        rewrite /prod_scheme /prod_ser'' /prod_deser /prod_count.
        wp_pures. iFrame. iModIntro.
        iApply (refines_un_Auth_pair with "HA_un HB_un"). }
    - rewrite interp_un_forall_unfold.
      iIntros (A ??) "!# Htok".
      rewrite /v_Auth_pair.
      wp_pures.
      iModIntro. iFrame.
      rewrite interp_un_forall_unfold.
      iIntros (B ??) "!# Htok".
      wp_pures.
      iModIntro. iFrame.
      rewrite interp_un_arr_unfold.
      iIntros (?) "!# #HA_un".
      iEval (rewrite interp_app_unfold; interp_unfold_tac; interp_unfold_tac) in "HA_un".
      iPoseProof "HA_un" as (tA_un serA_un deserA_un countA_un ->) "(#HserA_un & #Hser3A_un & #HcountA_un & #HdeserA_un)".
      iIntros "Htok".
      wp_pures.
      iModIntro. iFrame.
      rewrite interp_un_arr_unfold.
      iIntros (?) "!# #HB_un".
      iEval (rewrite interp_app_unfold; interp_unfold_tac; interp_unfold_tac) in "HB_un".
      iPoseProof "HB_un" as (tB_un serB_un deserB_un countB_un ->) "(#HserB_un & #Hser3B_un & #HcountB_un & #HdeserB_un)".
      iIntros "Htok".
      wp_pures.
      rewrite /prod_scheme /prod_ser'' /prod_deser /prod_count.
      wp_pures. iFrame. iModIntro.
      iApply (refines_un_Auth_pair with "HA_un HB_un").
  Admitted.
      
            
    (* - iIntros (??????) "!# (Hsusp & Hin & Hc) HΦ".
      iSimpl in "Hin Hc".
      iDestruct "Hin" as (??) "[% [HinA|HinB]]";
        iDestruct "Hc" as (????) "((% & %) & [HcA HcB])";
        simplify_eq.
      + iPoseProof (count_gt0 with "[$HinA $HcA]") as (?) "[HinA HcA]".
        wp_apply ("HcupdA" with "[$Hsusp $HinA $HcA]").
        iIntros "[Hc Hsusp]". iApply "HΦ". iFrame.
        iPureIntro. split; [done|lia].
      + iPoseProof (count_gt0 with "[$HinB $HcB]") as (?) "[HinB HcB]".
        wp_apply ("HcupdB" with "[$Hsusp $HinB $HcB]").
        iIntros "[Hc Hsusp]". iApply "HΦ". iFrame.
        iPureIntro. split; [done|lia]. *)
  
  Lemma refines_Auth_sum Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆; ⋆, var2 var1 → var2 var0 → var2 (var1 + var0) ⟧
      (ext Δ (lrel_evidence N)) v_Auth_sum i_Auth_sum.
  Proof. Admitted.

  Lemma refines_Auth_string :
    ⊢ (lrel_evidence N) (LRelBi lrel_un_string lrel_string) v_Auth_string i_Auth_string.
  Proof. Admitted.

  Lemma refines_Auth_int :
    ⊢ (lrel_evidence N) (LRelBi lrel_un_int lrel_int) v_Auth_int i_Auth_int.
  Proof. Admitted.

  Lemma refines_Auth_mu Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆ ⇒ ⋆, var1 (var0 (μ: ⋆; var1 var0)) → var1 (μ: ⋆; var1 var0) ⟧
      (ext Δ (lrel_evidence N)) v_Auth_mu i_Auth_mu.
  Proof.
    rewrite /lrel_car /lrel_un_car/=. iSplit; interp_unfold !.
    - iIntros (A v1 v2) "!# _". iIntros (??) "(Hi & Htok)".
      rewrite /i_Auth_mu /v_Auth_mu.
      i_pures. wp_pures.
      iFrame. iModIntro. clear.
      iSplit; interp_unfold!.
      + iIntros (??) "!# H".
        iIntros (??) "(Hi & Htok)".
        interp_unfold! in "H".
        iDestruct "H" as "[H H_un]".
        iDestruct "H" as "(%t & %ser & %deser & %count & -> & #Hser & #Hser3 & #Hcount & #Hdeser & #Hrel)".
        i_pures. wp_pures.
        iFrame. iModIntro.
        iSplit; interp_unfold!.
        * iExists t, _, _, _. iSplit; [done|].
          clear. iSplit; [|iSplit]; [| |iSplit; [|iSplit]].
          -- iIntros (v1 v2 ?? Ψ) "!# (#Hs & Htok) HΨ".
             wp_pures.
             rewrite interp_rec_star_bin_unfold.
             rewrite interp_unseal /=.
             wp_apply ("Hser" with "[//] [$Htok]"); [by iFrame|done].
          (* - iIntros (v1 Ψ) "!# (Hs & Htok) HΨ".
      wp_pures.
      wp_apply ("Hser2" with "[Hs Htok]"); [by iFrame|done]. *)
          -- iIntros (v1 ??? Ψ) "!# (Hs & Htok) HΨ".
             wp_pures.
             by wp_apply ("Hser3" with "[//] [$Hs $Htok]").
          -- iIntros (?????) "!# (Hp & Htok) HΨ". wp_pures.
             by iApply ("Hcount" with "[//] [$Hp $Htok]").
          -- iIntros (pid Ψ) "!# _ HΨ". wp_pures.
             iApply "HΨ". iModIntro.
             iIntros (s ?) "!# _ HΨ". wp_pures.
             wp_apply "Hdeser"; [done|].
             iIntros (depar) "HΨ1".
             iApply "HΨ1"; [done|].
             iModIntro.
             iIntros ([]) "H"; last first.
             { by iApply "HΨ". }
             by iApply "HΨ".
          -- iIntros (?????) "!# (Htok & Heq & HA)".
             rewrite interp_rec_star_bin_unfold.
             rewrite interp_unseal /=.
             iPoseProof ("Hrel" with "[//] [$Heq HA $Htok]") as "H"; admit.
        * iDestruct "H_un" as "(%t_un & %ser_un & %deser_un & %count_un & % & #Hser_un & #Hser3_un & #Hcount_un & #Hdeser_un)".
          simplify_eq.
          iExists t_un, _, _, _. iSplit; first done.
          clear. iSplit; [|iSplit; [|iSplit]].
          -- iIntros (v ?? Ψ) "!# (#Hs & Htok) HΨ".
             wp_pures.
             rewrite interp_rec_star_un_unfold.
             rewrite interp_unseal /=.
             wp_apply ("Hser_un" with "[//] [$Htok]"); [by iFrame|done].
          (* - iIntros (v1 Ψ) "!# (Hs & Htok) HΨ".
      wp_pures.
      wp_apply ("Hser2" with "[Hs Htok]"); [by iFrame|done]. *)
          -- iIntros (v1 ??? Ψ) "!# (Hs & Htok) HΨ".
             wp_pures.
             by wp_apply ("Hser3_un" with "[//] [$Hs $Htok]").
          -- iIntros (?????) "!# (Hp & Htok) HΨ". wp_pures.
             by iApply ("Hcount_un" with "[//] [$Hp $Htok]").
          -- iIntros (pid Ψ) "!# _ HΨ". wp_pures.
             iApply "HΨ". iModIntro.
             iIntros (s ?) "!# _ HΨ". wp_pures.
             wp_apply "Hdeser_un"; [done|].
             iIntros (depar) "HΨ1".
             iApply "HΨ1"; [done|].
             iModIntro.
             iIntros ([]) "H"; last first.
             { by iApply "HΨ". }
             by iApply "HΨ".
      + rewrite interp_un_arr_unfold.
        iIntros (?) "!# H Htok".
        interp_unfold! in "H".
        iDestruct "H" as "(%t_un & %ser_un & %deser_un & %count_un & % & #Hser_un & #Hser3_un & #Hcount_un & #Hdeser_un)".
        simplify_eq. wp_pures.
        iFrame. iModIntro.
        interp_unfold!.
        iExists t_un, _, _, _. iSplit; first done.
        clear. iSplit; [|iSplit; [|iSplit]].
        -- iIntros (v ?? Ψ) "!# (#Hs & Htok) HΨ".
           wp_pures.
           rewrite interp_rec_star_un_unfold.
           rewrite interp_unseal /=.
           wp_apply ("Hser_un" with "[//] [$Htok]"); [by iFrame|done].
        (* - iIntros (v1 Ψ) "!# (Hs & Htok) HΨ".
      wp_pures.
      wp_apply ("Hser2" with "[Hs Htok]"); [by iFrame|done]. *)
        -- iIntros (v1 ??? Ψ) "!# (Hs & Htok) HΨ".
           wp_pures.
           by wp_apply ("Hser3_un" with "[//] [$Hs $Htok]").
        -- iIntros (?????) "!# (Hp & Htok) HΨ". wp_pures.
           by iApply ("Hcount_un" with "[//] [$Hp $Htok]").
        -- iIntros (pid Ψ) "!# _ HΨ". wp_pures.
           iApply "HΨ". iModIntro.
           iIntros (s ?) "!# _ HΨ". wp_pures.
           wp_apply "Hdeser_un"; [done|].
           iIntros (depar) "HΨ1".
           iApply "HΨ1"; [done|].
           iModIntro.
           iIntros ([]) "H"; last first.
           { by iApply "HΨ". }
           by iApply "HΨ".
    - rewrite interp_un_forall_unfold.
      iIntros (A v) "!# _ Htok".
      rewrite /v_Auth_mu.
      wp_pures.
      iFrame. iModIntro. clear.
      rewrite interp_un_arr_unfold.
      iIntros (?) "!# H Htok".
      interp_unfold! in "H".
      iDestruct "H" as "(%t_un & %ser_un & %deser_un & %count_un & % & #Hser_un & #Hser3_un & #Hcount_un & #Hdeser_un)".
      simplify_eq. wp_pures.
      iFrame. iModIntro.
      interp_unfold!.
      iExists t_un, _, _, _. iSplit; first done.
      clear. iSplit; [|iSplit; [|iSplit]].
      -- iIntros (v ?? Ψ) "!# (#Hs & Htok) HΨ".
         wp_pures.
         rewrite interp_rec_star_un_unfold.
         rewrite interp_unseal /=.
         wp_apply ("Hser_un" with "[//] [$Htok]"); [by iFrame|done].
      (* - iIntros (v1 Ψ) "!# (Hs & Htok) HΨ".
      wp_pures.
      wp_apply ("Hser2" with "[Hs Htok]"); [by iFrame|done]. *)
      -- iIntros (v1 ??? Ψ) "!# (Hs & Htok) HΨ".
         wp_pures.
         by wp_apply ("Hser3_un" with "[//] [$Hs $Htok]").
      -- iIntros (?????) "!# (Hp & Htok) HΨ". wp_pures.
         by iApply ("Hcount_un" with "[//] [$Hp $Htok]").
      -- iIntros (pid Ψ) "!# _ HΨ". wp_pures.
         iApply "HΨ". iModIntro.
         iIntros (s ?) "!# _ HΨ". wp_pures.
         wp_apply "Hdeser_un"; [done|].
         iIntros (depar) "HΨ1".
         iApply "HΨ1"; [done|].
         iModIntro.
         iIntros ([]) "H"; last first.
         { by iApply "HΨ". }
         by iApply "HΨ".
  Admitted.

  (* Remove suspended case from lrel_auth? It would also make serialization always pass *)
  (*  Definition auth_inv (susp : loc) (s1 : string) :=
    ((hashed s1 ∗ susp ↦□ InjRV #(hash s1) ∗ auth_valid_val_2 susp) ∨
       auth_valid_val_3 susp (DfracOwn (3/4)))%I. *)

  Definition auth_rel_inv (s1 : string) (susp : loc) : iProp Σ :=
    ∃ (s : string), ⌜s = some_ser_str (string_ser_str (hash s1))⌝ ∗
      (hashed s1 ∗ auth_is_ser_2 s susp ∨ auth_is_ser_3_proph s susp).

  Definition auth_some (A : lrel Σ) (v1 v2 : val) : iProp Σ :=
    (∃ (a1 : val) (t : evi_type) (s1 : string),
        s_is_ser'' t a1 s1 ∗ A a1 v2 ∗
          ((hashed s1 ∗ ⌜v1 = InjLV #(hash s1)⌝) ∨
             (∃ (susp : loc),
                ⌜v1 = InjRV #susp⌝ ∗ 
                seq_inv (authSerProofN N #susp)
                  (auth_rel_inv s1 susp)))).

  #[global] Instance auth_some_persistent A v1 v2 : Persistent (auth_some A v1 v2).
  Proof. unfold auth_some. apply _. Qed.

  Definition lrel_auth_some (A : lrel Σ) : lrel Σ :=
    LRel (λ v1 v2, auth_some A v1 v2)%I.

  Definition lrel_bin_auth' (A : lrel Σ) : lrel Σ :=
    LRel (λ a1 v2, (∃ v1, ⌜a1 = SOMEV v1⌝ ∗ auth_some A v1 v2) ∨ ⌜a1 = NONEV⌝)%I.

  Definition auth_some_un (v1 : val) : iProp Σ :=
    (∃ (s1 : string),
        ((hashed s1 ∗ ⌜v1 = InjLV #(hash s1)⌝) ∨
          (∃ (susp : loc),
            ⌜v1 = InjRV #susp⌝ ∗ 
            seq_inv (authSerProofN N #susp)
              (auth_rel_inv s1 susp)))).
  
  #[global] Instance auth_some_un_persistent v1 : Persistent (auth_some_un v1).
  Proof. unfold auth_some_un. apply _. Qed.

  Definition lrel_un_auth_some : lrel_un Σ :=
    LRelUn (λ v, auth_some_un v)%I.

  Definition lrel_un_auth' : lrel_un Σ :=
    LRelUn (λ a, (∃ v, ⌜a = SOMEV v⌝ ∗ auth_some_un v) ∨ ⌜a = NONEV⌝)%I.

  Definition lrel_auth' (A : lrel_bi Σ) : lrel_bi Σ :=
    LRelBi lrel_un_auth' (lrel_bin_auth' (lrel_bi_bin A)).
  
  Program Definition lrel_auth : kindO Σ (⋆ ⇒ ⋆)%kind := λne A, lrel_auth' A.
  Next Obligation.
    intros ????.
    rewrite /lrel_auth' /=.
    split; [intros ?|intros ??];
      rewrite /lrel_car/= /lrel_un_car/= /auth_some_un /auth_some; solve_proper.
  Qed.

  Definition auth_ctx {Θ} (Δ : ctxO Σ Θ) (R : kindO Σ (⋆ ⇒ ⋆)) :=
    ext (ext (ext Δ lrel_auth) R) (lrel_evidence N).

  Lemma refines_Auth_auth Θ (Δ : ctxO Σ Θ) R :
    ⊢ ⟦ ∀: ⋆, var1 (var3 var0) ⟧
      (auth_ctx Δ R) v_Auth_auth i_Auth_auth.
  Proof.
    iSplit; interp_unfold!.
    { iIntros (A ??) "!# _"; rewrite -!/interp.
      iIntros (??) "(Hi & Htok)".
      rewrite /v_Auth_auth /i_Auth_auth.
      i_pures; wp_pures.
      iModIntro. iFrame.
      rewrite /auth_ctx.
      iSplit; interp_unfold!.
      { iExists tauth, _, _, _.
        iSplit; [done|]. clear. iSplit; [|iSplit]; [| |iSplit; [|iSplit]].
        - iIntros (?????) "!# (#Hauth & Htok) H".
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
            iMod (na_inv_acc with "Hinv Htok") as "(Hinv1 & Htok & Hclose)"; [solve_ndisj|solve_ndisj|].
            iDestruct "Hinv1" as (?) "(>% & [(#hashs1& %& #Hsusp & #Hser1)|(%& %& %& Hsusp & Hproph & #Hser1)])".
            * (* 
              ∃ (pid: nat) (p : proph_id) (h : string),
      ⌜v = InjRV #susp⌝ ∗ susp ↦ InjLV (#pid, #p) ∗ proph_susp p h ∗
        s_is_ser (g:=gwp_upto_bad) auth_scheme (SOMEV #h) s.
            iMod ("Hclose" with "[Htok]") as "Htok".
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
              iMod ("Hclose" with "[Hser HA Hsusp Htok Hser1]") as "Htok".
              { iFrame. iNext. iExists _. iSplit; first done. iLeft. by iFrame "∗ #". }
              wp_pures.
              wp_apply s_ser_spec'.
              { iRight. eauto. }
              iIntros (o) "#Ho". destruct o; last first.
              { iApply ("H" $! None). iFrame. }
              iApply ("H" $! (Some _)). iFrame.
              iExists _. iSplit; [done|].
              iRight. iExists _. iSplit; first done.
              iExists _. eauto.
            * wp_load.
              iMod ("Hclose" with "[Hsusp Hproph Hser1 $Htok]") as "Htok".
              { iNext. iExists _. iSplit; first done. iRight. by iFrame. }
              wp_pures.
              iApply ("H" $! None). by iFrame.
        (* - iIntros (??) "!# (#Hauth & Htok) H".
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
              iApply ("H" $! None). by iFrame. *)

        - iIntros (?????) "!# (Hser & Htok) HΦ".
          rewrite /auth_ser_v. wp_pure. iSimpl in "Hser".
          iDestruct "Hser" as (?->) "[(% & -> & Hser)|(% & ->& Hinv)]".
          + wp_pures. wp_apply s_ser_spec'.
            { iRight. eauto. }
            iIntros (o) "#Ho". destruct o; last first.
            { iApply ("HΦ"  $! None). by iFrame. }
            iApply ("HΦ" $! (Some _)). iFrame.
            iExists _. iSplit; [done|].
            iLeft. iExists _. eauto.
          + simplify_eq. wp_pures. wp_bind (!_)%E.
            iMod (na_inv_acc with "Hinv Htok") as "(Hinv1 & Htok & Hclose)"; [solve_ndisj|solve_ndisj|].
            iDestruct "Hinv1" as "[(%& #Hsusp & Hser1)|(%& %& %& Hsusp & Hproph & Hser1)]".
            * wp_load.
              iDestruct "Hser1" as "#Hser1".
              iMod ("Hclose" with "[Hsusp Htok Hser1]") as "Htok".
              { iFrame. iNext. iLeft. by iFrame "∗ #". }
              wp_pures.
              wp_apply s_ser_spec'.
              { iRight. eauto. }
              iIntros (o) "#Ho". destruct o; last first.
              { iApply ("HΦ" $! None). by iFrame. }
              iApply ("HΦ" $! (Some _)). iFrame.
              iExists _. iSplit; [done|].
              iRight. iExists _. iSplit; first done.
              iExists _. eauto.
            * wp_load.
              iMod ("Hclose" with "[Hsusp Hproph Hser1 $Htok]") as "Htok".
              { iNext. iRight. by iFrame. }
              wp_pures.
              iApply ("HΦ" $! None). by iFrame.
            
        - iIntros (?????) "!# (Hser & Htok) H".
          rewrite /auth_count. wp_pures.
          iDestruct "Hser" as (?->) "[(%& ->& Hser)|(%& ->& Hinv)]"; simplify_eq; wp_pures.
          { by iApply ("H" $! 0%nat). }
          iMod (na_inv_acc with "Hinv Htok") as "(Hinv & Htok & Hclose)"; [solve_ndisj|solve_ndisj|].
          iDestruct "Hinv" as "[(%& #Hsusp & Hser1)|(%& %& %& Hsusp & Hproph & Hser1)]"; wp_load; wp_pures.
          { iApply ("H" $! 0%nat). 
            iMod ("Hclose" with "[Hsusp Htok Hser1]") as "$"; last done.
            iFrame. iNext. iLeft. by iFrame "∗ #". }

            iApply ("H" $! (1%nat)).
            iMod ("Hclose" with "[Hsusp Hproph Hser1 $Htok]") as "Htok".
            { iNext. iRight. by iFrame. }
            by iFrame.

            (* iAssert (susp ↦{#1/2} InjLV #pid ∗ susp ↦{#1/4} InjLV #pid)%I with "[Hsusp]" as "[Hsusp1 Hsusp2]"; [admit|].
            iSplitR "Hin Heq Hsusp1".
            { iExists _. iSplit; [done|]. iRight. iExists susp.
              iSplit; [done|]. iRight. iExists _. iSplit; [|done]. iFrame. }
            iExists _. iSplit; [done|]. iRight. iExists susp.
            iSplit; [done|]. iFrame. *)
          
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
          iIntros ([] ?); wp_pures; last (by iApply ("H" $! None)).
          destruct H as [(->&H)|(?&?&(->&H)&?)]; wp_pures.
          * wp_apply (typed_proph_wp_new_proph1 StringTypedProph); first done.
            iIntros (??) "Hproph".
            wp_alloc susp as "Hsusp".
            (* iMod (own_alloc parent_agree pid tauth NONEV). *)
            (*          iMod(inv_alloc (authSerN #susp) _ (auth_inv A susp) with "[Hsusp]") as "#Hinv".
              { iModIntro. iRight. eauto. } *)
            wp_pures.
            iApply ("H" $! (Some _)).
            (* iAssert (susp ↦{#1/4} InjLV (#pid, #p) ∗ susp ↦{#3/4} InjLV (#pid, #p))%I with "[Hsusp]" as "[Hsusp1 Hsusp2]"; [admit|].
            pose (s' := some_ser_str (string_ser_str v)).
            iMod (na_inv_alloc seqG_name ⊤ (authSerN N #susp)
                    (auth_ser_inv (InjRV #susp) s' susp) with "[Hsusp1 Hproph]") as "Hinv".
            { iNext. iRight. iFrame. iSplit; first done.
              iRight. iExists _, _. iSplit; first done. eauto. } *)
            iModIntro.
            iExists _. iSplit; [done|].
            (*          { simpl. iExists _. iSplit; [done|].
                iRight. rewrite /auth_is_ser_3.
                iExists _, _. iSplit; [done|].
                iInv "Hinv" as "[(%&%&%&%&Hser&HA&Hhash&#Hsusp)|(%&Hsusp)]" "Hclose".
                iInv 
                eauto. } *)
            iRight. iExists _. iSplit; [done|].
            iFrame. iSimpl. iLeft. done. 
          * iModIntro. iApply ("H" $! (Some _)).
            iExists _. iSplit; [done|].
            iLeft. rewrite /auth_is_ser_1.
            destruct! H0. simplify_eq.          
            iExists _. iSplit; [done|].
            iRight. iExists _, _.
            eauto.
        - iIntros (?????) "!# (Htok & Heq & Hauth)".
          iDestruct "Hauth" as "[(% & -> & Hauth)|->]"; iSimpl in "Heq"; last first.
          { iDestruct "Heq" as "[(% & %)|(% & ([%|(% & % & H)]&Heq))]"; simplify_eq.
            iFrame. by iRight. }

          iDestruct "Heq" as "[(% & %)|(% & Heq)]"; simplify_eq.
          iDestruct "Hauth" as "(%&%&%&#Hser&#HA&[(#Hhash&%)|(%&%&#Hinv)])"; simplify_eq.
          + iDestruct "Heq" as "([%|(% & % & H)] & [%|(% & % & #Hsusp)])";
              simplify_eq; iFrame; iLeft; iExists _.
            * iModIntro. iSplit; [done|]. do 3 iExists _. iFrame "∗ #". iLeft. eauto.
            * iMod (na_inv_alloc seqG_name _ (authSerProofN N #susp) (auth_rel_inv s1 susp) with "[Hhash]") as "Hinv".
              { iModIntro. iExists _. iSplit; first done. iLeft. iFrame "∗ #".
                iRight. iExists _, _. iSplit; first done.
                iExists _. done. }
                (* { iModIntro. iLeft. iFrame "∗ #". do 3 iExists _.
                iIntros "HancIn". iDestruct "HancIn" as (?) "[_ Heq]".
                iExists a1. iIntros "_". iFrame. } *)
              iModIntro. iSplit; [done|]. do 3 iExists _. iFrame "∗ #". iRight.
              iExists _. iSplit; [done|]. by iFrame.
          + iMod (na_inv_acc with "Hinv Htok") as "(Hinv1 & Htok & Hclose)"; [solve_ndisj|solve_ndisj|].
            iDestruct "Heq" as "([%|(% & % & #Hsusp1)] & [%|(% & % & #Hsusp2)])"; simplify_eq;
              (* simplify_eq; iDestruct "Hinv1" as "[(>#Hsusp & Hval)|(%pid&%&%&%&%&%&% & Hsusp & Hin & Heq)]". *)
              iDestruct "Hinv1" as (?) "(>% & [(>#hashs1& %& >#Hsusp & >#Hser1)|(%& %& %& >Hsusp & Hproph & >#Hser1)])";
              iPoseProof (pointsto_agree with "Hsusp Hsusp1") as "%"; try done.
            (* 2, 4: iMod (timeless (susp0 ↦{DfracOwn (3/4)} InjLV #pid) with "Hsusp") as "Hsusp";
            iPoseProof (pointsto_agree with "Hsusp1 Hsusp") as "%"; done.
            all: (iMod ("Hclose" with "[$Htok Hval]") as "Htok").
            1, 3: iNext; iLeft; iFrame "∗ #".
            all: iMod (timeless with "Hsusp") as "Hsusp_";
              iPoseProof (pointsto_agree with "Hsusp1 Hsusp_") as "%";
              simplify_eq; iFrame.
            * iModIntro. iLeft. iExists _. iSplit; first done.
              iFrame "#". by iLeft.
            * iMod (na_inv_alloc seqG_name _ (authSerProofN N #susp1) (auth_inv susp1 s1) with "[]") as "#Hinv2".
              { iLeft. iFrame "∗ #". iNext. do 3 iExists _.
                iIntros "HancIn". iDestruct "HancIn" as (?) "[_ Heq]".
                iExists a1. iIntros "_". iFrame. }
              iModIntro. iLeft. iExists _. iSplit; first done.
              do 3 iExists _. iFrame "#". by iRight. *)
            * iMod ("Hclose" with "[$Htok]") as "$".
              { iNext; iExists _. iSplit; first done. iLeft; iFrame "#". }
              iModIntro. iLeft. iExists _. iSplit; first done.
              iFrame "# ∗".
              iDestruct "Hser1" as "[(%&%)|(%&%&(%&%)&Hser1)]"; simplify_eq.
              iDestruct "Hser1" as "(%&%&%)". simplify_eq. by iLeft.
            * iMod ("Hclose" with "[$Htok]") as "$".
              { iNext; iExists _. iSplit; first done. iLeft. iFrame "∗ #". }
              simplify_eq.
              iMod (na_inv_alloc seqG_name _ (authSerProofN N #susp1) (auth_rel_inv s1 susp1) with "[]") as "#Hinv2".
              { by iFrame "# % ∗". }
              iModIntro. iLeft. iExists _. iSplit; first done.
              iFrame "#". by iRight. }
      { iExists tauth, _, _, _.
        iSplit; [done|]. clear. iSplit; [|iSplit]; [| |iSplit].
        - iIntros (????) "!# (#Hauth & Htok) H".
          rewrite /auth_ser_v. wp_pure.
          iDestruct "Hauth" as "[(% & -> & Hauth)|->]"; wp_pures; last first.
          { iApply ("H" $! None). by iFrame. }
          iDestruct "Hauth" as "(%&[(Hhash&%)|(%&%&Hinv)])";
            simplify_eq; wp_pures.
          + wp_apply s_ser_spec'.
            { iRight. eauto. }
            iIntros (o) "#Ho". destruct o; last first.
            { iApply ("H"  $! None). by iFrame. }
            iApply ("H" $! (Some _)). iFrame.
            iExists _. iSplit; [done|].
            iLeft. iExists _. eauto.
          + wp_bind (!_)%E.
            iMod (na_inv_acc with "Hinv Htok") as "(Hinv1 & Htok & Hclose)"; [solve_ndisj|solve_ndisj|].
            iDestruct "Hinv1" as (?) "(>% & [(#hashs1& %& #Hsusp & #Hser1)|(%& %& %& Hsusp & Hproph & #Hser1)])".
            * wp_load.
              iMod ("Hclose" with "[Hsusp Htok Hser1]") as "Htok".
              { iFrame. iNext. iExists _. iSplit; first done. iLeft. by iFrame "∗ #". }
              wp_pures.
              wp_apply s_ser_spec'.
              { iRight. eauto. }
              iIntros (o) "#Ho". destruct o; last first.
              { iApply ("H" $! None). iFrame. }
              iApply ("H" $! (Some _)). iFrame.
              iExists _. iSplit; [done|].
              iRight. iExists _. iSplit; first done.
              iExists _. eauto.
            * wp_load.
              iMod ("Hclose" with "[Hsusp Hproph Hser1 $Htok]") as "Htok".
              { iNext. iExists _. iSplit; first done. iRight. by iFrame. }
              wp_pures.
              iApply ("H" $! None). by iFrame.
        - iIntros (?????) "!# (Hser & Htok) HΦ".
          rewrite /auth_ser_v. wp_pure. iSimpl in "Hser".
          iDestruct "Hser" as (?->) "[(% & -> & Hser)|(% & ->& Hinv)]".
          + wp_pures. wp_apply s_ser_spec'.
            { iRight. eauto. }
            iIntros (o) "#Ho". destruct o; last first.
            { iApply ("HΦ"  $! None). by iFrame. }
            iApply ("HΦ" $! (Some _)). iFrame.
            iExists _. iSplit; [done|].
            iLeft. iExists _. eauto.
          + simplify_eq. wp_pures. wp_bind (!_)%E.
            iMod (na_inv_acc with "Hinv Htok") as "(Hinv1 & Htok & Hclose)"; [solve_ndisj|solve_ndisj|].
            iDestruct "Hinv1" as "[(%& #Hsusp & Hser1)|(%& %& %& Hsusp & Hproph & Hser1)]".
            * wp_load.
              iDestruct "Hser1" as "#Hser1".
              iMod ("Hclose" with "[Hsusp Htok Hser1]") as "Htok".
              { iFrame. iNext. iLeft. by iFrame "∗ #". }
              wp_pures.
              wp_apply s_ser_spec'.
              { iRight. eauto. }
              iIntros (o) "#Ho". destruct o; last first.
              { iApply ("HΦ" $! None). by iFrame. }
              iApply ("HΦ" $! (Some _)). iFrame.
              iExists _. iSplit; [done|].
              iRight. iExists _. iSplit; first done.
              iExists _. eauto.
            * wp_load.
              iMod ("Hclose" with "[Hsusp Hproph Hser1 $Htok]") as "Htok".
              { iNext. iRight. by iFrame. }
              wp_pures.
              iApply ("HΦ" $! None). by iFrame.
            
        - iIntros (?????) "!# (Hser & Htok) H".
          rewrite /auth_count. wp_pures.
          iDestruct "Hser" as (?->) "[(%& ->& Hser)|(%& ->& Hinv)]"; simplify_eq; wp_pures.
          { by iApply ("H" $! 0%nat). }
          iMod (na_inv_acc with "Hinv Htok") as "(Hinv & Htok & Hclose)"; [solve_ndisj|solve_ndisj|].
          iDestruct "Hinv" as "[(%& #Hsusp & Hser1)|(%& %& %& Hsusp & Hproph & Hser1)]"; wp_load; wp_pures.
          { iApply ("H" $! 0%nat). 
            iMod ("Hclose" with "[Hsusp Htok Hser1]") as "$"; last done.
            iFrame. iNext. iLeft. by iFrame "∗ #". }

            iApply ("H" $! (1%nat)).
            iMod ("Hclose" with "[Hsusp Hproph Hser1 $Htok]") as "Htok".
            { iNext. iRight. by iFrame. }
            by iFrame.
              
        - iIntros (??) "!# _ H".
          rewrite /auth_deser_v. wp_pures.
          iModIntro. iApply "H".
          iIntros (s?) "!# _ H".
          wp_pures. wp_apply s_deser_sound; [done|].
          iIntros ([] ?); wp_pures; last (by iApply ("H" $! None)).
          destruct H as [(->&H)|(?&?&(->&H)&?)]; wp_pures.
          * wp_apply (typed_proph_wp_new_proph1 StringTypedProph); first done.
            iIntros (??) "Hproph".
            wp_alloc susp as "Hsusp".
            wp_pures. iApply ("H" $! (Some _)).
            iModIntro. iExists _. iSplit; [done|].
            iRight. iExists _. iSplit; [done|].
            iFrame. iSimpl. iLeft. done. 
          * iModIntro. iApply ("H" $! (Some _)).
            iExists _. iSplit; [done|].
            iLeft. rewrite /auth_is_ser_1.
            destruct! H0. simplify_eq.          
            iExists _. iSplit; [done|].
            iRight. iExists _, _.
            eauto. } }
    { rewrite interp_un_forall_unfold.
      iIntros (A ?) "!# _ Htok"; rewrite -!/interp.
      rewrite /v_Auth_auth.
      wp_pures.
      iModIntro. iFrame.
      rewrite /auth_ctx. interp_unfold!.
      iExists tauth, _, _, _.
      iSplit; [done|]. clear. iSplit; [|iSplit]; [| |iSplit].
      - iIntros (????) "!# (#Hauth & Htok) H".
        rewrite /auth_ser_v. wp_pure.
        iDestruct "Hauth" as "[(% & -> & Hauth)|->]"; wp_pures; last first.
        { iApply ("H" $! None). by iFrame. }
        iDestruct "Hauth" as "(%&[(Hhash&%)|(%&%&Hinv)])";
          simplify_eq; wp_pures.
        + wp_apply s_ser_spec'.
          { iRight. eauto. }
          iIntros (o) "#Ho". destruct o; last first.
          { iApply ("H"  $! None). by iFrame. }
          iApply ("H" $! (Some _)). iFrame.
          iExists _. iSplit; [done|].
          iLeft. iExists _. eauto.
        + wp_bind (!_)%E.
          iMod (na_inv_acc with "Hinv Htok") as "(Hinv1 & Htok & Hclose)"; [solve_ndisj|solve_ndisj|].
          iDestruct "Hinv1" as (?) "(>% & [(#hashs1& %& #Hsusp & #Hser1)|(%& %& %& Hsusp & Hproph & #Hser1)])".
          * wp_load.
            iMod ("Hclose" with "[Hsusp Htok Hser1]") as "Htok".
            { iFrame. iNext. iExists _. iSplit; first done. iLeft. by iFrame "∗ #". }
            wp_pures.
            wp_apply s_ser_spec'.
            { iRight. eauto. }
            iIntros (o) "#Ho". destruct o; last first.
            { iApply ("H" $! None). iFrame. }
            iApply ("H" $! (Some _)). iFrame.
            iExists _. iSplit; [done|].
            iRight. iExists _. iSplit; first done.
            iExists _. eauto.
          * wp_load.
            iMod ("Hclose" with "[Hsusp Hproph Hser1 $Htok]") as "Htok".
            { iNext. iExists _. iSplit; first done. iRight. by iFrame. }
            wp_pures.
            iApply ("H" $! None). by iFrame.
      - iIntros (?????) "!# (Hser & Htok) HΦ".
        rewrite /auth_ser_v. wp_pure. iSimpl in "Hser".
        iDestruct "Hser" as (?->) "[(% & -> & Hser)|(% & ->& Hinv)]".
        + wp_pures. wp_apply s_ser_spec'.
          { iRight. eauto. }
          iIntros (o) "#Ho". destruct o; last first.
          { iApply ("HΦ"  $! None). by iFrame. }
          iApply ("HΦ" $! (Some _)). iFrame.
          iExists _. iSplit; [done|].
          iLeft. iExists _. eauto.
        + simplify_eq. wp_pures. wp_bind (!_)%E.
          iMod (na_inv_acc with "Hinv Htok") as "(Hinv1 & Htok & Hclose)"; [solve_ndisj|solve_ndisj|].
          iDestruct "Hinv1" as "[(%& #Hsusp & Hser1)|(%& %& %& Hsusp & Hproph & Hser1)]".
          * wp_load.
            iDestruct "Hser1" as "#Hser1".
            iMod ("Hclose" with "[Hsusp Htok Hser1]") as "Htok".
            { iFrame. iNext. iLeft. by iFrame "∗ #". }
            wp_pures.
            wp_apply s_ser_spec'.
            { iRight. eauto. }
            iIntros (o) "#Ho". destruct o; last first.
            { iApply ("HΦ" $! None). by iFrame. }
            iApply ("HΦ" $! (Some _)). iFrame.
            iExists _. iSplit; [done|].
            iRight. iExists _. iSplit; first done.
            iExists _. eauto.
          * wp_load.
            iMod ("Hclose" with "[Hsusp Hproph Hser1 $Htok]") as "Htok".
            { iNext. iRight. by iFrame. }
            wp_pures.
            iApply ("HΦ" $! None). by iFrame.
          
      - iIntros (?????) "!# (Hser & Htok) H".
        rewrite /auth_count. wp_pures.
        iDestruct "Hser" as (?->) "[(%& ->& Hser)|(%& ->& Hinv)]"; simplify_eq; wp_pures.
        { by iApply ("H" $! 0%nat). }
        iMod (na_inv_acc with "Hinv Htok") as "(Hinv & Htok & Hclose)"; [solve_ndisj|solve_ndisj|].
        iDestruct "Hinv" as "[(%& #Hsusp & Hser1)|(%& %& %& Hsusp & Hproph & Hser1)]"; wp_load; wp_pures.
        { iApply ("H" $! 0%nat). 
          iMod ("Hclose" with "[Hsusp Htok Hser1]") as "$"; last done.
          iFrame. iNext. iLeft. by iFrame "∗ #". }

          iApply ("H" $! (1%nat)).
          iMod ("Hclose" with "[Hsusp Hproph Hser1 $Htok]") as "Htok".
          { iNext. iRight. by iFrame. }
          by iFrame.
            
      - iIntros (??) "!# _ H".
        rewrite /auth_deser_v. wp_pures.
        iModIntro. iApply "H".
        iIntros (s?) "!# _ H".
        wp_pures. wp_apply s_deser_sound; [done|].
        iIntros ([] ?); wp_pures; last (by iApply ("H" $! None)).
        destruct H as [(->&H)|(?&?&(->&H)&?)]; wp_pures.
        * wp_apply (typed_proph_wp_new_proph1 StringTypedProph); first done.
          iIntros (??) "Hproph".
          wp_alloc susp as "Hsusp".
          wp_pures. iApply ("H" $! (Some _)).
          iModIntro. iExists _. iSplit; [done|].
          iRight. iExists _. iSplit; [done|].
          iFrame. iSimpl. iLeft. done. 
        * iModIntro. iApply ("H" $! (Some _)).
          iExists _. iSplit; [done|].
          iLeft. rewrite /auth_is_ser_1.
          destruct! H0. simplify_eq.          
          iExists _. iSplit; [done|].
          iRight. iExists _, _.
          eauto. }

            

  (*        - iIntros (??????) "!# (Hsusp & Hin & Hcount) HΦ".
          iDestruct "Hin" as (?[??]) "[(% & Hsusp1)|Hf]"; try done.
          iDestruct "Hcount" as (??) "[[% [% %]]|(% & % & [(% & Hsusp2 & %)|(%& Hsusp2 & %)])]"; simplify_eq.
          + iPoseProof (pointsto_agree with "Hsusp2 Hsusp1") as "%". done.
          + iCombine "Hsusp2 Hsusp1 Hsusp" as "H".
            iAssert (susp0 ↦ InjLV #pid1)%I with "[H]" as "H"; [admit|].
            wp_store. iApply "HΦ".
            iAssert (susp0 ↦□ InjRV #h)%I with "[H]" as "#H1"; [admit|].
            iFrame "#". iModIntro. iExists _. iSplit; [done|].
            iRight. iSplit; [done|].
            iLeft. done. *)
  Qed.

  Lemma refines_auth_auth Θ (Δ : ctxO Σ Θ) R:
    ⊢ ⟦ ∀: ⋆, var1 var0 → var0 → var3 var0 ⟧
      (auth_ctx Δ R) v_auth i_auth.
  Proof.
    iSplit; interp_unfold!.
    - iIntros (???) "!# _"; rewrite -/interp.
      iIntros (??) "(Hi & Htok)".
      rewrite /v_auth  /i_auth.
      i_pures; wp_pures.
      iModIntro. iFrame. clear.
      iSplit; interp_unfold!.
      + iIntros (??) "!# #HeviA".
        rewrite /auth_ctx.
        interp_unfold! in "HeviA".
        iDestruct "HeviA" as "[HeviA HeviA_un]".
        iDestruct "HeviA" as (tA ser count deser ->) "(#Hser & #Hser3 & #Hcount & #Hdeser & #Hrel)".
        iIntros (??) "(Hi & Htok)".
        i_pures; wp_pures.
        iFrame. iModIntro. iSplit; interp_unfold!.
        * iIntros (w1 w2) "!# #HA". clear.
          iIntros (??) "(Hi & Htok)".
          i_pures; wp_pures. iDestruct "HA" as "[HA HA_un]".
          wp_apply ("Hser" with "[] [$Htok]"); [done|done|].
          iIntros ([]) "(Htok & Hs)"; wp_pures; last first.
          { iFrame. interp_unfold!. iModIntro. 
            iSplit; by iRight. }
          wp_apply (wp_hash with "[$]"). iIntros "#Hh1".
          wp_pures.
          iFrame.
          interp_unfold!. iModIntro. iSplit;
            iLeft; iExists _;
            iSplit; try done;
            repeat (iExists _); iFrame "# ∗ %";
            by iLeft.
        * iDestruct "HeviA_un" as (tA_un ser_un count_un deser_un ?) 
            "(#Hser_un & #Hser3_un & #Hcount_un & #Hdeser_un)".
          rewrite interp_un_arr_unfold. simplify_eq.
          iIntros (w1) "!# #HA Htok". clear.
          wp_pures. rewrite interp_tvar_unfold.
          wp_apply ("Hser_un" with "[] [$Htok]"); [done|done|].
          iIntros ([]) "(Htok & Hs)"; wp_pures; last first.
          { iFrame. interp_unfold!. iModIntro. 
            by iRight. }
          wp_apply (wp_hash with "[$]"). iIntros "#Hh1".
          wp_pures.
          iFrame.
          interp_unfold!. iModIntro;
            iLeft; iExists _;
            iSplit; try done;
            repeat (iExists _); iFrame "# ∗ %";
            by iLeft.
      + rewrite interp_un_arr_unfold.
        iIntros (?) "!# #HeviA Htok".
        rewrite /auth_ctx.
        interp_unfold! in "HeviA".
        iDestruct "HeviA" as (tA_un ser_un count_un deser_un ->) 
          "(#Hser_un & #Hser3_un & #Hcount_un & #Hdeser_un)".
        wp_pures. iModIntro. iFrame. 
        rewrite interp_un_arr_unfold.
        iIntros (w1) "!# #HA Htok". clear.
        wp_pures. rewrite interp_tvar_unfold.
        wp_apply ("Hser_un" with "[] [$Htok]"); [done|done|].
        iIntros ([]) "(Htok & Hs)"; wp_pures; last first.
        { iFrame. interp_unfold!. iModIntro. 
          by iRight. }
        wp_apply (wp_hash with "[$]"). iIntros "#Hh1".
        wp_pures.
        iFrame.
        interp_unfold!. iModIntro;
          iLeft; iExists _;
          iSplit; try done;
          repeat (iExists _); iFrame "# ∗ %";
          by iLeft.
        
    - rewrite interp_un_forall_unfold.
      iIntros (??) "!# _ Htok"; rewrite -/interp.
      rewrite /v_auth. wp_pures.
      iModIntro. iFrame. clear.
      rewrite interp_un_arr_unfold.
      iIntros (?) "!# #HeviA Htok".
      rewrite /auth_ctx.
      interp_unfold! in "HeviA".
      iDestruct "HeviA" as (tA_un ser_un count_un deser_un ->) 
        "(#Hser_un & #Hser3_un & #Hcount_un & #Hdeser_un)".
      wp_pures. iModIntro. iFrame. 
      rewrite interp_un_arr_unfold.
      iIntros (w1) "!# #HA Htok". clear.
      wp_pures. rewrite interp_tvar_unfold.
      wp_apply ("Hser_un" with "[] [$Htok]"); [done|done|].
      iIntros ([]) "(Htok & Hs)"; wp_pures; last first.
      { iFrame. interp_unfold!. iModIntro. 
        by iRight. }
      wp_apply (wp_hash with "[$]"). iIntros "#Hh1".
      wp_pures.
      iFrame.
      interp_unfold!. iModIntro;
        iLeft; iExists _;
        iSplit; try done;
        repeat (iExists _); iFrame "# ∗ %";
        by iLeft.

  Qed.

End proof.

