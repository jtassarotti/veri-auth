From auth.prelude Require Import stdpp.
From auth.rel_logic_bin Require Export model spec_rules spec_tactics interp lib adequacy fundamental.
From auth.heap_lang Require Import gen_weakestpre.
From auth.heap_lang.lib Require Import list map.
From auth.examples Require Export authentikit_susp authentikit_base_susp_security.
From iris.base_logic.lib Require Export na_invariants.

(* Class tableG (Σ: gFunctors) := {
  tableG_na_invG :: na_invG Σ;
  tableG_name: gname;
}.

Definition table_inv `{!invGS_gen hlc Σ} `{!tableG Σ} (N : namespace) (P : iProp Σ) :=
  na_inv tableG_name N P.
Definition table_tok `{!invGS_gen hlc Σ} `{!tableG Σ} (E : coPset) :=
  na_own tableG_name E. *)

Section proof.
  Context `{!authG Σ, !seqG Σ}.

  Definition authBaseN : namespace := nroot .@ "susp_ver".
  Definition authN (v : val) : namespace := authBaseN .@ v.
  Definition tableN : namespace := authBaseN .@ "table".

  Definition lrel_auth := lrel_auth authBaseN.

  Definition finish_spec (A : lrel Σ) (finish : val) (t : evi_type) (x a2 : val) : iProp Σ :=
    {{{ seq_tok ⊤ }}}
        finish #()
    {{{ (o : option val), RET $o; seq_tok ⊤ ∗
                                    if o is None then ⌜True⌝ else
                                      (∃ (a1 : val), A a1 a2 ∗ val_eq t x a1) }}}.
        
  Definition is_susp_table (l : loc) : iProp Σ :=
    ∃ (d : val) (m : gmap val val),
      l ↦ d ∗ ⌜is_map d m⌝ ∗
        ([∗ map] k ↦ v ∈ m, ∃ (pid ctr : nat) (finish ctrv : val) (A : lrel Σ),
            (⌜k = #pid ∧ ctrv = #ctr ∧ ctr > 0 ∧ v = (ctrv, finish)%V⌝ ∗
               (∃ (t: evi_type) (x a2 : val), finish_spec A finish t x a2))).

  Definition inv_susp_table (l: loc) := seq_inv tableN (is_susp_table l).

(*  Definition proph_list (vs : val) : iProp Σ :=
    ∃ (m: gmap int proph_id),
      ([∗ map] id ↦ p ∈ m, ∃ ( 

  Definition resolves (i : nat) : iProp Σ := True.

  Fixpoint is_fine (A : lrel Σ) (anc_exist : bool) (v1 v2 anc1 anc2 : val) (pid : int) : iProp Σ :=
    ∃ (anc_exist : bool) (anc1 anc2 : val) (pid : int)
    if anc then
      resolves pid -∗ is_fine A 
    else
      .*)
  
  Lemma v_finish_spec (A : lrel Σ) :
    ∀ (st : loc) (a a1 a2 x ser : val) (t : evi_type) (c : nat) (h : string),
      inv_susp_table st ⊢
      {{{ (lrel_auth A) a a2 ∗ ⌜a = SOMEV a1 ∧ a1 = InjLV #h⌝ ∗ seq_tok ⊤ ∗
            ser_spec_3 authBaseN ser t ∗ count_is_correct authBaseN t x c
            (* (∃ (p: proph_id) (vs : list (val * val)), ⌜pv = #p⌝ ∗ proph p vs)*) }}}
        v_finish #st a1 x ser
      {{{ (finish : val), RET finish;
          finish_spec A finish t x a2 ∗ seq_tok ⊤ }}}.
  Proof.
    iIntros (?????????) "#Htab".
    iIntros (?) "!# (#Hauth & (-> & ->) & Htok & #Hserspec & #Hcount) HΦ".
    rewrite /v_finish.
    iDestruct "Hauth" as "[(% & % & Hauth)|%]"; [|done].
    simplify_eq. wp_pures. iModIntro.
    iApply "HΦ". iFrame.
    rewrite /finish_spec.
    iIntros (?) "!# Htok HΦ".
    wp_pures.
    wp_apply ("Hserspec" with "[$Hcount $Htok]").
    iIntros ([]); last first.
    { iIntros "(Htok & _)". wp_pures.
      iModIntro. iApply ("HΦ" $! None). eauto. }
    iIntros "(Htok & #Hsers)". wp_pures.
    
    iDestruct "Hauth" as "(%&%&%&#Hser1&HA&[(#hashs1&%)|(%&%&Hinv)])"; simplify_eq.
    - wp_pures. wp_apply (wp_hash); [done|].
      iIntros "#hashs". wp_pures.
      case_bool_decide; simplify_eq; wp_pures; last first.
      { iApply ("HΦ" $! None). eauto. }
      destruct (decide (collision s s1)) as [|Hnc%not_collision].
      { iExFalso. by iApply (hashes_auth.hashed_inj_or_coll with "hashs hashs1"). }
      destruct Hnc as [<-|?]; simplify_eq.
      iPoseProof (evi_type_ser''_inj authBaseN with "[Hsers] Hser1") as "Heq";
        [iLeft; iFrame "#"|].
      iApply ("HΦ" $! (Some _)). by iFrame "∗ #".
      
(*    - wp_pures. wp_bind (!_)%E.
      iMod (na_inv_acc with "Hinv Htok") as "(Hinv1 & Htok & Hclose)"; [done|done|].
      iDestruct "Hinv1" as "[(%&#hashs1&#Hsusp)|(%&Hsusp)]"; wp_load.
      + iMod ("Hclose" with "[$Htok Hser1]") as "Htok".
        { iLeft. iNext. iFrame "# ∗". }
        wp_pures. wp_apply (wp_hash); [done|].
        iIntros "#hashs". wp_pures.
        case_bool_decide; simplify_eq; wp_pures; iModIntro; last first.
        { iApply ("HΦ" $! None). iFrame. }
        destruct (decide (collision s s0)) as [|Hnc%not_collision].
        { iExFalso. by iApply (hashes_auth.hashed_inj_or_coll with "hashs hashs1"). }
        destruct Hnc as [<-|?]; simplify_eq.
        by iApply ("HΦ" $! (Some _)).
      + iMod (na_inv_acc with "Htab Htok") as "(Htabo & Htok_tab & Hclose_tab)"; [done|solve_ndisj|].
        wp_pures.
        iDestruct "Htabo" as (??) "(Hl & %Hismap & #Hmap)".
        wp_load.
        wp_apply (gwp_map_lookup #pid d m); [done|done|].
        iIntros (? hoption).
        (* iMod ("Hclose" with "[Htok Hmap Hl]") as "Htok".
        { by iFrame. } *)
        destruct (m !! #pid) as [a|] eqn:Hlookup; last first.
        { simpl in hoption. simplify_eq. wp_pures. iApply ("HΦ" $! None).
          iMod ("Hclose_tab" with "[Htok_tab Hmap Hl]") as "Htok"; [by iFrame "# ∗"|].
          iMod ("Hclose" with "[Htok Hsusp]") as "Htok"; by iFrame. }

        iDestruct (big_sepM_lookup with "Hmap") as (??????) "Hfinish"; [done|].
        destruct! H. simplify_eq.

        simpl in hoption. simplify_eq. wp_pures.
        case_bool_decide; simplify_eq.
        * wp_pures. wp_load. wp_bind (map_remove _ _)%E.
          iApply (gwp_map_remove _ _ #pid0 _ m with "[]"); [done|done|].
          iIntros (??).
          iModIntro. wp_store.
          wp_apply (wp_hash); [done|].
          iIntros "#hashs". wp_pures.
          wp_store.
          simplify_eq.
          iMod (pointsto_persist with "Hsusp") as "#Hsusp".
          iMod ("Hclose_tab" with "[Htok_tab Hl]") as "Htok".
          { iFrame. iModIntro.
            iExists (delete _ _). iFrame "%".
            iApply (big_sepM_subseteq _ m); [by apply delete_subseteq|done]. }
          iMod ("Hclose" with "[$Htok Hsers Hsusp]") as "Htok".
          { iLeft. iNext. iFrame "# ∗". }

          by iApply ("Hfinish" with "Htok").

        * wp_pures. wp_apply (wp_hash); [done|].
          iIntros "#hashs". wp_pures.
          wp_store. wp_load.
          wp_bind (map_remove _ _)%E.
          iApply (gwp_map_remove _ _ #pid0 _ m with "[]"); [done|done|].
          iIntros (??).
          iModIntro. wp_store. wp_load. wp_pures.
          wp_bind (map.map_insert _ _ _).
          iApply (gwp_map_insert #pid0 _ d' _ _ _ with "[//]"); [done|].
          iModIntro. iIntros (??).
          wp_store.

          iMod ("Hclose_tab" with "[Htok_tab Hl]") as "Htok".
          { iFrame. iModIntro.
            iExists (<[#pid0:=(#(ctr - 1), finish)%V]> (delete #pid0 m)). iFrame "%".
            iApply big_sepM_insert; [by apply lookup_delete|].
            iFrame "# %". iSplit.
            { iExists _,_,_. iSplit; [done|]. instantiate (2 := (ctr - 1)).
              iSplit; [done|].
              iPureIntro. assert (ctr > 1).
              { destruct ctr; [lia|].
                simpl in H1. destruct ctr; try lia. done. }
              split; [lia|].
              f_equal. f_equal. rewrite Nat2Z.inj_sub; auto. }

            iPoseProof (big_sepM_delete _ m #pid0 _ with "Hmap") as "(Hpid & Hmapdel)"; [done|iFrame "#"]. }            

          iMod (pointsto_persist with "Hsusp") as "#Hsusp".
          iMod ("Hclose" with "[$Htok Hsers Hsusp]") as "Htok".
          { iLeft. iNext. iFrame "# ∗". }

          iModIntro. by iApply ("HΦ" $! (Some _)). *)
  Qed.

  Definition is_proof_state (v : val) : iProp Σ :=
    ∃ prf (counter : nat), ⌜v = (prf, #counter)%V⌝ ∗ is_proof prf.

  Definition lrel_auth_comp_post (A : lrel Σ) : lrel Σ :=
    LRel (λ v1 a2, ∃ a1 prf1, ⌜v1 = (prf1, a1)%V⌝ ∗ is_proof_state prf1 ∗ A a1 a2)%I.

  Definition lrel_auth_comp' (A : lrel Σ) : lrel Σ := LRel (λ v1 v2,
    ∀ t K (w w' : val),
      {{{ spec_ideal t (fill K (v2 w')) ∗ seq_tok ⊤ ∗ is_proof_state w }}}
        v1 w
      {{{ (o1 : option val), RET $o1;
          seq_tok ⊤ ∗
            if o1 is Some w1 then
              ∃ (w2 : val), spec_ideal t (fill K w2) ∗ lrel_auth_comp_post A w1 w2
            else True }}})%I.
              
  Program Definition lrel_auth_comp : kindO Σ (⋆ ⇒ ⋆)%kind := λne A, lrel_auth_comp' A.
  Next Obligation.
    intros ??? ???. rewrite /lrel_car /=.
    do 23 f_equiv. solve_proper.
  Qed.

  Definition auth_ctx {Θ} (Δ : ctxO Σ Θ) := ext (ext Δ lrel_auth) lrel_auth_comp.

  Lemma refines_auth_return Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆, var0 → var1 var0 ⟧ (auth_ctx Δ) v_return i_return.
  Proof.
    iIntros (A ??) "!# _".
    iIntros (??) "(Hi & Htok)".
    rewrite /v_return /i_return.
    i_pures; wp_pures.
    iModIntro. iFrame.
    iIntros (??) "!# #HA".
    iIntros (??) "(Hi & Htok)".
    i_pures; wp_pures.
    iModIntro. iFrame. clear.
    interp_unfold!.
    iIntros (???? Ψ) "!# (Hi & Htok & %) HΨ".
    destruct H as (? & ? & -> & Hp).
    i_pures; wp_pures.
    iModIntro. iApply ("HΨ" $! (Some _)).
    iFrame "Hi Htok".
    iExists _, _.
    interp_unfold in "HA".
    iFrame "HA".
    iSplit; [done|]. rewrite /is_proof_state.
    eauto.
  Qed.

  Lemma refines_auth_bind Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆; ⋆, var2 var1 → (var1 → var2 var0) → var2 var0 ⟧
      (auth_ctx Δ) v_bind i_bind.
  Proof.
    iIntros (A ??) "!# _".
    iIntros (??) "(Hi & Htok)".
    rewrite /v_bind/i_bind.
    i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iIntros (B ??) "!# _".
    iIntros (??) "(Hi & Htok)".
    i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iIntros (v1 v2) "!# #HmA".
    iIntros (??) "(Hi & Htok)".
    i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iIntros (w1 w2) "!# #HmB".
    iIntros (??) "(Hi & Htok)".
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
    iSpecialize ("HmB" with "HA [$Hi $Htok]").
    wp_apply (wp_wand with "HmB").
    iIntros (v) "(% & Hi & H & Htok) /=".
    interp_unfold in "H".
    wp_apply ("H" with "[$Htok $Hi $Hprf]").
    iIntros (?) "(Htok & Ho) /=".
    iApply "HΨ". iFrame.
  Qed.

  Lemma refines_auth_unauth Θ (Δ : ctxO Σ Θ) c :
    inv_susp_table c
    ⊢ REL v_unauth #c << i_unauth :
      ⟦ ∀: ⋆, var1 var0 → var3 var0 → var2 var0 ⟧ (ext (auth_ctx Δ) (lrel_evidence authBaseN)).
  Proof.
    iIntros "#Ht" (??) "(Hi & Htok)".
    rewrite /v_unauth /i_unauth.
    wp_pures.
    iFrame. iModIntro.
    iIntros (A v1 v2) "!# _".
    iIntros (??) "(Hi & Htok)".
    i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iIntros (??) "!# #Hevi".
    iIntros (??) "(Hi & Htok)".
    i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iIntros (w1 w2) "!# #Hauth /=".
    iIntros (??) "(Hi & Htok)".
    i_pures.
    interp_unfold in "Hevi Hauth".
    iDestruct "Hauth" as "[(% & -> & Hauth)|->]"; wp_pures; last first.
    { iFrame. iModIntro.
      interp_unfold!. iIntros (?????) "!# (Hi & Htok & Hproof) HΦ".
      wp_pures.
      iApply ("HΦ" $! None). by iFrame. }
        
    iDestruct "Hevi" as (tA' ??? ->) "(#Hser' & #Hser2 & #Hser3 & #Hcount & #Hdeser)".
    iPoseProof "Hauth" as "(%&%&%&#Hser1&HA&[(#hashs1&%)|(%&%&Hinv)])"; simplify_eq.
    - iFrame. iModIntro.
      interp_unfold!. iIntros (?????) "!# (Hi & Htok & Hproof) HΦ".
      wp_pures. iDestruct "Hproof" as (?? -> ) "Hproof".
      wp_pures. iDestruct "Hproof" as "(% & %)".
      wp_apply gwp_list_head; [done| ].
      iIntros (vl [[-> ->] | (s1' &?& -> & -> )]).
      { wp_pures. iModIntro.
        iApply ("HΦ" $! None). iFrame. }

      wp_pures.
      wp_apply "Hdeser"; [done|].
      iIntros (?) "Hdepar".
      wp_apply "Hdepar"; [done|].
      iIntros ([]); last first.

      { iIntros "_". wp_pures.
        iApply ("HΦ" $! None).
        iFrame. eauto. }

      iIntros "Hserser".
      wp_pures.
      wp_apply ("Hcount" with "[Hserser]").
      { iModIntro. by iApply (deser_valid). }

      iIntros (?) "(% & % & #Hc)". simplify_eq. wp_pures.
      wp_apply (v_finish_spec with "[//] [$Hauth $Htok $Hser3 $Hc]"); [eauto|].
      iIntros (finish) "(Hfinish & Htok)". wp_pures.

      case_bool_decide; simplify_eq; wp_pures.
      + wp_apply ("Hfinish" with "Htok").
        iIntros ([]) "(Htok & Heq)"; wp_pures; last first.
        { iApply ("HΦ" $! (None)). eauto. }
                
        wp_apply gwp_list_tail; [done|].
        iIntros (vl Hl). wp_pures.
        iApply ("HΦ" $! (Some _)).
        i_pures. iFrame.
        iExists _, _. iModIntro.
        iSplit; [done|].
        iExists _.
        
          
      wp_bind (v_finish _ _ _ _).
      iApply (v_finish_spec.
      
      iDestruct "Hcache" as (?) "(Htable & #Hm)".
      wp_apply (gwp_table_lookup with "Htable"); [done|].
      iIntros "Htable".
      destruct (m !! hash s1) as [a|] eqn:Hlookup.
    - iDestruct (big_sepM_lookup with "Hm") as (s1' t') "(#Hs1' & % & #Hsh1')"; [done|subst].
      wp_pures.

      destruct (decide (collision s1 s1')) as [|Hnc%not_collision].
      { iExFalso. by iApply (hashes_auth.hashed_inj_or_coll with "Hsh1 Hsh1'"). }
      destruct Hnc as [<- |?]; [|simplify_eq].
      
      iAssert (⌜a1 = a⌝)%I as "%".
      { by iApply (evi_type_ser_inj tA t'). }

      iMod ("Hclose" with "[$Htok $Hm $Htable]") as "Htok".
      
      
      destruct l.
      + wp_apply gwp_list_head; [done| ].
        iIntros (vl [[? ->] | (s1' &?& -> & -> )]).
        { wp_pures. iModIntro.
          iApply ("HΨ" $! None). iFrame. }
      
      wp_pures. iFrame. iModIntro.
      interp_unfold!.
      iIntros (???? Ψ) "!# (Hi & Htok & [% %Hprf]) HΨ".
      
      i_pures; wp_pures.
      destruct Hprf as (? & -> & ? & ?).
      wp_pures.

      wp_apply gwp_list_head; [done| ].
      iIntros (vl [[-> ->] | (s1' &?& -> & -> )]).
      { wp_pures. iModIntro.
        iApply ("HΨ" $! None). iFrame. }

      wp_pures.
      wp_apply "Hdeser"; [done|].
      iIntros (?) "#Hdepar".
      wp_apply "Hdepar"; [done|].
      iIntros ([]); last first.
      { iIntros "_". wp_pures.
        iApply ("HΨ" $! None).
        iFrame. eauto. }

      iIntros "Hserser".
      wp_pures.
      wp_bind (count _).
      wp_apply "Hcount".
      
        
    iDestruct "Hcache" as (?) "(Htable & #Hm)".
    wp_apply (gwp_table_lookup with "Htable"); [done|].
    iIntros "Htable".
    destruct (m !! hash s1) as [a|] eqn:Hlookup.
    - iDestruct (big_sepM_lookup with "Hm") as (s1' t') "(#Hs1' & % & #Hsh1')"; [done|subst].
      wp_pures.

      destruct (decide (collision s1 s1')) as [|Hnc%not_collision].
      { iExFalso. by iApply (hashes_auth.hashed_inj_or_coll with "Hsh1 Hsh1'"). }
      destruct Hnc as [<- |?]; [|simplify_eq].
      
      iAssert (⌜a1 = a⌝)%I as "%".
      { by iApply (evi_type_ser_inj tA t'). }

      iMod ("Hclose" with "[$Htok $Hm $Htable]") as "Htok".
      iModIntro. iApply ("HΨ" $! (Some _)). iFrame.
      iExists  _. iFrame "#". by simplify_eq.
    - wp_pures.
      iDestruct "Hprf" as (?) "%".
      wp_apply gwp_list_head; [done|].
      iIntros (vl [[-> ->] | (s1' &?& -> & -> )]).
      { wp_pures.
        iMod ("Hclose" with "[$Htok $Hm $Htable]") as "Htok".
        iModIntro. iApply ("HΨ" $! None). iFrame. }
      wp_pures.
      wp_apply (wp_hash with "[$]").
      iIntros "#Hsh1'".
      wp_pures.

      case_bool_decide; simplify_eq; wp_pures; last first.
      { iMod ("Hclose" with "[$Htok $Hm $Htable]") as "Htok".
        iModIntro. iApply ("HΨ" $! None). iFrame. }

      wp_apply "Hdeser"; [done|].
      iIntros ([r|]) "Hs1'"; wp_pures; last first.
      { iMod ("Hclose" with "[$Htok $Hm $Htable]") as "Htok".
        iModIntro. iApply ("HΨ" $! None). iFrame. }

      wp_apply (gwp_table_insert with "Htable"); [done|].
      iIntros "Htable".
      wp_pures.
      wp_apply (gwp_list_tail with "[//]").
      iIntros "/=" (tl Htl). wp_pures.

      destruct (decide (collision s1 s1')) as [|Hnc%not_collision].
      { iExFalso. by iApply (hashes_auth.hashed_inj_or_coll with "Hsh1 Hsh1'"). }
      destruct Hnc as [<- |?]; [|simplify_eq].

      iAssert (⌜a1 = r⌝)%I as "<-".
      { by iApply (evi_type_ser_inj tA tA'). }

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
  
  

