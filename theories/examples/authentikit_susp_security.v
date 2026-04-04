From auth.prelude Require Import stdpp.
From auth.rel_logic_bin Require Export model spec_rules spec_tactics interp lib adequacy fundamental.
From auth.heap_lang Require Import gen_weakestpre typedproph.
From auth.heap_lang.lib Require Import list map.
From auth.examples Require Export authentikit_susp authentikit_base_susp_security.
From iris.base_logic.lib Require Export na_invariants.
From iris.algebra Require Import auth agree numbers csum excl.


Definition poisonOSR := authUR (optionUR (optionUR (agree unitUR))).
Class poisonOSG Σ := PoisonOSG { poisonOS_inG :> inG Σ poisonOSR; poisonOSG_name : gname }.

Definition idcntrUR := authUR nat.
Class idcntrG Σ := IdcntrG { idcntr_inG :> inG Σ idcntrUR; idcntrG_name : gname }.

Lemma pos_alloc `{inG Σ poisonOSR} :
  ⊢ |==> ∃ _ : poisonOSG Σ, 
      (own poisonOSG_name (●{DfracOwn (1/2)} None)) ∗ 
      (own poisonOSG_name (●{DfracOwn (1/2)} None))%I.
Proof.
  iMod (own_alloc (● None)) as (γ) "[Hauth1 Hauth2]"; [admit|].
  set (H1 := PoisonOSG _ _ γ).
  iExists _. by iFrame.
Admitted.

Lemma idcntr_alloc `{inG Σ idcntrUR} :
  ⊢ |==> ∃ _ : idcntrG Σ, 
      (own idcntrG_name (●{DfracOwn (1/2)} 0) ∗ 
      own idcntrG_name (●{DfracOwn (1/2)} 0))%I.
Proof.
  iMod (own_alloc (● 0 ⋅ ◯ 0)) as (γ) "[Hauth _]"; [admit|].
  set (H1 := IdcntrG _ _ γ).
  iExists _.
  by iDestruct "Hauth" as "[$ $]".
Admitted.
  
Section proof.
  Context `{!authG Σ, !seqG Σ, !poisonOSG Σ, !idcntrG Σ}.

  Definition authBaseN : namespace := nroot .@ "susp_sec".
  Definition tableN : namespace := authBaseN .@ "table".

  Local Notation s_is_ser_proph := (s_is_ser_proph authBaseN).
  Local Notation ser_spec_un := (ser_spec_un authBaseN).
  Local Notation ser_spec_3 := (ser_spec_3 authBaseN).
  Local Notation count_spec := (count_spec authBaseN).
  Local Notation val_eq_rel := (val_eq_rel authBaseN).

  Local Notation lrel_evidence := (lrel_evidence authBaseN).
  Local Notation lrel_auth := (lrel_auth authBaseN).
  
  Definition pos_car := optionUR (optionUR (agree unitUR)).

  Definition pos (o : pos_car) := own poisonOSG_name (●{DfracOwn (1/2)} o).
  Definition good_pos := pos None.
  Definition bad_pos := pos (Some None).
  Definition done_pos := pos (Some (Some (to_agree ()))).
  Definition valid_pos o : iProp Σ := pos o ∧ ⌜o = None ∨ o = Some None⌝.

  Definition pos_frag (o : pos_car) := own poisonOSG_name (◯ o).
  Definition good_pos_frag := pos_frag None.
  Definition bad_pos_frag := pos_frag (Some None).
  Definition done_pos_frag := pos_frag (Some (Some (to_agree ()))).

  Definition id_frag (id : nat) := own idcntrG_name (●{DfracOwn (1/2)} id).


  Lemma pos_agree (o o' : pos_car) :
    pos o -∗ pos o' -∗ ⌜o' = o⌝ ∗ pos o ∗ pos o'.
  Proof. Admitted.

  Lemma pos_auth_frag_valid (o o' : pos_car) :
    pos o -∗ pos_frag o' -∗ ⌜o' ≼ o⌝ ∗ pos o ∗ pos_frag o'.
  Proof. Admitted.

  Lemma pos_update1 :
    good_pos -∗ good_pos ==∗ bad_pos ∗ bad_pos ∗ bad_pos_frag.
  Proof. Admitted.

  Lemma pos_update2 :
    bad_pos -∗ bad_pos ==∗ done_pos ∗ done_pos ∗ done_pos_frag.
  Proof. Admitted.

  
  Lemma id_agree id id' :
    id_frag id -∗ id_frag id' -∗ ⌜id = id'⌝ ∗ id_frag id ∗ id_frag id'.
  Proof. Admitted.

  Lemma id_update id id':
    id_frag id -∗ id_frag id ==∗ id_frag id' ∗ id_frag id'.
  Proof. Admitted.


  Definition finish_spec1 (finish : val) (x a ser : val) : iProp Σ :=
    ∀ (E: coPset) (s s' : string) (t : evi_type),
      ⌜↑authSet authBaseN ⊆ E⌝ -∗
      {{{ seq_tok E ∗ s_is_ser_proph t x s' ∗ ser_spec_3 ser t ∗
          ⌜a = InjLV #s⌝ }}}
        finish #()
        {{{ (o : option val), RET $o; seq_tok E }}}.

  Definition finish_spec1_bad (finish : val) (x a ser : val) : iProp Σ :=
    ∀ (E: coPset) (s s' : string) (t : evi_type),
      ⌜↑authSet authBaseN ⊆ E⌝ -∗
      {{{ seq_tok E ∗ s_is_ser_proph t x s' ∗ ser_spec_3 ser t ∗
          hashed s ∗ ⌜a = InjLV #(hash s)⌝ ∗ ⌜s ≠ s'⌝ }}}
        finish #()
        {{{ (o : option val), RET $o; seq_tok E ∗ ⌜o = None⌝ }}}.

  Definition finish_spec2 (finish : val) (x a ser : val) : iProp Σ :=
    ∀ (E: coPset) (s' s'' : string) (t : evi_type) (susp : loc) (o' : pos_car),
      ⌜↑authSet authBaseN ⊆ E ∧ ↑tableN ⊆ E⌝ -∗
      {{{ seq_tok E ∗ s_is_ser_proph t x s' ∗ ser_spec_3 ser t ∗ valid_pos o' ∗ 
          ⌜a = InjRV #susp⌝ ∗ seq_inv (authN authBaseN susp) (auth_inv s'' susp) }}}
        finish #()
        {{{ (o : option val), RET $o;
            seq_tok E ∗ (if o is Some _ then pos o' else True) }}}.

  Definition finish_spec2_bad (finish : val) (x a ser : val) : iProp Σ :=
    ∀ (E: coPset) (s s' s'' : string) (t : evi_type) (susp : loc),
      ⌜↑authSet authBaseN ⊆ E⌝ -∗
      {{{ seq_tok E ∗ s_is_ser_proph t x s' ∗ ser_spec_3 ser t ∗
          ⌜a = InjRV #susp⌝ ∗ ⌜s'' = some_ser_str (string_ser_str (hash s))⌝ ∗ 
          hashed s ∗ seq_inv (authN authBaseN susp) (auth_inv s'' susp) ∗ ⌜s ≠ s'⌝ }}}
        finish #()
        {{{ (o : option val), RET $o; seq_tok E ∗ ⌜o = None⌝ }}}.

  Definition good_finish_specs finish x a ser : iProp Σ :=
    ((∃ (s : string), ⌜a = InjLV #s⌝ ∗ finish_spec1 finish x a ser) ∨ 
      (∃ s'' (susp : loc), ⌜a = InjRV #susp⌝ ∗
        seq_inv (authN authBaseN susp) (auth_inv s'' susp) ∗
        finish_spec2 finish x a ser)).

  Definition bad_finish_specs finish x a ser s s' : iProp Σ :=
    ((⌜a = InjLV #(hash s)⌝ ∗ hashed s ∗ 
        (finish_spec1_bad finish x a ser ∧ ⌜s ≠ s'⌝)) ∨ 
      (∃ s'' (susp : loc), ⌜a = InjRV #susp⌝ ∗ hashed s ∗
        ⌜s'' = some_ser_str (string_ser_str (hash s))⌝ ∗ 
        seq_inv (authN authBaseN susp) (auth_inv s'' susp) ∗
          (finish_spec2_bad finish x a ser ∧ ⌜s ≠ s'⌝))).


  Definition susp_big_sep (m : gmap val val) : iProp Σ :=
    [∗ map] k ↦ v ∈ m,
      ∃ (ctr : nat) (finish x a ser : val) (t : evi_type) (s' : string),
        (⌜ctr > 0 ∧ v = (#ctr, finish)%V⌝ ∗ 
            s_is_ser_proph t x s' ∗ ser_spec_3 ser t ∗
            (good_finish_specs finish x a ser ∨
              (∃ s, bad_pos_frag ∗ bad_finish_specs finish x a ser s s'))).

  Definition susp_bad_ge1 (m : gmap val val) : iProp Σ :=
    good_pos ∨ done_pos ∨
      (bad_pos ∗ 
        ∃ (pid ctr : nat) (v finish x a ser : val) (t : evi_type) (s s' : string),
        ⌜m !! #pid = Some v ∧ ctr > 0 ∧ v = (#ctr, finish)%V⌝ ∗
          s_is_ser_proph t x s' ∗ ser_spec_3 ser t ∗
          bad_finish_specs finish x a ser s s').
      
  Definition is_susp_table (l : loc) : iProp Σ :=
    ∃ (d : val) (m : gmap val val) (ctr : nat),
      l ↦ d ∗ ⌜is_map d m⌝ ∗ susp_big_sep m ∗ susp_bad_ge1 m ∗
      id_frag ctr ∗ ⌜∀ ctr', ctr' ≥ ctr → m !! #ctr' = None⌝.

  Definition inv_susp_table (l: loc) := seq_inv tableN (is_susp_table l).

  
  Lemma v_finish_spec1 :
    ∀ (a x ser : val) (st : loc),
      {{{ True }}}
        v_finish #st a x ser
        {{{ (finish : val), RET finish;
            finish_spec1 finish x a ser }}}.
  Proof.
    iIntros (?????) "_ HΦ".
    rewrite /v_finish.
    wp_pures. iModIntro. iApply "HΦ".
    rewrite /finish_spec1.
    iIntros (?????).
    iIntros (?) "!# (Htok & #Hser & #Hserspec & %) HΦ".
    wp_pures. wp_apply ("Hserspec" with "[//] [$Hser $Htok]").
    iIntros ([]); last first.
    { iIntros "(Htok & #Hsers)". wp_pures.
      iModIntro. iApply ("HΦ" $! None). iFrame. }
    iIntros "(Htok & #[[% Hsers]|%])"; simplify_eq; wp_pures;
    wp_apply (wp_hash); try done;
    iIntros "#hashs'"; wp_pures;
    case_bool_decide; simplify_eq; wp_pures.
    - iApply ("HΦ" $! (Some _)); by iFrame "∗ #".
    - iApply ("HΦ" $! None); by iFrame "∗ #".
  Qed.

  Lemma v_finish_spec1_bad :
    ∀ (a x ser : val) (st : loc),
      {{{ True }}}
        v_finish #st a x ser
        {{{ (finish : val), RET finish;
            finish_spec1_bad finish x a ser }}}.
  Proof.
    iIntros (?????) "_ HΦ".
    rewrite /v_finish.
    wp_pures. iModIntro. iApply "HΦ".
    rewrite /finish_spec1.
    iIntros (?????).
    iIntros (?) "!# (Htok & #Hser & #Hserspec & #hashs & % & %) HΦ".
    wp_pures. wp_apply ("Hserspec" with "[//] [$Hser $Htok]").
    iIntros ([]); last first.
    { iIntros "(Htok & #Hsers)". wp_pures.
      iModIntro. iApply ("HΦ" $! None). by iFrame. }
    iIntros "(Htok & #[[% Hsers]|%])"; simplify_eq; wp_pures;
    wp_apply (wp_hash); try done;
    iIntros "#hashs'"; wp_pures;
    case_bool_decide; simplify_eq; wp_pures.
    { iPoseProof (hashes_auth.hashed_s_equal s s' with "[//] hashs hashs'") as "->". done. }
    iApply ("HΦ" $! None); by iFrame "∗ #".
  Qed.

  Lemma v_finish_spec2 :
    ∀ (a x ser : val) (st : loc),
      {{{ inv_susp_table st }}}
        v_finish #st a x ser
        {{{ (finish : val), RET finish;
            finish_spec2 finish x a ser }}}.
  Proof.
    iIntros (?????) "#Htab HΦ".
    rewrite /v_finish.
    wp_pures. iModIntro. iApply "HΦ".
    rewrite /finish_spec1.
    iIntros (s' s'' ????[??]).
    iIntros (?) "!# (Htok & #Hser & #Hserspec & [Hpos %Ho'] & % & #Hinv) HΦ".
    wp_pures. wp_apply ("Hserspec" with "[//] [$Hser $Htok]").
    iIntros ([]); last first.
    { iIntros "(Htok & #Hsers)". wp_pures.
      iModIntro. iApply ("HΦ" $! None). iFrame. }
    iIntros "(Htok & #[[% Hsers]|%])"; simplify_eq; wp_pures.
    
    iMod (na_inv_acc with "Htab Htok") as "(Htabo & Htok & Hclose_tab)"; [solve_ndisj|solve_ndisj|].
    iMod (na_inv_acc with "Hinv Htok") as "(Hinv1 & Htok & Hclose)"; [solve_ndisj|solve_ndisj|].
    
    iDestruct "Hinv1" as ">[(%s1&%& #hashs1 & %& #Hsusp & %Hser)|(%&%&%& Hsusp & Hproph & %Hser)]";
      wp_load; wp_pures; destruct! Hser; simplify_eq.
    - iMod ("Hclose" with "[$Htok]") as "Htok".
      { iNext. iLeft. iFrame "#". iSplit; eauto. 
        iRight. repeat iExists _. iSplit; eauto. }
      iMod ("Hclose_tab" with "[$Htok $Htabo]") as "Htok".
      wp_apply wp_hash; try done;
      iIntros "#hashs'"; wp_pures;
      case_bool_decide; simplify_eq; wp_pures.
      + iApply ("HΦ" $! (Some _)); by iFrame "∗ #".
      + iApply ("HΦ" $! None); by iFrame "∗ #".
    
    - wp_apply wp_hash; try done; iIntros "#hashs'"; wp_pures.
      wp_apply (typed_proph_wp_resolve1 StringTypedProph with "Hproph"); try done.
      wp_pures. iModIntro. iIntros (?). wp_pures.

      iDestruct "Htabo" as (???) "(Hl & %Hm & Hbigsep & Hge & Hid)".
      wp_apply wp_hash; try done; iIntros "_"; wp_pures; wp_store.
      iMod (pointsto_persist with "Hsusp") as "#Hsusp".

      wp_load. wp_bind (map_lookup _ _).
      wp_apply (gwp_map_lookup with "[//]"); try done.
      iIntros (? Hl). destruct (m !! #pid) eqn:Hlookup;
        simpl in Hl; simplify_eq; wp_pures; last first.
      { iMod ("Hclose" with "[$Htok]") as "Htok".
        { iNext. iLeft. iFrame "#". iSplit; eauto.
          iRight. repeat iExists _. iSplit; eauto. }
        iMod ("Hclose_tab" with "[$Hl $Hbigsep $Htok $Hge $Hid //]") as "Htok".
        iApply ("HΦ" $! None). by iFrame. }

      iDestruct (big_sepM_lookup_acc with "Hbigsep") as "[[% #Hs] Hbigsep]"; [done|subst].
      iDestruct "Hs" as (?????? Hv) "Hs"; destruct! Hv; simplify_eq; wp_pures.
      case_bool_decide; simplify_eq; wp_pures; wp_load;
        wp_bind (map_remove _ _); wp_apply (gwp_map_remove with "[//]");
        try done; iIntros (??); wp_store; wp_pures;
        iPoseProof ("Hbigsep" with "[$Hs]") as "Hbigsep";
          try (iFrame; iExists ctr0; iSplit; try done; iRight; iFrame "#");
        iDestruct (big_sepM_delete _ m #pid ((#ctr0, finish)%V) with "Hbigsep")
          as "[_ Hbigsep']"; try done;
        destruct Ho' as [-> | ->];
          iDestruct "Hge" as "[Hpos'|[Hpos'|[Hpos' Hge]]]";
          iPoseProof (pos_agree with "Hpos Hpos'") as (?) "[Hpos Hpos']";
        iDestruct "Hs" as 
          "(#Hser' & #Hserspec' & [#Hfinish|(%& Hfrag &#Hfinish)])";
          simplify_eq;
        iMod ("Hclose" with "[$Htok]") as "Htok";
          try (iNext; iLeft; iFrame "hashs' #"; iSplit; eauto;
              iRight; repeat iExists _; iSplit; eauto).

      2,6:
        iPoseProof (pos_auth_frag_valid with "Hpos Hfrag") as (Hincl) "[Hpos #Hfrag']";
        simplify_eq; apply option_included in Hincl; destruct! Hincl; simplify_eq.

      4,5,6:
        wp_load; wp_pures; wp_bind (map.map_insert _ _ _);
          wp_apply (gwp_map_insert with "[//]"); try done;
          iIntros (??); wp_store.

      + iMod ("Hclose_tab" with "[$Hl $Hbigsep' $Htok Hpos' Hid]") as "Htok".
        { iNext. iExists ctr. iSplit; iFrame; try done.
          iDestruct "Hid" as "[$ %]". iPureIntro.
          intros ??. rewrite lookup_delete_None. eauto. }
        iDestruct "Hfinish" as "[(%&%&Hfinish)|(%&%&%&#Hinv'&Hfinish)]".
        { wp_apply ("Hfinish" with "[//] [$Htok $Hser' $Hserspec' //]").
          iIntros (?) "Htok"; iApply "HΦ". iFrame. destruct o; eauto. }
        { wp_apply ("Hfinish" with "[//] [$Htok $Hser' $Hserspec' Hpos]");
          iFrame "# ∗"; eauto. }

      + iDestruct "Hge" as (?????????? ?) "Hge". destruct! H4.

        destruct (decide (#pid = #pid0)); simplify_eq.
        { iMod (pos_update2 with "Hpos Hpos'") as "(Hpos & Hpos' & _)".
          iMod ("Hclose_tab" with "[$Hl $Hbigsep' $Htok Hpos' Hid]") as "Htok".
          { iNext. iExists ctr. iSplit; iFrame; try done.
            iDestruct "Hid" as "[$ %]". iPureIntro.
            intros ??. rewrite lookup_delete_None. eauto. }
          iClear "#".
          iDestruct "Hge" as  "(Hser1 & Hser1' & Hfinish1)".
          iDestruct "Hfinish1" as "[(%&#hashs&[Hfinish %])|(%&%&%&#hashs&%&#Hinv'&[Hfinish %])]";
            wp_apply ("Hfinish" with "[//] [$Htok $Hser1 $Hser1' $hashs]"); eauto;
            iIntros (?) "[Htok ->]"; iApply ("HΦ" $! None); by iFrame. }

        destruct (size (delete #pid m)) as [|size] eqn:Hsize.
        { rewrite map_size_empty_iff in Hsize.
          eassert (delete #pid m !! #pid0 = Some _).
          { rewrite lookup_delete_Some /=. eauto. }
          rewrite Hsize in H6. done. }

        iMod ("Hclose_tab" with "[$Hl $Hbigsep' Hge $Htok Hpos' Hid]") as "Htok"; iFrame "%".
        { iNext. iExists ctr. iSplitL "Hpos' Hge".
          { do 2 iRight. iFrame "∗ # %". iExists pid0, ctr1, _. iPureIntro.
            by rewrite (lookup_delete_ne _ _ _ n). }
          iDestruct "Hid" as "[$ %]". iPureIntro.
          intros ??. rewrite lookup_delete_None. eauto. }
        iDestruct "Hfinish" as "[(%&%&Hfinish)|(%&%&%&#Hinv'&Hfinish)]".
        { wp_apply ("Hfinish" with "[//] [$Htok $Hser' $Hserspec' //]").
          iIntros (?) "Htok"; iApply "HΦ". iFrame. destruct o; eauto. }
        { wp_apply ("Hfinish" with "[//] [$Htok $Hser' $Hserspec' Hpos]");
          iFrame "# ∗"; eauto. }

      + iMod (pos_update2 with "Hpos Hpos'") as "(Hpos & Hpos' & _)".
        iMod ("Hclose_tab" with "[$Hl $Hbigsep' $Htok Hpos' Hid]") as "Htok".
        { iNext. iExists ctr. iSplit; iFrame; try done.
          iDestruct "Hid" as "[$ %]". iPureIntro.
          intros ??. rewrite lookup_delete_None. eauto. }
        iDestruct "Hfinish" as 
          "[(%&#hashs&[Hfinish %])|(%&%&%&#hashs&%&#Hinv'&[Hfinish %])]";
        wp_apply ("Hfinish" with "[] [$Htok]");
        try solve_ndisj; iFrame "# ∗"; eauto;
        iIntros (?) "[Htok ->]"; iApply ("HΦ" $! None); by iFrame.

      + iDestruct (big_sepM_insert _ (delete #pid m) #pid ((#(ctr0-1), finish)%V) with "[$Hbigsep']")
          as "Hbigsep'"; try apply lookup_delete;
          try (iFrame "Hser' Hserspec'"); try (iExists (ctr0-1)); repeat iExists _;
          try iSplit; 
            try (iPureIntro; split; repeat f_equal; try lia;
              inversion H1; try lia; by simplify_eq);
            try (by iLeft).
        iMod ("Hclose_tab" with "[$Hl $Hbigsep' $Htok Hpos' Hid]") as "Htok".
        { iNext. iExists ctr. iSplit; iFrame; try done.
          iDestruct "Hid" as "[$ %]". iPureIntro.
          intros ??. rewrite lookup_insert_None.
          destruct (decide (#pid = #ctr')); simplify_eq.
          { specialize (H5 ctr' H6) as H5'. simplify_eq. }
          rewrite lookup_delete_ne; eauto. }
        iApply ("HΦ" $! (Some _)); iModIntro. iFrame.

      + iDestruct (big_sepM_insert _ (delete #pid m) #pid ((#(ctr0-1), finish)%V) with "[$Hbigsep']")
          as "Hbigsep'"; try apply lookup_delete;
          try (iFrame "Hser' Hserspec'"); try (iExists (ctr0-1)); repeat iExists _;
          try iSplit; 
            try (iPureIntro; split; repeat f_equal; try lia;
              inversion H1; try lia; by simplify_eq);
            try (by iLeft).
        iMod ("Hclose_tab" with "[$Hl $Hbigsep' $Htok Hge Hpos' Hid]") as "Htok".
        { iNext. iExists ctr. iSplit; try done. 
          iSplitL "Hge Hpos'".
          { do 2 iRight; iFrame.
            iDestruct "Hge" as (?????????? ?) "$". 
            destruct! H5. simplify_eq.
            destruct (decide (#pid = #pid0)); simplify_eq.
            { iExists pid0, (ctr0-1), _. iPureIntro.
              rewrite lookup_insert_Some. split; eauto.
              split; repeat f_equal; try lia.
              inversion H1; try lia. by simplify_eq. }
            { iExists pid0, ctr1, _. iPureIntro.
              rewrite (lookup_insert_ne _ _ _ _ n).
              rewrite lookup_delete_Some /=. split; eauto. } }
          iDestruct "Hid" as "[$ %]". iPureIntro.
          intros ??. rewrite lookup_insert_None.
          destruct (decide (#pid = #ctr')); simplify_eq.
          { specialize (H5 ctr' H6) as H5'. simplify_eq. }
          rewrite lookup_delete_ne; eauto. }

        iApply ("HΦ" $! (Some _)); iModIntro. iFrame.

      + iDestruct (big_sepM_insert _ (delete #pid m) #pid ((#(ctr0-1), finish)%V) with "[$Hbigsep']")
          as "Hbigsep'"; try apply lookup_delete;
          try (iFrame "Hser' Hserspec'"); try (iExists (ctr0-1)); repeat iExists _;
          try iSplit;
            try (iPureIntro; split; repeat f_equal; try lia;
              inversion H1; try lia; by simplify_eq);
            try (iRight; iFrame "#").
        iMod ("Hclose_tab" with "[$Hl $Hbigsep' $Htok Hpos' Hid]") as "Htok".
        { iNext; iExists ctr; iSplit; try done. 
          iSplitL "Hpos'".
          { do 2 iRight; iFrame "# ∗".
            iExists pid, (ctr0-1), _. iPureIntro.
            rewrite lookup_insert_Some. split; eauto.
            split; repeat f_equal; try lia.
            inversion H1; try lia. by simplify_eq. }
          iDestruct "Hid" as "[$ %]". iPureIntro.
          intros ??. rewrite lookup_insert_None.
          destruct (decide (#pid = #ctr')); simplify_eq.
          { specialize (H5 ctr' H6) as H5'. simplify_eq. }
          rewrite lookup_delete_ne; eauto. }

        iApply ("HΦ" $! (Some _)); iModIntro. iFrame.
  Qed.

  Lemma v_finish_spec2_bad :
    ∀ (a x ser : val) (st : loc),
      {{{ True }}}
        v_finish #st a x ser
        {{{ (finish : val), RET finish;
            finish_spec2_bad finish x a ser }}}.
  Proof.
    iIntros (????? _ ) "HΦ".
    rewrite /v_finish.
    wp_pures. iModIntro. iApply "HΦ".
    rewrite /finish_spec1.
    iIntros (? s s' s'' ???).
    iIntros (?) "!# (Htok & #Hser & #Hserspec & % & % & #hashs & #Hinv & %) HΦ".
    wp_pures. wp_apply ("Hserspec" with "[//] [$Hser $Htok]").
    iIntros ([]); last first.
    { iIntros "(Htok & #Hsers)". wp_pures.
      iModIntro. iApply ("HΦ" $! None). by iFrame. }
    iIntros "(Htok & #[[% Hsers]|%])"; simplify_eq; wp_pures.
    iMod (na_inv_acc with "Hinv Htok") as "(Hinv1 & Htok & Hclose)"; [solve_ndisj|solve_ndisj|].
    iDestruct "Hinv1" as ">[(%s1&%& #hashs1 & %& #Hsusp & %Hser)|(%&%&%& Hsusp & Hproph & %Hser)]";
      wp_load; wp_pures; destruct! Hser; simplify_eq.
    - iPoseProof (hashes_auth.hashed_s_equal s s1 with "[//] hashs hashs1") as "->".
      iMod ("Hclose" with "[$Htok]") as "Htok".
      { iNext. iLeft. iFrame "#". iSplit; eauto. 
        iRight. repeat iExists _. iSplit; eauto. }
      wp_apply wp_hash; try done;
      iIntros "#hashs'"; wp_pures;
      case_bool_decide; simplify_eq; wp_pures.
      { by iPoseProof (hashes_auth.hashed_s_equal s' s1 with "[//] hashs' hashs1") as "->".  }
      iApply ("HΦ" $! None); by iFrame "∗ #".
    
    - wp_apply wp_hash; try done; iIntros "#hashs'"; wp_pures.
      wp_apply (typed_proph_wp_resolve1 StringTypedProph with "Hproph"); try done.
      wp_pures. iModIntro. iIntros (?). wp_pures.
      by iPoseProof (hashes_auth.hashed_s_equal s' s with "[//] hashs' hashs") as "->".
  Qed.


  Definition is_proof (v : val) : iProp Σ :=
    ∃ (l : list string), ⌜is_list l v⌝.

  Definition is_proof_state (v : val) (counter : nat) : iProp Σ :=
    ∃ prf, ⌜v = (prf, #counter)%V⌝ ∗ is_proof prf.

  Definition lrel_auth_comp_post (A : lrel_bi Σ) : lrel Σ :=
    LRel (λ v1 a2, ∃ a1 prf1 counter, ⌜v1 = (prf1, a1)%V⌝ ∗ 
      is_proof_state prf1 counter ∗ A a1 a2)%I.

  Definition lrel_auth_comp_post_bad (A_un : lrel_un Σ) : lrel_un Σ :=
    LRelUn (λ v1, ∃ prf1 x counter,
          ⌜v1 = (prf1, x)%V⌝ ∗ is_proof_state prf1 counter ∗ A_un x)%I.

  Definition lrel_bin_auth_comp' (A : lrel_bi Σ) : lrel Σ := LRel (λ v1 v2,
    ∀ t K (w w' : val) (cntr : nat),
      {{{ spec_ideal t (fill K (v2 w')) ∗ seq_tok ⊤ ∗ 
          is_proof_state w cntr ∗ good_pos ∗ id_frag cntr }}}
        v1 w
      {{{ (o1 : option val), RET $o1;
          seq_tok ⊤ ∗
            if o1 is Some w1 then
              ∃ (a prfst prf : val) (cntr' : nat), id_frag cntr' ∗
                 ⌜w1 = (prfst, a)%V ∧ prfst = (prf, #cntr')%V⌝ ∗
                  ((∃ (w2 : val), spec_ideal t (fill K w2) ∗ 
                    lrel_auth_comp_post A w1 w2 ∗ good_pos) ∨ 
                    lrel_auth_comp_post_bad (lrel_bi_un A) w1 ∗ bad_pos)
            else True }}})%I.

  Definition lrel_un_auth_comp' (A_un : lrel_un Σ) : lrel_un Σ := LRelUn (λ v1,
    ∀ (w : val) (cntr : nat),
      {{{ seq_tok ⊤ ∗ is_proof_state w cntr ∗ bad_pos ∗ id_frag cntr }}}
        v1 w
      {{{ (o1 : option val), RET $o1;
          seq_tok ⊤ ∗
            if o1 is Some w1 then
              ∃ (a prfst prf : val) (cntr' : nat), id_frag cntr' ∗
                ⌜w1 = (prfst, a)%V ∧ prfst = (prf, #cntr')%V⌝ ∗
                  lrel_auth_comp_post_bad A_un w1 ∗ bad_pos
            else True }}})%I.

  Definition lrel_auth_comp' (A : lrel_bi Σ) : lrel_bi Σ :=
    LRelBi (lrel_un_auth_comp' (lrel_bi_un A)) (lrel_bin_auth_comp' A).
        
  Program Definition lrel_auth_comp : kindO Σ (⋆ ⇒ ⋆)%kind := λne A, lrel_auth_comp' A.
  Next Obligation.
    intros ????. split; [intros ?|intros ??];
      rewrite /lrel_car/= /lrel_un_car/= /lrel_un_auth_comp' /lrel_bin_auth_comp'.
    do 27 f_equiv; first solve_proper.
    do 37 f_equiv; solve_proper.
  Qed.
  
  Definition auth_ctx {Θ} (Δ : ctxO Σ Θ) := ext (ext Δ lrel_auth) lrel_auth_comp.

  Lemma refines_un_auth_return Θ (Δ : ctxO Σ Θ) (A : kindO Σ ⋆) v :
    lrel_bi_un A v -∗
    lrel_bi_un (⟦ var1 ⟧ (ext (auth_ctx Δ) A) A) (λ: "pf", InjR ("pf", v))%V.
  Proof.
    iIntros "#HA".
    rewrite interp_var1_ext2.
    iIntros (?? Ψ) "!# (Htok & %H & Hpos & Hid) HΨ".
    simpl in H. destruct H as (? & -> & Hp).
    wp_pures. iModIntro. iApply ("HΨ" $! (Some _)).
    iFrame. do 3 iExists _.
    iSplit; first done. iFrame.
    iExists _, _. iFrame "HA".
    iExists _. iSplit; [done|]. rewrite /is_proof_state.
    eauto.
  Qed.

  Lemma refines_auth_return Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆, var0 → var1 var0 ⟧ (auth_ctx Δ) v_return i_return.
  Proof.
    iSplit; interp_unfold!.
    { iIntros (A ??) "!# _".
      iIntros (??) "(Hi & Htok)".
      rewrite /v_return /i_return.
      i_pures; wp_pures.
      iModIntro. iFrame.
      iSplit; interp_unfold!.
      { iIntros (??) "!# #HA".
        iIntros (??) "(Hi & Htok)".
        i_pures; wp_pures.
        iModIntro. iFrame. clear.
        iSplit; interp_unfold!.
        { rewrite interp_var1_ext2.
          iIntros (????? Ψ) "!# (Hi & Htok & %H & Hpos & Hid) HΨ".
          simpl in H. destruct H as (? & -> & Hp).
          i_pures; wp_pures.
          iModIntro. iApply ("HΨ" $! (Some _)).
          iFrame. iExists _, _, _.
          iSplit; first done. iFrame.
          iLeft. iFrame. iExists _, _.
          iFrame "HA".
          iExists _. iSplit; [done|]. rewrite /is_proof_state.
          eauto. }
        { iDestruct "HA" as "[_ HA]".
          iApply (refines_un_auth_return with "HA"). } }
      { rewrite interp_un_arr_unfold.
        iIntros (?) "!# #HA Htok".
        wp_pures. iModIntro. iFrame. clear.
        interp_unfold!. interp_unfold! in "HA".
        iApply (refines_un_auth_return with "HA"). }}
    { rewrite interp_un_forall_unfold.
      iIntros (A ?) "!# _ Htok".
      rewrite /v_return. wp_pures.
      iModIntro. iFrame.
      rewrite interp_un_arr_unfold.
      iIntros (?) "!# #HA Htok".
      wp_pures. iModIntro. iFrame. clear.
      interp_unfold!. interp_unfold! in "HA".
      iApply (refines_un_auth_return with "HA"). }
  Qed.

  Lemma refines_un_auth_bind Θ (Δ : ctxO Σ Θ) (A B : kindO Σ ⋆) (v w : val) :
    lrel_bi_un (⟦ var2 ⟧ (ext (ext (auth_ctx Δ) A) B) A) v -∗
    lrel_bi_un (⟦ var1 → var2 var0 ⟧ (ext (ext (auth_ctx Δ) A) B)) w -∗
    lrel_bi_un (⟦ var2 ⟧ (ext (ext (auth_ctx Δ) A) B) B)
      (λ: "pf",
        match: v "pf" with InjL <> => InjL #()
        | InjR "x" => let: "a" := "x" in let: "pf'" := Fst "a" in let: "a" := Snd "a" in w "a" "pf'" end)%V.
  Proof.
    iIntros "#HmA #HmB".
    rewrite interp_var2_ext3. 
    iIntros (?? Ψ) "!# (Htok & #Hprf & Hpos & Hid) HΨ". wp_pures.
    wp_pures. wp_bind (v _)%I.
    wp_apply ("HmA" with "[$Htok $Hprf $Hpos $Hid]").
    iIntros (o) "[Htok Ho]".
    destruct o; last first.
    { wp_pures. iApply ("HΨ" $! None). by iFrame. }
    iPoseProof "Hprf" as (??) "Hprf'". 
    iDestruct "Ho" as (????) "(Hid & [%%] & [(%&%&%&%& #Hprf1 & HA) Hpos])".
    iPoseProof "Hprf1" as (??) "Hprf1'". 
    simplify_eq. wp_pures.
    rewrite interp_un_arr_unfold.
    iSpecialize ("HmB" with "[HA] [$Htok]").
    { by interp_unfold!. }
    wp_apply (wp_wand with "HmB").
    iIntros (?) "(H & Htok) /=".
    interp_unfold in "H".
    rewrite interp_var2_ext3.
    wp_apply ("H" with "[$Htok $Hprf1 $Hpos $Hid]").
    iIntros (o) "[Htok Ho] /=".
    iApply "HΨ". iFrame.
  Qed.

  Lemma refines_auth_bind Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆; ⋆, var2 var1 → (var1 → var2 var0) → var2 var0 ⟧
      (auth_ctx Δ) v_bind i_bind.
  Proof.
    iSplit; interp_unfold!.
    { iIntros (A ??) "!# _".
      iIntros (??) "(Hi & Htok)".
      rewrite /v_bind/i_bind.
      i_pures; wp_pures.
      iModIntro. iFrame. clear.
      iSplit; interp_unfold!.
      { iIntros (B ??) "!# _".
        iIntros (??) "(Hi & Htok)".
        i_pures; wp_pures.
        iModIntro. iFrame. clear.
        iSplit; interp_unfold!.
        { iIntros (v1 v2) "!# #HmA".
          iIntros (??) "(Hi & Htok)".
          i_pures; wp_pures.
          iModIntro. iFrame. clear.
          iSplit; interp_unfold!.
          { iIntros (w1 w2) "!# #HmB".
            iIntros (??) "(Hi & Htok)".
            i_pures; wp_pures.
            iModIntro. iFrame. clear.
            interp_unfold in "HmA".
            iSplit; interp_unfold!.
            { rewrite interp_var2_ext3.
              iIntros (u1 u2 ??? Ψ) "!# (Hi & Htok & Hprf & Hpos & Hid) HΨ".
              i_pures; wp_pures.
              i_bind (v2 _)%I; wp_bind (v1 _)%I.
              iDestruct "HmA" as "[HmA _]".
              wp_apply ("HmA" with "[$Hi $Htok $Hprf $Hpos $Hid]").
              iIntros (o) "[Htok Ho]".
              destruct o; last first.
              { wp_pures. iApply ("HΨ" $! None). by iFrame. }
              iDestruct "Ho" as (????) "(Hid & %H & [H|H])".
              + iDestruct "H" as (?) "(Hi & H & Hpos)".
                iDestruct "H" as (? a1' a2 ->) "[#Hprf #HA]".
                wp_pures.
                wp_bind (w1 _)%E; i_bind (w2 _ )%E.
                iDestruct "HmB" as "[HmB _]".
                interp_unfold in "HmB".
                iSpecialize ("HmB" with "HA [$Hi $Htok]").
                wp_apply (wp_wand with "HmB").
                iIntros (v) "(% & Hi & H & Htok) /=".
                destruct! H. simplify_eq.
                iPoseProof "Hprf" as (??) "Hprf'". simplify_eq.
                interp_unfold in "H". rewrite interp_var2_ext3.
                iDestruct "H" as "[H _]".
                wp_apply ("H" with "[$Hi $Htok $Hprf $Hpos $Hid]").
                iIntros (?) "(Htok & Ho) /=".
                iApply "HΨ". iFrame.
              + iDestruct "H" as "[H Hpos]".
                iDestruct "H" as (??? ->) "(#Hprf & #HA)".
                wp_pures.
                wp_bind (w1 _)%E.
                iDestruct "HmB" as "[_ HmB]".
                rewrite interp_un_arr_unfold.
                iSpecialize ("HmB" with "[HA] [$Htok]").
                { by interp_unfold!. }
                wp_apply (wp_wand with "HmB").
                iIntros (v) "(H & Htok) /=".
                interp_unfold in "H".
                destruct! H. simplify_eq.
                iPoseProof "Hprf" as (??) "Hprf'". simplify_eq.
                rewrite interp_var2_ext3.
                wp_apply ("H" with "[$Htok $Hprf $Hpos $Hid]").
                iIntros (?) "(Htok & Ho) /=".
                iApply "HΨ". iFrame.
                destruct o1; last done. iFrame.
                iDestruct "Ho" as (????) "($ & % & $)".
                eauto. }
            { iDestruct "HmA" as "[_ HmA]".
              iDestruct "HmB" as "[_ HmB]".
              iApply (refines_un_auth_bind with "HmA HmB"). } }
          { rewrite interp_un_arr_unfold.
            iIntros (w1) "!# #HmB Htok".
            wp_pures. iModIntro. iFrame.
            interp_unfold in "HmA".
            iDestruct "HmA" as "[_ HmA]".
            interp_unfold!.
            iApply (refines_un_auth_bind with "HmA HmB"). } }
        { rewrite interp_un_arr_unfold.
          iIntros (v1) "!# #HmA Htok".
          wp_pures. iModIntro. iFrame.
          rewrite interp_un_arr_unfold.
          iIntros (w1) "!# #HmB Htok".
          wp_pures. iModIntro. iFrame.
          interp_unfold in "HmA".
          interp_unfold!.
          iApply (refines_un_auth_bind with "HmA HmB"). } }
      { rewrite interp_un_forall_unfold.
        iIntros (B ?) "!# _ Htok".
        wp_pures. iModIntro. iFrame.
        rewrite interp_un_arr_unfold.
        iIntros (v1) "!# #HmA Htok".
        wp_pures. iModIntro. iFrame.
        rewrite interp_un_arr_unfold.
        iIntros (w1) "!# #HmB Htok".
        wp_pures. iModIntro. iFrame.
        interp_unfold in "HmA".
        interp_unfold!.
        iApply (refines_un_auth_bind with "HmA HmB"). } }
    { rewrite interp_un_forall_unfold.
      iIntros (A ?) "!# _ Htok".
      rewrite /v_bind. wp_pures.
      iModIntro. iFrame.
      rewrite interp_un_forall_unfold.
      iIntros (B ?) "!# _ Htok".
      wp_pures. iModIntro. iFrame.
      rewrite interp_un_arr_unfold.
      iIntros (v1) "!# #HmA Htok".
      wp_pures. iModIntro. iFrame.
      rewrite interp_un_arr_unfold.
      iIntros (w1) "!# #HmB Htok".
      wp_pures. iModIntro. iFrame.
      interp_unfold in "HmA".
      interp_unfold!.
      iApply (refines_un_auth_bind with "HmA HmB"). }
  Qed.

  Lemma refines_un_auth_unauth c :
    ∀ (ser deser count v : val) tA' A,
    inv_susp_table c -∗
    ser_spec_un (lrel_bi_un A) ser tA' -∗
    ser_spec_3 ser tA' -∗
    count_spec count tA' -∗
    deser_spec authBaseN (lrel_bi_un A) deser tA' -∗
    auth_some_un authBaseN (lrel_bi_un A) v -∗
    lrel_bi_un (lrel_auth_comp A)
      (λ: "proof",
        match: InjRV v with
          InjL <> => InjL #()
        | InjR "a" =>
          let: "counter" := "proof" in
          let: "pf_stream" := Fst "counter" in
          let: "counter" := Snd "counter" in
          match: list_head "pf_stream" with
            InjL <> => InjL #()
          | InjR "p" =>
            let: "id" := "counter" in
            let: "serialize" := (ser, deser, count)%V in
            let: "deserialize" := Snd (Fst "serialize") in
            let: "count" := Snd "serialize" in
            let: "serialize" := Fst (Fst "serialize") in
            match: "deserialize" "id" "p" with
              InjL <> => InjL #()
            | InjR "x" =>
              let: "nchild" := "count" "x" in
              let: "finish" := v_finish #c "a" "x" "serialize" in
              match: if: "nchild" = #0 then "finish" #() else #c <- map.map_insert "id" ("nchild", "finish") ! #c;;  InjRV #() with
                InjL <> => InjL #()
              | InjR <> => InjR (list_tail "pf_stream", "id" + #1, "x")
              end
            end
          end
        end)%V.
  Proof.
    iIntros (??????) "#Htab #Hser' #Hser3 #Hcount #Hdeser #Hauth_un".
    iIntros (???) "!# (Htok & Hproof & Hpos & Hid) HΦ".
    wp_pures.
    iDestruct "Hproof" as (? -> ) "Hproof".
    wp_pures. iDestruct "Hproof" as "(% & %)".
    wp_apply gwp_list_head; [done| ].
    iIntros (vl [[-> ->] | (s1' &?& -> & -> )]).
    { wp_pures. iModIntro.
      iApply ("HΦ" $! None). iFrame. }

    wp_pures. wp_apply "Hdeser"; [done|].
    iIntros (?) "Hdepar".
    wp_apply "Hdepar"; [done|].
    iIntros ([]); last first.
    { iIntros "_". wp_pures. iApply ("HΦ" $! None). iFrame. eauto. }
    
    iPoseProof "Hauth_un" as "[(%&%)|(%&%&%&#Hinv)]";
      simplify_eq; iIntros "[Hserser Hserproph]";
      iPoseProof ("Hserproph" with "Hserser") as ">[#HA_un [%s2 #Hserproph]]";
      wp_pures; wp_apply ("Hcount" $! _ _ ⊤ with "[//] [$Hserproph $Htok]");
      iIntros (?) "[_ Htok]"; wp_pures.
    - wp_apply v_finish_spec1; try done.
      iIntros (finish) "Hfinish". wp_pures.

      case_bool_decide; wp_pures; simplify_eq.
      + wp_bind (finish #()).
        assert (c0 = 0); [lia|]. simplify_eq.

        iMod (na_inv_acc with "Htab Htok") as "(Htabo & Htok & Hclose_tab)"; [solve_ndisj|solve_ndisj|].
        iDestruct "Htabo" as (???) "(Hl & >%Hm & Hbigsep & Hge & >Hid' & >%Hidinv)".

        iPoseProof (id_agree with "Hid Hid'") as (->) "[Hid Hid']".
        iMod (id_update _ (ctr+1) with "Hid Hid'") as "[Hid Hid']".

        iMod ("Hclose_tab" with "[$Htok $Hl $Hbigsep $Hge $Hid']") as "Htok".
        { iNext. iFrame "%". iPureIntro. intros ??. apply Hidinv. lia. }

        iApply ("Hfinish" $! ⊤ with "[//] [$Htok $Hserproph $Hser3 //]").
        iNext. iIntros ([]) "Htok"; wp_pures; last first.
        { iApply ("HΦ" $! (None)). by iFrame. }

        wp_apply gwp_list_tail; [done|].
        iIntros (vl Hl). wp_pures.
        
        iApply ("HΦ" $! (Some _)).
        iFrame "# ∗"; iModIntro; repeat (iExists _);
          iSplit; try (iSplit; try done; iPureIntro; repeat f_equal; lia); 
          iFrame "# ∗ %"; iExists _, (ctr+1);
          iSplit; iPureIntro; repeat f_equal; lia.

      + iMod (na_inv_acc with "Htab Htok") as "(Htabo & Htok & Hclose_tab)"; [solve_ndisj|solve_ndisj|].
        iDestruct "Htabo" as (???) "(Hl & >%Hm & Hbigsep & Hge & Hid' & >%Hidinv)". wp_load.

        iPoseProof (id_agree with "Hid Hid'") as (->) "[Hid Hid']".
        iMod (id_update _ (ctr+1) with "Hid Hid'") as "[Hid Hid']".

        wp_pures. wp_bind (map.map_insert _ _ _).
        wp_apply (gwp_map_insert #ctr); try done.
        
        iIntros (d') "%Hmap'". wp_store.
        wp_pures. wp_apply (gwp_list_tail with "[//]").
        iIntros "/=" (tl Htl). wp_pures.
        iDestruct "Hge" as "[Hpos'|[Hpos'|[Hpos' Hge]]]";
          iPoseProof (pos_agree with "Hpos Hpos'") as (?) "[Hpos Hpos']"; 
          simplify_eq.

        iMod ("Hclose_tab" with "[$Hl Hbigsep Hpos' $Htok Hfinish Hge $Hid']") as "Htok".
        { iNext. iExists _. iSplit; try done. 
          iSplit; [|iSplitL "Hpos' Hfinish Hge"].
          { iApply (big_sepM_insert_2 with "[Hfinish]"); last done.
            assert (c0 > 0).
            { apply Nat.neq_0_lt_0. intros ->. by apply H0. }
            repeat iExists _. repeat (try (iSplit; eauto)).
            do 2 iLeft. iFrame. eauto. }
          { iDestruct "Hge" as (?????????? Hv) "Hge".
            destruct! Hv. simplify_eq.
            do 2 iRight. iFrame. iExists pid, ctr0, _.
            destruct (decide (#ctr = #pid)); simplify_eq.
            { specialize (Hidinv pid ltac:(lia)). simplify_eq. }
            iPureIntro. rewrite lookup_insert_ne; eauto. }
          iPureIntro. intros ??.
          specialize (Hidinv ctr' ltac:(lia)).
          rewrite lookup_insert_None. split; eauto.
          intros ?. simplify_eq. lia. }

        iApply ("HΦ" $! (Some _)).
        iFrame "# ∗"; iModIntro; repeat (iExists _);
          iSplit; try (iSplit; try done; iPureIntro; repeat f_equal; lia); 
          iFrame "# ∗ %"; iExists _, (ctr+1);
          iSplit; iPureIntro; repeat f_equal; lia.
    
    - wp_apply (v_finish_spec2 with "Htab").
      iIntros (finish) "Hfinish". wp_pures.

      case_bool_decide; wp_pures; simplify_eq.
      * wp_bind (finish #()).
        assert (c0 = 0); [lia|]. simplify_eq.

        iMod (na_inv_acc with "Htab Htok") as "(Htabo & Htok & Hclose_tab)"; [solve_ndisj|solve_ndisj|].
        iDestruct "Htabo" as (???) "(Hl & >%Hm & Hbigsep & Hge & >Hid' & >%Hidinv)".

        iPoseProof (id_agree with "Hid Hid'") as (->) "[Hid Hid']".
        iMod (id_update _ (ctr+1) with "Hid Hid'") as "[Hid Hid']".

        iMod ("Hclose_tab" with "[$Htok $Hl $Hbigsep $Hge $Hid']") as "Htok".
        { iNext. iFrame "%". iPureIntro. intros ??. apply Hidinv. lia. }
        
        iApply ("Hfinish" $! ⊤ with "[//] [$Htok $Hserproph $Hser3 $Hinv $Hpos]"); eauto.
        iNext. iIntros ([]) "[Htok Hpos]"; wp_pures; last first.
        { iApply ("HΦ" $! (None)). eauto. }

        wp_apply gwp_list_tail; [done|].
        iIntros (vl Hl). wp_pures.
        
        iApply ("HΦ" $! (Some _)).
        iFrame "# ∗"; iModIntro; repeat (iExists _);
          iSplit; try (iSplit; try done; iPureIntro; repeat f_equal; lia); 
          iFrame "# ∗ %"; iExists _, (ctr+1);
          iSplit; iPureIntro; repeat f_equal; lia.
      
      * iMod (na_inv_acc with "Htab Htok") as "(Htabo & Htok & Hclose_tab)"; [solve_ndisj|solve_ndisj|].
        iDestruct "Htabo" as (???) "(Hl & >%Hm & Hbigsep & Hge & Hid' & >%Hidinv)". wp_load.

        iPoseProof (id_agree with "Hid Hid'") as (->) "[Hid Hid']".
        iMod (id_update _ (ctr+1) with "Hid Hid'") as "[Hid Hid']".

        wp_bind (map.map_insert _ _ _). wp_pures.
        iApply (gwp_map_insert #ctr (#c0, finish)%V d m _ _); [done|done|].
        
        iModIntro. iIntros (d') "%Hmap'". wp_store.
        wp_pures. wp_apply (gwp_list_tail with "[//]").
        iIntros "/=" (tl Htl). wp_pures.
        iDestruct "Hge" as "[Hpos'|[Hpos'|[Hpos' Hge]]]";
          iPoseProof (pos_agree with "Hpos Hpos'") as (?) "[Hpos Hpos']"; 
          simplify_eq.

        iMod ("Hclose_tab" with "[$Hl Hbigsep Hpos' $Htok Hfinish Hge $Hid']") as "Htok".
        { iNext. iExists _. iSplit; try done. 
          iSplit; [|iSplitL "Hpos' Hfinish Hge"].
          { iApply (big_sepM_insert_2 with "[Hfinish]"); last done.
            assert (c0 > 0).
            { apply Nat.neq_0_lt_0. intros ->. by apply H0. }
            repeat iExists _. repeat (try (iSplit; eauto)).
            iLeft. iRight. iFrame. eauto. }
          { iDestruct "Hge" as (?????????? Hv) "Hge".
            destruct! Hv. simplify_eq.
            do 2 iRight. iFrame. iExists pid, ctr0, _.
            destruct (decide (#ctr = #pid)); simplify_eq.
            { specialize (Hidinv pid ltac:(lia)). simplify_eq. }
            iPureIntro. rewrite lookup_insert_ne; eauto. }
          iPureIntro. intros ??.
          specialize (Hidinv ctr' ltac:(lia)).
          rewrite lookup_insert_None. split; eauto.
          intros ?. simplify_eq. lia. }

        iApply ("HΦ" $! (Some _)).
        iFrame "# ∗"; iModIntro; repeat (iExists _);
          iSplit; try (iSplit; try done; iPureIntro; repeat f_equal; lia); 
          iFrame "# ∗ %"; iExists _, (ctr+1);
          iSplit; iPureIntro; repeat f_equal; lia.
  Qed.

  Lemma refines_auth_unauth Θ (Δ : ctxO Σ Θ) c :
    inv_susp_table c
    ⊢ REL v_unauth #c << i_unauth :
      ⟦ ∀: ⋆, var1 var0 → var3 var0 → var2 var0 ⟧ (ext (auth_ctx Δ) lrel_evidence).
  Proof.
    iIntros "#Htab" (??) "(Hi & Htok)".
    rewrite /v_unauth /i_unauth.
    wp_pures.
    iFrame. iModIntro.
    iSplit; interp_unfold!.
    { iIntros (A v1 v2) "!# _".
      iIntros (??) "(Hi & Htok)".
      i_pures; wp_pures.
      iModIntro. iFrame. clear.
      iSplit; interp_unfold!.
      { iIntros (??) "!# #Hevi".
        iIntros (??) "(Hi & Htok)".
        i_pures; wp_pures.
        iModIntro. iFrame. clear.
        iSplit; interp_unfold!.
        { iIntros (w1 w2) "!# #Hauth /=".
          iIntros (??) "(Hi & Htok)".
          i_pures.
          interp_unfold in "Hevi Hauth".
          rewrite interp_var3_ext4.
          iDestruct "Hauth" as "[Hauth_bi Hauth_un]".
          iDestruct "Hauth_bi" as "[(% & -> & Hauth_bi)|->]"; wp_pures; last first.
          { iFrame. iModIntro.
            interp_unfold!. rewrite interp_var2_ext3. iSplit.
            { iIntros (??????) "!# (Hi & Htok & Hproof & Hpos & Hid) HΦ".
              wp_pures. iApply ("HΦ" $! None). by iFrame. }
            iIntros (???) "!# (Htok & Hproof & Hpos) HΦ".
            wp_pures. iApply ("HΦ" $! None). by iFrame. }
          iDestruct "Hauth_un" as "[(% & % & Hauth_un)|->]"; last first.
          { iFrame. iModIntro.
            interp_unfold!. rewrite interp_var2_ext3. iSplit.
            { iIntros (??????) "!# (Hi & Htok & Hproof & Hpos & Hid) HΦ".
              wp_pures. iApply ("HΦ" $! None). by iFrame. }
            iIntros (???) "!# (Htok & Hproof & Hpos) HΦ".
            wp_pures. iApply ("HΦ" $! None). by iFrame. }

          iDestruct "Hevi" as "[Hrel Hevi_un]".    
          iDestruct "Hevi_un" as (tA' ??? ->) "(#Hser' & #Hser3 & #Hcount & #Hdeser)".
          simplify_eq.
          iFrame. iModIntro.
          iSplit; interp_unfold!; rewrite interp_var2_ext3.
          { iIntros (??????) "!# (Hi & Htok & Hproof & Hpos & Hid) HΦ".
            wp_pures. i_pures. iDestruct "Hproof" as (? -> ) "Hproof".
            wp_pures. iDestruct "Hproof" as "(% & %)".
            wp_apply gwp_list_head; [done| ].
            iIntros (vl [[-> ->] | (s1' &?& -> & -> )]).
            { wp_pures. iModIntro.
              iApply ("HΦ" $! None). iFrame. }

            wp_pures. wp_apply "Hdeser"; [done|].
            iIntros (?) "Hdepar".
            wp_apply "Hdepar"; [done|].
            iIntros ([]); last first.
            { iIntros "_". wp_pures. iApply ("HΦ" $! None). iFrame. eauto. }
            
            iPoseProof "Hauth_bi" as "(%&%&%&#hashs1&#Hser1&#HA&[%|(%&%&%&%&#Hinv)])";
              simplify_eq; iIntros "[Hserser Hserproph]";
              iPoseProof ("Hserproph" with "Hserser") as ">[#HA_un [%s2 #Hserproph]]";
            wp_pures; wp_apply ("Hcount" $! _ _ ⊤ with "[//] [$Hserproph $Htok]");
              iIntros (?) "[_ Htok]"; wp_pures.

            - destruct (decide (s2 = s1)); simplify_eq; last first.

              + wp_apply v_finish_spec1_bad; try done.
                iIntros (finish) "Hfinish". wp_pures.

                case_bool_decide; wp_pures; simplify_eq.
                * wp_bind (finish #()).
                  assert (c0 = 0); [lia|]. simplify_eq.

                  iApply ("Hfinish" $! ⊤ with "[//] [$Htok $Hserproph $Hser3 $hashs1 //]").
                  iNext. iIntros ([]) "[Htok %]"; simplify_eq; wp_pures.
                  iApply ("HΦ" $! (None)). by iFrame.

                * iMod (na_inv_acc with "Htab Htok") as "(Htabo & Htok & Hclose_tab)"; [solve_ndisj|solve_ndisj|].
                  iDestruct "Htabo" as (???) "(Hl & >%Hm & Hbigsep & Hge & Hid' & >%Hidinv)". wp_load.

                  iPoseProof (id_agree with "Hid Hid'") as (->) "[Hid Hid']".
                  iMod (id_update _ (ctr+1) with "Hid Hid'") as "[Hid Hid']".

                  iDestruct "Hge" as "[Hpos'|[Hpos'|[Hpos' Hge]]]";
                    iPoseProof (pos_agree with "Hpos Hpos'") as (?) "[Hpos Hpos']"; 
                    simplify_eq.

                  iMod (pos_update1 with "Hpos Hpos'") as "(Hpos & Hpos' & Hfrag)".

                  wp_bind (map.map_insert _ _ _). wp_pures.
                  iApply (gwp_map_insert #ctr (#c0, finish)%V d m _ _); [done|done|].
                  
                  iModIntro. iIntros (d') "%Hmap'". wp_store.
                  wp_pures. wp_apply (gwp_list_tail with "[//]").
                  iIntros "/=" (tl Htl). wp_pures.
                  iMod ("Hclose_tab" with "[$Hl Hbigsep $Htok Hfinish Hpos' Hfrag $Hid']") as "Htok".
                  { iNext. iFrame "# %". iSplit; [|iSplitL].
                    { iApply (big_sepM_insert_2 with "[Hfinish Hfrag]"); last done.
                      assert (c0 > 0).
                      { apply Nat.neq_0_lt_0. intros ->. by apply H0. }
                      repeat iExists _. repeat (try (iSplit; eauto)).
                      iRight. iFrame. iExists _. iLeft. by iFrame "# ∗". }
                    { do 2 iRight. iFrame "∗ #". iExists ctr, c0. repeat iExists _.
                      iSplit; [|iLeft; by iFrame]. iPureIntro.
                      rewrite lookup_insert. repeat (split; eauto).
                      assert (c0 ≠ 0); try lia.
                      intros ?. simplify_eq. } 
                    iPureIntro. intros ??.
                    specialize (Hidinv ctr' ltac:(lia)).
                    rewrite lookup_insert_None. split; eauto.
                    intros ?. simplify_eq. lia. }

                  iModIntro. iApply ("HΦ" $! (Some _)). iFrame "∗ % #". 
                  repeat (iExists _). iSplit.
                  { iPureIntro. split; repeat f_equal. lia. }
                  iRight; iFrame "# ∗ %"; iExists _, (ctr+1);
                    iSplit; iPureIntro; repeat f_equal; lia.
                  
              + wp_apply v_finish_spec1; try done.
                iIntros (finish) "Hfinish". wp_pures.

                case_bool_decide; wp_pures; simplify_eq.
                * wp_bind (finish #()).
                  assert (c0 = 0); [lia|]. simplify_eq.

                  iMod (na_inv_acc with "Htab Htok") as "(Htabo & Htok & Hclose_tab)"; [solve_ndisj|solve_ndisj|].
                  iDestruct "Htabo" as (???) "(Hl & >%Hm & Hbigsep & Hge & >Hid' & >%Hidinv)".

                  iPoseProof (id_agree with "Hid Hid'") as (->) "[Hid Hid']".
                  iMod (id_update _ (ctr+1) with "Hid Hid'") as "[Hid Hid']".

                  iMod ("Hclose_tab" with "[$Htok $Hl $Hbigsep $Hge $Hid']") as "Htok".
                  { iNext. iFrame "%". iPureIntro. intros ??. apply Hidinv. lia. }

                  iApply ("Hfinish" $! ⊤ with "[//] [$Htok $Hserproph $Hser3 //]").
                  iNext. iIntros ([]) "Htok"; simplify_eq; wp_pures; last first.
                  { iApply ("HΦ" $! (None)). by iFrame. }

                  wp_pures. wp_apply (gwp_list_tail with "[//]").
                  iIntros "/=" (tl Htl). wp_pures.

                  iApply ("HΦ" $! (Some _)).
                  iMod ("Hrel" $! ⊤ with "[//] Htok [Hserproph] Hser1 HA") as "[Htok #HA']";
                    try by iRight.
                  iFrame "# ∗". iModIntro; repeat (iExists _);
                  iSplit; try (iSplit; try done; iPureIntro; repeat f_equal; lia);
                  iLeft; iFrame "# ∗ %"; iExists _, (ctr+1);
                    iSplit; iPureIntro; repeat f_equal; lia.
                    
                * iMod (na_inv_acc with "Htab Htok") as "(Htabo & Htok & Hclose_tab)"; [solve_ndisj|solve_ndisj|].
                  iDestruct "Htabo" as (???) "(Hl & >%Hm & Hbigsep & Hge & Hid' & >%Hidinv)". wp_load.

                  iPoseProof (id_agree with "Hid Hid'") as (->) "[Hid Hid']".
                  iMod (id_update _ (ctr+1) with "Hid Hid'") as "[Hid Hid']".

                  iDestruct "Hge" as "[Hpos'|[Hpos'|[Hpos' Hge]]]";
                    iPoseProof (pos_agree with "Hpos Hpos'") as (?) "[Hpos Hpos']"; 
                    simplify_eq.

                  wp_bind (map.map_insert _ _ _). wp_pures.
                  iApply (gwp_map_insert #ctr (#c0, finish)%V d m _ _); [done|done|].
                  
                  iModIntro. iIntros (d') "%Hmap'". wp_store.

                  wp_pures. wp_apply (gwp_list_tail with "[//]").
                  iIntros "/=" (tl Htl). wp_pures.
                  iMod ("Hclose_tab" with "[$Hl Hbigsep $Htok Hfinish Hpos Hid']") as "Htok".
                  { iNext. iFrame "% ∗". iSplitL.
                    { iApply (big_sepM_insert_2 with "[Hfinish]"); last done.
                      assert (c0 > 0).
                      { apply Nat.neq_0_lt_0. intros ->. by apply H0. }
                      repeat iExists _. repeat (try (iSplit; eauto)).
                      do 2 iLeft. iFrame. eauto. }
                    iPureIntro. intros ??.
                    specialize (Hidinv ctr' ltac:(lia)).
                    rewrite lookup_insert_None. split; eauto.
                    intros ?. simplify_eq. lia. }

                  iApply ("HΦ" $! (Some _)).
                  iMod ("Hrel" $! ⊤ with "[//] Htok [Hserproph] Hser1 HA") as "[Htok #HA']";
                    try by iRight.
                  iFrame "# ∗"; iModIntro; repeat (iExists _).
                  iSplit; try (iSplit; try done; iPureIntro; repeat f_equal; lia).
                  iLeft. iFrame "# ∗ %"; iExists _, (ctr+1);
                    iSplit; iPureIntro; repeat f_equal; lia.

            - destruct (decide (s1 = s2)); simplify_eq; last first.

              + wp_apply v_finish_spec2_bad; try done.
                iIntros (finish) "Hfinish". wp_pures.

                case_bool_decide; wp_pures; simplify_eq.
                * wp_bind (finish #()).
                  assert (c0 = 0); [lia|]. simplify_eq.

                  iApply ("Hfinish" $! ⊤ with "[//] [$Htok $Hserproph $Hser3 $hashs1 $Hinv //]").
                  iNext. iIntros ([]) "[Htok %]"; simplify_eq; wp_pures.
                  iApply ("HΦ" $! (None)). by iFrame.
                
                * iMod (na_inv_acc with "Htab Htok") as "(Htabo & Htok & Hclose_tab)"; [solve_ndisj|solve_ndisj|].
                  iDestruct "Htabo" as (???) "(Hl & >%Hm & Hbigsep & Hge & Hid' & >%Hidinv)". wp_load.

                  iPoseProof (id_agree with "Hid Hid'") as (->) "[Hid Hid']".
                  iMod (id_update _ (ctr+1) with "Hid Hid'") as "[Hid Hid']".

                  iDestruct "Hge" as "[Hpos'|[Hpos'|[Hpos' Hge]]]";
                    iPoseProof (pos_agree with "Hpos Hpos'") as (?) "[Hpos Hpos']"; 
                    simplify_eq.

                  iMod (pos_update1 with "Hpos Hpos'") as "(Hpos & Hpos' & Hfrag)".

                  wp_bind (map.map_insert _ _ _). wp_pures.
                  iApply (gwp_map_insert #ctr (#c0, finish)%V d m _ _); [done|done|].
                  
                  iModIntro. iIntros (d') "%Hmap'". wp_store.

                  (* iMod (msize_update _ (s+1) with "[$Hms $Hs]") as "[Hms Hs]". *)
                  wp_pures. wp_apply (gwp_list_tail with "[//]").
                  iIntros "/=" (tl Htl). wp_pures.
                  iMod ("Hclose_tab" with "[$Hl Hbigsep $Htok Hfinish Hpos' Hfrag Hid']") as "Htok".
                  { iNext. iFrame "% ∗". iSplit; [|iSplitL].
                    { iApply (big_sepM_insert_2 with "[Hfinish Hfrag]"); last done.
                      assert (c0 > 0).
                      { apply Nat.neq_0_lt_0. intros ->. by apply H0. }
                      repeat iExists _. repeat (try (iSplit; eauto)).
                      iRight. iFrame. iExists _. iRight. by iFrame "# ∗". }
                    { do 2 iRight. iFrame "∗ #". iExists ctr, c0. repeat iExists _.
                      iSplit; [|iRight; by iFrame]. iPureIntro.
                      rewrite lookup_insert. repeat (split; eauto).
                      assert (c0 ≠ 0); try lia.
                      intros ?. simplify_eq. } 
                    iPureIntro. intros ??.
                    specialize (Hidinv ctr' ltac:(lia)).
                    rewrite lookup_insert_None. split; eauto.
                    intros ?. simplify_eq. lia. }
                  
                  iModIntro. iApply ("HΦ" $! (Some _)). iFrame "∗ % #". 
                  repeat (iExists _). iSplit.
                  { iPureIntro. split; repeat f_equal. lia. }
                  iRight; iFrame "# ∗ %"; iExists _, (ctr+1);
                    iSplit; iPureIntro; repeat f_equal; lia.

              + wp_apply (v_finish_spec2 with "Htab").
                iIntros (finish) "Hfinish". wp_pures.

                case_bool_decide; wp_pures; simplify_eq.
                * wp_bind (finish #()).
                  assert (c0 = 0); [lia|]. simplify_eq.

                  iMod (na_inv_acc with "Htab Htok") as "(Htabo & Htok & Hclose_tab)"; [solve_ndisj|solve_ndisj|].
                  iDestruct "Htabo" as (???) "(Hl & >%Hm & Hbigsep & Hge & >Hid' & >%Hidinv)".

                  iPoseProof (id_agree with "Hid Hid'") as (->) "[Hid Hid']".
                  iMod (id_update _ (ctr+1) with "Hid Hid'") as "[Hid Hid']".

                  iMod ("Hclose_tab" with "[$Htok $Hl $Hbigsep $Hge $Hid']") as "Htok".
                  { iNext. iFrame "%". iPureIntro. intros ??. apply Hidinv. lia. }

                  iApply ("Hfinish" $! ⊤ with "[//] [$Htok $Hserproph $Hser3 $Hinv $Hpos]"); eauto.
                  iNext. iIntros ([]) "[Htok Hpos]"; wp_pures; last first.
                  { iApply ("HΦ" $! (None)). eauto. }

                  wp_apply gwp_list_tail; [done|].
                  iIntros (vl Hl). wp_pures.

                  iApply ("HΦ" $! (Some _)).
                  iMod ("Hrel" $! ⊤ with "[//] Htok [Hserproph] Hser1 HA") as "[Htok #HA']";
                    try by iRight.
                  iFrame "# ∗"; iModIntro; repeat (iExists _).
                  iSplit; try (iSplit; try done; iPureIntro; repeat f_equal; lia).
                  iLeft. iFrame "# ∗ %"; iExists _, (ctr+1);
                    iSplit; iPureIntro; repeat f_equal; lia.
                
                * iMod (na_inv_acc with "Htab Htok") as "(Htabo & Htok & Hclose_tab)"; [solve_ndisj|solve_ndisj|].
                  iDestruct "Htabo" as (???) "(Hl & >%Hm & Hbigsep & Hge & Hid' & >%Hidinv)". wp_load.

                  iPoseProof (id_agree with "Hid Hid'") as (->) "[Hid Hid']".
                  iMod (id_update _ (ctr+1) with "Hid Hid'") as "[Hid Hid']".

                  iDestruct "Hge" as "[Hpos'|[Hpos'|[Hpos' Hge]]]";
                    iPoseProof (pos_agree with "Hpos Hpos'") as (?) "[Hpos Hpos']"; 
                    simplify_eq.

                  wp_bind (map.map_insert _ _ _). wp_pures.
                  iApply (gwp_map_insert #ctr (#c0, finish)%V d m _ _); [done|done|].
                  
                  iModIntro. iIntros (d') "%Hmap'". wp_store.

                  wp_pures. wp_apply (gwp_list_tail with "[//]").
                  iIntros "/=" (tl Htl). wp_pures.
                  iMod ("Hclose_tab" with "[$Hl Hbigsep $Htok Hfinish Hpos Hid']") as "Htok".
                  { iNext. iFrame "% ∗". iSplitL.
                    { iApply (big_sepM_insert_2 with "[Hfinish]"); last done.
                      assert (c0 > 0).
                      { apply Nat.neq_0_lt_0. intros ->. by apply H0. }
                      repeat iExists _. repeat (try (iSplit; [done|])).
                      iLeft. iRight. by iFrame "# ∗". }
                    iPureIntro. intros ??.
                    specialize (Hidinv ctr' ltac:(lia)).
                    rewrite lookup_insert_None. split; eauto.
                    intros ?. simplify_eq. lia. }
                  
                  iApply ("HΦ" $! (Some _)).
                  iMod ("Hrel" $! ⊤ with "[//] Htok [Hserproph] Hser1 HA") as "[Htok #HA']";
                    try by iRight.
                  iFrame "# ∗"; iModIntro; repeat (iExists _).
                  iSplit; try (iSplit; try done; iPureIntro; repeat f_equal; lia).
                  iLeft. iFrame "# ∗ %"; iExists _, (ctr+1);
                    iSplit; iPureIntro; repeat f_equal; lia. }
              
          { iApply (refines_un_auth_unauth with "Htab Hser' Hser3 Hcount Hdeser Hauth_un"). } }
        { rewrite interp_un_arr_unfold.
          iIntros (w) "!# #Hauth Htok /=".
          interp_unfold in "Hevi Hauth".
          rewrite interp_var3_ext4.
          iDestruct "Hauth" as "[(% & % & Hauth_un)|->]"; wp_pures; last first.
          { iFrame. iModIntro.
            interp_unfold!. rewrite interp_var2_ext3.
            iIntros (???) "!# (Htok & Hproof & Hpos) HΦ".
            wp_pures. iApply ("HΦ" $! None). by iFrame. }

          iDestruct "Hevi" as "[Hrel Hevi_un]".    
          iDestruct "Hevi_un" as (tA' ??? ->) "(#Hser' & #Hser3 & #Hcount & #Hdeser)".
          simplify_eq.
          iFrame. iModIntro. interp_unfold!.
          rewrite interp_var2_ext3.
          iApply (refines_un_auth_unauth with "Htab Hser' Hser3 Hcount Hdeser Hauth_un"). } }
      { rewrite interp_un_arr_unfold.
        iIntros (?) "!# #Hevi Htok".
        wp_pures. iModIntro. iFrame. clear.
        rewrite interp_un_arr_unfold.
        iIntros (w) "!# #Hauth Htok /=".
        interp_unfold in "Hevi Hauth".
        rewrite interp_var3_ext4.
        iDestruct "Hauth" as "[(% & % & Hauth_un)|->]"; wp_pures; last first.
        { iFrame. iModIntro.
          interp_unfold!. rewrite interp_var2_ext3.
          iIntros (???) "!# (Htok & Hproof & Hpos) HΦ".
          wp_pures. iApply ("HΦ" $! None). by iFrame. }
            
        iDestruct "Hevi" as (tA' ??? ->) "(#Hser' & #Hser3 & #Hcount & #Hdeser)".
        simplify_eq.
        iFrame. iModIntro. interp_unfold!.
        rewrite interp_var2_ext3.
        iApply (refines_un_auth_unauth with "Htab Hser' Hser3 Hcount Hdeser Hauth_un"). } }
    { rewrite interp_un_forall_unfold.
      iIntros (A v) "!# _ Htok".
      wp_pures.
      iModIntro. iFrame. clear.
      rewrite interp_un_arr_unfold.
      iIntros (?) "!# #Hevi Htok".
      wp_pures. iModIntro. iFrame. clear.
      rewrite interp_un_arr_unfold.
      iIntros (w) "!# #Hauth Htok /=".
      interp_unfold in "Hevi Hauth".
      rewrite interp_var3_ext4.
      iDestruct "Hauth" as "[(% & % & Hauth_un)|->]"; wp_pures; last first.
      { iFrame. iModIntro.
        interp_unfold!. rewrite interp_var2_ext3.
        iIntros (???) "!# (Htok & Hproof & Hpos) HΦ".
        wp_pures. iApply ("HΦ" $! None). by iFrame. }
          
      iDestruct "Hevi" as (tA' ??? ->) "(#Hser' & #Hser3 & #Hcount & #Hdeser)".
      simplify_eq.
      iFrame. iModIntro. interp_unfold!.
      rewrite interp_var2_ext3.
      iApply (refines_un_auth_unauth with "Htab Hser' Hser3 Hcount Hdeser Hauth_un"). }
  Qed.
  
  Lemma refines_Authenticatable Θ (Δ : ctxO Σ Θ) :
    ⊢ REL v_Authenticable << i_Authenticable : ⟦ Authenticatable ⟧ (auth_ctx Δ).
  Proof.
    iIntros (??) "[Hi Htok]".
    rewrite /i_Authenticable /v_Authenticable /v_Authenticable_run.
    wp_apply gwp_map_empty; [done|].
    iIntros (d) "Hd". wp_alloc l as "Hl". wp_pures.
    
    iMod pos_alloc as (γm) "[Hpos Hpos']".
    
    iMod (na_inv_alloc seqG_name ⊤ tableN (is_susp_table l) with "[$Hd $Hl Hpos']") as "#Htab".
    { iNext. iSplitR; last first.
      { iLeft. admit. } 
      by iApply big_sepM_empty. }
    
    iAssert (|={⊤}=> spec_ideal tᵢ (fill Kᵢ (i_Auth_auth, i_Auth_mu, i_Auth_pair, i_Auth_sum, i_Auth_string, i_Auth_int, i_auth, i_unauth)))%I with "[Hi]" as ">Hi"; [admit|].
    
    wp_rec. wp_pures.
    wp_bind (v_unauth _).
    i_bind (i_unauth).    
    iPoseProof (refines_auth_unauth with "Htab [$Hi $Htok]") as "Hwp".
    wp_apply (wp_wand with "Hwp").
    iIntros (?) "(% & Hi & #[Hauth Hauth_un] & Htok)".
    iSimpl in "Hi".
    i_pures. wp_pures.
    iModIntro. iFrame.
    rewrite /Authenticatable.
    iSplit; interp_unfold!.
    { iExists lrel_evidence.
      iSplit; interp_unfold!.
      { iExists  _, _, _, _.
        do 2 (iSplit; [done|]).
        iSplit; [|done].
        interp_unfold.
        iExists _, _, _, _.
        do 2 (iSplit; [done|]).
        iSplit; last first.
        { iPoseProof refines_auth_auth as "[$ _]". }
        interp_unfold.
        iExists _, _, _, _.
        do 2 (iSplit; [done|]).
        iSplit; last first.
        { interp_unfold!. iPoseProof (refines_Auth_int authBaseN) as "[Hint _]".
          rewrite /lrel_car /=. rewrite interp_unseal //. }
        interp_unfold!.
        iExists _, _, _, _.
        do 2 (iSplit; [done|]).
        iSplit; last first.
        { interp_unfold!. iPoseProof (refines_Auth_string authBaseN) as "[Hstr _]".
          rewrite /lrel_car /=. rewrite interp_unseal //. }
        interp_unfold!.
        iExists _, _, _, _.
        do 2 (iSplit; [done|]).
        iSplit; last first.
        { iPoseProof refines_Auth_sum as "[$ _]". }
        interp_unfold!.
        iExists _, _, _, _.
        do 2 (iSplit; [done|]).
        iSplit; last first.
        { iPoseProof refines_Auth_pair as "[$ _]". }
        interp_unfold.
        iExists _, _, _, _.
        do 2 (iSplit; [done|]).
        iSplit; last first.
        { iPoseProof refines_Auth_mu as "[$ _]". }
        iPoseProof refines_Auth_auth as "[$ _]". }
      { rewrite interp_un_prod_unfold.
        iExists _, _.
        iSplit; try done.
        rewrite interp_un_prod_unfold.
        iSplit; try done.
        iExists _, _.
        iSplit; try done.
        iSplit; last first.
        { iPoseProof refines_auth_auth as "[_ $]". }
        rewrite interp_un_prod_unfold.
        iExists _, _.
        iSplit; try done.
        iSplit; last first.
        { interp_unfold!. iPoseProof (refines_Auth_int authBaseN) as "[_ Hint]".
          rewrite /lrel_car /=. rewrite interp_unseal //. }
        rewrite interp_un_prod_unfold.
        iExists _, _.
        iSplit; try done.
        iSplit; last first.
        { interp_unfold!. iPoseProof (refines_Auth_string authBaseN) as "[_ Hstr]".
          rewrite /lrel_car /=. rewrite interp_unseal //. }
        rewrite interp_un_prod_unfold.
        iExists _, _.
        iSplit; try done.
        iSplit; last first.
        { iPoseProof refines_Auth_sum as "[_ $]". }
        rewrite interp_un_prod_unfold.
        iExists _, _.
        iSplit; try done.
        iSplit; last first.
        { iPoseProof refines_Auth_pair as "[_ $]". }
        rewrite interp_un_prod_unfold.
        iExists _, _.
        iSplit; try done.
        iSplit; last first.
        { iPoseProof refines_Auth_mu as "[_ $]". }
        iPoseProof refines_Auth_auth as "[_ $]". } }
    { rewrite interp_un_exists_unfold.
      iExists lrel_evidence.
      rewrite interp_un_prod_unfold.
      iExists _, _.
      iSplit; try done.
      rewrite interp_un_prod_unfold.
      iSplit; try done.
      iExists _, _.
      iSplit; try done.
      iSplit; last first.
      { iPoseProof refines_auth_auth as "[_ $]". }
      rewrite interp_un_prod_unfold.
      iExists _, _.
      iSplit; try done.
      iSplit; last first.
      { interp_unfold!. iPoseProof (refines_Auth_int authBaseN) as "[_ Hint]".
        rewrite /lrel_car /=. rewrite interp_unseal //. }
      rewrite interp_un_prod_unfold.
      iExists _, _.
      iSplit; try done.
      iSplit; last first.
      { interp_unfold!. iPoseProof (refines_Auth_string authBaseN) as "[_ Hstr]".
        rewrite /lrel_car /=. rewrite interp_unseal //. }
      rewrite interp_un_prod_unfold.
      iExists _, _.
      iSplit; try done.
      iSplit; last first.
      { iPoseProof refines_Auth_sum as "[_ $]". }
      rewrite interp_un_prod_unfold.
      iExists _, _.
      iSplit; try done.
      iSplit; last first.
      { iPoseProof refines_Auth_pair as "[_ $]". }
      rewrite interp_un_prod_unfold.
      iExists _, _.
      iSplit; try done.
      iSplit; last first.
      { iPoseProof refines_Auth_mu as "[_ $]". }
      iPoseProof refines_Auth_auth as "[_ $]". }
  Admitted.

  Lemma refines_authentikit_func Θ (Δ : ctxO Σ Θ) :
    ⊢ REL v_Authentikit << i_Authentikit : ⟦ Authentikit_func var1 var0 ⟧ (auth_ctx Δ).
  Proof.
    iIntros (??) "[Hi Htok]".
    rewrite /i_Authentikit /v_Authentikit.
    iAssert (|={⊤}=> spec_ideal tᵢ (fill Kᵢ (i_return, i_bind, i_Authenticable)))%I with "[Hi]" as ">Hi"; [admit|].
    
    i_bind (i_Authenticable).
    iPoseProof (refines_Authenticatable with "[$Hi $Htok]") as "H".
    wp_apply (wp_wand with "H").
    iIntros (?) "(% & Hv & #[Hauth Hauth_un] & Htok)".
    iSimpl in "Hv".
    i_pures. wp_pures.
    iModIntro. iFrame.
    rewrite interp_unseal -/interp.interp_def.
    iSplit.
    { iExists _, _, _, _; rewrite -!/interp.interp_def.
      do 2 (iSplit; [done|]).
      iSplit; [|done].
      iExists _, _, _, _; rewrite -!/interp.interp_def.
      do 2 (iSplit; [done|]).
      iSplit.
      { iPoseProof refines_auth_return as "[H _]". rewrite interp_unseal //. }
      iPoseProof refines_auth_bind as "[? _]".
      rewrite interp_unseal //. }
    { iExists _, _; rewrite -!/interp.interp_def.
      iSplit; [done|].
      iSplit; [|done].
      iExists _, _; rewrite -!/interp.interp_def.
      iSplit; [done|].
      iSplit.
      { iPoseProof refines_auth_return as "[_ H]". rewrite interp_unseal //. }
      iPoseProof refines_auth_bind as "[_ ?]".
      rewrite interp_unseal //. }
  Admitted.

  Lemma refines_authentikit Θ (Δ : ctxO Σ Θ) :
    ⊢ REL v_Authentikit << i_Authentikit : ⟦ Authentikit ⟧ Δ .
  Proof.
    iIntros (??) "Hi".
    iPoseProof (refines_authentikit_func with "Hi") as "H".
    wp_apply (wp_wand  with "H").
    iIntros (?) "(% & $ & #Hauth & $)".
    iPoseProof "Hauth" as "[Hauth' Hauth_un]".
    iSplit.
    - rewrite interp_exists_unfold. iExists lrel_auth.
      iSplit.
      + rewrite interp_exists_unfold. by iExists lrel_auth_comp.
      + rewrite interp_un_exists_unfold. by iExists lrel_auth_comp.
    - do 2 setoid_rewrite interp_un_exists_unfold. 
      by iExists lrel_auth, lrel_auth_comp.
  Qed.

  Lemma refines_run w (c1 c2 : expr) A :
    is_proof w -∗
    (REL c1 << c2 : lrel_auth_comp A) -∗
    refines_Some ⊤ (v_run #~ c1 w) (i_run #~ c2) A.
  Proof.
    iIntros "#Hprf Hc".
    iIntros (??) "[Hi Htok]".
    rewrite /v_run /i_run.
    wp_bind c1; i_bind c2.
    iSpecialize ("Hc" with "[$Hi $Htok]").
    wp_apply (wp_wand with "Hc").
    iIntros (f1) "(%f2 & Hi & [Hc Hc_un] & Htok) /=".
    rewrite /v_Authenticable_run.
    rewrite /i_Authenticable /v_Authenticable /v_Authenticable_run.
    wp_apply gwp_map_empty; [done|].
    iIntros (d) "Hd". wp_alloc l as "Hl". wp_pures.
    
    iMod pos_alloc as (γm) "[Hpos Hpos']".
    
    iMod (na_inv_alloc seqG_name ⊤ tableN (is_susp_table l) with "[$Hd $Hl Hpos']") as "#Htab".
    { iNext. iSplitR; last admit.
      by iApply big_sepM_empty. }

    wp_rec. wp_pures.
    wp_rec. wp_pures.    
    wp_pures; i_pures.

    wp_apply ("Hc" with "[$Hi $Htok $Hprf Hpos]").
    { instantiate (1 := 0). iSplit. { iPureIntro. f_equal. }
      admit. }

    iIntros (?) "(Htok & Ho)".
    destruct o1; last first.
    { wp_pures. iExists None. by iFrame. }
    
    iMod (na_inv_acc with "Htab Htok") as "(Htabo & Htok & Hclose_tab)"; [solve_ndisj|solve_ndisj|].
    iDestruct "Htabo" as (??) "(Hl & >%Hm & Hbigsep & >Hge)".
    wp_pures. wp_load.
    wp_bind (map.map_is_empty _).
    iApply (gwp_map_is_empty with "[]"); [done|].
    iModIntro. iIntros (?) "%".
    simpl in H. subst.
    iDestruct "Ho" as (????[??]) "[(% & Hi & Hpost & Hpos)|(Hpost & Hpos)]"; simplify_eq;
      iDestruct "Hge" as "[Hpos'|[Hpos'|[Hpos' %Hge]]]";
      iPoseProof (pos_agree with "Hpos Hpos'") as (?) "[Hpos Hpos']"; 
      simplify_eq.
    - destruct (map.map_length m); wp_pures;
      iMod ("Hclose_tab" with "[$Hl $Htok $Hbigsep Hpos']") as "Htok";
        try (iNext; iFrame "%"; by iLeft);
      iModIntro; [iExists (Some _)|iExists None]; iSplit; eauto.
      iDestruct "Hpost" as (???) "(% & Hprf' & #HA)". simplify_eq.
      iFrame "∗ #".
    - destruct (map.map_length m) as [|n'] eqn:Hn; try lia. wp_pures.
      iMod ("Hclose_tab" with "[$Hl $Htok $Hbigsep Hpos']") as "Htok".
      { iNext. iFrame "%". iRight. iRight. iFrame. iPureIntro. lia. }
      iModIntro. iExists None. by iFrame.
  Admitted.

  Lemma refines_instantiate (c1 c2 : expr) (τ : type _ ⋆) :
    (REL c1 << c2 : ⟦ ∀: ⋆ ⇒ ⋆; ⋆ ⇒ ⋆, Authentikit_func var1 var0 → var0 τ ⟧ ∅) -∗
    REL c1 #~ #~ v_Authentikit
     << c2 #~ #~ i_Authentikit : lrel_auth_comp (⟦ τ ⟧ (auth_ctx ∅)).
  Proof.
    iIntros "Hc" (??) "[Hi Htok]".
    wp_bind v_Authentikit. i_bind i_Authentikit.
    iPoseProof (refines_authentikit_func with "[$Hi $Htok]") as "H".
    wp_apply (wp_wand with "H").
    iIntros (?) "(% & Hi & #Hauth & Htok)".
    wp_bind c1; i_bind c2.
    iSpecialize ("Hc" with "[$Hi $Htok]").
    wp_apply (wp_wand with "Hc").
    iIntros (v1) "(%v2 & Hi & Hcnt & Htok)".
    iSpecialize ("Hcnt" $! lrel_auth with "[//]").
    i_bind (v2 _).
    iSpecialize ("Hcnt" with "[$Hi $Htok]").
    wp_apply (wp_wand with "Hcnt").
    iIntros (v1'') "(%v2'' & Hi & Hcnt & Htok)".
    iSpecialize ("Hcnt" $! lrel_auth_comp with "[//]").
    i_bind (v2'' _).
    iSpecialize ("Hcnt" with "[$Hi $Htok]").
    wp_apply (wp_wand with "Hcnt").
    iIntros (v1''') "(%v2''' & Hi & [Hcnt _] & Htok)".
    i_bind (v2''' _).
    interp_unfold! in "Hcnt".
    iSpecialize ("Hcnt" with "[] [$Hi $Htok]"); rewrite -!/interp; [done|].
    wp_apply (wp_wand with "Hcnt").
    iIntros (v1'''') "(%v2''''& Hi & Hcnt & Htok)".
    iEval (rewrite interp_app_unfold) in "Hcnt".
    interp_unfold in "Hcnt".
    iFrame.
  Qed.

End proof.
  
Theorem authentikit_security Σ `{authPreG Σ, na_invG Σ, inG Σ poisonOSR} (A : ∀ `{authG Σ, seqG Σ, poisonOSG Σ}, (kindO Σ ⋆) )
  (φ : val → val → Prop) (cᵥ cᵢ : expr) (σ : state) (l : list string) (prf : val) :
  (∀ `{authG Σ, seqG Σ, poisonOSG Σ}, ∀ vᵥ vᵢ, A vᵥ vᵢ -∗ ⌜φ vᵥ vᵢ⌝) →
  (∀ `{authG Σ, seqG Σ, poisonOSG Σ}, ⊢ REL cᵥ << cᵢ : lrel_auth_comp A) →
  is_list l prf →
  adequate hash_collision NotStuck (v_run #~ cᵥ prf) σ
    (λ vᵥ σᵥ, ∃ thpᵢ σᵢ vᵢ o,
        vᵥ = $o ∧
          if o is Some wᵥ then
            (** a valid ideal execution *)
            rtc erased_step ([i_run #~ cᵢ], σ) (of_val vᵢ :: thpᵢ, σᵢ) ∧
              (** [φ] holds *)
              φ wᵥ vᵢ
          else True).
Proof.
  intros HA Hcomp Hprf.
  eapply (heap_adequacy_strong Σ).
  iIntros (Hinv) "_".
  iMod (cfg_alloc (i_run #~ cᵢ) σ) as (Hcfgᵢ) "[Hauthᵢ Heᵢ]".
  set (Hcfg := AuthG _ _ Hcfgᵢ).
  iMod (inv_alloc specN _ (spec_inv ([(i_run #~ cᵢ)], σ)) with "[Hauthᵢ]") as "#Hcfg".
  { iNext. iExists _, _. iFrame "# ∗ %". eauto. }
  iAssert (spec_ctx) as "#Hctx"; [by iExists _|].
  iMod na_alloc as (np) "Htok".
  set (Hseq := Build_seqG _ _ np).
  iMod pos_alloc as (γ) "Hpos".
  set (Hpos := PoisonOSG _ _ poisonOSG_name).

  wp_apply wp_fupd.
  wp_apply (wp_wand with "[-]").
  { iPoseProof (refines_run (seqG0 := Hseq) (poisonOSG0 := Hpos) prf with "[] []") as "Hrun".
    - by iExists _.
    - iApply Hcomp.
    - iApply ("Hrun" $! empty_ectx with "[$Hctx $Heᵢ $Htok]"). }
  iIntros (v) "(%o & -> & Htok & Ho)".
  destruct o; last first.
  { iIntros "!#" (????) "_". by iExists inhabitant, inhabitant, inhabitant, None. }
  iDestruct "Ho" as "(%vᵢ & [_ Hi] & Hinterp) /=".

  iDestruct (HA with "Hinterp") as %Hφ.
  iInv specN as (tpᵢ σᵢ) ">(Hauthᵢ & %)" "Hclose".
  iDestruct (cfg_auth_tpool_agree with "Hauthᵢ Hi") as %?.
  destruct tpᵢ as [|? tpᵢ]; simplify_eq/=.
  iMod ("Hclose" with "[-]") as "_".
  { iExists (_ :: tpᵢ), σᵢ. iFrame "∗ % #". }
  iModIntro.
  iIntros (σᵥ ???) "(?&?&?&?& Hhashes)".
  iIntros "!%". do 3 eexists; eexists (Some _). eauto.
Qed.

Theorem authentikit_security_syntactic (c : expr) (σ : state) (τ : type _ ⋆) prf (l : list string) :
  EqType τ →
  ε |ₜ ∅ ⊢ₜ c : (∀: ⋆ ⇒ ⋆; ⋆ ⇒ ⋆, Authentikit_func var1 var0 → var0 τ) →
                is_list l prf →
                adequate hash_collision NotStuck (v_run #~ (c #~ #~ v_Authentikit) prf) σ
                  (λ vᵥ σᵥ, ∃ thpᵢ σᵢ vᵢ o,
                      vᵥ = $o ∧
                        if o is Some wᵥ then
                          (** a valid ideal execution *)
                          rtc erased_step ([i_run #~ (c #~ #~ i_Authentikit)], σ) (of_val vᵢ :: thpᵢ, σᵢ) ∧
                            (** and they return the same value *)
                            wᵥ = vᵢ
                        else True).
Proof.
  intros Hτ Htyped Hprf.
  set Σ := (#[authΣ; na_invΣ; GFunctor poisonOSR]).
  eapply (authentikit_security Σ (λ _ _ _, ⟦ τ ⟧ (auth_ctx ∅))); [| |done].
  { iIntros (?????) "Hτ". by iDestruct (eq_type_sound with "Hτ") as %->. }
  iIntros (?????).
  iApply (refines_instantiate with "[]").
  by iApply refines_typed.
Admitted.


             
