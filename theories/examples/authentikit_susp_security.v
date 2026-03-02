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
  Context `{!stateG Σ, !authG Σ, !seqG Σ}.

  Definition authBaseN : namespace := nroot .@ "susp_ver".
  Definition authN (v : val) : namespace := authBaseN .@ v.
  Definition gmapN : namespace := authBaseN .@ "gmap".
  Definition tableN : namespace := authBaseN .@ "table".
  Definition tableLocSet : namespace := authBaseN .@ "tableloc".
  Definition tableLocN (susp : val) : namespace := tableLocSet .@ susp.

  Definition lrel_auth := lrel_auth authBaseN.

  (* Definition proph_type : Type := nat * option unit.

  Definition proph_cond (v : proph_type) (pid : nat) : iProp Σ :=
    (∀ (m : parentUR), ∃ (x av : val) (t : evi_type),
        ⌜v = (pid, Some tt)⌝ ∗ val_eq t x av ∗
          ⌜m !! pid = Some (to_agree (t, x))⌝) ∨
      (⌜v = (pid, None)⌝).

  Fixpoint take_until {A B : Type} (f : A → option B) (xs : list A) : list B :=
    match xs with
    | []      => []
    | x :: xs =>
      match f x with
      | Some y => y :: (take_until f xs)
      | None   => []
      end
    end.

  Definition longest_valid_prefix (us : list val) : list proph_type :=
    take_until (λ u,
        match u with
          (#(LitInt v), SOMEV #())%V => if Z.geb v 0 then Some (Z.to_nat v, Some ()) else None
        | (#(LitInt v), NONEV)%V => if Z.geb v 0 then Some (Z.to_nat v, None) else None
        | _ => None
        end
      ) us.

  Definition proph_list (p : proph_id) (vs : list (nat * option unit)) : iProp Σ :=
    ∃ (us : list (val * val)),
      proph p us ∗ ⌜vs = longest_valid_prefix (map snd us)⌝
        ∗ [∗ list] k↦v ∈ vs, (∃ (pid : nat), proph_cond v pid).

  Definition option_unit_val (v : option unit) : val :=
    match v with Some _ => SOMEV #() | None => NONEV end.
  
  Lemma wp_resolve_proph_val_some p vs (pid : nat) :
    ∀ x av t (m : parentUR),
      {{{ proph_list p vs ∗ val_eq t x av ∗ ⌜m !! pid = Some (to_agree (t, x))⌝ }}}
        resolve_proph: #p to: (#pid, SOMEV #())%V
      {{{ vs', RET #(); ⌜vs = (pid, Some tt) :: vs'⌝ ∗ proph_list p vs' }}}.
  Proof.
    iIntros (???? Φ) "((%us & Hp & % & Hcon) & Heq & %Hmap) HΦ".
    wp_apply (wp_resolve_proph with "Hp").
    iIntros (us') "[% Hp]". simplify_eq.
    iApply "HΦ". iFrame "Hp". iSplit; [|iSplit; [done|]].
    - iPureIntro. simpl.
      rewrite /longest_valid_prefix. simpl.
      assert ((pid >=? 0)%Z = true).
      { rewrite Z.geb_le. lia. }
      rewrite H. do 2 f_equal. lia.
    - iSimpl in "Hcon".
      rewrite /longest_valid_prefix.
      assert ((pid >=? 0)%Z = true).
      { rewrite Z.geb_le. lia. }
      simpl. rewrite H. simpl.
      iDestruct "Hcon" as "[H1 Hcon]". iFrame.
  Qed.
  
  Lemma wp_resolve_proph_val_none p vs (pid : nat) :
    {{{ proph_list p vs }}}
      resolve_proph: #p to: (#pid, NONEV)%V;;
      resolve_proph: #p to: NONEV
    {{{ RET #(); ⌜vs = [(pid, None)]⌝ }}}.
  Proof.
    iIntros (Φ) "(%us & Hp & %) HΦ".
    wp_apply (wp_resolve_proph with "Hp").
    iIntros (?) "[% Hp]". wp_pures.
    wp_apply (wp_resolve_proph with "Hp").
    iIntros (?) "[% Hp]". iApply "HΦ".
    simplify_eq. iPureIntro.
    rewrite /longest_valid_prefix /option_unit_val.
    simpl; f_equal.
    assert ((pid >=? 0)%Z = true).
    { rewrite Z.geb_le. lia. }
    rewrite H. do 2 f_equal. lia.
  Qed.

  Lemma wp_resolve_proph_final p vs (v : option unit) :
    {{{ proph_list p vs }}}
      resolve_proph: #p to: (#0, option_unit_val v)%V;;
      resolve_proph: #p to: NONEV
    {{{ RET #(); ⌜vs = [(0, v)]⌝ }}}.
  Proof.
    iIntros (Φ) "(%us & Hp & %) HΦ".
    wp_apply (wp_resolve_proph with "Hp").
    iIntros (?) "[% Hp]". wp_pures.
    wp_apply (wp_resolve_proph with "Hp").
    iIntros (?) "[% Hp]". iApply "HΦ".
    simplify_eq. iPureIntro.
    rewrite /longest_valid_prefix /option_unit_val.
    destruct v; simpl; [destruct u|]; f_equal.
  Qed. *)

  Definition finish_spec1 (finish : val) (x a aᵥ aᵢ ser : val) (A : lrel Σ) : iProp Σ :=
    ∀ (s : string) (E: coPset) (t1 t2 : evi_type),
      ⌜↑authSerProofSet authBaseN ⊆ E⌝ -∗
      {{{ seq_tok E ∗ count_is_correct t1 x 0 ∗ A aᵥ aᵢ ∗
            ser_spec_3 ser t1 ∗ val_eq_rel authBaseN A t1 ∗ hashed s ∗
            s_is_ser'' t2 aᵥ s ∗ ⌜a = InjLV #(hash s)⌝ }}}
        finish #()
        {{{ (o : option val), RET $o;
            seq_tok E ∗ if o is None then True else A x aᵢ }}}.

  Definition finish_spec2 (finish : val) (x a aᵥ aᵢ ser : val) (A : lrel Σ) : iProp Σ :=
    ∀ (s1 s2 : string) (E: coPset) (susp : loc) (t1 t2 : evi_type),
      {{{ seq_tok E ∗ count_is_correct t1 x 0 ∗ A aᵥ aᵢ ∗
            ser_spec_3 ser t1 ∗ val_eq_rel authBaseN A t1 ∗ hashed s2 ∗
            s_is_ser'' t2 aᵥ s1 ∗ ⌜a = InjRV #susp⌝ ∗ susp ↦□ InjRV #(hash s2) }}}
        finish #()
        {{{ (o : option val), RET $o;
            seq_tok E ∗ if o is None then True else ⌜s1 = s2⌝ -∗ val_eq t1 x aᵥ }}}.

  (* Definition finish_spec (finish : val) (t : evi_type) (x : val) : iProp Σ :=
    ∀ (E : coPset) (ser av ai : val),
      ⌜↑authSerProofSet authBaseN ⊆ E⌝ -∗ ⌜↑tableN ⊆ E⌝ -∗ ⌜↑tableLocSet ⊆ E⌝ -∗
      {{{ A av ai ∗ ser_spec_3 ser t ∗ seq_tok E ∗ count_is_correct t x 0 }}}
        finish #() @ E
        {{{ (o : option val), RET $o;
            seq_tok E ∗ if o is None then ⌜True⌝ else
                (A x ai ∗ val_eq t x av) }}}. *)

  Definition susp_big_sep (m : gmap val val) : iProp Σ :=
    [∗ map] k ↦ v ∈ m,
      ∃ (id ctr : nat) (finish ctrv x a aᵥ aᵢ ser : val) (t : evi_type) (A : lrel Σ) (b : bool),
        (⌜k = #id ∧ ctrv = #ctr ∧ ctr > 0 ∧ v = (ctrv, finish)%V⌝ ∗ A aᵥ aᵢ ∗
           count_is_correct t x ctr ∗ single_instance id t x aᵥ None b ∗
           (∃ (h: string), (⌜a = InjLV #h⌝ ∗ finish_spec1 finish x a aᵥ aᵢ ser A) ∨
                             (∃ (susp : loc), ⌜a = InjRV #susp⌝ ∗ susp↦□ InjRV #h ∗
                                                finish_spec2 finish x a aᵥ aᵢ ser A))).
      
  Definition is_susp_table (l : loc) : iProp Σ :=
    ∃ (d : val) (m : gmap val val),  l ↦ d ∗ ⌜is_map d m⌝ ∗ susp_big_sep m.

  Definition in_susp_table (l : loc) (id : nat) : iProp Σ :=
    ∃ (d v : val) (m : gmap val val),
      is_susp_table l -∗ l ↦ d ∗ ⌜is_map d m⌝
      -∗ is_susp_table l ∗ ⌜m !! #id = Some v⌝.

  Definition not_in_susp_table (l : loc) (id : nat) : iProp Σ :=
    ∃ (d : val) (m : gmap val val),
      is_susp_table l -∗ l ↦ d ∗ ⌜is_map d m⌝
      -∗ is_susp_table l ∗ ⌜m !! #id = None⌝.

  Definition inv_susp_table (l: loc) := seq_inv tableN (is_susp_table l).

  Definition count_inv (cnt : nat) (m : mapUR) (lm : locPidMapUR) :=
    ∀ (id : nat),
      id ≥ cnt →
      (m !! id = None ∧
         (∀ (l : loc), lm !! l = None ∨
                         (∀ id', lm !! l = Some id' → id ≠ id'))).
  
  Definition global_state (cnt : nat) (m : mapUR) (lm : locPidMapUR) : iProp Σ :=
    own stateG_name (● (MaxNat (cnt-1), m, lm)) ∗
      ⌜count_inv cnt m lm⌝ ∗
      (∀ (id : nat) (x vᵥ : val) (l : loc) (t : evi_type),
          ⌜m !! id = Some (to_agree (t, x, vᵥ, (None : option loc), true))⌝ ∗
            (in_susp_table l id ∨ (not_in_susp_table l id ∗ val_eq t x vᵥ))).
  
  Definition empty_state n : prodUR (prodUR max_natUR mapUR) locPidMapUR := (MaxNat n, ∅, ∅).
  
  Lemma global_state_update_empty E (cnt : nat) (m : mapUR) (lm : locPidMapUR) :
    global_state cnt m lm ={E}=∗ global_state (cnt + 1) m lm.
  Proof.
    iIntros "(Hproph & %Hcntinv & Hseminv)".
    iMod ((own_update
             stateG_name
             (● (MaxNat (cnt-1), m, lm))
             (● (MaxNat cnt, m, lm) ⋅ ◯ (empty_state cnt) ))
           with "Hproph") as "Hproph".
    { apply (auth_update _ (empty_state 0) _ _).
      do 2 apply prod_local_update_1.
      apply max_nat_local_update.
      simpl. lia. }
    iPoseProof (own_op with "Hproph") as "[Hproph _]".
    iModIntro. rewrite /global_state.
    rewrite Nat.add_sub. iFrame. iPureIntro.
    intros id H. apply Hcntinv. lia.
  Qed.

  Definition singleton_map (id : nat) (t : evi_type) (x vᵥ : val) (so : option loc) (b : bool) : mapUR :=
    {[ id := to_agree (t, x, vᵥ, so, b) ]}.

  Definition single_instance_frag (id : nat) (t : evi_type) (x vᵥ : val) (so : option loc) (b : bool) : stateUR :=
    ◯ (MaxNat id, singleton_map id t x vᵥ so b, if so is Some s then {[ s := id ]} else ∅).

  Definition updated_map (m : mapUR) (id : nat) (t : evi_type) (x vᵥ : val) (so : option loc) (b : bool) : mapUR :=
    <[ id := to_agree (t, x, vᵥ, so, b) ]> m.

  Definition updated_loc_map (m : locPidMapUR) (so : option loc) (id : nat) : locPidMapUR :=
    if so is Some s then <[ s := id ]> m else m.

  Lemma global_state_update_singleton E (cnt : nat) (m : mapUR) (lm : locPidMapUR) (t : evi_type) (x vᵥ : val) (so : option loc) (b : bool) :
    global_state cnt m lm
    ={E}=∗ global_state (cnt + 1) (updated_map m cnt t x vᵥ so b) (updated_loc_map lm so cnt) ∗ single_instance cnt t x vᵥ so b.
  Proof.
    iIntros "(Hproph & %Hcntinv & Hseminv)".
    iMod ((own_update
             stateG_name
             (● (MaxNat (cnt-1), m, lm))
             (● (MaxNat cnt, updated_map m cnt t x vᵥ so b, updated_loc_map lm so cnt) ⋅ single_instance_frag cnt t x vᵥ so b))
           with "Hproph") as "Hproph".
    { apply (auth_update _ (empty_state 0) _ _).
      apply prod_local_update; simpl.
      { apply prod_local_update; simpl.
        { apply max_nat_local_update. simpl. lia. }
        apply gmap.alloc_local_update; last done.
        apply Hcntinv. lia. }
      destruct so; last done.
      admit. }
    iPoseProof (own_op with "Hproph") as "[Hproph Hfrag]".
    iModIntro. rewrite /global_state.
    rewrite Nat.add_sub. iFrame. iSplitR "Hseminv".
    iPureIntro.
    { intros id H. rewrite /updated_map.
      rewrite lookup_insert_None.
      split; last admit.
      split; last lia.
      apply Hcntinv. lia. }
    iIntros (?????).
    iSpecialize ("Hseminv" $! id x0 vᵥ0 l t0) as #.
    iDestruct "Hseminv" as "[%Hseminv $]".
    iPureIntro. unfold updated_map.
  Admitted.
  
    
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

  Lemma v_finish_spec1 :
    ∀ (a aᵥ aᵢ x ser : val) (st : loc) (A : lrel Σ),
      {{{ inv_susp_table st }}}
        v_finish #st a x ser
        {{{ (finish : val), RET finish;
            finish_spec1 finish x a aᵥ aᵢ ser A }}}.
  Proof.
    iIntros (????????) "#Htab HΦ".
    rewrite /v_finish.
    wp_pures. iModIntro. iApply "HΦ".
    rewrite /finish_spec1.
    iIntros (?????).
    iIntros (?) "!# (Htok & Hcount & #HA & #Hserspec & #Hrel & #hashs & #Hser & %) HΦ".
    wp_pures. wp_apply ("Hserspec" with "[$Hcount $Htok]").
    iIntros ([]); last first.
    { iIntros "(Htok & #Hsers)". wp_pures.
      iModIntro. iApply ("HΦ" $! None). eauto. }
    iIntros "(Htok & #Hsers)". wp_pures.
    simplify_eq. wp_pures.
    wp_apply (wp_hash); try done.
    iIntros "#hashs0". wp_pures.
    case_bool_decide; simplify_eq; wp_pures;
      try ( iApply ("HΦ" $! None); eauto ).

    destruct (decide (collision s s0)) as [|Hnc%not_collision];
      try (iExFalso; by iApply (hashes_auth.hashed_inj_or_coll with "hashs hashs0") ).
    destruct Hnc as [<-|?]; simplify_eq.
    iPoseProof (evi_type_ser''_inj authBaseN with "[Hsers] Hser") as "Heq";
      try (iLeft; iFrame "#").
    iApply ("HΦ" $! (Some _)).
    iPoseProof (val_eq_sym authBaseN with "Heq") as "Heq1".
    iMod ("Hrel" with "[] [Htok]") as "(Htok & Heq2)";
      iFrame "∗ #"; try done.
  Qed.
    
  Lemma v_finish_spec2 :
    ∀ (a x aᵥ aᵢ ser : val) (st : loc) (A : lrel Σ),
      {{{ inv_susp_table st }}}
        v_finish #st a x ser 
      {{{ (finish : val), RET finish;
          finish_spec2 finish x a aᵥ aᵢ ser A }}}.
  Proof.
    iIntros (????????) "#Htab HΦ".
    rewrite /v_finish.
    wp_pures. iModIntro. iApply "HΦ".
    rewrite /finish_spec2.
    iIntros (?????).
    iIntros (??) "!# (Htok & Hcount & #HA & #Hserspec & #Hrel & #hashs2 & #Hser & % & #Hsusp) HΦ".
    wp_pures. wp_apply ("Hserspec" with "[$Hcount $Htok]").
    iIntros ([]); last first.
    { iIntros "(Htok & #Hsers)". wp_pures.
      iModIntro. iApply ("HΦ" $! None). eauto. }
    iIntros "(Htok & #Hsers)". wp_pures.
    simplify_eq. wp_pures. wp_load. wp_pures.
    wp_apply (wp_hash); try done.
    iIntros "#hashs". wp_pures.
    case_bool_decide; simplify_eq; wp_pures;
      try ( iApply ("HΦ" $! None); eauto ).

    destruct (decide (collision s s2)) as [|Hnc%not_collision];
      try (iExFalso; by iApply (hashes_auth.hashed_inj_or_coll with "hashs hashs2") ).
    destruct Hnc as [<-|?]; simplify_eq.
    iApply ("HΦ" $! (Some _)).
    iFrame.
    iModIntro. iIntros (->).
    iApply (evi_type_ser''_inj authBaseN); [by iLeft|done].
  Qed.

  (* Lemma v_finish_spec_2 :
    ∀ (st : loc) (a a1 a2 x ser : val) (t : evi_type) (pid: nat) (susp : loc) (E : coPset) (A : lrel Σ),      
      inv_susp_table st ⊢
        {{{ ⌜a = InjRV #susp⌝ ∗ susp ↦ InjLV #pid ∗
              ser_spec_3 ser t ∗ A a1 a2 }}}
        v_finish #st a x ser @ E
        {{{ (finish : val), RET finish;
            finish_spec2 finish t x }}}.
  Proof.
    iIntros (???????????) "#Htab".
    iIntros (?) "!# (% & Hsusp & #Hserspec & #HA) HΦ".
    rewrite /v_finish.
    simplify_eq. wp_pures. iModIntro.
    iApply "HΦ". iFrame.
    rewrite /finish_spec2.
    iIntros (??????) "!# (Htok & Hcount & Hval) HΦ".
    wp_pures.
    wp_apply ("Hserspec" with "[$Hcount $Htok]").
    iIntros ([]); last first.
    { iIntros "(Htok & _)". wp_pures.
      iModIntro. iApply ("HΦ" $! None). iFrame. }

    iIntros "(Htok & #Hsers)". wp_pures.
    wp_load. wp_pures.

    iMod (na_inv_acc with "Htab Htok") as "(Htabo & Htok_tab & Hclose_tab)"; [solve_ndisj|solve_ndisj|].
    wp_pures.
    iDestruct "Htabo" as (??) "(Hl & >%Hismap & #Hmap)".
    wp_load.
    wp_apply (gwp_map_lookup #pid d m); [done|done|].
    iIntros (? hoption).
    (* iMod ("Hclose" with "[Htok Hmap Hl]") as "Htok".
        { by iFrame. } *)
    destruct (m !! #pid) as [a|] eqn:Hlookup; last first.
    { simpl in hoption. simplify_eq. wp_pures. iApply ("HΦ" $! None).
      iMod ("Hclose_tab" with "[Htok_tab Hmap Hl]") as "Htok"; [by iFrame "# ∗"|by iFrame]. }

    iDestruct (big_sepM_lookup with "Hmap") as (?????? Hf) "(Hcountp & Hfinish)"; [done|].
    destruct! Hf. simplify_eq.
    
    simpl in hoption. simplify_eq. wp_pures.
    case_bool_decide; simplify_eq.
    - wp_pures. wp_load. wp_bind (map_remove _ _)%E.
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

      iDestruct "Hfinish" as "[(%&%&%& Hfinish)|(%&%&Hfinish&Hinv)]".    
      + wp_apply ("Hfinish" with "[//] [//] [$Htok $Hcountp]").
        iIntros ([]) "Htok"; last first.
        { iApply ("HΦ" $! None). iFrame. }
        iDestruct "Htok" as "(Htok & Heq)".
        iApply ("HΦ" $! (Some _)). iFrame "∗ #".

      + iMod (na_inv_acc with "Hinv Htok") as "(Hsuspo & Htok & Hclose_susp)"; [solve_ndisj|solve_ndisj|].
        iApply ("Hfinish" $! (E0 ∖ ↑tableLocN susp0) with "[] [] [] [] [Hsuspo Htok Hcountp] []").

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

          iModIntro. by iApply ("HΦ" $! (Some _)).

    iDestruct "Hval" as "[->|(% & -> & Hsusp)]"; [wp_pures|wp_load; wp_pures];
      wp_apply (wp_hash); try done;
      iIntros "#hashs0"; wp_pures;
      case_bool_decide; simplify_eq; wp_pures;
      try ( iApply ("HΦ" $! None); eauto );
      destruct (decide (collision s s0)) as [|Hnc%not_collision];
      try (iExFalso; by iApply (hashes_auth.hashed_inj_or_coll with "hashs hashs0") );
      destruct Hnc as [<-|?]; simplify_eq;
      
      iPoseProof (evi_type_ser''_inj authBaseN with "[Hsers] Hser") as "Heq";
      try (iLeft; iFrame "#");
      iApply ("HΦ" $! (Some _)); iFrame "#";
      iPoseProof (val_eq_sym authBaseN with "Heq") as "Heq1";
      iPoseProof ("Hrel" with "[Htok]") as "H"; iFrame "∗ #";
      iDestruct "H" as ">(H1 & H2)"; by iFrame. *)

                              
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

          iModIntro. by iApply ("HΦ" $! (Some _)).
  Qed. *)

  Definition is_proof (v : val) : iProp Σ :=
    ∃ (l : list string), ⌜is_list l v⌝.

  Definition is_proof_state (v : val) (counter : nat) : iProp Σ :=
    ∃ prf, ⌜v = (prf, #counter)%V⌝ ∗ is_proof prf.

  Definition lrel_auth_comp_post (A : lrel Σ) : lrel Σ :=
    LRel (λ v1 a2, ∃ a1 prf1 counter, ⌜v1 = (prf1, a1)%V⌝ ∗ is_proof_state prf1 counter ∗ A a1 a2)%I.

  Definition lrel_auth_comp_post_bad (A : lrel Σ) : lrel Σ :=
    LRel (λ v1 v2, ∃ t a1 prf1 x counter,
          ⌜v1 = (prf1, x)%V⌝ ∗ is_proof_state prf1 counter ∗ s_valid_val authBaseN t x ∗
            A a1 v2)%I.

  Definition lrel_auth_comp' (A : lrel Σ) : lrel Σ := LRel (λ v1 v2,
    ∀ t K (w w' : val) m lm (cntr : nat),
      {{{ spec_ideal t (fill K (v2 w')) ∗ seq_tok ⊤ ∗ is_proof_state w cntr ∗
            global_state cntr m lm }}}
        v1 w
      {{{ (o1 : option val), RET $o1;
          seq_tok ⊤ ∗
            if o1 is Some w1 then
              ∃ (w2 a prfst prf : val) (cntr' : nat) m' lm',
                spec_ideal t (fill K w2) ∗ ⌜w1 = (prfst, a)%V ∧ prfst = (prf, #cntr')%V⌝ ∗
                           global_state cntr' m' lm' ∗
                           (lrel_auth_comp_post A w1 w2 ∨ lrel_auth_comp_post_bad A w1 w2)
            else True }}})%I.

  (* Definition lrel_auth_comp_bad : lrel Σ := LRel (λ v1 v2,
    ∀ w,
      {{{ seq_tok ⊤ ∗ is_proof_state w }}}
        v1 w
      {{{ (o1 : option val), RET $o1;
          seq_tok ⊤ ∗
            if o1 is Some w1 then lrel_auth_comp_post_bad w1 v2
            else True }}})%I.

  Definition lrel_auth_comp' (A : lrel Σ) : lrel Σ := LRel (λ v1 v2,
    (lrel_auth_comp_good A v1 v2 ∨ lrel_auth_comp_bad v1 v2))%I. *)
        
  Program Definition lrel_auth_comp : kindO Σ (⋆ ⇒ ⋆)%kind := λne A, lrel_auth_comp' A.
  Next Obligation.
    intros ??? ???. rewrite /lrel_car /=.
    do 43 f_equiv; solve_proper.
  Qed.

  Definition lrel_hash_fail_option' (A : lrel Σ) : lrel Σ := LRel (λ v1 v2,
    (A v1 v2 ∨ (∃ t x, A x v2 ∗ s_valid_val authBaseN t v1)))%I.

  Program Definition lrel_hash_fail_option : kindO Σ (⋆ ⇒ ⋆)%kind := λne A, lrel_hash_fail_option' A.
  Next Obligation.
    intros ??????. rewrite /lrel_car /=.
    solve_proper.
  Qed.    
  
  Definition auth_ctx {Θ} (Δ : ctxO Σ Θ) := ext (ext (ext Δ lrel_hash_fail_option) lrel_auth) lrel_auth_comp.

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
    iIntros (??????? Ψ) "!# (Hi & Htok & % & Hst) HΨ".
    simpl in H. destruct H as (? & -> & Hp).
    i_pures; wp_pures.
    iModIntro. iApply ("HΨ" $! (Some _)).
    iFrame "Htok".
    iExists _, _, _, _. iFrame. iSplit; first done.
    iLeft. iExists _, _.
    interp_unfold in "HA".
    iFrame "HA".
    iExists _. iSplit; [done|]. rewrite /is_proof_state.
    eauto.
  Qed.

  Lemma refines_auth_bind Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆; ⋆, var2 var1 → (var4 var1 → var2 var0) → var2 var0 ⟧
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
    interp_unfold in "HmA".
    iIntros (u1 u2 ????? Ψ) "!# (Hi & Htok & Hprf & Hst) HΨ".
    i_pures; wp_pures.
    i_bind (v2 _)%I; wp_bind (v1 _)%I.
    wp_apply ("HmA" with "[$Hi $Htok $Hprf $Hst]").
    iIntros (o) "[Htok Ho]".
    destruct o; last first.
    { wp_pures. iApply ("HΨ" $! None). by iFrame. }
    iDestruct "Ho" as (???????) "(Hi & %H & Hst & [H|H])".
    + iDestruct "H" as (a1 a2 ? ->) "[#Hprf #HA]".
      wp_pures.
      wp_bind (w1 _)%E; i_bind (w2 _ )%E.
      interp_unfold in "HmB".
      iSpecialize ("HmB" with "[HA] [$Hi $Htok]").
      { interp_unfold!. by iLeft. }
      wp_apply (wp_wand with "HmB").
      iIntros (v) "(% & Hi & H & Htok) /=".
      destruct! H. simplify_eq.
      iPoseProof "Hprf" as (??) "Hprf'". simplify_eq.
      interp_unfold in "H".
      wp_apply ("H" with "[$Htok $Hi $Hprf $Hst]").
      iIntros (?) "(Htok & Ho) /=".
      iApply "HΨ". iFrame.
    + iDestruct "H" as (????? ->) "(#Hprf & Hval & #HA)".
      wp_pures.
      wp_bind (w1 _)%E; i_bind (w2 _)%E.
      interp_unfold in "HmB".
      iSpecialize ("HmB" with "[Hval] [$Hi $Htok]").
      { interp_unfold!. iRight. iFrame "# ∗". }
      wp_apply (wp_wand with "HmB").
      iIntros (v) "(% & Hi & H & Htok) /=".
      interp_unfold in "H".
      destruct! H. simplify_eq.
      iPoseProof "Hprf" as (??) "Hprf'". simplify_eq.
      wp_apply ("H" with "[$Htok $Hi $Hprf $Hst]").
      iIntros (?) "(Htok & Ho) /=".
      iApply "HΨ". iFrame.
  Qed.

  Lemma refines_auth_unauth Θ (Δ : ctxO Σ Θ) c :
    inv_susp_table c
    ⊢ REL v_unauth #c << i_unauth :
      ⟦ ∀: ⋆, var1 var0 → var3 var0 → var2 var0 ⟧ (ext (auth_ctx Δ) (lrel_evidence authBaseN)).
  Proof.
    iIntros "#Htab" (??) "(Hi & Htok)".
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
      interp_unfold!. iIntros (????????) "!# (Hi & Htok & Hproof & Hst) HΦ".
      wp_pures.
      iApply ("HΦ" $! None). by iFrame. }
        
    iDestruct "Hevi" as (tA' ??? ->) "(#Hser' & #Hser3 & #Hcount & #Hdeser & #Hrel & #Hcupd)".
    iFrame. iModIntro.
    interp_unfold!. iIntros (????????) "!# (Hi & Htok & Hproof & Hst) HΦ".
    wp_pures. i_pures. iDestruct "Hproof" as (? -> ) "Hproof".
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
    
    iPoseProof "Hauth" as "(%&%&%&#Hser1&HA&[(#hashs1&%)|(%&%&Hinv)])"; simplify_eq.
    - iIntros "Hserser".
      wp_pures. wp_apply ("Hcount" with "[Hserser]").
      { iModIntro. iApply (deser_valid authBaseN _ v a1 _); [by iRight| |done].
        iModIntro. instantiate (1 := t0). iIntros "$". }

      iIntros (?) "(Hc & Hval)".
      wp_pures.
      wp_apply (v_finish_spec1 _ a1 w2 _ _ _ A with "Htab").
      iIntros (finish) "Hfinish". wp_pures.

      case_bool_decide; wp_pures; simplify_eq.
      + wp_bind (finish #()).
        assert (c0 = 0); [lia|]. simplify_eq.
        iApply ("Hfinish" $! s1 ⊤ tA' with "[//] [$Htok $Hc $HA $Hser3 $Hrel $hashs1 $Hser1]"); [done|].
        iNext. iIntros ([]) "(Htok & #HAfin)"; wp_pures; last first.
        { iApply ("HΦ" $! (None)). eauto. }
        wp_apply gwp_list_tail; [done|].
        iIntros (vl Hl). wp_pures.

        iMod (global_state_update_empty with "Hst") as "Hst".
        
        iApply ("HΦ" $! (Some _)).
        iFrame. iModIntro.
        iExists _, _, _.
        iSplit.
        { iPureIntro. split; first done.
          do 3 f_equal. lia. }
        iLeft. iExists _, _, _.
        iSplit; [done|]. iFrame "#".
        iExists _. iSplit.
        { iPureIntro. f_equal.
          instantiate (1 := (S cntr)).
          rewrite Nat2Z.inj_succ. done. }
        iExists _. done.

      + iMod (na_inv_acc with "Htab Htok") as "(Htabo & Htok & Hclose_tab)"; [solve_ndisj|solve_ndisj|].
        iDestruct "Htabo" as (??) "(Hl & Htabo)". wp_load.
        iDestruct "Htabo" as (Hmap) "Hbigsep". wp_pures.

        iMod (global_state_update_singleton with "Hst") as "[Hst Hfrag]".
        
        wp_bind (map.map_insert _ _ _).
        iApply (gwp_map_insert #cntr); [done|done|].
        iModIntro. iIntros (d') "%Hmap'". wp_store.
        wp_pures. wp_apply (gwp_list_tail with "[//]").
        iIntros "/=" (tl Htl). wp_pures.
        iMod ("Hclose_tab" with "[$Hl Hbigsep $Htok Hfinish Hc Hfrag]") as "Htok".
        { iFrame "%". iNext.
          iApply (big_sepM_insert_2 with "[Hfinish Hc Hfrag]"); last done.
          instantiate (1 := true).
          iFrame "∗ #". iExists _.
          assert (c0 > 0).
          { apply Nat.neq_0_lt_0. intros ->. by apply H0. }
          do 3 iExists _. repeat (try (iSplit; [done|])).
          iExists _. iLeft. iFrame. eauto. }
        
        iMod (deser_valid_weak with "Hval") as "Hval".

        iModIntro. iApply ("HΦ" $! (Some _)).
        iFrame. iExists _, _, _. iSplit.
        { iPureIntro. f_equal. split; first done.
          do 3 f_equal. lia. }

        iRight. do 5 iExists _.
        iSplit; first done.
        iFrame "# ∗".
        iExists _. iSplit.
        { iPureIntro. do 3 f_equal.
          instantiate (1 := (S cntr)).
          rewrite Nat2Z.inj_succ. done. }
        eauto.

    - iIntros "Hserser".
      iMod (na_inv_acc with "Hinv Htok") as "(Hinv1 & Htok & Hclose)"; [done|done|].
      wp_pures. wp_apply ("Hcount" with "[Hserser]").
      { iModIntro. iApply (deser_valid authBaseN _ v a1 _); [by iRight| |done].
        iModIntro. instantiate (1 := t0). iIntros "$". }

      iIntros (?) "(Hc & Hval)".
      wp_pures.
      wp_apply (v_finish_spec2 _ _ a1 w2 _ _ A  with "Htab").
      iIntros (finish) "Hfinish". wp_pures.

      iDestruct "Hinv1" as "[(#hashs1&#Hsusp & Hval2)|(%&%&%&%&%&%&% & Hsusp & Hin & Heq)]"; last first.
      { admit. }
      
      case_bool_decide; wp_pures; simplify_eq.
      + wp_bind (finish #()).
        assert (c0 = 0); [lia|]. simplify_eq.
        
        iApply ("Hfinish" $! _ _ (⊤ ∖ ↑authSerProofN authBaseN #susp) with "[$Htok $Hc $HA $Hser3 $Hrel $hashs1 $Hser1]").
        { by iFrame "#". }
        iNext. iIntros ([]) "(Htok & #HAfin)"; wp_pures; last first.
        { iApply ("HΦ" $! (None)).
          iMod ("Hclose" with "[$hashs1 Hval2 $Htok]") as "H".
          { iNext. iLeft. iFrame "∗ #".  }
          eauto. }

        iMod ("Hclose" with "[$hashs1 Hval2 $Htok]") as "Htok".
        { iNext. iLeft. iFrame "∗ #".  }
        
        iMod ("Hrel" $! a1 v w2 ⊤ with "[//] [$Htok]") as "[#HA' Htok]".
        { iFrame "#". iApply (val_eq_sym authBaseN).
          by iApply "HAfin". }

        wp_apply gwp_list_tail; [done|].
        iIntros (vl Hl). wp_pures.

        iMod (global_state_update_empty with "Hst") as "Hst".
        
        iApply ("HΦ" $! (Some _)).
        iFrame. iModIntro.
        iExists _, _, _.
        iSplit.
        { iPureIntro. split; first done.
          do 3 f_equal. lia. }

        iLeft. iExists _, _, _.
        iSplit; [done|]. iFrame "#".
        iExists _. iSplit.
        { iPureIntro. f_equal.
          instantiate (1 := (S cntr)).
          rewrite Nat2Z.inj_succ. done. }
        iExists _. done.

      + iMod (na_inv_acc with "Htab Htok") as "(Htabo & Htok & Hclose_tab)"; [solve_ndisj|solve_ndisj|].
        iDestruct "Htabo" as (??) "(Hl & Htabo)". wp_load.
        iDestruct "Htabo" as (Hmap) "Hbigsep". wp_pures.

        iMod (global_state_update_singleton with "Hst") as "[Hst Hfrag]".
        
        wp_bind (map.map_insert _ _ _).
        iApply (gwp_map_insert #cntr); [done|done|].
        iModIntro. iIntros (d') "%Hmap'". wp_store.
        wp_pures. wp_apply (gwp_list_tail with "[//]").
        iIntros "/=" (tl Htl). wp_pures.
        iMod ("Hclose_tab" with "[$Hl Hbigsep $Htok Hfinish Hc Hfrag]") as "Htok".
        { iFrame "%". iNext.
          iApply (big_sepM_insert_2 with "[Hfinish Hc Hfrag]"); last done.
          instantiate (1 := true).
          iFrame "∗ #". iExists _.
          assert (c0 > 0).
          { apply Nat.neq_0_lt_0. intros ->. by apply H0. }
          do 3 iExists _. repeat (try (iSplit; [done|])).
          iRight. iFrame. eauto. }
        
        iMod (deser_valid_weak authBaseN with "Hval") as "Hval".

        iMod ("Hclose" with "[$hashs1 Hval2 $Htok]") as "Htok".
        { iNext. iLeft. iFrame "∗ #".  }

        iModIntro. iApply ("HΦ" $! (Some _)).
        iFrame. iExists _, _, _. iSplit.
        { iPureIntro. f_equal. split; first done.
          do 3 f_equal. lia. }

        iRight. do 5 iExists _.
        iSplit; first done.
        iFrame "# ∗".
        iExists _. iSplit.
        { iPureIntro. do 3 f_equal.
          instantiate (1 := (S cntr)).
          rewrite Nat2Z.inj_succ. done. }
        eauto.
  Admitted.
        
  (* admit. (* What happens when we put finish in a map *)

      + admit. (* What happens when we fill in a suspended value *)
        
          
      wp_bind (v_finish _ _ _ _).
      iAply (v_finish_spec.
      
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
  Qed. *)

  Lemma refines_Authenticatable Θ (Δ : ctxO Σ Θ) :
    ⊢ REL v_Authenticable << i_Authenticable : ⟦ Authenticatable ⟧ (auth_ctx Δ).
  Proof.
    iIntros (??) "[Hi Htok]".
    rewrite /i_Authenticable /v_Authenticable.
    wp_apply gwp_map_empty; [done|].
    iIntros (d) "Hd".
    i_bind (i_unauth)%V.
    iMod (na_inv_alloc seqG_name ⊤ tableN (is_susp_table c) with "[$Hd $Hc]") as "#Htab".
    { by iApply big_sepM_empty. }
    i_bind _.
    wp_pures. i_pures.
    iPoseProof (refines_auth_unauth with "Htab [Hi $Htok]") as "Hwp".
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

             
