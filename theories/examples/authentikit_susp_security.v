From auth.prelude Require Import stdpp.
From auth.rel_logic_bin Require Export model spec_rules spec_tactics interp lib adequacy fundamental.
From auth.heap_lang Require Import gen_weakestpre typedproph.
From auth.heap_lang.lib Require Import list map.
From auth.examples Require Export authentikit_susp authentikit_base_susp_security.
From iris.base_logic.lib Require Export na_invariants.
From iris.algebra Require Import auth agree numbers.

(* Class tableG (Σ: gFunctors) := {
  tableG_na_invG :: na_invG Σ;
  tableG_name: gname;
}.

Definition table_inv `{!invGS_gen hlc Σ} `{!tableG Σ} (N : namespace) (P : iProp Σ) :=
  na_inv tableG_name N P.
Definition table_tok `{!invGS_gen hlc Σ} `{!tableG Σ} (E : coPset) :=
  na_own tableG_name E. *)

Definition idcntrUR := authUR nat.
Class idcntrG Σ := IdcntrG { idcntr_inG :> inG Σ idcntrUR; idcntrG_name : gname }.

(* Definition msizeUR := authUR natUR.
Class msizeG Σ := MsizeG { msize_inG :> inG Σ msizeUR; msizeG_name : gname }.

Lemma msize_alloc `{inG Σ msizeUR} :
  ⊢ |==> ∃ _ : msizeG Σ,
      (own msizeG_name (●{DfracOwn (1/2)} 0) ∗
         own msizeG_name (●{DfracOwn (1/2)} 0) ∗ own msizeG_name (◯ 0))%I.
Proof.
  iMod (own_alloc (● 0 ⋅ ◯ 0)) as (γ) "[Hauth Hfrag]"; [admit|].
  set (H1 := MsizeG _ _ γ).
  iExists _. iDestruct "Hauth" as "[$ $]".
  by iFrame.
Admitted. *)

Lemma idcntr_alloc `{inG Σ idcntrUR} :
  ⊢ |==> ∃ _ : idcntrG Σ, (own idcntrG_name (●{DfracOwn (1/2)} 0) ∗ own idcntrG_name (●{DfracOwn (1/2)} 0))%I.
Proof.
  iMod (own_alloc (● 0 ⋅ ◯ 0)) as (γ) "[Hauth _]"; [admit|].
  set (H1 := IdcntrG _ _ γ).
  iExists _.
  by iDestruct "Hauth" as "[$ $]".
Admitted.

(* Lemma state_alloc `{inG Σ stateUR} :
  ⊢ |==> ∃ _ : stateG Σ, (own stateG_name (● (∅, ∅)))%I.
Proof.
  iMod (own_alloc ((● (∅, ∅)) : stateUR)) as (γ) "Hst"; [admit|].
  by iExists (StateG _ _ γ).
Admitted. *)
  
Section proof.
  Context `{!idcntrG Σ, !authG Σ, !seqG Σ}.

  Definition authBaseN : namespace := nroot .@ "susp_ver".
  Definition gmapN : namespace := authBaseN .@ "gmap".
  Definition tableN : namespace := authBaseN .@ "table".
  Definition tableLocSet : namespace := authBaseN .@ "tableloc".
  Definition tableLocN (susp : val) : namespace := tableLocSet .@ susp.

  (* Definition msize_auth (n : nat) : iProp Σ :=
    own msizeG_name (●{DfracOwn (1/2)} n) ∗ own msizeG_name (◯ n).
  Definition msize_frag (n : nat) : iProp Σ :=
    own msizeG_name (●{DfracOwn (1/2)} n). *)

  Definition idcntr_frag (n : nat) := own idcntrG_name (●{DfracOwn (1/2)} n).

  Local Notation s_is_ser_proph := (s_is_ser_proph authBaseN).
  Local Notation ser_spec_un := (ser_spec_un authBaseN).
  Local Notation ser_spec_3 := (ser_spec_3 authBaseN).
  Local Notation count_spec := (count_spec authBaseN).
  Local Notation val_eq_rel := (val_eq_rel authBaseN).

  Local Notation lrel_evidence := (lrel_evidence authBaseN).
  Local Notation lrel_auth := (lrel_auth authBaseN).


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

  Definition finish_spec1 (finish : val) (x a aᵥ aᵢ ser : val) (A : lrel_bi Σ) : iProp Σ :=
    ∀ (s s' : string) (E: coPset) (t t' : evi_type),
      ⌜↑authSet authBaseN ⊆ E⌝ -∗
      {{{ seq_tok E ∗ ⌜a = InjLV #(hash s)⌝ ∗ hashed s ∗ ser_spec_3 ser t ∗ 
          s_is_ser_proph t x s' ∗ s_is_ser'' t' aᵥ s ∗ lrel_bi_bin A aᵥ aᵢ }}}
            (* ser_spec_3 ser t  ∗
            val_eq_rel authBaseN (lrel_bi_bin A) ∗ val_eq_rel_un authBaseN (lrel_bi_un A) ∗ *)
            (* s_is_ser'' t' aᵥ s ∗ ⌜a = InjLV #(hash s)⌝ }}} *)
        finish #()
        {{{ (o : option val), RET $o;
        (* We might prophesy that the filled-in value is the correct one,
           But it is still possible that the value isn't actually filled. *)
            seq_tok E ∗ if o is None then True else ⌜s = s'⌝ }}}.

  Definition finish_spec2 (finish : val) (x a aᵥ aᵢ ser : val) (A : lrel_bi Σ) : iProp Σ :=
    ∀ (s s' h : string) (E: coPset) (t t' : evi_type) (susp : loc),
      ⌜↑authSet authBaseN ⊆ E ∧ ↑tableN ⊆ E⌝ -∗
      {{{ seq_tok E ∗ ⌜a = InjRV #susp⌝ ∗ ser_spec_3 ser t ∗ hashed s ∗
          seq_inv (authN authBaseN susp) (auth_inv h susp) ∗
          s_is_ser_proph t x s' ∗ s_is_ser'' t' aᵥ s ∗ lrel_bi_bin A aᵥ aᵢ ∗
          ⌜h = some_ser_str (string_ser_str (hash s))⌝ }}}
            (* ser_spec_3 ser t  ∗
            val_eq_rel authBaseN (lrel_bi_bin A) ∗ val_eq_rel_un authBaseN (lrel_bi_un A) ∗ *)
            (* s_is_ser'' t' aᵥ s ∗ ⌜a = InjLV #(hash s)⌝ }}} *)
        finish #()
        {{{ (o : option val), RET $o;
        (* We might prophesy that the filled-in value is the correct one,
           But it is still possible that the value isn't actually filled. *)
            seq_tok E ∗ if o is None then True else ⌜s = s'⌝ }}}.

  Definition susp_big_sep (m : gmap val val) : iProp Σ :=
    [∗ map] k ↦ v ∈ m,
      ∃ (ctr : nat) (finish x a aᵥ aᵢ ser : val) (t : evi_type) (A : lrel_bi Σ) (s : string),
        (⌜ctr > 0 ∧ v = (#ctr, finish)%V⌝ ∗ 
            lrel_bi_un A x ∗ ser_spec_3 ser t ∗
            ((⌜a = InjLV #(hash s)⌝ ∗ hashed s ∗ finish_spec1 finish x a aᵥ aᵢ ser A) ∨ 
              (∃ (susp : loc), ⌜a = InjRV #susp⌝ ∗ finish_spec2 finish x a aᵥ aᵢ ser A ∗
                seq_inv (authN authBaseN susp) (auth_inv s susp)))).
           (* ∨ (∃ (susp : loc), ⌜a = InjRV #susp⌝ ∗ susp↦□ InjRV #h ∗
                                                finish_spec2 finish x a aᵥ aᵢ ser A))). *)
      
  Definition is_susp_table (l : loc) : iProp Σ :=
    ∃ (d : val) (m : gmap val val),
      l ↦ d ∗ ⌜is_map d m⌝ ∗ susp_big_sep m.
        (* idcntr_frag c ∗ (∀ (id : nat), ⌜id ≥ c → m !! #id = None⌝) *)

  (* Definition in_susp_table (l : loc) (id : nat) : iProp Σ :=
    ∃ (d v : val) (m : gmap val val) (s : nat),
      is_susp_table l -∗ l ↦ d ∗ ⌜is_map d m⌝
      -∗ is_susp_table l ∗ ⌜m !! #id = Some v⌝.

  Definition not_in_susp_table (l : loc) (id : nat) : iProp Σ :=
    ∃ (d : val) (m : gmap val val) (s : nat),
      is_susp_table l -∗ l ↦ d ∗ ⌜is_map d m s⌝
      -∗ is_susp_table l ∗ ⌜m !! #id = None⌝. *)

  Definition inv_susp_table (l: loc) := seq_inv tableN (is_susp_table l).

  (* Lemma idcntr_update (cnt : nat) :
    idcntr_frag cnt ∗ idcntr_frag cnt ==∗ idcntr_frag (cnt + 1) ∗ idcntr_frag (cnt + 1).
  Proof. Admitted.

  Lemma idcntr_agree (cnt cnt' : nat) :
    idcntr_frag cnt ∗ idcntr_frag cnt' -∗ ⌜cnt = cnt'⌝ ∗ idcntr_frag cnt ∗ idcntr_frag cnt'.
  Proof. Admitted. *)

  (* Definition count_inv (cnt : nat) (m : mapUR) (lm : locPidMapUR) :=
    ∀ (id : nat),
      id ≥ cnt →
      (m !! id = None ∧
         (∀ (l : loc), lm !! l = None ∨
                         (∀ id', lm !! l = Some id' → id ≠ id'))).
  
  Definition global_state (cnt : nat) (m : mapUR) (lm : locPidMapUR) : iProp Σ :=
    own stateG_name (● (m, lm)) ∗ idcntr_frag cnt ∗
      ⌜count_inv cnt m lm⌝ ∗
      (∀ (id : nat) (x vᵥ : val) (l : loc) (t : evi_type),
          ⌜m !! id = Some (to_agree (t, x, vᵥ, (None : option loc), true))⌝ -∗
            (in_susp_table l id ∨ (not_in_susp_table l id ∗ val_eq t x vᵥ))).
  
  Definition empty_state : prodUR mapUR locPidMapUR := (∅, ∅).

  Lemma init_global_state :
    idcntr_frag 0 ==∗ global_state 0 ∅ ∅.
  Proof.
    iIntros "Hfrag".
    iFrame.
    iMod state_alloc as (γs) "Hst".

    iModIntro. iSplitL; [admit|].
    iSplit.
    { iPureIntro. intros ??. split; first done.
      intros ?. by left. }
    iIntros (??????). done.
  Admitted.
  
  Lemma global_state_update_empty (cnt : nat) (m : mapUR) (lm : locPidMapUR) :
    global_state cnt m lm ∗ idcntr_frag cnt ==∗ global_state (cnt+1) m lm ∗ idcntr_frag (cnt+1).
  Proof.
    iIntros "((Hst & Hcntfrag & %Hcntinv & Hseminv) & Hcntauth)".
    
    iCombine "Hcntauth Hcntfrag" as "Hfull".
    iMod (own_update with "Hfull") as "[Hfull _]".
    { apply (auth_update _ 0 (cnt+1) 1).
      apply (nat_local_update _ _ (cnt+1)).
      lia. }

  Admitted.

  Definition singleton_map (id : nat) (t : evi_type) (x vᵥ : val) (so : option loc) (b : bool) : mapUR :=
    {[ id := to_agree (t, x, vᵥ, so, b) ]}.

  Definition single_instance_frag (id : nat) (t : evi_type) (x vᵥ : val) (so : option loc) (b : bool) : stateUR :=
    ◯ (singleton_map id t x vᵥ so b, if so is Some s then {[ s := id ]} else ∅).

  Definition updated_map (m : mapUR) (id : nat) (t : evi_type) (x vᵥ : val) (so : option loc) (b : bool) : mapUR :=
    <[ id := to_agree (t, x, vᵥ, so, b) ]> m.

  Definition updated_loc_map (m : locPidMapUR) (so : option loc) (id : nat) : locPidMapUR :=
    if so is Some s then <[ s := id ]> m else m.

  Lemma global_state_update_singleton (cnt : nat) (m : mapUR) (lm : locPidMapUR) (t : evi_type) (x vᵥ : val) (so : option loc) (b : bool) :
    global_state cnt m lm ∗ idcntr_frag cnt
    ==∗ global_state (cnt + 1) (updated_map m cnt t x vᵥ so b) (updated_loc_map lm so cnt) ∗ single_instance cnt t x vᵥ so b ∗ idcntr_frag (cnt + 1).
  Proof.
    iIntros "((Hst & Hcntfrag & %Hcntinv & Hseminv) & Hcntauth)".
    iMod ((own_update
             stateG_name
             (● (m, lm))
             (● (updated_map m cnt t x vᵥ so b, updated_loc_map lm so cnt) ⋅ single_instance_frag cnt t x vᵥ so b))
           with "Hst") as "Hst".
    { apply (auth_update _ empty_state _ _).
      apply prod_local_update; simpl.
      { apply gmap.alloc_local_update; last done.
        apply Hcntinv. lia. }
      destruct so; last done.
      admit. }
    iPoseProof (own_op with "Hst") as "[Hst Hfrag]".

    iCombine "Hcntauth Hcntfrag" as "Hfull".
    iMod (own_update with "Hfull") as "[Hfull _]".
    { apply (auth_update _ 0 (cnt+1) 1).
      apply (nat_local_update _ _ (cnt+1)).
      lia. }

    iAssert (idcntr_frag (cnt + 1) ∗ idcntr_frag (cnt + 1))%I with "[Hfull]" as "[H1 H2]".
    { admit. }

    iModIntro.
    iSplitR "H2 Hfrag"; [|iFrame].

    rewrite /global_state.
    iFrame. iSplitR "Hseminv".
    iPureIntro.
    { intros id H. rewrite /updated_map.
      rewrite lookup_insert_None.
      split; last admit.
      split; last lia.
      apply Hcntinv. lia. }
    iIntros (?????).
    iSpecialize ("Hseminv" $! id x0 vᵥ0 l t0) as #.
    iIntros (?). iApply "Hseminv".
  Admitted.

  Lemma msize_agree (s s' : nat) :
    msize_auth s ∗ msize_frag s' -∗ ⌜s = s'⌝ ∗ msize_auth s ∗ msize_frag s'.
  Proof.
    iIntros "[[Hauth1 Hfrag] Hauth2]".
    iCombine "Hauth1 Hauth2" as "Hauth".
    iDestruct (own_valid with "Hauth") as "%H".
    move: H => /auth_auth_dfrac_op_inv ->.

    iDestruct "Hauth" as "[Hauth1 Hauth2]". by iFrame.
  Qed.

  Lemma msize_update (s s': nat) :
    msize_auth s ∗ msize_frag s ==∗ msize_auth s' ∗ msize_frag s'.
  Proof.
    iIntros "[[Hauth1 Hfrag] Hauth2]".
    iCombine "Hauth1 Hauth2" as "Hauth".
    iMod (own_update_2 with "Hauth Hfrag") as "[Hauth Hfrag]".
    { apply (auth_update s s s' s').
      apply nat_local_update. lia. }

    iDestruct "Hauth" as "[Hauth1 Hauth2]".
    by iFrame.
  Qed.
    
  Lemma idcntr_agree (cnt cnt' : nat) :
    ∀ m lm, global_state cnt m lm ∗ idcntr_frag cnt'
            -∗ ⌜cnt = cnt'⌝ ∗ global_state cnt m lm ∗ idcntr_frag cnt.
  Proof.
    iIntros (??) "[(? & Hcntfrag & ?) Hidauth]".
    iCombine "Hcntfrag Hidauth" as "Hfull".
    iDestruct (own_valid with "Hfull") as "%H".
    move: H => /auth_auth_dfrac_op_inv H.
    rewrite H.

    iDestruct "Hfull" as "[Hcntfrag Hidauth]".
    by iFrame.
  Qed. *)
    
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
    ∀ (a aᵥ aᵢ x ser : val) (st : loc) (A : lrel_bi Σ),
      {{{ inv_susp_table st }}}
        v_finish #st a x ser
        {{{ (finish : val), RET finish;
            finish_spec1 finish x a aᵥ aᵢ ser A }}}.
  Proof.
    iIntros (????????) "#Htab HΦ".
    rewrite /v_finish.
    wp_pures. iModIntro. iApply "HΦ".
    rewrite /finish_spec1.
    iIntros (??????).
    iIntros (?) "!# (Htok & % & #hashs & #Hserspec & Hserproph & Hser & #HA) HΦ".
    (* iIntros (?) "!# (Htok & Hserproph & #HA & #Hserspec & #hashs & #Hrel_bin & #Hrel_un & #Hser & %) HΦ". *)
    wp_pures. wp_apply ("Hserspec" with "[//] [$Hserproph $Htok]").
    iIntros ([]); last first.
    { iIntros "(Htok & #Hsers)". wp_pures.
      iModIntro. iApply ("HΦ" $! None). eauto. }
    iIntros "(Htok & #[[% #Hsers]|%])"; simplify_eq; wp_pures;
    wp_apply (wp_hash); try done;
    iIntros "#hashs0"; wp_pures;
    case_bool_decide; simplify_eq; wp_pures;

    destruct (decide (collision s s')) as [|Hnc%not_collision];
      try (iExFalso; by iApply (hashes_auth.hashed_inj_or_coll with "hashs hashs0") );
    destruct Hnc as [<-|?]; simplify_eq.
    - iApply ("HΦ" $! (Some _)). by iFrame "∗ #".
    - iApply ("HΦ" $! None); by iFrame "∗ #".

    (* iPoseProof "HA" as "[HA_bin HA_un]".
    iMod ("Hrel_bin" with "[//] Htok [Hsers] Hser HA_bin") as "[Htok HA'_bin]".
    { by iLeft. }
    iMod ("Hrel_un" with "[//] Htok [Hsers] Hser HA_un") as "[Htok HA'_un]".
    { by iLeft. }

    iApply ("HΦ" $! (Some _)). by iFrame "∗ #". *)
  Qed.

  Lemma v_finish_spec2 :
    ∀ (a aᵥ aᵢ x ser : val) (st : loc) (A : lrel_bi Σ),
      {{{ inv_susp_table st }}}
        v_finish #st a x ser
        {{{ (finish : val), RET finish;
            finish_spec2 finish x a aᵥ aᵢ ser A }}}.
  Proof.
    iIntros (????????) "#Htab HΦ".
    rewrite /v_finish.
    wp_pures. iModIntro. iApply "HΦ".
    rewrite /finish_spec1.
    iIntros (???????[??]).
    iIntros (?) "!# (Htok & % & #Hserspec & #hashs & #Hinv & #Hserproph & #Hser & #HA & %) HΦ".
    wp_pures. wp_apply ("Hserspec" with "[//] [$Hserproph $Htok]").
    iIntros ([]); last first.
    { iIntros "(Htok & #Hsers)". wp_pures.
      iModIntro. iApply ("HΦ" $! None). eauto. }
    iIntros "(Htok & #[[% Hsers]|%])"; simplify_eq; wp_pures.
    iMod (na_inv_acc with "Hinv Htok") as "(Hinv1 & Htok & Hclose)"; [solve_ndisj|solve_ndisj|].
    iDestruct "Hinv1" as ">[(%&%& #hashs1 & %& #Hsusp & %Hser)|(%&%&%& Hsusp & Hproph & %Hser)]";
      wp_load; wp_pures; destruct! Hser; simplify_eq.
    - iMod ("Hclose" with "[$Htok]") as "Htok".
      { iNext. iLeft. iFrame "hashs #". iSplit; try done.
        iRight. repeat iExists _. iSplit; eauto. }
      wp_apply wp_hash; try done;
      iIntros "#hashs0"; wp_pures.
      destruct (decide (collision s1 s)) as [|Hnc%not_collision];
        try (iExFalso; by iApply (hashes_auth.hashed_inj_or_coll with "hashs1 hashs") );
      destruct Hnc as [<-|?]; simplify_eq.

      case_bool_decide; simplify_eq; wp_pures;

      destruct (decide (collision s1 s')) as [|Hnc%not_collision];
        try (iExFalso; by iApply (hashes_auth.hashed_inj_or_coll with "hashs1 hashs0") );
      destruct Hnc as [<-|?]; simplify_eq.
      + iApply ("HΦ" $! (Some _)). by iFrame "∗ #".
      + iApply ("HΦ" $! None); by iFrame "∗ #".
    
    - wp_apply wp_hash; try done; iIntros "#hashs0"; wp_pures.
      wp_apply (typed_proph_wp_resolve1 StringTypedProph with "Hproph"); try done.
      wp_pures. iModIntro. iIntros (->). wp_pures.

      iMod (na_inv_acc with "Htab Htok") as "(Htabo & Htok & Hclose_tab)"; [solve_ndisj|solve_ndisj|].
      iDestruct "Htabo" as (??) "(Hl & >%Hm & #Hbigsep)".
      wp_apply wp_hash; try done; iIntros "_"; wp_pures; wp_store.
      iMod (pointsto_persist with "Hsusp") as "#Hsusp".

      wp_load. wp_bind (map_lookup _ _).
      wp_apply (gwp_map_lookup with "[//]"); try done.
      iIntros (??). destruct (m !! #pid) eqn:Hlookup;
        simpl in H1; simplify_eq; wp_pures; last first.
      { iMod ("Hclose_tab" with "[$Hl $Hbigsep $Htok //]") as "Htok".
        iMod ("Hclose" with "[$Htok]") as "Htok".
        { iNext. iLeft. iFrame "#". iSplit; eauto.
          iRight. repeat iExists _. iSplit; eauto. }
        iApply ("HΦ" $! None). by iFrame. }

      iDestruct (big_sepM_lookup with "Hbigsep") as "[% Hs]"; [done|subst].
      iDestruct "Hs" as (????????? Hv) 
        "(#HA' & Hserspec' & [(%&hashs'&Hfinish)|(%&%&Hfinish&Hinvx)])";
        destruct! Hv; simplify_eq; wp_pures;
        case_bool_decide; simplify_eq; wp_pures; wp_load;
        wp_bind (map_remove _ _); wp_apply (gwp_map_remove with "[//]");
        try done; iIntros (??); wp_store; wp_pures;
        iDestruct (big_sepM_delete _ m #pid ((#ctr, finish)%V) with "Hbigsep")
          as "[_ #Hbigsep']"; try done.
      1,3: (* First branch of the if *)
        iMod ("Hclose_tab" with "[$Hl $Hbigsep' $Htok]") as "Htok".
        1,3: iNext; iFrame "%".
      1,2: (* refocus on first branch *)
        iMod ("Hclose" with "[$Htok]") as "Htok";
        try (iNext; iLeft; iFrame "hashs0 #"; iSplit; eauto;
              iRight; repeat iExists _; iSplit; eauto);
        wp_apply ("Hfinish" with "[] [$Htok]"); try done
        iFrame "#"; eauto.
      all: (* else branch *)
        wp_load; wp_pures; wp_bind (map.map_insert _ _ _);
        wp_apply (gwp_map_insert with "[//]"); try done;
        iIntros (??); wp_store;
        iDestruct (big_sepM_insert _ (delete #pid m) #pid ((#(ctr-1), finish)%V) with "[$Hbigsep']")
          as "Hbigsep''"; try apply lookup_delete; 
          iFrame "#"; repeat iExists _.
        1,3: 
          iSplit; try (iPureIntro; instantiate (1 := ctr-1); split; repeat f_equal; try lia);
            eauto; admit. (* ctr - 1 > 0 *)
      all:
        iMod ("Hclose_tab" with "[$Hl $Hbigsep'' $Htok $Hfrag]") as "Htok";
          iFrame "%";
        iMod ("Hclose" with "[$Htok]") as "Htok";
        try (iNext; iLeft; iFrame "hashs0 #"; iSplit; eauto;
              iRight; repeat iExists _; iSplit; eauto);
        iModIntro; by iApply ("HΦ" $! (Some _)).
  Admitted.

  (* Lemma v_finish_spec1_bad :
    ∀ (a x ser : val) (st : loc),
      {{{ inv_susp_table st }}}
        v_finish #st a x ser
        {{{ (finish : val), RET finish;
            finish_spec1_bad finish x a ser }}}.
  Proof.
    iIntros (?????) "#Htab HΦ".
    rewrite /v_finish.
    wp_pures. iModIntro. iApply "HΦ".
    rewrite /finish_spec1.
    iIntros (?????).
    iIntros (?) "!# (Htok & Hserproph & #Hserspec & #hashs & % & Hval) HΦ".
    wp_pures. wp_apply ("Hserspec" with "[//] [$Hserproph $Htok]").
    iIntros ([]); last first.
    { iIntros "(Htok & #Hsers)". wp_pures.
      iModIntro. iApply ("HΦ" $! None). eauto. }
    iDestruct "Hval" as "[%|(%&%& Hsusp)]";
      iIntros "(Htok & #[[% Hsers]|%])"; simplify_eq; wp_pures; [|wp_load; wp_pures];
      wp_apply (wp_hash); try done; iIntros "#hashs0"; wp_pures;

      destruct (decide (collision s1 s2)) as [|Hnc%not_collision];
        try ( iExFalso; by iApply (hashes_auth.hashed_inj_or_coll with "hashs0 hashs"));
        destruct Hnc as [<-|?]; simplify_eq;
        case_bool_decide; wp_pures; simplify_eq;
        iApply ("HΦ" $! None); eauto.
  Qed. *)
    
  (* Lemma v_finish_spec2 :
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
  Qed. *)

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
      {{{ spec_ideal t (fill K (v2 w')) ∗ seq_tok ⊤ ∗ is_proof_state w cntr ∗ idcntr_frag cntr }}}
        v1 w
      {{{ (o1 : option val), RET $o1;
          seq_tok ⊤ ∗
            if o1 is Some w1 then
              ∃ (a prfst prf : val) (cntr' : nat),
                 ⌜w1 = (prfst, a)%V ∧ prfst = (prf, #cntr')%V⌝ ∗ idcntr_frag cntr' ∗
                  ((∃ (w2 : val), spec_ideal t (fill K w2) ∗ lrel_auth_comp_post A w1 w2) ∨ lrel_auth_comp_post_bad (lrel_bi_un A) w1)
            else True }}})%I.

  Definition lrel_un_auth_comp' (A_un : lrel_un Σ) : lrel_un Σ := LRelUn (λ v1,
    ∀ (w : val) (cntr : nat),
      {{{ seq_tok ⊤ ∗ is_proof_state w cntr ∗ idcntr_frag cntr }}}
        v1 w
      {{{ (o1 : option val), RET $o1;
          seq_tok ⊤ ∗
            if o1 is Some w1 then
              ∃ (a prfst prf : val) (cntr' : nat),
                ⌜w1 = (prfst, a)%V ∧ prfst = (prf, #cntr')%V⌝ ∗ idcntr_frag cntr' ∗
                  lrel_auth_comp_post_bad A_un w1
            else True }}})%I.

  (* Definition lrel_auth_comp_bad : lrel Σ := LRel (λ v1 v2,
    ∀ w,
      {{{ seq_tok ⊤ ∗ is_proof_state w }}}
        v1 w
      {{{ (o1 : option val), RET $o1;
          seq_tok ⊤ ∗
            if o1 is Some w1 then lrel_auth_comp_post_bad w1 v2
            else True }}})%I. *)

  Definition lrel_auth_comp' (A : lrel_bi Σ) : lrel_bi Σ :=
    LRelBi (lrel_un_auth_comp' (lrel_bi_un A)) (lrel_bin_auth_comp' A).
        
  Program Definition lrel_auth_comp : kindO Σ (⋆ ⇒ ⋆)%kind := λne A, lrel_auth_comp' A.
  Next Obligation.
    intros ????. split; [intros ?|intros ??];
      rewrite /lrel_car/= /lrel_un_car/= /lrel_un_auth_comp' /lrel_bin_auth_comp';
      do 25 f_equiv; first solve_proper.
    do 10 f_equiv; solve_proper.
  Qed.

  (* Definition lrel_hash_fail_option' (A : lrel Σ) : lrel Σ := LRel (λ v1 v2,
    (A v1 v2 ∨ (∃ x, A x v2)))%I.

  Program Definition lrel_hash_fail_option : kindO Σ (⋆ ⇒ ⋆)%kind := λne A, lrel_hash_fail_option' A.
  Next Obligation.
    intros ??????. rewrite /lrel_car /=.
    solve_proper.
  Qed.    *)
  
  Definition auth_ctx {Θ} (Δ : ctxO Σ Θ) := ext (ext Δ lrel_auth) lrel_auth_comp.

  Lemma refines_un_auth_return Θ (Δ : ctxO Σ Θ) (A : kindO Σ ⋆) v :
    lrel_bi_un A v -∗
    lrel_bi_un (⟦ var1 ⟧ (ext (auth_ctx Δ) A) A) (λ: "pf", InjR ("pf", v))%V.
  Proof.
    iIntros "#HA".
    rewrite interp_var1_ext2.
    iIntros (?? Ψ) "!# (Htok & %H & Hid) HΨ".
    simpl in H. destruct H as (? & -> & Hp).
    wp_pures. iModIntro. iApply ("HΨ" $! (Some _)).
    iFrame "Htok". iExists _, _, _, _.
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
          iIntros (????? Ψ) "!# (Hi & Htok & %H & Hid) HΨ".
          simpl in H. destruct H as (? & -> & Hp).
          i_pures; wp_pures.
          iModIntro. iApply ("HΨ" $! (Some _)).
          iFrame "Htok".
          iExists _, _, _, _.
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
    iIntros (???Ψ) "!# [Htok [#Hprf Hid]] HΨ". wp_pures.
    wp_pures. wp_bind (v _)%I.
    wp_apply ("HmA" with "[$Htok $Hprf $Hid]").
    iIntros (o) "[Htok Ho]".
    destruct o; last first.
    { wp_pures. iApply ("HΨ" $! None). by iFrame. }
    iPoseProof "Hprf" as (??) "Hprf'". 
    iDestruct "Ho" as (????[??]) "[Hid (%&%&%&%& #Hprf1 & HA)]".
    iPoseProof "Hprf1" as (??) "Hprf1'". 
    simplify_eq. wp_pures.
    rewrite interp_un_arr_unfold.
    iSpecialize ("HmB" with "[HA] [$Htok]").
    { by interp_unfold!. }
    wp_apply (wp_wand with "HmB").
    iIntros (?) "(H & Htok) /=".
    interp_unfold in "H".
    rewrite interp_var2_ext3.
    wp_apply ("H" with "[$Htok $Hprf1 $Hid]").
    iIntros (?) "(Htok & Ho) /=".
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
              iIntros (u1 u2 ??? Ψ) "!# (Hi & Htok & Hprf & Hid) HΨ".
              i_pures; wp_pures.
              i_bind (v2 _)%I; wp_bind (v1 _)%I.
              iDestruct "HmA" as "[HmA _]".
              wp_apply ("HmA" with "[$Hi $Htok $Hprf $Hid]").
              iIntros (o) "[Htok Ho]".
              destruct o; last first.
              { wp_pures. iApply ("HΨ" $! None). by iFrame. }
              iDestruct "Ho" as (????) "(%H & Hid & [H|H])".
              + iDestruct "H" as (?) "[Hi H]".
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
                wp_apply ("H" with "[$Hi $Htok $Hprf $Hid]").
                iIntros (?) "(Htok & Ho) /=".
                iApply "HΨ". iFrame.
              + iDestruct "H" as (??? ->) "(#Hprf & #HA)".
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
                wp_apply ("H" with "[$Htok $Hprf $Hid]").
                iIntros (?) "(Htok & Ho) /=".
                iApply "HΨ". iFrame.
                destruct o1; last done. iFrame.
                iDestruct "Ho" as (????[??]) "[Hbad Hid]".
                iExists _, _, _, _. iSplit; first done.
                iFrame. }
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
            { iIntros (??????) "!# (Hi & Htok & Hproof & Hid) HΦ".
              wp_pures. iApply ("HΦ" $! None). by iFrame. }
            iIntros (???) "!# (Htok & Hproof) HΦ".
            wp_pures. iApply ("HΦ" $! None). by iFrame. }
          iDestruct "Hauth_un" as "[(% & % & Hauth_un)|->]"; last first.
          { iFrame. iModIntro.
            interp_unfold!. rewrite interp_var2_ext3. iSplit.
            { iIntros (??????) "!# (Hi & Htok & Hproof & Hid) HΦ".
              wp_pures. iApply ("HΦ" $! None). by iFrame. }
            iIntros (???) "!# (Htok & Hproof) HΦ".
            wp_pures. iApply ("HΦ" $! None). by iFrame. }

          iDestruct "Hevi" as "[Hrel Hevi_un]".    
          iDestruct "Hevi_un" as (tA' ??? ->) "(#Hser' & #Hser3 & #Hcount & #Hdeser)".
          simplify_eq.
          iFrame. iModIntro.
          iSplit; interp_unfold!; rewrite interp_var2_ext3.
          { iIntros (??????) "!# (Hi & Htok & Hproof & Hid) HΦ".
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
            
            iPoseProof "Hauth_bi" as "(%&%&%&#Hser1&#HA&[(#hashs1&%)|(%&%&%&%&Hinv)])";
              simplify_eq; iIntros "[Hserser Hserproph]";
              iPoseProof ("Hserproph" with "Hserser") as ">[#HA_un [%s2 #Hserproph]]";
              wp_pures; wp_apply ("Hcount" $! _ _ ⊤ with "[//] [$Hserproph $Htok]");
              iIntros (?) "[_ Htok]"; wp_pures.
            - (* iPoseProof (deser_ser_proph authBaseN with "[$Htok $Hserser]") as ">[Htok [% Hserproph]]". *)
              wp_apply (v_finish_spec1 with "Htab").
              iIntros (finish) "Hfinish". wp_pures.

              case_bool_decide; wp_pures; simplify_eq.
              + wp_bind (finish #()).
                assert (c0 = 0); [lia|]. simplify_eq.

                iApply ("Hfinish" $! s1 ⊤ tA' with "[//] [$Htok $Hser' $HA_un $hashs1]");
                  first by iLeft.
                iNext. iIntros ([]) "Htok"; wp_pures; last first.
                { iApply ("HΦ" $! (None)). eauto. }

                wp_apply gwp_list_tail; [done|].
                iIntros (vl Hl).

                iMod (na_inv_acc with "Htab Htok") as "(Htabo & Htok & Hclose_tab)"; [solve_ndisj|solve_ndisj|].
                iDestruct "Htabo" as (???) "(Hl & >%Hm & Hbigsep & Hfrag)".
                wp_pures.

                iPoseProof (idcntr_agree with "[$Hid $Hfrag]") as (->) "[Hid Hfrag]".
                iMod (idcntr_update with "[$Hid $Hfrag]") as "[Hid Hfrag]".

                (* iPoseProof (idcntr_agree with "[$Hst $Hfrag]") as (->) "[Hst Hfrag]".
                iMod (global_state_update_empty with "[$Hst $Hfrag]") as "[Hst Hfrag]". *)
                
                iMod ("Hclose_tab" with "[$Hl $Hbigsep $Htok $Hfrag]") as "Htok"; try done.
                (* { iFrame "%". iPureIntro. intros ?. apply Hci. lia. } *)
                
                iApply ("HΦ" $! (Some _)).

                destruct (decide (s2 = s1)); simplify_eq;
                  [iMod ("Hrel" $! ⊤ with "[//] Htok [Hserproph] Hser1 HA") as "[Htok #HA']";
                    try by iRight|]; iFrame "# ∗ %"; iModIntro; repeat (iExists _); 
                    iSplit; try (iSplit; try done; iPureIntro; repeat f_equal; lia);
                    [iLeft|iRight]; iFrame "# ∗ %"; iExists _; iExists (c0+1);
                    iSplit; iPureIntro; repeat f_equal; lia.

              + iMod (na_inv_acc with "Htab Htok") as "(Htabo & Htok & Hclose_tab)"; [solve_ndisj|solve_ndisj|].
                iDestruct "Htabo" as (???) "(Hl & >%Hm & Hbigsep & Hfrag)". wp_load.

                (* iPoseProof (idcntr_agree with "[$Hst $Hfrag]") as (->) "[Hst Hfrag]".
                iPoseProof (msize_agree with "[$Hms $Hs]") as (<-) "[Hms Hs]".
                iMod (global_state_update_singleton with "[$Hst $Hfrag]") as "(Hst & Hins & Hfrag)". *)
                iPoseProof (idcntr_agree with "[$Hid $Hfrag]") as (->) "[Hid Hfrag]".
                iMod (idcntr_update with "[$Hid $Hfrag]") as "[Hid Hfrag]".

                (* assert (m0 !! #c1 = None). { apply Hci. lia. } *)
                wp_bind (map.map_insert _ _ _). wp_pures.
                iApply (gwp_map_insert #c1 (#c0, finish)%V d m _ _); [done|done|].
                
                iModIntro. iIntros (d') "%Hmap'". wp_store.
                (* iMod (msize_update _ (s+1) with "[$Hms $Hs]") as "[Hms Hs]". *)
                wp_pures. wp_apply (gwp_list_tail with "[//]").
                iIntros "/=" (tl Htl). wp_pures.
                iMod ("Hclose_tab" with "[$Hl Hbigsep $Htok $Hfrag Hfinish]") as "Htok".
                { iNext. iFrame "%".
                  iApply (big_sepM_insert_2 with "[Hfinish]"); last done.
                  iFrame "∗ #". iExists _.
                  assert (c0 > 0).
                  { apply Nat.neq_0_lt_0. intros ->. by apply H0. }
                  do 2 iExists _. repeat (try (iSplit; eauto)).  }

                iApply ("HΦ" $! (Some _)).
                destruct (decide (s2 = s1)); simplify_eq;
                  [iMod ("Hrel" $! ⊤ with "[//] Htok [Hserproph] Hser1 HA") as "[Htok #HA']";
                    try by iRight|]; iFrame "# ∗ %"; iModIntro; repeat (iExists _);
                    iSplit; try (iSplit; try done; iPureIntro; repeat f_equal; lia);
                    [iLeft|iRight]; iFrame "# ∗ %"; iExists _; iExists (c1+1);
                    iSplit; iPureIntro; repeat f_equal; lia.

            - wp_apply (v_finish_spec2 with "Htab").
              iIntros (finish) "Hfinish". wp_pures.

              case_bool_decide; wp_pures; simplify_eq.
              * wp_bind (finish #()).
                assert (c0 = 0); [lia|]. simplify_eq.

                iApply ("Hfinish" $! _ ⊤ tA' with "[//] [$Htok $Hser' $HA_un $Hinv //]").
                iNext. iIntros ([]) "Htok"; wp_pures; last first.
                { iApply ("HΦ" $! (None)). eauto. }

                wp_apply gwp_list_tail; [done|].
                iIntros (vl Hl).

                iMod (na_inv_acc with "Htab Htok") as "(Htabo & Htok & Hclose_tab)"; [solve_ndisj|solve_ndisj|].
                iDestruct "Htabo" as (???) "(Hl & >%Hm & Hbigsep & Hfrag)".
                wp_pures.

                iPoseProof (idcntr_agree with "[$Hid $Hfrag]") as (->) "[Hid Hfrag]".
                iMod (idcntr_update with "[$Hid $Hfrag]") as "[Hid Hfrag]".

                (* iPoseProof (idcntr_agree with "[$Hst $Hfrag]") as (->) "[Hst Hfrag]".
                iMod (global_state_update_empty with "[$Hst $Hfrag]") as "[Hst Hfrag]". *)
                
                iMod ("Hclose_tab" with "[$Hl $Hbigsep $Htok $Hfrag]") as "Htok"; try done.
                (* { iFrame "%". iIntros (id). iPureIntro. intros ?. apply Hci. lia. } *)
                
                iApply ("HΦ" $! (Some _)).

                destruct (decide (s2 = s1)); simplify_eq;
                  [iMod ("Hrel" $! ⊤ with "[//] Htok [Hserproph] Hser1 HA") as "[Htok #HA']";
                    try by iRight|]; iFrame "# ∗ %"; iModIntro; repeat (iExists _); 
                    iSplit; try (iSplit; try done; iPureIntro; repeat f_equal; lia);
                    [iLeft|iRight]; iFrame "# ∗ %"; iExists _; iExists (c0+1);
                    iSplit; iPureIntro; repeat f_equal; lia.
              
              * iMod (na_inv_acc with "Htab Htok") as "(Htabo & Htok & Hclose_tab)"; [solve_ndisj|solve_ndisj|].
                iDestruct "Htabo" as (???) "(Hl & >%Hm & Hbigsep & Hfrag)". wp_load.

                (* iPoseProof (idcntr_agree with "[$Hst $Hfrag]") as (->) "[Hst Hfrag]".
                iPoseProof (msize_agree with "[$Hms $Hs]") as (<-) "[Hms Hs]".
                iMod (global_state_update_singleton with "[$Hst $Hfrag]") as "(Hst & Hins & Hfrag)". *)
                iPoseProof (idcntr_agree with "[$Hid $Hfrag]") as (->) "[Hid Hfrag]".
                iMod (idcntr_update with "[$Hid $Hfrag]") as "[Hid Hfrag]".

                (* assert (m0 !! #c1 = None). { apply Hci. lia. } *)
                wp_bind (map.map_insert _ _ _). wp_pures.
                iApply (gwp_map_insert #c1 (#c0, finish)%V d m _ _); [done|done|].
                
                iModIntro. iIntros (d') "%Hmap'". wp_store.
                (* iMod (msize_update _ (s+1) with "[$Hms $Hs]") as "[Hms Hs]". *)
                wp_pures. wp_apply (gwp_list_tail with "[//]").
                iIntros "/=" (tl Htl). wp_pures.
                iMod ("Hclose_tab" with "[$Hl Hbigsep $Htok $Hfrag Hfinish]") as "Htok".
                { iNext. iFrame "%".
                  iApply (big_sepM_insert_2 with "[Hfinish]"); last done.
                  iFrame "∗ #". iExists _.
                  assert (c0 > 0).
                  { apply Nat.neq_0_lt_0. intros ->. by apply H0. }
                  do 2 iExists _. repeat (try (iSplit; eauto)). }

                iApply ("HΦ" $! (Some _)).
                destruct (decide (s2 = s1)); simplify_eq;
                  [iMod ("Hrel" $! ⊤ with "[//] Htok [Hserproph] Hser1 HA") as "[Htok #HA']";
                    try by iRight|]; iFrame "# ∗ %"; iModIntro; repeat (iExists _);
                    iSplit; try (iSplit; try done; iPureIntro; repeat f_equal; lia);
                    [iLeft|iRight]; iFrame "# ∗ %"; iExists _; iExists (c1+1);
                    iSplit; iPureIntro; repeat f_equal; lia. }
              
          { iIntros (???) "!# (Htok & Hproof & Hid) HΦ".
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
            
            iPoseProof "Hauth_un" as "[(%&%)|(%&%&%&#Hinv)]";
              simplify_eq; iIntros "[Hserser Hserproph]";
              iPoseProof ("Hserproph" with "Hserser") as ">[#HA_un [%s2 #Hserproph]]";
              wp_pures; wp_apply ("Hcount" $! _ _ ⊤ with "[//] [$Hserproph $Htok]");
              iIntros (?) "[_ Htok]"; wp_pures.
            - 

          }
        }
      }
    }
      
            
  Admitted.

  Lemma refines_Authenticatable Θ (Δ : ctxO Σ Θ) :
    ⊢ REL v_Authenticable << i_Authenticable : ⟦ Authenticatable ⟧ (auth_ctx Δ).
  Proof.
    iIntros (??) "[Hi Htok]".
    rewrite /i_Authenticable /v_Authenticable /v_Authenticable_run.
    wp_apply gwp_map_empty; [done|].
    iIntros (d) "Hd". wp_alloc l as "Hl". wp_pures.
    
    iMod msize_alloc as (γm) "[Hmfrag Hmauth]".
    iMod idcntr_alloc as (γc) "[Hcauth Hcfrag]".
    
    iMod (na_inv_alloc seqG_name ⊤ tableN (is_susp_table l) with "[$Hd $Hl Hmauth Hcauth]") as "#Htab".
    { iNext. iExists 0.
      rewrite /msize_auth /idcntr_frag. iFrame.
      iSplitR; [by iApply big_sepM_empty|].
      iSplitL "Hmauth"; [admit|].
      iSplitL "Hcauth"; [admit|].
      iIntros (id). done. }
    
    iAssert (|={⊤}=> spec_ideal tᵢ (fill Kᵢ (i_Auth_auth, i_Auth_mu, i_Auth_pair, i_Auth_sum, i_Auth_string, i_Auth_int, i_auth, i_unauth)))%I with "[Hi]" as ">Hi"; [admit|].
    
    wp_rec. wp_pures.
    wp_bind (v_unauth _).
    i_bind (i_unauth).    
    iPoseProof (refines_auth_unauth with "Htab [$Hi $Htok]") as "Hwp".
    wp_apply (wp_wand with "Hwp").
    iIntros (?) "(% & Hi & #Hauth & Htok)".
    iSimpl in "Hi".
    i_pures. wp_pures.
    iModIntro. iFrame.
    rewrite /Authenticatable.
    interp_unfold!.
    iExists (lrel_evidence authBaseN).
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
  Admitted.

  Lemma refines_authentikit_func Θ (Δ : ctxO Σ Θ) :
    ⊢ REL v_Authentikit << i_Authentikit : ⟦ Authentikit_func var2 var1 var0 ⟧ (auth_ctx Δ).
  Proof.
    iIntros (??) "[Hi Htok]".
    rewrite /i_Authentikit /v_Authentikit.
    iAssert (|={⊤}=> spec_ideal tᵢ (fill Kᵢ (i_return, i_bind, i_Authenticable)))%I with "[Hi]" as ">Hi"; [admit|].
    
    i_bind (i_Authenticable).
    iPoseProof (refines_Authenticatable with "[$Hi $Htok]") as "H".
    wp_apply (wp_wand with "H").
    iIntros (?) "(% & Hv & #Hauth & Htok)".
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
  Admitted.

  Lemma refines_authentikit Θ (Δ : ctxO Σ Θ) :
    ⊢ REL v_Authentikit << i_Authentikit : ⟦ Authentikit ⟧ Δ .
  Proof.
    iIntros (??) "Hi".
    iPoseProof (refines_authentikit_func with "Hi") as "H".
    wp_apply (wp_wand  with "H").
    iIntros (?) "(% & $ & #Hauth & Htok)".
    do 3 setoid_rewrite interp_exists_unfold. iFrame.
    by iExists lrel_hash_fail_option, lrel_auth, lrel_auth_comp.
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
    iIntros (f1) "(%f2 & Hi & Hc & Htok) /=".
    rewrite /v_Authenticable_run.
    rewrite /i_Authenticable /v_Authenticable /v_Authenticable_run.
    wp_apply gwp_map_empty; [done|].
    iIntros (d) "Hd". wp_alloc l as "Hl". wp_pures.
    
    iMod msize_alloc as (γm) "[Hmfrag Hmauth]".
    iMod idcntr_alloc as (γc) "[Hcauth Hcfrag]".
    
    iMod (na_inv_alloc seqG_name ⊤ tableN (is_susp_table l) with "[$Hd $Hl Hmauth Hcauth]") as "#Htab".
    { iNext. iExists 0.
      rewrite /msize_auth /idcntr_frag. iFrame.
      iSplitR; [by iApply big_sepM_empty|].
      iSplitL "Hmauth"; [admit|].
      iSplitL "Hcauth"; [admit|].
      iIntros (id). done. }

    wp_rec. wp_pures.
    wp_rec. wp_pures.    
    wp_pures; i_pures.
    iMod (init_global_state with "[Hcfrag]") as "Hst"; [admit|].
    wp_apply ("Hc" with "[$Hi $Htok $Hprf Hmfrag Hst]").
    { instantiate (4 := 0). iSplit. { iPureIntro. f_equal. }
      rewrite /msize_frag. iFrame. admit. }

    iIntros (?) "(Htok & Ho)".
    destruct o1; last first.
    { wp_pures. iExists None. by iFrame. }
    
    iMod (na_inv_acc with "Htab Htok") as "(Htabo & Htok & Hclose_tab)"; [solve_ndisj|solve_ndisj|].
    iDestruct "Htabo" as (????) "(Hl & >%Hm & Hbigsep & >Hmauth & Hfrag & >%Hci)".
    iDestruct "Ho" as (????????) "(Hi & % & Hst & Hmfrag & Hpost)".
    iPoseProof (msize_agree with "[$Hmauth $Hmfrag]") as (->) "[Hmauth Hmfrag]".
    wp_pures. wp_load.
    wp_bind (map.map_is_empty _).
    iApply (gwp_map_is_empty with "[]"); [done|].
    iModIntro. iIntros (?) "%".
    simpl in H0. subst.
    iDestruct "Hpost" as "[[-> Hpost]|[% Hpost]]".
    - wp_pures.
      destruct! H. simplify_eq. wp_pures.
      iMod ("Hclose_tab" with "[$Htok $Hbigsep $Hmauth $Hfrag $Hl]") as "Htok".
      { iNext. iFrame "%". }
      iModIntro. iExists (Some _).
      iDestruct "Hpost" as (???) "(% & Hprf' & #HA)".
      iFrame "∗". iSplit; first done. by simplify_eq.
    - destruct l2; [done|]. wp_pures.
      iMod ("Hclose_tab" with "[$Htok $Hbigsep $Hmauth $Hfrag $Hl]") as "Htok".
      { iNext. iFrame "%". }
      iModIntro. iExists None. by iFrame.
  Admitted.

  Lemma refines_instantiate (c1 c2 : expr) (τ : type _ ⋆) :
    (REL c1 << c2 : ⟦ ∀: ⋆ ⇒ ⋆; ⋆ ⇒ ⋆; ⋆ ⇒ ⋆, Authentikit_func var2 var1 var0 → var0 τ ⟧ ∅) -∗
    REL c1 #~ #~ #~ v_Authentikit
     << c2 #~ #~ #~ i_Authentikit : lrel_auth_comp (⟦ τ ⟧ (auth_ctx ∅)).
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
    iSpecialize ("Hcnt" $! lrel_hash_fail_option with "[//]").
    i_bind (v2 _).
    iSpecialize ("Hcnt" with "[$Hi $Htok]").
    wp_apply (wp_wand with "Hcnt").
    iIntros (v1') "(%v2' & Hi & Hcnt & Htok)".
    iSpecialize ("Hcnt" $! lrel_auth with "[//]").
    i_bind (v2' _).
    iSpecialize ("Hcnt" with "[$Hi $Htok]").
    wp_apply (wp_wand with "Hcnt").
    iIntros (v1'') "(%v2'' & Hi & Hcnt & Htok)".
    iSpecialize ("Hcnt" $! lrel_auth_comp with "[//]").
    i_bind (v2'' _).
    iSpecialize ("Hcnt" with "[$Hi $Htok]").
    wp_apply (wp_wand with "Hcnt").
    iIntros (v1''') "(%v2''' & Hi & Hcnt & Htok)".
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
  
Theorem authentikit_security Σ `{msizeG Σ, idcntrG Σ, stateG Σ, authPreG Σ, seqG Σ} (A : ∀ `{msizeG Σ, idcntrG Σ, stateG Σ, authG Σ, seqG Σ}, lrel Σ)
  (φ : val → val → Prop) (cᵥ cᵢ : expr) (σ : state) (l : list string) (prf : val) :
  (∀ `{msizeG Σ, idcntrG Σ, stateG Σ, authG Σ, seqG Σ}, ∀ vᵥ vᵢ, A vᵥ vᵢ -∗ ⌜φ vᵥ vᵢ⌝) →
  (∀ `{msizeG Σ, idcntrG Σ, stateG Σ, authG Σ, seqG Σ}, ⊢ REL cᵥ << cᵢ : lrel_auth_comp A) →
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

  wp_apply wp_fupd.
  wp_apply (wp_wand with "[-]").
  { iPoseProof (refines_run (seqG0 := Hseq) prf with "[] []") as "Hrun".
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
  ε |ₜ ∅ ⊢ₜ c : (∀: ⋆ ⇒ ⋆; ⋆ ⇒ ⋆; ⋆ ⇒ ⋆, Authentikit_func var2 var1 var0 → var0 τ) →
                is_list l prf →
                adequate hash_collision NotStuck (v_run #~ (c #~ #~ #~ v_Authentikit) prf) σ
                  (λ vᵥ σᵥ, ∃ thpᵢ σᵢ vᵢ o,
                      vᵥ = $o ∧
                        if o is Some wᵥ then
                          (** a valid ideal execution *)
                          rtc erased_step ([i_run #~ (c #~ #~ #~ i_Authentikit)], σ) (of_val vᵢ :: thpᵢ, σᵢ) ∧
                            (** and they return the same value *)
                            wᵥ = vᵢ
                        else True).
Proof.
  intros Hτ Htyped Hprf.
  set Σ := (#[authΣ; na_invΣ; GFunctor msizeUR; GFunctor idcntrUR; GFunctor stateUR]).
  eapply (authentikit_security Σ (λ _ _ _ _ _, ⟦ τ ⟧ (auth_ctx ∅))); [| |done].
  { iIntros (???????) "Hτ". by iDestruct (eq_type_sound with "Hτ") as %->. }
  iIntros (?????).
  iApply refines_instantiate.
  by iApply refines_typed.
Admitted.


             
