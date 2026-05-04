(** A resource algebra for [HeapLang] specification programs. *)
From iris.algebra Require Import auth excl gmap agree list dfrac.
From iris.bi Require Export fractional.
From iris.base_logic Require Export invariants.
From iris.proofmode Require Import proofmode.
From auth.heap_lang Require Import lang.
Import uPred.

Definition authN := nroot .@ "auth".
Definition specN := authN .@ "spec".

(** The CMRA for the heap and hashes of the specification. *)
Definition heapUR (L V : Type) `{Countable L} : ucmra :=
  gmapUR L (prodR dfracR (agreeR (leibnizO V))).
Definition tpoolUR : ucmra := gmapUR nat (exclR exprO).
Definition cfgUR := prodUR tpoolUR (heapUR loc (option val)).

(** The CMRA for the thread pool. *)
Class cfgSG Σ := CFGSG { cfg_inG :: inG Σ (authR cfgUR); cfg_name : gname }.

Definition to_heap {L V} `{Countable L} : gmap L V → heapUR L V :=
  fmap (λ v, (DfracOwn 1, to_agree (v : leibnizO V))).
Definition to_tpool (tp : list expr) : tpoolUR := Excl <$> (map_seq 0 tp).

Section definitionsS.
  Context `{cfgSG Σ, invGS Σ}.

  Definition cfg_auth_def (tp : list expr) (σ : state) : iProp Σ :=
    own cfg_name (● (to_tpool tp, to_heap σ.(heap))).
  Definition cfg_auth_aux : seal (@cfg_auth_def). by eexists. Qed.
  Definition cfg_auth := cfg_auth_aux.(unseal).
  Definition cfg_auth_eq :
    @cfg_auth = @cfg_auth_def := cfg_auth_aux.(seal_eq).

  Definition heapS_pointsto_def (l : loc) (q : dfrac) (v: val) : iProp Σ :=
    own cfg_name (◯ (∅, {[ l := (q, to_agree (Some v)) ]})).
  Definition heapS_pointsto_aux : seal (@heapS_pointsto_def). by eexists. Qed.
  Definition heapS_pointsto := heapS_pointsto_aux.(unseal).
  Definition heapS_pointsto_eq :
    @heapS_pointsto = @heapS_pointsto_def := heapS_pointsto_aux.(seal_eq).

  Definition tpool_pointsto_def (j : nat) (e: expr) : iProp Σ :=
    own cfg_name (◯ ({[ j := Excl e ]}, ∅)).
  Definition tpool_pointsto_aux : seal (@tpool_pointsto_def). by eexists. Qed.
  Definition tpool_pointsto := tpool_pointsto_aux.(unseal).
  Definition tpool_pointsto_eq :
    @tpool_pointsto = @tpool_pointsto_def := tpool_pointsto_aux.(seal_eq).

  Global Instance cfg_auth_timeless tp σ : Timeless (cfg_auth tp σ).
  Proof. rewrite cfg_auth_eq. apply _. Qed.
  Global Instance heapS_pointsto_timeless l q v : Timeless (heapS_pointsto l q v).
  Proof. rewrite heapS_pointsto_eq. apply _. Qed.
  Global Instance tpool_pointsto_timeless j e: Timeless (tpool_pointsto j e).
  Proof. rewrite tpool_pointsto_eq. apply _. Qed.

End definitionsS.

Section conversions.
  Context `{cfgSG Σ}.

  #[local] Notation "l ↦ₛ{ q } v" := (heapS_pointsto l q v)
    (at level 20, q at level 50, format "l  ↦ₛ{ q }  v") : bi_scope.
  #[local] Notation "l ↦ₛ{# q } v" := (heapS_pointsto l (DfracOwn q) v)
    (at level 20, q at level 50, format "l  ↦ₛ{# q }  v") : bi_scope.  
  #[local] Notation "l ↦ₛ v" := (heapS_pointsto l (DfracOwn 1) v) (at level 20) : bi_scope.
  #[local] Notation "j ⤇ e" := (tpool_pointsto j e) (at level 20) : bi_scope.

  Local Open Scope nat_scope.
  (** Conversion to tpools and back *)
  Lemma to_tpool_valid es : ✓ to_tpool es.
  Proof.
    rewrite /to_tpool. move: 0.
    induction es as [|e es]=> n /= //.
    rewrite fmap_insert. by apply insert_valid.
  Qed.

  Lemma tpool_lookup tp j : to_tpool tp !! j = Excl <$> tp !! j.
  Proof.
    unfold to_tpool. rewrite lookup_fmap.
    by rewrite lookup_map_seq_0.
  Qed.
  Lemma tpool_lookup_Some tp j e : to_tpool tp !! j = Excl' e → tp !! j = Some e.
  Proof. rewrite tpool_lookup fmap_Some. naive_solver. Qed.
  Hint Resolve tpool_lookup_Some : core.

  Lemma to_tpool_insert tp j e :
    j < length tp →
    to_tpool (<[j:=e]> tp) = <[j:=Excl e]> (to_tpool tp).
  Proof.
    intros. apply: map_eq=> i. destruct (decide (i = j)) as [->|].
    - by rewrite tpool_lookup lookup_insert list_lookup_insert.
    - rewrite tpool_lookup lookup_insert_ne // list_lookup_insert_ne //.
      by rewrite tpool_lookup.
  Qed.
  Lemma to_tpool_insert' tp j e :
    is_Some (to_tpool tp !! j) →
    to_tpool (<[j:=e]> tp) = <[j:=Excl e]> (to_tpool tp).
  Proof.
    rewrite tpool_lookup fmap_is_Some lookup_lt_is_Some. apply to_tpool_insert.
  Qed.
  Lemma to_tpool_snoc tp e :
    to_tpool (tp ++ [e]) = <[length tp:=Excl e]>(to_tpool tp).
  Proof.
    intros. apply: map_eq=> i.
    destruct (lt_eq_lt_dec i (length tp)) as [[?| ->]|?].
    - rewrite lookup_insert_ne; last lia. by rewrite !tpool_lookup lookup_app_l.
    - by rewrite lookup_insert tpool_lookup lookup_app_r // Nat.sub_diag.
    - rewrite lookup_insert_ne; last lia.
      rewrite !tpool_lookup ?lookup_ge_None_2 ?app_length //=;
         change (ofe_car exprO) with expr; lia.
  Qed.

  Lemma tpool_singleton_included tp j e :
    {[j := Excl e]} ≼ to_tpool tp → tp !! j = Some e.
  Proof.
    move=> /singleton_included_l [ex [/leibniz_equiv_iff]].
    rewrite tpool_lookup fmap_Some=> [[e' [-> ->]] /Excl_included ?]. by f_equal.
  Qed.
  Lemma tpool_singleton_included' tp j e :
    {[j := Excl e]} ≼ to_tpool tp → to_tpool tp !! j = Excl' e.
  Proof. rewrite tpool_lookup. by move=> /tpool_singleton_included=> ->. Qed.

End conversions.

Section to_heap.
  Context (L V : Type) `{Countable L}.
  Implicit Types σ : gmap L V.
  Implicit Types m : gmap L gname.

  Lemma lookup_to_heap_None σ l : σ !! l = None → to_heap σ !! l = None.
  Proof. by rewrite /to_heap lookup_fmap=> ->. Qed.
  Lemma to_heap_insert l v σ :
    to_heap (<[l:=v]> σ) = <[l:=(DfracOwn 1, to_agree (v:leibnizO V))]> (to_heap σ).
  Proof. by rewrite /to_heap fmap_insert. Qed.

  Lemma heap_singleton_included σ l q v :
    {[l := (q, to_agree v)]} ≼ to_heap σ → σ !! l = Some v.
  Proof.
    rewrite singleton_included_l=> -[[q' av] []].
    rewrite /to_heap lookup_fmap fmap_Some_equiv => -[v' [Hl [/= -> ->]]].
    move=> /Some_pair_included_total_2 [_] /to_agree_included /leibniz_equiv_iff -> //.
  Qed.

  Lemma to_heap_valid σ : ✓ to_heap σ.
  Proof. intros l. rewrite lookup_fmap. by case: (σ !! l). Qed.

End to_heap.

Section pointsto.
  Context `{!cfgSG Σ}.

  #[local] Notation "l ↦ₛ{ q } v" := (heapS_pointsto l q v)
    (at level 20, q at level 50, format "l  ↦ₛ{ q }  v") : bi_scope.
  #[local] Notation "l ↦ₛ{# q } v" := (heapS_pointsto l (DfracOwn q) v)
    (at level 20, q at level 50, format "l  ↦ₛ{# q }  v") : bi_scope.  
  #[local] Notation "l ↦ₛ v" := (heapS_pointsto l (DfracOwn 1) v) (at level 20) : bi_scope.
  #[local] Notation "j ⤇ e" := (tpool_pointsto j e) (at level 20) : bi_scope.
 
  Global Instance pointstoS_fractional l v : Fractional (λ q, l ↦ₛ{# q} v)%I.
  Proof.
    intros p q. rewrite heapS_pointsto_eq -own_op -auth_frag_op.
    by rewrite -!pair_op singleton_op -pair_op agree_idemp right_id.
  Qed.
  Global Instance pointstoS_as_fractional l q v :
    AsFractional (l ↦ₛ{# q} v) (λ q, l ↦ₛ{# q} v)%I q.
  Proof. split. done. apply _. Qed.
  Global Instance frame_pointstoS p l v q1 q2 q :
    FrameFractionalQp q1 q2 q →
    Frame p (l ↦ₛ{# q1} v) (l ↦ₛ{# q2} v) (l ↦ₛ{# q} v) | 5.
  Proof. apply: frame_fractional. Qed.

  
  Lemma pointstoS_agree l dq1 dq2 v1 v2 : l ↦ₛ{dq1} v1 -∗ l ↦ₛ{dq2} v2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
  Proof.
    apply bi.entails_wand, bi.wand_intro_r.
    rewrite heapS_pointsto_eq -own_op -auth_frag_op own_valid uPred.discrete_valid.
    f_equiv=> /=.
    rewrite -!pair_op singleton_op right_id -!pair_op.
    rewrite auth_frag_valid.
    intros [_ Hv]. move:Hv => /=.
    rewrite singleton_valid.
    rewrite pair_valid.
    by move=> [? -] /to_agree_op_inv_L [->].
  Qed.

  Lemma pointstoS_valid l q v : l ↦ₛ{q} v -∗ ✓ q.
  Proof.
    rewrite heapS_pointsto_eq /heapS_pointsto_def own_valid !uPred.discrete_valid.
    apply bi.entails_wand, pure_mono=> /auth_frag_valid /= [_ Hfoo].
    revert Hfoo. simpl. rewrite singleton_valid.
    by intros [? _].
  Qed.

  Lemma pointstoS_valid_2 l q1 q2 v1 v2 : l ↦ₛ{q1} v1 -∗ l ↦ₛ{q2} v2 -∗ ✓ (q1 ⋅ q2).
  Proof. iIntros "H1 H2". by iDestruct (pointstoS_agree with "H1 H2") as "[% %]". Qed. 

  Global Instance pointstoS_combine_sep_gives l dq1 dq2 v1 v2 :
    CombineSepGives (l ↦ₛ{dq1} v1) (l ↦ₛ{dq2} v2) ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
  Proof.
    rewrite /CombineSepGives. iIntros "[H1 H2]". iSplit.
    - iDestruct (pointstoS_valid_2 with "H1 H2") as %?; auto.
    - iDestruct (pointstoS_agree with "H1 H2") as %[? ?]; auto.
  Qed.

  Lemma pointstoS_half_combine l v1 v2 :
    l ↦ₛ{#1/2} v1 -∗ l ↦ₛ{#1/2} v2 -∗ ⌜v1 = v2⌝ ∗ l ↦ₛ v1.
  Proof.
    iIntros "Hl1 Hl2".
    iDestruct (pointstoS_agree with "Hl1 Hl2") as %[? ->]. 
    by iCombine "Hl1 Hl2" as "$".
  Qed.

End pointsto.

#[local] Notation "l ↦ₛ{ q } v" := (heapS_pointsto l q v)
  (at level 20, q at level 50, format "l  ↦ₛ{ q }  v") : bi_scope.
#[local] Notation "l ↦ₛ{# q } v" := (heapS_pointsto l (DfracOwn q) v)
  (at level 20, q at level 50, format "l  ↦ₛ{# q }  v") : bi_scope.
#[local] Notation "l ↦ₛ v" := (heapS_pointsto l (DfracOwn 1) v) (at level 20) : bi_scope.
#[local] Notation "j ⤇ e" := (tpool_pointsto j e) (at level 20) : bi_scope.

Section cfg_auth.
  Context `{!cfgSG Σ}.

  Lemma cfg_auth_heap_agree tp σ l q v :
    cfg_auth tp σ -∗ l ↦ₛ{ q } v -∗ ⌜σ.(heap) !! l = Some $ Some v⌝.
  Proof.
    iIntros "Hauth Hl".
    rewrite cfg_auth_eq /cfg_auth_def heapS_pointsto_eq /heapS_pointsto_def.
    iCombine "Hauth Hl" as "H".
    iDestruct (own_valid with "H") as
      %[[_ ?%heap_singleton_included]%pair_included _]%auth_both_valid_discrete.
    done.
  Qed.

  Lemma cfg_auth_heap_alloc tp σ v :
    cfg_auth tp σ ==∗ ∃ l, ⌜σ.(heap) !! l = None⌝ ∗ cfg_auth tp (state_upd_heap <[l:=Some v]> σ) ∗ l ↦ₛ v.
  Proof.
    iIntros "Hauth".
    rewrite cfg_auth_eq /cfg_auth_def heapS_pointsto_eq /heapS_pointsto_def.
    destruct (exist_fresh (dom (heap σ))) as [l Hl%not_elem_of_dom].
    iMod (own_update with "Hauth") as "[Hauth Hl]".
    { apply auth_update_alloc, prod_local_update_2.
      rewrite /to_heap /=.
      apply (alloc_singleton_local_update _ l (DfracOwn 1%Qp, to_agree (Some v : leibnizO _))); [|done].
      by apply lookup_to_heap_None. }
    rewrite /to_heap /state_upd_heap /=.
    iFrame; iFrame "%".
    rewrite fmap_insert //.
  Qed.

  Lemma cfg_auth_heap_update tp σ l v w :
    cfg_auth tp σ -∗ l ↦ₛ v ==∗ cfg_auth tp (state_upd_heap <[l:=Some w]> σ) ∗ l ↦ₛ w.
  Proof.
    iIntros "Hauth Hl".
    iDestruct (cfg_auth_heap_agree with "Hauth Hl") as %Hl.
    rewrite cfg_auth_eq /cfg_auth_def heapS_pointsto_eq /heapS_pointsto_def.
    iMod (own_update_2 with "Hauth Hl") as "[Hauth Hl]".
    { eapply auth_update, prod_local_update_2.
      apply: singleton_local_update.
      { rewrite /to_heap lookup_fmap Hl //. }
      apply: (exclusive_local_update _ (DfracOwn 1%Qp, to_agree (Some w : leibnizO (option val))));
        [|done].
      apply: pair_exclusive_l. }
    rewrite /to_heap fmap_insert.
    by iFrame.
  Qed.

  Lemma cfg_auth_prophs_update tp σ p :
    cfg_auth tp σ ≡ cfg_auth tp (state_upd_used_proph_id ({[ p ]} ∪.) σ).
  Proof. rewrite cfg_auth_eq /cfg_auth_def //. Qed.

  Lemma cfg_auth_tpool_agree tp σ j e :
    cfg_auth tp σ -∗ j ⤇ e -∗ ⌜tp !! j = Some e⌝.
  Proof.
    iIntros "Hauth Htpool".
    rewrite cfg_auth_eq /cfg_auth_def tpool_pointsto_eq /tpool_pointsto_def.
    iCombine "Hauth Htpool" as "H".
    iDestruct (own_valid with "H") as
      %[[?%tpool_singleton_included _]%pair_included _]%auth_both_valid_discrete.
    done.
  Qed.

  Lemma cfg_auth_tpool_update tp σ j e e' :
    cfg_auth tp σ -∗ j ⤇ e ==∗ cfg_auth (<[j := e']> tp) σ ∗ j ⤇ e'.
  Proof.
    iIntros "Hauth Htpool".
    iDestruct (cfg_auth_tpool_agree with "Hauth Htpool") as %?.
    rewrite cfg_auth_eq /cfg_auth_def tpool_pointsto_eq /tpool_pointsto_def.
    iMod (own_update_2 with "Hauth Htpool") as "[Hauth Htpool]".
    { apply auth_update, prod_local_update_1.
      eapply singleton_local_update, (exclusive_local_update _ (Excl (e'))); [|done].
      rewrite tpool_lookup H //. }
    iFrame.
    rewrite to_tpool_insert' //.
    eexists. rewrite tpool_lookup H //.
  Qed.

  Lemma cfg_auth_tpool_fork tp σ e :
    cfg_auth tp σ ==∗ cfg_auth (tp ++ [e]) σ ∗ (length tp) ⤇ e.
  Proof.
    iIntros "Hauth".
    rewrite cfg_auth_eq /cfg_auth_def tpool_pointsto_eq /tpool_pointsto_def.
    iMod (own_update with "Hauth") as "[Hauth Hj]".
    { eapply auth_update_alloc, prod_local_update_1.
      eapply (alloc_singleton_local_update _ (length tp) (Excl e)); [|done].
      rewrite tpool_lookup lookup_ge_None_2 //. }
    iFrame. rewrite -to_tpool_snoc //.
  Qed.

  Lemma cfg_auth_hash_update tp σ s :
    cfg_auth tp σ ==∗ cfg_auth tp (state_upd_hashed_strings ({[ s ]} ∪.) σ).
  Proof. iIntros "Hauth". rewrite cfg_auth_eq /cfg_auth_def //. Qed.

End cfg_auth.

Lemma cfg_alloc `{!inG Σ (authR cfgUR)} e σ :
  ⊢ |==> ∃ _ : cfgSG Σ, (cfg_auth [e] σ ∗ 0 ⤇ e)%I.
Proof.
  iMod (own_alloc (● (to_tpool [e], to_heap (heap σ))
    ⋅ ◯ ((to_tpool [e] : tpoolUR, ∅) : cfgUR)))
    as (γc) "[Hcfg1 Hcfg2]".
  { apply auth_both_valid_discrete. split=>//.
    - apply prod_included.
      split=>///=.
      apply: ucmra_unit_least.
    - split=>//=; [apply to_tpool_valid|]. apply to_heap_valid. }
  set (Hcfg := CFGSG _ _ γc).
  iExists _.
  rewrite cfg_auth_eq /cfg_auth_def /= tpool_pointsto_eq /tpool_pointsto_def.
  by iFrame.
Qed.
