From auth.prelude Require Import stdpp.
From auth.rel_logic_tern_susp Require Export model spec_rules.
From iris.algebra Require Import gmap auth excl gset csum frac reservation_map.
From iris.algebra.lib Require Import dfrac_agree.
From iris.base_logic.lib Require Import ghost_map gen_heap.


(* Nat is going to be the id assigned by the verifier. We are going to show that
  for some value in the verifier's map, the ctr must be > 0. These values are either
  yet to be seen or are in the map. visit_done denotes values have been seen.
  In the end we will say that for the highest id value in the map all values must
  have been seen (because of flush_buf_stream), and since this is the highest
  id, and children's ids are higher, we have a contradiction. *)
Definition visited_state_mapUR :=
  authUR (gmap gname (csumR (exclR (optionO natO)) (agreeR natO))).
Definition visited_done_mapUR :=
  authUR (gmap gname (agreeR natO)).
Definition pending_setUR :=
  authUR (gset_disjUR gname).
Definition pendingnUR := dfrac_agreeR natO.
Definition pending_idUR :=
  authUR (gset_disjUR nat).
Class visited_mapG Σ := VisitedMapG {
  visited_state_inG :> inG Σ visited_state_mapUR;
  visited_done_inG :> inG Σ visited_done_mapUR;
  pending_set_inG :> inG Σ pending_setUR;
  pendingn_inG :> inG Σ pendingnUR;
  pending_id_inG :> inG Σ pending_idUR;
  visited_state_name : gname;
  visited_done_name : gname;
  pending_set_name : gname;
  pendingnG_name : gname;
  pending_id_name : gname;
}.

Section visited_map_res.
  Context `{!visited_mapG Σ}.

  Definition state_val_type := csumR (exclR (optionO natO)) (agreeR natO).
  Definition state_mapg_type := gmap gname state_val_type.
  Definition done_mapg_type := gmap gname (agreeR natO).
  Definition pending_setg_type := gset gname.

  Definition pencount_frag (pn : nat) : iProp Σ :=
    own pendingnG_name (to_dfrac_agree (DfracOwn (1/2)) pn).

  Definition pending_val : state_val_type :=
    Cinl (Excl None).

  Definition done_val n : state_val_type :=
    Cinl (Excl (Some n)).

  Definition finished_val n : state_val_type :=
    Cinr (to_agree n).

  Definition penset_frag (γs : gset gname) : iProp Σ :=
    own pending_set_name (◯ GSet γs).

  Definition visited_coherent (m : state_mapg_type) (d : done_mapg_type) : Prop :=
    ∀ γ, d !! γ ≠ None →
      ∃ n, m !! γ = Some (done_val n) ∨ m !! γ = Some (finished_val n).

  (** [done_id_coherent m d] strengthens [visited_coherent] by linking the
      id-tag in [d] to the id-tag in [m]. Used in
      [id_token_visit_reached_done_invalid] to derive the matching id from
      a [visit_reached_done γ id] fragment. *)
  Definition done_id_coherent (m : state_mapg_type) (d : done_mapg_type) : Prop :=
    ∀ γ n, d !! γ ≡ Some (to_agree n) →
      m !! γ = Some (done_val n) ∨ m !! γ = Some (finished_val n).

  Definition pending_coherent (m : state_mapg_type) (ps : pending_setg_type) (pending_n : nat) : Prop :=
    pending_n = size ps ∧
      ∀ γ, m !! γ = Some pending_val → γ ∈ ps.

  (** [B] is the bag of [id]s already consumed by [visited_transition_done]
      — the codomain of [d] is contained in [B]. The bag fragment
      [own pending_id_name (◯ GSet B)] held inside the auth makes the
      free [id_token id] tokens disjoint from [B] (and hence from the
      done/finished entries of [m]). *)
  Definition visited_mapg_auth (m : state_mapg_type) (d : done_mapg_type)
      (ps : pending_setg_type) (pending_n : nat) (B : gset nat) : iProp Σ :=
    own visited_state_name (● m) ∗ own visited_done_name (● d) ∗
    own pending_set_name (● GSet ps) ∗ pencount_frag pending_n ∗
    own pending_id_name (◯ GSet B) ∗
    ⌜∀ γ n, m !! γ = Some (done_val n) ∨ m !! γ = Some (finished_val n) → n ∈ B⌝ ∗
    ⌜done_id_coherent m d⌝ ∗
    ⌜visited_coherent m d⌝ ∗ ⌜pending_coherent m ps pending_n⌝.

  Definition visited_map_update_pending
      (m : state_mapg_type) (d : done_mapg_type) (ps : pending_setg_type) pn (γs : gset gname) (B : gset nat) : iProp Σ :=
    let m' := set_fold (λ γ m, <[ γ := pending_val ]>m) m γs in
    let ps' := ps ∪ γs in
    own visited_state_name (● m') ∗
    own visited_done_name (● d) ∗
    own pending_set_name (● GSet ps') ∗ pencount_frag (pn + size γs) ∗
    own pending_id_name (◯ GSet B) ∗
    ⌜∀ γ n, m' !! γ = Some (done_val n) ∨ m' !! γ = Some (finished_val n) → n ∈ B⌝ ∗
    ⌜done_id_coherent m' d⌝ ∗
    ⌜visited_coherent m' d⌝ ∗
    ⌜pending_coherent m' ps' (pn + size γs)⌝.

  Definition visited_map_update_done
      (m : state_mapg_type) (d : done_mapg_type) (ps : pending_setg_type) pn γ n (B : gset nat) : iProp Σ :=
    own visited_state_name (● <[ γ := done_val n ]>m) ∗
    own visited_done_name (● <[ γ := to_agree n ]>d) ∗
    own pending_set_name (● GSet ps) ∗ pencount_frag pn ∗
    own pending_id_name (◯ GSet (B ∪ {[n]})) ∗
    ⌜∀ γ' n', <[ γ := done_val n ]>m !! γ' = Some (done_val n') ∨ <[ γ := done_val n ]>m !! γ' = Some (finished_val n') → n' ∈ B ∪ {[n]}⌝ ∗
    ⌜done_id_coherent (<[ γ := done_val n ]>m) (<[ γ := to_agree n ]>d)⌝ ∗
    ⌜visited_coherent (<[ γ := done_val n ]>m) (<[ γ := to_agree n ]>d)⌝ ∗
    ⌜pending_coherent (<[ γ := done_val n ]>m) ps pn⌝.

  Definition visited_map_update_finished
      (m : state_mapg_type) (d : done_mapg_type) (ps : pending_setg_type) pn γ n (B : gset nat) : iProp Σ :=
    own visited_state_name (● <[ γ := finished_val n ]>m) ∗
    own visited_done_name (● d) ∗
    own pending_set_name (● GSet ps) ∗ pencount_frag pn ∗
    own pending_id_name (◯ GSet B) ∗
    ⌜∀ γ' n', <[ γ := finished_val n ]>m !! γ' = Some (done_val n') ∨ <[ γ := finished_val n ]>m !! γ' = Some (finished_val n') → n' ∈ B⌝ ∗
    ⌜done_id_coherent (<[ γ := finished_val n ]>m) d⌝ ∗
    ⌜visited_coherent (<[ γ := finished_val n ]>m) d⌝ ∗
    ⌜pending_coherent (<[ γ := finished_val n ]>m) ps pn⌝.

  Definition visited_mapg_pending_removed (m : state_mapg_type) (d : done_mapg_type) (ps : pending_setg_type) (pending_n : nat) (γs : gset gname) (B : gset nat) : iProp Σ :=
    own visited_state_name (● m) ∗ own visited_done_name (● d) ∗
    own pending_set_name (● GSet (ps ∖ γs)) ∗ pencount_frag (pending_n - size γs) ∗
    own pending_id_name (◯ GSet B) ∗
    ⌜∀ γ n, m !! γ = Some (done_val n) ∨ m !! γ = Some (finished_val n) → n ∈ B⌝ ∗
    ⌜done_id_coherent m d⌝ ∗
    ⌜visited_coherent m d⌝ ∗
    ⌜pending_coherent m (ps ∖ γs) (pending_n - size γs)⌝.

  Lemma visited_map_update_pending_rewrite m d ps pn γs B:
    visited_map_update_pending m d ps pn γs B ⊣⊢
    visited_mapg_auth (set_fold (λ γ m, <[ γ := pending_val ]>m) m γs) d (ps ∪ γs) (pn + size γs) B.
  Proof. rewrite /visited_map_update_pending /visited_mapg_auth. done. Qed.

  Lemma visited_map_update_done_rewrite m d ps pn γ n B:
    visited_map_update_done m d ps pn γ n B ⊣⊢
    visited_mapg_auth (<[ γ := done_val n ]>m) (<[ γ := to_agree n ]>d) ps pn (B ∪ {[n]}).
  Proof. rewrite /visited_map_update_done /visited_mapg_auth. done. Qed.

  Lemma visited_map_update_finished_rewrite m d ps pn γ n B:
    visited_map_update_finished m d ps pn γ n B ⊣⊢
    visited_mapg_auth (<[ γ := finished_val n ]>m) d ps pn B.
  Proof. rewrite /visited_map_update_finished /visited_mapg_auth. done. Qed.

  Lemma visited_mapg_pending_remove_rewrite m d ps pn γs B:
    visited_mapg_pending_removed m d ps pn γs B ⊣⊢ visited_mapg_auth m d (ps ∖ γs) (pn - size γs) B.
  Proof. rewrite /visited_mapg_pending_removed /visited_mapg_auth. done. Qed.

  Definition visit_pending γ : iProp Σ :=
    own visited_state_name (◯ {[ γ := pending_val ]}).

  Definition visit_reached_done γ n : iProp Σ :=
    own visited_done_name (◯ {[ γ := to_agree n ]}).

  Definition visit_done γ n : iProp Σ :=
    own visited_state_name (◯ {[ γ := done_val n ]}) ∗ visit_reached_done γ n.

  Definition visit_finished γ n : iProp Σ :=
    own visited_state_name (◯ {[ γ := finished_val n ]}) ∗ visit_reached_done γ n.

  Global Instance visit_reached_done_persistent γ n :
    Persistent (visit_reached_done γ n).
  Proof. rewrite /visit_reached_done. apply _. Qed.

  Global Instance visit_finished_persistent γ n :
    Persistent (visit_finished γ n).
  Proof. rewrite /visit_finished /finished_val. apply _. Qed.

  Lemma pn_agree pn pn' :
    pencount_frag pn -∗ pencount_frag pn' -∗ ⌜pn = pn'⌝ ∗ pencount_frag pn ∗ pencount_frag pn'.
  Proof.
    iIntros "H1 H2". rewrite /pencount_frag. iCombine "H1 H2" as "H".
    iDestruct (own_valid with "H") as %Hv%dfrac_agree_op_valid_L.
    destruct Hv as [_ ->].
    iDestruct "H" as "[H1 H2]". by iFrame.
  Qed.

  Lemma pn_update pn pn' :
    pencount_frag pn -∗ pencount_frag pn ==∗ pencount_frag pn' ∗ pencount_frag pn'.
  Proof.
    iIntros "H1 H2". rewrite /pencount_frag. iCombine "H1 H2" as "H".
    iMod (own_update with "H") as "[H1 H2]"; last by iFrame.
    apply frac_agree_update_2. by rewrite Qp.half_half.
  Qed.

  (** Pointwise Leibniz: [done_val n] and [finished_val n] involve no [agreeR]
      components, so any [s ≡ done_val n] (resp. [finished_val n]) gives
      Leibniz equality. Used to bridge [singleton_included_exclusive_l]'s
      [≡] result to the [=] expected by the bag-coherence invariant. *)
  Local Lemma done_val_equiv_eq (s : state_val_type) (n : nat) :
    s ≡ done_val n → s = done_val n.
  Proof.
    rewrite /done_val. destruct s as [s'| |]; intros Heq;
      [|by inversion Heq|by inversion Heq].
    apply (inj Cinl) in Heq. destruct s' as [v|];
      [|by inversion Heq].
    apply (inj Excl) in Heq. apply leibniz_equiv in Heq.
    by subst.
  Qed.

  Local Lemma some_done_val_equiv_eq (x : option state_val_type) (n : nat) :
    x ≡ Some (done_val n) → x = Some (done_val n).
  Proof.
    intros Heq. destruct x as [s|]; [|by inversion Heq].
    apply Some_equiv_inj in Heq. by rewrite (done_val_equiv_eq _ _ Heq).
  Qed.

  (** [id_ctr_frag ctr] is a half-share of the [pending_id_name] authority at
      universe [{0,..,ctr-1}]. Two halves combine to give the full authority
      and agree on [ctr]. Mirrors the old [id_frag] from [idcntr]. *)
  Definition id_ctr_frag (ctr : nat) : iProp Σ :=
    own pending_id_name (●{DfracOwn (1/2)} GSet (set_seq 0 ctr)).

  (** [id_token id] is an exclusive token witnessing that [id] has been
      issued but not yet consumed by [visited_transition_done]. Mirrors the
      [vmeta_token l] pattern from [spec_rules.v]. *)
  Definition id_token (id : nat) : iProp Σ :=
    own pending_id_name (◯ GSet {[id]}).

  Global Instance id_token_timeless id : Timeless (id_token id).
  Proof. apply _. Qed.

  Global Instance id_ctr_frag_timeless ctr : Timeless (id_ctr_frag ctr).
  Proof. apply _. Qed.

  Lemma id_token_ne id1 id2 :
    id_token id1 -∗ id_token id2 -∗ ⌜id1 ≠ id2⌝.
  Proof.
    rewrite /id_token. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    rewrite auth_frag_op_valid gset_disj_valid_op in Hv.
    iPureIntro. set_solver.
  Qed.

  Lemma id_token_excl id : id_token id -∗ id_token id -∗ False.
  Proof.
    iIntros "H1 H2".
    by iDestruct (id_token_ne with "H1 H2") as %?.
  Qed.

  Lemma id_ctr_frag_agree ctr ctr' :
    id_ctr_frag ctr -∗ id_ctr_frag ctr' -∗
      ⌜ctr = ctr'⌝ ∗ id_ctr_frag ctr ∗ id_ctr_frag ctr'.
  Proof.
    rewrite /id_ctr_frag. iIntros "H1 H2". iCombine "H1 H2" as "H".
    iDestruct (own_valid with "H") as %Hv.
    apply auth_auth_dfrac_op_valid in Hv as [_ [Heq _]].
    iDestruct "H" as "[H1 H2]". iFrame. iPureIntro.
    apply leibniz_equiv in Heq. injection Heq as Heq.
    apply (f_equal size) in Heq.
    rewrite !size_set_seq in Heq. exact Heq.
  Qed.

  Lemma id_ctr_frag_alloc ctr :
    id_ctr_frag ctr -∗ id_ctr_frag ctr ==∗
      id_ctr_frag (S ctr) ∗ id_ctr_frag (S ctr) ∗ id_token ctr.
  Proof.
    rewrite /id_ctr_frag /id_token. iIntros "H1 H2".
    iCombine "H1 H2" as "H".
    iMod (own_update _ _
      (●{DfracOwn (1/2)} (GSet (set_seq 0 (S ctr)))
       ⋅ ●{DfracOwn (1/2)} (GSet (set_seq 0 (S ctr)))
       ⋅ ◯ GSet {[ctr]})
      with "H") as "[[$ $] $]"; last done.
    rewrite -auth_auth_dfrac_op dfrac_op_own Qp.half_half.
    rewrite (set_seq_S_end_union_L 0 ctr) Nat.add_0_l.
    apply auth_update_alloc, gset_disj_alloc_empty_local_update.
    apply disjoint_singleton_l. intros ?%elem_of_set_seq. lia.
  Qed.

  Lemma id_token_lt_ctr ctr id :
    id_ctr_frag ctr -∗ id_ctr_frag ctr -∗ id_token id -∗
      ⌜id < ctr⌝ ∗ id_ctr_frag ctr ∗ id_ctr_frag ctr ∗ id_token id.
  Proof.
    rewrite /id_ctr_frag /id_token. iIntros "H1 H2 Htok".
    iDestruct (own_valid_2 with "H1 Htok") as %Hv.
    iFrame. iPureIntro.
    apply auth_both_dfrac_valid_discrete in Hv as (_ & Hincl & _).
    apply gset_disj_included, singleton_subseteq_l, elem_of_set_seq in Hincl. lia.
  Qed.

  Lemma visited_insert m d ps pn B :
    visited_mapg_auth m d ps pn B ∗ pencount_frag pn ==∗
      ∃ γ,
        visited_map_update_pending m d ps pn {[γ]} B ∗ pencount_frag (pn+1) ∗
          visit_pending γ ∗ penset_frag {[γ]}.
  Proof.
    iIntros "((Hms & Hd & Hps & Hpn1 & Hbag & %HBcoh & %Hdid & %Hcoh & %Hpcoh) & Hpn2)".
    set (γ := fresh (dom m ∪ ps)).
    assert (γ ∉ (dom m ∪ ps : gset gname)) as Hfr by apply is_fresh.
    rewrite not_elem_of_union in Hfr.
    destruct Hfr as [Hfm%not_elem_of_dom Hfps].
    iMod (own_update _ _
      (● <[γ := pending_val]>m ⋅ ◯ {[γ := pending_val]})
      with "Hms") as "[Hms' Hp]".
    { apply auth_update_alloc, alloc_singleton_local_update; done. }
    iMod (own_update _ _ (● GSet ({[γ]} ∪ ps) ⋅ ◯ GSet {[γ]}) with "Hps") as "[Hps' Hpsf]".
    { apply auth_update_alloc, gset_disj_alloc_empty_local_update. set_solver. }
    iMod (pn_update pn (pn+1) with "Hpn1 Hpn2") as "[Hpn1 Hpn2]".
    iModIntro. iExists γ.
    rewrite /visited_map_update_pending /visit_pending /penset_frag.
    rewrite set_fold_singleton size_singleton (union_comm_L ps {[γ]}) /=.
    iFrame "Hms' Hd Hps' Hpn1 Hp Hpsf Hpn2 Hbag".
    iPureIntro. split; last split; last split.
    - intros γ' n' Hmγ'.
      destruct Hmγ' as [Hmγ' | Hmγ'];
        apply lookup_insert_Some in Hmγ' as [[<- Heq]|[Hne Hm']].
      + by inversion Heq.
      + apply (HBcoh γ' n'). by left.
      + by inversion Heq.
      + apply (HBcoh γ' n'). by right.
    - intros γ' n' Hdγ'. destruct (decide (γ' = γ)) as [-> | Hne].
      + exfalso. specialize (Hdid γ n' Hdγ').
        destruct Hdid as [Hmγ | Hmγ]; rewrite Hfm in Hmγ; discriminate.
      + destruct (Hdid γ' n' Hdγ') as [Hmγ | Hmγ];
          [left|right]; rewrite lookup_insert_ne; done.
    - intros γ' Hdγ'. destruct (decide (γ' = γ)) as [-> | Hne].
      + destruct (Hcoh γ Hdγ') as (n & [Heq | Heq]); rewrite Hfm in Heq; discriminate.
      + rewrite lookup_insert_ne; [|done]. by apply Hcoh.
    - destruct Hpcoh as [Hsize Hl]. split.
      + rewrite size_union; last set_solver. rewrite size_singleton. lia.
      + intros γ' Hγ'. destruct (decide (γ' = γ)) as [-> | Hne].
        * set_solver.
        * rewrite lookup_insert_ne in Hγ'; [|done].
          apply elem_of_union; right. by apply Hl.
  Qed.

  Lemma visited_transition_done m d ps pn B γ n :
    d !! γ = None →
    visited_mapg_auth m d ps pn B -∗ visit_pending γ -∗ id_token n
    ==∗ visited_map_update_done m d ps pn γ n B ∗ visit_done γ n.
  Proof.
    iIntros (Hdγ) "(Hms & Hd & Hps & Hpn & Hbag & %HBcoh & %Hdid & %Hcoh & %Hpcoh) H1 Htok".
    rewrite /visited_map_update_done /visit_done /visit_reached_done /id_token.
    iMod (own_update_2 _ _ _
      (● <[γ := done_val n]>m ⋅ ◯ {[γ := done_val n]})
      with "Hms H1") as "[$ Hf]".
    { apply auth_update, singleton_local_update_any.
      intros x Hx. unfold pending_val.
      apply (exclusive_local_update _ (done_val n)). done. }
    iMod (own_update _ _
      (● <[γ := to_agree n]>d ⋅ ◯ {[γ := to_agree n]})
      with "Hd") as "[$ #$]".
    { apply auth_update_alloc, alloc_singleton_local_update; done. }
    (* Combine the bag with the consumed token; validity gives B ## {[n]}. *)
    iDestruct (own_valid_2 with "Hbag Htok") as %Hv.
    rewrite auth_frag_op_valid gset_disj_valid_op in Hv.
    iAssert (own pending_id_name (◯ GSet (B ∪ {[n]})))%I with "[Hbag Htok]" as "Hbag'".
    { rewrite -gset_disj_union // auth_frag_op own_op. iFrame. }
    iModIntro.
    iFrame "Hps Hpn Hf Hbag'". iPureIntro. split; last split; last split.
    - intros γ' n' Hmγ'.
      destruct Hmγ' as [Hmγ' | Hmγ'];
        apply lookup_insert_Some in Hmγ' as [[<- Heq]|[Hne Hm']].
      + inversion Heq. set_solver.
      + specialize (HBcoh γ' n' (or_introl Hm')). set_solver.
      + by inversion Heq.
      + specialize (HBcoh γ' n' (or_intror Hm')). set_solver.
    - intros γ' n' Hdγ'.
      destruct (decide (γ' = γ)) as [-> | Hne].
      + rewrite lookup_insert in Hdγ'.
        apply Some_equiv_inj, (inj to_agree) in Hdγ'.
        fold_leibniz. subst n'. left. by rewrite lookup_insert.
      + rewrite lookup_insert_ne in Hdγ'; [|done].
        destruct (Hdid γ' n' Hdγ') as [Hmγ | Hmγ];
          [left|right]; rewrite lookup_insert_ne; done.
    - intros γ' Hdγ'. destruct (decide (γ' = γ)) as [-> | Hne].
      + exists n. left. by rewrite lookup_insert.
      + rewrite lookup_insert_ne; [|done]. apply Hcoh.
        rewrite lookup_insert_ne in Hdγ'; done.
    - destruct Hpcoh as [Hsize Hl]. split; [exact Hsize|].
      intros γ' Hγ'. destruct (decide (γ' = γ)) as [-> | Hne].
      + exfalso. rewrite lookup_insert in Hγ'.
        rewrite /done_val /pending_val in Hγ'.
        by inversion Hγ'.
      + rewrite lookup_insert_ne in Hγ'; [|done]. by apply Hl.
  Qed.

  Lemma visited_transition_finished m d ps pn B γ n :
    visited_mapg_auth m d ps pn B -∗ visit_done γ n
    ==∗ visited_map_update_finished m d ps pn γ n B ∗ visit_finished γ n.
  Proof.
    iIntros "(Hms & Hd & Hps & Hpn & Hbag & %HBcoh & %Hdid & %Hcoh & %Hpcoh) [Hsfrag #Hreached]".
    rewrite /visited_map_update_finished /visit_finished /visit_reached_done.
    (* Derive m !! γ = Some (done_val n) from Hms ⋅ Hsfrag, using exclusivity of done_val. *)
    iDestruct (own_valid_2 with "Hms Hsfrag") as %Hvm.
    apply auth_both_valid_discrete in Hvm as [Hinclm Hvalidm].
    apply (singleton_included_exclusive_l m γ (done_val n)) in Hinclm; [|apply _|done].
    apply some_done_val_equiv_eq in Hinclm.
    (* Hinclm : m !! γ = Some (done_val n) *)
    iDestruct (own_valid_2 with "Hd Hreached") as %Hv.
    apply auth_both_valid_discrete in Hv as [Hincl _].
    apply singleton_included_l in Hincl as (xd & Hxd & _).
    assert (d !! γ ≠ None) as Hdγ.
    { intros Heq. rewrite Heq in Hxd. inversion Hxd. }
    iMod (own_update_2 _ _ _
      (● <[γ := finished_val n]>m ⋅ ◯ {[γ := finished_val n]})
      with "Hms Hsfrag") as "[$ $]".
    { apply auth_update, singleton_local_update_any.
      intros x Hx. unfold done_val.
      apply (exclusive_local_update _ (finished_val n)). done. }
    iFrame "Hd Hps Hpn Hreached Hbag". iPureIntro.
    assert (n ∈ B) as HnB by (apply (HBcoh γ n); by left).
    split; last split; last split.
    - intros γ' n' Hmγ'.
      destruct Hmγ' as [Hmγ' | Hmγ'];
        apply lookup_insert_Some in Hmγ' as [[<- Heq]|[Hne Hm']].
      + by inversion Heq.
      + specialize (HBcoh γ' n' (or_introl Hm')). exact HBcoh.
      + inversion Heq. by subst.
      + specialize (HBcoh γ' n' (or_intror Hm')). exact HBcoh.
    - intros γ' n' Hdγ'.
      destruct (decide (γ' = γ)) as [-> | Hne].
      + (* d unchanged at γ. m'[γ] = finished_val n. Need m[γ] = done_val n_old where
           Hdγ' : d[γ] ≡ Some (to_agree n'). Old Hdid γ n' gives m[γ] is done/finished n'.
           We also know m[γ] = done_val n (from Hinclm). So done_val n is either
           done_val n' or finished_val n', the latter impossible. Hence n = n'. *)
        specialize (Hdid γ n' Hdγ').
        rewrite Hinclm in Hdid. destruct Hdid as [Heq | Heq]; inversion Heq as [Heqn].
        subst n. right. by rewrite lookup_insert.
      + rewrite lookup_insert_ne; [|done].
        destruct (Hdid γ' n' Hdγ') as [Hmγ | Hmγ]; [by left|by right].
    - intros γ' Hdγ'. destruct (decide (γ' = γ)) as [-> | Hne].
      + exists n. right. by rewrite lookup_insert.
      + rewrite lookup_insert_ne; [|done]. by apply Hcoh.
    - destruct Hpcoh as [Hsize Hl]. split; [exact Hsize|].
      intros γ' Hγ'. destruct (decide (γ' = γ)) as [-> | Hne].
      + exfalso. rewrite lookup_insert in Hγ'.
        rewrite /finished_val /pending_val in Hγ'.
        by inversion Hγ'.
      + rewrite lookup_insert_ne in Hγ'; [|done]. by apply Hl.
  Qed.

  Lemma visit_done_keep γ n :
    visit_done γ n ⊢ visit_done γ n ∗ visit_reached_done γ n.
  Proof.
    iIntros "[Hs #Hr]". iFrame "Hs Hr Hr".
  Qed.

  Lemma visit_finished_keep γ n :
    visit_finished γ n ⊢ visit_finished γ n ∗ visit_reached_done γ n.
  Proof.
    iIntros "[Hs #Hr]". iFrame "Hs Hr Hr".
  Qed.

  Lemma visited_invalid_1 γ n :
    visit_pending γ ∗ visit_done γ n -∗ False.
  Proof.
    rewrite /visit_pending /visit_done.
    iIntros "[H1 [H2 _]]". iCombine "H1 H2" as "H".
    iDestruct (own_valid with "H") as %Hv. iPureIntro.
    rewrite auth_frag_valid singleton_valid in Hv.
    rewrite /pending_val /done_val -Cinl_op in Hv.
    apply (@Cinl_valid _ (agreeR natO)), exclusive_l in Hv; done.
  Qed.

  Lemma visited_invalid_2 γ n :
    visit_pending γ ∗ visit_finished γ n -∗ False.
  Proof.
    rewrite /visit_pending /visit_finished.
    iIntros "[H1 [H2 _]]". iCombine "H1 H2" as "H".
    iDestruct (own_valid with "H") as %Hv. iPureIntro.
    rewrite auth_frag_valid singleton_valid in Hv.
    rewrite /pending_val /finished_val in Hv. done.
  Qed.

  Lemma visited_invalid_3 γ n1 n2 :
    visit_done γ n1 ∗ visit_finished γ n2 -∗ False.
  Proof.
    rewrite /visit_done /visit_finished.
    iIntros "[[H1 _] [H2 _]]". iCombine "H1 H2" as "H".
    iDestruct (own_valid with "H") as %Hv. iPureIntro.
    rewrite auth_frag_valid singleton_valid in Hv.
    rewrite /done_val /finished_val in Hv. done.
  Qed.

  Lemma visited_reached_done_agree γ n1 n2 :
    visit_reached_done γ n1 -∗ visit_reached_done γ n2 -∗ ⌜n1 = n2⌝.
  Proof.
    rewrite /visit_reached_done.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv. iPureIntro.
    rewrite -auth_frag_op singleton_op auth_frag_valid singleton_valid in Hv.
    by apply to_agree_op_inv_L in Hv.
  Qed.

  Lemma get_visit_reached_done γ n m d ps pn B :
    d !! γ = Some (to_agree n) →
    visited_mapg_auth m d ps pn B ==∗ visited_mapg_auth m d ps pn B ∗ visit_reached_done γ n.
  Proof.
    iIntros (Hd) "(Hms & Hd & Hps & Hpn & Hbag & %HBcoh & %Hdid & %Hcoh & %Hpcoh)".
    rewrite /visit_reached_done.
    iMod (own_update _ _ (● d ⋅ ◯ {[γ := to_agree n]}) with "Hd") as "[Hd #Hr]".
    { apply auth_update_dfrac_alloc; [apply _|].
      apply singleton_included_l. exists (to_agree n). split; [by rewrite Hd|].
      apply Some_included_2. by left. }
    iModIntro. by iFrame "∗ # %".
  Qed.

  Lemma visited_reached_done_invalid γ n m d ps pn B :
    visited_mapg_auth m d ps pn B -∗ visit_reached_done γ n -∗ visit_pending γ -∗ False.
  Proof.
    iIntros "(Hms & Hd & Hps & Hpn & Hbag & %HBcoh & %Hdid & %Hcoh & %Hpcoh) Hreached Hpending".
    rewrite /visit_reached_done /visit_pending.
    iDestruct (own_valid_2 with "Hd Hreached") as %Hvd.
    apply auth_both_valid_discrete in Hvd as [Hincl_d _].
    apply singleton_included_l in Hincl_d as (xd & Hxd & _).
    assert (d !! γ ≠ None) as Hdγ.
    { intros Heq. rewrite Heq in Hxd. inversion Hxd. }
    destruct (Hcoh γ Hdγ) as (n' & Hmγ).
    iDestruct (own_valid_2 with "Hms Hpending") as %Hvm.
    apply auth_both_valid_discrete in Hvm as [Hincl_m _].
    apply singleton_included_l in Hincl_m as (ym & Hym & Hle).
    iPureIntro. destruct Hmγ as [Hmγ | Hmγ]; rewrite Hmγ in Hym;
      apply Some_equiv_inj in Hym; rewrite -Hym in Hle;
      apply Some_included in Hle as [Heq | Hle].
    - rewrite /pending_val /done_val in Heq.
      apply (inj Cinl), (inj Excl) in Heq. by inversion Heq.
    - rewrite /pending_val /done_val in Hle.
      apply csum_included in Hle as [Hbot | [(?&?& Heq1 & Heq2 & Hinc) | (?&?& Heq1 & _ & _)]].
      + by inversion Hbot.
      + injection Heq1 as <-. injection Heq2 as <-.
        exfalso. apply (exclusive_included (Excl None) (Excl (Some n'))); done.
      + by inversion Heq1.
    - rewrite /pending_val /finished_val in Heq. by inversion Heq.
    - rewrite /pending_val /finished_val in Hle.
      apply csum_included in Hle as [Hbot | [(?&?& _ & Heq1 & _) | (?&?& Heq1 & _ & _)]].
      + by inversion Hbot.
      + by inversion Heq1.
      + by inversion Heq1.
  Qed.

  Lemma visited_agree_n γ n1 n2 :
    (visit_done γ n1 ∨ visit_finished γ n1) -∗
    (visit_done γ n2 ∨ visit_finished γ n2) -∗
    ⌜n1 = n2⌝ ∗
    (visit_done γ n1 ∨ visit_finished γ n1) ∗
    (visit_done γ n2 ∨ visit_finished γ n2).
  Proof.
    iIntros "H1 H2".
    iAssert (visit_reached_done γ n1) as "#R1".
    { iDestruct "H1" as "[[_ $]|[_ $]]". }
    iAssert (visit_reached_done γ n2) as "#R2".
    { iDestruct "H2" as "[[_ $]|[_ $]]". }
    iSplit. iApply (visited_reached_done_agree with "R1 R2").
    iFrame.
  Qed.

  Lemma pending_set_combine γs1 γs2 :
    penset_frag γs1 ∗ penset_frag γs2 ⊣⊢ ⌜γs1 ## γs2⌝ ∗ penset_frag (γs1 ∪ γs2).
  Proof.
    rewrite /penset_frag. iSplit.
    - iIntros "[H1 H2]". iCombine "H1 H2" as "H".
      iDestruct (own_valid with "H") as %Hv%auth_frag_valid_1.
      apply gset_disj_valid_op in Hv.
      iSplit; [done|]. by rewrite gset_disj_union //.
    - iIntros "[%Hdisj H]". rewrite -gset_disj_union // -own_op -auth_frag_op //.
  Qed.

  Lemma pending_set_remove m d ps pn B γs :
    visited_mapg_auth m d ps pn B -∗ pencount_frag pn -∗ penset_frag γs -∗
    ([∗ set] γ ∈ γs, ∃ n, visit_reached_done γ n) ==∗
    visited_mapg_pending_removed m d ps pn γs B ∗ pencount_frag (pn - size γs).
  Proof.
    iIntros "(Hms & Hd & Hps & Hpn1 & Hbag & %HBcoh & %Hdid & %Hcoh & %Hpcoh) Hpn2 Hfrag #Hreached".
    iAssert (⌜∀ γ, γ ∈ γs → d !! γ ≠ None⌝)%I as %Hdγs.
    { iIntros (γ Hin).
      iDestruct (big_sepS_elem_of with "Hreached") as (n) "Hr"; first done.
      iDestruct (own_valid_2 with "Hd Hr") as %Hv.
      apply auth_both_valid_discrete in Hv as [Hincl _].
      apply singleton_included_l in Hincl as (xd & Hxd & _).
      iPureIntro. intros Heq. rewrite Heq in Hxd. inversion Hxd. }
    rewrite /visited_mapg_pending_removed /penset_frag.
    iCombine "Hps Hfrag" as "Hpsfull".
    iDestruct (own_valid with "Hpsfull") as %Hv.
    apply auth_both_valid_discrete in Hv as [Hincl%gset_disj_included _].
    iMod (own_update with "Hpsfull") as "Hps'".
    { apply auth_update_dealloc, gset_disj_dealloc_local_update. }
    iMod (pn_update pn (pn - size γs) with "Hpn1 Hpn2") as "[Hpn1 Hpn2]".
    iModIntro. iFrame "Hms Hd Hps' Hpn1 Hpn2 Hbag". iPureIntro.
    split; [exact HBcoh|]. split; [exact Hdid|]. split; first done.
    destruct Hpcoh as [Hsz Hpcoh].
    split.
    - rewrite (size_difference _ _ Hincl) -Hsz //.
    - intros γ' Hm. specialize (Hpcoh γ' Hm).
      destruct (decide (γ' ∈ γs)) as [Hin | Hnin].
      + exfalso. specialize (Hdγs _ Hin).
        destruct (Hcoh γ' Hdγs) as (n & [Hmγ | Hmγ]); rewrite Hmγ in Hm;
          rewrite /done_val /finished_val /pending_val in Hm;
          by inversion Hm.
      + by apply elem_of_difference.
  Qed.

  (** [id_token id] witnesses that no [γ] in [m] maps to [done_val id]
      or [finished_val id] — id is unused in the visited map. *)
  Lemma id_token_unused m d ps pn B id :
    visited_mapg_auth m d ps pn B -∗ id_token id -∗
      ⌜∀ γ,
          m !! γ ≠ Some (done_val id) ∧
          m !! γ ≠ Some (finished_val id)⌝ ∗
      visited_mapg_auth m d ps pn B ∗ id_token id.
  Proof.
    iIntros "(Hms & Hd & Hps & Hpn & Hbag & %HBcoh & %Hdid & %Hcoh & %Hpcoh) Htok".
    iAssert (⌜id ∉ B⌝)%I as %HnotB.
    { rewrite /id_token. iDestruct (own_valid_2 with "Hbag Htok") as %Hv.
      rewrite auth_frag_op_valid gset_disj_valid_op in Hv. iPureIntro. set_solver. }
    iFrame "∗ %". iPureIntro. intros γ. split.
    - intros Hmγ. specialize (HBcoh γ id (or_introl Hmγ)). done.
    - intros Hmγ. specialize (HBcoh γ id (or_intror Hmγ)). done.
  Qed.

  (** Direct corollary: holding [id_token id] and [visit_reached_done γ id]
      together is inconsistent under any [visited_mapg_auth]. *)
  Lemma id_token_visit_reached_done_invalid m d ps pn B γ id :
    visited_mapg_auth m d ps pn B -∗ id_token id -∗ visit_reached_done γ id -∗ False.
  Proof.
    iIntros "Hauth Htok Hreached".
    iDestruct "Hauth" as
      "(Hms & Hd & Hps & Hpn & Hbag & %HBcoh & %Hdid & %Hcoh & %Hpcoh)".
    rewrite /id_token /visit_reached_done.
    (* id ∉ B *)
    iDestruct (own_valid_2 with "Hbag Htok") as %Hv.
    rewrite auth_frag_op_valid gset_disj_valid_op in Hv.
    assert (id ∉ B) as HnotB by set_solver.
    (* d !! γ ≡ Some (to_agree id) via auth validity + agree_valid_included *)
    iDestruct (own_valid_2 with "Hd Hreached") as %Hvd.
    apply auth_both_valid_discrete in Hvd as [Hincl_d Hvalid_d].
    apply singleton_included_l in Hincl_d as (xd & Hxd & Hle).
    assert (✓ xd) as Hvxd
      by (eapply lookup_valid_Some; [exact Hvalid_d|exact Hxd]).
    assert (xd ≡ to_agree id) as Hxd_eq.
    { apply Some_included in Hle as [Heq | Hinc].
      - by symmetry.
      - symmetry. by apply (agree_valid_included _ _ Hvxd). }
    assert (d !! γ ≡ Some (to_agree id)) as Hdg_eq.
    { rewrite Hxd. by f_equiv. }
    (* Apply Hdid + HBcoh; contradicts id ∉ B *)
    specialize (Hdid γ id Hdg_eq).
    specialize (HBcoh γ id Hdid).
    iPureIntro. set_solver.
  Qed.

End visited_map_res.

(* Each [loc] in the lg_map is in one of two states:
   - [Cinl (to_agree ())]   — explicitly unallocated (filled tauth leaf)
   - [Cinr (to_agree γ)]    — allocated to [γ] (suspended tauth leaf)
   Both states use [agreeR], so fragments are persistent and a single [loc]
   cannot be in both states simultaneously ([Cinl · Cinr] is invalid). *)
Definition lg_mapEntry := csumR (agreeR unitO) (agreeR (leibnizO gname)).
Definition lg_mapUR := authR (gmapUR loc lg_mapEntry).
Class lg_mapG Σ := Lg_mapG { lg_map_inG :> inG Σ lg_mapUR; lg_mapG_name : gname }.

Section lg_map.
  Context `{!lg_mapG Σ, !spec_metaG Σ}.

  Definition lg_mapg_type := gmap loc lg_mapEntry.

  (** [lg_mapg_auth m] bundles the lg-map authority with a held bag of
      [vmeta_token]s for every key in [dom m]. The bag is the auth
      fragment [own spec_meta_name (◯ GSet (dom m))]; it acts as proof
      that every key was once handed to us via [step_verifier_alloc].
      Composed with a fresh [vmeta_token l] from a new allocation,
      [gset_disj] validity gives [l ∉ dom m] without any external
      freshness obligation. *)
  Definition lg_mapg_auth (m : lg_mapg_type) : iProp Σ :=
    own lg_mapG_name (● m) ∗ own spec_meta_name (◯ GSet (dom m)).

  Definition lg_mapg_frag l γ : iProp Σ :=
    own lg_mapG_name (◯ {[ l := Cinr (to_agree γ) ]}).

  Definition lg_mapg_unalloc l : iProp Σ :=
    own lg_mapG_name (◯ {[ l := Cinl (to_agree ()) ]}).

  Global Instance lg_mapg_frag_persistent l γ : Persistent (lg_mapg_frag l γ).
  Proof. apply _. Qed.

  Global Instance lg_mapg_unalloc_persistent l : Persistent (lg_mapg_unalloc l).
  Proof. apply _. Qed.

  Lemma lg_mapg_agree l γ1 γ2 :
    lg_mapg_frag l γ1 -∗ lg_mapg_frag l γ2 -∗ ⌜γ1 = γ2⌝ ∗ lg_mapg_frag l γ1 ∗ lg_mapg_frag l γ2.
  Proof.
    rewrite /lg_mapg_frag. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    iFrame. iPureIntro.
    rewrite -auth_frag_op auth_frag_valid singleton_op singleton_valid -Cinr_op
      Cinr_valid in Hv.
    fold_leibniz. by apply to_agree_op_inv_L in Hv.
  Qed.

  (* The two states are mutually exclusive at the same location. *)
  Lemma lg_mapg_frag_unalloc_excl l γ :
    lg_mapg_frag l γ -∗ lg_mapg_unalloc l -∗ False.
  Proof.
    rewrite /lg_mapg_frag /lg_mapg_unalloc. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    rewrite -auth_frag_op singleton_op auth_frag_valid singleton_valid in Hv.
    done.
  Qed.

  (** Combined [vmeta_token l ∗ own spec_meta_name (◯ GSet (dom m))]
      proves [l ∉ dom m] via [gset_disj] validity, and the merged
      fragment becomes [◯ GSet (dom m ∪ {[l]})] which equals
      [◯ GSet (dom (<[l := _]> m))]. Used by both insert variants. *)
  Local Lemma vmeta_combine_dom (m : lg_mapg_type) (l : loc) (e : lg_mapEntry) :
    vmeta_token l -∗ own spec_meta_name (◯ GSet (dom m)) -∗
      ⌜l ∉ dom m⌝ ∗ own spec_meta_name (◯ GSet (dom (<[ l := e ]> m))).
  Proof.
    iIntros "Hvtok Hsmeta".
    iDestruct (own_valid_2 with "Hsmeta Hvtok") as %Hv.
    rewrite auth_frag_op_valid gset_disj_valid_op in Hv.
    iSplit; [iPureIntro; set_solver|].
    iCombine "Hsmeta Hvtok" as "Hsmeta'".
    rewrite gset_disj_union; [|set_solver].
    rewrite dom_insert_L (comm_L union {[l]}).
    iFrame "Hsmeta'".
  Qed.

  Lemma lg_mapg_insert m l γ :
    vmeta_token l -∗ lg_mapg_auth m ==∗
      lg_mapg_auth (<[ l := Cinr (to_agree γ) ]> m) ∗ lg_mapg_frag l γ.
  Proof.
    rewrite /lg_mapg_auth /lg_mapg_frag. iIntros "Hvtok [Hauth Hsmeta]".
    iDestruct (vmeta_combine_dom m l (Cinr (to_agree γ))
               with "Hvtok Hsmeta") as "[%Hl_nin Hsmeta']".
    apply not_elem_of_dom in Hl_nin.
    iMod (own_update with "Hauth") as "[$ $]";
      last by iModIntro; iFrame "Hsmeta'".
    apply auth_update_alloc.
    by apply alloc_singleton_local_update.
  Qed.

  Lemma lg_mapg_insert_unalloc m l :
    vmeta_token l -∗ lg_mapg_auth m ==∗
      lg_mapg_auth (<[ l := Cinl (to_agree ()) ]> m) ∗ lg_mapg_unalloc l.
  Proof.
    rewrite /lg_mapg_auth /lg_mapg_unalloc. iIntros "Hvtok [Hauth Hsmeta]".
    iDestruct (vmeta_combine_dom m l (Cinl (to_agree ()))
               with "Hvtok Hsmeta") as "[%Hl_nin Hsmeta']".
    apply not_elem_of_dom in Hl_nin.
    iMod (own_update with "Hauth") as "[$ $]";
      last by iModIntro; iFrame "Hsmeta'".
    apply auth_update_alloc.
    by apply alloc_singleton_local_update.
  Qed.

End lg_map.

(** Prover-side parallel of [lg_map]. Uses Iris's standard [meta]/[meta_token]
    machinery (from [iris.base_logic.lib.gen_heap]) for freshness, since
    prover allocations come from [wp_alloc_meta] which yields [meta_token l ⊤].
    The verifier and prover [loc]s come from independent heaps and may
    coincide as values, so the two [lg_map] instances must use distinct
    gnames — hence a separate [lg_mapG_p] class. *)
Class lg_mapG_p Σ := Lg_mapG_p { lg_map_p_inG :> inG Σ lg_mapUR; lg_mapG_p_name : gname }.

Definition lg_p_meta_n : namespace := nroot .@ "lg_p_meta".

Section lg_map_p.
  Context `{!lg_mapG_p Σ, !heapGS Σ}.

  (** [lg_mapg_p_auth m] bundles the lg-map authority with a persistent
      [meta l lg_p_meta_n (true : bool)] witness for every key [l ∈ dom m].
      At insert time, [meta_combine_dom] uses [decide] to check whether
      [l ∈ dom m]: in the positive case it calls [meta_set false] using
      [meta_token l (↑lg_p_meta_n)] (a sub-token of the [meta_token l ⊤]
      input), obtains [meta l lg_p_meta_n false], and applies [meta_agree]
      to get [⌜false = true⌝] — a contradiction.  In the negative case it
      calls [meta_set true] to extend the bigsep for the new key. *)
  Definition lg_mapg_p_auth (m : lg_mapg_type) : iProp Σ :=
    own lg_mapG_p_name (● m) ∗
    [∗ set] l ∈ dom m, meta l lg_p_meta_n (true : bool).

  Definition lg_mapg_p_frag l γ : iProp Σ :=
    own lg_mapG_p_name (◯ {[ l := Cinr (to_agree γ) ]}).

  Definition lg_mapg_p_unalloc l : iProp Σ :=
    own lg_mapG_p_name (◯ {[ l := Cinl (to_agree ()) ]}).

  Global Instance lg_mapg_p_frag_persistent l γ : Persistent (lg_mapg_p_frag l γ).
  Proof. apply _. Qed.

  Global Instance lg_mapg_p_unalloc_persistent l : Persistent (lg_mapg_p_unalloc l).
  Proof. apply _. Qed.

  Lemma lg_mapg_p_agree l γ1 γ2 :
    lg_mapg_p_frag l γ1 -∗ lg_mapg_p_frag l γ2 -∗
      ⌜γ1 = γ2⌝ ∗ lg_mapg_p_frag l γ1 ∗ lg_mapg_p_frag l γ2.
  Proof.
    rewrite /lg_mapg_p_frag. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    iFrame. iPureIntro.
    rewrite -auth_frag_op auth_frag_valid singleton_op singleton_valid -Cinr_op
      Cinr_valid in Hv.
    fold_leibniz. by apply to_agree_op_inv_L in Hv.
  Qed.

  Lemma lg_mapg_p_frag_unalloc_excl l γ :
    lg_mapg_p_frag l γ -∗ lg_mapg_p_unalloc l -∗ False.
  Proof.
    rewrite /lg_mapg_p_frag /lg_mapg_p_unalloc. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    rewrite -auth_frag_op singleton_op auth_frag_valid singleton_valid in Hv.
    done.
  Qed.

  (** Combined [meta_token l ⊤ ∗ ([∗ set] l' ∈ dom m, meta l' lg_p_meta_n true)]
      yields [l ∉ dom m] and re-bundles into the extended big-sep for the
      inserted key.  We split [meta_token l ⊤] into [meta_token l (↑lg_p_meta_n)]
      and case on [decide (l ∈ dom m)]: the [∈] branch uses [meta_set false]
      to obtain [meta l lg_p_meta_n false] and [meta_agree] to derive
      [⌜false = true⌝] (a contradiction discharged by [discriminate]); the
      [∉] branch uses [meta_set true] to extend the bigsep. *)
  Local Lemma meta_combine_dom (m : lg_mapg_type) (l : loc) (e : lg_mapEntry) :
    meta_token l ⊤ -∗ ([∗ set] l' ∈ dom m, meta l' lg_p_meta_n (true : bool)) ==∗
      ⌜l ∉ dom m⌝ ∗
      ([∗ set] l' ∈ dom (<[ l := e ]> m), meta l' lg_p_meta_n (true : bool)).
  Proof.
    iIntros "Hmtok Hbig".
    iDestruct (meta_token_difference l (↑lg_p_meta_n) with "Hmtok")
      as "[Hmtok_N _]"; first set_solver.
    destruct (decide (l ∈ dom m)) as [Hin | Hnin].
    - iDestruct (big_sepS_elem_of with "Hbig") as "#Hmeta_l"; first done.
      iMod (meta_set _ l (false : bool) lg_p_meta_n with "Hmtok_N")
        as "#Hmeta_false"; first done.
      iDestruct (meta_agree with "Hmeta_false Hmeta_l") as %H.
      discriminate.
    - iMod (meta_set _ l (true : bool) lg_p_meta_n with "Hmtok_N")
        as "#Hmeta_l"; first done.
      iModIntro. iSplit; first done.
      rewrite dom_insert_L big_sepS_insert; last done.
      iFrame "Hmeta_l Hbig".
  Qed.

  Lemma lg_mapg_p_insert m l γ :
    meta_token l ⊤ -∗ lg_mapg_p_auth m ==∗
      lg_mapg_p_auth (<[ l := Cinr (to_agree γ) ]> m) ∗ lg_mapg_p_frag l γ.
  Proof.
    rewrite /lg_mapg_p_auth /lg_mapg_p_frag.
    iIntros "Hmtok [Hauth Hbig]".
    iMod (meta_combine_dom m l (Cinr (to_agree γ)) with "Hmtok Hbig")
      as "[%Hl_nin Hbig']".
    apply not_elem_of_dom in Hl_nin.
    iMod (own_update with "Hauth") as "[$ $]";
      last by iModIntro; iFrame "Hbig'".
    apply auth_update_alloc.
    by apply alloc_singleton_local_update.
  Qed.

  Lemma lg_mapg_p_insert_unalloc m l :
    meta_token l ⊤ -∗ lg_mapg_p_auth m ==∗
      lg_mapg_p_auth (<[ l := Cinl (to_agree ()) ]> m) ∗ lg_mapg_p_unalloc l.
  Proof.
    rewrite /lg_mapg_p_auth /lg_mapg_p_unalloc.
    iIntros "Hmtok [Hauth Hbig]".
    iMod (meta_combine_dom m l (Cinl (to_agree ())) with "Hmtok Hbig")
      as "[%Hl_nin Hbig']".
    apply not_elem_of_dom in Hl_nin.
    iMod (own_update with "Hauth") as "[$ $]";
      last by iModIntro; iFrame "Hbig'".
    apply auth_update_alloc.
    by apply alloc_singleton_local_update.
  Qed.

End lg_map_p.

Definition mapUR := authR (gmapUR val (dfrac_agreeR valO)).
Class mapG Σ := MapG { map_inG :> inG Σ mapUR; mapG_name : gname }.

Section map_res.
  Context `{!mapG Σ}.

  Definition mapg_type := gmap val (dfrac_agreeR valO).

  Definition mapg_auth (m : mapg_type) : iProp Σ :=
    own mapG_name (● m).

  Definition mapg_insert_def (m : mapg_type) k v : mapg_type :=
    <[ k := to_frac_agree 1 v ]> m.

  (* A fragment with fraction [q] for key [k] and value [v]. A full fraction
     [q = 1] gives exclusive ownership and permits removal. The caller may
     split a full fragment into [n] pieces of fraction [1/n] via [mapg_split]. *)
  Definition mapg_frag (k : val) (q : Qp) (v : val) : iProp Σ :=
    own mapG_name (◯ {[ k := to_frac_agree q v ]}).

  Lemma mapg_frag_op k q1 q2 v :
    mapg_frag k (q1 + q2) v ⊣⊢ mapg_frag k q1 v ∗ mapg_frag k q2 v.
  Proof.
    rewrite /mapg_frag -own_op -auth_frag_op singleton_op.
    by rewrite -frac_agree_op.
  Qed.

  Lemma mapg_frag_split k q1 q2 v :
    mapg_frag k (q1 + q2) v -∗ mapg_frag k q1 v ∗ mapg_frag k q2 v.
  Proof. iIntros "H". by iApply mapg_frag_op. Qed.

  Lemma mapg_frag_combine k q1 q2 v :
    mapg_frag k q1 v -∗ mapg_frag k q2 v -∗ mapg_frag k (q1 + q2) v.
  Proof. iIntros "H1 H2". rewrite mapg_frag_op. iFrame. Qed.

  Lemma mapg_frag_agree k q1 q2 v1 v2 :
    mapg_frag k q1 v1 -∗ mapg_frag k q2 v2 -∗ ⌜v1 = v2⌝.
  Proof.
    rewrite /mapg_frag. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    iPureIntro.
    rewrite -auth_frag_op auth_frag_valid singleton_op singleton_valid in Hv.
    apply dfrac_agree_op_valid_L in Hv as [_ ?]. done.
  Qed.

  Lemma mapg_insert m k v :
    m !! k = None →
    mapg_auth m ==∗ mapg_auth (mapg_insert_def m k v) ∗ mapg_frag k 1 v.
  Proof.
    rewrite /mapg_auth /mapg_frag. iIntros (Hfresh) "H".
    iMod (own_update with "H") as "[$ $]"; last done.
    apply auth_update_alloc.
    apply alloc_singleton_local_update; done.
  Qed.

  Lemma mapg_subset m k q v :
    mapg_auth m -∗ mapg_frag k q v -∗
      ⌜∃ y, m !! k ≡ Some y ∧ y.2 ≡ to_agree v⌝.
  Proof.
    rewrite /mapg_auth /mapg_frag. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv. iPureIntro.
    apply auth_both_valid_discrete in Hv as [Hincl Hv].
    apply singleton_included_l in Hincl as (y & Hy & Hle).
    assert (✓ y) as Hvy.
    { eapply (lookup_valid_Some _ k); [done|by rewrite Hy]. }
    destruct y as [d a]. simpl.
    apply Some_included in Hle as [Heq | Hinc].
    - destruct Heq as [_ Heq2]. simpl in Heq2.
      exists (d, a). split; [done|]. by symmetry.
    - apply pair_included in Hinc as [_ Ha].
      destruct Hvy as [_ Hva].
      apply (agree_valid_included _ _ Hva) in Ha.
      exists (d, a). split; [done|by symmetry].
  Qed.

  Lemma mapg_remove m k v :
    mapg_auth m -∗ mapg_frag k 1 v ==∗ mapg_auth (delete k m).
  Proof.
    rewrite /mapg_auth /mapg_frag. iIntros "H1 H2".
    iCombine "H1 H2" as "H".
    iMod (own_update with "H") as "$"; last done.
    apply auth_update_dealloc.
    by apply delete_singleton_local_update, _.
  Qed.

End map_res.

Definition capUR := authR (gmapUR nat (agreeR natO)).
Class capG Σ := CapG { cap_inG :> inG Σ capUR; capG_name : gname }.

Section cap_res.
  Context `{!capG Σ}.

  Definition cap_type := gmap nat (agree nat).

  Definition cap_auth (m : cap_type) : iProp Σ :=
    own capG_name (● m).

  Definition cap_frag (id n : nat) : iProp Σ :=
    own capG_name (◯ {[ id := to_agree n ]}).

  Global Instance cap_frag_persistent id n : Persistent (cap_frag id n).
  Proof. apply _. Qed.

  Lemma cap_frag_agree id n1 n2 :
    cap_frag id n1 -∗ cap_frag id n2 -∗ ⌜n1 = n2⌝.
  Proof.
    rewrite /cap_frag. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv. iPureIntro.
    rewrite -auth_frag_op auth_frag_valid singleton_op singleton_valid in Hv.
    fold_leibniz. by apply to_agree_op_inv_L in Hv.
  Qed.

  Lemma cap_insert m id n :
    m !! id = None →
    cap_auth m ==∗ cap_auth (<[ id := to_agree n ]> m) ∗ cap_frag id n.
  Proof.
    rewrite /cap_auth /cap_frag. iIntros (Hfresh) "H".
    iMod (own_update with "H") as "[$ $]"; last done.
    apply auth_update_alloc.
    by apply alloc_singleton_local_update.
  Qed.

End cap_res.

Definition intransitUR := fracR.
Class intransitG Σ := IntransitG { intransit_inG :> inG Σ intransitUR; intransitG_name : gname }.

Section intransit_res.
  Context `{!intransitG Σ}.

  Definition intransit (q : Qp) : iProp Σ := own intransitG_name q.

  Lemma intransit_valid q : intransit q ⊢ ⌜(q ≤ 1)%Qp⌝.
  Proof.
    iIntros "H". by iDestruct (own_valid with "H") as %?%frac_valid.
  Qed.

  Lemma intransit_split q1 q2 :
    intransit (q1 + q2)%Qp ⊣⊢ intransit q1 ∗ intransit q2.
  Proof. by rewrite /intransit -own_op frac_op. Qed.

  Lemma intransit_excl_full q :
    intransit 1%Qp -∗ intransit q -∗ False.
  Proof.
    rewrite /intransit. iIntros "H1 H2".
    iCombine "H1 H2" as "H".
    iDestruct (own_valid with "H") as %Hv%frac_valid.
    iPureIntro. revert Hv. apply Qp.not_add_le_l.
  Qed.

End intransit_res.

(* Tracks whether we are in the bad case or not. *)
Definition stateUR := authUR (optionUR unitO).
Class stateG Σ := StateG { state_inG :> inG Σ stateUR; stateG_name : gname }.

Section state_res.
  Context `{!stateG Σ}.

  Definition state_car := optionUR unitO.

  Definition state (o : state_car) := own stateG_name (●{DfracOwn (1/2)} o).
  (* good_state represents the good case.
    false_state represents the bad case.
    Explained in more detail later. *)
  Definition good_state := state None.
  Definition false_state := state (Some ()).

  Lemma state_agree (o o' : state_car) :
    state o -∗ state o' -∗ ⌜o' = o⌝ ∗ state o ∗ state o'.
  Proof.
    rewrite /state. iIntros "H1 H2". iCombine "H1 H2" as "H".
    iDestruct (own_valid with "H") as %Hv.
    apply auth_auth_dfrac_op_valid in Hv as [_ [Heq _]].
    iDestruct "H" as "[H1 H2]". iFrame.
    iPureIntro. symmetry. apply leibniz_equiv. exact Heq.
  Qed.

  Lemma state_update_bad :
    good_state -∗ good_state ==∗ false_state ∗ false_state.
  Proof.
    rewrite /good_state /false_state /state.
    iIntros "H1 H2". iCombine "H1 H2" as "H".
    iMod (own_update with "H") as "H".
    { apply (auth_update_auth None (Some ()) (Some ())).
      apply alloc_option_local_update. done. }
    iDestruct "H" as "[H1 H2]". by iFrame.
  Qed.

End state_res.

(* Single-instance token carrying a [gname]. The full fraction (1) is
   exclusive; any two fragments agree on the carried [gname] and
   split/combine via fractional ownership. *)
Definition gnameTokUR := dfrac_agreeR (leibnizO gname).
Class gnameTokG Σ := GnameTokG {
  gname_tok_inG :> inG Σ gnameTokUR;
  gname_tok_name : gname;
}.

Section gname_tok_res.
  Context `{!gnameTokG Σ}.

  Definition gtok (q : Qp) (γ : gname) : iProp Σ :=
    own gname_tok_name (to_dfrac_agree (DfracOwn q) (γ : leibnizO gname)).

  Lemma gtok_agree q1 q2 γ1 γ2 :
    gtok q1 γ1 -∗ gtok q2 γ2 -∗ ⌜γ1 = γ2⌝.
  Proof.
    iIntros "H1 H2". rewrite /gtok. iCombine "H1 H2" as "H".
    iDestruct (own_valid with "H") as %[_ Heq]%dfrac_agree_op_valid_L.
    done.
  Qed.

  Lemma gtok_split q1 q2 γ :
    gtok (q1 + q2)%Qp γ ⊣⊢ gtok q1 γ ∗ gtok q2 γ.
  Proof.
    by rewrite /gtok -own_op -dfrac_agree_op dfrac_op_own.
  Qed.

  Lemma gtok_combine q1 q2 γ1 γ2 :
    gtok q1 γ1 -∗ gtok q2 γ2 -∗ ⌜γ1 = γ2⌝ ∗ gtok (q1 + q2)%Qp γ1.
  Proof.
    iIntros "H1 H2".
    iDestruct (gtok_agree with "H1 H2") as %->.
    iSplit; [done|]. iApply gtok_split. iFrame.
  Qed.

  Lemma gtok_excl q γ1 γ2 :
    gtok 1 γ1 -∗ gtok q γ2 -∗ False.
  Proof.
    iIntros "H1 H2". rewrite /gtok. iCombine "H1 H2" as "H".
    iDestruct (own_valid with "H") as %[Hv _]%dfrac_agree_op_valid_L.
    iPureIntro. apply dfrac_valid_own in Hv.
    by apply Qp.not_add_le_l in Hv.
  Qed.

  Lemma gtok_update γ γ' :
    gtok 1 γ ==∗ gtok 1 γ'.
  Proof.
    iIntros "H". rewrite /gtok.
    iApply (own_update with "H").
    by apply cmra_update_exclusive.
  Qed.

End gname_tok_res.

(* Single-instance token with two states:
   - [None]   — unparameterized state
   - [Some n] — state parameterized by [n : nat].
   The full fraction (1) is exclusive; any two fragments agree on the
   carried [option nat] and split/combine via fractional ownership.
   At full fraction the value can be updated (e.g. unparameterized to
   [Some n] or vice versa). *)
Definition stateTokUR := dfrac_agreeR (leibnizO (option nat)).
Class stateTokG Σ := StateTokG {
  state_tok_inG :> inG Σ stateTokUR;
  state_tok_name : gname;
}.

Section state_tok_res.
  Context `{!stateTokG Σ}.

  Definition stok (s : option nat) : iProp Σ :=
    own state_tok_name (to_dfrac_agree (DfracOwn (1/2)) (s : leibnizO (option nat))).

  Definition stok_comp (s : option nat) : iProp Σ :=
    own state_tok_name (to_dfrac_agree (DfracOwn 1) (s : leibnizO (option nat))).

  Definition stok_unset : iProp Σ := stok None.
  Definition stok_set (n : nat) : iProp Σ := stok (Some n).

  Lemma stok_agree s1 s2 :
    stok s1 -∗ stok s2 -∗ ⌜s1 = s2⌝.
  Proof.
    iIntros "H1 H2". rewrite /stok. iCombine "H1 H2" as "H".
    iDestruct (own_valid with "H") as %[_ Heq]%dfrac_agree_op_valid_L.
    done.
  Qed.

  Lemma stok_split s :
    stok_comp s ⊣⊢ stok s ∗ stok s.
  Proof.
    by rewrite /stok /stok_comp -own_op -dfrac_agree_op dfrac_op_own Qp.half_half.
  Qed.

  Lemma stok_combine s1 s2 :
    stok s1 -∗ stok s2 -∗ ⌜s1 = s2⌝ ∗ stok_comp s1.
  Proof.
    iIntros "H1 H2".
    iDestruct (stok_agree with "H1 H2") as %->.
    iSplit; [done|]. iApply stok_split. iFrame.
  Qed.

  Lemma stok_excl s1 s2 :
    stok_comp s1 -∗ stok s2 -∗ False.
  Proof.
    iIntros "H1 H2". rewrite /stok /stok_comp. iCombine "H1 H2" as "H".
    iDestruct (own_valid with "H") as %[Hv _]%dfrac_agree_op_valid_L.
    iPureIntro. apply dfrac_valid_own in Hv.
    by apply Qp.not_add_le_l in Hv.
  Qed.

  Lemma stok_update s s' :
    stok_comp s ==∗ stok_comp s'.
  Proof.
    iIntros "H". rewrite /stok_comp.
    iApply (own_update with "H").
    by apply cmra_update_exclusive.
  Qed.

End state_tok_res.
