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
(** [id_alloc_entry]: the per-id state of the alloc map. [Cinl (Excl ())]
    is the consumable [id_token]; [Cinr (to_agree γ)] is the persistent
    binding of [id] to [γ]. The [Cinl/Cinr] split makes
    [id_token id ∗ id_alloc id γ -∗ False] follow from cmra validity
    alone (no auth required), and the [agreeR] makes
    [id_alloc id γ1 ∗ id_alloc id γ2 -∗ ⌜γ1 = γ2⌝] follow from
    [to_agree_op_inv]. *)
Definition id_alloc_entry := csumR (exclR unitO) (agreeR (leibnizO gname)).
Definition pending_idUR :=
  authUR (gmapUR nat id_alloc_entry).
Definition idCounterUR := dfrac_agreeR natO.
Class visited_mapG Σ := VisitedMapG {
  visited_state_inG :> inG Σ visited_state_mapUR;
  visited_done_inG :> inG Σ visited_done_mapUR;
  pending_set_inG :> inG Σ pending_setUR;
  pendingn_inG :> inG Σ pendingnUR;
  pending_id_inG :> inG Σ pending_idUR;
  idCounter_inG :> inG Σ idCounterUR;
  visited_state_name : gname;
  visited_done_name : gname;
  pending_set_name : gname;
  pendingnG_name : gname;
  pending_id_name : gname;
  idCounter_name : gname;
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

  (** [done_id_coherent m d] links the id-tag in [d] to the id-tag in [m]:
      whenever [d !! γ ≡ Some (to_agree n)], [m !! γ] is in the matching
      done/finished state at the same [n]. This subsumes the earlier
      existence-style coherence — given [✓ d], every valid agree element
      is equivalent to some [to_agree n] (cf. [to_agree_uninj]); see
      [done_id_visited_coherent] below. *)
  Definition done_id_coherent (m : state_mapg_type) (d : done_mapg_type) : Prop :=
    ∀ γ n, d !! γ ≡ Some (to_agree n) →
      m !! γ = Some (done_val n) ∨ m !! γ = Some (finished_val n).

  (** Derives the existence-style coherence (every key in [dom d] is
      done/finished in [m] for some [n]) from [done_id_coherent] and [✓ d].
      Used wherever the old [visited_coherent] hypothesis was needed. *)
  Local Lemma done_id_visited_coherent m d :
    ✓ d → done_id_coherent m d →
      ∀ γ, d !! γ ≠ None →
        ∃ n, m !! γ = Some (done_val n) ∨ m !! γ = Some (finished_val n).
  Proof.
    intros Hvd Hdid γ Hdγ.
    destruct (d !! γ) as [xd|] eqn:Heqd; [|done].
    assert (d !! γ ≡ Some xd) as Hxd by (rewrite Heqd; done).
    assert (✓ xd) as Hvxd by (eapply lookup_valid_Some; [exact Hvd|exact Hxd]).
    apply to_agree_uninj in Hvxd as [n Hxd_eq].
    exists n. apply (Hdid γ n). rewrite Hxd. by f_equiv.
  Qed.

  Definition pending_coherent (m : state_mapg_type) (ps : pending_setg_type) (pending_n : nat) : Prop :=
    pending_n = size ps ∧
      ∀ γ, m !! γ = Some pending_val → γ ∈ ps.

  Definition id_mapg_type := gmap nat id_alloc_entry.

  (** [gm_m_coherent m gm]: the alloc map at [pending_id_name] mirrors
      [m]'s done/finished entries (with the matching [γ]) on the [Cinr]
      side. [Cinl] entries correspond to ids that have been issued but
      not yet bound (i.e. tokens that are still floating). *)
  Definition gm_m_coherent (m : state_mapg_type) (gm : id_mapg_type) : Prop :=
    ∀ id γ, gm !! id = Some (Cinr (to_agree (γ : leibnizO gname))) ↔
      m !! γ = Some (done_val id) ∨ m !! γ = Some (finished_val id).

  (** [visited_mapg_auth] now tracks the alloc map [gm] (at [pending_id_name])
      and the counter [ctr] (at [idCounter_name], half-share). The pure
      invariants link them: [dom gm = set_seq 0 ctr], and [gm_m_coherent]
      ties [gm]'s [Cinr] entries to [m]'s done/finished entries. *)
  Definition visited_mapg_auth (m : state_mapg_type) (d : done_mapg_type)
      (ps : pending_setg_type) (pending_n : nat) (ctr : nat) (gm : id_mapg_type) : iProp Σ :=
    own visited_state_name (● m) ∗ own visited_done_name (● d) ∗
    own pending_set_name (● GSet ps) ∗ pencount_frag pending_n ∗
    own pending_id_name (● gm) ∗
    own idCounter_name (to_dfrac_agree (DfracOwn (1/2)) ctr) ∗
    ⌜dom gm = set_seq 0 ctr⌝ ∗
    ⌜gm_m_coherent m gm⌝ ∗
    ⌜done_id_coherent m d⌝ ∗ ⌜pending_coherent m ps pending_n⌝.

  Definition visited_map_update_pending
      (m : state_mapg_type) (d : done_mapg_type) (ps : pending_setg_type) pn (γs : gset gname) (ctr : nat) (gm : id_mapg_type) : iProp Σ :=
    let m' := set_fold (λ γ m, <[ γ := pending_val ]>m) m γs in
    let ps' := ps ∪ γs in
    own visited_state_name (● m') ∗
    own visited_done_name (● d) ∗
    own pending_set_name (● GSet ps') ∗ pencount_frag (pn + size γs) ∗
    own pending_id_name (● gm) ∗
    own idCounter_name (to_dfrac_agree (DfracOwn (1/2)) ctr) ∗
    ⌜dom gm = set_seq 0 ctr⌝ ∗
    ⌜gm_m_coherent m' gm⌝ ∗
    ⌜done_id_coherent m' d⌝ ∗
    ⌜pending_coherent m' ps' (pn + size γs)⌝.

  Definition visited_map_update_done
      (m : state_mapg_type) (d : done_mapg_type) (ps : pending_setg_type) pn γ n (ctr : nat) (gm : id_mapg_type) : iProp Σ :=
    own visited_state_name (● <[ γ := done_val n ]>m) ∗
    own visited_done_name (● <[ γ := to_agree n ]>d) ∗
    own pending_set_name (● GSet ps) ∗ pencount_frag pn ∗
    own pending_id_name (● <[ n := Cinr (to_agree (γ : leibnizO gname)) ]>gm) ∗
    own idCounter_name (to_dfrac_agree (DfracOwn (1/2)) ctr) ∗
    ⌜dom (<[ n := Cinr (to_agree (γ : leibnizO gname)) ]>gm) = set_seq 0 ctr⌝ ∗
    ⌜gm_m_coherent (<[ γ := done_val n ]>m) (<[ n := Cinr (to_agree (γ : leibnizO gname)) ]>gm)⌝ ∗
    ⌜done_id_coherent (<[ γ := done_val n ]>m) (<[ γ := to_agree n ]>d)⌝ ∗
    ⌜pending_coherent (<[ γ := done_val n ]>m) ps pn⌝.

  Definition visited_map_update_finished
      (m : state_mapg_type) (d : done_mapg_type) (ps : pending_setg_type) pn γ n (ctr : nat) (gm : id_mapg_type) : iProp Σ :=
    own visited_state_name (● <[ γ := finished_val n ]>m) ∗
    own visited_done_name (● d) ∗
    own pending_set_name (● GSet ps) ∗ pencount_frag pn ∗
    own pending_id_name (● gm) ∗
    own idCounter_name (to_dfrac_agree (DfracOwn (1/2)) ctr) ∗
    ⌜dom gm = set_seq 0 ctr⌝ ∗
    ⌜gm_m_coherent (<[ γ := finished_val n ]>m) gm⌝ ∗
    ⌜done_id_coherent (<[ γ := finished_val n ]>m) d⌝ ∗
    ⌜pending_coherent (<[ γ := finished_val n ]>m) ps pn⌝.

  Definition visited_mapg_pending_removed (m : state_mapg_type) (d : done_mapg_type) (ps : pending_setg_type) (pending_n : nat) (γs : gset gname) (ctr : nat) (gm : id_mapg_type) : iProp Σ :=
    own visited_state_name (● m) ∗ own visited_done_name (● d) ∗
    own pending_set_name (● GSet (ps ∖ γs)) ∗ pencount_frag (pending_n - size γs) ∗
    own pending_id_name (● gm) ∗
    own idCounter_name (to_dfrac_agree (DfracOwn (1/2)) ctr) ∗
    ⌜dom gm = set_seq 0 ctr⌝ ∗
    ⌜gm_m_coherent m gm⌝ ∗
    ⌜done_id_coherent m d⌝ ∗
    ⌜pending_coherent m (ps ∖ γs) (pending_n - size γs)⌝.

  Lemma visited_map_update_pending_rewrite m d ps pn γs ctr gm :
    visited_map_update_pending m d ps pn γs ctr gm ⊣⊢
    visited_mapg_auth (set_fold (λ γ m, <[ γ := pending_val ]>m) m γs) d (ps ∪ γs) (pn + size γs) ctr gm.
  Proof. rewrite /visited_map_update_pending /visited_mapg_auth. done. Qed.

  Lemma visited_map_update_done_rewrite m d ps pn γ n ctr gm :
    visited_map_update_done m d ps pn γ n ctr gm ⊣⊢
    visited_mapg_auth (<[ γ := done_val n ]>m) (<[ γ := to_agree n ]>d) ps pn ctr
      (<[ n := Cinr (to_agree (γ : leibnizO gname)) ]>gm).
  Proof. rewrite /visited_map_update_done /visited_mapg_auth. done. Qed.

  Lemma visited_map_update_finished_rewrite m d ps pn γ n ctr gm :
    visited_map_update_finished m d ps pn γ n ctr gm ⊣⊢
    visited_mapg_auth (<[ γ := finished_val n ]>m) d ps pn ctr gm.
  Proof. rewrite /visited_map_update_finished /visited_mapg_auth. done. Qed.

  Lemma visited_mapg_pending_remove_rewrite m d ps pn γs ctr gm :
    visited_mapg_pending_removed m d ps pn γs ctr gm ⊣⊢
    visited_mapg_auth m d (ps ∖ γs) (pn - size γs) ctr gm.
  Proof. rewrite /visited_mapg_pending_removed /visited_mapg_auth. done. Qed.

  Definition visit_pending γ : iProp Σ :=
    own visited_state_name (◯ {[ γ := pending_val ]}).

  (** [id_alloc id γ] is the persistent witness "id has been bound to γ".
      Lives at [pending_id_name] keyed by [id], so it conflicts directly
      (no auth required) with [id_token id] via [Cinl (Excl ()) ⋅ Cinr _]
      = [CsumBot], and two [id_alloc id γ_i] for the same [id] force
      [γ_1 = γ_2] via [to_agree_op_inv]. *)
  Definition id_alloc (id : nat) (γ : gname) : iProp Σ :=
    own pending_id_name (◯ {[ id := Cinr (to_agree (γ : leibnizO gname)) ]}).

  Definition visit_reached_done γ n : iProp Σ :=
    own visited_done_name (◯ {[ γ := to_agree n ]}) ∗ id_alloc n γ.

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

  Local Lemma some_pending_val_equiv_eq (x : option state_val_type) :
    x ≡ Some pending_val → x = Some pending_val.
  Proof.
    intros Heq. destruct x as [s|]; [|by inversion Heq].
    apply Some_equiv_inj in Heq. rewrite /pending_val in Heq |- *.
    destruct s as [s'| |]; [|by inversion Heq|by inversion Heq].
    apply (inj Cinl) in Heq. destruct s' as [v|]; [|by inversion Heq].
    apply (inj Excl) in Heq. apply leibniz_equiv in Heq. by subst.
  Qed.

  Local Lemma some_cinl_excl_unit_equiv_eq (x : option id_alloc_entry) :
    x ≡ Some (Cinl (Excl ())) → x = Some (Cinl (Excl ())).
  Proof.
    intros Heq. destruct x as [s|]; [|by inversion Heq].
    apply Some_equiv_inj in Heq.
    destruct s as [s'| |]; [|by inversion Heq|by inversion Heq].
    apply (inj Cinl) in Heq. destruct s' as [v|]; [|by inversion Heq].
    apply (inj Excl) in Heq. apply leibniz_equiv in Heq.
    by destruct v; subst.
  Qed.

  (** [id_ctr_frag ctr] is a half-share at [idCounter_name] tracking the
      "next id to allocate". Mirrors [pencount_frag]. The other half lives
      inside [visited_mapg_auth]; the auth's pure invariant ties [ctr] to
      [dom gm = set_seq 0 ctr]. *)
  Definition id_ctr_frag (ctr : nat) : iProp Σ :=
    own idCounter_name (to_dfrac_agree (DfracOwn (1/2)) ctr).

  (** [id_token id] is a consumable token at [pending_id_name] keyed by
      [id]. Holding it claims [id] has been issued but not yet bound to
      any [γ] (via [visited_transition_done]). Exclusive at the same [id]
      since [Cinl (Excl ())] is exclusive. *)
  Definition id_token (id : nat) : iProp Σ :=
    own pending_id_name (◯ {[ id := Cinl (Excl ()) ]}).

  Global Instance id_token_timeless id : Timeless (id_token id).
  Proof. apply _. Qed.

  Global Instance id_alloc_persistent id γ : Persistent (id_alloc id γ).
  Proof. apply _. Qed.

  Global Instance id_alloc_timeless id γ : Timeless (id_alloc id γ).
  Proof. apply _. Qed.

  Global Instance id_ctr_frag_timeless ctr : Timeless (id_ctr_frag ctr).
  Proof. apply _. Qed.

  Lemma id_token_excl id : id_token id -∗ id_token id -∗ False.
  Proof.
    rewrite /id_token. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    rewrite -auth_frag_op singleton_op auth_frag_valid singleton_valid in Hv.
    by apply (Cinl_valid (A:=exclR unitO) (B:=agreeR (leibnizO gname))), exclusive_l in Hv.
  Qed.

  Lemma id_ctr_frag_agree ctr ctr' :
    id_ctr_frag ctr -∗ id_ctr_frag ctr' -∗
      ⌜ctr = ctr'⌝ ∗ id_ctr_frag ctr ∗ id_ctr_frag ctr'.
  Proof.
    rewrite /id_ctr_frag. iIntros "H1 H2". iCombine "H1 H2" as "H".
    iDestruct (own_valid with "H") as %Hv%dfrac_agree_op_valid_L.
    destruct Hv as [_ ->].
    iDestruct "H" as "[H1 H2]". by iFrame.
  Qed.

  (** [id_token_alloc_invalid] is the cmra-level conflict between an
      unalloc token and an alloc fragment at the same [id]. Auth-free. *)
  Lemma id_token_alloc_invalid id γ :
    id_token id -∗ id_alloc id γ -∗ False.
  Proof.
    rewrite /id_token /id_alloc. iIntros "Htok Halloc".
    iDestruct (own_valid_2 with "Htok Halloc") as %Hv.
    rewrite -auth_frag_op singleton_op auth_frag_valid singleton_valid in Hv.
    done.
  Qed.

  (** [id_alloc_agree] is the cmra-level agreement between two alloc
      fragments at the same [id]. Auth-free. *)
  Lemma id_alloc_agree id γ1 γ2 :
    id_alloc id γ1 -∗ id_alloc id γ2 -∗ ⌜γ1 = γ2⌝.
  Proof.
    rewrite /id_alloc. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    rewrite -auth_frag_op singleton_op auth_frag_valid singleton_valid in Hv.
    iPureIntro. apply (Cinr_valid (A:=exclR unitO)) in Hv.
    fold_leibniz. by apply to_agree_op_inv_L in Hv.
  Qed.

  Lemma visited_insert m d ps pn ctr gm :
    visited_mapg_auth m d ps pn ctr gm ∗ pencount_frag pn ==∗
      ∃ γ,
        visited_map_update_pending m d ps pn {[γ]} ctr gm ∗ pencount_frag (pn+1) ∗
          visit_pending γ ∗ penset_frag {[γ]}.
  Proof.
    iIntros "((Hms & Hd & Hps & Hpn1 & Hgm & Hctr & %Hdom & %Hgmm & %Hdid & %Hpcoh) & Hpn2)".
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
    iFrame "Hms' Hd Hps' Hpn1 Hp Hpsf Hpn2 Hgm Hctr".
    iPureIntro. split; [exact Hdom|]. split; last split.
    - (* gm_m_coherent for new m' = <[γ := pending_val]>m *)
      intros id γ'. specialize (Hgmm id γ'). split.
      + intros Hgm_id. apply Hgmm in Hgm_id.
        destruct (decide (γ' = γ)) as [-> | Hne].
        * destruct Hgm_id as [Hmγ | Hmγ]; rewrite Hfm in Hmγ; discriminate.
        * destruct Hgm_id as [Hmγ | Hmγ];
            [left|right]; rewrite lookup_insert_ne; done.
      + intros Hmγ'. apply Hgmm.
        destruct (decide (γ' = γ)) as [-> | Hne].
        * exfalso. destruct Hmγ' as [Hmγ' | Hmγ']; rewrite lookup_insert in Hmγ';
            inversion Hmγ' as [Heq]; rewrite /pending_val /done_val /finished_val in Heq;
            by inversion Heq.
        * destruct Hmγ' as [Hmγ' | Hmγ'];
            [left|right]; rewrite lookup_insert_ne in Hmγ'; done.
    - (* done_id_coherent for new m' *)
      intros γ' n' Hdγ'. destruct (decide (γ' = γ)) as [-> | Hne].
      + exfalso. specialize (Hdid γ n' Hdγ').
        destruct Hdid as [Hmγ | Hmγ]; rewrite Hfm in Hmγ; discriminate.
      + destruct (Hdid γ' n' Hdγ') as [Hmγ | Hmγ];
          [left|right]; rewrite lookup_insert_ne; done.
    - destruct Hpcoh as [Hsize Hl]. split.
      + rewrite size_union; last set_solver. rewrite size_singleton. lia.
      + intros γ' Hγ'. destruct (decide (γ' = γ)) as [-> | Hne].
        * set_solver.
        * rewrite lookup_insert_ne in Hγ'; [|done].
          apply elem_of_union; right. by apply Hl.
  Qed.

  Lemma visited_transition_done m d ps pn ctr gm γ id :
    d !! γ = None →
    visited_mapg_auth m d ps pn ctr gm -∗ visit_pending γ -∗ id_token id
    ==∗ visited_map_update_done m d ps pn γ id ctr gm ∗ visit_done γ id.
  Proof.
    iIntros (Hdγ) "(Hms & Hd & Hps & Hpn & Hgm & Hctr & %Hdom & %Hgmm & %Hdid & %Hpcoh) H1 Htok".
    rewrite /visited_map_update_done /visit_done /visit_reached_done /id_alloc.
    (* Derive m !! γ = pending_val BEFORE consuming H1. *)
    iDestruct (own_valid_2 with "Hms H1") as %Hvm.
    apply auth_both_valid_discrete in Hvm as [Hinclm Hvalidm].
    apply (singleton_included_exclusive_l m γ pending_val) in Hinclm; [|apply _|exact Hvalidm].
    assert (m !! γ = Some pending_val) as Hmγ_pend by (apply some_pending_val_equiv_eq; exact Hinclm).
    (* Derive gm !! id = Some (Cinl (Excl ())) BEFORE consuming Htok. *)
    iDestruct (own_valid_2 with "Hgm Htok") as %Hvgm.
    apply auth_both_valid_discrete in Hvgm as [Hinclgm Hvalidgm].
    apply (singleton_included_exclusive_l gm id (Cinl (Excl ()))) in Hinclgm; [|apply _|exact Hvalidgm].
    assert (gm !! id = Some (Cinl (Excl ()))) as Hgm_id_cinl by (apply some_cinl_excl_unit_equiv_eq; exact Hinclgm).
    assert (id ∈ dom gm) as Hin by (apply elem_of_dom; rewrite Hgm_id_cinl; done).
    (* Update m: pending → done. *)
    iMod (own_update_2 _ _ _
      (● <[γ := done_val id]>m ⋅ ◯ {[γ := done_val id]})
      with "Hms H1") as "[$ Hf]".
    { apply auth_update, singleton_local_update_any.
      intros x Hx. unfold pending_val.
      apply (exclusive_local_update _ (done_val id)). done. }
    (* Update d: alloc γ → to_agree id. *)
    iMod (own_update _ _
      (● <[γ := to_agree id]>d ⋅ ◯ {[γ := to_agree id]})
      with "Hd") as "[$ #$]".
    { apply auth_update_alloc, alloc_singleton_local_update; done. }
    (* Update gm: Cinl (Excl ()) → Cinr (to_agree γ), minting id_alloc id γ. *)
    iMod (own_update_2 _ _ _
      (● <[id := Cinr (to_agree (γ : leibnizO gname))]>gm ⋅
       ◯ {[id := Cinr (to_agree (γ : leibnizO gname))]})
      with "Hgm Htok") as "[$ #Halloc]".
    { apply auth_update, singleton_local_update_any.
      intros y _. apply exclusive_local_update. done. }
    iModIntro. iFrame "Hps Hpn Hctr Hf Halloc".
    iPureIntro. split; [|split; [|split]].
    - (* dom <[id:=Cinr ...]>gm = dom gm = set_seq 0 ctr *)
      rewrite dom_insert_L (subseteq_union_1_L {[id]} (dom gm)).
      + exact Hdom.
      + by apply singleton_subseteq_l.
    - (* gm_m_coherent (<[γ:=done_val id]>m) (<[id:=Cinr (to_agree γ)]>gm) *)
      intros id' γ'. split.
      + intros Hgm'.
        destruct (decide (id' = id)) as [-> | Hne_id].
        * (* id' = id: new value Cinr (to_agree γ), so γ' = γ *)
          rewrite lookup_insert in Hgm'. injection Hgm' as Hγ'_eq.
          subst γ'. left. by rewrite lookup_insert.
        * (* id' ≠ id: old gm entry *)
          rewrite lookup_insert_ne in Hgm'; [|done].
          apply Hgmm in Hgm' as [Hm | Hm].
          -- destruct (decide (γ' = γ)) as [-> | Hne_γ].
             ++ exfalso. rewrite Hmγ_pend in Hm. discriminate.
             ++ left. rewrite lookup_insert_ne; done.
          -- destruct (decide (γ' = γ)) as [-> | Hne_γ].
             ++ exfalso. rewrite Hmγ_pend in Hm. discriminate.
             ++ right. rewrite lookup_insert_ne; done.
      + intros Hm'.
        destruct (decide (id' = id)) as [-> | Hne_id].
        * (* id' = id: need gm' !! id = Cinr (to_agree γ'), i.e. γ' = γ *)
          rewrite lookup_insert.
          assert (γ' = γ) as ->.
          { destruct Hm' as [Hm' | Hm'];
              destruct (decide (γ' = γ)) as [-> | Hne_γ]; [done| |done|].
            - rewrite lookup_insert_ne in Hm'; [|done].
              exfalso. have Hcin := proj2 (Hgmm id γ') (or_introl Hm').
              rewrite Hgm_id_cinl in Hcin. discriminate.
            - rewrite lookup_insert_ne in Hm'; [|done].
              exfalso. have Hcin := proj2 (Hgmm id γ') (or_intror Hm').
              rewrite Hgm_id_cinl in Hcin. discriminate. }
          done.
        * rewrite lookup_insert_ne; [|done]. apply Hgmm.
          destruct Hm' as [Hm' | Hm']; [left|right].
          -- destruct (decide (γ' = γ)) as [-> | Hne_γ].
             ++ rewrite lookup_insert in Hm'. injection Hm' as ->.
                exfalso. exact (Hne_id eq_refl).
             ++ rewrite lookup_insert_ne in Hm'; done.
          -- destruct (decide (γ' = γ)) as [-> | Hne_γ].
             ++ rewrite lookup_insert in Hm'. discriminate.
             ++ rewrite lookup_insert_ne in Hm'; done.
    - (* done_id_coherent (<[γ:=done_val id]>m) (<[γ:=to_agree id]>d) *)
      intros γ' n' Hdγ'.
      destruct (decide (γ' = γ)) as [-> | Hne].
      + rewrite lookup_insert in Hdγ'.
        apply Some_equiv_inj, (inj to_agree) in Hdγ'.
        fold_leibniz. subst n'. left. by rewrite lookup_insert.
      + rewrite lookup_insert_ne in Hdγ'; [|done].
        destruct (Hdid γ' n' Hdγ') as [Hmγ | Hmγ];
          [left|right]; rewrite lookup_insert_ne; done.
    - (* pending_coherent *)
      destruct Hpcoh as [Hsize Hl]. split; [exact Hsize|].
      intros γ' Hγ'. destruct (decide (γ' = γ)) as [-> | Hne].
      + exfalso. rewrite lookup_insert in Hγ'.
        rewrite /done_val /pending_val in Hγ'. by inversion Hγ'.
      + rewrite lookup_insert_ne in Hγ'; [|done]. by apply Hl.
  Qed.

  Lemma visited_transition_finished m d ps pn ctr gm γ n :
    visited_mapg_auth m d ps pn ctr gm -∗ visit_done γ n
    ==∗ visited_map_update_finished m d ps pn γ n ctr gm ∗ visit_finished γ n.
  Proof.
    iIntros "(Hms & Hd & Hps & Hpn & Hgm & Hctr & %Hdom & %Hgmm & %Hdid & %Hpcoh) [Hsfrag #Hreached]".
    iDestruct "Hreached" as "[#Hrd #Hid_alloc]".
    rewrite /visited_map_update_finished /visit_finished /visit_reached_done.
    (* Derive m !! γ = Some (done_val n) from Hms ⋅ Hsfrag, using exclusivity of done_val. *)
    iDestruct (own_valid_2 with "Hms Hsfrag") as %Hvm.
    apply auth_both_valid_discrete in Hvm as [Hinclm Hvalidm].
    apply (singleton_included_exclusive_l m γ (done_val n)) in Hinclm; [|apply _|done].
    apply some_done_val_equiv_eq in Hinclm.
    (* Hinclm : m !! γ = Some (done_val n) *)
    iDestruct (own_valid_2 with "Hd Hrd") as %Hv.
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
    iFrame "Hd Hps Hpn Hgm Hctr Hrd Hid_alloc". iPureIntro.
    split; [exact Hdom|]. split; [|split].
    - (* gm_m_coherent (<[γ := finished_val n]>m) gm: only m changes at γ *)
      intros id γ'. split.
      + intros Hgm_id. apply Hgmm in Hgm_id as [Hm | Hm].
        * destruct (decide (γ' = γ)) as [-> | Hne].
          { rewrite Hinclm in Hm. injection Hm as ->.
            right. by rewrite lookup_insert. }
          { left. by rewrite lookup_insert_ne. }
        * destruct (decide (γ' = γ)) as [-> | Hne].
          { rewrite Hinclm in Hm. discriminate. }
          { right. by rewrite lookup_insert_ne. }
      + intros [Hm | Hm].
        * destruct (decide (γ' = γ)) as [-> | Hne].
          { rewrite lookup_insert in Hm.
            rewrite /done_val /finished_val in Hm. discriminate. }
          { rewrite lookup_insert_ne in Hm; [|done]. apply Hgmm. by left. }
        * destruct (decide (γ' = γ)) as [-> | Hne].
          { rewrite lookup_insert in Hm.
            injection Hm as Hm. subst id.
            apply Hgmm. left. exact Hinclm. }
          { rewrite lookup_insert_ne in Hm; [|done]. apply Hgmm. by right. }
    - intros γ' n' Hdγ'.
      destruct (decide (γ' = γ)) as [-> | Hne].
      + specialize (Hdid γ n' Hdγ').
        rewrite Hinclm in Hdid. destruct Hdid as [Heq | Heq]; inversion Heq as [Heqn].
        subst n. right. by rewrite lookup_insert.
      + rewrite lookup_insert_ne; [|done].
        destruct (Hdid γ' n' Hdγ') as [Hmγ | Hmγ]; [by left|by right].
    - destruct Hpcoh as [Hsize Hl]. split; [exact Hsize|].
      intros γ' Hγ'. destruct (decide (γ' = γ)) as [-> | Hne].
      + exfalso. rewrite lookup_insert in Hγ'.
        rewrite /finished_val /pending_val in Hγ'. discriminate.
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

  (** [visit_done_lookup] reads off [m !! γ = Some (done_val n)] from the
      auth and a [visit_done γ n] fragment. The token-side fragment is
      exclusive at γ ([Cinl (Excl _)]), so singleton inclusion collapses to
      a pointwise equiv, and Leibniz on [optionO natO] turns equiv into
      equality. The auth and fragment are returned unchanged. *)
  Lemma visit_done_lookup γ n m d ps pn ctr gm :
    visited_mapg_auth m d ps pn ctr gm -∗ visit_done γ n -∗
      ⌜m !! γ = Some (done_val n)⌝ ∗
      visited_mapg_auth m d ps pn ctr gm ∗ visit_done γ n.
  Proof.
    iIntros "(Hms & Hd & Hps & Hpn & Hgm & Hctr & %Hdom & %Hgmm & %Hdid & %Hpcoh) [Hf #Hr]".
    iDestruct (own_valid_2 with "Hms Hf") as %Hv.
    apply auth_both_valid_discrete in Hv as [Hincl Hvalid].
    apply (singleton_included_exclusive_l m γ (done_val n)) in Hincl;
      [|apply _|exact Hvalid].
    iFrame "∗ # %". iPureIntro. by apply some_done_val_equiv_eq.
  Qed.

  (** [visit_finished_lookup] reads off [m !! γ = Some (finished_val n)]
      from the auth and a [visit_finished γ n] fragment. The fragment's
      [Cinr (to_agree n)] side at [visited_state_name] is not exclusive,
      so equiv-to-eq cannot be bridged at that resource alone. Instead we
      route through [done_id_coherent]: the persistent [visit_reached_done]
      half gives [d !! γ ≡ Some (to_agree n)], which under
      [done_id_coherent] forces [m !! γ] to be one of [done_val n] /
      [finished_val n] (with Leibniz =). The [done_val n] alternative is
      then ruled out using the state-map fragment, which would require
      [Cinr (to_agree n) ≼ Cinl (Excl (Some n))] — impossible on a csum. *)
  Lemma visit_finished_lookup γ n m d ps pn ctr gm :
    visited_mapg_auth m d ps pn ctr gm -∗ visit_finished γ n -∗
      ⌜m !! γ = Some (finished_val n)⌝ ∗
      visited_mapg_auth m d ps pn ctr gm ∗ visit_finished γ n.
  Proof.
    iIntros "(Hms & Hd & Hps & Hpn & Hgm & Hctr & %Hdom & %Hgmm & %Hdid & %Hpcoh)
            [Hf #Hr]".
    iDestruct "Hr" as "[#Hrd #Hid_alloc]".
    (* d !! γ ≡ Some (to_agree n) via auth+frag at visited_done_name. *)
    iDestruct (own_valid_2 with "Hd Hrd") as %Hvd.
    apply auth_both_valid_discrete in Hvd as [Hincl_d Hvalid_d].
    apply singleton_included_l in Hincl_d as (xd & Hxd & Hle_d).
    assert (✓ xd) as Hvxd
      by (eapply lookup_valid_Some; [exact Hvalid_d|exact Hxd]).
    assert (d !! γ ≡ Some (to_agree n)) as Hdg_eq.
    { rewrite Hxd. f_equiv.
      apply Some_included in Hle_d as [|Hinc]; [by symmetry|].
      symmetry. by apply (agree_valid_included _ _ Hvxd). }
    pose proof (Hdid γ n Hdg_eq) as Hmγ.
    (* Rule out the done_val n alternative using the state-map fragment. *)
    iDestruct (own_valid_2 with "Hms Hf") as %Hvm.
    apply auth_both_valid_discrete in Hvm as [Hincl_m _].
    apply singleton_included_l in Hincl_m as (ym & Hym & Hle_m).
    iFrame "∗ # %". iPureIntro.
    destruct Hmγ as [Hmγ | Hmγ]; [exfalso|exact Hmγ].
    rewrite Hmγ in Hym. apply Some_equiv_inj in Hym. symmetry in Hym.
    apply done_val_equiv_eq in Hym. subst ym.
    apply Some_included in Hle_m as [Heq | Hle].
    - rewrite /finished_val /done_val in Heq. by inversion Heq.
    - rewrite /finished_val /done_val in Hle.
      apply csum_included in Hle as
        [Hbot | [(?&?& Heq1 & _ & _) | (?&?& _ & Heq2 & _)]].
      + by inversion Hbot.
      + by inversion Heq1.
      + by inversion Heq2.
  Qed.

  (** Given [visit_finished γ id], no [γ'] has [m !! γ' = Some (done_val id)].
      The argument: by [gm_m_coherent], [gm !! id] uniquely determines the
      [γ'] holding [done_val id] / [finished_val id]. Combined with
      [id_alloc id γ] (carried inside [visit_finished]), [γ' = γ]. But
      [m !! γ = Some (finished_val id)] (by [visit_finished_lookup]),
      contradicting [m !! γ = Some (done_val id)]. *)
  Lemma vm_finished_no_done m d ps pn ctr gm γ id :
    visited_mapg_auth m d ps pn ctr gm -∗ visit_finished γ id -∗
      ⌜∀ γ', m !! γ' ≠ Some (done_val id)⌝ ∗
      visited_mapg_auth m d ps pn ctr gm.
  Proof.
    iIntros "Hauth #Hvf".
    iDestruct (visit_finished_lookup with "Hauth Hvf") as "(%Hmγ & Hauth & _)".
    iDestruct "Hvf" as "[_ [_ #Halloc]]".
    iDestruct "Hauth" as "(Hms & Hd & Hps & Hpn & Hgm & Hctr & %Hdom & %Hgmm & %Hdid & %Hpcoh)".
    iDestruct (own_valid_2 with "Hgm Halloc") as %Hvgm.
    apply auth_both_valid_discrete in Hvgm as [Hinclgm Hvalidgm].
    apply singleton_included_l in Hinclgm as (xgm & Hxgm & Hle).
    iSplit; last by iFrame "∗ %".
    iPureIntro. intros γ' Hcontra.
    pose proof (proj2 (Hgmm id γ') (or_introl Hcontra)) as Hgmm_id.
    rewrite Hgmm_id in Hxgm. apply Some_equiv_inj in Hxgm.
    assert (✓ xgm) as Hvxgm by (rewrite -Hxgm; done).
    apply Some_included in Hle as [Heq | Hinc].
    - rewrite -Heq in Hxgm.
      apply (inj Cinr) in Hxgm.
      apply (inj to_agree) in Hxgm.
      fold_leibniz. subst γ'.
      rewrite Hcontra in Hmγ. discriminate.
    - apply csum_included in Hinc as
        [Hbot | [(? & ? & Heq1 & _ & _) | (? & ? & Heq1 & Heq2 & Hle')]].
      + subst xgm. by inversion Hxgm.
      + by inversion Heq1.
      + injection Heq1 as <-. subst xgm.
        apply (inj Cinr) in Hxgm.
        apply (Cinr_valid (A:=exclR unitO)) in Hvxgm.
        apply (agree_valid_included _ _ Hvxgm) in Hle'.
        rewrite -Hxgm in Hle'.
        apply (inj to_agree) in Hle'.
        fold_leibniz. subst γ'.
        rewrite Hcontra in Hmγ. discriminate.
  Qed.

  (** [visit_reached_done γ n] forces [m !! γ] into the done/finished
      family at [n]. Routes through [done_id_coherent]. *)
  Lemma visit_reached_done_lookup γ n m d ps pn ctr gm :
    visited_mapg_auth m d ps pn ctr gm -∗ visit_reached_done γ n -∗
      ⌜m !! γ = Some (done_val n) ∨ m !! γ = Some (finished_val n)⌝ ∗
      visited_mapg_auth m d ps pn ctr gm.
  Proof.
    iIntros "Hauth #Hr".
    iDestruct "Hr" as "[#Hrd _]".
    iDestruct "Hauth" as "(Hms & Hd & Hps & Hpn & Hgm & Hctr & %Hdom & %Hgmm & %Hdid & %Hpcoh)".
    iDestruct (own_valid_2 with "Hd Hrd") as %Hvd.
    apply auth_both_valid_discrete in Hvd as [Hincl_d Hvalid_d].
    apply singleton_included_l in Hincl_d as (xd & Hxd & Hle_d).
    assert (✓ xd) as Hvxd
      by (eapply lookup_valid_Some; [exact Hvalid_d|exact Hxd]).
    assert (d !! γ ≡ Some (to_agree n)) as Hdg_eq.
    { rewrite Hxd. f_equiv. apply Some_included in Hle_d as [|Hinc]; [by symmetry|].
      symmetry. by apply (agree_valid_included _ _ Hvxd). }
    iSplit; last by iFrame "∗ %".
    iPureIntro. by apply (Hdid γ n).
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
    iIntros "[H1 _] [H2 _]".
    iDestruct (own_valid_2 with "H1 H2") as %Hv. iPureIntro.
    rewrite -auth_frag_op singleton_op auth_frag_valid singleton_valid in Hv.
    by apply to_agree_op_inv_L in Hv.
  Qed.

  Lemma get_visit_reached_done γ n m d ps pn ctr gm :
    d !! γ = Some (to_agree n) →
    visited_mapg_auth m d ps pn ctr gm ==∗ visited_mapg_auth m d ps pn ctr gm ∗ visit_reached_done γ n.
  Proof.
    iIntros (Hd) "(Hms & Hd_auth & Hps & Hpn & Hgm & Hctr & %Hdom & %Hgmm & %Hdid & %Hpcoh)".
    rewrite /visit_reached_done /id_alloc.
    iMod (own_update _ _ (● d ⋅ ◯ {[γ := to_agree n]}) with "Hd_auth") as "[Hd_auth #Hr]".
    { apply auth_update_dfrac_alloc; [apply _|].
      apply singleton_included_l. exists (to_agree n). split; [by rewrite Hd|].
      apply Some_included_2. by left. }
    assert (gm !! n = Some (Cinr (to_agree (γ : leibnizO gname)))) as Hgm_n.
    { apply (proj2 (Hgmm n γ)). apply (Hdid γ n). by rewrite Hd. }
    iMod (own_update _ _ (● gm ⋅ ◯ {[n := Cinr (to_agree (γ : leibnizO gname))]}) with "Hgm")
      as "[Hgm #Halloc]".
    { apply auth_update_dfrac_alloc; [apply _|].
      apply singleton_included_l. exists (Cinr (to_agree (γ : leibnizO gname))). split; [by rewrite Hgm_n|].
      apply Some_included_2. by left. }
    iModIntro. by iFrame "∗ # %".
  Qed.

  Lemma visited_reached_done_invalid γ n m d ps pn ctr gm :
    visited_mapg_auth m d ps pn ctr gm -∗ visit_reached_done γ n -∗ visit_pending γ -∗ False.
  Proof.
    iIntros "(Hms & Hd & Hps & Hpn & Hgm & Hctr & %Hdom & %Hgmm & %Hdid & %Hpcoh) [Hreached _] Hpending".
    rewrite /visit_pending.
    iDestruct (own_valid_2 with "Hd Hreached") as %Hvd.
    apply auth_both_valid_discrete in Hvd as [Hincl_d Hvalid_d].
    apply singleton_included_l in Hincl_d as (xd & Hxd & Hle_d).
    assert (✓ xd) as Hvxd
      by (eapply lookup_valid_Some; [exact Hvalid_d|exact Hxd]).
    assert (d !! γ ≡ Some (to_agree n)) as Hdg_eq.
    { rewrite Hxd. f_equiv. apply Some_included in Hle_d as [|Hinc]; [by symmetry|].
      symmetry. by apply (agree_valid_included _ _ Hvxd). }
    pose proof (Hdid γ n Hdg_eq) as Hmγ.
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
        exfalso. apply (exclusive_included (Excl None) (Excl (Some n))); done.
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

  Lemma pending_set_remove m d ps pn ctr gm γs :
    visited_mapg_auth m d ps pn ctr gm -∗ pencount_frag pn -∗ penset_frag γs -∗
    ([∗ set] γ ∈ γs, ∃ n, visit_reached_done γ n) ==∗
    visited_mapg_pending_removed m d ps pn γs ctr gm ∗ pencount_frag (pn - size γs).
  Proof.
    iIntros "(Hms & Hd & Hps & Hpn1 & Hgm & Hctr & %Hdom & %Hgmm & %Hdid & %Hpcoh) Hpn2 Hfrag #Hreached".
    iAssert (⌜∀ γ, γ ∈ γs →
              ∃ n, m !! γ = Some (done_val n) ∨ m !! γ = Some (finished_val n)⌝)%I
      as %Hmγs.
    { iIntros (γ Hin).
      iDestruct (big_sepS_elem_of with "Hreached") as (n) "Hr"; first done.
      iDestruct "Hr" as "[Hr _]".
      iDestruct (own_valid_2 with "Hd Hr") as %Hvd.
      apply auth_both_valid_discrete in Hvd as [Hincl Hvalid_d].
      apply singleton_included_l in Hincl as (xd & Hxd & Hle).
      iPureIntro.
      assert (✓ xd) as Hvxd
        by (eapply lookup_valid_Some; [exact Hvalid_d|exact Hxd]).
      assert (d !! γ ≡ Some (to_agree n)) as Hdg_eq.
      { rewrite Hxd. f_equiv. apply Some_included in Hle as [|Hinc]; [by symmetry|].
        symmetry. by apply (agree_valid_included _ _ Hvxd). }
      exists n. apply (Hdid γ n Hdg_eq). }
    rewrite /visited_mapg_pending_removed /penset_frag.
    iCombine "Hps Hfrag" as "Hpsfull".
    iDestruct (own_valid with "Hpsfull") as %Hv.
    apply auth_both_valid_discrete in Hv as [Hincl%gset_disj_included _].
    iMod (own_update with "Hpsfull") as "Hps'".
    { apply auth_update_dealloc, gset_disj_dealloc_local_update. }
    iMod (pn_update pn (pn - size γs) with "Hpn1 Hpn2") as "[Hpn1 Hpn2]".
    iModIntro. iFrame "Hms Hd Hps' Hpn1 Hpn2 Hgm Hctr". iPureIntro.
    split; [exact Hdom|]. split; [exact Hgmm|]. split; [exact Hdid|].
    destruct Hpcoh as [Hsz Hpcoh].
    split.
    - rewrite (size_difference _ _ Hincl) -Hsz //.
    - intros γ' Hm. specialize (Hpcoh γ' Hm).
      destruct (decide (γ' ∈ γs)) as [Hin | Hnin].
      + exfalso. destruct (Hmγs _ Hin) as (n & [Hmγ | Hmγ]);
          rewrite Hmγ in Hm;
          rewrite /done_val /finished_val /pending_val in Hm;
          by inversion Hm.
      + by apply elem_of_difference.
  Qed.

  (** [id_token id] witnesses that no [γ] in [m] maps to [done_val id]
      or [finished_val id] — id is unused in the visited map. *)
  Lemma id_token_unused m d ps pn ctr gm id :
    visited_mapg_auth m d ps pn ctr gm -∗ id_token id -∗
      ⌜∀ γ,
          m !! γ ≠ Some (done_val id) ∧
          m !! γ ≠ Some (finished_val id)⌝ ∗
      visited_mapg_auth m d ps pn ctr gm ∗ id_token id.
  Proof.
    iIntros "(Hms & Hd & Hps & Hpn & Hgm & Hctr & %Hdom & %Hgmm & %Hdid & %Hpcoh) Htok".
    iDestruct (own_valid_2 with "Hgm Htok") as %Hvgm.
    apply auth_both_valid_discrete in Hvgm as [Hinclgm Hvalidgm].
    apply (singleton_included_exclusive_l gm id (Cinl (Excl ()))) in Hinclgm; [|apply _|exact Hvalidgm].
    assert (gm !! id = Some (Cinl (Excl ()))) as Hgm_id by (apply some_cinl_excl_unit_equiv_eq; exact Hinclgm).
    iFrame "∗ %". iPureIntro. intros γ. split.
    - intros Hmγ.
      have Hcin := proj2 (Hgmm id γ) (or_introl Hmγ).
      rewrite Hgm_id in Hcin. discriminate.
    - intros Hmγ.
      have Hcin := proj2 (Hgmm id γ) (or_intror Hmγ).
      rewrite Hgm_id in Hcin. discriminate.
  Qed.

  (** Auth-free: [id_token id] and [visit_reached_done γ id] conflict directly
      at [pending_id_name] via [Cinl (Excl ()) ⋅ Cinr _] = CsumBot. *)
  Lemma id_token_visit_reached_done_invalid γ id :
    id_token id -∗ visit_reached_done γ id -∗ False.
  Proof.
    iIntros "Htok [_ Halloc]".
    iApply (id_token_alloc_invalid with "Htok Halloc").
  Qed.

  (** Auth-free: two [visit_reached_done] at the same [id] force agreement
      on [γ] via [to_agree γ1 ⋅ to_agree γ2] valid implies [γ1 = γ2]. *)
  Lemma visit_reached_done_inj γ1 γ2 id :
    visit_reached_done γ1 id -∗ visit_reached_done γ2 id -∗ ⌜γ1 = γ2⌝.
  Proof.
    iIntros "[_ H1] [_ H2]".
    iApply (id_alloc_agree with "H1 H2").
  Qed.

  (** [id_ctr_frag_alloc] allocates the next fresh id. It takes the auth
      (for the gm-auth and the in-auth counter half) together with the
      external [id_ctr_frag ctr]. Returns the updated auth, a new
      [id_ctr_frag (S ctr)], and [id_token ctr] for the freshly-allocated id. *)
  Lemma id_ctr_frag_alloc m d ps pn ctr gm :
    visited_mapg_auth m d ps pn ctr gm -∗ id_ctr_frag ctr ==∗
      visited_mapg_auth m d ps pn (S ctr) (<[ctr := Cinl (Excl ())]>gm) ∗
      id_ctr_frag (S ctr) ∗ id_token ctr.
  Proof.
    iIntros "(Hms & Hd & Hps & Hpn & Hgm & Hctr & %Hdom & %Hgmm & %Hdid & %Hpcoh) Hid_ctr".
    rewrite /id_ctr_frag /id_token.
    assert (gm !! ctr = None) as Hgm_ctr.
    { apply not_elem_of_dom. rewrite Hdom. intro H.
      apply elem_of_set_seq in H. lia. }
    iCombine "Hctr Hid_ctr" as "Hctr_full".
    iMod (own_update with "Hctr_full") as "[Hctr Hid_ctr']".
    { apply frac_agree_update_2. by rewrite Qp.half_half. }
    iMod (own_update _ _
      (● <[ctr := Cinl (Excl ())]>gm ⋅ ◯ {[ctr := Cinl (Excl ())]})
      with "Hgm") as "[Hgm Htok]".
    { apply auth_update_alloc.
      apply alloc_singleton_local_update; [rewrite Hgm_ctr; done | done]. }
    iModIntro. iFrame "Hms Hd Hps Hpn Hgm Hctr Hid_ctr' Htok". iPureIntro.
    split; [|split; [|split]].
    - rewrite dom_insert_L Hdom -(set_seq_S_end_union_L 0) /=. set_solver.
    - intros id γ'. split.
      + intros Hgm'.
        destruct (decide (id = ctr)) as [-> | Hne].
        * rewrite lookup_insert in Hgm'. discriminate.
        * rewrite lookup_insert_ne in Hgm'; [|done]. apply Hgmm. exact Hgm'.
      + intros [Hm | Hm].
        * destruct (decide (id = ctr)) as [-> | Hne].
          { exfalso. have Hcin := proj2 (Hgmm ctr γ') (or_introl Hm).
            rewrite Hgm_ctr in Hcin. discriminate. }
          { rewrite lookup_insert_ne; [|done]. apply Hgmm. by left. }
        * destruct (decide (id = ctr)) as [-> | Hne].
          { exfalso. have Hcin := proj2 (Hgmm ctr γ') (or_intror Hm).
            rewrite Hgm_ctr in Hcin. discriminate. }
          { rewrite lookup_insert_ne; [|done]. apply Hgmm. by right. }
    - exact Hdid.
    - exact Hpcoh.
  Qed.

  (** [id_token id] implies [id < ctr]: the id has been allocated (is in
      [dom gm = set_seq 0 ctr]) so it is strictly below the counter. *)
  Lemma id_token_lt_ctr m d ps pn ctr gm id :
    visited_mapg_auth m d ps pn ctr gm -∗ id_token id -∗
      ⌜id < ctr⌝ ∗ visited_mapg_auth m d ps pn ctr gm ∗ id_token id.
  Proof.
    iIntros "(Hms & Hd & Hps & Hpn & Hgm & Hctr & %Hdom & %Hgmm & %Hdid & %Hpcoh) Htok".
    iDestruct (own_valid_2 with "Hgm Htok") as %Hvgm.
    apply auth_both_valid_discrete in Hvgm as [Hinclgm Hvalidgm].
    apply singleton_included_l in Hinclgm as (x & Hx & _).
    assert (id ∈ dom gm) as Hin.
    { apply elem_of_dom. destruct (gm !! id) as [y|] eqn:Heq.
      - by exists y.
      - rewrite Heq in Hx. inversion Hx. }
    iFrame "∗ %". iPureIntro.
    rewrite Hdom in Hin. apply elem_of_set_seq in Hin. lia.
  Qed.

End visited_map_res.

(* Each [loc] in the lg_map is in one of two states:
   - [Cinl (to_agree ())]   — explicitly unallocated (filled tauth leaf)
   - [Cinr (to_agree γ)]    — allocated to [γ] (suspended tauth leaf)
   Both states use [agreeR], so fragments are persistent and a single [loc]
   cannot be in both states simultaneously ([Cinl · Cinr] is invalid). *)
Definition lg_mapEntry := csumR (agreeR unitO) (agreeR (leibnizO gname)).
Definition lg_mapUR := authR (gmapUR loc lg_mapEntry).
Class lg_mapG Σ := Lg_mapG {
  lg_map_inG :> inG Σ lg_mapUR;
  lg_mapG_v_name : gname;
  lg_mapG_p_name : gname;
}.

Definition lg_p_meta_n : namespace := nroot .@ "lg_p_meta".

Section lg_map.
  Context `{!lg_mapG Σ, !spec_metaG Σ, !heapGS Σ}.

  Definition lg_mapg_type := gmap loc lg_mapEntry.

  (** Combined verifier+prover authority. [m_v] is the verifier-side
      ghost map and [m_p] the prover-side. The verifier-side is gated by
      [vmeta_token] freshness via [own spec_meta_name (◯ GSet (dom m_v))];
      the prover-side is gated by [meta_token l ⊤] freshness via the
      bigsep of [meta l lg_p_meta_n (true : bool)] over [dom m_p]. *)
  Definition lg_mapg_auth (m_v m_p : lg_mapg_type) : iProp Σ :=
    own lg_mapG_v_name (● m_v) ∗
    own spec_meta_name (◯ GSet (dom m_v)) ∗
    own lg_mapG_p_name (● m_p) ∗
    ([∗ set] l ∈ dom m_p, meta l lg_p_meta_n (true : bool)).

  (* Verifier-side fragments. *)
  Definition lg_mapg_frag l γ : iProp Σ :=
    own lg_mapG_v_name (◯ {[ l := Cinr (to_agree γ) ]}).

  Definition lg_mapg_unalloc l : iProp Σ :=
    own lg_mapG_v_name (◯ {[ l := Cinl (to_agree ()) ]}).

  (* Prover-side fragments. *)
  Definition lg_mapg_p_frag l γ : iProp Σ :=
    own lg_mapG_p_name (◯ {[ l := Cinr (to_agree γ) ]}).

  Definition lg_mapg_p_unalloc l : iProp Σ :=
    own lg_mapG_p_name (◯ {[ l := Cinl (to_agree ()) ]}).

  Global Instance lg_mapg_frag_persistent l γ : Persistent (lg_mapg_frag l γ).
  Proof. apply _. Qed.

  Global Instance lg_mapg_unalloc_persistent l : Persistent (lg_mapg_unalloc l).
  Proof. apply _. Qed.

  Global Instance lg_mapg_p_frag_persistent l γ : Persistent (lg_mapg_p_frag l γ).
  Proof. apply _. Qed.

  Global Instance lg_mapg_p_unalloc_persistent l : Persistent (lg_mapg_p_unalloc l).
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

  (** Combined [vmeta_token l ∗ own spec_meta_name (◯ GSet (dom m))]
      proves [l ∉ dom m] via [gset_disj] validity, and the merged
      fragment becomes [◯ GSet (dom m ∪ {[l]})] which equals
      [◯ GSet (dom (<[l := _]> m))]. Used by both verifier insert variants. *)
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

  Lemma lg_mapg_insert m_v m_p l γ :
    vmeta_token l -∗ lg_mapg_auth m_v m_p ==∗
      lg_mapg_auth (<[ l := Cinr (to_agree γ) ]> m_v) m_p ∗ lg_mapg_frag l γ.
  Proof.
    rewrite /lg_mapg_auth /lg_mapg_frag.
    iIntros "Hvtok (Hauth_v & Hsmeta & Hauth_p & Hbig_p)".
    iDestruct (vmeta_combine_dom m_v l (Cinr (to_agree γ))
               with "Hvtok Hsmeta") as "[%Hl_nin Hsmeta']".
    apply not_elem_of_dom in Hl_nin.
    iMod (own_update with "Hauth_v") as "[$ $]";
      last by iModIntro; iFrame "Hsmeta' Hauth_p Hbig_p".
    apply auth_update_alloc.
    by apply alloc_singleton_local_update.
  Qed.

  Lemma lg_mapg_insert_unalloc m_v m_p l :
    vmeta_token l -∗ lg_mapg_auth m_v m_p ==∗
      lg_mapg_auth (<[ l := Cinl (to_agree ()) ]> m_v) m_p ∗ lg_mapg_unalloc l.
  Proof.
    rewrite /lg_mapg_auth /lg_mapg_unalloc.
    iIntros "Hvtok (Hauth_v & Hsmeta & Hauth_p & Hbig_p)".
    iDestruct (vmeta_combine_dom m_v l (Cinl (to_agree ()))
               with "Hvtok Hsmeta") as "[%Hl_nin Hsmeta']".
    apply not_elem_of_dom in Hl_nin.
    iMod (own_update with "Hauth_v") as "[$ $]";
      last by iModIntro; iFrame "Hsmeta' Hauth_p Hbig_p".
    apply auth_update_alloc.
    by apply alloc_singleton_local_update.
  Qed.

  Lemma lg_mapg_p_insert m_v m_p l γ :
    meta_token l ⊤ -∗ lg_mapg_auth m_v m_p ==∗
      lg_mapg_auth m_v (<[ l := Cinr (to_agree γ) ]> m_p) ∗ lg_mapg_p_frag l γ.
  Proof.
    rewrite /lg_mapg_auth /lg_mapg_p_frag.
    iIntros "Hmtok (Hauth_v & Hsmeta & Hauth_p & Hbig_p)".
    iMod (meta_combine_dom m_p l (Cinr (to_agree γ)) with "Hmtok Hbig_p")
      as "[%Hl_nin Hbig_p']".
    apply not_elem_of_dom in Hl_nin.
    iMod (own_update with "Hauth_p") as "[$ $]";
      last by iModIntro; iFrame "Hauth_v Hsmeta Hbig_p'".
    apply auth_update_alloc.
    by apply alloc_singleton_local_update.
  Qed.

  Lemma lg_mapg_p_insert_unalloc m_v m_p l :
    meta_token l ⊤ -∗ lg_mapg_auth m_v m_p ==∗
      lg_mapg_auth m_v (<[ l := Cinl (to_agree ()) ]> m_p) ∗ lg_mapg_p_unalloc l.
  Proof.
    rewrite /lg_mapg_auth /lg_mapg_p_unalloc.
    iIntros "Hmtok (Hauth_v & Hsmeta & Hauth_p & Hbig_p)".
    iMod (meta_combine_dom m_p l (Cinl (to_agree ())) with "Hmtok Hbig_p")
      as "[%Hl_nin Hbig_p']".
    apply not_elem_of_dom in Hl_nin.
    iMod (own_update with "Hauth_p") as "[$ $]";
      last by iModIntro; iFrame "Hauth_v Hsmeta Hbig_p'".
    apply auth_update_alloc.
    by apply alloc_singleton_local_update.
  Qed.

End lg_map.

(** [mapEntry]: per-key state. [Cinl (to_frac_agree q v)] is an alive
    entry with fractional ownership of value [v]; [Cinr (to_agree ())]
    is a tombstone — a persistent "this key has been removed" marker.
    Once [k] transitions Cinl → Cinr at [mapg_remove], the persistent
    [mapg_removed k] fragment forces the auth's [k] entry to remain
    [Cinr] forever, so the key cannot become alive again. *)
Definition mapEntry := csumR (dfrac_agreeR valO) (agreeR unitO).
Definition mapUR := authR (gmapUR nat mapEntry).
Class mapG Σ := MapG { map_inG :> inG Σ mapUR; mapG_name : gname }.

Section map_res.
  Context `{!mapG Σ}.

  Definition mapg_type := gmap nat mapEntry.

  Definition mapg_auth (m : mapg_type) : iProp Σ :=
    own mapG_name (● m).

  Definition mapg_insert_def (m : mapg_type) k v : mapg_type :=
    <[ k := Cinl (to_frac_agree 1 v) ]> m.

  (** Alive fragment: fraction [q] for key [k] and value [v]. A full
      fraction [q = 1] is exclusive (since [to_frac_agree 1 v] is
      exclusive in [dfrac_agreeR]) and permits removal. *)
  Definition mapg_frag (k : nat) (q : Qp) (v : val) : iProp Σ :=
    own mapG_name (◯ {[ k := Cinl (to_frac_agree q v) ]}).

  (** Persistent tombstone: witness that [k] was removed and will
      never be alive again. Minted by [mapg_remove]. *)
  Definition mapg_removed (k : nat) : iProp Σ :=
    own mapG_name (◯ {[ k := Cinr (to_agree ()) ]}).

  Global Instance mapg_removed_persistent k : Persistent (mapg_removed k).
  Proof. apply _. Qed.

  Lemma mapg_frag_op k q1 q2 v :
    mapg_frag k (q1 + q2) v ⊣⊢ mapg_frag k q1 v ∗ mapg_frag k q2 v.
  Proof.
    rewrite /mapg_frag -own_op -auth_frag_op singleton_op.
    by rewrite -Cinl_op -frac_agree_op.
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
    rewrite -auth_frag_op auth_frag_valid singleton_op singleton_valid -Cinl_op
      Cinl_valid in Hv.
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

  (** Alive fragment forces the auth to have a [Cinl] entry agreeing on
      the value. Replaces the old [mapg_subset]. *)
  Lemma mapg_auth_alive m k q v :
    mapg_auth m -∗ mapg_frag k q v -∗
      ⌜∃ y, m !! k ≡ Some (Cinl y) ∧ y.2 ≡ to_agree v⌝.
  Proof.
    rewrite /mapg_auth /mapg_frag. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv. iPureIntro.
    apply auth_both_valid_discrete in Hv as [Hincl Hvm].
    apply singleton_included_l in Hincl as (y & Hy & Hle).
    assert (✓ y) as Hvy.
    { eapply (lookup_valid_Some _ k); [done|by rewrite Hy]. }
    apply Some_included in Hle as [Heq | Hinc].
    - destruct y as [[d a]| |]; [|by inversion Heq|by inversion Heq].
      apply (inj Cinl) in Heq. destruct Heq as [_ Ha]. simpl in Ha.
      exists (d, a). split; [done|]. by symmetry.
    - apply csum_included in Hinc
        as [Hbot | [(? & y' & Hil & -> & Hle)|(? & ? & Hbad & _)]].
      + by rewrite Hbot in Hvy.
      + injection Hil as <-. destruct y' as [d a].
        apply pair_included in Hle as [_ Ha'].
        apply (Cinl_valid (B:=agreeR unitO)) in Hvy as [_ Hva].
        apply (agree_valid_included _ _ Hva) in Ha'.
        exists (d, a). split; [done|by symmetry].
      + inversion Hbad.
  Qed.

  (** Auth-side query for tombstones: removed witness implies the auth's
      [k] entry is on the [Cinr] branch (i.e. tombstoned). *)
  Lemma mapg_auth_removed m k :
    mapg_auth m -∗ mapg_removed k -∗
      ⌜∃ a : agree unit, m !! k = Some (Cinr a)⌝.
  Proof.
    rewrite /mapg_auth /mapg_removed. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv. iPureIntro.
    apply auth_both_valid_discrete in Hv as [Hincl Hvm].
    apply singleton_included_l in Hincl as (y & Hy & Hle).
    assert (✓ y) as Hvy.
    { eapply (lookup_valid_Some _ k); [done|by rewrite Hy]. }
    destruct (m !! k) as [x|] eqn:Hk; last first.
    { rewrite Hk in Hy. by inversion Hy. }
    rewrite Hk in Hy. apply Some_equiv_inj in Hy.
    destruct x as [|a'|].
    - (* Cinl: derive contradiction from Cinr ≼ Cinl. *)
      exfalso. apply Some_included in Hle as [Heq | Hinc].
      + rewrite -Hy in Heq. by inversion Heq.
      + rewrite -Hy in Hinc.
        apply csum_included in Hinc
          as [Hbot | [(? & ? & Hxeq & _) | (? & ? & _ & Hyeq & _)]].
        * by inversion Hbot.
        * by inversion Hxeq.
        * by inversion Hyeq.
    - by exists a'.
    - exfalso. revert Hvy. by rewrite -Hy.
  Qed.

  (** Auth-free conflict: alive ∗ removed at the same key is False.
      Mirror of [lg_mapg_frag_unalloc_excl]. *)
  Lemma mapg_frag_removed_excl k q v :
    mapg_frag k q v -∗ mapg_removed k -∗ False.
  Proof.
    rewrite /mapg_frag /mapg_removed. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    rewrite -auth_frag_op auth_frag_valid singleton_op singleton_valid in Hv.
    done.
  Qed.

  (** Removal: full fraction [q = 1] transitions Cinl → Cinr; mints a
      persistent [mapg_removed k] witness. *)
  Lemma mapg_remove m k v :
    mapg_auth m -∗ mapg_frag k 1 v ==∗
      mapg_auth (<[ k := Cinr (to_agree ()) ]> m) ∗ mapg_removed k.
  Proof.
    rewrite /mapg_auth /mapg_frag /mapg_removed. iIntros "H1 H2".
    iMod (own_update_2 _ _ _
      (● <[ k := Cinr (to_agree ()) ]> m ⋅
       ◯ {[ k := Cinr (to_agree ()) ]})
      with "H1 H2") as "[$ $]"; last done.
    apply auth_update, singleton_local_update_any.
    intros y _. apply exclusive_local_update. done.
  Qed.

  (** [mapg_alive m] is the alive subset of [m]: keys mapping to [Cinl _]
      are kept (with the underlying [dfrac_agreeR valO] value), tombstones
      are dropped. Lets consumers iterate only over live entries. *)
  Definition mapg_alive (m : mapg_type) : gmap nat (dfrac_agreeR valO) :=
    omap (λ e, match e with
               | Cinl x => Some x
               | _      => None
               end) m.

  Lemma mapg_alive_insert m k v :
    mapg_alive (<[ k := Cinl (to_frac_agree 1 v) ]> m)
      = <[ k := to_frac_agree 1 v ]> (mapg_alive m).
  Proof. apply (omap_insert_Some _ _ _ _ (to_frac_agree 1 v)). done. Qed.

  Lemma mapg_alive_remove m k :
    mapg_alive (<[ k := Cinr (to_agree ()) ]> m)
      = delete k (mapg_alive m).
  Proof. apply omap_insert_None. done. Qed.

  (** Membership: a [Cinl] entry in [m] surfaces in the alive view. *)
  Lemma mapg_alive_lookup_Cinl m k x y :
    m !! k = Some x → x ≡ Cinl y →
    ∃ y', mapg_alive m !! k = Some y' ∧ y' ≡ y.
  Proof.
    intros Hm Heq. rewrite /mapg_alive lookup_omap Hm /=.
    destruct x as [x'| |]; [|by inversion Heq|by inversion Heq].
    apply (inj Cinl) in Heq. by exists x'.
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
  (* tern_state represents the good case.
    un_state represents the bad case.
    Explained in more detail later. *)
  Definition tern_state := state None.
  Definition un_state := own stateG_name (●□ (Some () : state_car)).

  Global Instance un_state_persistent : Persistent un_state.
  Proof. apply _. Qed.

  Lemma state_agree (o o' : state_car) :
    state o -∗ state o' -∗ ⌜o' = o⌝ ∗ state o ∗ state o'.
  Proof.
    rewrite /state. iIntros "H1 H2". iCombine "H1 H2" as "H".
    iDestruct (own_valid with "H") as %Hv.
    apply auth_auth_dfrac_op_valid in Hv as [_ [Heq _]].
    iDestruct "H" as "[H1 H2]". iFrame.
    iPureIntro. symmetry. apply leibniz_equiv. exact Heq.
  Qed.

  Lemma state_un_agree (o : state_car) :
    state o -∗ un_state -∗ ⌜o = Some tt⌝ ∗ state o.
  Proof.
    rewrite /state /un_state.
    iIntros "H1 #H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    apply auth_auth_dfrac_op_valid in Hv as [_ [Heq _]].
    iFrame "H1". iPureIntro. apply leibniz_equiv. exact Heq.
  Qed.

  Lemma tern_state_un_state_excl :
    tern_state -∗ un_state -∗ False.
  Proof.
    iIntros "H1 #H2".
    iDestruct (state_un_agree with "H1 H2") as "[%Heq _]". done.
  Qed.

  Lemma state_update_bad :
    tern_state -∗ tern_state ==∗ un_state.
  Proof.
    rewrite /tern_state /un_state /state.
    iIntros "H1 H2". iCombine "H1 H2" as "H".
    iMod (own_update with "H") as "H".
    { apply (auth_update_auth None (Some ()) (Some ())).
      apply alloc_option_local_update. done. }
    iMod (own_update with "H") as "#H".
    { apply auth_update_auth_persist. }
    by iFrame "#".
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
