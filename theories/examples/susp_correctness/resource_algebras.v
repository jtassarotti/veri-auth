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
  authUR (gmap gname (csumR (exclR (optionO natO)) (agreeR unitO))).
Definition visited_done_mapUR :=
  authUR (gmap gname (agreeR unitO)).
Definition pending_setUR :=
  authUR (gset_disjUR gname).
Definition pendingnUR := dfrac_agreeR natO.
(** [id_alloc_entry]: the per-id state of the alloc map. [Cinl (Excl ())]
    is the consumable [id_token]; [Cinr (to_agree γ)] is the binding of
    [id] to [γ] inside the auth (no longer exposed as a named iProp). *)
Definition id_alloc_entry := csumR (exclR unitO) (agreeR (leibnizO gname)).
Definition pending_idUR :=
  authUR (gmapUR nat id_alloc_entry).
Definition idCounterUR := dfrac_agreeR natO.

(* Each [loc] in the lg_map is in one of two states:
   - [Cinl (to_agree (tt : unitO))]   — explicitly unallocated (filled tauth leaf)
   - [Cinr (to_agree γ)]    — allocated to [γ] (suspended tauth leaf)
   Both states use [agreeR], so fragments are persistent and a single [loc]
   cannot be in both states simultaneously ([Cinl · Cinr] is invalid). *)
Definition lg_mapEntry := csumR (agreeR unitO) (agreeR (leibnizO gname)).
Definition lg_mapUR := authR (gmapUR loc lg_mapEntry).
Definition lg_mapg_type := gmap loc lg_mapEntry.

(** [mapEntry]: per-key state. [Cinl (to_frac_agree q v)] is an alive
    entry with fractional ownership of value [v]; [Cinr (to_agree (tt : unitO))]
    is a tombstone — a persistent "this key has been removed" marker.
    Once [k] transitions Cinl → Cinr at [mapg_remove], the persistent
    [mapg_removed k] fragment forces the auth's [k] entry to remain
    [Cinr] forever, so the key cannot become alive again. *)
Definition mapEntry := csumR (dfrac_agreeR valO) (agreeR unitO).
Definition mapUR := authR (gmapUR nat mapEntry).

Definition capUR := authR (gmapUR nat (agreeR natO)).

Definition pvalmapUR := authR (gmapUR nat (agreeR locO)).

(* [id_refUR]: a functional ghost map [nat → nat] indexing each "from"
   id to a single "to" id. The map is persistent agreement-typed:
   two fragments at the same [from] force agreement on [to]
   via [agreeR (leibnizO nat)]. Used in tandem with [pvalmap] and
   [lg_map_v]: the pure invariant [id_ref_coherent] (in
   [visited_mapg_auth]) requires [to < from] and that the susp loc
   recorded for [from] in [pvm] differs from the susp loc for [to]. *)
Definition id_refUR := authR (gmapUR nat (agreeR natO)).

Definition intransitUR := fracR.

Definition stateUR := authUR (optionUR unitO).

(* Single-instance token with two states:
   - [None]   — unparameterized state
   - [Some n] — state parameterized by [n : nat].
   The full fraction (1) is exclusive; any two fragments agree on the
   carried [option nat] and split/combine via fractional ownership.
   At full fraction the value can be updated (e.g. unparameterized to
   [Some n] or vice versa). *)
Definition stateTokUR := dfrac_agreeR (leibnizO (option nat)).

(* Per-loc two-state ghost. Tracks whether a suspended location has been
   filled or not. Each loc is bound to a fresh ghost name [γ] (via
   [suspfilledmap], a loc → gname auth tracked by [vmeta_token] freshness);
   the per-γ state lives at that γ:
   - [Cinl (Excl ())]   — unfilled, exclusive token (no fractional ownership).
   - [Cinr (to_agree (tt : unitO))] — filled, persistent.
   The two states are mutually exclusive at the same [γ]
   ([Cinl _ ⋅ Cinr _ = CsumBot]). *)
Definition suspfilledStateUR := csumR (exclR unitO) (agreeR unitO).
Definition suspfilledmapUR := authUR (gmapUR loc (agreeR gnameO)).

Class correctnessG Σ := CorrectnessG {
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

  lg_map_inG :> inG Σ lg_mapUR;
  lg_mapG_v_name : gname;
  lg_mapG_p_name : gname;

  map_inG :> inG Σ mapUR;
  mapG_name : gname;

  cap_inG :> inG Σ capUR; 
  capG_name : gname;

  pvalmap_inG :> inG Σ pvalmapUR;
  pvalmapG_name : gname;

  id_ref_inG :> inG Σ id_refUR;
  id_refG_name : gname;

  intransit_inG :> inG Σ intransitUR;
  intransitG_name : gname;

  state_inG :> inG Σ stateUR;
  stateG_name : gname;

  state_tok_inG :> inG Σ stateTokUR;
  state_tok_name : gname;

  suspfilledmap_inG :> inG Σ suspfilledmapUR;
  suspfilledmapG_name : gname;

  suspfilledState_inG :> inG Σ suspfilledStateUR;
}.

Section pvalmap_res.
  Context `{!correctnessG Σ}.

  Definition pvalmap_type := gmap nat (agree loc).

  Definition pvalmap_auth (m : pvalmap_type) : iProp Σ :=
    own pvalmapG_name (● m).

  Definition pval_frag (k : nat) (susp : loc) : iProp Σ :=
    own pvalmapG_name (◯ {[ k := to_agree susp ]}).

  Global Instance pval_frag_persistent k susp : Persistent (pval_frag k susp).
  Proof. apply _. Qed.

  Global Instance pval_frag_timeless k susp : Timeless (pval_frag k susp).
  Proof. apply _. Qed.

  Lemma pval_frag_agree k susp1 susp2 :
    pval_frag k susp1 -∗ pval_frag k susp2 -∗ ⌜susp1 = susp2⌝.
  Proof.
    rewrite /pval_frag. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv. iPureIntro.
    rewrite -auth_frag_op auth_frag_valid singleton_op singleton_valid in Hv.
    fold_leibniz. by apply to_agree_op_inv_L in Hv.
  Qed.

  Lemma pvalmap_auth_frag m k susp :
    pvalmap_auth m -∗ pval_frag k susp -∗
      ⌜∃ a, m !! k = Some a ∧ to_agree susp ≼ a⌝.
  Proof.
    rewrite /pvalmap_auth /pval_frag. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv. iPureIntro.
    apply auth_both_valid_discrete in Hv as [Hincl _].
    apply singleton_included_l in Hincl as (y & Hy & Hle).
    destruct (m !! k) as [a|] eqn:Hk; last first.
    { rewrite Hk in Hy. by inversion Hy. }
    rewrite Hk in Hy. apply Some_equiv_inj in Hy.
    exists a. split; [done|].
    apply Some_included in Hle as [Heq | Hinc].
    - rewrite -Hy in Heq. by rewrite Heq.
    - by rewrite -Hy in Hinc.
  Qed.

  Lemma pvalmap_auth_frag_eq m k susp :
    pvalmap_auth m -∗ pval_frag k susp -∗
      ⌜m !! k ≡ Some (to_agree susp)⌝.
  Proof.
    iIntros "Hauth Hfrag".
    rewrite /pvalmap_auth /pval_frag.
    iDestruct (own_valid_2 with "Hauth Hfrag") as %Hv. iPureIntro.
    apply auth_both_valid_discrete in Hv as [Hincl Hval].
    apply singleton_included_l in Hincl as (y & Hy & Hle).
    rewrite Hy. f_equiv.
    apply Some_included in Hle as [Heq | Hinc]; [by symmetry|].
    assert (✓ y) as Hvy.
    { eapply (lookup_valid_Some _ k); [done|by rewrite Hy]. }
    symmetry. by apply (agree_valid_included _ _ Hvy).
  Qed.

End pvalmap_res.


Section id_ref_res.
  Context `{!correctnessG Σ}.

  Definition id_ref_type := gmap nat nat.

  Definition id_ref_auth (rs : id_ref_type) : iProp Σ :=
    own id_refG_name (● ((to_agree : nat → agree nat) <$> rs : gmap nat _)).

  Definition id_ref_frag (from to : nat) : iProp Σ :=
    own id_refG_name (◯ {[ from := to_agree to ]}).

  Global Instance id_ref_frag_persistent from to : Persistent (id_ref_frag from to).
  Proof. apply _. Qed.

  Global Instance id_ref_frag_timeless from to : Timeless (id_ref_frag from to).
  Proof. apply _. Qed.

  Lemma id_ref_frag_agree from to1 to2 :
    id_ref_frag from to1 -∗ id_ref_frag from to2 -∗ ⌜to1 = to2⌝.
  Proof.
    rewrite /id_ref_frag. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv. iPureIntro.
    rewrite -auth_frag_op auth_frag_valid singleton_op singleton_valid in Hv.
    fold_leibniz. by apply to_agree_op_inv_L in Hv.
  Qed.

  Lemma id_ref_auth_frag rs from to :
    id_ref_auth rs -∗ id_ref_frag from to -∗ ⌜rs !! from = Some to⌝.
  Proof.
    rewrite /id_ref_auth /id_ref_frag. iIntros "Hauth Hfrag".
    iDestruct (own_valid_2 with "Hauth Hfrag") as %Hv. iPureIntro.
    apply auth_both_valid_discrete in Hv as [Hincl Hval].
    apply singleton_included_l in Hincl as (y & Hy & Hle).
    rewrite lookup_fmap in Hy.
    destruct (rs !! from) as [to'|] eqn:Hr; last first.
    { rewrite Hr /= in Hy. by inversion Hy. }
    rewrite Hr /= in Hy.
    apply Some_equiv_inj in Hy.
    assert (✓ y) as Hvy.
    { eapply (lookup_valid_Some _ from); first exact Hval.
      rewrite lookup_fmap Hr /=. by rewrite Hy. }
    apply Some_included in Hle as [Heq | Hinc].
    - rewrite -Hy in Heq. fold_leibniz. apply (inj to_agree) in Heq.
      by rewrite Heq.
    - rewrite -Hy in Hinc.
      apply to_agree_included in Hinc.
      fold_leibniz. by rewrite Hinc.
  Qed.

End id_ref_res.


Section visited_map_res.
  Context `{!correctnessG Σ, !spec_metaG Σ}.

  Definition state_val_type := csumR (exclR (optionO natO)) (agreeR unitO).
  Definition state_mapg_type := gmap gname state_val_type.
  Definition done_mapg_type := gmap gname (agreeR unitO).
  Definition pending_setg_type := gset gname.

  Definition pencount_frag (pn : nat) : iProp Σ :=
    own pendingnG_name (to_dfrac_agree (DfracOwn (1/2)) pn).

  Definition pending_val : state_val_type :=
    Cinl (Excl None).

  Definition done_val n : state_val_type :=
    Cinl (Excl (Some n)).

  Definition finished_val : state_val_type :=
    Cinr (to_agree (tt : unitO)).

  Definition penset_frag (γs : gset gname) : iProp Σ :=
    own pending_set_name (◯ GSet γs).

  (** [id_ctr_frag ctr] is a half-share at [idCounter_name] tracking the
      "next id to allocate". Mirrors [pencount_frag]. The other half lives
      inside [visited_mapg_auth]; the auth's pure invariant ties [ctr] to
      [dom gm = set_seq 0 ctr]. *)
  Definition id_ctr_frag (ctr : nat) : iProp Σ :=
    own idCounter_name (to_dfrac_agree (DfracOwn (1/2)) ctr).

  (** [done_id_coherent m d]: every γ in d is in m at a done/finished entry.
      The done-map [d] only records γ-presence; the specific id of a done
      entry is recoverable from [m] (in the done case). *)
  Definition done_id_coherent (m : state_mapg_type) (d : done_mapg_type) : Prop :=
    ∀ γ, d !! γ ≡ Some (to_agree (tt : unitO)) →
      (∃ n, m !! γ = Some (done_val n)) ∨ m !! γ = Some finished_val.

  Definition pending_coherent (m : state_mapg_type) (ps : pending_setg_type) (pending_n : nat) : Prop :=
    pending_n = size ps ∧
      ∀ γ, m !! γ = Some pending_val → γ ∈ ps.

  Definition id_mapg_type := gmap nat id_alloc_entry.

  (** [gm_m_coherent m gm]: the alloc map at [pending_id_name] mirrors
      [m]'s done/finished entries on the [Cinr] side. [Cinl] entries
      correspond to ids that have been issued but not yet bound (tokens
      that are still floating). The [finished_val] side of [m] no longer
      records the id, so coherence is expressed as two directional facts:
      [gm → m] holds for both done and finished; [m → gm] holds only for
      the done case (where [m] records the id). *)
  Definition gm_m_coherent (m : state_mapg_type) (gm : id_mapg_type) : Prop :=
    (∀ id γ, gm !! id = Some (Cinr (to_agree (γ : leibnizO gname))) →
       m !! γ = Some (done_val id) ∨ m !! γ = Some finished_val) ∧
    (∀ id γ, m !! γ = Some (done_val id) →
       gm !! id = Some (Cinr (to_agree (γ : leibnizO gname)))).

  (** [id_susp_gamma_coherent gm pvm m_v]: forward direction only. For
      every bound id in [gm], the susp loc recorded in [pvm] is bound to
      the same γ in the verifier-side [lg_map_v]. The converse does not
      hold: an id may have a [pvm] entry (and thus a [pval_frag]) before
      it is ever bound to a γ. Multiple ids may also share a susp.
      Used by [id_susp_γ_lookup] to mint persistent
      [pval_frag id susp ∗ lg_mapg_frag susp γ] from
      [m !! γ = Some (done_val id)]. *)
  Definition id_susp_gamma_coherent
      (gm : id_mapg_type) (pvm : pvalmap_type) (m_v : lg_mapg_type) : Prop :=
    ∀ id γ, gm !! id = Some (Cinr (to_agree (γ : leibnizO gname))) →
      ∃ susp, pvm !! id ≡ Some (to_agree susp) ∧
              m_v !! susp ≡ Some (Cinr (to_agree (γ : leibnizO gname))).

  (** [id_ref_coherent gm pvm rs]: each [(from, to)] in [rs] has [to < from],
      `from` is bound in [gm] (Cinr side — established at the same step
      where the rs entry is allocated), and the locs [pvm] records for
      [from] and [to] differ. The "from is bound" conjunct lets
      [bind_id_*_susp] internally derive [rs[from] = None] from
      [id_token from] (gm[from] = Cinl), so callers don't need to thread
      [⌜rs !! from = None⌝] as a precondition. *)
  Definition id_ref_coherent
      (gm : id_mapg_type) (pvm : pvalmap_type) (rs : id_ref_type) : Prop :=
    ∀ from to, rs !! from = Some to →
      to < from ∧
      (∃ γ, gm !! from = Some (Cinr (to_agree (γ : leibnizO gname)))) ∧
      ∃ susp_from susp_to,
        pvm !! from ≡ Some (to_agree susp_from) ∧
        pvm !! to ≡ Some (to_agree susp_to) ∧
        susp_from ≠ susp_to.

  (** [visited_mapg_auth m pn ctr] bundles the entire visited-map authority
      and exposes only the three externally-meaningful parameters:
      - [m] : the state map (used by clients e.g. via [vm_big_sep]).
      - [pn] : pending count (paired with external [pencount_frag pn]).
      - [ctr] : id counter (paired with external [id_ctr_frag ctr]).

      The remaining six maps are existentially quantified inside:
      [d] (done-map), [ps] (pending set), [gm] (id-alloc map),
      [pvm] (id→susp map), [m_v] (verifier-side lg_map), [rs] (id_ref map).
      Clients hold fragments at these maps' gnames ([visit_done],
      [penset_frag], [lg_mapg_frag], [pval_frag], [id_ref_frag], …) and
      never need them as Coq-level maps. *)
  Definition visited_mapg_auth (m : state_mapg_type) (pn : nat) (ctr : nat) : iProp Σ :=
    ∃ (d : done_mapg_type) (ps : pending_setg_type)
      (gm : id_mapg_type) (pvm : pvalmap_type)
      (m_v : lg_mapg_type) (rs : id_ref_type),
      own visited_state_name (● m) ∗ own visited_done_name (● d) ∗
      own pending_set_name (● GSet ps) ∗ pencount_frag pn ∗
      own pending_id_name (● gm) ∗
      id_ctr_frag ctr ∗
      pvalmap_auth pvm ∗
      own lg_mapG_v_name (● m_v) ∗
      own spec_meta_name (◯ GSet (dom m_v)) ∗
      id_ref_auth rs ∗
      ⌜dom gm = set_seq 0 ctr⌝ ∗
      ⌜dom pvm = set_seq 0 ctr⌝ ∗
      ⌜gm_m_coherent m gm⌝ ∗
      ⌜id_susp_gamma_coherent gm pvm m_v⌝ ∗
      ⌜id_ref_coherent gm pvm rs⌝ ∗
      ⌜done_id_coherent m d⌝ ∗ ⌜pending_coherent m ps pn⌝.

  (** Shape wrappers. Each now defers entirely to [visited_mapg_auth]
      (which existentially hides the six internal maps). The wrappers
      express only the externally-visible state transition (changes to
      [m], [pn], [ctr]). *)
  Definition visited_map_update_pending
      (m : state_mapg_type) (γs : gset gname) (pn : nat) (ctr : nat) : iProp Σ :=
    visited_mapg_auth (set_fold (λ γ m, <[ γ := pending_val ]>m) m γs)
                      (pn + size γs) ctr.

  Definition visited_map_update_done
      (m : state_mapg_type) (γ : gname) (pn : nat) (ctr : nat) : iProp Σ :=
    ∃ n, visited_mapg_auth (<[ γ := done_val n ]>m) pn ctr.

  Definition visited_map_update_finished
      (m : state_mapg_type) (γ : gname) (pn : nat) (ctr : nat) : iProp Σ :=
    visited_mapg_auth (<[ γ := finished_val ]>m) pn ctr.

  Definition visited_mapg_pending_removed
      (m : state_mapg_type) (γs : gset gname) (pn : nat) (ctr : nat) : iProp Σ :=
    visited_mapg_auth m (pn - size γs) ctr.

  Lemma visited_map_update_pending_rewrite m γs pn ctr :
    visited_map_update_pending m γs pn ctr ⊣⊢
    visited_mapg_auth (set_fold (λ γ m, <[ γ := pending_val ]>m) m γs) (pn + size γs) ctr.
  Proof. rewrite /visited_map_update_pending. done. Qed.

  Lemma visited_map_update_done_rewrite m γ pn ctr :
    visited_map_update_done m γ pn ctr ⊣⊢
    ∃ n, visited_mapg_auth (<[ γ := done_val n ]>m) pn ctr.
  Proof. rewrite /visited_map_update_done. done. Qed.

  Lemma visited_map_update_finished_rewrite m γ pn ctr :
    visited_map_update_finished m γ pn ctr ⊣⊢
    visited_mapg_auth (<[ γ := finished_val ]>m) pn ctr.
  Proof. rewrite /visited_map_update_finished. done. Qed.

  Lemma visited_mapg_pending_remove_rewrite m γs pn ctr :
    visited_mapg_pending_removed m γs pn ctr ⊣⊢
    visited_mapg_auth m (pn - size γs) ctr.
  Proof. rewrite /visited_mapg_pending_removed. done. Qed.

  Definition visit_pending γ : iProp Σ :=
    own visited_state_name (◯ {[ γ := pending_val ]}).

  Definition visit_reached_done γ : iProp Σ :=
    own visited_done_name (◯ {[ γ := to_agree (tt : unitO) ]}).

  Definition visit_done γ n : iProp Σ :=
    own visited_state_name (◯ {[ γ := done_val n ]}) ∗ visit_reached_done γ.

  Definition visit_finished γ : iProp Σ :=
    own visited_state_name (◯ {[ γ := finished_val ]}) ∗ visit_reached_done γ.

  Global Instance visit_reached_done_persistent γ :
    Persistent (visit_reached_done γ).
  Proof. rewrite /visit_reached_done. apply _. Qed.

  Global Instance visit_finished_persistent γ :
    Persistent (visit_finished γ).
  Proof. rewrite /visit_finished /finished_val. apply _. Qed.

  Global Instance visit_reached_done_timeless γ :
    Timeless (visit_reached_done γ).
  Proof. rewrite /visit_reached_done. apply _. Qed.

  Global Instance visit_finished_timeless γ :
    Timeless (visit_finished γ).
  Proof. rewrite /visit_finished /finished_val. apply _. Qed.

  Lemma pn_agree m pn ctr pn' :
    visited_mapg_auth m pn ctr -∗ pencount_frag pn' -∗ ⌜pn = pn'⌝.
  Proof.
    iIntros "(%d & %ps & %gm & %pvm & %m_v & %rs & Hms & Hd & Hps & H1 & Hgm & Hctr & Hpvm & Hmv & Hsmeta & Hrs & %Hdom & %Hdompvm & %Hgmm & %Hisgc & %Hirc & %Hdid & %Hpcoh) H2".
    rewrite /pencount_frag. iCombine "H1 H2" as "H".
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

  (** [id_token id] is a consumable token at [pending_id_name] keyed by
      [id]. Holding it claims [id] has been issued but not yet bound to
      any [γ] (via [visited_transition_done]). Exclusive at the same [id]
      since [Cinl (Excl ())] is exclusive. *)
  Definition id_token (id : nat) : iProp Σ :=
    own pending_id_name (◯ {[ id := Cinl (Excl ()) ]}).

  Global Instance id_token_timeless id : Timeless (id_token id).
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

  Lemma id_ctr_frag_agree m pn ctr ctr' :
    visited_mapg_auth m pn ctr -∗ id_ctr_frag ctr' -∗
      ⌜ctr = ctr'⌝.
  Proof.
    iIntros "(%d & %ps & %gm & %pvm & %m_v & %rs & Hms & Hd & Hps & Hpn & Hgm & H1 & Hpvm & Hmv & Hsmeta & Hrs & %Hdom & %Hdompvm & %Hgmm & %Hisgc & %Hirc & %Hdid & %Hpcoh) H2".
    rewrite /id_ctr_frag. iCombine "H1 H2" as "H".
    iDestruct (own_valid with "H") as %Hv%dfrac_agree_op_valid_L.
    destruct Hv as [_ ->].
    iDestruct "H" as "[H1 H2]". by iFrame.
  Qed.

  Lemma visited_insert m pn ctr :
    visited_mapg_auth m pn ctr ∗ pencount_frag pn ==∗
      ∃ γ,
        visited_map_update_pending m {[γ]} pn ctr ∗ pencount_frag (pn+1) ∗
          visit_pending γ ∗ penset_frag {[γ]}.
  Proof.
    iIntros "((%d & %ps & %gm & %pvm & %m_v & %rs & Hms & Hd & Hps & Hpn1 & Hgm & Hctr & Hpvm & Hmv & Hsmeta & Hrs & %Hdom & %Hdompvm & %Hgmm & %Hisgc & %Hirc & %Hdid & %Hpcoh) & Hpn2)".
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
    rewrite /visited_map_update_pending /visited_mapg_auth /visit_pending /penset_frag.
    rewrite set_fold_singleton size_singleton /=.
    iSplitR "Hp Hpsf Hpn2"; last by iFrame.
    iExists d, ({[γ]} ∪ ps), gm, pvm, m_v, rs.
    iFrame "Hms' Hd Hps' Hpn1 Hgm Hctr Hpvm Hmv Hsmeta Hrs".
    iPureIntro. split; [exact Hdom|]. split; [exact Hdompvm|].
    split; [|split; [exact Hisgc|split; [exact Hirc|split]]].
    - (* gm_m_coherent for new m' = <[γ := pending_val]>m *)
      destruct Hgmm as [Hgmm1 Hgmm2]. split.
      + intros id γ' Hgm_id. apply Hgmm1 in Hgm_id.
        destruct (decide (γ' = γ)) as [-> | Hne].
        * destruct Hgm_id as [Hmγ | Hmγ]; rewrite Hfm in Hmγ; discriminate.
        * destruct Hgm_id as [Hmγ | Hmγ];
            [left|right]; rewrite lookup_insert_ne; done.
      + intros id γ' Hmγ'. apply Hgmm2.
        destruct (decide (γ' = γ)) as [-> | Hne].
        * exfalso. rewrite lookup_insert in Hmγ'.
          rewrite /pending_val /done_val in Hmγ'. by inversion Hmγ'.
        * rewrite lookup_insert_ne in Hmγ'; done.
    - (* done_id_coherent for new m' *)
      intros γ' Hdγ'. destruct (decide (γ' = γ)) as [-> | Hne].
      + exfalso. specialize (Hdid γ Hdγ').
        destruct Hdid as [[n' Hmγ] | Hmγ]; rewrite Hfm in Hmγ; discriminate.
      + destruct (Hdid γ' Hdγ') as [[n' Hmγ] | Hmγ].
        * left. exists n'. rewrite lookup_insert_ne; done.
        * right. rewrite lookup_insert_ne; done.
    - destruct Hpcoh as [Hsize Hl]. split.
      + rewrite size_union; last set_solver. rewrite size_singleton. lia.
      + intros γ' Hγ'. destruct (decide (γ' = γ)) as [-> | Hne].
        * set_solver.
        * rewrite lookup_insert_ne in Hγ'; [|done].
          apply elem_of_union; right. by apply Hl.
  Qed.

  (* visited_transition_done has been subsumed by [bind_id_fresh_susp] —
     binding now writes to gm, pvm, and m_v atomically to maintain
     [id_susp_gamma_coherent]. *)

  Lemma visited_transition_finished m pn ctr γ n :
    visited_mapg_auth m pn ctr -∗ visit_done γ n
    ==∗ visited_map_update_finished m γ pn ctr ∗ visit_finished γ.
  Proof.
    iIntros "(%d & %ps & %gm & %pvm & %m_v & %rs & Hms & Hd & Hps & Hpn & Hgm & Hctr & Hpvm & Hmv & Hsmeta & Hrs & %Hdom & %Hdompvm & %Hgmm & %Hisgc & %Hirc & %Hdid & %Hpcoh) [Hsfrag #Hrd]".
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
      (● <[γ := finished_val]>m ⋅ ◯ {[γ := finished_val]})
      with "Hms Hsfrag") as "[$ $]".
    { apply auth_update, singleton_local_update_any.
      intros x Hx. unfold done_val.
      apply (exclusive_local_update _ finished_val). done. }
    iFrame "Hd Hps Hpn Hgm Hctr Hpvm Hmv Hsmeta Hrs Hrd". iPureIntro.
    split; [exact Hdom|]. split; [exact Hdompvm|].
    split; [|split; [exact Hisgc|split; [exact Hirc|split]]].
    - (* gm_m_coherent (<[γ := finished_val]>m) gm: only m changes at γ *)
      destruct Hgmm as [Hgmm1 Hgmm2]. split.
      + intros id γ' Hgm_id. apply Hgmm1 in Hgm_id as [Hm | Hm].
        * destruct (decide (γ' = γ)) as [-> | Hne].
          { rewrite Hinclm in Hm. injection Hm as ->.
            right. by rewrite lookup_insert. }
          { left. by rewrite lookup_insert_ne. }
        * destruct (decide (γ' = γ)) as [-> | Hne].
          { rewrite Hinclm in Hm. discriminate. }
          { right. by rewrite lookup_insert_ne. }
      + intros id γ' Hm.
        destruct (decide (γ' = γ)) as [-> | Hne].
        * rewrite lookup_insert in Hm.
          rewrite /done_val /finished_val in Hm. discriminate.
        * rewrite lookup_insert_ne in Hm; [|done]. apply Hgmm2. exact Hm.
    - intros γ' Hdγ'.
      destruct (decide (γ' = γ)) as [-> | Hne].
      + right. by rewrite lookup_insert.
      + rewrite lookup_insert_ne; [|done].
        destruct (Hdid γ' Hdγ') as [[n' Hmγ] | Hmγ].
        * left. by exists n'.
        * by right.
    - destruct Hpcoh as [Hsize Hl]. split; [exact Hsize|].
      intros γ' Hγ'. destruct (decide (γ' = γ)) as [-> | Hne].
      + exfalso. rewrite lookup_insert in Hγ'.
        rewrite /finished_val /pending_val in Hγ'. discriminate.
      + rewrite lookup_insert_ne in Hγ'; [|done]. by apply Hl.
  Qed.

  Lemma visit_done_keep γ n :
    visit_done γ n ⊢ visit_done γ n ∗ visit_reached_done γ.
  Proof.
    iIntros "[Hs #Hr]". iFrame "Hs Hr Hr".
  Qed.

  Lemma visit_finished_keep γ :
    visit_finished γ ⊢ visit_finished γ ∗ visit_reached_done γ.
  Proof.
    iIntros "[Hs #Hr]". iFrame "Hs Hr Hr".
  Qed.

  (** [visit_done_lookup] reads off [m !! γ = Some (done_val n)] from the
      auth and a [visit_done γ n] fragment. The token-side fragment is
      exclusive at γ ([Cinl (Excl _)]), so singleton inclusion collapses to
      a pointwise equiv, and Leibniz on [optionO natO] turns equiv into
      equality. The auth and fragment are returned unchanged. *)
  Lemma visit_done_lookup γ n m pn ctr :
    visited_mapg_auth m pn ctr -∗ visit_done γ n -∗
      ⌜m !! γ = Some (done_val n)⌝ ∗
      visited_mapg_auth m pn ctr ∗ visit_done γ n.
  Proof.
    iIntros "(%d & %ps & %gm & %pvm & %m_v & %rs & Hms & Hd & Hps & Hpn & Hgm & Hctr & Hpvm & Hmv & Hsmeta & Hrs & %Hdom & %Hdompvm & %Hgmm & %Hisgc & %Hirc & %Hdid & %Hpcoh) [Hf #Hr]".
    iDestruct (own_valid_2 with "Hms Hf") as %Hv.
    apply auth_both_valid_discrete in Hv as [Hincl Hvalid].
    apply (singleton_included_exclusive_l m γ (done_val n)) in Hincl;
      [|apply _|exact Hvalid].
    iFrame "∗ # %". iPureIntro. by apply some_done_val_equiv_eq.
  Qed.

  (** [visit_finished_lookup] reads off [m !! γ = Some finished_val] from
      the auth and a [visit_finished γ] fragment. The fragment's
      [Cinr (to_agree ())] side at [visited_state_name] is not exclusive,
      so equiv-to-eq cannot be bridged at that resource alone. Instead we
      route through [done_id_coherent]: the persistent [visit_reached_done]
      half gives [d !! γ ≡ Some (to_agree ())], which under
      [done_id_coherent] forces [m !! γ] to be a done/finished entry. The
      state-map fragment then rules out the done branch via
      csum-incompatibility. *)
  Lemma visit_finished_lookup γ m pn ctr :
    visited_mapg_auth m pn ctr -∗ visit_finished γ -∗
      ⌜m !! γ = Some finished_val⌝ ∗
      visited_mapg_auth m pn ctr ∗ visit_finished γ.
  Proof.
    iIntros "(%d & %ps & %gm & %pvm & %m_v & %rs & Hms & Hd & Hps & Hpn & Hgm & Hctr & Hpvm & Hmv & Hsmeta & Hrs & %Hdom & %Hdompvm & %Hgmm & %Hisgc & %Hirc & %Hdid & %Hpcoh)
            [Hf #Hrd]".
    (* d !! γ ≡ Some (to_agree ()) via auth+frag at visited_done_name. *)
    iDestruct (own_valid_2 with "Hd Hrd") as %Hvd.
    apply auth_both_valid_discrete in Hvd as [Hincl_d Hvalid_d].
    apply singleton_included_l in Hincl_d as (xd & Hxd & Hle_d).
    assert (✓ xd) as Hvxd
      by (eapply lookup_valid_Some; [exact Hvalid_d|exact Hxd]).
    assert (d !! γ ≡ Some (to_agree (tt : unitO))) as Hdg_eq.
    { rewrite Hxd. f_equiv.
      apply Some_included in Hle_d as [|Hinc]; [by symmetry|].
      symmetry. by apply (agree_valid_included _ _ Hvxd). }
    destruct (Hdid γ Hdg_eq) as [[n' Hmγ] | Hmγ].
    - (* m !! γ = Some (done_val n'): rule out via state fragment. *)
      iDestruct (own_valid_2 with "Hms Hf") as %Hvm.
      apply auth_both_valid_discrete in Hvm as [Hincl_m _].
      apply singleton_included_l in Hincl_m as (ym & Hym & Hle_m).
      exfalso. rewrite Hmγ in Hym. apply Some_equiv_inj in Hym. symmetry in Hym.
      apply done_val_equiv_eq in Hym. subst ym.
      apply Some_included in Hle_m as [Heq | Hle].
      + rewrite /finished_val /done_val in Heq. by inversion Heq.
      + rewrite /finished_val /done_val in Hle.
        apply csum_included in Hle as
          [Hbot | [(?&?& Heq1 & _ & _) | (?&?& _ & Heq2 & _)]].
        * by inversion Hbot.
        * by inversion Heq1.
        * by inversion Heq2.
    - (* m !! γ = Some finished_val: direct. *)
      iFrame "∗ # %".
  Qed.

  (** [visit_reached_done γ] forces [m !! γ] into the done/finished family.
      Routes through [done_id_coherent]. *)
  Lemma visit_reached_done_lookup γ m pn ctr :
    visited_mapg_auth m pn ctr -∗ visit_reached_done γ -∗
      ⌜(∃ n, m !! γ = Some (done_val n)) ∨ m !! γ = Some finished_val⌝ ∗
      visited_mapg_auth m pn ctr.
  Proof.
    iIntros "Hauth #Hrd".
    iDestruct "Hauth" as "(%d & %ps & %gm & %pvm & %m_v & %rs & Hms & Hd & Hps & Hpn & Hgm & Hctr & Hpvm & Hmv & Hsmeta & Hrs & %Hdom & %Hdompvm & %Hgmm & %Hisgc & %Hirc & %Hdid & %Hpcoh)".
    iDestruct (own_valid_2 with "Hd Hrd") as %Hvd.
    apply auth_both_valid_discrete in Hvd as [Hincl_d Hvalid_d].
    apply singleton_included_l in Hincl_d as (xd & Hxd & Hle_d).
    assert (✓ xd) as Hvxd
      by (eapply lookup_valid_Some; [exact Hvalid_d|exact Hxd]).
    assert (d !! γ ≡ Some (to_agree (tt : unitO))) as Hdg_eq.
    { rewrite Hxd. f_equiv. apply Some_included in Hle_d as [|Hinc]; [by symmetry|].
      symmetry. by apply (agree_valid_included _ _ Hvxd). }
    iSplit; last by iFrame "∗ %".
    iPureIntro. by apply (Hdid γ).
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

  Lemma visited_invalid_2 γ :
    visit_pending γ ∗ visit_finished γ -∗ False.
  Proof.
    rewrite /visit_pending /visit_finished.
    iIntros "[H1 [H2 _]]". iCombine "H1 H2" as "H".
    iDestruct (own_valid with "H") as %Hv. iPureIntro.
    rewrite auth_frag_valid singleton_valid in Hv.
    rewrite /pending_val /finished_val in Hv. done.
  Qed.

  Lemma visited_invalid_3 γ n1 :
    visit_done γ n1 ∗ visit_finished γ -∗ False.
  Proof.
    rewrite /visit_done /visit_finished.
    iIntros "[[H1 _] [H2 _]]". iCombine "H1 H2" as "H".
    iDestruct (own_valid with "H") as %Hv. iPureIntro.
    rewrite auth_frag_valid singleton_valid in Hv.
    rewrite /done_val /finished_val in Hv. done.
  Qed.


  Lemma visited_reached_done_invalid γ m pn ctr :
    visited_mapg_auth m pn ctr -∗ visit_reached_done γ -∗ visit_pending γ -∗ False.
  Proof.
    iIntros "(%d & %ps & %gm & %pvm & %m_v & %rs & Hms & Hd & Hps & Hpn & Hgm & Hctr & Hpvm & Hmv & Hsmeta & Hrs & %Hdom & %Hdompvm & %Hgmm & %Hisgc & %Hirc & %Hdid & %Hpcoh) Hreached Hpending".
    rewrite /visit_pending /visit_reached_done.
    iDestruct (own_valid_2 with "Hd Hreached") as %Hvd.
    apply auth_both_valid_discrete in Hvd as [Hincl_d Hvalid_d].
    apply singleton_included_l in Hincl_d as (xd & Hxd & Hle_d).
    assert (✓ xd) as Hvxd
      by (eapply lookup_valid_Some; [exact Hvalid_d|exact Hxd]).
    assert (d !! γ ≡ Some (to_agree (tt : unitO))) as Hdg_eq.
    { rewrite Hxd. f_equiv. apply Some_included in Hle_d as [|Hinc]; [by symmetry|].
      symmetry. by apply (agree_valid_included _ _ Hvxd). }
    iDestruct (own_valid_2 with "Hms Hpending") as %Hvm.
    apply auth_both_valid_discrete in Hvm as [Hincl_m _].
    apply singleton_included_l in Hincl_m as (ym & Hym & Hle).
    iPureIntro. destruct (Hdid γ Hdg_eq) as [[n Hmγ] | Hmγ];
      rewrite Hmγ in Hym;
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

  Lemma visited_done_excl γ n1 n2 :
    visit_done γ n1 -∗ visit_done γ n2 -∗ False.
  Proof.
    rewrite /visit_done.
    iIntros "[Hs1 _] [Hs2 _]".
    iDestruct (own_valid_2 with "Hs1 Hs2") as %Hv. iPureIntro.
    rewrite -auth_frag_op singleton_op auth_frag_valid singleton_valid in Hv.
    rewrite /done_val in Hv.
    apply (Cinl_valid (B:=agreeR unitO)) in Hv. by apply exclusive_l in Hv.
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

  Lemma pending_set_remove m pn ctr γs :
    visited_mapg_auth m pn ctr -∗ pencount_frag pn -∗ penset_frag γs -∗
    ([∗ set] γ ∈ γs, visit_reached_done γ) ==∗
    visited_mapg_pending_removed m γs pn ctr ∗ pencount_frag (pn - size γs).
  Proof.
    iIntros "(%d & %ps & %gm & %pvm & %m_v & %rs & Hms & Hd & Hps & Hpn1 & Hgm & Hctr & Hpvm & Hmv & Hsmeta & Hrs & %Hdom & %Hdompvm & %Hgmm & %Hisgc & %Hirc & %Hdid & %Hpcoh) Hpn2 Hfrag #Hreached".
    iAssert (⌜∀ γ, γ ∈ γs →
              (∃ n, m !! γ = Some (done_val n)) ∨ m !! γ = Some finished_val⌝)%I
      as %Hmγs.
    { iIntros (γ Hin).
      iDestruct (big_sepS_elem_of with "Hreached") as "Hr"; first done.
      iDestruct (own_valid_2 with "Hd Hr") as %Hvd.
      apply auth_both_valid_discrete in Hvd as [Hincl Hvalid_d].
      apply singleton_included_l in Hincl as (xd & Hxd & Hle).
      iPureIntro.
      assert (✓ xd) as Hvxd
        by (eapply lookup_valid_Some; [exact Hvalid_d|exact Hxd]).
      assert (d !! γ ≡ Some (to_agree (tt : unitO))) as Hdg_eq.
      { rewrite Hxd. f_equiv. apply Some_included in Hle as [|Hinc]; [by symmetry|].
        symmetry. by apply (agree_valid_included _ _ Hvxd). }
      apply (Hdid γ Hdg_eq). }
    rewrite /visited_mapg_pending_removed /penset_frag.
    iCombine "Hps Hfrag" as "Hpsfull".
    iDestruct (own_valid with "Hpsfull") as %Hv.
    apply auth_both_valid_discrete in Hv as [Hincl%gset_disj_included _].
    iMod (own_update with "Hpsfull") as "Hps'".
    { apply auth_update_dealloc, gset_disj_dealloc_local_update. }
    iMod (pn_update pn (pn - size γs) with "Hpn1 Hpn2") as "[Hpn1 Hpn2]".
    iModIntro. iFrame "Hms Hd Hps' Hpn1 Hpn2 Hgm Hctr Hpvm Hmv Hsmeta Hrs". iPureIntro.
    split; [exact Hdom|]. split; [exact Hdompvm|]. split; [exact Hgmm|].
    split; [exact Hisgc|]. split; [exact Hirc|]. split; [exact Hdid|].
    destruct Hpcoh as [Hsz Hpcoh].
    split.
    - rewrite (size_difference _ _ Hincl) -Hsz //.
    - intros γ' Hm. specialize (Hpcoh γ' Hm).
      destruct (decide (γ' ∈ γs)) as [Hin | Hnin].
      + exfalso. destruct (Hmγs _ Hin) as [[n Hmγ] | Hmγ];
          rewrite Hmγ in Hm;
          rewrite /done_val /finished_val /pending_val in Hm;
          by inversion Hm.
      + by apply elem_of_difference.
  Qed.

  (** [id_token id] witnesses that no [γ] in [m] maps to [done_val id] —
      id is unused as a done-tag in the visited map. (Since finished_val
      no longer carries an id, there is no analogous statement to make
      about finished entries.) *)
  Lemma id_token_unused m pn ctr id :
    visited_mapg_auth m pn ctr -∗ id_token id -∗
      ⌜∀ γ, m !! γ ≠ Some (done_val id)⌝ ∗
      visited_mapg_auth m pn ctr ∗ id_token id.
  Proof.
    iIntros "(%d & %ps & %gm & %pvm & %m_v & %rs & Hms & Hd & Hps & Hpn & Hgm & Hctr & Hpvm & Hmv & Hsmeta & Hrs & %Hdom & %Hdompvm & %Hgmm & %Hisgc & %Hirc & %Hdid & %Hpcoh) Htok".
    iDestruct (own_valid_2 with "Hgm Htok") as %Hvgm.
    apply auth_both_valid_discrete in Hvgm as [Hinclgm Hvalidgm].
    apply (singleton_included_exclusive_l gm id (Cinl (Excl ()))) in Hinclgm; [|apply _|exact Hvalidgm].
    assert (gm !! id = Some (Cinl (Excl ()))) as Hgm_id by (apply some_cinl_excl_unit_equiv_eq; exact Hinclgm).
    iFrame "∗ %". iPureIntro. intros γ Hmγ.
    destruct Hgmm as [_ Hgmm2].
    have Hcin := Hgmm2 id γ Hmγ.
    rewrite Hgm_id in Hcin. discriminate.
  Qed.

  (** [id_ctr_frag_alloc] allocates the next fresh id-token paired with
      the susp loc [l] the verifier has just minted. Writes [Cinl (Excl ())]
      into [gm] at [ctr] and [to_agree l] into [pvm] at [ctr] in lockstep —
      this keeps [dom gm = dom pvm = set_seq 0 ctr]. The [m_v] / [rs]
      entries (and the γ binding) are written later by [bind_id_fresh_susp].

      Returns the pure fact [⌜rs !! ctr = None⌝] so that callers can chain
      directly into [bind_id_fresh_susp] (whose [rs !! from = None]
      precondition is exactly this). The fact follows from
      [id_ref_coherent] on the pre-state: [ctr ∉ dom pvm], and every key
      of [rs] must have a [pvm] entry. *)
  Lemma id_ctr_frag_alloc m pn ctr (l : loc) :
    visited_mapg_auth m pn ctr -∗ id_ctr_frag ctr ==∗
      visited_mapg_auth m pn (S ctr) ∗
      id_ctr_frag (S ctr) ∗ id_token ctr ∗ pval_frag ctr l.
  Proof.
    iIntros "(%d & %ps & %gm & %pvm & %m_v & %rs & Hms & Hd & Hps & Hpn & Hgm & Hctr & Hpvm & Hmv & Hsmeta & Hrs & %Hdom & %Hdompvm & %Hgmm & %Hisgc & %Hirc & %Hdid & %Hpcoh) Hid_ctr".
    rewrite /id_ctr_frag /id_token /pvalmap_auth /pval_frag.
    assert (gm !! ctr = None) as Hgm_ctr.
    { apply not_elem_of_dom. rewrite Hdom. intro H.
      apply elem_of_set_seq in H. lia. }
    assert (pvm !! ctr = None) as Hpvm_ctr.
    { apply not_elem_of_dom. rewrite Hdompvm. intro H.
      apply elem_of_set_seq in H. lia. }
    (* rs !! ctr = None: if rs[ctr] = Some to, id_ref_coherent forces
       gm[ctr] = Some (Cinr ...), contradicting Hgm_ctr. *)
    assert (rs !! ctr = None) as Hrs_ctr.
    { destruct (rs !! ctr) as [to|] eqn:Hr; [|done].
      exfalso. pose proof (Hirc ctr to Hr) as [_ [(γ' & Hgm_eq) _]].
      rewrite Hgm_ctr in Hgm_eq. by inversion Hgm_eq. }
    iCombine "Hctr Hid_ctr" as "Hctr_full".
    iMod (own_update with "Hctr_full") as "[Hctr Hid_ctr']".
    { apply frac_agree_update_2. by rewrite Qp.half_half. }
    iMod (own_update _ _
      (● <[ctr := Cinl (Excl ())]>gm ⋅ ◯ {[ctr := Cinl (Excl ())]})
      with "Hgm") as "[Hgm Htok]".
    { apply auth_update_alloc.
      apply alloc_singleton_local_update; [rewrite Hgm_ctr; done | done]. }
    iMod (own_update _ _
      (● <[ctr := to_agree l]>pvm ⋅ ◯ {[ctr := to_agree l]})
      with "Hpvm") as "[Hpvm #Hpvf]".
    { apply auth_update_alloc.
      apply alloc_singleton_local_update; [exact Hpvm_ctr | done]. }
    iModIntro. rewrite /visited_mapg_auth.
    iSplitR "Hid_ctr' Htok Hpvf"; last by iFrame.
    iExists d, ps, (<[ctr := Cinl (Excl ())]>gm), (<[ctr := to_agree l]>pvm), m_v, rs.
    iFrame "Hms Hd Hps Hpn Hgm Hctr Hpvm Hmv Hsmeta Hrs".
    iPureIntro.
    split; [|split; [|split; [|split; [|split; [|split; [exact Hdid|exact Hpcoh]]]]]].
    - rewrite dom_insert_L Hdom -(set_seq_S_end_union_L 0) /=. set_solver.
    - rewrite dom_insert_L Hdompvm -(set_seq_S_end_union_L 0) /=. set_solver.
    - destruct Hgmm as [Hgmm1 Hgmm2]. split.
      + intros id γ' Hgm'.
        destruct (decide (id = ctr)) as [-> | Hne].
        * rewrite lookup_insert in Hgm'. discriminate.
        * rewrite lookup_insert_ne in Hgm'; [|done]. by apply Hgmm1.
      + intros id γ' Hm.
        destruct (decide (id = ctr)) as [-> | Hne].
        * exfalso. have Hcin := Hgmm2 ctr γ' Hm.
          rewrite Hgm_ctr in Hcin. discriminate.
        * rewrite lookup_insert_ne; [|done]. by apply Hgmm2.
    - (* id_susp_gamma_coherent: forward direction; pvm at ctr is new but
         gm[ctr] is Cinl so we never query it. Other ids unchanged. *)
      intros id γ' Hgm'.
      destruct (decide (id = ctr)) as [-> | Hne_id].
      + rewrite lookup_insert in Hgm'. discriminate.
      + rewrite lookup_insert_ne in Hgm'; [|done].
        destruct (Hisgc id γ' Hgm') as (susp & Hpvm_id & Hmv_susp).
        exists susp. split; [|exact Hmv_susp].
        rewrite lookup_insert_ne; [exact Hpvm_id|]. done.
    - (* id_ref_coherent: existing entries in rs have from ≠ ctr and to ≠ ctr
         because their pvm lookups must exist (old pvm[ctr] = None). *)
      intros from' to' Hrs'.
      destruct (Hirc from' to' Hrs') as [Hlt' [(γ' & Hgm_from) (sf & st & Hpf & Hpt & Hneq)]].
      split; [exact Hlt'|]. split.
      { exists γ'. rewrite lookup_insert_ne; [exact Hgm_from|]. intros ->.
        rewrite Hgm_ctr in Hgm_from. by inversion Hgm_from. }
      exists sf, st. split_and!; [| |exact Hneq].
      + rewrite lookup_insert_ne; [exact Hpf|]. intros ->.
        rewrite Hpvm_ctr in Hpf. by inversion Hpf.
      + rewrite lookup_insert_ne; [exact Hpt|]. intros ->.
        rewrite Hpvm_ctr in Hpt. by inversion Hpt.
  Qed.

  (** [id_token id] implies [id < ctr]: the id has been allocated (is in
      [dom gm = set_seq 0 ctr]) so it is strictly below the counter. *)
  Lemma id_token_lt_ctr m pn ctr id :
    visited_mapg_auth m pn ctr -∗ id_token id -∗
      ⌜id < ctr⌝ ∗ visited_mapg_auth m pn ctr ∗ id_token id.
  Proof.
    iIntros "(%d & %ps & %gm & %pvm & %m_v & %rs & Hms & Hd & Hps & Hpn & Hgm & Hctr & Hpvm & Hmv & Hsmeta & Hrs & %Hdom & %Hdompvm & %Hgmm & %Hisgc & %Hirc & %Hdid & %Hpcoh) Htok".
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

  (** Mint a persistent [pval_frag id susp ∗ (lg_mapg_v_frag susp γ)] witness
      from a known [m !! γ = Some (done_val id)]. The lg-map fragment is
      written out as a raw [own] here since [lg_mapg_frag] is defined later
      in [Section lg_map]. *)
  Lemma id_susp_γ_lookup m pn ctr γ id :
    m !! γ = Some (done_val id) →
    visited_mapg_auth m pn ctr ==∗
      visited_mapg_auth m pn ctr ∗
      ∃ susp, pval_frag id susp ∗
              own lg_mapG_v_name
                  (◯ ({[susp := Cinr (to_agree (γ : leibnizO gname))]}
                        : gmap loc lg_mapEntry)).
  Proof.
    iIntros (Hmγ) "(%d & %ps & %gm & %pvm & %m_v & %rs & Hms & Hd & Hps & Hpn & Hgm & Hctr & Hpvm & Hmv & Hsmeta & Hrs & %Hdom & %Hdompvm & %Hgmm & %Hisgc & %Hirc & %Hdid & %Hpcoh)".
    pose proof Hgmm as [_ Hgmm2].
    pose proof (Hgmm2 id γ Hmγ) as Hgm_id.
    pose proof (Hisgc id γ Hgm_id) as (susp & Hpvm_id & Hmv_susp).
    rewrite /pval_frag.
    iMod (own_update _ _
      (● pvm ⋅ ◯ {[id := to_agree susp]})
      with "Hpvm") as "[Hpvm #Hpvf]".
    { apply auth_update_dfrac_alloc; [apply _|].
      apply singleton_included_l. exists (to_agree susp). split.
      - rewrite Hpvm_id //.
      - apply Some_included_2. by left. }
    iMod (own_update _ _
      (● m_v ⋅ ◯ ({[susp := Cinr (to_agree (γ : leibnizO gname))]} : gmap loc lg_mapEntry))
      with "Hmv") as "[Hmv #Hlbf]".
    { apply auth_update_dfrac_alloc; [apply _|].
      apply singleton_included_l. eexists. split; [by rewrite Hmv_susp|].
      apply Some_included_2. by left. }
    iModIntro.
    iSplitL "Hms Hd Hps Hpn Hgm Hctr Hpvm Hmv Hsmeta Hrs"; last first.
    { iExists susp. by iFrame "Hpvf Hlbf". }
    iFrame "Hms Hd Hps Hpn Hgm Hctr Hpvm Hmv Hsmeta Hrs".
    iPureIntro. eauto 10.
  Qed.

  (** [id_ref_frag from to] forces [to < from] (via [id_ref_coherent]). *)
  Lemma id_ref_frag_lt m pn ctr from to :
    visited_mapg_auth m pn ctr -∗ id_ref_frag from to -∗
      ⌜to < from⌝ ∗ visited_mapg_auth m pn ctr.
  Proof.
    iIntros "(%d & %ps & %gm & %pvm & %m_v & %rs & Hms & Hd & Hps & Hpn & Hgm & Hctr & Hpvm & Hmv & Hsmeta & Hrs & %Hdom & %Hdompvm & %Hgmm & %Hisgc & %Hirc & %Hdid & %Hpcoh) Hfrag".
    iDestruct (id_ref_auth_frag with "Hrs Hfrag") as %Hrs_lookup.
    pose proof (Hirc from to Hrs_lookup) as [Hlt _].
    iFrame "Hms Hd Hps Hpn Hgm Hctr Hpvm Hmv Hsmeta Hrs". iPureIntro. eauto 10.
  Qed.

  (** [id_ref_frag from to] paired with [pval_frag from susp_from] and
      [pval_frag to susp_to] forces [susp_from ≠ susp_to]. *)
  Lemma id_ref_frag_locs_neq m pn ctr from to susp_from susp_to :
    visited_mapg_auth m pn ctr -∗
    id_ref_frag from to -∗
    pval_frag from susp_from -∗ pval_frag to susp_to -∗
      ⌜susp_from ≠ susp_to⌝ ∗ visited_mapg_auth m pn ctr.
  Proof.
    iIntros "(%d & %ps & %gm & %pvm & %m_v & %rs & Hms & Hd & Hps & Hpn & Hgm & Hctr & Hpvm & Hmv & Hsmeta & Hrs & %Hdom & %Hdompvm & %Hgmm & %Hisgc & %Hirc & %Hdid & %Hpcoh) Hfrag Hpvf Hpvt".
    iDestruct (id_ref_auth_frag with "Hrs Hfrag") as %Hrs_lookup.
    pose proof (Hirc from to Hrs_lookup) as [_ [_ (susp_f & susp_t & Hpvf_eq & Hpvt_eq & Hneq)]].
    iDestruct (pvalmap_auth_frag_eq with "Hpvm Hpvf") as %Hpvf_eq2.
    iDestruct (pvalmap_auth_frag_eq with "Hpvm Hpvt") as %Hpvt_eq2.
    rewrite Hpvf_eq in Hpvf_eq2.
    rewrite Hpvt_eq in Hpvt_eq2.
    apply Some_equiv_inj, (inj to_agree) in Hpvf_eq2.
    apply Some_equiv_inj, (inj to_agree) in Hpvt_eq2.
    fold_leibniz. subst susp_f susp_t.
    iFrame "Hms Hd Hps Hpn Hgm Hctr Hpvm Hmv Hsmeta Hrs". iPureIntro. eauto 10.
  Qed.

End visited_map_res.


Definition lg_p_meta_n : namespace := nroot .@ "lg_p_meta".

Section lg_map.
  Context `{!correctnessG Σ, !spec_metaG Σ, !heapGS Σ}.

  (** Prover-side authority only. The verifier-side [m_v] auth and its
      [spec_meta_name (◯ GSet (dom m_v))] freshness accumulator have been
      hoisted into [visited_mapg_auth] so the [id_susp_gamma_coherent]
      pure invariant can refer to [m_v]. *)
  (* Verifier-side authority (also lives inside [visited_mapg_auth]). *)
  Definition lg_v_auth (m_v : lg_mapg_type) : iProp Σ :=
    own lg_mapG_v_name (● m_v) ∗
    own spec_meta_name (◯ GSet (dom m_v)).

  (* Prover-side authority. *)
  Definition lg_p_auth (m_p : lg_mapg_type) : iProp Σ :=
    own lg_mapG_p_name (● m_p) ∗
    ([∗ set] l ∈ dom m_p, meta l lg_p_meta_n (true : bool)).

  (* Combined verifier+prover authority. *)
  Definition lg_mapg_auth (m_v m_p : lg_mapg_type) : iProp Σ :=
    lg_v_auth m_v ∗ lg_p_auth m_p.

  (* Verifier-side fragments. *)
  Definition lg_mapg_frag (l : loc) (γ : gname) : iProp Σ :=
    own lg_mapG_v_name (◯ ({[ l := Cinr (to_agree γ) ]} : gmap loc lg_mapEntry)).

  Definition lg_mapg_unalloc (l : loc) : iProp Σ :=
    own lg_mapG_v_name (◯ ({[ l := Cinl (to_agree (tt : unitO)) ]} : gmap loc lg_mapEntry)).

  (* Prover-side fragments. *)
  Definition lg_mapg_p_frag (l : loc) (γ : gname) : iProp Σ :=
    own lg_mapG_p_name (◯ ({[ l := Cinr (to_agree γ) ]} : gmap loc lg_mapEntry)).

  Definition lg_mapg_p_unalloc (l : loc) : iProp Σ :=
    own lg_mapG_p_name (◯ ({[ l := Cinl (to_agree (tt : unitO)) ]} : gmap loc lg_mapEntry)).

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
    iIntros "Hvtok ((Hauth_v & Hsmeta) & Hauth_p & Hbig_p)".
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
      lg_mapg_auth (<[ l := Cinl (to_agree (tt : unitO)) ]> m_v) m_p ∗ lg_mapg_unalloc l.
  Proof.
    rewrite /lg_mapg_auth /lg_mapg_unalloc.
    iIntros "Hvtok ((Hauth_v & Hsmeta) & Hauth_p & Hbig_p)".
    iDestruct (vmeta_combine_dom m_v l (Cinl (to_agree (tt : unitO)))
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
    iIntros "Hmtok ((Hauth_v & Hsmeta) & Hauth_p & Hbig_p)".
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
      lg_mapg_auth m_v (<[ l := Cinl (to_agree (tt : unitO)) ]> m_p) ∗ lg_mapg_p_unalloc l.
  Proof.
    rewrite /lg_mapg_auth /lg_mapg_p_unalloc.
    iIntros "Hmtok ((Hauth_v & Hsmeta) & Hauth_p & Hbig_p)".
    iMod (meta_combine_dom m_p l (Cinl (to_agree (tt : unitO))) with "Hmtok Hbig_p")
      as "[%Hl_nin Hbig_p']".
    apply not_elem_of_dom in Hl_nin.
    iMod (own_update with "Hauth_p") as "[$ $]";
      last by iModIntro; iFrame "Hauth_v Hsmeta Hbig_p'".
    apply auth_update_alloc.
    by apply alloc_singleton_local_update.
  Qed.

  (** [bind_id_fresh_susp]: bind an existing id [from] (whose susp loc is
      [l], certified by the input [pval_frag from l]) to a fresh γ. The
      caller provides [vmeta_token l] which guarantees [l ∉ dom m_v];
      combined with the persistent [lg_mapg_frag susp_to γ_to] for the
      prior id's susp, this discharges [l ≠ susp_to] for
      [id_ref_coherent]. Writes [gm] (Cinl → Cinr γ at [from]), [d]
      (γ → ()), [m_v] ([l] → Cinr γ), [m] (γ → done_val from), and [rs]
      ([from] → [to]). [pvm] is unchanged. *)
  Lemma bind_id_fresh_susp
      m pn ctr
      from to γ γ_to susp_to (l : loc) :
    to < from →
    vmeta_token l -∗
    id_token from -∗
    visit_pending γ -∗
    pval_frag from l -∗
    pval_frag to susp_to -∗
    lg_mapg_frag susp_to γ_to -∗
    visited_mapg_auth m pn ctr ==∗
      visited_mapg_auth (<[γ := done_val from]>m) pn ctr ∗
      visit_done γ from ∗
      lg_mapg_frag l γ ∗
      id_ref_frag from to.
  Proof.
    iIntros (Hlt) "Hvtok Htok Hpen #Hpvf #Hpvt #Hlbf
              (%d & %ps & %gm & %pvm & %m_v & %rs & Hms & Hd & Hps & Hpn & Hgm & Hctr & Hpvm & Hmv & Hsmeta & Hrs &
               %Hdom & %Hdompvm & %Hgmm & %Hisgc & %Hirc & %Hdid & %Hpcoh)".
    rewrite /vmeta_token /pval_frag /id_token /visit_pending
            /visit_done /visit_reached_done /lg_mapg_frag /id_ref_frag.
    (* susp_to ∈ dom m_v via the lg_mapg_frag's agreement with m_v auth. *)
    iDestruct (own_valid_2 with "Hmv Hlbf") as %Hv_mv.
    apply auth_both_valid_discrete in Hv_mv as [Hinc_mv _].
    apply singleton_included_l in Hinc_mv as (x_mv & Hx_mv & _).
    assert (susp_to ∈ dom m_v) as Hsusp_to_dom.
    { apply elem_of_dom. destruct (m_v !! susp_to) as [a|] eqn:Heq.
      - eauto.
      - rewrite Heq in Hx_mv. by inversion Hx_mv. }
    iDestruct (own_valid_2 with "Hms Hpen") as %Hvm.
    apply auth_both_valid_discrete in Hvm as [Hinclm Hvalidm].
    apply (singleton_included_exclusive_l m γ pending_val) in Hinclm; [|apply _|exact Hvalidm].
    assert (m !! γ = Some pending_val) as Hmγ_pend
      by (apply some_pending_val_equiv_eq; exact Hinclm).
    iDestruct (own_valid with "Hd") as %Hvd_auth.
    pose proof (proj1 (auth_auth_valid d) Hvd_auth) as Hvd_auth'.
    assert (d !! γ = None) as Hdγ.
    { destruct (d !! γ) as [xd|] eqn:Hdeq; [|done].
      exfalso.
      assert (✓ xd) as Hvxd.
      { apply (lookup_valid_Some d γ xd Hvd_auth'). rewrite Hdeq. done. }
      assert (d !! γ ≡ Some (to_agree (tt : unitO))) as Hdg_eq.
      { rewrite Hdeq. f_equiv.
        apply to_agree_uninj in Hvxd as [u Hxd_eq].
        destruct u. by rewrite Hxd_eq. }
      destruct (Hdid γ Hdg_eq) as [[n Hmγ] | Hmγ];
        rewrite Hmγ_pend in Hmγ; discriminate. }
    iDestruct (own_valid_2 with "Hgm Htok") as %Hvgm.
    apply auth_both_valid_discrete in Hvgm as [Hinclgm Hvalidgm].
    apply (singleton_included_exclusive_l gm from (Cinl (Excl ()))) in Hinclgm; [|apply _|exact Hvalidgm].
    assert (gm !! from = Some (Cinl (Excl ()))) as Hgm_from_cinl
      by (apply some_cinl_excl_unit_equiv_eq; exact Hinclgm).
    (* rs !! from = None: id_ref_coherent says rs[from] = Some _ requires
       gm[from] = Cinr (to_agree _), contradicting Hgm_from_cinl. *)
    assert (rs !! from = None) as Hrsfrom.
    { destruct (rs !! from) as [to'|] eqn:Hr; [|done].
      exfalso. pose proof (Hirc from to' Hr) as [_ [(γ' & Hgm_eq) _]].
      rewrite Hgm_from_cinl in Hgm_eq. by inversion Hgm_eq. }
    (* pvm[from] ≡ Some (to_agree l) via the input pval_frag *)
    iDestruct (pvalmap_auth_frag_eq with "Hpvm Hpvf") as %Hpvf_eq.
    (* pvm[to] ≡ Some (to_agree susp_to) via the input pval_frag *)
    iDestruct (pvalmap_auth_frag_eq with "Hpvm Hpvt") as %Hpvt_eq.
    (* l ∉ dom m_v from vmeta_token freshness combined with the accumulator *)
    iDestruct (own_valid_2 with "Hsmeta Hvtok") as %Hv_smeta.
    rewrite auth_frag_op_valid gset_disj_valid_op in Hv_smeta.
    assert (l ∉ dom m_v) as Hl_nin by set_solver.
    apply not_elem_of_dom in Hl_nin.
    iCombine "Hsmeta Hvtok" as "Hsmeta'".
    rewrite gset_disj_union; [|set_solver].
    assert (l ≠ susp_to) as Hl_ne_susp_to.
    { intros ->. apply not_elem_of_dom in Hl_nin. set_solver. }
    iMod (own_update_2 _ _ _
      (● <[γ := done_val from]>m ⋅ ◯ {[γ := done_val from]})
      with "Hms Hpen") as "[Hms Hms_f]".
    { apply auth_update, singleton_local_update_any.
      intros x Hx. unfold pending_val.
      apply (exclusive_local_update _ (done_val from)). done. }
    iMod (own_update _ _
      (● <[γ := to_agree (tt : unitO)]>d ⋅ ◯ {[γ := to_agree (tt : unitO)]})
      with "Hd") as "[Hd #Hd_f]".
    { apply auth_update_alloc, alloc_singleton_local_update; done. }
    iMod (own_update_2 _ _ _
      (● <[from := Cinr (to_agree (γ : leibnizO gname))]>gm ⋅
       ◯ {[from := Cinr (to_agree (γ : leibnizO gname))]})
      with "Hgm Htok") as "[Hgm _]".
    { apply auth_update, singleton_local_update_any.
      intros y _. apply exclusive_local_update. done. }
    iMod (own_update _ _
      (● <[l := Cinr (to_agree (γ : leibnizO gname)) : lg_mapEntry]>m_v ⋅
       ◯ ({[l := Cinr (to_agree (γ : leibnizO gname)) : lg_mapEntry]}
            : gmap loc lg_mapEntry))
      with "Hmv") as "[Hmv #Hmv_f]".
    { apply auth_update_alloc.
      apply alloc_singleton_local_update; [exact Hl_nin | done]. }
    iMod (own_update _ _
      (● ((to_agree : nat → agree nat) <$> <[from := to]>rs : gmap nat _) ⋅
       ◯ {[from := to_agree to]})
      with "Hrs") as "[Hrs #Hrs_f]".
    { rewrite fmap_insert.
      apply auth_update_alloc.
      apply alloc_singleton_local_update; [|done].
      rewrite lookup_fmap Hrsfrom //. }
    iModIntro.
    rewrite /visited_mapg_auth.
    iSplitR "Hms_f Hd_f Hmv_f Hrs_f"; last by iFrame "Hms_f Hd_f Hmv_f Hrs_f".
    iExists (<[γ := to_agree (tt : unitO)]>d), ps,
      (<[from := Cinr (to_agree (γ : leibnizO gname))]>gm),
      pvm,
      (<[l := Cinr (to_agree (γ : leibnizO gname)) : lg_mapEntry]>m_v),
      (<[from := to]>rs).
    rewrite dom_insert_L (comm_L union {[l]} (dom m_v)).
    iFrame "Hms Hd Hps Hpn Hgm Hctr Hpvm Hmv Hsmeta' Hrs".
    iPureIntro.
    split_and!.
    - rewrite dom_insert_L (subseteq_union_1_L {[from]} (dom gm)); [done|].
      apply elem_of_subseteq_singleton, elem_of_dom; rewrite Hgm_from_cinl; eauto.
    - exact Hdompvm.
    - destruct Hgmm as [Hgmm1 Hgmm2]. split.
      + intros id γ' Hgm'.
        destruct (decide (id = from)) as [-> | Hne_id].
        * rewrite lookup_insert in Hgm'. injection Hgm' as Hγ'_eq.
          subst γ'. left. by rewrite lookup_insert.
        * rewrite lookup_insert_ne in Hgm'; [|done].
          apply Hgmm1 in Hgm' as [Hm | Hm].
          -- destruct (decide (γ' = γ)) as [-> | Hne_γ].
             { exfalso. rewrite Hmγ_pend in Hm. discriminate. }
             { left. rewrite lookup_insert_ne; done. }
          -- destruct (decide (γ' = γ)) as [-> | Hne_γ].
             { exfalso. rewrite Hmγ_pend in Hm. discriminate. }
             { right. rewrite lookup_insert_ne; done. }
      + intros id γ' Hm'.
        destruct (decide (id = from)) as [-> | Hne_id].
        * rewrite lookup_insert.
          assert (γ' = γ) as ->.
          { destruct (decide (γ' = γ)) as [-> | Hne_γ]; [done|].
            rewrite lookup_insert_ne in Hm'; [|done].
            exfalso. have Hcin := Hgmm2 from γ' Hm'.
            rewrite Hgm_from_cinl in Hcin. discriminate. }
          done.
        * rewrite lookup_insert_ne; [|done]. apply Hgmm2.
          destruct (decide (γ' = γ)) as [-> | Hne_γ].
          -- rewrite lookup_insert in Hm'. injection Hm' as ->.
             exfalso. exact (Hne_id eq_refl).
          -- rewrite lookup_insert_ne in Hm'; done.
    - (* id_susp_gamma_coherent on new state *)
      intros id γ' Hgm'.
      destruct (decide (id = from)) as [-> | Hne_id].
      + rewrite lookup_insert in Hgm'. injection Hgm' as Hγ'_eq.
        subst γ'. exists l. split; [exact Hpvf_eq|].
        by rewrite lookup_insert.
      + rewrite lookup_insert_ne in Hgm'; [|done].
        destruct (Hisgc id γ' Hgm') as (susp & Hpvm_id & Hmv_susp).
        exists susp. split; [exact Hpvm_id|].
        destruct (decide (susp = l)) as [-> | Hne_susp].
        * exfalso. assert (l ∈ dom m_v) as Hl_in.
          { apply elem_of_dom.
            destruct (m_v !! l) eqn:Hl; [eauto|].
            rewrite Hl in Hmv_susp. by inversion Hmv_susp. }
          apply not_elem_of_dom in Hl_nin. set_solver.
        * rewrite lookup_insert_ne; done.
    - (* id_ref_coherent on new state *)
      intros from' to' Hrs'.
      destruct (decide (from' = from)) as [-> | Hne].
      + rewrite lookup_insert in Hrs'. injection Hrs' as ->.
        split; [exact Hlt|]. split.
        { exists γ. by rewrite lookup_insert. }
        exists l, susp_to. by repeat split.
      + rewrite lookup_insert_ne in Hrs'; [|done].
        destruct (Hirc from' to' Hrs') as [Hlt' [(γ'' & Hgm_from') (sf & st & Hpf & Hpt & Hneq)]].
        split; [exact Hlt'|]. split.
        { exists γ''. rewrite lookup_insert_ne; [exact Hgm_from'|done]. }
        exists sf, st. by repeat split.
    - intros γ' Hdγ'.
      destruct (decide (γ' = γ)) as [-> | Hne].
      + left. exists from. by rewrite lookup_insert.
      + rewrite lookup_insert_ne in Hdγ'; [|done].
        destruct (Hdid γ' Hdγ') as [[n' Hmγ] | Hmγ].
        * left. exists n'. rewrite lookup_insert_ne; done.
        * right. rewrite lookup_insert_ne; done.
    - destruct Hpcoh as [Hsize Hl_pcoh]. split; [exact Hsize|].
      intros γ' Hγ'. destruct (decide (γ' = γ)) as [-> | Hne].
      + exfalso. rewrite lookup_insert in Hγ'.
        rewrite /done_val /pending_val in Hγ'. by inversion Hγ'.
      + rewrite lookup_insert_ne in Hγ'; [|done]. by apply Hl_pcoh.
  Qed.

  (** [bind_id_existing_susp]: bind an existing id [from] (whose susp loc
      [susp_from] is *already* in [m_v]) to a γ that the susp is already
      bound to. Distinguished from [bind_id_fresh_susp] by not writing
      [m_v] — the susp→γ binding is taken as the input [lg_mapg_frag
      susp_from γ]. Writes [m] (γ → done_val from), [d] (γ → ()), [gm]
      (Cinl → Cinr γ at [from]), and [rs] ([from] → [to]). [pvm] and
      [m_v] are unchanged. *)
  Lemma bind_id_existing_susp
      m pn ctr
      from to γ susp_from susp_to :
    to < from →
    susp_from ≠ susp_to →
    id_token from -∗
    visit_pending γ -∗
    pval_frag from susp_from -∗
    pval_frag to susp_to -∗
    lg_mapg_frag susp_from γ -∗
    visited_mapg_auth m pn ctr ==∗
      visited_mapg_auth (<[γ := done_val from]>m) pn ctr ∗
      visit_done γ from ∗
      id_ref_frag from to.
  Proof.
    iIntros (Hlt Hneq) "Htok Hpen #Hpvf #Hpvt #Hlbf
              (%d & %ps & %gm & %pvm & %m_v & %rs & Hms & Hd & Hps & Hpn & Hgm & Hctr & Hpvm & Hmv & Hsmeta & Hrs &
               %Hdom & %Hdompvm & %Hgmm & %Hisgc & %Hirc & %Hdid & %Hpcoh)".
    rewrite /pval_frag /id_token /visit_pending
            /visit_done /visit_reached_done /lg_mapg_frag /id_ref_frag.
    iDestruct (own_valid_2 with "Hms Hpen") as %Hvm.
    apply auth_both_valid_discrete in Hvm as [Hinclm Hvalidm].
    apply (singleton_included_exclusive_l m γ pending_val) in Hinclm; [|apply _|exact Hvalidm].
    assert (m !! γ = Some pending_val) as Hmγ_pend
      by (apply some_pending_val_equiv_eq; exact Hinclm).
    iDestruct (own_valid with "Hd") as %Hvd_auth.
    pose proof (proj1 (auth_auth_valid d) Hvd_auth) as Hvd_auth'.
    assert (d !! γ = None) as Hdγ.
    { destruct (d !! γ) as [xd|] eqn:Hdeq; [|done].
      exfalso.
      assert (✓ xd) as Hvxd.
      { apply (lookup_valid_Some d γ xd Hvd_auth'). rewrite Hdeq. done. }
      assert (d !! γ ≡ Some (to_agree (tt : unitO))) as Hdg_eq.
      { rewrite Hdeq. f_equiv.
        apply to_agree_uninj in Hvxd as [u Hxd_eq].
        destruct u. by rewrite Hxd_eq. }
      destruct (Hdid γ Hdg_eq) as [[n Hmγ] | Hmγ];
        rewrite Hmγ_pend in Hmγ; discriminate. }
    iDestruct (own_valid_2 with "Hgm Htok") as %Hvgm.
    apply auth_both_valid_discrete in Hvgm as [Hinclgm Hvalidgm].
    apply (singleton_included_exclusive_l gm from (Cinl (Excl ()))) in Hinclgm; [|apply _|exact Hvalidgm].
    assert (gm !! from = Some (Cinl (Excl ()))) as Hgm_from_cinl
      by (apply some_cinl_excl_unit_equiv_eq; exact Hinclgm).
    (* rs !! from = None: derived from id_ref_coherent + Hgm_from_cinl. *)
    assert (rs !! from = None) as Hrsfrom.
    { destruct (rs !! from) as [to'|] eqn:Hr; [|done].
      exfalso. pose proof (Hirc from to' Hr) as [_ [(γ' & Hgm_eq) _]].
      rewrite Hgm_from_cinl in Hgm_eq. by inversion Hgm_eq. }
    iDestruct (pvalmap_auth_frag_eq with "Hpvm Hpvf") as %Hpvf_eq.
    iDestruct (pvalmap_auth_frag_eq with "Hpvm Hpvt") as %Hpvt_eq.
    (* m_v !! susp_from ≡ Some (Cinr (to_agree γ)) from lg_mapg_frag *)
    iDestruct (own_valid_2 with "Hmv Hlbf") as %Hv_mv.
    apply auth_both_valid_discrete in Hv_mv as [Hinc_mv Hvalid_mv].
    apply singleton_included_l in Hinc_mv as (x_mv & Hx_mv & Hle_mv).
    assert (m_v !! susp_from ≡ Some (Cinr (to_agree (γ : leibnizO gname))))
      as Hmv_susp_from.
    { assert (✓ x_mv) as Hvx.
      { eapply (lookup_valid_Some _ susp_from); first exact Hvalid_mv.
        exact Hx_mv. }
      assert (Cinr (to_agree (γ : leibnizO gname)) ≡ x_mv) as Heq_x.
      { apply Some_included in Hle_mv as [Heq2 | Hinc]; [exact Heq2|].
        apply csum_included in Hinc
          as [Hbot | [(? & ? & Heq1 & _) | (b & b' & Heq1 & Heq2 & Hle)]].
        - exfalso. rewrite Hbot in Hvx. by inversion Hvx.
        - by inversion Heq1.
        - injection Heq1 as Hbeq. subst x_mv. rewrite -Hbeq in Hle.
          assert (✓ b') as Hvb' by (by apply (Cinr_valid (A:=exclR unitO)) in Hvx).
          pose proof (agree_valid_included _ _ Hvb' Hle) as Heq_ag.
          by rewrite Heq_ag. }
      rewrite Hx_mv -Heq_x //. }
    iMod (own_update_2 _ _ _
      (● <[γ := done_val from]>m ⋅ ◯ {[γ := done_val from]})
      with "Hms Hpen") as "[Hms Hms_f]".
    { apply auth_update, singleton_local_update_any.
      intros x Hx. unfold pending_val.
      apply (exclusive_local_update _ (done_val from)). done. }
    iMod (own_update _ _
      (● <[γ := to_agree (tt : unitO)]>d ⋅ ◯ {[γ := to_agree (tt : unitO)]})
      with "Hd") as "[Hd #Hd_f]".
    { apply auth_update_alloc, alloc_singleton_local_update; done. }
    iMod (own_update_2 _ _ _
      (● <[from := Cinr (to_agree (γ : leibnizO gname))]>gm ⋅
       ◯ {[from := Cinr (to_agree (γ : leibnizO gname))]})
      with "Hgm Htok") as "[Hgm _]".
    { apply auth_update, singleton_local_update_any.
      intros y _. apply exclusive_local_update. done. }
    iMod (own_update _ _
      (● ((to_agree : nat → agree nat) <$> <[from := to]>rs : gmap nat _) ⋅
       ◯ {[from := to_agree to]})
      with "Hrs") as "[Hrs #Hrs_f]".
    { rewrite fmap_insert.
      apply auth_update_alloc.
      apply alloc_singleton_local_update; [|done].
      rewrite lookup_fmap Hrsfrom //. }
    iModIntro.
    rewrite /visited_mapg_auth.
    iSplitR "Hms_f Hd_f Hrs_f"; last by iFrame "Hms_f Hd_f Hrs_f".
    iExists (<[γ := to_agree (tt : unitO)]>d), ps,
      (<[from := Cinr (to_agree (γ : leibnizO gname))]>gm),
      pvm, m_v, (<[from := to]>rs).
    iFrame "Hms Hd Hps Hpn Hgm Hctr Hpvm Hmv Hsmeta Hrs".
    iPureIntro.
    split_and!.
    - rewrite dom_insert_L (subseteq_union_1_L {[from]} (dom gm)); [done|].
      apply elem_of_subseteq_singleton, elem_of_dom; rewrite Hgm_from_cinl; eauto.
    - exact Hdompvm.
    - destruct Hgmm as [Hgmm1 Hgmm2]. split.
      + intros id γ' Hgm'.
        destruct (decide (id = from)) as [-> | Hne_id].
        * rewrite lookup_insert in Hgm'. injection Hgm' as Hγ'_eq.
          subst γ'. left. by rewrite lookup_insert.
        * rewrite lookup_insert_ne in Hgm'; [|done].
          apply Hgmm1 in Hgm' as [Hm | Hm].
          -- destruct (decide (γ' = γ)) as [-> | Hne_γ].
             { exfalso. rewrite Hmγ_pend in Hm. discriminate. }
             { left. rewrite lookup_insert_ne; done. }
          -- destruct (decide (γ' = γ)) as [-> | Hne_γ].
             { exfalso. rewrite Hmγ_pend in Hm. discriminate. }
             { right. rewrite lookup_insert_ne; done. }
      + intros id γ' Hm'.
        destruct (decide (id = from)) as [-> | Hne_id].
        * rewrite lookup_insert.
          assert (γ' = γ) as ->.
          { destruct (decide (γ' = γ)) as [-> | Hne_γ]; [done|].
            rewrite lookup_insert_ne in Hm'; [|done].
            exfalso. have Hcin := Hgmm2 from γ' Hm'.
            rewrite Hgm_from_cinl in Hcin. discriminate. }
          done.
        * rewrite lookup_insert_ne; [|done]. apply Hgmm2.
          destruct (decide (γ' = γ)) as [-> | Hne_γ].
          -- rewrite lookup_insert in Hm'. injection Hm' as ->.
             exfalso. exact (Hne_id eq_refl).
          -- rewrite lookup_insert_ne in Hm'; done.
    - (* id_susp_gamma_coherent on new state *)
      intros id γ' Hgm'.
      destruct (decide (id = from)) as [-> | Hne_id].
      + rewrite lookup_insert in Hgm'. injection Hgm' as Hγ'_eq.
        subst γ'. exists susp_from. split; [exact Hpvf_eq|exact Hmv_susp_from].
      + rewrite lookup_insert_ne in Hgm'; [|done].
        by apply (Hisgc id γ').
    - (* id_ref_coherent on new state *)
      intros from' to' Hrs'.
      destruct (decide (from' = from)) as [-> | Hne].
      + rewrite lookup_insert in Hrs'. injection Hrs' as ->.
        split; [exact Hlt|]. split.
        { exists γ. by rewrite lookup_insert. }
        exists susp_from, susp_to. by repeat split.
      + rewrite lookup_insert_ne in Hrs'; [|done].
        destruct (Hirc from' to' Hrs') as [Hlt' [(γ'' & Hgm_from') (sf & st & Hpf & Hpt & Hneq')]].
        split; [exact Hlt'|]. split.
        { exists γ''. rewrite lookup_insert_ne; [exact Hgm_from'|done]. }
        exists sf, st. by repeat split.
    - intros γ' Hdγ'.
      destruct (decide (γ' = γ)) as [-> | Hne].
      + left. exists from. by rewrite lookup_insert.
      + rewrite lookup_insert_ne in Hdγ'; [|done].
        destruct (Hdid γ' Hdγ') as [[n' Hmγ] | Hmγ].
        * left. exists n'. rewrite lookup_insert_ne; done.
        * right. rewrite lookup_insert_ne; done.
    - destruct Hpcoh as [Hsize Hl_pcoh]. split; [exact Hsize|].
      intros γ' Hγ'. destruct (decide (γ' = γ)) as [-> | Hne].
      + exfalso. rewrite lookup_insert in Hγ'.
        rewrite /done_val /pending_val in Hγ'. by inversion Hγ'.
      + rewrite lookup_insert_ne in Hγ'; [|done]. by apply Hl_pcoh.
  Qed.

  (** [pval_snapshot susp k M] is a persistent "freshness snapshot": at
      some past moment the id-counter was [k], [M] enumerated every id in
      [set_seq 0 k] together with the susp registered there, and [susp]
      was not among those susps. Combined with [pval_frag id' susp'] for
      [id' < k] this gives [susp ≠ susp']. *)
  Definition pval_snapshot (susp : loc) (k : nat) (M : gmap nat loc) : iProp Σ :=
    ⌜dom M = set_seq 0 k⌝ ∗
    ⌜susp ∉ (map_img M : gset loc)⌝ ∗
    [∗ map] id ↦ susp_id ∈ M, pval_frag id susp_id.

  Global Instance pval_snapshot_persistent susp k M : Persistent (pval_snapshot susp k M).
  Proof. apply _. Qed.

  Global Instance pval_snapshot_timeless susp k M : Timeless (pval_snapshot susp k M).
  Proof. apply _. Qed.

  (** Mint a [pval_snapshot] from the auth and a user-supplied collection of
      [pval_frag] + [lg_mapg_frag] covering every id in [set_seq 0 k]. The
      [lg_mapg_frag] entries witness that each susp in [M] is bound in
      [m_v], i.e. lives in [dom m_v]. Combined with [vmeta_token susp]
      (which forces [susp ∉ dom m_v]), this gives [susp ∉ map_img M].
      No state changes; we only extract a pure fact. *)
  Lemma pval_snapshot_alloc m pn k susp (M : gmap nat loc) :
    dom M = set_seq 0 k →
    vmeta_token susp -∗
    visited_mapg_auth m pn k -∗
    ([∗ map] id ↦ susp_id ∈ M, pval_frag id susp_id ∗ ∃ γ, lg_mapg_frag susp_id γ) -∗
      vmeta_token susp ∗ visited_mapg_auth m pn k ∗ pval_snapshot susp k M.
  Proof.
    iIntros (Hdom) "Hvtok Hauth #Hmap".
    iDestruct "Hauth" as "(%d & %ps & %gm & %pvm & %m_v & %rs & Hms & Hd & Hps & Hpn & Hgm & Hctr & Hpvm & Hmv & Hsmeta & Hrs & %Hgm_dom & %Hpvm_dom & %Hgmm & %Hisgc & %Hirc & %Hdid & %Hpcoh)".
    (* Show susp ∉ dom m_v via vmeta_token + spec_meta accumulator. *)
    iDestruct (own_valid_2 with "Hsmeta Hvtok") as %Hsm_v.
    rewrite auth_frag_op_valid gset_disj_valid_op in Hsm_v.
    assert (susp ∉ dom m_v) as Hsusp_notin by set_solver.
    (* Show every susp_id in map_img M is in dom m_v. *)
    iAssert (∀ l, ⌜l ∈ (map_img M : gset loc)⌝ -∗ ⌜l ∈ dom m_v⌝)%I as %Hsub.
    { iIntros (l Hl%elem_of_map_img).
      destruct Hl as [id Hid].
      iDestruct (big_sepM_lookup _ _ id l Hid with "Hmap")
        as "[_ (%γ & Hlbf)]".
      rewrite /lg_mapg_frag.
      iDestruct (own_valid_2 with "Hmv Hlbf") as %Hlb_v.
      apply auth_both_valid_discrete in Hlb_v as [Hincl _].
      apply singleton_included_l in Hincl as (y & Hy & _).
      iPureIntro. apply elem_of_dom. destruct (m_v !! l) as [a|] eqn:Hl_eq.
      - by eexists.
      - rewrite Hl_eq in Hy. by inversion Hy. }
    iFrame "Hvtok". iSplitR "".
    { iExists d, ps, gm, pvm, m_v, rs.
      iFrame "Hms Hd Hps Hpn Hgm Hctr Hpvm Hmv Hsmeta Hrs". iPureIntro. eauto 10. }
    rewrite /pval_snapshot.
    iSplit; [done|]. iSplit.
    { iPureIntro. intros Hin. apply Hsub in Hin. set_solver. }
    iApply (big_sepM_mono with "Hmap").
    iIntros (?? _) "[$ _]".
  Qed.

  (** [pval_snapshot susp k M] + [pval_frag id' susp'] with [id' < k]
      yields [susp ≠ susp']. The snapshot's big-sep gives a
      [pval_frag id' susp_id'] for the snapshot value; agreement at id'
      forces [susp' = susp_id']; [susp_id' ∈ map_img M] combined with
      [susp ∉ map_img M] gives the inequality. No auth needed. *)
  Lemma pval_snapshot_neq susp k M id' susp' :
    id' < k →
    pval_snapshot susp k M -∗ pval_frag id' susp' -∗ ⌜susp ≠ susp'⌝.
  Proof.
    iIntros (Hlt) "(%Hdom & %Hnotin & #Hsnap) #Hpv".
    assert (id' ∈ dom M) as Hin.
    { rewrite Hdom. apply elem_of_set_seq. lia. }
    apply elem_of_dom in Hin as [susp_id Hmid].
    iDestruct (big_sepM_lookup _ _ id' susp_id Hmid with "Hsnap") as "Hpv'".
    iDestruct (pval_frag_agree with "Hpv Hpv'") as %->.
    iPureIntro. intros ->. apply Hnotin. by eapply elem_of_map_img_2.
  Qed.

End lg_map.


Section map_res.
  Context `{!correctnessG Σ}.

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
    own mapG_name (◯ {[ k := Cinr (to_agree (tt : unitO)) ]}).

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
      mapg_auth (<[ k := Cinr (to_agree (tt : unitO)) ]> m) ∗ mapg_removed k.
  Proof.
    rewrite /mapg_auth /mapg_frag /mapg_removed. iIntros "H1 H2".
    iMod (own_update_2 _ _ _
      (● <[ k := Cinr (to_agree (tt : unitO)) ]> m ⋅
       ◯ {[ k := Cinr (to_agree (tt : unitO)) ]})
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
    mapg_alive (<[ k := Cinr (to_agree (tt : unitO)) ]> m)
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


Section cap_res.
  Context `{!correctnessG Σ}.

  Definition cap_type := gmap nat (agree nat).

  Definition cap_auth (m : cap_type) : iProp Σ :=
    own capG_name (● m).

  Definition cap_insert_auth (m : cap_type) id n : iProp Σ :=
    own capG_name (● <[ id := to_agree n ]> m).

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
    cap_auth m ==∗ cap_insert_auth m id n ∗ cap_frag id n.
  Proof.
    rewrite /cap_auth /cap_insert_auth /cap_frag. iIntros (Hfresh) "H".
    iMod (own_update with "H") as "[$ $]"; last done.
    apply auth_update_alloc.
    by apply alloc_singleton_local_update.
  Qed.

End cap_res.


Section intransit_res.
  Context `{!correctnessG Σ}.

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


Section state_res.
  Context `{!correctnessG Σ}.

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


Section state_tok_res.
  Context `{!correctnessG Σ}.

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


Section suspfilledmap_res.
  Context `{!correctnessG Σ, !spec_metaG Σ}.

  Definition suspfilledmap_type := gmap loc gname.

  (* Auth tracking the loc → gname binding. The [◯ GSet (dom m)] fragment
     at [spec_meta_name] is what makes [vmeta_token l] enforce freshness
     at insertion. *)
  Definition suspfilledmap_auth (m : suspfilledmap_type) : iProp Σ :=
    own suspfilledmapG_name (● ((to_agree <$> m) : gmap loc (agreeR gnameO))) ∗
    own spec_meta_name (◯ GSet (dom m)).

  (* Persistent agreement that loc [l] is bound to gname [γ]. *)
  Definition suspfilledmap_frag (l : loc) (γ : gname) : iProp Σ :=
    own suspfilledmapG_name (◯ {[ l := to_agree γ ]}).

  Global Instance suspfilledmap_frag_persistent l γ :
    Persistent (suspfilledmap_frag l γ).
  Proof. apply _. Qed.

  Definition unfilled (l : loc) : iProp Σ :=
    ∃ γ, suspfilledmap_frag l γ ∗ own γ (Cinl (Excl ()) : suspfilledStateUR).

  Definition filled (l : loc) : iProp Σ :=
    ∃ γ, suspfilledmap_frag l γ ∗ own γ (Cinr (to_agree (tt : unitO)) : suspfilledStateUR).

  Global Instance filled_persistent l : Persistent (filled l).
  Proof. apply _. Qed.

  Lemma suspfilledmap_frag_agree l γ1 γ2 :
    suspfilledmap_frag l γ1 -∗ suspfilledmap_frag l γ2 -∗ ⌜γ1 = γ2⌝.
  Proof.
    rewrite /suspfilledmap_frag. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    rewrite -auth_frag_op singleton_op auth_frag_valid singleton_valid in Hv.
    by apply to_agree_op_inv_L in Hv.
  Qed.

  Lemma unfilled_excl l :
    unfilled l -∗ unfilled l -∗ False.
  Proof.
    iIntros "(%γ1 & #Hfr1 & Hs1) (%γ2 & #Hfr2 & Hs2)".
    iDestruct (suspfilledmap_frag_agree with "Hfr1 Hfr2") as %<-.
    iDestruct (own_valid_2 with "Hs1 Hs2") as %Hv.
    by apply (Cinl_valid (B:=agreeR unitO)), exclusive_l in Hv.
  Qed.

  Lemma unfilled_filled_excl l :
    unfilled l -∗ filled l -∗ False.
  Proof.
    iIntros "(%γ1 & #Hfr1 & Hs1) (%γ2 & #Hfr2 & #Hs2)".
    iDestruct (suspfilledmap_frag_agree with "Hfr1 Hfr2") as %<-.
    iDestruct (own_valid_2 with "Hs1 Hs2") as %Hv.
    done.
  Qed.

  (* Local variant of [vmeta_combine_dom] for [suspfilledmap_type]. The proof
     is identical — only the value type of the gmap differs. *)
  Local Lemma suspfilledmap_combine_dom (m : suspfilledmap_type) (l : loc) (γ : gname) :
    vmeta_token l -∗ own spec_meta_name (◯ GSet (dom m)) -∗
      ⌜l ∉ dom m⌝ ∗ own spec_meta_name (◯ GSet (dom (<[ l := γ ]> m))).
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

  (* Insert a fresh loc as unfilled. Uses [vmeta_token l] for freshness
     (the [spec_meta_name] auth is shared with [lg_mapg_auth]), allocates
     a fresh per-loc gname, and produces the loc → gname binding
     fragment together with the per-γ unfilled state. *)
  Lemma suspfilledmap_insert_unfilled m l :
    vmeta_token l -∗ suspfilledmap_auth m ==∗
      ∃ γ, suspfilledmap_auth (<[ l := γ ]> m) ∗ unfilled l.
  Proof.
    rewrite /suspfilledmap_auth /unfilled /suspfilledmap_frag.
    iIntros "Hvtok (Hauth & Hsmeta)".
    iMod (own_alloc (Cinl (Excl ()) : suspfilledStateUR)) as (γ) "Hγ"; [done|].
    iDestruct (suspfilledmap_combine_dom m l γ with "Hvtok Hsmeta") as "[%Hl_nin Hsmeta']".
    apply not_elem_of_dom in Hl_nin.
    iMod (own_update with "Hauth") as "[Hauth Hfr]".
    { apply auth_update_alloc, (alloc_singleton_local_update _ l (to_agree γ));
        [|done].
      by rewrite lookup_fmap Hl_nin. }
    iModIntro. iExists γ.
    rewrite fmap_insert. iFrame "Hauth Hsmeta'".
    iExists γ. by iFrame.
  Qed.

  (* Transition unfilled → filled. The per-γ state is exclusive in CSum,
     so [cmra_update_exclusive] swaps [Cinl (Excl ())] for
     [Cinr (to_agree (tt : unitO))] without touching the loc → gname auth. *)
  Lemma unfilled_to_filled l :
    unfilled l ==∗ filled l.
  Proof.
    iIntros "(%γ & #Hfr & Hγ)".
    iMod (own_update with "Hγ") as "Hγ".
    { apply (cmra_update_exclusive (Cinr (to_agree (tt : unitO)) : suspfilledStateUR)).
      done. }
    iModIntro. iExists γ. by iFrame.
  Qed.

End suspfilledmap_res.
