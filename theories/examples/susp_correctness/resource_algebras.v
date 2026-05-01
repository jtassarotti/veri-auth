From auth.prelude Require Import stdpp.
From auth.rel_logic_tern_susp Require Export model.
From iris.algebra Require Import gmap auth excl gset csum frac.
From iris.algebra.lib Require Import dfrac_agree.


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
Class visited_mapG Σ := VisitedMapG {
  visited_state_inG :> inG Σ visited_state_mapUR;
  visited_done_inG :> inG Σ visited_done_mapUR;
  pending_set_inG :> inG Σ pending_setUR;
  visited_state_name : gname;
  visited_done_name : gname;
  pending_set_name : gname;
}.

Section visited_map_res.
  Context `{!visited_mapG Σ}.

  Definition state_val_type := csumR (exclR (optionO natO)) (agreeR natO).
  Definition state_mapg_type := gmap gname state_val_type.
  Definition done_mapg_type := gmap gname (agreeR natO).
  Definition pending_setg_type := gset gname.

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

  Definition pending_coherent (m : state_mapg_type) (ps : pending_setg_type) (pending_n : nat) : Prop :=
    pending_n = size ps ∧
      ∀ γ, m !! γ = Some pending_val → γ ∈ ps.

  Definition visited_mapg_auth (m : state_mapg_type) (d : done_mapg_type) (ps : pending_setg_type) (pending_n : nat) : iProp Σ :=
    own visited_state_name (● m) ∗ own visited_done_name (● d) ∗
    own pending_set_name (● GSet ps) ∗
    ⌜visited_coherent m d⌝ ∗ ⌜pending_coherent m ps pending_n⌝.

  Definition visited_map_update_pending
      (m : state_mapg_type) (d : done_mapg_type) (ps : pending_setg_type) pn (γs : gset gname) : iProp Σ :=
    let m' := set_fold (λ γ m, <[ γ := pending_val ]>m) m γs in
    let ps' := ps ∪ γs in
    own visited_state_name (● m') ∗
    own visited_done_name (● d) ∗
    own pending_set_name (● GSet ps') ∗
    ⌜visited_coherent m' d⌝ ∗
    ⌜pending_coherent m' ps' (pn + size γs)⌝.

  Definition visited_map_update_done
      (m : state_mapg_type) (d : done_mapg_type) (ps : pending_setg_type) pn γ n : iProp Σ :=
    own visited_state_name (● <[ γ := done_val n ]>m) ∗
    own visited_done_name (● <[ γ := to_agree n ]>d) ∗
    own pending_set_name (● GSet ps) ∗
    ⌜visited_coherent (<[ γ := done_val n ]>m) (<[ γ := to_agree n ]>d)⌝ ∗
    ⌜pending_coherent (<[ γ := done_val n ]>m) ps pn⌝.

  Definition visited_map_update_finished
      (m : state_mapg_type) (d : done_mapg_type) (ps : pending_setg_type) pn γ n : iProp Σ :=
    own visited_state_name (● <[ γ := finished_val n ]>m) ∗
    own visited_done_name (● d) ∗
    own pending_set_name (● GSet ps) ∗
    ⌜visited_coherent (<[ γ := finished_val n ]>m) d⌝ ∗
    ⌜pending_coherent (<[ γ := finished_val n ]>m) ps pn⌝.

  Definition visited_mapg_pending_removed (m : state_mapg_type) (d : done_mapg_type) (ps : pending_setg_type) (pending_n : nat) (γs : gset gname) : iProp Σ :=
    own visited_state_name (● m) ∗ own visited_done_name (● d) ∗
    own pending_set_name (● GSet (ps ∖ γs)) ∗
    ⌜visited_coherent m d⌝ ∗ ⌜pending_coherent m (ps ∖ γs) (pending_n - size γs)⌝.

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

  Lemma visited_insert m d ps pn :
    visited_mapg_auth m d ps pn ==∗
      ∃ γ,
        visited_map_update_pending m d ps pn {[γ]} ∗
          visit_pending γ ∗ penset_frag {[γ]}.
  Proof.
    iIntros "(Hms & Hd & Hps & %Hcoh & %Hpcoh)".
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
    iModIntro. iExists γ.
    rewrite /visited_map_update_pending /visit_pending /penset_frag.
    rewrite set_fold_singleton size_singleton (union_comm_L ps {[γ]}) /=.
    iFrame "Hms' Hd Hps' Hp Hpsf".
    iPureIntro. split.
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

  Lemma visited_transition_done m d ps pn γ n :
    d !! γ = None →
    visited_mapg_auth m d ps pn -∗ visit_pending γ
    ==∗ visited_map_update_done m d ps pn γ n ∗ visit_done γ n.
  Proof.
    iIntros (Hdγ) "(Hms & Hd & Hps & %Hcoh & %Hpcoh) H1".
    rewrite /visited_map_update_done /visit_done /visit_reached_done.
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
    iFrame "Hps Hf". iPureIntro. split.
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

  Lemma visited_transition_finished m d ps pn γ n :
    visited_mapg_auth m d ps pn -∗ visit_done γ n
    ==∗ visited_map_update_finished m d ps pn γ n ∗ visit_finished γ n.
  Proof.
    iIntros "(Hms & Hd & Hps & %Hcoh & %Hpcoh) [Hsfrag #Hreached]".
    rewrite /visited_map_update_finished /visit_finished /visit_reached_done.
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
    iFrame "Hd Hps Hreached". iPureIntro. split.
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

  Lemma get_visit_reached_done γ n m d ps pn :
    d !! γ = Some (to_agree n) →
    visited_mapg_auth m d ps pn ==∗ visited_mapg_auth m d ps pn ∗ visit_reached_done γ n.
  Proof.
    iIntros (Hd) "(Hms & Hd & Hps & %Hcoh & %Hpcoh)".
    rewrite /visit_reached_done.
    iMod (own_update _ _ (● d ⋅ ◯ {[γ := to_agree n]}) with "Hd") as "[Hd #Hr]".
    { apply auth_update_dfrac_alloc; [apply _|].
      apply singleton_included_l. exists (to_agree n). split; [by rewrite Hd|].
      apply Some_included_2. by left. }
    iModIntro. by iFrame "∗ # %".
  Qed.

  Lemma visited_reached_done_invalid γ n m d ps pn :
    visited_mapg_auth m d ps pn -∗ visit_reached_done γ n -∗ visit_pending γ -∗ False.
  Proof.
    iIntros "(Hms & Hd & Hps & %Hcoh & %Hpcoh) Hreached Hpending".
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

  Lemma pending_set_remove m d ps pn γs :
    visited_mapg_auth m d ps pn -∗ penset_frag γs -∗
    ([∗ set] γ ∈ γs, ∃ n, visit_reached_done γ n) ==∗
    visited_mapg_pending_removed m d ps pn γs.
  Proof.
    iIntros "(Hms & Hd & Hps & %Hcoh & %Hpcoh) Hfrag #Hreached".
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
    iModIntro. iFrame "Hms Hd Hps'". iPureIntro. split; first done.
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
  Context `{!lg_mapG Σ}.

  Definition lg_mapg_type := gmap loc lg_mapEntry.

  Definition lg_mapg_auth (m : lg_mapg_type) : iProp Σ :=
    own lg_mapG_name (● m).

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

  Lemma lg_mapg_insert m l γ :
    m !! l = None →
    lg_mapg_auth m ==∗
      lg_mapg_auth (<[ l := Cinr (to_agree γ) ]> m) ∗ lg_mapg_frag l γ.
  Proof.
    rewrite /lg_mapg_auth /lg_mapg_frag. iIntros (Hfresh) "H".
    iMod (own_update with "H") as "[$ $]"; last done.
    apply auth_update_alloc.
    by apply alloc_singleton_local_update.
  Qed.

  Lemma lg_mapg_insert_unalloc m l :
    m !! l = None →
    lg_mapg_auth m ==∗
      lg_mapg_auth (<[ l := Cinl (to_agree ()) ]> m) ∗ lg_mapg_unalloc l.
  Proof.
    rewrite /lg_mapg_auth /lg_mapg_unalloc. iIntros (Hfresh) "H".
    iMod (own_update with "H") as "[$ $]"; last done.
    apply auth_update_alloc.
    by apply alloc_singleton_local_update.
  Qed.

End lg_map.

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

Definition idcntrUR := authUR nat.
Class idcntrG Σ := IdcntrG { idcntr_inG :> inG Σ idcntrUR; idcntrG_name : gname }.

Section idcntr.
  Context `{!idcntrG Σ}.

  Definition id_frag (id : nat) := own idcntrG_name (●{DfracOwn (1/2)} id).

  Lemma id_agree id id' :
    id_frag id -∗ id_frag id' -∗ ⌜id = id'⌝ ∗ id_frag id ∗ id_frag id'.
  Proof.
    rewrite /id_frag. iIntros "H1 H2". iCombine "H1 H2" as "H".
    iDestruct (own_valid with "H") as %Hv.
    apply auth_auth_dfrac_op_valid in Hv as [_ [Heq _]].
    iDestruct "H" as "[H1 H2]". iFrame.
    iPureIntro. apply leibniz_equiv. exact Heq.
  Qed.

  Lemma id_update id id' (Hle : id ≤ id') :
    id_frag id -∗ id_frag id ==∗ id_frag id' ∗ id_frag id'.
  Proof.
    rewrite /id_frag. iIntros "H1 H2". iCombine "H1 H2" as "H".
    iMod (own_update with "H") as "H".
    { apply (auth_update_auth id id' (id' - id)).
      apply (nat_local_update id 0 id' (id' - id)). lia. }
    iDestruct "H" as "[H1 H2]". iFrame. done.
  Qed.

End idcntr.

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
