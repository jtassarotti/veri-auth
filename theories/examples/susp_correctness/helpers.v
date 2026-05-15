From auth.prelude Require Import stdpp.
From auth.rel_logic_tern_susp Require Export spec_rules spec_tactics.
From iris.algebra Require Import gmap auth excl csum agree.
From iris.algebra.lib Require Import dfrac_agree.
From auth.examples.susp_correctness Require Import resource_algebras definitions.

Lemma gset_max_elem_of (X : gset nat) :
  X ≠ ∅ → set_fold Nat.max 0 X ∈ X.
Proof.
  intros HX.
  apply (set_fold_ind_L (fun r X => (X = ∅ → r = 0) ∧ (X ≠ ∅ → r ∈ X))).
  - split; [done|set_solver].
  - intros x X0 r Hxni [Hempty Hnonempty]. split; [set_solver|].
    intros _. destruct (decide (X0 = ∅)) as [-> | HX0].
    { rewrite Hempty //. rewrite Nat.max_0_r. set_solver. }
    specialize (Hnonempty HX0).
    assert (Nat.max x r = x ∨ Nat.max x r = r) as [-> | ->] by lia; set_solver.
  - exact HX.
Qed.

Lemma gset_max_ge (X : gset nat) (x : nat) :
  x ∈ X → x ≤ set_fold Nat.max 0 X.
Proof.
  intros Hx. revert x Hx.
  apply (set_fold_ind_L (fun r X => ∀ x, x ∈ X → x ≤ r)).
  - set_solver.
  - intros y X0 r Hni IH z Hz.
    apply elem_of_union in Hz as [Hz%elem_of_singleton | Hz]; [lia|].
    apply IH in Hz. lia.
Qed.

Lemma size_set_map_inj_nat_val (X : gset nat) (f : nat → val) :
  Inj eq eq f → size (set_map f X : gset val) = size X.
Proof.
  intros Hinj. unfold set_map.
  rewrite size_list_to_set; [|by apply NoDup_fmap_2, NoDup_elements].
  rewrite length_fmap. unfold size, set_size. simpl. reflexivity.
Qed.

Lemma inj_val_of_nat : Inj (=) (=) (λ n : nat, #n).
Proof. intros n m. inversion 1. lia. Qed.

Lemma id_in_alive_dom (m : gmap val val) (D : gset nat) (n : nat) :
  size m = size D →
  (∀ (id : nat), id ∈ D → ∃ v, m !! #id = Some v) →
  (∃ v, m !! #n = Some v) →
  n ∈ D.
Proof.
  intros Hsize HsubD [v Hv].
  set (fD := set_map (λ k : nat, #k : val) D : gset val).
  assert (fD ⊆ dom m) as Hfsub.
  { intros u Hu. apply elem_of_map in Hu as [k [-> Hk]].
    apply HsubD in Hk as [v' Hv']. by apply elem_of_dom. }
  assert (size fD = size D) as HfDsize.
  { apply size_set_map_inj_nat_val, inj_val_of_nat. }
  assert (fD = dom m) as Hfdom.
  { apply set_subseteq_size_eq; [done|]. rewrite -size_dom in Hsize. lia. }
  assert (#n ∈ dom m) as Hndom by (apply elem_of_dom; eauto).
  rewrite -Hfdom in Hndom.
  apply elem_of_map in Hndom as [k [Heq Hk]].
  apply inj_val_of_nat in Heq as ->. exact Hk.
Qed.

Section authentikit_helpers.
  Context `{!authG Σ, !seqG Σ, !correctnessG Σ}.

  Lemma sub_susp_count_update_map :
    ∀ t v c (id : nat) Nc m,
      m !! id = None →
      ⌜c > 0⌝ -∗
      mapg_auth m -∗
      sub_susp_count t v c id Nc v ==∗
        mapg_auth (mapg_insert_def m id v) ∗
        sub_susp_count_frags t v c id Nc.
  Proof.
    iIntros (t v c id Nc m Hnone) "%Hc Hmauth Hcnt".
    iAssert (∀ (v_outer : val) (tind : evi_type) (vind : val) (cind : nat),
               ⌜cind > 0⌝ -∗ sub_susp_count tind vind cind id Nc v_outer -∗
               ∃ q, mapg_frag id q v_outer)%I with "[]" as "Hext".
    { iIntros (v_outer tind).
      iInduction tind as [t1 t2 | t1 t2 | | | ] "IH".
      all: iIntros (vind cind) "%Hci Hcnt'".
      - simpl. iDestruct "Hcnt'" as (c1 c2 v1 v2 [-> Hsum]) "[Hc1 Hc2]".
        destruct c1 as [|c1'].
        + assert (c2 > 0) by lia.
          iApply ("IH1" $! v2 c2 with "[%//] Hc2").
        + assert (S c1' > 0) by lia.
          iApply ("IH" $! v1 (S c1') with "[%//] Hc1").
      - simpl. iDestruct "Hcnt'" as "[H|H]".
        + iDestruct "H" as (?) "[-> Hc']".
          iApply ("IH" with "[%//] Hc'").
        + iDestruct "H" as (?) "[-> Hc']".
          iApply ("IH1" with "[%//] Hc'").
      - simpl. iDestruct "Hcnt'" as "[_ %Heq]". lia.
      - simpl. iDestruct "Hcnt'" as "[_ %Heq]". lia.
      - simpl. iDestruct "Hcnt'" as (v1) "[-> Hcases]".
        iDestruct "Hcases" as "[Hl|Hr]".
        + iDestruct "Hl" as (h) "%Heq". destruct Heq as [_ Heq]. lia.
        + iDestruct "Hr" as (susp) "[-> Hcases]".
          iDestruct "Hcases" as "[Hh|Hp]".
          * iDestruct "Hh" as (h) "[_ %Heq]". lia.
          * iDestruct "Hp" as (p γ) "(_ & _ & _ & Hfrag & _ & _)".
            iExists _. iFrame "Hfrag". }
    iDestruct ("Hext" $! v t v c with "[%//] Hcnt") as (q) "Hfrag".
    iDestruct (mapg_auth_alive with "Hmauth Hfrag") as %(y & Hy & _).
    rewrite Hnone in Hy. inversion Hy.
  Qed.

  Lemma mapg_remove_count_0 :
    ∀ t v id Nc m,
      Nc ≠ 0 →
      sub_susp_count_frags t v 0 id Nc -∗
      mapg_auth m
      ==∗
        sub_susp_count t v 0 id Nc v ∗
        mapg_auth (<[ id := Cinr (to_agree tt) ]> m) ∗
        mapg_removed id.
  Proof.
    iIntros (t v id Nc m HN) "(#Hcap & %Hle & Hcount & Hagg) Hmauth".
    iDestruct "Hagg" as "[%Heq | [%Hlt Hq]]".
    - exfalso. lia.
    - iDestruct "Hq" as (q Hqeq) "Hfrag".
      replace (Nc - 0) with Nc in Hqeq by lia.
      assert (q = 1%Qp) as ->.
      { apply (inj (λ q : Qp, (q * pos_to_Qp (Pos.of_nat Nc))%Qp)).
        rewrite Qp.mul_1_l. exact Hqeq. }
      iMod (mapg_remove with "Hmauth Hfrag") as "[Hmauth #Hrem]".
      iModIntro. iFrame "∗ #".
  Qed.

  Lemma no_fix_InjLV (v : val) : v = InjLV v → False.
  Proof.
    induction v; intros H; try discriminate.
    injection H as H. by apply IHv.
  Qed.

  Lemma no_fix_InjRV (v : val) : v = InjRV v → False.
  Proof.
    induction v; intros H; try discriminate.
    injection H as H. by apply IHv.
  Qed.

  Lemma sub_susp_count_ne_loc t (l : loc) c pid Nc v_outer :
    sub_susp_count t #l c pid Nc v_outer ⊢ False.
  Proof.
    iIntros "H".
    iInduction t as [t1 IH1 t2 IH2 | t1 IH1 t2 IH2 | | | ] ""
      forall (c); simpl.
    - iDestruct "H" as (? ? ? ? [Heq _]) "_". discriminate.
    - iDestruct "H" as "[H|H]"; iDestruct "H" as (?) "[%Heq _]"; discriminate.
    - iDestruct "H" as "[Hv _]". iDestruct "Hv" as (?) "%Heq". discriminate.
    - iDestruct "H" as "[Hv _]". iDestruct "Hv" as (?) "%Heq". discriminate.
    - iDestruct "H" as (v1) "[%Heq _]". discriminate.
  Qed.

  Lemma sub_susp_count_ne_injr_loc t (susp : loc) c pid Nc v_outer :
    sub_susp_count t (InjRV #susp) c pid Nc v_outer ⊢ False.
  Proof.
    iIntros "H".
    iInduction t as [t1 IH1 t2 IH2 | t1 IH1 t2 IH2 | | | ] ""
      forall (c); simpl.
    - iDestruct "H" as (? ? ? ? [Heq _]) "_". discriminate.
    - iDestruct "H" as "[H|H]".
      + iDestruct "H" as (?) "[%Heq _]". discriminate.
      + iDestruct "H" as (v) "[%Heq H]". injection Heq as <-.
        by iApply (sub_susp_count_ne_loc with "H").
    - iDestruct "H" as "[Hv _]". iDestruct "Hv" as (?) "%Heq". discriminate.
    - iDestruct "H" as "[Hv _]". iDestruct "Hv" as (?) "%Heq". discriminate.
    - iDestruct "H" as (v1) "[%Heq Hcases]". injection Heq as <-.
      iDestruct "Hcases" as "[H|H]".
      + iDestruct "H" as (h) "%Heq'". destruct Heq' as [Heq' _]. discriminate.
      + iDestruct "H" as (susp') "[%Heq' _]". discriminate.
  Qed.

  Lemma sub_susp_count_ne_injL_injR_susp t (susp : loc) c pid Nc v_outer :
    sub_susp_count t (InjLV (InjRV #susp)) c pid Nc v_outer ⊢ False.
  Proof.
    iIntros "H".
    iInduction t as [t1 IH1 t2 IH2 | t1 IH1 t2 IH2 | | | ] ""
      forall (c); simpl.
    - iDestruct "H" as (? ? ? ? [Heq _]) "_". discriminate.
    - iDestruct "H" as "[H|H]".
      + iDestruct "H" as (v) "[%Heq H]". injection Heq as <-.
        by iApply (sub_susp_count_ne_injr_loc with "H").
      + iDestruct "H" as (v) "[%Heq _]". discriminate.
    - iDestruct "H" as "[Hv _]". iDestruct "Hv" as (?) "%Heq". discriminate.
    - iDestruct "H" as "[Hv _]". iDestruct "Hv" as (?) "%Heq". discriminate.
    - iDestruct "H" as (v1) "[%Heq _]". discriminate.
  Qed.

  Lemma sub_susp_count_ne_injL_susp t (susp : loc) c pid Nc v_outer :
    sub_susp_count t (InjLV #susp) c pid Nc v_outer ⊢ False.
  Proof.
    iIntros "H".
    iInduction t as [t1 IH1 t2 IH2 | t1 IH1 t2 IH2 | | | ] ""
      forall (c); simpl.
    - iDestruct "H" as (? ? ? ? [Heq _]) "_". discriminate.
    - iDestruct "H" as "[H|H]".
      + iDestruct "H" as (v) "[%Heq H]". injection Heq as <-.
        by iApply (sub_susp_count_ne_loc with "H").
      + iDestruct "H" as (v) "[%Heq _]". discriminate.
    - iDestruct "H" as "[Hv _]". iDestruct "Hv" as (?) "%Heq". discriminate.
    - iDestruct "H" as "[Hv _]". iDestruct "Hv" as (?) "%Heq". discriminate.
    - iDestruct "H" as (v1) "[%Heq _]". discriminate.
  Qed.

  Lemma sub_susp_count_frags_N_agree t v c id Nc Nc' :
    sub_susp_count_frags t v c id Nc -∗ cap_frag id Nc' -∗ ⌜Nc = Nc'⌝.
  Proof.
    iIntros "(Hcap & _) Hcap'".
    iApply (cap_frag_agree with "Hcap Hcap'").
  Qed.

  Lemma sub_susp_count_eats_susp (id : nat) t (c pid Nc : nat) γ
      (susp : loc) (p : proph_id) (v_outer : val) m d ps pn ctr gm pvm :
    d !! γ = None →
    id > pid →
    visited_mapg_auth m d ps pn ctr gm pvm -∗
    id_token id -∗
    intransit 1 -∗
    lg_mapg_frag susp γ -∗
    susp ↦ᵥ{#3/4} InjLV (#pid, #p) -∗
    sub_susp_count t (InjRV (InjRV #susp)) c pid Nc v_outer
    ==∗
      visited_map_update_done m d ps pn γ id ctr gm pvm ∗
      visit_reached_done γ ∗
      intransit 1 ∗
      sub_susp_count t (InjRV (InjRV #susp)) c pid Nc v_outer ∗
      susp ↦ᵥ{#3/4} InjLV (#pid, #p).
  Proof.
    iIntros (Hfresh Hid) "Hauth Htok Hintr #Hlg Hsusp Hcount".
    destruct t; simpl.
    - iDestruct "Hcount" as (? ? ? ? [Heq _]) "_". discriminate.
    - iDestruct "Hcount" as "[H|H]".
      + iDestruct "H" as (?) "[%Heq _]". discriminate.
      + iDestruct "H" as (v) "[%Heq H]". injection Heq as <-.
        by iDestruct (sub_susp_count_ne_injr_loc with "H") as %[].
    - iDestruct "Hcount" as "[Hv _]". iDestruct "Hv" as (?) "%Heq". discriminate.
    - iDestruct "Hcount" as "[Hv _]". iDestruct "Hv" as (?) "%Heq". discriminate.
    - (* tauth — substantive *)
      iDestruct "Hcount" as (v1) "[%Heq Hcases]".
      injection Heq as <-.
      iDestruct "Hcases" as "[H|H]".
      + iDestruct "H" as (h) "%Heq'". destruct Heq' as [Heq' _]. discriminate.
      + iDestruct "H" as (susp') "[%Heq' Hinner]".
        injection Heq' as Heq'. subst susp'.
        iDestruct "Hinner" as "[Hfilled|Hsusp_inner]".
        * iDestruct "Hfilled" as (h) "[Hsusp_f _]".
          iDestruct (pointstoS_agree with "Hsusp Hsusp_f") as %[_ Heq''].
          discriminate.
        * iDestruct "Hsusp_inner" as (p' γ')
            "(#Hlg' & Hsusp_s & %Hc & Hfrag & #Hcap' & Hdisj)".
          iDestruct (lg_mapg_agree with "Hlg Hlg'") as "(<- & _ & _)".
          iDestruct (pointstoS_agree with "Hsusp Hsusp_s") as %[_ Heqvals].
          assert (p = p') as <- by congruence.
          iDestruct "Hdisj" as "[Hpen|[Hdone|Hfin]]".
          -- iMod (visited_transition_done m d ps pn ctr gm pvm γ id with "Hauth Hpen Htok")
               as "(Hauth' & Hdone)".
             iDestruct (visit_done_keep with "Hdone") as "[Hdone #Hreached]".
             iModIntro.
             iSplitL "Hauth'"; [iExact "Hauth'"|].
             iSplit; [iExact "Hreached"|].
             iFrame "Hintr".
             iSplitR "Hsusp"; [|iExact "Hsusp"].
             simpl.
             iExists (InjRV #susp). iSplit; [done|].
             iRight. iExists susp. iSplit; [done|].
             iRight. iExists p, γ.
             iFrame "Hlg' Hsusp_s Hfrag Hcap'". iSplit; [done|].
             iRight. iLeft. iExists id. iSplit; [iPureIntro; done|].
             iExact "Hdone".
          -- (* Hdone: γ already done at some id_other. The d !! γ = None
                premise rules this out (visit_done implies γ ∈ d). *)
             iDestruct "Hdone" as (id_other Hgt) "Hdone".
             iDestruct "Hdone" as "[_ #Hrd]".
             iDestruct "Hauth" as "(Hms & Hd & Hrest)".
             iDestruct (own_valid_2 with "Hd Hrd") as %Hvd.
             apply auth_both_valid_discrete in Hvd as [Hincl _].
             apply singleton_included_l in Hincl as (xd & Hxd & _).
             exfalso. rewrite Hfresh in Hxd. inversion Hxd.
          -- (* Hfin: γ is finished, with intransit (1/2). Combined with input
                intransit 1, total > 1 → invalid. *)
             iDestruct "Hfin" as "[_ Hintr_half]".
             by iDestruct (intransit_excl_full with "Hintr Hintr_half") as %[].
  Qed.

  Lemma visited_update_done (id : nat) :
    ∀ t t' v (c pid Nc : nat) (susp : loc) (p : proph_id) γ m d ps pn ctr gm pvm,
      d !! γ = None →
      id > pid →
      v_sub_obj t' v #susp →
      visited_mapg_auth m d ps pn ctr gm pvm -∗
      id_token id -∗
      intransit 1 -∗
      lg_mapg_frag susp γ -∗
      susp ↦ᵥ{#3/4} InjLV (#pid, #p) -∗
      sub_susp_count_frags t v c pid Nc
      ==∗
        intransit 1 ∗
        visit_reached_done γ ∗
        visited_map_update_done m d ps pn γ id ctr gm pvm ∗
        sub_susp_count_frags t v c pid Nc ∗
        susp ↦ᵥ{#3/4} InjLV (#pid, #p).
  Proof.
    iIntros (t t' v c pid Nc susp p γ m d ps pn ctr gm pvm Hfresh Hid Hsub)
      "Hauth Htok Hintr #Hlg Hsusp (#Hcap & %Hle & Hinner & Hagg)".
    iAssert (∀ v_outer (tind : evi_type) (vind : val) (cind : nat) (tind' : evi_type),
               ⌜v_sub_obj tind' vind #susp⌝ -∗
               visited_mapg_auth m d ps pn ctr gm pvm -∗
               id_token id -∗
               intransit 1 -∗
               lg_mapg_frag susp γ -∗
               susp ↦ᵥ{#3/4} InjLV (#pid, #p) -∗
               sub_susp_count tind vind cind pid Nc v_outer ==∗
               visit_reached_done γ ∗
               intransit 1 ∗
               visited_map_update_done m d ps pn γ id ctr gm pvm ∗
               sub_susp_count tind vind cind pid Nc v_outer ∗
               susp ↦ᵥ{#3/4} InjLV (#pid, #p))%I
      with "[]" as "Hlem".
    { iClear "Hcap Hlg".
      iIntros (v_outer t0).
      iInduction t0 as [t1 t2 | t1 t2 | | | ] "IH".
      all: iIntros (vind cind tind') "%Hsubind Hauth Htok Hintr #Hlg Hsusp Hinner".
      - (* tprod *)
        simpl. iDestruct "Hinner" as (c1 c2 v1 v2 [-> <-]) "[Hc1 Hc2]".
        destruct tind' as [t1' t2' | | | | ]; simpl in Hsubind; try done.
        + destruct Hsubind as (v1' & v2' & Heq & Hdisj). injection Heq as <- <-.
          destruct Hdisj as [<- | [<- | [Hsub1 | Hsub2]]].
          * by iDestruct (sub_susp_count_ne_loc with "Hc1") as %[].
          * by iDestruct (sub_susp_count_ne_loc with "Hc2") as %[].
          * iMod ("IH" $! v1 c1 t1' Hsub1 with "Hauth Htok Hintr Hlg Hsusp Hc1")
              as "(#Hreached & Hintr & Hauth' & Hc1' & Hsusp')".
            iModIntro. iFrame "Hreached Hintr Hauth' Hsusp'".
            iExists c1, c2, v1, v2. by iFrame.
          * iMod ("IH1" $! v2 c2 t2' Hsub2 with "Hauth Htok Hintr Hlg Hsusp Hc2")
              as "(#Hreached & Hintr & Hauth' & Hc2' & Hsusp')".
            iModIntro. iFrame "Hreached Hintr Hauth' Hsusp'".
            iExists c1, c2, v1, v2. by iFrame.
        + destruct Hsubind as (? & [(Heq & _ & _) | (Heq & _ & _)]); discriminate.
        + destruct Hsubind as (? & [Heq|Heq] & _); discriminate.
      - (* tsum *)
        simpl. iDestruct "Hinner" as "[Hl|Hr]".
        + iDestruct "Hl" as (v1') "[-> Hc]".
          destruct tind' as [t1' t2' | t1' t2' | | | ]; simpl in Hsubind; try done.
          * destruct Hsubind as (? & ? & Heq & _); discriminate.
          * destruct Hsubind as (v'' & [(Heq1 & _ & Heq3) | (Heq1 & _ & _)]).
            -- subst v''. injection Heq1 as Heq. by apply no_fix_InjLV in Heq.
            -- discriminate.
          * destruct Hsubind as (? & [Heq|Heq] & _); discriminate.
        + iDestruct "Hr" as (v2') "[-> Hc]".
          destruct tind' as [t1' t2' | t1' t2' | | | ]; simpl in Hsubind; try done.
          * destruct Hsubind as (? & ? & Heq & _); discriminate.
          * destruct Hsubind as (v'' & [(Heq1 & _ & _) | (Heq1 & _ & Heq3)]).
            -- discriminate.
            -- subst v''. injection Heq1 as Heq. by apply no_fix_InjRV in Heq.
          * destruct Hsubind as (v'' & [Heq|Heq] & Heqsv).
            -- subst v''. injection Heq as ->.
               by iDestruct (sub_susp_count_ne_injL_susp with "Hc") as %[].
            -- subst v''. injection Heq as ->.
               by iDestruct (sub_susp_count_ne_injr_loc with "Hc") as %[].
      - (* tstring *)
        simpl. iDestruct "Hinner" as "[Hv %Hc]". iDestruct "Hv" as (s) "->".
        destruct tind'; simpl in Hsubind; try done.
        + destruct Hsubind as (? & ? & Heq & _); discriminate.
        + destruct Hsubind as (v'' & [(Heq & _) | (Heq & _)]); discriminate.
        + destruct Hsubind as (? & [Heq|Heq] & _); discriminate.
      - (* tint *)
        simpl. iDestruct "Hinner" as "[Hv %Hc]". iDestruct "Hv" as (z) "->".
        destruct tind'; simpl in Hsubind; try done.
        + destruct Hsubind as (? & ? & Heq & _); discriminate.
        + destruct Hsubind as (v'' & [(Heq & _) | (Heq & _)]); discriminate.
        + destruct Hsubind as (? & [Heq|Heq] & _); discriminate.
      - (* tauth *)
        destruct tind'; simpl in Hsubind; try done.
        + iDestruct "Hinner" as (v1) "[-> _]".
          destruct Hsubind as (? & ? & Heq & _); discriminate.
        + iDestruct "Hinner" as (v1) "[-> _]".
          destruct Hsubind as (? & [(Heq & _ & _) | (Heq & _ & Heq2)]).
          * discriminate.
          * subst. injection Heq as Heq. by apply no_fix_InjRV in Heq.
        + destruct Hsubind as (? & [Heq|Heq] & ->).
          * iDestruct "Hinner" as (v1) "[-> Hcases]".
            injection Heq as ->.
            iDestruct "Hcases" as "[H|H]".
            -- iDestruct "H" as (h) "%Heq'". destruct Heq' as [Heq' _]. discriminate.
            -- iDestruct "H" as (susp') "[%Heq' _]". discriminate.
          * subst vind.
            iMod (sub_susp_count_eats_susp id _ cind pid Nc γ susp p v_outer m d ps pn ctr gm
              with "Hauth Htok Hintr Hlg Hsusp Hinner")
              as "(Hauth' & #Hreached & Hintr & Hinner' & Hsusp')"; [done|done|].
            iModIntro. by iFrame. }
    iMod ("Hlem" $! v t v c t' Hsub with "Hauth Htok Hintr Hlg Hsusp Hinner")
      as "(#Hreached & Hintr & Hauth' & Hinner & Hsusp)".
    iModIntro. iFrame "Hreached Hintr Hauth' Hsusp Hcap Hinner Hagg". done.
  Qed.

  (* Substantive tauth B2 update: reached via tsum's right branch when the
     external [susp] matches a B2 leaf. Consumes [c = 1] for the leaf,
     transitions [visit_done] -> [visit_finished] using the visited map auth,
     releases the [1/Nc] fragment, steps the verifier store. *)
  Lemma count_update_eats_susp K tᵥ v' t (susp : loc) (c pid Nc : nat) (h : string) (v_outer : val) γ :
    lg_mapg_frag susp γ -∗
    visit_finished γ -∗
    sub_susp_count t (InjRV (InjRV #susp)) c pid Nc v_outer -∗
    susp ↦ᵥ{#(3/4)} InjLV (#pid, v') -∗
    unfilled susp -∗
    spec_verifier tᵥ (fill K (#susp <- InjRV #h))
    ={⊤}=∗
      ⌜c = 1⌝ ∗
      intransit (1/2) ∗
      sub_susp_count t (InjRV (InjRV #susp)) (c-1) pid Nc v_outer ∗
      susp ↦ᵥ{#(3/4)} InjRV #h ∗
      spec_verifier tᵥ (fill K (#())) ∗
      mapg_frag pid (1 / (2 * pos_to_Qp (Pos.of_nat Nc)))%Qp v_outer ∗
      filled susp.
  Proof.
    iIntros "#Hlg #Hreached Hinner Hsusp Hunfill Hspec".
    destruct t; simpl.
    - iDestruct "Hinner" as (? ? ? ? [Heq _]) "_". discriminate.
    - iDestruct "Hinner" as "[H|H]".
      + iDestruct "H" as (?) "[%Heq _]". discriminate.
      + iDestruct "H" as (v) "[%Heq H]". injection Heq as <-.
        by iDestruct (sub_susp_count_ne_injr_loc with "H") as %[].
    - iDestruct "Hinner" as "[Hv _]". iDestruct "Hv" as (?) "%Heq". discriminate.
    - iDestruct "Hinner" as "[Hv _]". iDestruct "Hv" as (?) "%Heq". discriminate.
    - (* tauth — substantive *)
      iDestruct "Hinner" as (v1) "[%Heq Hcases]".
      injection Heq as <-.
      iDestruct "Hcases" as "[H|H]".
      + iDestruct "H" as (h') "%Heq'". destruct Heq' as [Heq' _]. discriminate.
      + iDestruct "H" as (susp') "[%Heq' Hinner]".
        injection Heq' as Heq'. subst susp'.
        iDestruct "Hinner" as "[Hfilled|Hsusp_inner]".
        * iDestruct "Hfilled" as (h') "[Hsusp_f _]".
          iDestruct (pointstoS_agree with "Hsusp Hsusp_f") as %[_ Heq''].
          discriminate.
        * iDestruct "Hsusp_inner" as (p' γ') "(#Hlg' & Hsusp_s & %Hc & Hfrag & #Hcap' & Hdisj)".
          iDestruct (lg_mapg_agree with "Hlg Hlg'") as "(<- & _ & _)".
          iDestruct (pointstoS_agree with "Hsusp Hsusp_s") as %[_ Heqvals].
          injection Heqvals as Heqv'. subst v'.
          iDestruct "Hdisj" as "[Hpen|[Hdone|Hfin]]".
          { (* Hpen: pending γ + visit_finished γ → False *)
            by iDestruct (visited_invalid_2 with "[$Hpen $Hreached]") as %[]. }
          { (* Hdone: visit_done γ id + visit_finished γ → False *)
            iDestruct "Hdone" as (id Hidpid) "Hdone".
            by iDestruct (visited_invalid_3 with "[$Hdone $Hreached]") as %[]. }
          (* Hfin: γ is finished. Extract intransit (1/2) and proceed with store. *)
          iDestruct "Hfin" as "[_ Hintr_half]".
          iCombine "Hsusp Hsusp_s" as "Hsusp_full".
          rewrite Qp.three_quarter_quarter.
          iMod (step_verifier_store with "[$Hsusp_full $Hspec]") as "(Hspec & Hsusp_full)"; [done|].
          iEval (rewrite -Qp.three_quarter_quarter) in "Hsusp_full".
          iDestruct "Hsusp_full" as "[Hsusp Hsusp_s]".
          iMod (unfilled_to_filled with "Hunfill") as "#Hfilled".
          iModIntro.
          iSplitR; [done|].
          iFrame "Hintr_half".
          iSplitR "Hsusp Hspec Hfrag".
          { iExists (InjRV #susp). iSplit; [done|].
            iRight. iExists susp. iSplit; [done|].
            iLeft. iExists h. iFrame "Hsusp_s". subst c. done. }
          iFrame "Hsusp Hspec Hfrag Hfilled".
  Qed.

  Lemma count_update :
    ∀ K tᵥ v v' (t t' : evi_type) (susp : loc) (c pid Nc : nat) (h : string) γ,
      ⌜v_sub_obj t' v #susp⌝ -∗
      lg_mapg_frag susp γ -∗
      mapg_frag pid (1 / (2 * pos_to_Qp (Pos.of_nat Nc)))%Qp v -∗
      visit_finished γ -∗
      sub_susp_count_frags t v c pid Nc -∗
      susp ↦ᵥ{#(3/4)} InjLV (#pid, v') -∗
      unfilled susp -∗
      spec_verifier tᵥ (fill K (#susp <- InjRV #h))
      ={⊤}=∗
        intransit (1/2) ∗
        sub_susp_count_frags t v (c-1) pid Nc ∗
        susp ↦ᵥ{#(3/4)} InjRV #h ∗
        spec_verifier tᵥ (fill K (#())) ∗
        filled susp.
  Proof.
    iIntros (K tᵥ v v' t t' susp c pid Nc h γ)
      "%Hsub #Hlg Hmapg #Hreached (#Hcap & %Hle & Hinner & Hagg) Hsusp Hunfill Hspec".
    iAssert (∀ v_outer (t : evi_type) (v : val) (c : nat) (t' : evi_type),
               ⌜v_sub_obj t' v #susp⌝ -∗
               sub_susp_count t v c pid Nc v_outer -∗
               susp ↦ᵥ{#3/4} InjLV (#pid, v') -∗
               unfilled susp -∗
               spec_verifier tᵥ (fill K (#susp <- InjRV #h)) ={⊤}=∗
               ⌜1 ≤ c⌝ ∗
               intransit (1/2) ∗
               sub_susp_count t v (c - 1) pid Nc v_outer ∗
               susp ↦ᵥ{#3/4} InjRV #h ∗
               spec_verifier tᵥ (fill K #()) ∗
               mapg_frag pid (1 / (2 * pos_to_Qp (Pos.of_nat Nc)))%Qp v_outer ∗
               filled susp)%I
      with "[]" as "Hlem".
    { iClear "Hcap".
      iIntros (v_outer tind).
      iInduction tind as [t1 t2 | t1 t2 | | | ] "IH".
      all: iIntros (vind cind tind') "%Hsubind Hinner' Hsusp' Hunfill' Hspec'".
      - (* tind = tprod *)
        simpl. iDestruct "Hinner'" as (c1 c2 v1 v2 [-> <-]) "[Hc1 Hc2]".
        destruct tind' as [t1' t2' | | | | ]; simpl in Hsubind; try done.
        + destruct Hsubind as (v1' & v2' & Heq & Hdisj). injection Heq as <- <-.
          destruct Hdisj as [<- | [<- | [Hsub1 | Hsub2]]].
          * by iDestruct (sub_susp_count_ne_loc with "Hc1") as %[].
          * by iDestruct (sub_susp_count_ne_loc with "Hc2") as %[].
          * iMod ("IH" $! v1 c1 t1' Hsub1 with "Hc1 Hsusp' Hunfill' Hspec'")
              as "(%Hc & Hintr & Hc1' & Hsusp'' & Hspec'' & Hnew & #Hfilled)".
            iModIntro. iSplit; [iPureIntro; lia|].
            iFrame "Hintr Hsusp'' Hspec'' Hnew Hfilled".
            iExists (c1 - 1), c2, v1, v2.
            iSplit; [iPureIntro; split; [done|lia]|]. iFrame.
          * iMod ("IH1" $! v2 c2 t2' Hsub2 with "Hc2 Hsusp' Hunfill' Hspec'")
              as "(%Hc & Hintr & Hc2' & Hsusp'' & Hspec'' & Hnew & #Hfilled)".
            iModIntro. iSplit; [iPureIntro; lia|].
            iFrame "Hintr Hsusp'' Hspec'' Hnew Hfilled".
            iExists c1, (c2 - 1), v1, v2.
            iSplit; [iPureIntro; split; [done|lia]|]. iFrame.
        + destruct Hsubind as (v'' & [(Heq & _ & _) | (Heq & _ & _)]); discriminate.
        + destruct Hsubind as (v'' & [Heq|Heq] & _); discriminate.
      - (* tind = tsum *)
        simpl. iDestruct "Hinner'" as "[Hl|Hr]".
        + iDestruct "Hl" as (v1) "[-> Hc]".
          destruct tind'; simpl in Hsubind; try done.
          * destruct Hsubind as (? & ? & Heq & _); discriminate.
          * destruct Hsubind as (v'' & [(Heq1 & _ & Heq2) | (Heq1 & _ & _)]).
            -- subst v''. injection Heq1 as Heq. by apply no_fix_InjLV in Heq.
            -- discriminate.
          * destruct Hsubind as (v'' & [Heq|Heq] & _); discriminate.
        + iDestruct "Hr" as (v2) "[-> Hc]".
          destruct tind'; simpl in Hsubind; try done.
          * destruct Hsubind as (? & ? & Heq & _); discriminate.
          * destruct Hsubind as (v'' & [(Heq1 & _ & _) | (Heq1 & _ & Heq2)]).
            -- discriminate.
            -- subst v''. injection Heq1 as Heq. by apply no_fix_InjRV in Heq.
          * destruct Hsubind as (v'' & [Heq|Heq] & Heqsv).
            -- subst v''. injection Heq as ->.
               by iDestruct (sub_susp_count_ne_injL_susp with "Hc") as %[].
            -- subst v''. injection Heq as ->.
               by iDestruct (sub_susp_count_ne_injr_loc with "Hc") as %[].
      - (* tind = tstring *)
        simpl. iDestruct "Hinner'" as "[Hv %Hc]". iDestruct "Hv" as (s) "->".
        destruct tind'; simpl in Hsubind; try done.
        + destruct Hsubind as (? & ? & Heq & _); discriminate.
        + destruct Hsubind as (v'' & [(Heq & _) | (Heq & _)]); discriminate.
        + destruct Hsubind as (v'' & [Heq|Heq] & _); discriminate.
      - (* tind = tint *)
        simpl. iDestruct "Hinner'" as "[Hv %Hc]". iDestruct "Hv" as (z) "->".
        destruct tind'; simpl in Hsubind; try done.
        + destruct Hsubind as (? & ? & Heq & _); discriminate.
        + destruct Hsubind as (v'' & [(Heq & _) | (Heq & _)]); discriminate.
        + destruct Hsubind as (v'' & [Heq|Heq] & _); discriminate.
      - (* tind = tauth *)
        destruct tind'; simpl in Hsubind; try done.
        + iDestruct "Hinner'" as (v1) "[-> _]".
          destruct Hsubind as (? & ? & Heq & _); discriminate.
        + iDestruct "Hinner'" as (v1) "[-> _]".
          destruct Hsubind as (v'' & [(Heq & _ & _) | (Heq & _ & Heq2)]).
          * discriminate.
          * subst v''. injection Heq as Heq. by apply no_fix_InjRV in Heq.
        + destruct Hsubind as (v'' & [Heq|Heq] & ->).
          * iDestruct "Hinner'" as (v1) "[-> Hcases]".
            injection Heq as ->.
            iDestruct "Hcases" as "[H|H]".
            -- iDestruct "H" as (h') "%Heq'". destruct Heq' as [Heq' _]. discriminate.
            -- iDestruct "H" as (susp') "[%Heq' _]". discriminate.
          * subst vind.
            iMod (count_update_eats_susp with "Hlg Hreached Hinner' Hsusp' Hunfill' Hspec'") as
              "(%Hc & Hintr & Hc' & Hsusp'' & Hspec'' & Hnew & #Hfilled)".
            iModIntro. iSplit; [iPureIntro; lia|]. iFrame "Hintr". iFrame "Hfilled". iFrame. }
    iMod ("Hlem" $! v t v c t' Hsub with "Hinner Hsusp Hunfill Hspec")
      as "(%Hc & Hintr & Hinner & Hsusp & Hspec & Hnew & #Hfilled)".
    iDestruct (mapg_frag_combine with "Hmapg Hnew") as "Hnew".
    rewrite Qp.div_2_mul.
    iModIntro. iFrame "Hintr Hsusp Hspec Hcap Hfilled".
    iSplit; [iPureIntro; lia|]. iFrame "Hinner".
    iDestruct "Hagg" as "[%HcN | [%HcN Hq]]".
    - iRight. iSplit; [iPureIntro; lia|].
      iExists (1 / pos_to_Qp (Pos.of_nat Nc))%Qp. iFrame "Hnew". iPureIntro.
      rewrite Qp.mul_div_l.
      assert (Nc - (c - 1) = 1)%nat as -> by lia. done.
    - iDestruct "Hq" as (q Heqq) "Hq".
      iRight. iSplit; [iPureIntro; lia|].
      iExists (q + 1 / pos_to_Qp (Pos.of_nat Nc))%Qp.
      iSplit.
      + iPureIntro.
        rewrite Qp.mul_add_distr_r. rewrite Heqq.
        rewrite Qp.mul_div_l.
        assert (Nc - (c - 1) = (Nc - c) + 1)%nat as -> by lia.
        assert (Nc - c ≠ 0)%nat as HNc by lia.
        rewrite Nat2Pos.inj_add; [|lia|lia].
        rewrite pos_to_Qp_add. done.
      + iApply (mapg_frag_combine with "Hq Hnew").
  Qed.

  (* Tauth-leaf helper: transitions the γ-state inside a [sub_susp_count]
     tauth-leaf from [visit_done γ id] to [visit_finished γ]. Mirrors
     [sub_susp_count_eats_susp] but for the done → finished step.
     - [Hpen] is ruled out via [visited_reached_done_invalid] + [visit_reached_done γ].
     - [Hdone] performs the transition via [visited_transition_finished];
       splits [intransit 1] into two halves — one stays inside the leaf's
       new third-disjunct, the other is returned to the caller.
     - [Hfin] is ruled out via [intransit_excl_full] (input [intransit 1]
       conflicts with the disjunct's [intransit (1/2)]). *)
  Lemma sub_susp_count_finishes_susp t (c pid Nc : nat) γ
      (susp : loc) (p : proph_id) (v_outer : val) m d ps pn ctr gm pvm :
    visited_mapg_auth m d ps pn ctr gm pvm -∗
    visit_reached_done γ -∗
    intransit 1 -∗
    lg_mapg_frag susp γ -∗
    susp ↦ᵥ{#3/4} InjLV (#pid, #p) -∗
    sub_susp_count t (InjRV (InjRV #susp)) c pid Nc v_outer
    ==∗
      visited_map_update_finished m d ps pn γ ctr gm pvm ∗
      visit_finished γ ∗
      intransit (1/2) ∗
      sub_susp_count t (InjRV (InjRV #susp)) c pid Nc v_outer ∗
      susp ↦ᵥ{#3/4} InjLV (#pid, #p).
  Proof.
    iIntros "Hauth #Hreached Hintr #Hlg Hsusp Hcount".
    destruct t; simpl.
    - iDestruct "Hcount" as (? ? ? ? [Heq _]) "_". discriminate.
    - iDestruct "Hcount" as "[H|H]".
      + iDestruct "H" as (?) "[%Heq _]". discriminate.
      + iDestruct "H" as (v) "[%Heq H]". injection Heq as <-.
        by iDestruct (sub_susp_count_ne_injr_loc with "H") as %[].
    - iDestruct "Hcount" as "[Hv _]". iDestruct "Hv" as (?) "%Heq". discriminate.
    - iDestruct "Hcount" as "[Hv _]". iDestruct "Hv" as (?) "%Heq". discriminate.
    - (* tauth — substantive *)
      iDestruct "Hcount" as (v1) "[%Heq Hcases]".
      injection Heq as <-.
      iDestruct "Hcases" as "[H|H]".
      + iDestruct "H" as (h) "%Heq'". destruct Heq' as [Heq' _]. discriminate.
      + iDestruct "H" as (susp') "[%Heq' Hinner]".
        injection Heq' as Heq'. subst susp'.
        iDestruct "Hinner" as "[Hfilled|Hsusp_inner]".
        * iDestruct "Hfilled" as (h) "[Hsusp_f _]".
          iDestruct (pointstoS_agree with "Hsusp Hsusp_f") as %[_ Heq''].
          discriminate.
        * iDestruct "Hsusp_inner" as (p' γ')
            "(#Hlg' & Hsusp_s & %Hc & Hfrag & #Hcap' & Hdisj)".
          iDestruct (lg_mapg_agree with "Hlg Hlg'") as "(<- & _ & _)".
          iDestruct (pointstoS_agree with "Hsusp Hsusp_s") as %[_ Heqvals].
          assert (p = p') as <- by congruence.
          iDestruct "Hdisj" as "[Hpen|[Hdone|Hfin]]".
          -- (* Hpen: visit_pending γ + visit_reached_done γ + auth → False *)
             by iDestruct (visited_reached_done_invalid with "Hauth Hreached Hpen") as %[].
          -- (* Hdone: transition γ to finished via the auth update. Split
                intransit 1 into two halves. *)
             iDestruct "Hdone" as (id Hidpid) "Hdone".
             iMod (visited_transition_finished with "Hauth Hdone")
               as "(Hauth' & #Hfin)".
             iEval (rewrite -{1}(Qp.div_2 1) intransit_split) in "Hintr".
             iDestruct "Hintr" as "[Hintr1 Hintr2]".
             iModIntro.
             iSplitL "Hauth'"; [iExact "Hauth'"|].
             iSplit; [iExact "Hfin"|].
             iFrame "Hintr1".
             iSplitR "Hsusp"; [|iExact "Hsusp"].
             simpl.
             iExists (InjRV #susp). iSplit; [done|].
             iRight. iExists susp. iSplit; [done|].
             iRight. iExists p, γ.
             iFrame "Hlg' Hsusp_s Hfrag Hcap'". iSplit; [done|].
             iRight. iRight. iFrame "Hfin Hintr2".
          -- (* Hfin: γ already finished — intransit conflict. *)
             iDestruct "Hfin" as "[_ Hintr_half]".
             by iDestruct (intransit_excl_full with "Hintr Hintr_half") as %[].
  Qed.

  (* Outer counterpart to [visited_update_done]: walks a [sub_susp_count_frags]
     to find the tauth-leaf labelled [susp] and transitions its γ from
     visit_done → visit_finished using [sub_susp_count_finishes_susp]. *)
  Lemma visit_update_finished :
    ∀ t t' v (c pid Nc : nat) (susp : loc) (p : proph_id) γ vm d ps pn ctr gm pvm,
      v_sub_obj t' v #susp →
      visited_mapg_auth vm d ps pn ctr gm pvm -∗
      visit_reached_done γ -∗
      intransit 1 -∗
      lg_mapg_frag susp γ -∗
      susp ↦ᵥ{#3/4} InjLV (#pid, #p) -∗
      sub_susp_count_frags t v c pid Nc
      ==∗
        visit_finished γ ∗
        intransit (1/2) ∗
        visited_map_update_finished vm d ps pn γ ctr gm pvm ∗
        sub_susp_count_frags t v c pid Nc ∗
        susp ↦ᵥ{#3/4} InjLV (#pid, #p).
  Proof.
    iIntros (t t' v c pid Nc susp p γ m d ps pn ctr gm pvm Hsub)
      "Hauth #Hreached Hintr #Hlg Hsusp (#Hcap & %Hle & Hinner & Hagg)".
    iAssert (∀ v_outer (tind : evi_type) (vind : val) (cind : nat) (tind' : evi_type),
               ⌜v_sub_obj tind' vind #susp⌝ -∗
               visited_mapg_auth m d ps pn ctr gm pvm -∗
               intransit 1 -∗
               lg_mapg_frag susp γ -∗
               susp ↦ᵥ{#3/4} InjLV (#pid, #p) -∗
               sub_susp_count tind vind cind pid Nc v_outer ==∗
               visit_finished γ ∗
               intransit (1/2) ∗
               visited_map_update_finished m d ps pn γ ctr gm pvm ∗
               sub_susp_count tind vind cind pid Nc v_outer ∗
               susp ↦ᵥ{#3/4} InjLV (#pid, #p))%I
      with "[]" as "Hlem".
    { iClear "Hcap Hlg".
      iIntros (v_outer t0).
      iInduction t0 as [t1 t2 | t1 t2 | | | ] "IH".
      all: iIntros (vind cind tind') "%Hsubind Hauth Hintr #Hlg Hsusp Hinner".
      - (* tprod *)
        simpl. iDestruct "Hinner" as (c1 c2 v1 v2 [-> <-]) "[Hc1 Hc2]".
        destruct tind' as [t1' t2' | | | | ]; simpl in Hsubind; try done.
        + destruct Hsubind as (v1' & v2' & Heq & Hdisj). injection Heq as <- <-.
          destruct Hdisj as [<- | [<- | [Hsub1 | Hsub2]]].
          * by iDestruct (sub_susp_count_ne_loc with "Hc1") as %[].
          * by iDestruct (sub_susp_count_ne_loc with "Hc2") as %[].
          * iMod ("IH" $! v1 c1 t1' Hsub1 with "Hauth Hintr Hlg Hsusp Hc1")
              as "(#Hfin & Hintr & Hauth' & Hc1' & Hsusp')".
            iModIntro. iFrame "Hfin Hintr Hauth' Hsusp'".
            iExists c1, c2, v1, v2. by iFrame.
          * iMod ("IH1" $! v2 c2 t2' Hsub2 with "Hauth Hintr Hlg Hsusp Hc2")
              as "(#Hfin & Hintr & Hauth' & Hc2' & Hsusp')".
            iModIntro. iFrame "Hfin Hintr Hauth' Hsusp'".
            iExists c1, c2, v1, v2. by iFrame.
        + destruct Hsubind as (? & [(Heq & _ & _) | (Heq & _ & _)]); discriminate.
        + destruct Hsubind as (? & [Heq|Heq] & _); discriminate.
      - (* tsum *)
        simpl. iDestruct "Hinner" as "[Hl|Hr]".
        + iDestruct "Hl" as (v1') "[-> Hc]".
          destruct tind' as [t1' t2' | t1' t2' | | | ]; simpl in Hsubind; try done.
          * destruct Hsubind as (? & ? & Heq & _); discriminate.
          * destruct Hsubind as (v'' & [(Heq1 & _ & Heq3) | (Heq1 & _ & _)]).
            -- subst v''. injection Heq1 as Heq. by apply no_fix_InjLV in Heq.
            -- discriminate.
          * destruct Hsubind as (? & [Heq|Heq] & _); discriminate.
        + iDestruct "Hr" as (v2') "[-> Hc]".
          destruct tind' as [t1' t2' | t1' t2' | | | ]; simpl in Hsubind; try done.
          * destruct Hsubind as (? & ? & Heq & _); discriminate.
          * destruct Hsubind as (v'' & [(Heq1 & _ & _) | (Heq1 & _ & Heq3)]).
            -- discriminate.
            -- subst v''. injection Heq1 as Heq. by apply no_fix_InjRV in Heq.
          * destruct Hsubind as (v'' & [Heq|Heq] & Heqsv).
            -- subst v''. injection Heq as ->.
               by iDestruct (sub_susp_count_ne_injL_susp with "Hc") as %[].
            -- subst v''. injection Heq as ->.
               by iDestruct (sub_susp_count_ne_injr_loc with "Hc") as %[].
      - (* tstring *)
        simpl. iDestruct "Hinner" as "[Hv %Hc]". iDestruct "Hv" as (s) "->".
        destruct tind'; simpl in Hsubind; try done.
        + destruct Hsubind as (? & ? & Heq & _); discriminate.
        + destruct Hsubind as (v'' & [(Heq & _) | (Heq & _)]); discriminate.
        + destruct Hsubind as (? & [Heq|Heq] & _); discriminate.
      - (* tint *)
        simpl. iDestruct "Hinner" as "[Hv %Hc]". iDestruct "Hv" as (z) "->".
        destruct tind'; simpl in Hsubind; try done.
        + destruct Hsubind as (? & ? & Heq & _); discriminate.
        + destruct Hsubind as (v'' & [(Heq & _) | (Heq & _)]); discriminate.
        + destruct Hsubind as (? & [Heq|Heq] & _); discriminate.
      - (* tauth *)
        destruct tind'; simpl in Hsubind; try done.
        + iDestruct "Hinner" as (v1) "[-> _]".
          destruct Hsubind as (? & ? & Heq & _); discriminate.
        + iDestruct "Hinner" as (v1) "[-> _]".
          destruct Hsubind as (? & [(Heq & _ & _) | (Heq & _ & Heq2)]).
          * discriminate.
          * subst. injection Heq as Heq. by apply no_fix_InjRV in Heq.
        + destruct Hsubind as (? & [Heq|Heq] & ->).
          * iDestruct "Hinner" as (v1) "[-> Hcases]".
            injection Heq as ->.
            iDestruct "Hcases" as "[H|H]".
            -- iDestruct "H" as (h) "%Heq'". destruct Heq' as [Heq' _]. discriminate.
            -- iDestruct "H" as (susp') "[%Heq' _]". discriminate.
          * subst vind.
            iMod (sub_susp_count_finishes_susp _ cind pid Nc γ susp p v_outer m d ps pn ctr gm
              with "Hauth Hreached Hintr Hlg Hsusp Hinner")
              as "(Hauth' & #Hfin & Hintr & Hinner' & Hsusp')".
            iModIntro. by iFrame. }
    iMod ("Hlem" $! v t v c t' Hsub with "Hauth Hintr Hlg Hsusp Hinner")
      as "(#Hfin & Hintr & Hauth' & Hinner & Hsusp)".
    iModIntro. iFrame "Hfin Hintr Hauth' Hsusp Hcap Hinner Hagg". done.
  Qed.

  (** Cardinality bound: any γ-set ranging over labels of [a] has size at
      most [c]. The substantive cases are:
      - [tauth c=0]: [auth_susp_ser_p_fill] carries [lg_mapg_unalloc lb_a],
        which excludes any [lg_mapg_frag lb_a γ] in [γs].
      - [tauth c=1]: at most one [γ] by [lg_mapg_agree] on the unique [lb_a].
      - [tprod]: by partition into v1/v2 sub-trees, summing IH bounds. *)
  Lemma susp_ser_p_real_γl_card_le (t : evi_type) (a : val) (s : string) (c : nat) (γs : gset gname) :
    susp_ser_p_real t c a s -∗
    ([∗ set] γ ∈ γs, ∃ lb, lg_mapg_frag lb γ ∗ ⌜p_sub_obj t a #lb⌝) -∗
    ⌜size γs ≤ c⌝.
  Proof.
    iIntros "Hser HbigL".
    iInduction t as [t1 IH1 t2 IH2 | t1 IH1 t2 IH2 | | | ] ""
      forall (a s c γs).
    - (* tprod: partition γs into v1-side and v2-side, then sum the IH
         bounds. The partition is built iteratively by induction on γs;
         vacuous cases (#lb = v1 or v2) are ruled out using the structure
         of v1 and v2 forced by Hser1/Hser2. *)
      simpl. iDestruct "Hser" as (c1 c2 ->) "Hser_pair".
      iDestruct "Hser_pair" as (v1 v2 s1 s2 [-> ->]) "[#Hser1 #Hser2]".
      (* Helper: v from [susp_ser_p_real] is not a loc literal. *)
      iAssert (⌜∀ lb : loc, v1 ≠ #lb⌝)%I as %Hv1_not_loc.
      { iIntros (lb).
        destruct t1; simpl.
        - iDestruct "Hser1" as (??) "[_ Hser']".
          iDestruct "Hser'" as (????) "[%Hp _]".
          iPureIntro. intros Heq. by destruct Hp as [-> _].
        - iDestruct "Hser1" as (??) "[H|H]".
          + iDestruct "H" as "[_ %Hp]".
            iPureIntro. intros Heq. by destruct Hp as [-> _].
          + iDestruct "H" as "[_ %Hp]".
            iPureIntro. intros Heq. by destruct Hp as [-> _].
        - iDestruct "Hser1" as "[%Hp _]".
          iPureIntro. intros Heq. by destruct Hp as (? & -> & _).
        - iDestruct "Hser1" as "[%Hp _]".
          iPureIntro. intros Heq. by destruct Hp as (? & -> & _).
        - iDestruct "Hser1" as "[[Hf _]|[He _]]".
          + iDestruct "Hf" as (??????) "[%Hp _]".
            iPureIntro. intros Heq. by destruct Hp as [-> _].
          + iDestruct "He" as (??????) "[%Hp _]".
            iPureIntro. intros Heq. by destruct Hp as [-> _]. }
      iAssert (⌜∀ lb : loc, v2 ≠ #lb⌝)%I as %Hv2_not_loc.
      { iIntros (lb).
        destruct t2; simpl.
        - iDestruct "Hser2" as (??) "[_ Hser']".
          iDestruct "Hser'" as (????) "[%Hp _]".
          iPureIntro. intros Heq. by destruct Hp as [-> _].
        - iDestruct "Hser2" as (??) "[H|H]".
          + iDestruct "H" as "[_ %Hp]".
            iPureIntro. intros Heq. by destruct Hp as [-> _].
          + iDestruct "H" as "[_ %Hp]".
            iPureIntro. intros Heq. by destruct Hp as [-> _].
        - iDestruct "Hser2" as "[%Hp _]".
          iPureIntro. intros Heq. by destruct Hp as (? & -> & _).
        - iDestruct "Hser2" as "[%Hp _]".
          iPureIntro. intros Heq. by destruct Hp as (? & -> & _).
        - iDestruct "Hser2" as "[[Hf _]|[He _]]".
          + iDestruct "Hf" as (??????) "[%Hp _]".
            iPureIntro. intros Heq. by destruct Hp as [-> _].
          + iDestruct "He" as (??????) "[%Hp _]".
            iPureIntro. intros Heq. by destruct Hp as [-> _]. }
      (* Build the partition by induction on γs *)
      iAssert (∃ γs1 γs2 : gset gname,
                 ⌜γs1 ## γs2 ∧ γs = γs1 ∪ γs2⌝ ∗
                 ([∗ set] γ ∈ γs1, ∃ lb, lg_mapg_frag lb γ ∗ ⌜p_sub_obj t1 v1 #lb⌝) ∗
                 ([∗ set] γ ∈ γs2, ∃ lb, lg_mapg_frag lb γ ∗ ⌜p_sub_obj t2 v2 #lb⌝))%I
        with "[HbigL]"
        as "(%γs1 & %γs2 & [%Hdisj %Hsplit] & H1 & H2)".
      { iRevert "HbigL".
        iInduction γs as [|γ γs' Hnotin] "IHγs" using set_ind_L.
        - iIntros "_". iExists ∅, ∅. rewrite !big_sepS_empty.
          iSplit; [iPureIntro; set_solver|]. by iSplit.
        - iIntros "HbigL".
          iEval (rewrite big_sepS_insert; [|done]) in "HbigL".
          iDestruct "HbigL" as "[(%lb_γ & #Hfrag_γ & %Hsub_γ) HbigL']".
          iDestruct ("IHγs" with "HbigL'")
            as "(%γs1' & %γs2' & [%Hdisj' %Hsplit'] & H1' & H2')".
          destruct Hsub_γ as (x & y & Heq & Hdisj_p).
          injection Heq as -> ->.
          destruct Hdisj_p as [Heq | [Heq | [Hsub | Hsub]]].
          + exfalso. by apply (Hv1_not_loc lb_γ).
          + exfalso. by apply (Hv2_not_loc lb_γ).
          + iExists ({[γ]} ∪ γs1'), γs2'.
            iSplit; [iPureIntro; split; [|set_solver]|].
            { assert (γ ∉ γs1') by set_solver. set_solver. }
            iSplitL "H1'".
            * rewrite big_sepS_insert; [|set_solver].
              iSplitL ""; [iExists lb_γ; by iFrame "Hfrag_γ"|done].
            * done.
          + iExists γs1', ({[γ]} ∪ γs2').
            iSplit; [iPureIntro; split; [|set_solver]|].
            { assert (γ ∉ γs2') by set_solver. set_solver. }
            iSplitL "H1'"; [done|].
            rewrite big_sepS_insert; [|set_solver].
            iSplitL ""; [iExists lb_γ; by iFrame "Hfrag_γ"|done]. }
      iDestruct ("" $! v1 s1 c1 γs1 with "Hser1 H1") as %Hsz1.
      iDestruct ("1" $! v2 s2 c2 γs2 with "Hser2 H2") as %Hsz2.
      iPureIntro. rewrite Hsplit size_union; [|done]. lia.
    - (* tsum: p_sub_obj forces v = InjLV/InjRV #lb, so the inner
         susp_ser_p_real holds at #lb — but no [t] makes #lb a serializable
         leaf, so γs must be empty. *)
      simpl. iDestruct "Hser" as (w s') "[H | H]".
      + iDestruct "H" as "[#Hser1 %Heq]". destruct Heq as [-> ->].
        iAssert (⌜∀ lb : loc, w ≠ #lb⌝)%I as %Hw_not_loc.
        { iIntros (lb).
          destruct t1; simpl.
          - iDestruct "Hser1" as (??) "[_ Hser']".
            iDestruct "Hser'" as (????) "[%Hp _]".
            iPureIntro. intros Heq. by destruct Hp as [-> _].
          - iDestruct "Hser1" as (??) "[H|H]".
            + iDestruct "H" as "[_ %Hp]".
              iPureIntro. intros Heq. by destruct Hp as [-> _].
            + iDestruct "H" as "[_ %Hp]".
              iPureIntro. intros Heq. by destruct Hp as [-> _].
          - iDestruct "Hser1" as "[%Hp _]".
            iPureIntro. intros Heq. by destruct Hp as (? & -> & _).
          - iDestruct "Hser1" as "[%Hp _]".
            iPureIntro. intros Heq. by destruct Hp as (? & -> & _).
          - iDestruct "Hser1" as "[[Hf _]|[He _]]".
            + iDestruct "Hf" as (??????) "[%Hp _]".
              iPureIntro. intros Heq. by destruct Hp as [-> _].
            + iDestruct "He" as (??????) "[%Hp _]".
              iPureIntro. intros Heq. by destruct Hp as [-> _]. }
        iAssert (⌜γs = ∅⌝)%I as %->.
        { destruct (decide (γs = ∅)) as [-> | Hne]; [done|].
          apply set_choose_L in Hne as [γ Hin].
          iDestruct (big_sepS_elem_of with "HbigL") as (lb) "[_ %Hsub]"; [exact Hin|].
          simpl in Hsub. destruct Hsub as (v' & [(He1 & _ & He2)|(He1 & _ & _)]).
          - subst v'. injection He1 as ->.
            iPureIntro. exfalso. by apply (Hw_not_loc lb).
          - discriminate. }
        rewrite size_empty. iPureIntro. lia.
      + iDestruct "H" as "[#Hser2 %Heq]". destruct Heq as [-> ->].
        iAssert (⌜∀ lb : loc, w ≠ #lb⌝)%I as %Hw_not_loc.
        { iIntros (lb).
          destruct t2; simpl.
          - iDestruct "Hser2" as (??) "[_ Hser']".
            iDestruct "Hser'" as (????) "[%Hp _]".
            iPureIntro. intros Heq. by destruct Hp as [-> _].
          - iDestruct "Hser2" as (??) "[H|H]".
            + iDestruct "H" as "[_ %Hp]".
              iPureIntro. intros Heq. by destruct Hp as [-> _].
            + iDestruct "H" as "[_ %Hp]".
              iPureIntro. intros Heq. by destruct Hp as [-> _].
          - iDestruct "Hser2" as "[%Hp _]".
            iPureIntro. intros Heq. by destruct Hp as (? & -> & _).
          - iDestruct "Hser2" as "[%Hp _]".
            iPureIntro. intros Heq. by destruct Hp as (? & -> & _).
          - iDestruct "Hser2" as "[[Hf _]|[He _]]".
            + iDestruct "Hf" as (??????) "[%Hp _]".
              iPureIntro. intros Heq. by destruct Hp as [-> _].
            + iDestruct "He" as (??????) "[%Hp _]".
              iPureIntro. intros Heq. by destruct Hp as [-> _]. }
        iAssert (⌜γs = ∅⌝)%I as %->.
        { destruct (decide (γs = ∅)) as [-> | Hne]; [done|].
          apply set_choose_L in Hne as [γ Hin].
          iDestruct (big_sepS_elem_of with "HbigL") as (lb) "[_ %Hsub]"; [exact Hin|].
          simpl in Hsub. destruct Hsub as (v' & [(He1 & _ & _)|(He1 & _ & He2)]).
          - discriminate.
          - subst v'. injection He1 as ->.
            iPureIntro. exfalso. by apply (Hw_not_loc lb). }
        rewrite size_empty. iPureIntro. lia.
    - (* tstring *)
      simpl. iDestruct "Hser" as "[_ %Hc0]". subst c.
      iAssert (⌜γs = ∅⌝)%I as %->.
      { destruct (decide (γs = ∅)) as [-> | Hne]; [done|].
        apply set_choose_L in Hne as [γ Hin].
        iDestruct (big_sepS_elem_of with "HbigL") as (lb) "[_ %Habs]"; [exact Hin|]. done. }
      rewrite size_empty. by iPureIntro.
    - (* tint *)
      simpl. iDestruct "Hser" as "[_ %Hc0]". subst c.
      iAssert (⌜γs = ∅⌝)%I as %->.
      { destruct (decide (γs = ∅)) as [-> | Hne]; [done|].
        apply set_choose_L in Hne as [γ Hin].
        iDestruct (big_sepS_elem_of with "HbigL") as (lb) "[_ %Habs]"; [exact Hin|]. done. }
      rewrite size_empty. by iPureIntro.
    - (* tauth *)
      simpl. iDestruct "Hser" as "[[Hf %Hc] | [He %Hc]]"; subst c.
      + (* c = 0 (filled): [lg_mapg_unalloc lb_a] excludes any frag *)
        rewrite /auth_susp_ser_p_fill.
        iDestruct "Hf" as (p lb_a lr a' h r [-> ->]) "[#Hunalloc _]".
        iAssert (⌜γs = ∅⌝)%I as %->.
        { destruct (decide (γs = ∅)) as [-> | Hne]; [done|].
          apply set_choose_L in Hne as [γ Hin].
          iDestruct (big_sepS_elem_of with "HbigL") as (lb) "[#Hfrag %Hsub]"; [exact Hin|].
          destruct Hsub as (?&?&?&?&?&Heq1&Heq2).
          injection Heq1 as -> -> -> -> ->. injection Heq2 as ->.
          by iDestruct (lg_mapg_frag_unalloc_excl with "Hfrag Hunalloc") as %[]. }
        rewrite size_empty. iPureIntro. lia.
      + (* c = 1 (suspended): at most 1 element via lg_mapg_agree *)
        rewrite /auth_susp_ser_p_emp.
        iDestruct "He" as (p lb_a lr a' h r [-> ->]) "_".
        destruct (decide (γs = ∅)) as [-> | Hne].
        { rewrite size_empty. iPureIntro. lia. }
        apply set_choose_L in Hne as [γ Hin].
        iDestruct (big_sepS_elem_of with "HbigL") as (lb) "[#Hfrag %Hsub]"; [exact Hin|].
        destruct Hsub as (?&?&?&?&?&Heq1&Heq2).
        injection Heq1 as -> -> -> -> ->. injection Heq2 as ->.
        iAssert (⌜∀ γ', γ' ∈ γs → γ' ∈ ({[γ]} : gset gname)⌝)%I as %Hsubeq.
        { iIntros (γ' Hin').
          iDestruct (big_sepS_elem_of with "HbigL") as (lb') "[#Hfrag' %Hsub']"; [exact Hin'|].
          destruct Hsub' as (?&?&?&?&?&Heq1&Heq2).
          injection Heq1 as -> -> -> -> ->. injection Heq2 as ->.
          iDestruct (lg_mapg_agree with "Hfrag Hfrag'") as "(% & _ & _)".
          iPureIntro. set_solver. }
        assert (γs ⊆ ({[γ]} : gset gname)) by set_solver.
        iPureIntro. transitivity (size ({[γ]} : gset gname)).
        * by apply subseteq_size.
        * by rewrite size_singleton.
  Qed.

  (** [γl] uniqueness for [susp_ser_p_real]:
      Two γ-sets of size [c] both ranging over labels of [a] (via
      [lg_mapg_frag] and [p_sub_obj]) must coincide. This is the key fact
      that lets [p_finish] reconcile the [γl] supplied by the caller with
      the [γl0] returned by [susp_p_ser_spec]'s [tern_state] post.

      Reasoning sketch:
      - [Hser : susp_ser_p_real t c a s] structurally exposes the c
        tauth-leaves of [a]; for each leaf, [p_sub_obj t a #lb] forces the
        label [lb] to be the explicit first projection in [a].
      - [lg_mapg_agree] makes [lb ↦ γ] functional, so the c labels in [a]
        determine at most c distinct γ's. Two γ-sets of size c saturating
        these constraints must coincide. *)
  Lemma susp_ser_p_real_γl_unique (γl γl0 : gset gname) (t : evi_type) (a : val) (s : string) (c : nat) :
    susp_ser_p_real t c a s -∗
    ⌜size γl = c⌝ -∗
    ⌜size γl0 = c⌝ -∗
    ([∗ set] γ ∈ γl,
       ∃ lb, lg_mapg_frag lb γ ∗ ⌜p_sub_obj t a #lb⌝) -∗
    ([∗ set] γ ∈ γl0,
       ∃ lb, lg_mapg_frag lb γ ∗ ⌜p_sub_obj t a #lb⌝) -∗
    ⌜γl = γl0⌝.
  Proof.
    iIntros "#Hser %Hsz %Hsz0 #HbigL #HbigL'".
    (* Combine the two big_sep's at γl ∪ γl0 (both bodies are persistent),
       then apply the cardinality bound to conclude
       [size (γl ∪ γl0) ≤ c]. With [size γl = size γl0 = c], that forces
       [γl = γl0]. *)
    iAssert ([∗ set] γ ∈ γl ∪ γl0,
              ∃ lb, lg_mapg_frag lb γ ∗ ⌜p_sub_obj t a #lb⌝)%I as "#Hbig_union".
    { iApply big_sepS_intro. iIntros "!#" (γ Hin).
      apply elem_of_union in Hin as [Hin | Hin].
      - iApply (big_sepS_elem_of with "HbigL"); done.
      - iApply (big_sepS_elem_of with "HbigL'"); done. }
    iDestruct (susp_ser_p_real_γl_card_le with "Hser Hbig_union") as %Hle.
    iPureIntro.
    assert (γl ⊆ γl ∪ γl0) as Hsub1 by set_solver.
    assert (γl0 ⊆ γl ∪ γl0) as Hsub2 by set_solver.
    transitivity (γl ∪ γl0).
    - apply set_subseteq_size_eq; [done|lia].
    - symmetry. apply set_subseteq_size_eq; [done|lia].
  Qed.

  Lemma gt_child :
    ∀ m vm dm ps gm pvm (id ctr ctr' Nc pn : nat) t x (q : Qp),
      ⌜ctr > 0⌝ -∗ ⌜(1/2 < q)%Qp⌝ -∗ vm_big_sep m vm -∗
      intransit q -∗ stok_unset -∗ pencount_frag pn -∗
      sub_susp_count_frags t x ctr id Nc -∗
      visited_mapg_auth vm dm ps pn ctr' gm pvm -∗
      (⌜pn > 0 ∨ (∃ id' v', id' > id ∧ m !! #id' = Some v')⌝).
  Proof.
    iIntros (m vm dm ps gm pvm id ctr ctr' Nc pn t x q).
    iIntros "%Hctr %Hq Hvm Hintr Hstok Hpn Hsub Hauth".
    iDestruct "Hsub" as "(_ & _ & Hcount & _)".
    iAssert (∀ (v_outer : val) (tind : evi_type) (vind : val) (cind : nat),
               ⌜cind > 0⌝ -∗ sub_susp_count tind vind cind id Nc v_outer -∗
               ∃ γ, visit_pending γ ∨
                    (∃ id', ⌜id' > id⌝ ∗ visit_done γ id') ∨
                    (visit_finished γ ∗ intransit (1/2)))%I
      with "[]" as "Hext".
    { iIntros (v_outer tind).
      iInduction tind as [t1 t2 | t1 t2 | | | ] "IH".
      all: iIntros (vind cind) "%Hci Hcnt".
      - simpl. iDestruct "Hcnt" as (c1 c2 v1 v2 [-> Hsum]) "[Hc1 Hc2]".
        destruct c1 as [|c1'].
        + assert (c2 > 0) by lia.
          iApply ("IH1" $! v2 c2 with "[%//] Hc2").
        + assert (S c1' > 0) by lia.
          iApply ("IH" $! v1 (S c1') with "[%//] Hc1").
      - simpl. iDestruct "Hcnt" as "[H|H]".
        + iDestruct "H" as (?) "[-> Hc']".
          iApply ("IH" with "[%//] Hc'").
        + iDestruct "H" as (?) "[-> Hc']".
          iApply ("IH1" with "[%//] Hc'").
      - simpl. iDestruct "Hcnt" as "[_ %Heq]". lia.
      - simpl. iDestruct "Hcnt" as "[_ %Heq]". lia.
      - simpl. iDestruct "Hcnt" as (v1) "[_ Hcases]".
        iDestruct "Hcases" as "[H|H]".
        + iDestruct "H" as (h) "%Heq". destruct Heq as [_ Heq]. lia.
        + iDestruct "H" as (susp) "[_ Hcases]".
          iDestruct "Hcases" as "[Hh|Hp]".
          * iDestruct "Hh" as (h) "[_ %Heq]". lia.
          * iDestruct "Hp" as (p γ) "(_ & _ & _ & _ & _ & Hdisj)".
            iExists γ. iExact "Hdisj". }
    iDestruct ("Hext" $! x t x ctr with "[%//] Hcount") as (γ) "[Hpend|[Hdone|Hfin]]".
    - iDestruct "Hauth" as "(Hms & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & %Hpcoh)".
      iDestruct (own_valid_2 with "Hms Hpend") as %Hvm.
      apply auth_both_valid_discrete in Hvm as [Hincl Hvalid].
      apply (singleton_included_exclusive_l vm γ pending_val) in Hincl;
        [|apply _|exact Hvalid].
      assert (vm !! γ = Some pending_val) as Hincl'.
      { destruct (vm !! γ) as [s|] eqn:Hvγ;
          rewrite Hvγ in Hincl; [|by inversion Hincl].
        apply Some_equiv_inj in Hincl. rewrite /pending_val in Hincl |- *.
        destruct s as [s'| |]; [|by inversion Hincl|by inversion Hincl].
        apply (inj Cinl) in Hincl. destruct s' as [v|]; [|by inversion Hincl].
        apply (inj Excl) in Hincl. apply leibniz_equiv in Hincl. by subst. }
      clear Hincl. rename Hincl' into Hincl.
      destruct Hpcoh as [-> Hpn_in].
      apply Hpn_in in Hincl.
      iPureIntro. left.
      assert (size ps ≠ 0) by (apply size_non_empty_iff; set_solver).
      lia.
    - iDestruct "Hdone" as (id' Hgt) "Hvd".
      iDestruct (visit_done_lookup with "Hauth Hvd") as "(%Hvmγ & _ & _)".
      iDestruct (big_sepM_lookup with "Hvm") as "Hlam"; [exact Hvmγ|].
      iDestruct ("Hlam" $! id' with "[//]") as (v') "%Hmid'".
      iPureIntro. right. exists id', v'. split; done.
    - (* Hfin: visit_finished γ ∗ intransit (1/2). Combine with input intransit q
         (q > 1/2): total q + 1/2 > 1, invalid → False. *)
      iDestruct "Hfin" as "[_ Hintr_half]".
      iCombine "Hintr Hintr_half" as "Hboth".
      iDestruct (intransit_valid with "Hboth") as %Hv.
      iPureIntro. exfalso.
      (* Hv : (q + 1/2 ≤ 1)%Qp, Hq : (1/2 < q)%Qp.
         From Hq, exists r > 0 such that q = 1/2 + r. Substituting:
         1/2 + r + 1/2 ≤ 1, i.e. 1 + r ≤ 1 — contradicts Qp.not_add_le_l. *)
      apply Qp.lt_sum in Hq as [r ->].
      revert Hv. rewrite (Qp.add_comm (1/2)%Qp r) -Qp.add_assoc Qp.half_half.
      apply Qp.not_add_le_r.
  Qed.

End authentikit_helpers.