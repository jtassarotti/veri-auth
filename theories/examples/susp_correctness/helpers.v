From auth.prelude Require Import stdpp.
From auth.rel_logic_tern_susp Require Export spec_rules spec_tactics.
From iris.algebra Require Import gmap auth.
From iris.algebra.lib Require Import dfrac_agree.
From auth.examples.susp_correctness Require Import resource_algebras definitions.

Section authentikit_helpers.
  Context `{!authG Σ, !seqG Σ, !visited_mapG Σ, !lg_mapG Σ, !mapG Σ, !capG Σ, !intransitG Σ, !stateG Σ} (N : namespace).

  Lemma sub_susp_count_update_map :
    ∀ t v c (id : nat) Nc m,
      m !! #id = None →
      ⌜c > 0⌝ -∗
      mapg_auth m -∗
      sub_susp_count t v c id Nc v ==∗
        mapg_auth (mapg_insert_def m #id v) ∗
        sub_susp_count_frags t v c id Nc.
  Proof.
    iIntros (t v c id Nc m Hnone) "%Hc Hmauth Hcnt".
    iAssert (∀ (v_outer : val) (tind : evi_type) (vind : val) (cind : nat),
               ⌜cind > 0⌝ -∗ sub_susp_count tind vind cind id Nc v_outer -∗
               ∃ q, mapg_frag #id q v_outer)%I with "[]" as "Hext".
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
    iDestruct (mapg_subset with "Hmauth Hfrag") as %(y & Hy & _).
    rewrite Hnone in Hy. inversion Hy.
  Qed.

  Lemma mapg_remove_count_0 :
    ∀ t v id Nc m,
      Nc ≠ 0 →
      sub_susp_count_frags t v 0 id Nc -∗
      mapg_auth m
      ==∗
        sub_susp_count t v 0 id Nc v ∗
        mapg_auth (delete #id m).
  Proof.
    iIntros (t v id Nc m HN) "(#Hcap & %Hle & Hcount & Hagg) Hmauth".
    iDestruct "Hagg" as "[%Heq | [%Hlt Hq]]".
    - exfalso. lia.
    - iDestruct "Hq" as (q Hqeq) "Hfrag".
      replace (Nc - 0) with Nc in Hqeq by lia.
      assert (q = 1%Qp) as ->.
      { apply (inj (λ q : Qp, (q * pos_to_Qp (Pos.of_nat Nc))%Qp)).
        rewrite Qp.mul_1_l. exact Hqeq. }
      iMod (mapg_remove with "Hmauth Hfrag") as "Hmauth".
      iModIntro. iFrame.
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
      (susp : loc) (p : proph_id) (v_outer : val) m d ps pn :
    d !! γ = None →
    id > pid →
    visited_mapg_auth m d ps pn -∗
    lg_mapg_frag susp γ -∗
    susp ↦ᵥ{#3/4} InjLV (#pid, #p) -∗
    sub_susp_count t (InjRV (InjRV #susp)) c pid Nc v_outer
    ==∗
      visited_map_update_done m d ps pn γ id ∗
      visit_reached_done γ id ∗
      sub_susp_count t (InjRV (InjRV #susp)) c pid Nc v_outer ∗
      susp ↦ᵥ{#3/4} InjLV (#pid, #p).
  Proof.
    iIntros (Hfresh Hid) "Hauth #Hlg Hsusp Hcount".
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
          iDestruct "Hdisj" as "[Hpen|Hdone]".
          -- iMod (visited_transition_done m d ps pn γ id with "Hauth Hpen")
               as "(Hauth' & Hdone)"; [done|].
             iDestruct (visit_done_keep with "Hdone") as "[Hdone #Hreached]".
             iModIntro.
             iSplitL "Hauth'"; [iExact "Hauth'"|].
             iSplit; [iExact "Hreached"|].
             iSplitR "Hsusp"; [|iExact "Hsusp"].
             simpl.
             iExists (InjRV #susp). iSplit; [done|].
             iRight. iExists susp. iSplit; [done|].
             iRight. iExists p, γ.
             iFrame "Hlg' Hsusp_s Hfrag Hcap'". iSplit; [done|].
             iRight. iExists id. iSplit; [iPureIntro; done|].
             iLeft. iExact "Hdone".
          -- iAssert (∃ n, visit_reached_done γ n)%I as "(%n & #Hreached)".
             { iDestruct "Hdone" as (n Hn) "[Hd|Hf]".
               - iExists n. iDestruct "Hd" as "[_ $]".
               - iExists n. iDestruct "Hf" as "[[_ $] _]". }
             iDestruct "Hauth" as "(Hms & Hd & Hrest)".
             iDestruct (own_valid_2 with "Hd Hreached") as %Hvd.
             apply auth_both_valid_discrete in Hvd as [Hincl _].
             apply singleton_included_l in Hincl as (xd & Hxd & _).
             exfalso. rewrite Hfresh in Hxd. inversion Hxd.
  Qed.

  Lemma visited_update_done (id : nat) :
    ∀ t t' v (c pid Nc : nat) (susp : loc) (p : proph_id) γ m d ps pn,
      d !! γ = None →
      id > pid →
      v_sub_obj t' v #susp →
      visited_mapg_auth m d ps pn -∗
      lg_mapg_frag susp γ -∗
      susp ↦ᵥ{#3/4} InjLV (#pid, #p) -∗
      sub_susp_count_frags t v c pid Nc
      ==∗
        visit_reached_done γ id ∗
        visited_map_update_done m d ps pn γ id ∗
        sub_susp_count_frags t v c pid Nc ∗
        susp ↦ᵥ{#3/4} InjLV (#pid, #p).
  Proof.
    iIntros (t t' v c pid Nc susp p γ m d ps pn Hfresh Hid Hsub)
      "Hauth #Hlg Hsusp (#Hcap & %Hle & Hinner & Hagg)".
    iAssert (∀ v_outer (tind : evi_type) (vind : val) (cind : nat) (tind' : evi_type),
               ⌜v_sub_obj tind' vind #susp⌝ -∗
               visited_mapg_auth m d ps pn -∗
               lg_mapg_frag susp γ -∗
               susp ↦ᵥ{#3/4} InjLV (#pid, #p) -∗
               sub_susp_count tind vind cind pid Nc v_outer ==∗
               visit_reached_done γ id ∗
               visited_map_update_done m d ps pn γ id ∗
               sub_susp_count tind vind cind pid Nc v_outer ∗
               susp ↦ᵥ{#3/4} InjLV (#pid, #p))%I
      with "[]" as "Hlem".
    { iClear "Hcap Hlg".
      iIntros (v_outer t0).
      iInduction t0 as [t1 t2 | t1 t2 | | | ] "IH".
      all: iIntros (vind cind tind') "%Hsubind Hauth #Hlg Hsusp Hinner".
      - (* tprod *)
        simpl. iDestruct "Hinner" as (c1 c2 v1 v2 [-> <-]) "[Hc1 Hc2]".
        destruct tind' as [t1' t2' | | | | ]; simpl in Hsubind; try done.
        + destruct Hsubind as (v1' & v2' & Heq & Hdisj). injection Heq as <- <-.
          destruct Hdisj as [<- | [<- | [Hsub1 | Hsub2]]].
          * by iDestruct (sub_susp_count_ne_loc with "Hc1") as %[].
          * by iDestruct (sub_susp_count_ne_loc with "Hc2") as %[].
          * iMod ("IH" $! v1 c1 t1' Hsub1 with "Hauth Hlg Hsusp Hc1")
              as "(#Hreached & Hauth' & Hc1' & Hsusp')".
            iModIntro. iFrame "Hreached Hauth' Hsusp'".
            iExists c1, c2, v1, v2. by iFrame.
          * iMod ("IH1" $! v2 c2 t2' Hsub2 with "Hauth Hlg Hsusp Hc2")
              as "(#Hreached & Hauth' & Hc2' & Hsusp')".
            iModIntro. iFrame "Hreached Hauth' Hsusp'".
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
            iMod (sub_susp_count_eats_susp id _ cind pid Nc γ susp p v_outer m d ps pn
              with "Hauth Hlg Hsusp Hinner")
              as "(Hauth' & #Hreached & Hinner' & Hsusp')"; [done|done|].
            iModIntro. by iFrame. }
    iMod ("Hlem" $! v t v c t' Hsub with "Hauth Hlg Hsusp Hinner")
      as "(#Hreached & Hauth' & Hinner & Hsusp)".
    iModIntro. iFrame "Hreached Hauth' Hsusp Hcap Hinner Hagg". done.
  Qed.

  Lemma sub_susp_count_finalizes_susp (id : nat) t (c pid Nc : nat) γ
      (susp : loc) (p : proph_id) (v_outer : val) m d ps pn :
    visited_mapg_auth m d ps pn -∗
    lg_mapg_frag susp γ -∗
    susp ↦ᵥ{#3/4} InjLV (#pid, #p) -∗
    sub_susp_count t (InjRV (InjRV #susp)) c pid Nc v_outer -∗
    visit_reached_done γ id -∗
    intransit 1%Qp ==∗
      visit_finished γ id ∗
      visited_map_update_finished m d ps pn γ id ∗
      sub_susp_count t (InjRV (InjRV #susp)) c pid Nc v_outer ∗
      susp ↦ᵥ{#3/4} InjLV (#pid, #p).
  Proof.
    iIntros "Hauth #Hlg Hsusp Hcount #Hreached Hintr".
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
          iDestruct "Hdisj" as "[Hpen|Hinner_disj]".
          { by iDestruct (visited_reached_done_invalid with "Hauth Hreached Hpen") as %[]. }
          iDestruct "Hinner_disj" as (id' Hid') "[Hinner_done|[Hinner_fin Hintr2]]".
          -- iDestruct (visit_done_keep with "Hinner_done") as "[Hinner_done #Hreached']".
             iDestruct (visited_reached_done_agree with "Hreached Hreached'") as %->.
             iMod (visited_transition_finished with "Hauth Hinner_done")
               as "(Hauth' & #Hfin)".
             iModIntro.
             iSplit; [iExact "Hfin"|].
             iSplitL "Hauth'"; [iExact "Hauth'"|].
             iSplitR "Hsusp"; [|iExact "Hsusp"].
             simpl.
             iExists (InjRV #susp). iSplit; [done|].
             iRight. iExists susp. iSplit; [done|].
             iRight. iExists p', γ.
             iFrame "Hlg' Hsusp_s Hfrag Hcap'". iSplit; [done|].
             iRight. iExists id'. iSplit; [iPureIntro; done|].
             iRight. iFrame "Hintr". iExact "Hfin".
          -- by iDestruct (intransit_excl_full with "Hintr Hintr2") as %[].
  Qed.

  Lemma visited_update_finished (id : nat) :
      ∀ t t' v (c pid Nc : nat) (susp : loc) (p : proph_id) γ m d ps pn,
        id > pid →
        v_sub_obj t' v #susp →
        visited_mapg_auth m d ps pn -∗
        lg_mapg_frag susp γ -∗
        susp ↦ᵥ{#3/4} InjLV (#pid, #p) -∗
        sub_susp_count_frags t v c pid Nc -∗
        visit_reached_done γ id -∗
        intransit 1%Qp ==∗
          visit_finished γ id ∗
          visited_map_update_finished m d ps pn γ id ∗
          sub_susp_count_frags t v c pid Nc ∗
          susp ↦ᵥ{#3/4} InjLV (#pid, #p).
  Proof.
    iIntros (t t' v c pid Nc susp p γ m d ps pn Hid Hsub)
      "Hauth #Hlg Hsusp (#Hcap & %Hle & Hinner & Hagg) #Hreached Hintr".
    iAssert (∀ v_outer (tind : evi_type) (vind : val) (cind : nat) (tind' : evi_type),
               ⌜v_sub_obj tind' vind #susp⌝ -∗
               visited_mapg_auth m d ps pn -∗
               lg_mapg_frag susp γ -∗
               susp ↦ᵥ{#3/4} InjLV (#pid, #p) -∗
               sub_susp_count tind vind cind pid Nc v_outer -∗
               intransit 1%Qp ==∗
               visit_finished γ id ∗
               visited_map_update_finished m d ps pn γ id ∗
               sub_susp_count tind vind cind pid Nc v_outer ∗
               susp ↦ᵥ{#3/4} InjLV (#pid, #p))%I
      with "[]" as "Hlem".
    { iClear "Hcap Hlg".
      iIntros (v_outer t0).
      iInduction t0 as [t1 t2 | t1 t2 | | | ] "IH".
      all: iIntros (vind cind tind') "%Hsubind Hauth #Hlg Hsusp Hinner Hintr".
      - (* tprod *)
        simpl. iDestruct "Hinner" as (c1 c2 v1 v2 [-> <-]) "[Hc1 Hc2]".
        destruct tind' as [t1' t2' | | | | ]; simpl in Hsubind; try done.
        + destruct Hsubind as (v1' & v2' & Heq & Hdisj). injection Heq as <- <-.
          destruct Hdisj as [<- | [<- | [Hsub1 | Hsub2]]].
          * by iDestruct (sub_susp_count_ne_loc with "Hc1") as %[].
          * by iDestruct (sub_susp_count_ne_loc with "Hc2") as %[].
          * iMod ("IH" $! v1 c1 t1' Hsub1 with "Hauth Hlg Hsusp Hc1 Hintr")
              as "(#Hfin & Hauth' & Hc1' & Hsusp')".
            iModIntro. iFrame "Hfin Hauth' Hsusp'".
            iExists c1, c2, v1, v2. by iFrame.
          * iMod ("IH1" $! v2 c2 t2' Hsub2 with "Hauth Hlg Hsusp Hc2 Hintr")
              as "(#Hfin & Hauth' & Hc2' & Hsusp')".
            iModIntro. iFrame "Hfin Hauth' Hsusp'".
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
            iMod (sub_susp_count_finalizes_susp id _ cind pid Nc γ susp p v_outer m d ps pn
              with "Hauth Hlg Hsusp Hinner Hreached Hintr")
              as "(#Hfin & Hauth' & Hinner' & Hsusp')".
            iModIntro. by iFrame. }
    iMod ("Hlem" $! v t v c t' Hsub with "Hauth Hlg Hsusp Hinner Hintr")
      as "(#Hfin & Hauth' & Hinner & Hsusp)".
    iModIntro. iFrame "Hfin Hauth' Hsusp Hcap Hinner Hagg". done.
  Qed.

  (* Substantive tauth B2 update: reached via tsum's right branch when the
     external [susp] matches a B2 leaf. Consumes [c = 1] for the leaf,
     releases the [1/Nc] fragment, steps the verifier store. *)
  Lemma count_update_eats_susp K tᵥ v' t (susp : loc) (c pid Nc : nat) (h : string) (v_outer : val) γ (n : nat) :
    lg_mapg_frag susp γ -∗
    visit_finished γ n -∗
    sub_susp_count t (InjRV (InjRV #susp)) c pid Nc v_outer -∗
    susp ↦ᵥ{#(3/4)} InjLV (#pid, v') -∗
    spec_verifier tᵥ (fill K (#susp <- InjRV #h))
    ={⊤}=∗
      ⌜c = 1⌝ ∗
      intransit 1%Qp ∗
      sub_susp_count t (InjRV (InjRV #susp)) (c-1) pid Nc v_outer ∗
      susp ↦ᵥ{#(3/4)} InjRV #h ∗
      spec_verifier tᵥ (fill K (#())) ∗
      mapg_frag #pid (1 / pos_to_Qp (Pos.of_nat Nc))%Qp v_outer.
  Proof.
    iIntros "#Hlg #Hfin Hinner Hsusp Hspec".
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
          iCombine "Hsusp Hsusp_s" as "Hsusp_full".
          rewrite Qp.three_quarter_quarter.
          iMod (step_verifier_store with "[$Hsusp_full $Hspec]") as "(Hspec & Hsusp_full)"; [done|].
          iEval (rewrite -Qp.three_quarter_quarter) in "Hsusp_full".
          iDestruct "Hsusp_full" as "[Hsusp Hsusp_s]".
          iDestruct "Hdisj" as "[Hpen|Hinner_disj]".
          { by iDestruct (visited_invalid_2 with "[$Hpen $Hfin]") as %[]. }
          iDestruct "Hinner_disj" as (id Hidpid) "[Hdone|[Hifin Hintr]]".
          { by iDestruct (visited_invalid_3 with "[$Hdone $Hfin]") as %[]. }
          iModIntro.
          iSplitR; [done|].
          iFrame "Hintr".
          iSplitR "Hsusp Hspec Hfrag".
          { iExists (InjRV #susp). iSplit; [done|].
            iRight. iExists susp. iSplit; [done|].
            iLeft. iExists h. iFrame "Hsusp_s". subst c. done. }
          iFrame "Hsusp Hspec Hfrag".
  Qed.

  Lemma count_update :
    ∀ K tᵥ v v' (t t' : evi_type) (susp : loc) (c pid Nc : nat) (h : string) γ (n : nat),
      ⌜v_sub_obj t' v #susp⌝ -∗
      lg_mapg_frag susp γ -∗
      visit_finished γ n -∗
      sub_susp_count_frags t v c pid Nc -∗
      susp ↦ᵥ{#(3/4)} InjLV (#pid, v') -∗
      spec_verifier tᵥ (fill K (#susp <- InjRV #h))
      ={⊤}=∗
        intransit 1%Qp ∗
        sub_susp_count_frags t v (c-1) pid Nc ∗
        susp ↦ᵥ{#(3/4)} InjRV #h ∗
        spec_verifier tᵥ (fill K (#())).
  Proof.
    iIntros (K tᵥ v v' t t' susp c pid Nc h γ n)
      "%Hsub #Hlg #Hfin (#Hcap & %Hle & Hinner & Hagg) Hsusp Hspec".
    iAssert (∀ v_outer (t : evi_type) (v : val) (c : nat) (t' : evi_type),
               ⌜v_sub_obj t' v #susp⌝ -∗
               sub_susp_count t v c pid Nc v_outer -∗
               susp ↦ᵥ{#3/4} InjLV (#pid, v') -∗
               spec_verifier tᵥ (fill K (#susp <- InjRV #h)) ={⊤}=∗
               ⌜1 ≤ c⌝ ∗
               intransit 1%Qp ∗
               sub_susp_count t v (c - 1) pid Nc v_outer ∗
               susp ↦ᵥ{#3/4} InjRV #h ∗
               spec_verifier tᵥ (fill K #()) ∗
               mapg_frag #pid (1 / pos_to_Qp (Pos.of_nat Nc))%Qp v_outer)%I
      with "[]" as "Hlem".
    { iClear "Hcap".
      iIntros (v_outer tind).
      iInduction tind as [t1 t2 | t1 t2 | | | ] "IH".
      all: iIntros (vind cind tind') "%Hsubind Hinner' Hsusp' Hspec'".
      - (* tind = tprod *)
        simpl. iDestruct "Hinner'" as (c1 c2 v1 v2 [-> <-]) "[Hc1 Hc2]".
        destruct tind' as [t1' t2' | | | | ]; simpl in Hsubind; try done.
        + destruct Hsubind as (v1' & v2' & Heq & Hdisj). injection Heq as <- <-.
          destruct Hdisj as [<- | [<- | [Hsub1 | Hsub2]]].
          * by iDestruct (sub_susp_count_ne_loc with "Hc1") as %[].
          * by iDestruct (sub_susp_count_ne_loc with "Hc2") as %[].
          * iMod ("IH" $! v1 c1 t1' Hsub1 with "Hc1 Hsusp' Hspec'")
              as "(%Hc & Hintr & Hc1' & Hsusp'' & Hspec'' & Hnew)".
            iModIntro. iSplit; [iPureIntro; lia|].
            iFrame "Hintr Hsusp'' Hspec'' Hnew".
            iExists (c1 - 1), c2, v1, v2.
            iSplit; [iPureIntro; split; [done|lia]|]. iFrame.
          * iMod ("IH1" $! v2 c2 t2' Hsub2 with "Hc2 Hsusp' Hspec'")
              as "(%Hc & Hintr & Hc2' & Hsusp'' & Hspec'' & Hnew)".
            iModIntro. iSplit; [iPureIntro; lia|].
            iFrame "Hintr Hsusp'' Hspec'' Hnew".
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
            iMod (count_update_eats_susp with "Hlg Hfin Hinner' Hsusp' Hspec'") as
              "(%Hc & Hintr & Hc' & Hsusp'' & Hspec'' & Hnew)".
            iModIntro. iSplit; [iPureIntro; lia|]. by iFrame. }
    iMod ("Hlem" $! v t v c t' Hsub with "Hinner Hsusp Hspec")
      as "(%Hc & Hintr & Hinner & Hsusp & Hspec & Hnew)".
    iModIntro. iFrame "Hintr Hsusp Hspec Hcap".
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

  (** Cardinality bound: any γ-set ranging over labels of [a] has size at
      most [c]. The substantive cases are:
      - [tauth c=0]: [auth_susp_ser_p_fill] carries [lg_mapg_unalloc lb_a],
        which excludes any [lg_mapg_frag lb_a γ] in [γs].
      - [tauth c=1]: at most one [γ] by [lg_mapg_agree] on the unique [lb_a].
      - [tprod]: by partition into v1/v2 sub-trees, summing IH bounds. *)
  Lemma susp_ser_p_real_γl_card_le (t : evi_type) (a : val) (s : string) (c : nat) (γs : gset gname) :
    susp_ser_p_real N t c a s -∗
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
      the [γl0] returned by [susp_p_ser_spec]'s [good_state] post.

      Reasoning sketch:
      - [Hser : susp_ser_p_real t c a s] structurally exposes the c
        tauth-leaves of [a]; for each leaf, [p_sub_obj t a #lb] forces the
        label [lb] to be the explicit first projection in [a].
      - [lg_mapg_agree] makes [lb ↦ γ] functional, so the c labels in [a]
        determine at most c distinct γ's. Two γ-sets of size c saturating
        these constraints must coincide. *)
  Lemma susp_ser_p_real_γl_unique (γl γl0 : gset gname) (t : evi_type) (a : val) (s : string) (c : nat) :
    susp_ser_p_real N t c a s -∗
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

End authentikit_helpers.