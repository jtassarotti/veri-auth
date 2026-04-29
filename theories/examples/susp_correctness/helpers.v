From auth.prelude Require Import stdpp.
From auth.rel_logic_tern_susp Require Export spec_rules spec_tactics.
From auth.examples.susp_correctness Require Import resource_algebras definitions.

Section authentikit_helpers.
  Context `{!authG Σ, !seqG Σ, !visited_mapG Σ, !lg_mapG Σ, !mapG Σ, !capG Σ, !intransitG Σ} (N : namespace).

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

  Lemma sub_susp_count_frags_N_agree t v c id Nc Nc' :
    sub_susp_count_frags t v c id Nc -∗ cap_frag id Nc' -∗ ⌜Nc = Nc'⌝.
  Proof.
    iIntros "(Hcap & _) Hcap'".
    iApply (cap_frag_agree with "Hcap Hcap'").
  Qed.

  Lemma sub_susp_count_eats_susp (id : nat) t (c pid Nc : nat) γ
      (susp : loc) (p : proph_id) (v_outer : val) m d :
    d !! γ = None →
    id > pid →
    visited_mapg_auth m d -∗
    lg_mapg_frag susp γ -∗
    susp ↦ᵥ{#3/4} InjLV (#pid, #p) -∗
    sub_susp_count t (InjRV (InjRV #susp)) c pid Nc v_outer -∗
    visit_pending γ ==∗
      visited_map_update_done m d γ id ∗
      visit_reached_done γ id ∗
      sub_susp_count t (InjRV (InjRV #susp)) c pid Nc v_outer ∗
      susp ↦ᵥ{#3/4} InjLV (#pid, #p).
  Proof.
    iIntros (Hfresh Hid) "Hauth #Hlg Hsusp Hcount Hpending".
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
          -- iMod (visited_transition_done m d γ id with "Hauth Hpending Hpen")
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
          -- iDestruct "Hdone" as (n) "[%Hn [Hdone|[Hfin _]]]".
             ++ by iDestruct (visited_invalid_1 with "[$Hpending $Hdone]") as %[].
             ++ by iDestruct (visited_invalid_2 with "[$Hpending $Hfin]") as %[].
  Qed.

  Lemma visited_update_done (id : nat) :
    ∀ t t' v (c pid Nc : nat) (susp : loc) (p : proph_id) γ m d,
      d !! γ = None →
      id > pid →
      sub_obj t' v (InjRV #susp) →
      visited_mapg_auth m d -∗
      lg_mapg_frag susp γ -∗
      susp ↦ᵥ{#3/4} InjLV (#pid, #p) -∗
      sub_susp_count_frags t v c pid Nc -∗
      visit_pending γ ==∗
        visit_reached_done γ id ∗
        visited_map_update_done m d γ id ∗
        sub_susp_count_frags t v c pid Nc ∗
        susp ↦ᵥ{#3/4} InjLV (#pid, #p).
  Proof.
    iIntros (t t' v c pid Nc susp p γ m d Hfresh Hid Hsub)
      "Hauth #Hlg Hsusp (#Hcap & %Hle & Hinner & Hagg) Hpending".
    iAssert (∀ v_outer (tind : evi_type) (vind : val) (cind : nat) (tind' : evi_type),
               ⌜sub_obj tind' vind (InjRV #susp)⌝ -∗
               visited_mapg_auth m d -∗
               lg_mapg_frag susp γ -∗
               susp ↦ᵥ{#3/4} InjLV (#pid, #p) -∗
               sub_susp_count tind vind cind pid Nc v_outer -∗
               visit_pending γ ==∗
               visit_reached_done γ id ∗
               visited_map_update_done m d γ id ∗
               sub_susp_count tind vind cind pid Nc v_outer ∗
               susp ↦ᵥ{#3/4} InjLV (#pid, #p))%I
      with "[]" as "Hlem".
    { iClear "Hcap Hlg".
      iIntros (v_outer t0).
      iInduction t0 as [t1 t2 | t1 t2 | | | ] "IH".
      all: iIntros (vind cind tind') "%Hsubind Hauth #Hlg Hsusp Hinner Hpending".
      - (* tprod *)
        simpl. iDestruct "Hinner" as (c1 c2 v1 v2 [-> <-]) "[Hc1 Hc2]".
        destruct tind' as [t1' t2' | | | | ]; simpl in Hsubind; try done.
        + destruct Hsubind as (v1' & v2' & Heq & Hdisj). injection Heq as <- <-.
          destruct Hdisj as [<- | [<- | [Hsub1 | Hsub2]]].
          * by iDestruct (sub_susp_count_ne_injr_loc with "Hc1") as %[].
          * by iDestruct (sub_susp_count_ne_injr_loc with "Hc2") as %[].
          * iMod ("IH" $! v1 c1 t1' Hsub1 with "Hauth Hlg Hsusp Hc1 Hpending")
              as "(#Hreached & Hauth' & Hc1' & Hsusp')".
            iModIntro. iFrame "Hreached Hauth' Hsusp'".
            iExists c1, c2, v1, v2. by iFrame.
          * iMod ("IH1" $! v2 c2 t2' Hsub2 with "Hauth Hlg Hsusp Hc2 Hpending")
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
               by iDestruct (sub_susp_count_ne_injL_injR_susp with "Hc") as %[].
            -- subst v''. injection Heq as ->.
               iMod (sub_susp_count_eats_susp id _ cind pid Nc γ susp p v_outer m d
                 with "Hauth Hlg Hsusp Hc Hpending")
                 as "(Hauth' & #Hreached & Hc' & Hsusp')"; [done|done|].
               iModIntro. iFrame "Hreached Hauth' Hsusp'".
               iRight. iExists (InjRV (InjRV #susp)). by iFrame.
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
        simpl. iDestruct "Hinner" as (v1) "[-> Hcases]".
        destruct tind'; simpl in Hsubind; try done.
        + destruct Hsubind as (? & ? & Heq & _); discriminate.
        + destruct Hsubind as (? & [(Heq & _ & _) | (Heq & _ & Heq2)]).
          * discriminate.
          * subst. injection Heq as Heq. by apply no_fix_InjRV in Heq.
        + destruct Hsubind as (? & [Heq|Heq] & ->).
          * injection Heq as ->.
            iDestruct "Hcases" as "[H|H]".
            -- iDestruct "H" as (h) "%Heq'". destruct Heq' as [Heq' _]. discriminate.
            -- iDestruct "H" as (susp') "[%Heq' _]". discriminate.
          * injection Heq as ->.
            iDestruct "Hcases" as "[H|H]".
            -- iDestruct "H" as (h) "%Heq'". destruct Heq' as [Heq' _]. discriminate.
            -- iDestruct "H" as (susp') "[%Heq' _]". by simplify_eq. }
    iMod ("Hlem" $! v t v c t' Hsub with "Hauth Hlg Hsusp Hinner Hpending")
      as "(#Hreached & Hauth' & Hinner & Hsusp)".
    iModIntro. iFrame "Hreached Hauth' Hsusp Hcap Hinner Hagg". done.
  Qed.
    (* iIntros (t t' v c pid Nc susp p γ m d Hfresh Hid Hsub)
      "Hauth #Hlg Hsusp (#Hcap & %Hle & Hinner & Hagg) Hpending".
    iAssert (∀ v_outer (tind : evi_type) (vind : val) (cind : nat) (tind' : evi_type),
               ⌜sub_obj tind' vind (InjRV #susp)⌝ -∗
               visited_mapg_auth m d -∗
               lg_mapg_frag susp γ -∗
               susp ↦ᵥ{#3/4} InjLV (#pid, #p) -∗
               sub_susp_count tind vind cind pid Nc v_outer -∗
               visit_pending γ ==∗
               visited_map_update_done m d γ id ∗
               visit_reached_done γ id ∗
               sub_susp_count tind vind cind pid Nc v_outer ∗
               susp ↦ᵥ{#3/4} InjLV (#pid, #p))%I
      with "[]" as "Hlem".
    { iClear "Hcap Hlg".
      iIntros (v_outer t0).
      iInduction t0 as [t1 t2 | t1 t2 | | | ] "IH".
      all: iIntros (vind cind tind') "%Hsubind Hauth #Hlg Hsusp Hinner Hpending".
      - (* tprod *)
        simpl. iDestruct "Hinner" as (c1 c2 v1 v2 [-> <-]) "[Hc1 Hc2]".
        destruct tind' as [t1' t2' | | | | ]; simpl in Hsubind; try done.
        + destruct Hsubind as (v1' & v2' & Heq & Hdisj). injection Heq as <- <-.
          destruct Hdisj as [<- | [<- | [Hsub1 | Hsub2]]].
          * by iDestruct (sub_susp_count_ne_injr_loc with "Hc1") as %[].
          * by iDestruct (sub_susp_count_ne_injr_loc with "Hc2") as %[].
          * iMod ("IH" $! v1 c1 t1' Hsub1 with "Hauth Hlg Hsusp Hc1 Hpending")
              as "(Hauth' & #Hreached & Hc1' & Hsusp')".
            iModIntro. iFrame "Hauth'".
            iSplitL ""; [iApply "Hreached"|].
            iFrame "Hsusp'".
            iExists c1, c2, v1, v2. by iFrame.
          * iMod ("IH1" $! v2 c2 t2' Hsub2 with "Hauth Hlg Hsusp Hc2 Hpending")
              as "(Hauth' & #Hreached & Hc2' & Hsusp')".
            iModIntro. iFrame "Hauth'".
            iSplitL ""; [iApply "Hreached"|].
            iFrame "Hsusp'".
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
               by iDestruct (sub_susp_count_ne_injL_injR_susp with "Hc") as %[].
            -- subst v''. injection Heq as ->.
               iMod (sub_susp_count_eats_susp id _ cind pid Nc γ susp p v_outer m d
                 with "Hauth Hlg Hsusp Hc Hpending")
                 as "(Hauth' & #Hreached & Hc' & Hsusp')"; [done|done|].
               iModIntro. iFrame "Hauth'".
               iSplitL ""; [iApply "Hreached"|].
               iFrame "Hsusp'".
               iRight. iExists (InjRV (InjRV #susp)). by iFrame.
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
        simpl. iDestruct "Hinner" as (v1) "[-> Hcases]".
        destruct tind'; simpl in Hsubind; try done.
        + destruct Hsubind as (? & ? & Heq & _); discriminate.
        + destruct Hsubind as (? & [(Heq & _ & _) | (Heq & _ & Heq2)]).
          * discriminate.
          * subst. injection Heq as Heq. by apply no_fix_InjRV in Heq.
        + destruct Hsubind as (? & [Heq|Heq] & ->).
          * injection Heq as ->.
            iDestruct "Hcases" as "[H|H]".
            -- iDestruct "H" as (h) "%Heq'". destruct Heq' as [Heq' _]. discriminate.
            -- iDestruct "H" as (susp') "[%Heq' _]". discriminate.
          * injection Heq as ->.
            iDestruct "Hcases" as "[H|H]".
            -- iDestruct "H" as (h) "%Heq'". destruct Heq' as [Heq' _]. discriminate.
            -- iDestruct "H" as (susp') "[%Heq' _]". by simplify_eq. }
    iMod ("Hlem" $! v t v c t' Hsub with "Hauth Hlg Hsusp Hinner Hpending")
      as "(Hauth' & #Hreached & Hinner & Hsusp)".
    iModIntro. iFrame "Hauth'".
    iSplitL ""; [iApply "Hreached"|].
    iFrame "Hsusp Hcap Hinner Hagg". done.
  Qed. *)

  Lemma sub_susp_count_finalizes_susp (id : nat) t (c pid Nc : nat) γ
      (susp : loc) (p : proph_id) (v_outer : val) m d :
    visited_mapg_auth m d -∗
    lg_mapg_frag susp γ -∗
    susp ↦ᵥ{#3/4} InjLV (#pid, #p) -∗
    sub_susp_count t (InjRV (InjRV #susp)) c pid Nc v_outer -∗
    visit_reached_done γ id -∗
    intransit ==∗
      visit_finished γ id ∗
      visited_map_update_finished m d γ id ∗
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
          -- by iDestruct (intransit_excl with "Hintr Hintr2") as %[].
  Qed.

  Lemma visited_update_finished (id : nat) :
      ∀ t t' v (c pid Nc : nat) (susp : loc) (p : proph_id) γ m d,
        id > pid →
        sub_obj t' v (InjRV #susp) →
        visited_mapg_auth m d -∗
        lg_mapg_frag susp γ -∗
        susp ↦ᵥ{#3/4} InjLV (#pid, #p) -∗
        sub_susp_count_frags t v c pid Nc -∗
        visit_reached_done γ id ∗
        intransit ==∗
          visit_finished γ id ∗
          visited_map_update_finished m d γ id ∗
          sub_susp_count_frags t v c pid Nc ∗
          susp ↦ᵥ{#3/4} InjLV (#pid, #p).
  Proof.
    iIntros (t t' v c pid Nc susp p γ m d Hid Hsub)
      "Hauth #Hlg Hsusp (#Hcap & %Hle & Hinner & Hagg) [#Hreached Hintr]".
    iAssert (∀ v_outer (tind : evi_type) (vind : val) (cind : nat) (tind' : evi_type),
               ⌜sub_obj tind' vind (InjRV #susp)⌝ -∗
               visited_mapg_auth m d -∗
               lg_mapg_frag susp γ -∗
               susp ↦ᵥ{#3/4} InjLV (#pid, #p) -∗
               sub_susp_count tind vind cind pid Nc v_outer -∗
               intransit ==∗
               visit_finished γ id ∗
               visited_map_update_finished m d γ id ∗
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
          * by iDestruct (sub_susp_count_ne_injr_loc with "Hc1") as %[].
          * by iDestruct (sub_susp_count_ne_injr_loc with "Hc2") as %[].
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
               by iDestruct (sub_susp_count_ne_injL_injR_susp with "Hc") as %[].
            -- subst v''. injection Heq as ->.
               iMod (sub_susp_count_finalizes_susp id _ cind pid Nc γ susp p v_outer m d
                 with "Hauth Hlg Hsusp Hc Hreached Hintr")
                 as "(#Hfin & Hauth' & Hc' & Hsusp')".
               iModIntro. iFrame "Hfin Hauth' Hsusp'".
               iRight. iExists (InjRV (InjRV #susp)). by iFrame.
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
        simpl. iDestruct "Hinner" as (v1) "[-> Hcases]".
        destruct tind'; simpl in Hsubind; try done.
        + destruct Hsubind as (? & ? & Heq & _); discriminate.
        + destruct Hsubind as (? & [(Heq & _ & _) | (Heq & _ & Heq2)]).
          * discriminate.
          * subst. injection Heq as Heq. by apply no_fix_InjRV in Heq.
        + destruct Hsubind as (? & [Heq|Heq] & ->).
          * injection Heq as ->.
            iDestruct "Hcases" as "[H|H]".
            -- iDestruct "H" as (h) "%Heq'". destruct Heq' as [Heq' _]. discriminate.
            -- iDestruct "H" as (susp') "[%Heq' _]". discriminate.
          * injection Heq as ->.
            iDestruct "Hcases" as "[H|H]".
            -- iDestruct "H" as (h) "%Heq'". destruct Heq' as [Heq' _]. discriminate.
            -- iDestruct "H" as (susp') "[%Heq' _]". by simplify_eq. }
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
      intransit ∗
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
      ⌜sub_obj t' v (InjRV #susp)⌝ -∗
      lg_mapg_frag susp γ -∗
      visit_finished γ n -∗
      sub_susp_count_frags t v c pid Nc -∗
      susp ↦ᵥ{#(3/4)} InjLV (#pid, v') -∗
      spec_verifier tᵥ (fill K (#susp <- InjRV #h))
      ={⊤}=∗
        intransit ∗
        sub_susp_count_frags t v (c-1) pid Nc ∗
        susp ↦ᵥ{#(3/4)} InjRV #h ∗
        spec_verifier tᵥ (fill K (#())).
  Proof.
    iIntros (K tᵥ v v' t t' susp c pid Nc h γ n)
      "%Hsub #Hlg #Hfin (#Hcap & %Hle & Hinner & Hagg) Hsusp Hspec".
    iAssert (∀ v_outer (t : evi_type) (v : val) (c : nat) (t' : evi_type),
               ⌜sub_obj t' v (InjRV #susp)⌝ -∗
               sub_susp_count t v c pid Nc v_outer -∗
               susp ↦ᵥ{#3/4} InjLV (#pid, v') -∗
               spec_verifier tᵥ (fill K (#susp <- InjRV #h)) ={⊤}=∗
               ⌜1 ≤ c⌝ ∗
               intransit ∗
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
          * by iDestruct (sub_susp_count_ne_injr_loc with "Hc1") as %[].
          * by iDestruct (sub_susp_count_ne_injr_loc with "Hc2") as %[].
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
               by iDestruct (sub_susp_count_ne_injL_injR_susp with "Hc") as %[].
            -- subst v''. injection Heq as ->.
               iMod (count_update_eats_susp with "Hlg Hfin Hc Hsusp' Hspec'") as
                 "(%Hc & Hintr & Hc' & Hsusp'' & Hspec'' & Hnew)".
               iModIntro. iSplit; [iPureIntro; lia|].
               iFrame "Hintr Hsusp'' Hspec'' Hnew".
               iRight. iExists (InjRV (InjRV #susp)). by iFrame.
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
        simpl. iDestruct "Hinner'" as (v1) "[-> Hcases]".
        destruct tind'; simpl in Hsubind; try done.
        + destruct Hsubind as (? & ? & Heq & _); discriminate.
        + destruct Hsubind as (v'' & [(Heq & _ & _) | (Heq & _ & Heq2)]).
          * discriminate.
          * subst v''. injection Heq as Heq. by apply no_fix_InjRV in Heq.
        + destruct Hsubind as (v'' & [Heq|Heq] & ->).
          * injection Heq as ->.
            iDestruct "Hcases" as "[H|H]".
            -- iDestruct "H" as (h') "%Heq'". destruct Heq' as [Heq' _]. discriminate.
            -- iDestruct "H" as (susp') "[%Heq' _]". discriminate.
          * injection Heq as ->.
            iDestruct "Hcases" as "[H|H]".
            -- iDestruct "H" as (h') "%Heq'". destruct Heq' as [Heq' _]. discriminate.
            -- iDestruct "H" as (susp') "[%Heq' _]". by simplify_eq. }
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
    (* iIntros (K tᵥ v v' t t' susp c pid Nc h γ n)
      "%Hsub #Hlg #Hfin (#Hcap & %Hle & Hinner & Hagg) Hsusp Hspec".
    iAssert (∀ v_outer (t : evi_type) (v : val) (c : nat) (t' : evi_type),
               ⌜sub_obj t' v (InjRV #susp)⌝ -∗
               sub_susp_count t v c pid Nc v_outer -∗
               susp ↦ᵥ{#3/4} InjLV (#pid, v') -∗
               spec_verifier tᵥ (fill K (#susp <- InjRV #h)) ={⊤}=∗
               ⌜1 ≤ c⌝ ∗
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
          * by iDestruct (sub_susp_count_ne_injr_loc with "Hc1") as %[].
          * by iDestruct (sub_susp_count_ne_injr_loc with "Hc2") as %[].
          * iMod ("IH" $! v1 c1 t1' Hsub1 with "Hc1 Hsusp' Hspec'")
              as "(%Hc & Hc1' & Hsusp'' & Hspec'' & Hnew)".
            iModIntro. iSplit; [iPureIntro; lia|].
            iFrame "Hsusp'' Hspec'' Hnew".
            iExists (c1 - 1), c2, v1, v2.
            iSplit; [iPureIntro; split; [done|lia]|]. iFrame.
          * iMod ("IH1" $! v2 c2 t2' Hsub2 with "Hc2 Hsusp' Hspec'")
              as "(%Hc & Hc2' & Hsusp'' & Hspec'' & Hnew)".
            iModIntro. iSplit; [iPureIntro; lia|].
            iFrame "Hsusp'' Hspec'' Hnew".
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
               by iDestruct (sub_susp_count_ne_injL_injR_susp with "Hc") as %[].
            -- subst v''. injection Heq as ->.
               iMod (count_update_eats_susp with "Hlg Hfin Hc Hsusp' Hspec'") as
                 "(%Hc & Hc' & Hsusp'' & Hspec'' & Hnew)".
               iModIntro. iSplit; [iPureIntro; lia|].
               iFrame "Hsusp'' Hspec'' Hnew".
               iRight. iExists (InjRV (InjRV #susp)). by iFrame.
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
        simpl. iDestruct "Hinner'" as (v1) "[-> Hcases]".
        destruct tind'; simpl in Hsubind; try done.
        + destruct Hsubind as (? & ? & Heq & _); discriminate.
        + destruct Hsubind as (v'' & [(Heq & _ & _) | (Heq & _ & Heq2)]).
          * discriminate.
          * subst v''. injection Heq as Heq. by apply no_fix_InjRV in Heq.
        + destruct Hsubind as (v'' & [Heq|Heq] & ->).
          * injection Heq as ->.
            iDestruct "Hcases" as "[H|H]".
            -- iDestruct "H" as (h') "%Heq'". destruct Heq' as [Heq' _]. discriminate.
            -- iDestruct "H" as (susp') "[%Heq' _]". discriminate.
          * injection Heq as ->.
            iDestruct "Hcases" as "[H|H]".
            -- iDestruct "H" as (h') "%Heq'". destruct Heq' as [Heq' _]. discriminate.
            -- iDestruct "H" as (susp') "[%Heq' _]". by simplify_eq. }
    iMod ("Hlem" $! v t v c t' Hsub with "Hinner Hsusp Hspec")
      as "(%Hc & Hinner & Hsusp & Hspec & Hnew)".
    iModIntro. iFrame "Hsusp Hspec Hcap".
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
  Qed. *)

End authentikit_helpers.