From auth.prelude Require Import stdpp.
From auth.rel_logic_bin Require Import fundamental.
From auth.examples Require Import authentikit_list_security merkle.

Section semantic.
  Context `{!authG Σ}.

  Lemma wp_parse_retrieve_proof (prf: val) :
    {{{ ⌜∃ s: string, prf = #s⌝ }}}
      parse_retrieve_proof merkle_ser prf
    {{{ w, RET w;
        ⌜w = NONEV ∨ (∃ (l_s: string) (v_r: val), w = SOMEV (#l_s, v_r) ∧
    (∃ v_s: string, v_r = SOMEV #v_s ∨ v_r = NONEV))⌝ }}}.
  Proof.
    iIntros (Φ) "%HPre HPost". destruct HPre as [s ->].
    rewrite /parse_retrieve_proof. wp_pures.
    wp_apply (s_deser_sound); [done|].
    iIntros ([] Hdeser); wp_pures; last first.
    { iModIntro. iApply "HPost". by iLeft. }
    destruct! Hdeser; simplify_eq; wp_pures.
    { iModIntro. iApply "HPost". iRight.
      destruct! H2; simplify_eq. iExists _,_.
      iSplit; [done| iExists _; by iRight]. }
    destruct! H2; simplify_eq.
    destruct! H6; destruct! H7; simplify_eq.
    wp_pures.
    iModIntro. iApply "HPost". iRight. iExists _,_.
    iSplit; [done| iExists _; by iLeft].
    Unshelve. done.
  Qed.

  Definition lrel_path : kindO Σ (⋆)%kind := LRel (λ v1 v2,
    ∃ (l : list (() + ())), ⌜is_list l v1⌝ ∗ ⌜is_list l v2⌝)%I.

  Definition merkle_retrieve_ctx {Θ} (Δ : ctxO Σ Θ) : ctxO Σ (Θ ▹ ⋆ ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆))%kind :=
    auth_ctx (ext Δ lrel_path).

  Lemma refines_path Θ Δ Γ :
    ⊢ { (Θ ▹ ⋆ ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆))%kind ; merkle_retrieve_ctx Δ; Γ }
      ⊨ path ≤log≤ path : t_path.
  Proof.
    iIntros (?) "_". iIntros (??) "Hi".
    rewrite ![subst_map _ _]/=.
    wp_pures. iFrame. iModIntro.
    rewrite interp_prod_unfold.
    iExists _, _, _, _. do 2 (iSplit; [done|]).
    iSplit; last first.
    { interp_unfold!.
      iIntros (v1 v2) "!# /= (% & %Hv1 & %Hv2)".
      iIntros (??) "Hi".
      rewrite /path_pop.
      i_pures. wp_pures.
      i_bind (list_head _).
      iMod (gwp_list_head_opt ⊤ _ l () (λ w, ⌜w = $(hd_error l)⌝)%I
             with "[//] [] [$Hi //]") as (?) "[Hi ->]".
      { by iIntros "!>" (?). }
      wp_apply gwp_list_head; [done|].
      rewrite /list_tail.
      iIntros (? [[-> ->] | (d & l' & -> & ->)]) "/=".
      { i_pures. wp_pures. iFrame. rewrite interp_sum_unfold. iExists _, _. interp_unfold. eauto. }
      destruct Hv1 as (w1 & -> & Hw1), Hv2 as (w2 & -> & Hw2).
      i_pures. wp_pures. iFrame. iModIntro.
      interp_unfold.
      iExists _, _. iRight. do 2 (iSplit; [done|]).
      interp_unfold!.
      iExists _, _, _, _. do 2 (iSplit; [done|]).
      iSplit; [|iFrame "%"].
      interp_unfold.
      iExists _, _. interp_unfold. destruct d; eauto. }
    interp_unfold.
    iExists _, _, _, _. do 2 (iSplit; [done|]).
    iSplit; last first; interp_unfold!.
    { iIntros (v1 v2) "!# /= (% & %Hv1 & %Hv2)".
      iIntros (??) "Hi".
      rewrite /path_right.
      i_pures. wp_pures.
      iMod (gwp_list_cons (inr tt) l _ ⊤ () (λ w, ⌜is_list ((inr tt) :: l) w⌝)%I
             with "[//] [] [$Hi //]") as (?) "[Hi %]".
      { by iIntros "!>" (?). }
      wp_apply (gwp_list_cons (inr tt) l); [done|].
      iIntros (??). iFrame. by iExists (_ :: _). }
    iExists _, _, _, _. do 2 (iSplit; [done|]).
    iSplit; last first; interp_unfold!.
    { iIntros (v1 v2) "!# /= (% & %Hv1 & %Hv2)".
      iIntros (??) "Hi".
      rewrite /path_left.
      i_pures. wp_pures.
      iMod (gwp_list_cons (inl tt) l _ ⊤ () (λ w, ⌜is_list ((inl tt) :: l) w⌝)%I
             with "[//] [] [$Hi //]") as (?) "[Hi %]".
      { by iIntros "!>" (?). }
      wp_apply (gwp_list_cons (inl tt) l); [done|].
      iIntros (??). iFrame. by iExists (_ :: _). }
    by iExists [].
  Qed.

  Lemma wp_list_head_nil E lv s :
    {{{ ⌜is_list [] lv⌝ }}}
      list_head lv @ s; E
    {{{ RET NONEV; True }}}.
  Proof.
    iIntros (Φ a) "HΦ".
    wp_apply (gwp_list_head _ _ [] with "[//]").
    iIntros (v) "[[_ ->] | (% & % & % & _)]"; simplify_eq.
    by iApply "HΦ".
  Qed.

  (* A separate lemma for induction exclusively on the verifier for the case when the
     ideal terminates early. Here, we simply want the verifier to terminate.
   *)
  Lemma refines_retrieve_aux_empty_i (l_path: list (()+())) (l_proof: list val) (l_proof_s: list string)
    (tip_v_hash: string) (path_v proof: val) :
    is_list l_path path_v → is_list l_proof proof →
      (l_proof = (fun (x : string) => #x) <$> l_proof_s) →
      ⊢ {{{ ⌜True⌝ }}}
          retrieve_magic_verifier_aux path_v proof #tip_v_hash
        {{{ v_v, RET v_v;
          ((∃ (tree_v_hash: string), ⌜v_v = SOMEV #tree_v_hash⌝) ∨
             ⌜(v_v = NONEV)⌝) }}}%I.
  Proof.
    iIntros (is_list_v is_list_proof proof_str).
    iIntros (Φ) "!# _ HPost".
    iInduction (l_path) as [|h t_path] "IH"
      forall (Φ path_v l_proof l_proof_s proof is_list_v is_list_proof proof_str) "HPost".
    - wp_rec. wp_pures. wp_rec.
      wp_apply (wp_list_head_nil); [done|].
      iIntros (_). wp_pures.
      destruct l_proof.
      + wp_apply (gwp_list_head_nil); [done|].
        iIntros (_). wp_pures.
        iModIntro. iApply "HPost". iLeft.
        by iExists _.
      + wp_apply (gwp_list_head_cons); [done|].
        iIntros (_). wp_pures.
        wp_apply (gwp_list_tail); [done|].
        iIntros (??). wp_pures.
        iModIntro. iApply "HPost". by iRight.
    - wp_rec. wp_pures. wp_rec.
      wp_apply (gwp_list_head_cons); [done|].
      iIntros (_). wp_pures.
      wp_apply (gwp_list_tail); [done|].
      iIntros (path_tail_v is_list_tail_path_v).
      wp_pures.
      destruct l_proof.
      { wp_apply (gwp_list_head_nil); [done|].
        iIntros (_). wp_pures.
        iModIntro. iApply "HPost". by iRight. }
      destruct l_proof_s; [done|].
      wp_apply (gwp_list_head_cons); [done|].
      iIntros (_). wp_pures.
      wp_apply (gwp_list_tail); [done|].
      iIntros (proof_tail is_list_ptail).
      wp_pures.
      wp_bind (retrieve_magic_verifier_aux _ _ _).
      iApply ("IH" with "[//] [//] [] [HPost]").
      { iPureIntro. simplify_list_eq. done. }
      iNext.
      iIntros (v_v) "[(% & ->)|->]"; last first.
      { wp_pures. iModIntro.
        iApply "HPost". by iRight. }
      wp_pures.
      destruct h.
      + wp_pures.
        wp_apply s_ser_spec.
        { iExists _. iRight. iSplit; [done|].
          iExists _,_. iSplit; [done|].
          inversion proof_str.
          iSplit; by iExists _. }
        iIntros (s0 Hser).
        wp_apply wp_hash; [done|]. iIntros "Hashs".
        wp_pures. iModIntro.
        iApply "HPost". iFrame.
        iLeft. by iExists _.
      + wp_pures.
        wp_apply s_ser_spec.
        { iExists _. iRight. iSplit; [done|].
          iExists _,_. iSplit; [done|].
          inversion proof_str.
          iSplit; by iExists _. }
        iIntros (s0 Hser).
        wp_apply wp_hash; [done|]. iIntros "Hashs".
        wp_pures. iModIntro.
        iApply "HPost". iFrame.
        iLeft. by iExists _.
  Qed.

  (* This lemma simply unfolds the t_tree_auth definition.
     We state this separately to speed-up compilation.
   *)
  Lemma t_tree_auth_unfold Θ (Δ : ctxO Σ Θ) v1 v2 :
    ⟦ t_tree_auth ⟧ (merkle_retrieve_ctx Δ) v1 v2 ≡
      (∃ (a1 : val) (t : evi_type) (s1 : string),
          ⌜s_is_ser (evi_type_ser t) a1 s1⌝ ∗ ⌜v1 = #(hash s1)⌝ ∗
          ▷ (lrel_sum lrel_string
                   (lrel_prod
                      (⟦ t_tree_auth ⟧ (merkle_retrieve_ctx Δ))
                      (⟦ t_tree_auth ⟧ (merkle_retrieve_ctx Δ)))) a1 v2
          ∗ hashed s1)%I.
  Proof.
    rewrite interp_unseal.
    rewrite /lrel_car /=.
    do 9 f_equiv.
    epose (f := (λne A : lrelC Σ, lrel_sum lrel_string (lrel_prod (lrel_auth A) (lrel_auth A)))
             : kindO Σ ⋆ -n> kindO Σ ⋆).
    replace (interp_rec _) with (interp_rec f) at 1; last first.
    { rewrite /f //=. }
    setoid_rewrite (interp_rec_unfold f).
    done.
  Qed.

  (* This lemma gives the postconditions for the case when the verifier is given
     a proof that claims the retrieve query returns some result.
     This assumes that path's length is equal to the tree's height.

     There are three cases from here.
     1) The verifier accepts the proof, the ideal returns some tip.
        If tree_i_hash equals tree_v_hash, then tip_i should be equal to tip_v.
     2) The verifier accepts the proof, the ideal returns none.
        Then the final hashes shouldn't be equal.
     3) The verifier doesn't accept the proof.
   *)
  Lemma refines_retrieve_aux_some Θ (Δ : ctxO Σ Θ) :
    ∀  (l_path: list (()+())) ti Ki (l_proof: list val) (l_proof_s: list string)
      (tip_v_hash tip_v tree_i_hash: string)
      (path_v path_i proof tree_i: val),
      is_list l_path path_v → is_list l_path path_i →
      is_list l_proof proof →
      (l_proof = (fun (x : string) => #x) <$> l_proof_s) →
      ⟦ t_tree_auth ⟧ (merkle_retrieve_ctx Δ) #tree_i_hash tree_i -∗
      ⟦ t_tree_auth ⟧ (merkle_retrieve_ctx Δ) #tip_v_hash (InjLV #tip_v) -∗
      {{{ spec_ideal ti (fill Ki (retrieve_ideal_aux path_i tree_i)) }}}
        retrieve_magic_verifier_aux path_v proof #tip_v_hash
      {{{ v_v, RET v_v;
          (∃ v_i: val,
              ((∃ (tip_i tree_v_hash: string), (* Case 1 *)
                   ⌜v_v = SOMEV #tree_v_hash ∧ v_i = SOMEV #tip_i⌝ ∗
                     ((⌜tree_i_hash = tree_v_hash⌝ → ⌜tip_i = tip_v⌝) ∨
                        (⌜tree_i_hash ≠ tree_v_hash⌝))) ∨
                 (∃ (tree_v_hash: string), (* Case 2 *)
                     ⌜v_v = SOMEV #tree_v_hash ∧ v_i = NONEV ∧ tree_i_hash ≠ tree_v_hash⌝))
                ∗ spec_ideal ti (fill Ki v_i)) ∨
            (∃ e_i: expr, (* Case 3 *)
                ⌜(v_v = NONEV)⌝ ∗ spec_ideal ti (fill Ki e_i)) }}}%I.
  Proof.
    iIntros (l_path).
    iInduction (l_path) as [|h t_path] "IH".
    - iIntros (ti Ki l_proof l_proof_s tip_v_hash tip_v tree_i_hash path_v path_i proof tree_i
              is_list_v is_list_i is_list_proof proof_str) "#HTree #HTip".
      iIntros (Φ) "!# Hi HPost".
      wp_rec.
      iEval (rewrite t_tree_auth_unfold) in "HTip".
      iDestruct "HTip" as (tip_v_val t_tip tip_v_hashed Hser_tip ->) "(HTip & #Hash_tip)".
      wp_pure.
      iDestruct "HTip" as (tip_v_sum tip_i_sum) "[(%H1 & %H2 & %HLeaf)|(H1 & %H2 & #HNode)]"; simplify_eq.
      iEval (rewrite t_tree_auth_unfold) in "HTree".
      iDestruct "HTree" as (tree_i_val t_tree tree_i_hashed Hser_tree [= ->]) "(HTree & #Hash_tree)".
      destruct HLeaf as [? [H1 H2]]. simplify_eq.
      destruct t_tip; destruct! Hser_tip; simplify_eq.
      destruct t_tip1; destruct! H2; simplify_eq.
      wp_pures. wp_rec. wp_pures.
      wp_apply (gwp_list_head_nil); [done|].
      iIntros (_). wp_pures.
      destruct l_proof_s; simpl in is_list_proof; last first.
      { (* proof is longer than the path, the verifier rejects this *)
        destruct is_list_proof as [? [-> ?]].
        wp_rec. wp_pures. wp_rec. wp_pures.
        iApply "HPost". iModIntro.
        iRight. iExists _. iFrame. done. }

      i_rec ti.
      i_pures.
      simplify_eq. wp_rec. wp_pures.
      i_rec ti.
      i_bind (list_head _).
      iMod (gwp_list_head_nil ⊤ path_i () (λ w, ⌜w=NONEV⌝)%I
             with "[//] [] [$Hi //]") as (v) "[Hi ->]".
      { by iIntros "!>" (?). }
      iSimpl in "Hi". i_pures.

      iDestruct "HTree" as (tree_i_sum ?) "[(-> & -> & %HLeaf)|(-> & -> & #HNode)]".
      * i_pures. destruct! HLeaf; simplify_eq.
        destruct t_tree; destruct! Hser_tree; simplify_eq.
        destruct t_tree1; destruct! H4; simplify_eq.
        iModIntro.
        iApply "HPost". iFrame.
        iLeft. iLeft. iExists H1,(hash (inl_ser_str (string_ser_str H))).
        iSplit; [done|].
        destruct (decide (collision (inl_ser_str (string_ser_str H1))
                            (inl_ser_str (string_ser_str H)))) as [|Hnc%not_collision].
        { iExFalso. by iApply (hashes_auth.hashed_inj_or_coll with "Hash_tree Hash_tip"). }
        destruct Hnc as [Hnc | ?]; simplify_eq.
        { by iLeft. }
        by iRight.
      * (* ideal's tree's height is longer than the path, case 2 *)
        i_pures. iModIntro.
        iApply "HPost". iFrame.
        simplify_eq.
        iLeft. iRight.
        iExists (hash (inl_ser_str (string_ser_str H))).
        iSplit; [done|]. iSplit; [done|].
        destruct t_tree; destruct! Hser_tree; simplify_eq.
        destruct (decide (collision (inr_ser_str H2) (inl_ser_str (string_ser_str H)))) as [|Hnc%not_collision].
        { iExFalso. by iApply (hashes_auth.hashed_inj_or_coll with "Hash_tree Hash_tip"). }
        destruct Hnc as [Hnc | ?]; [|done]. simplify_eq.
      
    - iIntros (ti Ki l_proof l_proof_s tip_v_hash tip_v tree_i_hash path_v path_i proof tree_i
              is_list_v is_list_i is_list_proof proof_str) "#HTree #HTip".
      iIntros (Φ) "!# Hi HPost".

      wp_rec. wp_pures. wp_rec.
      wp_apply (gwp_list_head_cons); [done|].
      iIntros (_). wp_pures.
      wp_apply (gwp_list_tail); [done|].
      iIntros (path_tail_v is_list_tail_path_v). wp_pures.
      destruct l_proof.
      { wp_apply gwp_list_head_nil; [done|].
        iIntros (_). wp_pures.
        iApply "HPost". iRight. iExists _.
        iFrame. done. }
      destruct l_proof_s; [done|].

      wp_apply gwp_list_head_cons; [done|].
      iIntros (_). wp_pures.
      wp_apply gwp_list_tail; [done|].
      iIntros (proof_tail is_list_ptail).

      i_rec ti. i_pures. i_rec ti.
      i_bind (list_head _).
      iMod (gwp_list_head_cons ⊤ path_i h t_path () (λ w, ⌜w=SOMEV (inject h)⌝)%I
             with "[//] [] [$Hi //]") as (?) "[Hi ->] /=".
      { by iIntros "!>" (?). }
      i_pures.
      i_bind (list_tail _).
      iMod (gwp_list_tail ⊤ path_i (h::t_path) () (λ w, ⌜is_list t_path w⌝)%I
             with "[//] [] [$Hi //]") as (path_tail_i) "[Hi %is_list_tail_path_i] /=".
      { by iIntros "!>" (?). }
      i_pures.
      iEval (rewrite t_tree_auth_unfold) in "HTree".
      iDestruct "HTree" as (tree_i_val t_tree tree_i_hashed Hser_tree Htree_i_hash) "(HTree & #Hash_tree)".
      wp_pure.
      iDestruct "HTree" as (tree_v_sum tree_i_sum) "[(-> & -> & #HLeaf)|(-> & -> & #HNode)]".
      + (* ideal's tree's height is shorter than the path, case 2 *)
        i_pures. wp_pures.

        wp_bind (retrieve_magic_verifier_aux _ _ _).
        iApply (refines_retrieve_aux_empty_i  with "[//] [HPost Hi]").
        { done. }
        { done. }
        { simpl. instantiate (1 := l_proof_s). simplify_list_eq. done. }
        iNext.

        iIntros (?) "[(% & ->)|->]"; wp_pures; last first.
        { iApply "HPost". iRight. iExists _. by iFrame. }
        destruct h; wp_pures. (* Reasoning about whether the path is left or right *)
        * wp_apply s_ser_spec.
          { iExists _. iRight. iSplit; [done|].
            iExists _,_. iSplit; [done|].
            inversion proof_str.
            iSplit; by iExists _. }
          iIntros (s0 Hser).
          wp_apply wp_hash; [done|].
          iIntros "Hashs". wp_pures.
          iModIntro.
          iApply "HPost".
          iFrame. iLeft. iRight.
          iExists (hash s0).
          do 2 (iSplit; [done|]). simplify_eq.
          destruct! Hser; simplify_eq.
          destruct! H2; simplify_eq.
          destruct! H5; destruct! H6; simplify_eq.
          destruct t_tree; destruct! Hser_tree; simplify_eq.
          destruct (decide (collision (inl_ser_str H3)
                              (inr_ser_str (prod_ser_str (string_ser_str H) (string_ser_str H1)))))
            as [|Hnc%not_collision].
          { iExFalso. by iApply (hashes_auth.hashed_inj_or_coll with "Hash_tree Hashs"). }
          destruct Hnc as [Hnc | ?]; [|done]. simplify_eq.
        * wp_apply s_ser_spec.
          { iExists _. iRight. iSplit; [done|].
            iExists _,_. iSplit; [done|].
            inversion proof_str.
            iSplit; by iExists _. }
          iIntros (s0 Hser).
          wp_apply wp_hash; [done|].
          iIntros "Hashs". wp_pures.
          iModIntro.
          iApply "HPost".
          iFrame. iLeft. iRight.
          iExists (hash s0).
          do 2 (iSplit; [done|]). simplify_eq.
          destruct! Hser; simplify_eq.
          destruct! H2; simplify_eq.
          destruct! H5; destruct! H6; simplify_eq.
          destruct t_tree; destruct! Hser_tree; simplify_eq.
          destruct (decide (collision (inl_ser_str H3)
                              (inr_ser_str (prod_ser_str (string_ser_str H1) (string_ser_str H2)))))
            as [|Hnc%not_collision].
          { iExFalso. by iApply (hashes_auth.hashed_inj_or_coll with "Hash_tree Hashs"). }
          destruct Hnc as [Hnc | ?]; [|done]. simplify_eq.

      + wp_pures. i_pures.

        iDestruct "HNode" as (child1_v child1_i child2_v child2_i) "(-> & -> & #HChild1Rec & #HChild2Rec)".
        destruct h; i_pures. (* Reasoning about whether the path is left or right *)
        * wp_bind (retrieve_magic_verifier_aux _ _ _).
          iEval (rewrite t_tree_auth_unfold) in "HChild1Rec".
          iDestruct "HChild1Rec" as (child1_v_val t_child1 child1_v_string Hser_child ->) "(HChild1 & #Hs1)".

          iApply ("IH"  with "[] [//] [//] [] [] [] Hi").
          { done. }
          { iPureIntro. simpl. instantiate (1 := l_proof_s). inversion proof_str. done. }
          { iEval (rewrite t_tree_auth_unfold). iExists _, _, _. eauto. }
          { done. }

          iNext.
          iIntros (v_v) "HPost1".
          iDestruct "HPost1" as "[(% & [HPost1|HPost1] & Hi)|(% & -> & Hi)]"; last first.
          { (* Case 3 from recursive calls, should finally be case 3 *)
            wp_pures.
            iModIntro.
            iApply "HPost". iRight. iExists _. iFrame. done. }

          { (* Case 2 from recursive calls, should finally be case 2 *)
            iDestruct "HPost1" as (tree_v_hash) "(-> & -> & %Hneq)". 
            wp_pures.
            wp_apply s_ser_spec.
            { iExists _. iRight. iSplit; [done|].
              iExists _,_. iSplit; [done|].
              inversion proof_str.
              iSplit; by iExists _. }
            iIntros (s0 Hser).
            wp_apply wp_hash; [done|].
            iIntros "Hashs". wp_pures.
            iModIntro.
            iApply "HPost". iFrame.
            iLeft. iRight. iExists _.
            iSplit; [done|]. iSplit; [done|].
            destruct t_tree; destruct! Hser_tree; simplify_eq.
            destruct t_tree2; destruct! H2; simplify_eq.
            destruct! Hser; simplify_eq.
            destruct! H7; simplify_eq.
            destruct (decide (collision (inr_ser_str (prod_ser_str H0 H3))
                                (inr_ser_str (prod_ser_str H1 H8)))) as [|Hnc%not_collision].
            { iExFalso. by iApply (hashes_auth.hashed_inj_or_coll with "Hash_tree Hashs"). }
            iPureIntro.
            destruct Hnc as [Hnc | ?]; [|done].
            injection Hnc. destruct Hnc.
            intros Hnc. apply prod_ser_str_inj in Hnc.
            destruct Hnc as [-> ->].
            destruct t_tree2_1; destruct! H5; simplify_eq.
            destruct! H10; simplify_eq. }

          (* Case 1 from recursive calls, should finally be case 1 *)
          iDestruct "HPost1" as (tip_i tree_v_hash) "((-> & ->) & Hhashcomp)".
          wp_pures.
          wp_apply s_ser_spec.
          { iExists _. iRight. iSplit; [done|].
            iExists _,_. iSplit; [done|].
            inversion proof_str.
            iSplit; by iExists _. }
          iIntros (s0 Hser).
          wp_apply wp_hash; [done|].
          iIntros "Hashs". wp_pures.
          iModIntro.
          iApply "HPost". iFrame.
          iLeft. iLeft. iExists _, _.
          iSplit; [done|].

          iDestruct "Hhashcomp" as "[Heq|%Hneq]"; last first.
          { iRight. simplify_eq.
            destruct (decide (collision tree_i_hashed s0)) as [|Hnc%not_collision].
            { iExFalso. by iApply (hashes_auth.hashed_inj_or_coll with "Hash_tree Hashs"). }
            iPureIntro.
            destruct Hnc as [Hnc | ?]; [|done].
            destruct! Hser; simplify_eq.
            destruct t_tree; destruct! Hser_tree; simplify_eq.
            destruct t_tree2; destruct! H4; simplify_eq.
            destruct! H2; simplify_eq.
            destruct t_tree2_1; destruct! H6; simplify_eq.
            destruct! H9; simplify_eq.
          }

          simplify_eq. iLeft. iIntros (HTreeEq). iApply "Heq".
          destruct (decide (collision tree_i_hashed s0)) as [|Hnc%not_collision].
          { iExFalso. by iApply (hashes_auth.hashed_inj_or_coll with "Hash_tree Hashs"). }
          iPureIntro.
          destruct! Hser; simplify_eq.
          destruct! H2; simplify_eq.
          destruct! H5; destruct! H6; simplify_eq.
          destruct t_tree; destruct! Hser_tree; simplify_eq.
          destruct t_tree2; destruct! H4; simplify_eq.
          destruct t_tree2_1; destruct! H7; simplify_eq.
          destruct Hnc as [Hnc | Hnc]; [|done].
          inversion Hnc. simplify_eq. done.

        * wp_bind (retrieve_magic_verifier_aux _ _ _).
          iEval (rewrite t_tree_auth_unfold) in "HChild2Rec".
          iDestruct "HChild2Rec" as (child2_v_val t_child2 child2_v_string Hser_child ->) "(HChild2 & #Hs1)".

          iApply ("IH" with "[] [//] [//] [] [] [] Hi").
          { done. }
          { iPureIntro. simpl. simplify_list_eq. done. }
          { iEval (rewrite t_tree_auth_unfold). iExists  _, _, _. eauto. }
          { done. }

          iNext.
          iIntros (v_v) "HPost1".
          iDestruct "HPost1" as "[(% & [HPost1|HPost1] & Hi)|(% & -> & Hi)]"; last first.
          { wp_pures.
            iModIntro.
            iApply "HPost". iRight. iExists _. iFrame. done. }

          { iDestruct "HPost1" as (tree_v_hash) "(-> & -> & %Hneq)".
            wp_pures.
            wp_apply s_ser_spec.
            { iExists _. iRight. iSplit; [done|].
              iExists _,_. iSplit; [done|].
              inversion proof_str.
              iSplit; by iExists _. }
            iIntros (s0 Hser).
            wp_apply wp_hash; [done|].
            iIntros "Hashs". wp_pures.
            iModIntro.
            iApply "HPost". iFrame.
            iLeft. iRight. iExists _.
            iSplit; [done|]. iSplit; [done|].
            destruct t_tree; destruct! Hser_tree; simplify_eq.
            destruct t_tree2; destruct! H2; simplify_eq.
            destruct! Hser; simplify_eq.
            destruct! H7; simplify_eq.
            destruct (decide (collision (inr_ser_str (prod_ser_str H0 H3))
                                (inr_ser_str (prod_ser_str H2 H8)))) as [|Hnc%not_collision].
            { iExFalso. by iApply (hashes_auth.hashed_inj_or_coll with "Hash_tree Hashs"). }
            iPureIntro.
            destruct Hnc as [Hnc | ?]; [|done].
            injection Hnc. destruct Hnc.
            intros Hnc. apply prod_ser_str_inj in Hnc.
            destruct Hnc as [-> ->].
            destruct t_tree2_2; destruct! H6; simplify_eq.
            destruct! H11; simplify_eq. }

          iDestruct "HPost1" as (tip_i tree_v_hash) "((-> & ->) & Hhashcomp)".
          wp_pures.
          wp_apply s_ser_spec.
          { iExists _. iRight. iSplit; [done|].
            iExists _,_. iSplit; [done|].
            inversion proof_str.
            iSplit; by iExists _. }
          iIntros (s0 Hser).
          wp_apply wp_hash; [done|].
          iIntros "Hashs". wp_pures.
          iModIntro.
          iApply "HPost". iFrame.
          iLeft. iLeft. iExists _, _.
          iSplit; [done|].

          iDestruct "Hhashcomp" as "[Heq|%Hneq]"; last first.
          { iRight. simplify_eq.
            destruct (decide (collision tree_i_hashed s0)) as [|Hnc%not_collision].
            { iExFalso. by iApply (hashes_auth.hashed_inj_or_coll with "Hash_tree Hashs"). }
            iPureIntro.
            destruct Hnc as [Hnc | ?]; [|done].
            destruct! Hser; simplify_eq.
            destruct t_tree; destruct! Hser_tree; simplify_eq.
            destruct t_tree2; destruct! H4; simplify_eq.
            destruct! H2; simplify_eq.
            destruct t_tree2_2; destruct! H7; simplify_eq.
            destruct! H10; simplify_eq.
          }

          simplify_eq. iLeft. iIntros (HTreeEq). iApply "Heq".
          destruct (decide (collision tree_i_hashed s0)) as [|Hnc%not_collision].
          { iExFalso. by iApply (hashes_auth.hashed_inj_or_coll with "Hash_tree Hashs"). }
          iPureIntro.

          destruct! Hser; simplify_eq.
          destruct! H2; simplify_eq.
          destruct! H5; destruct! H6; simplify_eq.
          destruct t_tree; destruct! Hser_tree; simplify_eq.
          destruct t_tree2; destruct! H4; simplify_eq.
          destruct t_tree2_2; destruct! H8; simplify_eq.
          destruct Hnc as [Hnc | Hnc]; [|done].
          inversion Hnc. simplify_eq. done.
  Qed.

  (* This lemma gives the postconditions for the case when the verifier is given
     a proof that claims the retrieve query doesn't return some result.
     This assumes that path's length is shorter than the tree's height.
     The proof is structurally a quite similar to the previous one.

     There are three cases from here.
     1) The verifier accepts the proof, the ideal returns none.
        tree_i_hash may or may not be equal to tree_v_hash.
     2) The verifier accepts the proof, the ideal returns something.
        Then the final hashes shouldn't be equal.
     3) The verifier doesn't accept the proof.
   *)
  Lemma refines_retrieve_aux_none_short Θ (Δ : ctxO Σ Θ) :
    ∀ ti Ki (l_path: list (()+())) (l_proof: list val) (l_proof_s: list string)
      (last_string tree_i_hash: string) (path_v path_i proof tree_i v1 v2: val),
      is_list l_path path_v → is_list l_path path_i →
      is_list l_proof proof →
      (l_proof = (fun (x : string) => #x) <$> l_proof_s) →
      s_is_ser (sum_serialization string_serialization
                  (prod_serialization string_serialization string_serialization))
        (InjRV (v1, v2)) last_string →
      hashed last_string -∗
      ⟦ t_tree_auth ⟧ (merkle_retrieve_ctx Δ) #tree_i_hash tree_i -∗
      {{{ spec_ideal ti (fill Ki (retrieve_ideal_aux path_i tree_i)) }}}
        retrieve_magic_verifier_aux path_v proof #(hash last_string)
      {{{ v_v, RET v_v;
          (∃ (tree_v_hash: string) (v_i: val),
              ⌜v_v = SOMEV #tree_v_hash⌝ ∗
                ⌜(v_i = NONEV ∧ (* Case 1 *)
                     (tree_i_hash = tree_v_hash ∨
                       tree_i_hash ≠ tree_v_hash)) ∨
                   ∃ tip: string, v_i = SOMEV #tip ∧ tree_i_hash ≠ tree_v_hash⌝ (* Case 2 *)
                ∗ spec_ideal ti (fill Ki v_i)) ∨
            (∃ e_i: expr,       (* Case 3 *)
                ⌜(v_v = NONEV)⌝ ∗ spec_ideal ti (fill Ki e_i)) }}}%I.
  Proof.
    iIntros (????????????? is_list_v is_list_i is_list_proof proof_str Hser_val) "#Hash_tip #HTree".
    iIntros (Φ) "!# Hi HPost".
    iInduction (l_path) as [|h t_path] "IH"
                             forall (Φ path_v path_i l_proof l_proof_s proof tree_i tree_i_hash
                                       is_list_v is_list_i is_list_proof proof_str) "Hi HPost HTree".
    - iEval (rewrite t_tree_auth_unfold) in "HTree".
      iDestruct "HTree" as (tree_v_val t_tree tree_v_hashed Hser_tree HtreeiHash) "(HTree & #Hash_tree)".
      wp_rec. wp_pures. wp_rec.
      wp_apply (gwp_list_head_nil); [done|].
      iIntros (_). wp_pures.
      destruct l_proof_s; simpl in is_list_proof.
      + i_rec ti. i_pures. i_rec ti. simplify_eq.

        i_bind (list_head _).
        iMod (gwp_list_head_nil ⊤ path_i () (λ w, ⌜w=NONEV⌝)%I
               with "[//] [] [$Hi //]") as (v) "[Hi ->]".
        { by iIntros "!>" (?). }
        iSimpl in "Hi". simplify_eq.
        wp_apply (gwp_list_head_nil); [done |].
        iIntros (_). wp_pures.

        iDestruct "HTree" as (tree_v_sum tree_i_sum) "[(-> & -> & %HLeaf)|(-> & -> & #HNode)]".
        * i_pures. destruct! HLeaf; simplify_eq.
          destruct t_tree; destruct! Hser_tree; simplify_eq.
          destruct t_tree1; destruct! H3; simplify_eq.
          iModIntro.
          iApply "HPost". iFrame.
          iLeft. iExists _. iSplit; [done|].
          iRight. iExists _. iSplit; [done|].
          destruct! Hser_val; simplify_eq.
          destruct (decide (collision (inl_ser_str (string_ser_str H0))
                              (inr_ser_str H2))) as [|Hnc%not_collision].
          { iExFalso. by iApply (hashes_auth.hashed_inj_or_coll with "Hash_tree Hash_tip"). }
          destruct Hnc as [Hnc | ?]; simplify_eq.
          done.

        * i_pures. iModIntro.
          iApply "HPost". iFrame.
          iLeft. iExists _. iSplit; [done|].
          iLeft. iSplit; [done|].
          destruct (decide (collision tree_v_hashed last_string)) as [|Hnc%not_collision].
          { iExFalso. by iApply (hashes_auth.hashed_inj_or_coll with "Hash_tree Hash_tip"). }
          destruct Hnc as [Hnc | ?]; simplify_eq; eauto.

      + simplify_eq. destruct is_list_proof as [? [-> ?]].

        wp_rec. wp_pures. wp_rec. wp_pures.
        iApply "HPost". iModIntro.
        iRight. iExists _. iFrame. done.

    - wp_rec. wp_pures. wp_rec.
      wp_apply (gwp_list_head_cons); [done|].
      iIntros (_). wp_pures.
      wp_apply (gwp_list_tail); [done|].
      iIntros (path_tail_v is_list_tail_path_v). wp_pures.
      destruct l_proof.
      { wp_apply gwp_list_head_nil; [done|].
        iIntros (_). wp_pures.
        iApply "HPost". iRight. iExists _.
        iFrame. done. }
      destruct l_proof_s; [done|].

      wp_apply gwp_list_head_cons; [done|].
      iIntros (_). wp_pures.
      wp_apply gwp_list_tail; [done|].
      iIntros (proof_tail is_list_ptail).

      i_rec ti. i_pures. i_rec ti.

      i_bind (list_head _).
      iMod (gwp_list_head_cons ⊤ path_i h t_path () (λ w, ⌜w=SOMEV (inject h)⌝)%I
             with "[//] [] [$Hi //]") as (?) "[Hi ->]".
      { by iIntros "!>" (?). }
      iSimpl in "Hi". i_pures.
      i_bind (list_tail _).
      iMod (gwp_list_tail ⊤ path_i (h::t_path) () (λ w, ⌜is_list t_path w⌝)%I
             with "[//] [] [$Hi //]") as (path_tail_i) "[Hi %is_list_tail_path_i]".
      { by iIntros "!>" (?). }
      iSimpl in "Hi". i_pures.
      iEval (rewrite t_tree_auth_unfold) in "HTree".
      iDestruct "HTree" as (tree_i_val t_tree tree_i_hashed Hser_tree Htree_i_hash) "(HTree & #Hash_tree)".
      wp_pure.
      iDestruct "HTree" as (tree_i_sum ?) "[(-> & -> & #HLeaf)|(-> & -> & #HNode)]".
      + i_pures. wp_pures.

        wp_bind (retrieve_magic_verifier_aux _ _ _).
        iApply (refines_retrieve_aux_empty_i  with "[//] [HPost Hi]").
        { done. }
        { done. }
        { simpl. instantiate (1 := l_proof_s). simplify_list_eq. done. }
        iNext.

        iIntros (?) "[(% & ->)|->]"; wp_pures; last first.
        { iApply "HPost". iRight. iExists _. by iFrame. }
        destruct h; wp_pures.
        * wp_apply s_ser_spec.
          { iExists _. iRight. iSplit; [done|].
            iExists _,_. iSplit; [done|].
            inversion proof_str.
            iSplit; by iExists _. }
          iIntros (s0 Hser).
          wp_apply wp_hash; [done|].
          iIntros "Hashs". wp_pures.
          iModIntro.
          iApply "HPost".
          iFrame. iLeft. iExists _.
          iSplit; [done|]. iLeft.
          iSplit; [done|]. simplify_eq.
          destruct (decide (collision tree_i_hashed s0)) as [|Hnc%not_collision].
          { iExFalso. by iApply (hashes_auth.hashed_inj_or_coll with "Hash_tree Hashs"). }
          destruct Hnc as [Hnc | ?]; simplify_eq.
          { by iLeft. } { by iRight. }

        * wp_apply s_ser_spec.
          { iExists _. iRight. iSplit; [done|].
            iExists _,_. iSplit; [done|].
            inversion proof_str.
            iSplit; by iExists _. }
          iIntros (s0 Hser).
          wp_apply wp_hash; [done|].
          iIntros "Hashs". wp_pures.
          iModIntro.
          iApply "HPost".
          iFrame. iLeft. iExists _.
          iSplit; [done|]. iLeft.
          iSplit; [done|]. simplify_eq.
          destruct (decide (collision tree_i_hashed s0)) as [|Hnc%not_collision].
          { iExFalso. by iApply (hashes_auth.hashed_inj_or_coll with "Hash_tree Hashs"). }
          destruct Hnc as [Hnc | ?]; simplify_eq.
          { by iLeft. } { by iRight. }

      + wp_pures. i_pures.
        iDestruct "HNode" as (child1_v child1_i child2_v child2_i) "(-> & -> & #HChild1Rec & #HChild2Rec)".
        destruct h; i_pures.
        * wp_bind (retrieve_magic_verifier_aux _ _ _).
          iEval (rewrite t_tree_auth_unfold) in "HChild1Rec".
          iDestruct "HChild1Rec" as (child1_v_val t_child1 child1_v_string Hser_child ->) "(HChild1 & #Hs1)".
          iApply ("IH" with "[] [//] [//] [] Hi [HPost] []").
          { done. }
          { iPureIntro. simpl. instantiate (1 := l_proof_s). simplify_list_eq. done. }
          2 : { iModIntro. iEval (rewrite t_tree_auth_unfold). iExists _, _, _. eauto. }
          iNext.
          iIntros (v_v) "HPost1".
          iDestruct "HPost1" as "[(% & % & -> & [HPost1|HPost1] & Hi)|(% & -> & Hi)]"; last first.
          { wp_pures.
            iModIntro.
            iApply "HPost". iRight. iExists _. iFrame. done. }

          { iDestruct "HPost1" as "(% & -> & %Hneq)".
            wp_pures.
            wp_apply s_ser_spec.
            { iExists _. iRight. iSplit; [done|].
              iExists _,_. iSplit; [done|].
              inversion proof_str.
              iSplit; by iExists _. }
            iIntros (s0 Hser).
            wp_apply wp_hash; [done|].
            iIntros "Hashs". wp_pures.
            iModIntro.
            iApply "HPost". iFrame.
            iLeft. iExists _.
            iSplit; [done|]. iRight.
            iExists _. iSplit; [done|].
            destruct t_tree; destruct! Hser_tree; simplify_eq.
            destruct t_tree2; destruct! H2; simplify_eq.
            destruct t_tree2_1; destruct! H5; simplify_eq.
            destruct! Hser; simplify_eq.
            destruct! H4; simplify_eq.
            destruct! H8; simplify_eq.
            destruct (decide (collision (inr_ser_str (prod_ser_str (string_ser_str (hash child1_v_string)) H3))
                                (inr_ser_str (prod_ser_str (string_ser_str H) H5)))) as [|Hnc%not_collision].
            { iExFalso. by iApply (hashes_auth.hashed_inj_or_coll with "Hash_tree Hashs"). }
            destruct Hnc as [Hnc | Hnc]; simplify_eq. done. }

          iDestruct "HPost1" as "(-> & [%Heq|%Hneq])".
          { wp_pures.
            wp_apply s_ser_spec.
            { iExists _. iRight. iSplit; [done|].
              iExists _,_. iSplit; [done|].
              inversion proof_str.
              iSplit; by iExists _. }
            iIntros (s0 Hser).
            wp_apply wp_hash; [done|].
            iIntros "Hashs". wp_pures.
            iModIntro.
            iApply "HPost". iFrame.
            iLeft. iExists _. iSplit; [done|].
            iLeft. iSplit; [done|].
            simplify_eq.
            destruct (decide (collision tree_i_hashed s0)) as [|Hnc%not_collision].
            { iExFalso. by iApply (hashes_auth.hashed_inj_or_coll with "Hash_tree Hashs"). }
            destruct Hnc as [Hnc | Hnc]; simplify_eq; eauto. }

          { wp_pures.
            wp_apply s_ser_spec.
            { iExists _. iRight. iSplit; [done|].
              iExists _,_. iSplit; [done|].
              inversion proof_str.
              iSplit; by iExists _. }
            iIntros (s0 Hser).
            wp_apply wp_hash; [done|].
            iIntros "Hashs". wp_pures.
            iModIntro.
            iApply "HPost". iFrame.
            iLeft. iExists _. iSplit; [done|].
            iLeft. iSplit; [done|].
            simplify_eq.
            destruct (decide (collision tree_i_hashed s0)) as [|Hnc%not_collision].
            { iExFalso. by iApply (hashes_auth.hashed_inj_or_coll with "Hash_tree Hashs"). }
            destruct Hnc as [Hnc | Hnc]; simplify_eq; eauto. }

        * wp_bind (retrieve_magic_verifier_aux _ _ _).
          iEval (rewrite t_tree_auth_unfold) in "HChild2Rec".
          iDestruct "HChild2Rec" as (child2_v_val t_child2 child2_v_string Hser_child ->) "(HChild2 & #Hs1)".

          iApply ("IH" with "[] [//] [//] [] Hi [HPost]").
          { done. }
          { iPureIntro. simpl. instantiate (1 := l_proof_s). simplify_list_eq. done. }
          2 : { iModIntro. iEval (rewrite t_tree_auth_unfold). iExists _, _, _. eauto. }

          iNext.
          iIntros (v_v) "HPost1".
          iDestruct "HPost1" as "[(% & % & -> & [HPost1|HPost1] & Hi)|(% & -> & Hi)]"; last first.
          { wp_pures.
            iModIntro.
            iApply "HPost". iRight. iExists _. iFrame. done. }

          { iDestruct "HPost1" as "(% & -> & %Hneq)".
            wp_pures.
            wp_apply s_ser_spec.
            { iExists _. iRight. iSplit; [done|].
              iExists _,_. iSplit; [done|].
              inversion proof_str.
              iSplit; by iExists _. }
            iIntros (s0 Hser).
            wp_apply wp_hash; [done|].
            iIntros "Hashs". wp_pures.
            iModIntro.
            iApply "HPost". iFrame.
            iLeft. iExists _.
            iSplit; [done|]. iRight.
            iExists _. iSplit; [done|].
            destruct t_tree; destruct! Hser_tree; simplify_eq.
            destruct t_tree2; destruct! H2; simplify_eq.
            destruct t_tree2_2; destruct! H6; simplify_eq.
            destruct! Hser; simplify_eq.
            destruct! H4; simplify_eq.
            destruct! H9; simplify_eq.
            destruct (decide (collision (inr_ser_str
                                           (prod_ser_str H0 (string_ser_str (hash child2_v_string))))
                                (inr_ser_str (prod_ser_str H2 (string_ser_str H3))))) as [|Hnc%not_collision].
            { iExFalso. by iApply (hashes_auth.hashed_inj_or_coll with "Hash_tree Hashs"). }
            destruct Hnc as [Hnc | Hnc]; simplify_eq. done. }

          iDestruct "HPost1" as "(-> & [%Heq|%Hneq])".
          { wp_pures.
            wp_apply s_ser_spec.
            { iExists _. iRight. iSplit; [done|].
              iExists _,_. iSplit; [done|].
              inversion proof_str.
              iSplit; by iExists _. }
            iIntros (s0 Hser).
            wp_apply wp_hash; [done|].
            iIntros "Hashs". wp_pures.
            iModIntro.
            iApply "HPost". iFrame.
            iLeft. iExists _. iSplit; [done|].
            iLeft. iSplit; [done|].
            simplify_eq.
            destruct (decide (collision tree_i_hashed s0)) as [|Hnc%not_collision].
            { iExFalso. by iApply (hashes_auth.hashed_inj_or_coll with "Hash_tree Hashs"). }
            destruct Hnc as [Hnc | Hnc]; simplify_eq; eauto. }

          { wp_pures.
            wp_apply s_ser_spec.
            { iExists _. iRight. iSplit; [done|].
              iExists _,_. iSplit; [done|].
              simplify_list_eq.
              iSplit; by iExists _. }
            iIntros (s0 Hser).
            wp_apply wp_hash; [done|].
            iIntros "Hashs". wp_pures.
            iModIntro.
            iApply "HPost". iFrame.
            iLeft. iExists _. iSplit; [done|].
            iLeft. iSplit; [done|].
            simplify_eq.
            destruct (decide (collision tree_i_hashed s0)) as [|Hnc%not_collision].
            { iExFalso. by iApply (hashes_auth.hashed_inj_or_coll with "Hash_tree Hashs"). }
            destruct Hnc as [Hnc | Hnc]; simplify_eq; eauto. }
  Qed.

  (* This lemma gives the postconditions for the case when the verifier is given
     a proof that claims the retrieve query doesn't return some result.
     This assumes that path's length is longer than the tree's height.
     The proof is structurally a very similar to the previous one.

     There are three cases from here.
     1) The verifier accepts the proof, the ideal returns none.
        tree_i_hash may or may not be equal to tree_v_hash.
     2) The verifier accepts the proof, the ideal returns something.
        Then the final hashes shouldn't be equal. In this case it is possible
        that the verifier rejects the proof very early, and the ideal doesn't terminate.
     3) The verifier doesn't accept the proof.
   *)
  
  Lemma refines_retrieve_aux_none_long Θ (Δ : ctxO Σ Θ) :
    ∀ ti Ki (l_path_v l_path_i disc_v: list (()+())) (l_proof: list val)
      (l_proof_s: list string) (tip_v_hash tip_v tree_i_hash: string)
      (path_v path_i proof tree_i: val),
      is_list l_path_v path_v → is_list l_path_i path_i →
      l_path_i = l_path_v ++ disc_v → length disc_v > 0 → is_list l_proof proof →
      (l_proof = (fun (x : string) => #x) <$> l_proof_s) →
      ⟦ t_tree_auth ⟧ (merkle_retrieve_ctx Δ) #tree_i_hash tree_i -∗
      ⟦ t_tree_auth ⟧ (merkle_retrieve_ctx Δ) #tip_v_hash (InjLV #tip_v) -∗
      {{{ spec_ideal ti (fill Ki (retrieve_ideal_aux path_i tree_i)) }}}
        retrieve_magic_verifier_aux path_v proof #tip_v_hash
      {{{ v_v, RET v_v;
          (∃ tree_v_hash: string,
              ⌜v_v = SOMEV #tree_v_hash⌝ ∗
                ((⌜tree_i_hash = tree_v_hash ∨
                    tree_i_hash ≠ tree_v_hash⌝ ∗ spec_ideal ti (fill Ki NONEV)) ∨
                (∃ e_i: expr, ⌜tree_i_hash ≠ tree_v_hash⌝ ∗ spec_ideal ti (fill Ki e_i)))) ∨
            (∃ e_i: expr,
                ⌜(v_v = NONEV)⌝ ∗ spec_ideal ti (fill Ki e_i)) }}}%I.
  Proof.
    iIntros (?????????????? is_list_v is_list_i Hl Hdisc is_list_proof proof_str) "#HTree #HTip".
    iIntros (Φ) "!# Hi HPost".
    iInduction (l_path_v) as [|h t_path] "IH" forall (Φ path_v disc_v l_path_i path_i l_proof l_proof_s proof tree_i
                                                        tree_i_hash is_list_v is_list_i is_list_proof proof_str Hl Hdisc)
                                                     "Hi HPost HTree".
    - iEval (rewrite t_tree_auth_unfold) in "HTip".
      iDestruct "HTip" as (last_v_val t_last last_v_hashed Hser_tip ->) "(HTip & #Hash_tip)".
      wp_rec. wp_pures. wp_rec.
      simpl in Hl.
      iDestruct "HTip" as (last_v_sum last_v_sum2) "[(%H1 & %H2 & %HTip)|(-> & %H2 & #HTip)]"; simplify_eq.
      iEval (rewrite t_tree_auth_unfold) in "HTree".
      iDestruct "HTree" as (tree_i_val t_tree tree_i_hashed Hser_tree HtreeiHash) "(HTree & #Hash_tree)".
      wp_pures.
      wp_apply (gwp_list_head_nil); [done|].
      iIntros (_). wp_pures.
      destruct l_proof_s; simpl in is_list_proof.
      + i_rec ti. i_pures. i_rec ti. simplify_eq.
        wp_rec. wp_pures.
        destruct disc_v.
        { simpl in Hdisc. lia. }
        i_bind (list_head _).
        iMod (gwp_list_head_cons ⊤ path_i s disc_v () (λ w, ⌜w=SOMEV (inject s)⌝)%I
             with "[//] [] [$Hi //]") as (?) "[Hi ->]".
        { by iIntros "!>" (?). }
        iSimpl in "Hi". i_pures.
        i_bind (list_tail _).
        iMod (gwp_list_tail ⊤ path_i (s::disc_v) () (λ w, ⌜is_list disc_v w⌝)%I
               with "[//] [] [$Hi //]") as (path_tail_i) "[Hi %is_list_tail_path_i]".
        { by iIntros "!>" (?). }
        iSimpl in "Hi". i_pures.

        iDestruct "HTree" as (tree_i_sum tree_i_sum2) "[(-> & -> & %HLeaf)|(-> & -> & #HNode)]".
        { i_pures.
          iModIntro.
          iApply "HPost".
          iLeft. iExists _.
          iSplit; [done|]. iFrame. iLeft.
          destruct (decide (collision tree_i_hashed last_v_hashed)) as [|Hnc%not_collision].
          { iExFalso. by iApply (hashes_auth.hashed_inj_or_coll with "Hash_tree Hash_tip"). }
          destruct Hnc as [Hnc | ?]; simplify_eq; eauto. }

        iModIntro.
        iApply "HPost".
        iLeft. iExists _. iSplit; [done|].
        iRight. iFrame.
        destruct HTip as [? [? ?]]. simplify_eq.
        destruct t_last; destruct! Hser_tip; simplify_eq.
        destruct t_tree; destruct! Hser_tree; simplify_eq.
        destruct (decide (collision (inr_ser_str H3) (inl_ser_str H1))) as [|Hnc%not_collision].
        { iExFalso. by iApply (hashes_auth.hashed_inj_or_coll with "Hash_tree Hash_tip"). }
        destruct Hnc as [Hnc | ?]; simplify_eq; eauto.

      + destruct is_list_proof as [? [-> ?]].
        wp_rec. wp_pures. wp_rec. wp_pures.
        iApply "HPost". iModIntro.
        iRight. iExists _. iFrame. done.

    - wp_rec. wp_pures. wp_rec.
      wp_apply (gwp_list_head_cons); [done|].
      iIntros (_). wp_pures.
      wp_apply (gwp_list_tail); [done|].
      iIntros (path_tail_v is_list_tail_path_v). wp_pures.
      destruct l_proof.
      { wp_apply gwp_list_head_nil; [done|].
        iIntros (_). wp_pures.
        iApply "HPost". iRight. iExists _.
        iFrame. done. }
      destruct l_proof_s; [done|].

      wp_apply gwp_list_head_cons; [done|].
      iIntros (_). wp_pures.
      wp_apply gwp_list_tail; [done|].
      iIntros (proof_tail is_list_ptail).
      i_rec ti. i_pures. i_rec ti.
      i_bind (list_head _).
      iMod (gwp_list_head_cons ⊤ path_i h (t_path ++ disc_v) () (λ w, ⌜w=SOMEV (inject h)⌝)%I
             with "[] [] [$Hi //]") as (?) "[Hi ->]".
      { iPureIntro. simplify_list_eq. done. }
      { by iIntros "!>" (?). }
      iSimpl in "Hi". i_pures.
      i_bind (list_tail _).
      iMod (gwp_list_tail ⊤ path_i ((h::t_path)++disc_v) () (λ w, ⌜is_list (t_path++disc_v) w⌝)%I
             with "[] [] [$Hi //]") as (path_tail_i) "[Hi %is_list_tail_path_i]".
      { iPureIntro. simplify_list_eq. done. }
      { by iIntros "!>" (?). }
      iSimpl in "Hi". i_pures. fold path_pop. fold retrieve_ideal_aux.
      iEval (rewrite t_tree_auth_unfold) in "HTree".
      iDestruct "HTree" as (tree_i_val t_tree tree_i_hashed Hser_tree Htree_i_hash) "(HTree & #Hash_tree)".
      wp_pure.
      iDestruct "HTree" as (tree_i_sum tree_i_sum2) "[(-> & -> & #HLeaf)|(-> & -> & #HNode)]".
      + i_pures. wp_pures.
        wp_bind (retrieve_magic_verifier_aux _ _ _).
        iApply (refines_retrieve_aux_empty_i  with "[//] [HPost Hi]").
        { done. }
        { done. }
        { simpl. instantiate (1 := l_proof_s). simplify_list_eq. done. }
        iNext.
        iIntros (?) "[(% & ->)|->]"; wp_pures; last first.
        { iApply "HPost". iRight. iExists _. by iFrame. }
        destruct h; wp_pures.
        * wp_apply s_ser_spec.
          { iExists _. iRight. iSplit; [done|].
            iExists _,_. iSplit; [done|].
            inversion proof_str.
            iSplit; by iExists _. }
          iIntros (s1 Hser).
          wp_apply wp_hash; [done|].
          iIntros "Hashs". wp_pures.
          iModIntro.
          iApply "HPost".
          iFrame. iLeft. iExists _.
          iSplit; [done|]. iLeft.
          simplify_eq.
          destruct (decide (collision tree_i_hashed s1)) as [|Hnc%not_collision].
          { iExFalso. by iApply (hashes_auth.hashed_inj_or_coll with "Hash_tree Hashs"). }
          destruct Hnc as [Hnc | ?]; simplify_eq; eauto.

        * wp_apply s_ser_spec.
          { iExists _. iRight. iSplit; [done|].
            iExists _,_. iSplit; [done|].
            inversion proof_str.
            iSplit; by iExists _. }
          iIntros (s1 Hser).
          wp_apply wp_hash; [done|].
          iIntros "Hashs". wp_pures.
          iModIntro.
          iApply "HPost".
          iFrame. iLeft. iExists _.
          iSplit; [done|]. iLeft.
          simplify_eq.
          destruct (decide (collision tree_i_hashed s1)) as [|Hnc%not_collision].
          { iExFalso. by iApply (hashes_auth.hashed_inj_or_coll with "Hash_tree Hashs"). }
          destruct Hnc as [Hnc | ?]; simplify_eq; eauto.

      + wp_pures. i_pures.
        iDestruct "HNode" as (child1_v child1_i child2_v child2_i) "(-> & -> & #HChild1Rec & #HChild2Rec)".
        destruct h; i_pures.
        * wp_bind (retrieve_magic_verifier_aux _ _ _).
          iEval (rewrite t_tree_auth_unfold) in "HChild1Rec".
          iDestruct "HChild1Rec" as (child1_v_val t_child1 child1_v_string Hser_child ->) "(HChild1 & #Hs1)".
          iApply ("IH" with "[//] [//] [//] [] [//] [//] Hi [HPost]").
          { iPureIntro. simplify_list_eq. done. }
          2 : { iModIntro. iEval (rewrite t_tree_auth_unfold). iExists _, _, _. eauto. }
          iNext.
          iIntros (v_v) "HPost1".
          iDestruct "HPost1" as "[(% & -> & [([%Heq|%Hneq] & Hi)|(% & %Hneq & Hi)])|(% & -> & Hi)]"; last first.
          { wp_pures.
            iModIntro.
            iApply "HPost". iRight. iExists _. iFrame. done. }
          { wp_pures.
            wp_apply s_ser_spec.
            { iExists _. iRight. iSplit; [done|].
              iExists _,_. iSplit; [done|].
              inversion proof_str.
              iSplit; by iExists _. }
            iIntros (s0 Hser).
            wp_apply wp_hash; [done|].
            iIntros "Hashs". wp_pures.
            iModIntro.
            iApply "HPost". iFrame.
            iLeft. iExists _.
            iSplit; [done|]. iRight. iFrame.
            destruct t_tree; destruct! Hser_tree; simplify_eq.
            destruct t_tree2; destruct! H2; simplify_eq.
            destruct t_tree2_1; destruct! H5; simplify_eq.
            destruct! Hser; simplify_eq.
            destruct! H4; simplify_eq.
            destruct! H8; simplify_eq.
            destruct (decide (collision (inr_ser_str (prod_ser_str (string_ser_str (hash child1_v_string)) H3))
                                (inr_ser_str (prod_ser_str (string_ser_str H) H5)))) as [|Hnc%not_collision].
            { iExFalso. by iApply (hashes_auth.hashed_inj_or_coll with "Hash_tree Hashs"). }
            destruct Hnc as [Hnc | Hnc]; simplify_eq. done. }

          { wp_pures.
            wp_apply s_ser_spec.
            { iExists _. iRight. iSplit; [done|].
              iExists _,_. iSplit; [done|].
              inversion proof_str.
              iSplit; by iExists _. }
            iIntros (s0 Hser).
            wp_apply wp_hash; [done|].
            iIntros "Hashs". wp_pures.
            iModIntro.
            iApply "HPost". iFrame.
            iLeft. iExists _. iSplit; [done|].
            iLeft. iRight.
            destruct t_tree; destruct! Hser_tree; simplify_eq.
            destruct t_tree2; destruct! H2; simplify_eq.
            destruct t_tree2_1; destruct! H5; simplify_eq.
            destruct! Hser; simplify_eq.
            destruct! H4; simplify_eq.
            destruct! H8; simplify_eq.
            destruct (decide (collision (inr_ser_str (prod_ser_str (string_ser_str (hash child1_v_string)) H3))
                                (inr_ser_str (prod_ser_str (string_ser_str H) H5)))) as [|Hnc%not_collision].
            { iExFalso. by iApply (hashes_auth.hashed_inj_or_coll with "Hash_tree Hashs"). }
            destruct Hnc as [Hnc | Hnc]; simplify_eq. done. }

          { wp_pures.
            wp_apply s_ser_spec.
            { iExists _. iRight. iSplit; [done|].
              iExists _,_. iSplit; [done|].
              inversion proof_str.
              iSplit; by iExists _. }
            iIntros (s0 Hser).
            wp_apply wp_hash; [done|].
            iIntros "Hashs". wp_pures.
            iModIntro.
            iApply "HPost". iFrame.
            iLeft. iExists _. iSplit; [done|].
            iLeft. simplify_eq.
            destruct (decide (collision tree_i_hashed s0)) as [|Hnc%not_collision].
            { iExFalso. by iApply (hashes_auth.hashed_inj_or_coll with "Hash_tree Hashs"). }
            destruct Hnc as [Hnc | Hnc]; simplify_eq; eauto. }
        * wp_bind (retrieve_magic_verifier_aux _ _ _).
          iEval (rewrite t_tree_auth_unfold) in "HChild2Rec".
          iDestruct "HChild2Rec" as (child2_v_val t_child2 child2_v_string Hser_child ->) "(HChild2 & #Hs1)".

          iApply ("IH" with "[//] [//] [//] [] [//] [//] Hi [HPost]").
          { iPureIntro. simplify_list_eq. done. }
          2 : { iModIntro. iEval (rewrite t_tree_auth_unfold). iExists _, _, _. eauto. }

          iNext.
          iIntros (v_v) "HPost1".
          iDestruct "HPost1" as "[(% & -> & [([%Heq|%Hneq] & Hi)|(% & %Hneq & Hi)])|(% & -> & Hi)]"; last first.
          { wp_pures.
            iModIntro.
            iApply "HPost". iRight. iExists _. iFrame. done. }

          { wp_pures.
            wp_apply s_ser_spec.
            { iExists _. iRight. iSplit; [done|].
              iExists _,_. iSplit; [done|].
              inversion proof_str.
              iSplit; by iExists _. }
            iIntros (s0 Hser).
            wp_apply wp_hash; [done|].
            iIntros "Hashs". wp_pures.
            iModIntro.
            iApply "HPost". iFrame.
            iLeft. iExists _.
            iSplit; [done|]. iRight. iFrame.
            destruct t_tree; destruct! Hser_tree; simplify_eq.
            destruct t_tree2; destruct! H2; simplify_eq.
            destruct t_tree2_2; destruct! H6; simplify_eq.
            destruct! Hser; simplify_eq.
            destruct! H4; simplify_eq.
            destruct! H9; simplify_eq.
            destruct (decide (collision (inr_ser_str (prod_ser_str H0 (string_ser_str (hash child2_v_string))))
                                (inr_ser_str (prod_ser_str H2 (string_ser_str H3))))) as [|Hnc%not_collision].
            { iExFalso. by iApply (hashes_auth.hashed_inj_or_coll with "Hash_tree Hashs"). }
            destruct Hnc as [Hnc | Hnc]; simplify_eq. done. }

          { wp_pures.
            wp_apply s_ser_spec.
            { iExists _. iRight. iSplit; [done|].
              iExists _,_. iSplit; [done|].
              inversion proof_str.
              iSplit; by iExists _. }
            iIntros (s0 Hser).
            wp_apply wp_hash; [done|].
            iIntros "Hashs". wp_pures.
            iModIntro.
            iApply "HPost". iFrame.
            iLeft. iExists _. iSplit; [done|].
            iLeft. iRight.
            destruct t_tree; destruct! Hser_tree; simplify_eq.
            destruct t_tree2; destruct! H2; simplify_eq.
            destruct t_tree2_2; destruct! H6; simplify_eq.
            destruct! Hser; simplify_eq.
            destruct! H4; simplify_eq.
            destruct! H9; simplify_eq.
            destruct (decide (collision (inr_ser_str (prod_ser_str H0 (string_ser_str (hash child2_v_string))))
                                (inr_ser_str (prod_ser_str H2 (string_ser_str H3))))) as [|Hnc%not_collision].
            { iExFalso. by iApply (hashes_auth.hashed_inj_or_coll with "Hash_tree Hashs"). }
            destruct Hnc as [Hnc | Hnc]; simplify_eq. done. }

          { wp_pures.
            wp_apply s_ser_spec.
            { iExists _. iRight. iSplit; [done|].
              iExists _,_. iSplit; [done|].
              inversion proof_str.
              iSplit; by iExists _. }
            iIntros (s0 Hser).
            wp_apply wp_hash; [done|].
            iIntros "Hashs". wp_pures.
            iModIntro.
            iApply "HPost". iFrame.
            iLeft. iExists _. iSplit; [done|].
            iLeft. simplify_eq.
            destruct (decide (collision tree_i_hashed s0)) as [|Hnc%not_collision].
            { iExFalso. by iApply (hashes_auth.hashed_inj_or_coll with "Hash_tree Hashs"). }
            destruct Hnc as [Hnc | Hnc]; simplify_eq; eauto. }
  Qed.

  Lemma wp_deserialize_list_proof (v lv: val) (l: list val) (l_s: list string) :
    is_list l lv → l = (fun (x : string) => #x) <$> l_s →
    ((∃ s: string, v = SOMEV #s) ∨ v = NONEV) →
    {{{ ⌜True⌝ }}}
      deserialize_list_proof v lv
      {{{ w, RET w; ⌜∃ (l'' ret_l: list val) (l': list string) (w': val),
                        w = SOMEV w' ∧
                          ret_l = (fun (x : string) => #x) <$> l' ∧
                          is_list l'' w' ∧ l'' = (rev ret_l) ++ l⌝ ∨ ⌜w = NONEV⌝ }}}.
  Proof.
    iIntros (is_list_init list_str Hv).
    iIntros (Φ) "%_ HΦ".
    iLöb as "IH" forall (v l l_s lv is_list_init list_str Hv Φ) "HΦ".
    wp_rec. wp_pures.
    destruct Hv as [[s ->] | ->].
    - wp_pures.
      wp_apply wp_parse_retrieve_proof; [by iExists _|].
      iIntros (?) "[->|(% & % & -> & (% & %))]".
      { wp_pures. iApply "HΦ".
        iModIntro. by iRight. }
      wp_pures.
      wp_bind (_ :: _)%E.
      iApply (gwp_list_cons _ _ _ _); [done|].
      iModIntro. iIntros (v is_list_next).
      iApply ("IH" with "[//] [] [] [HΦ]").
      { iPureIntro. instantiate (1 := l_s0 :: l_s). simplify_list_eq. done. }
      { destruct H. { iLeft. by iExists _. }
        by iRight. }

      iNext.
      iIntros (w HPost).
      iApply "HΦ".

      destruct HPost; last first; [by iRight |].
      iLeft.
      destruct H0 as [? [? [? [? [-> [-> [? ->]]]]]]].
      iExists (rev ((λ x : string, #x) <$> x1) ++ #l_s0 :: l),
        (#l_s0 :: ((λ x : string, #x) <$> x1)), (l_s0 :: x1), _.
      iPureIntro. simplify_list_eq. done.

    - wp_pures. iApply "HΦ".
      iModIntro. iLeft.
      iExists l, [], [], lv. done.
  Qed.

  Lemma reverse_rev {A} (l: list A) :
    reverse l = rev l.
  Proof.
    unfold reverse. rewrite rev_alt. done.
  Qed.

  Lemma refines_retrieve Θ Δ Γ :
    ⊢ { (Θ ▹ ⋆ ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆))%kind ; merkle_retrieve_ctx Δ; Γ }
      ⊨ v_retrieve ≤log≤ i_retrieve : t_retrieve.
  Proof.
    iIntros (vs) "#Hvs %Ki %ti Hi".
    rewrite /v_retrieve /i_retrieve.
    wp_pures. iModIntro. iFrame.
    iIntros (path_v path_i) "!# Hpath".
    interp_unfold in "Hpath".
    iDestruct "Hpath" as (?) "(%is_list_path_v & %is_list_path_i)".
    iIntros (??) "Hi".
    wp_pures; i_pures.
    iModIntro. iFrame.
    iIntros (tree_v tree_i) "!# #Htree_auth". rewrite -!/interp.
    iPoseProof "Htree_auth" as "Htree_auth'".
    iEval (rewrite t_tree_auth_unfold) in "Htree_auth".
    iDestruct "Htree_auth" as (tree_v_val t_tree tree_v_hashed Hser_tree ->) "(#Htree & #Hash_tree)".
    iIntros (??) "Hi".
    wp_pures; i_pures.
    iModIntro. iFrame.
    interp_unfold!.
    iIntros "!# % [%prf %Hprf] % % Hi".
    wp_pures; i_pures.
    wp_apply (gwp_list_head with "[//]").
    iIntros (prf_head [[-> ->] | (?&?&->&->)]); wp_pures.
    { by iExists None. }
    wp_rec.
    wp_apply (s_deser_sound); [done|].
    iIntros ([] Hdeser); wp_pures; last first.
    { by iExists None. }
    destruct! Hdeser; simplify_eq.
    (* Whether the proof has an empty proof along with the first element *)
    - wp_pures. wp_rec. wp_pures.
      destruct! H2; simplify_eq; wp_pures.
      (* Whether the first element of the proof indicates case 1 or (2/3) *)
      + destruct! H4; simplify_eq.
        wp_apply s_ser_spec.
        { iExists _. iLeft. iSplit; [done|].
          by iExists _. }
        iIntros (tip Hser).
        wp_apply wp_hash; [done|]. iIntros "#Htip".
        wp_pures.
        wp_apply (refines_retrieve_aux_some _ _ with "Htree_auth' [] Hi []").
        { done. } { done. } { by instantiate (1 := []). }
        { by instantiate (1 := []). }
        { iEval (rewrite t_tree_auth_unfold).
          iExists (InjLV #H),(tsum tstring (tprod tstring tstring)),tip. iFrame "#".
          iSplit. { iFrame "%". } iSplit; [done|].
          iNext. iExists _,_. iLeft. iSplit; [done|].
          iSplit; [done|]. iExists _. iSplit; done. }
        iNext.
        iIntros (v_v) "[(% & [(% & % & (-> & ->) & %Hres)|(% & -> & -> & %Hres)] & Hi)|(% & -> & Hi)]".
        * wp_pures.
          destruct Hres as [Heq | Hneq]; last first.
          { wp_pures.
            case_bool_decide as Heq; simplify_eq.
            wp_pures.
            iSimpl in "Hi".
            iModIntro. iExists (None).
            iSplit; done. }
          case_bool_decide as Heq1; last first.
          { wp_pures.
            iSimpl in "Hi".
            iModIntro. iExists (None).
            iSplit; done. }
          wp_pures.
          wp_apply (gwp_list_tail); [done|].
          iIntros (v prf_is_tail). wp_pures.
          inversion Heq1. simplify_eq.
          assert (tip_i = H).
          { apply Heq. done. }
          iModIntro. iExists (Some _).
          iSplit; [done|]. iFrame.
          iExists _,_. iSplit; [done|].
          iSplit. { iExists _. done. }
          iExists _, _. iRight.
          repeat (iSplit; [done|]).
          rewrite H0. interp_unfold. by iExists _.
        * wp_pures.
          case_bool_decide as Heq; simplify_eq; wp_pures.
          iModIntro. iExists None.
          iSplit; done.
        * wp_pures. iModIntro.
          iExists None.
          iSplit; done.
      + wp_pures.
        destruct! H4; simplify_eq; wp_pures.
        (* Whether the first element of the proof indicates case 2 or 3 *)
        * wp_rec. wp_pures.
          wp_rec. wp_pures. wp_rec. wp_pures.
          destruct! H4; simplify_eq.
          destruct l.
          { wp_apply (gwp_list_length); [done|].
            iIntros (? ->). wp_pures.
            wp_apply s_ser_spec.
            { iExists _. iLeft.
              iSplit; [done|].
              by iExists _. }
            iIntros (tip Hser).
            wp_apply wp_hash; [done|]. iIntros "#Htip".
            wp_pures.
            iModIntro. iExists None. done. }
          wp_apply gwp_list_length; [done|].
          iIntros (? ->). wp_pures.
          wp_apply s_ser_spec.
          { iExists _. iLeft.
            iSplit; [done|].
            by iExists _. }
          iIntros (tip Hser).
          wp_apply wp_hash; [done|]. iIntros "#Htip".
          wp_pures.
          wp_apply (refines_retrieve_aux_none_long _ _ with "[//] [] Hi").
          { by instantiate (1 := []). }
          { done. } { done. } { simpl. lia. }
          { by instantiate (1 := []). }
          { by instantiate (1 := []). }
          { iEval (rewrite t_tree_auth_unfold).
            iExists (InjLV #H0),(tsum tstring (tprod tstring tstring)),tip. iFrame "#".
            iSplit. { iFrame "%". } iSplit; [done|].
            iNext. iExists _,_. iLeft. iSplit; [done|].
            iSplit; [done|]. iExists _. iSplit; done. }
          iIntros (v_v) "[(% & -> & [([%Heq|%Hneq] & Hi)|(% & %Hneq & Hi)])|(% & -> & Hi)]"; simplify_eq.
          { wp_pures.
            case_bool_decide as H; simplify_eq. wp_pures.
            wp_apply (gwp_list_tail); [done|].
            iIntros (v prf_is_tail). wp_pures.
            iModIntro. iExists (Some _).
            iSplit; [done|]. iFrame.
            iExists _,_. iSplit; [done|].
            iSplit. { iExists _. done. }
            iExists _, _. iLeft.
            repeat iSplit; done. }
          { wp_pures.
            case_bool_decide as H; simplify_eq. wp_pures.
            iModIntro. iExists None. done. }
          { wp_pures.
            case_bool_decide as H; simplify_eq. wp_pures.
            iModIntro. iExists None. done. }
          { wp_pures.
            iModIntro. iExists None. done. }
        * destruct! H4; simplify_eq.
          wp_apply s_ser_spec.
          { iExists _. iRight. iSplit; [done|].
            iExists _, _. iSplit; [done|].
            destruct! H6; destruct! H7; simplify_eq.
            iSplit; by iExists _. }
          iIntros (tip Hser).
          wp_apply wp_hash; [done|]. iIntros "#Htip".
          wp_pures.
          wp_apply (refines_retrieve_aux_none_short _ _ with "[//] [] Hi []").
          { done. } { done. } { by instantiate (1 := []). }
          { by instantiate (1 := []). } { done. } { done. }
          iNext.
          iIntros (v_v) "[(% & % & -> & [(-> & [%Heq|%Hneq])|(% & -> & %Hneq)] & Hi)|(% & -> & Hi)]"; simplify_eq.
          { wp_pures.
            case_bool_decide as Heq; simplify_eq; wp_pures.
            wp_apply (gwp_list_tail); [done|].
            iIntros (v prf_is_tail). wp_pures.
            iModIntro. iExists (Some _).
            iSplit; [done|]. iFrame.
            iExists _,_. iSplit; [done|].
            iSplit. { iExists _. done. }
            iExists _, _. iLeft. 
            repeat iSplit; done. }
          { wp_pures.
            case_bool_decide as Heq; simplify_eq; wp_pures.
            iModIntro. iExists None. done. }
          { wp_pures.
            case_bool_decide as Heq; simplify_eq; wp_pures.
            iModIntro. iExists None. done. }
          wp_pures. iModIntro.
          iExists None. done.
          
    - destruct! H2; simplify_eq. wp_pures.
      wp_apply wp_deserialize_list_proof.
      { by instantiate (1 := []). }
      { by instantiate (1 := []). }
      { left. destruct! H7; simplify_eq. by exists H. }
      { done. }
      iIntros (w HTemp). 
      destruct HTemp as [[? [? [? [? [-> [-> [Hlw ->]]]]]]] | ->]; last first.
      (* Whether the rest of the proof is valid or not (not valid first) *)
      { wp_pures. iModIntro. iExists None. done. }        
      destruct! H6; simplify_eq.
      (* Whether the first element of the proof indicates case 1 or (2/3) *)
      * wp_pures.
        wp_apply s_ser_spec.
        { iExists _. iLeft. iSplit; [done|].
          destruct! H6; simplify_eq. by iExists _. }
        iIntros (tip Hser).
        wp_apply wp_hash; [done|]. iIntros "#Htip".
        wp_pures.
        destruct! Hser; simplify_eq.
        destruct! H8; simplify_eq.
        wp_apply (refines_retrieve_aux_some _ _ with "[//] [] Hi []").
        { done. } { done. } { done. }
        { rewrite <- reverse_rev. simplify_list_eq.
          instantiate (1 := reverse (x2)).
          by rewrite fmap_reverse. }
        { iEval (rewrite t_tree_auth_unfold).
          iExists _, (tsum tstring (tprod tstring tstring)), (inl_ser_str (string_ser_str H)).
          iSplit.
          { instantiate (1 := InjLV #H).
            iExists _, _. iLeft. repeat (iSplit; [done|]).
            destruct! H6; simplify_eq. done. }
          repeat (iSplit; [done|]). iFrame "#".
          iNext. iExists _, _. iLeft. repeat (iSplit; [done|]).
          iExists _. iSplit; done. }
        iNext.
        iIntros (v_v) "[(% & [(% & % & (-> & ->) & %Hres)|(% & -> & -> & %Hres)] & Hi)|(% & -> & Hi)]".
        { wp_pures.
          destruct Hres as [Heq | Hneq].
          { case_bool_decide as Heq1; last first.
            { wp_pures. iModIntro. iExists None. done. }
            simplify_eq. assert (tip_i = H). { by apply Heq. }
            wp_pures.
            wp_apply (gwp_list_tail); [done|].
            iIntros (v prf_is_tail). wp_pures. iModIntro.
            iExists (Some _). repeat (iSplit; [done|]).
            iFrame. iExists _, _. repeat (iSplit; [done|]).
            iSplit. { by iExists _. }
            iExists _, _. iRight.
            repeat (iSplit; [done|]). simplify_eq.
            interp_unfold. by iExists _. }
          case_bool_decide; simplify_eq; last first.
          wp_pures. iModIntro. iExists None. done. }
        { wp_pures.
          case_bool_decide as Heq; simplify_eq.
          wp_pures. iModIntro. iExists None. done. }
        { wp_pures. iModIntro. iExists None. done. }
      * wp_pures. destruct! H6; simplify_eq.
        (* Whether the first element of the proof indicates case 2 or 3 *)
        -- wp_pures. wp_apply (gwp_list_length); [done|].
           iIntros (v ->).
           assert (length (rev ((λ x : string, #x) <$> x2) ++ []) = length x2).
           { rewrite <- reverse_rev. simplify_list_eq.
             rewrite length_reverse. rewrite length_fmap. done. }
           rewrite H.
           wp_apply gwp_list_sub; [done|].
           iIntros (v Hlv).
           wp_pures.
           wp_apply gwp_list_length; [done|].
           iIntros (v0 ->).
           wp_apply gwp_list_length; [done|].
           iIntros (v0 ->).
           assert (length x2 ≥ length l ∨ length x2 < length l).
           { lia. }
           destruct H1.
           (* Whether the proof is equal or shorter than the path.
                This is case 2, and thus, the proof should be shorter.
                If not, the verifier rejects the proof.
            *)
           { rewrite take_ge; [|done].
             wp_pures. case_bool_decide as HH; [|lia].
             wp_pures.
             wp_apply s_ser_spec.
             { iExists _. iLeft. iSplit; [done|].
               destruct! H6; simplify_eq. by iExists _. }
             iIntros (tip Hser).
             wp_apply wp_hash; [done|]. iIntros "#Htip".
             wp_pures.
             iModIntro. iExists None. done. }
           
           rewrite length_take_le; [|lia].
           wp_pures. case_bool_decide as HH; [lia|].
           wp_pures.
           wp_apply s_ser_spec.
           { iExists _. iLeft. iSplit; [done|].
             destruct! H6; simplify_eq. by iExists _. }
           iIntros (tip Hser).
           wp_apply wp_hash; [done|]. iIntros "#Htip".
           wp_pures.
           destruct! H6; simplify_eq.
           wp_apply (refines_retrieve_aux_none_long _ _ with "[//] [] Hi []").
           { done. } { done. } { instantiate (1 := drop (length x2) l). by rewrite take_drop. }
           { rewrite length_drop. lia. } { done. }
           { instantiate (1 := reverse x2). rewrite <- reverse_rev.
             simplify_list_eq. rewrite fmap_reverse. done. }
           { iEval (rewrite t_tree_auth_unfold).
             iExists (InjLV #H5), (tsum tstring (tprod tstring tstring)), tip.
             repeat (iSplit; [done|]). iFrame "#".
             iNext. iExists _, _. iLeft. repeat (iSplit; [done|]).
             by iExists _. }
           iNext.
           iIntros (v_v) "[(% & -> & [([%Heq|%Hneq] & Hi)|(% & %Hneq & Hi)])|(% & -> & Hi)]".
           { wp_pures. simplify_eq.
             case_bool_decide as Heq; simplify_eq. wp_pures.
             wp_apply (gwp_list_tail); [done|].
             iIntros (v0 prf_is_tail). wp_pures. iModIntro.
             iExists (Some _). repeat (iSplit; [done|]).
             iFrame. iExists _, _. repeat (iSplit; [done|]).
             iSplit. { by iExists _. }
             iExists _, _. iLeft.
             repeat iSplit; done. }
           { wp_pures.
             case_bool_decide as Heq; simplify_eq. wp_pures.
             iModIntro. iExists None. done. }
           { wp_pures.
             case_bool_decide as Heq; simplify_eq. wp_pures.
             iModIntro. iExists None. done. }
           { wp_pures.
             iModIntro. iExists None. done. }
           
        -- wp_pures.
           destruct! H6; simplify_eq.
           wp_apply s_ser_spec.
           { iExists _. iRight.
             iSplit; [done|]. iExists _, _.
             iSplit; [done|]. destruct! H9; destruct! H10; simplify_eq.
             iSplit; (iExists _; done). }
           iIntros (tip Hser).
           wp_apply wp_hash; [done|]. iIntros "#Htip".
           wp_pures.
           wp_apply (refines_retrieve_aux_none_short _ _ with "[//] [] Hi").
           { done. } { done. } { done. }
           { instantiate (1 := reverse x2). rewrite <- reverse_rev.
             simplify_list_eq. rewrite fmap_reverse. done. }
           { done. } { done. }
           iIntros (v_v) "[(% & % & -> & [(-> & [%Heq|%Hneq])|(% & -> & %Hneq)] & Hi)|(% & -> & Hi)]".
           { wp_pures.
             case_bool_decide as HH; simplify_eq; wp_pures.
             wp_apply (gwp_list_tail); [done|].
             iIntros (v0 prf_is_tail). wp_pures. iModIntro.
             iExists (Some _). repeat (iSplit; [done|]).
             iFrame. iExists _, _. repeat (iSplit; [done|]).
             iSplit. { by iExists _. }
             iExists _, _. iLeft.
             repeat iSplit; done. }
           { wp_pures.
             case_bool_decide as Heq; simplify_eq. wp_pures.
             iModIntro. iExists None. done. }
           { wp_pures.
             case_bool_decide as Heq; simplify_eq. wp_pures.
             iModIntro. iExists None. done. }
           { wp_pures.
             iModIntro. iExists None. done. }
  Qed.


End semantic.
