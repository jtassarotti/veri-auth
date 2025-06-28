From auth.prelude Require Import stdpp.
From auth.rel_logic_tern Require Import fundamental.
From auth.examples Require Import authentikit_list_correctness.
From auth.heap_lang Require Export gen_weakestpre.
From stdpp Require Import list.

From auth.examples Require Import merkle.

(* We recommend first going through the security proof. *)

(* make_hash is a coq-level algorithm that gives the hash-value that
   the verifier will compute using the proof list.
 *)
Fixpoint make_hash (retrieve_proof_list: list string) (path: list (()+())) (last_val: string) : string :=
  match retrieve_proof_list, path with
  | [], [] => last_val
  | h_proof::retrieve_proof_list, h_path::path =>
      match h_path with
      | inl _ => hash (inr_ser_str
                         (prod_ser_str
                            (string_ser_str (make_hash retrieve_proof_list path last_val))
                            (string_ser_str h_proof)))
      | inr _ => hash (inr_ser_str
                         (prod_ser_str
                            (string_ser_str h_proof)
                            (string_ser_str (make_hash retrieve_proof_list path last_val))))
      end
  | _, _ => ""
  end.

(* An inductive predicate that states that v is a serialized list string obtained from l. *)
Fixpoint is_retrieve_proof_list (l : list string) (v: val) :=
  match l with
    [] => v = NONEV
  | a::[] => ∃ (s: string), v = SOMEV #s ∧ s_is_ser merkle_ser (InjLV #a) s
  | a::l' => ∃ (s s': string) (lv: val),
     v = SOMEV #s ∧ lv = SOMEV #s' ∧ s_is_ser merkle_ser (InjRV (#a, #s')) s ∧
       is_retrieve_proof_list l' lv
end.

(* States that the proof list corresponds to the case when the retrieve
   query should return some result.
 *)
Definition some_retrieve_proof (l: list string) (tip: val) (proof_string: string) :=
  match l with
    [] => s_is_ser list_first_ser (InjLV tip) proof_string
  | _ => ∃ (r_proof: string),
    s_is_ser list_first_ser (InjRV (tip, #r_proof)) proof_string ∧ is_retrieve_proof_list l (SOMEV #r_proof)
  end.

(* States that the proof list corresponds to the case when the retrieve
   query should not return a result.
 *)
Definition none_retrieve_proof (l: list string) (last_val: val) (proof_string: string) :=
  match l with
    [] => s_is_ser list_first_ser (InjLV last_val) proof_string
  | _ => ∃ (r_proof: string),
    s_is_ser list_first_ser (InjRV (last_val, #r_proof)) proof_string ∧ is_retrieve_proof_list l (SOMEV #r_proof)
  end.

Section retrieve_proof_specs.
  Context `{invGS_gen hlc Σ} `{g : !GenWp Σ}.

  Implicit Types s : gwp_type g.

  Lemma gwp_append_retrieve_proof_list (l : list string) (h : string) (v : val) E s :
    G{{{ ⌜is_retrieve_proof_list l v⌝ }}}
      (make_retrieve_proof merkle_ser) #h v @ s; E
    {{{ v', RET v'; ⌜is_retrieve_proof_list (h::l) (SOMEV v')⌝ }}} ? gwp_laters g.
  Proof.
    iIntros (Φ) "%is_retrieve_list HΦ".
    rewrite /make_retrieve_proof.
    gwp_pures.
    destruct l.
    - simpl in is_retrieve_list. simplify_eq.
      gwp_pures.
      gwp_apply (s_ser_spec).
      { iExists _. iLeft.
        iSplit; [done|].
        by iExists _. }
      iIntros (s' Hser).
      iApply "HΦ". simpl.
      iExists s'. iSplit; done.
    - destruct l.
      + destruct is_retrieve_list as [s' [-> Hser]].
        gwp_pures.
        gwp_apply (s_ser_spec).
        { iExists _. iRight.
          iSplit; [done|].
          iExists _, _.
          iSplit; [done|].
          iSplit; by iExists _. }
        iIntros (s'' Hser').
        iApply "HΦ". simpl.
        iExists _, _, _. iSplit; [done|].
        iSplit; [done|]. iSplit.
        { iPureIntro. apply Hser'. }
        iExists _. iSplit; done.
      + destruct is_retrieve_list as [lv [s' [s'' [-> [-> [Hser is_retrieve_list]]]]]].
        gwp_pures.
        gwp_apply (s_ser_spec).
        { iExists _. iRight.
          iSplit; [done|].
          iExists _, _.
          iSplit; [done|].
          iSplit; by iExists _. }
        iIntros (s''' Hser').
        iApply "HΦ". simpl.
        iExists _, _, _.
        iSplit; [done|].
        iSplit; [done|].
        iSplit; [iPureIntro; apply Hser'|].
        iExists _, _, _.
        iSplit; [done|].
        iSplit; [done|].
        iSplit; [iPureIntro; apply Hser|].
        destruct l.
        * iExists _.
          iSplit; [done|].
          simpl in is_retrieve_list.
          destruct is_retrieve_list as [? [? Hser'']].
          by simplify_eq.
        * destruct is_retrieve_list as [? [? [? [? [-> [? ?]]]]]].
          simpl in H1.
          iExists _, _, (InjRV #x0).
          iSplit; [done|].
          iSplit; [done|].
          simplify_eq.
          iSplit; done.
  Qed.

  Lemma gwp_pop_retrieve_proof_list (l : list string) (v : string) E s :
    G{{{ ⌜is_retrieve_proof_list l (SOMEV #v)⌝ }}}
      (parse_retrieve_proof merkle_ser) #v @ s; E
    {{{ w, RET w; ⌜∃ (h : string) (l' : list string) (v' : val),
            w = InjRV (#h, v') ∧ (l = h :: l')∧
              is_retrieve_proof_list l' v'⌝ }}} ? gwp_laters g.
  Proof.
    iIntros (Φ) "%is_retrieve_list HΦ".
    rewrite /parse_retrieve_proof.
    gwp_pures.
    destruct l; [by simpl in is_retrieve_list|].
    simpl in is_retrieve_list.
    destruct l.
    - destruct is_retrieve_list as [s1 [? Hser]]. simplify_eq.
      gwp_apply (s_deser_complete); [done|].
      iIntros ([]). gwp_pures.
      iApply "HΦ".
      destruct! Hser; simplify_eq.
      destruct! H3; simplify_eq.
      iExists _, _, _. iModIntro.
      iSplit; done.
    - destruct is_retrieve_list as [lv [s2 [s3 [? [? [Hser is_retrieve_list]]]]]]. simplify_eq.
      gwp_apply (s_deser_complete); [done|].
      iIntros ([]). gwp_pures.
      iApply "HΦ".
      destruct! Hser; simplify_eq.
      destruct! H3; simplify_eq.
      destruct! H6; destruct! H7; simplify_eq.
      iExists _, _, _. iModIntro.
      iSplit; done.
  Qed.

  Lemma gwp_deserialize_list_proof (v lv: val) (l': list val) (l: list string) E s :
    is_retrieve_proof_list l v → is_list l' lv →
    G{{{ ⌜True⌝ }}}
      deserialize_list_proof v lv @ s ; E
    {{{ w, RET w; ⌜∃ (l'' ret_l: list val) (w': val),
                      w = SOMEV w' ∧ ret_l = (fun (x : string) => #x) <$> l ∧
                        is_list l'' w' ∧ l'' = (rev ret_l) ++ l'⌝ }}} ? gwp_laters g.
  Proof.
    iIntros (is_ret_list is_list_init).
    iIntros (Φ) "%_ HΦ".
    iInduction l as [|h l] "IH" forall (lv l' Φ v is_ret_list is_list_init) "HΦ".
    - rewrite /deserialize_list_proof.
      simpl in is_ret_list. simplify_eq.
      destruct l'.
      + simpl in is_list_init. simplify_eq.
        gwp_pures.
        iApply "HΦ". by iExists [], [], NONEV.
      + simpl in is_list_init.
        destruct is_list_init as [lv' [-> is_list_init]].
        gwp_pures.

        iApply "HΦ".
        iExists (v :: l'), [], _. iModIntro.
        repeat (iSplit; [done|]).
        iSplit; [|by simplify_list_eq].
        iPureIntro.
        simpl. by exists lv'.

   - rewrite /deserialize_list_proof.
     simpl in is_ret_list.
     destruct l.
     + destruct is_ret_list as [s'' [-> Hser]].
       gwp_pures.

       fold deserialize_list_proof.

       gwp_bind (parse_retrieve_proof _ _).
       iApply gwp_pop_retrieve_proof_list.
       { iPureIntro.
         instantiate (1 := [h]).
         simpl. by exists s''. }

       iModIntro.
       iIntros (w) "(% & % & % & -> & %Hl & %is_ret_list)".
       simplify_list_eq.

       gwp_pures.
       gwp_bind (list_cons _ _).
       iApply (gwp_list_cons #h0 l' lv E s); [done|].

       iModIntro. iIntros (v is_list_next).

       iApply ("IH"); [done| done| ].
       iModIntro. iIntros (w H1).

       iApply "HΦ".

       destruct H1 as [? [? [? [? [? [? ?]]]]]].
       simplify_eq. iExists _, _, _.
       iSplit; done.

     + destruct is_ret_list as [? [? [? [-> [-> [Hser ?]]]]]].
       gwp_pures.

       fold deserialize_list_proof.

       gwp_bind (parse_retrieve_proof _ _).
       iApply gwp_pop_retrieve_proof_list.
       { iPureIntro.
         instantiate (1 := (h :: s0 :: l)).
         simpl. by exists x, x0, (InjRV #x0). }

       iModIntro. iIntros (v is_list_next).
       destruct is_list_next as [? [? [? [-> [? ?]]]]].
       simplify_list_eq.
       gwp_pures.

       gwp_bind (list_cons _ _).
       iApply (gwp_list_cons #x1 l' lv E s); [done|].

       iModIntro. iIntros (v is_list_next).

       iApply "IH"; [done| done| ].
       iModIntro. iIntros (w ?).

       iApply "HΦ".
       destruct H1 as [? [? [? [? [? [? ?]]]]]].
       simplify_eq. simplify_list_eq.

       iExists _, _, x5.
       iSplit; last first.
       { iSplit; [done|]. iPureIntro.
         instantiate (1 := (rev ((λ x : string, #x) <$> l) ++ #s0 :: #x1 :: l')).
         simplify_list_eq. done. }

       done.
  Qed.

End retrieve_proof_specs.

Section semantic.
  Context `{!authG Σ}.

  Definition lrel_path : kindO Σ (⋆)%kind := LRel (λ v1 v2 v3,
    ∃ (l : list (() + ())), ⌜is_list l v1⌝ ∗ ⌜is_list l v2⌝ ∗ ⌜is_list l v3⌝)%I.

  Definition merkle_retrieve_ctx {Θ} (Δ : ctxO Σ Θ) : ctxO Σ (Θ ▹ ⋆ ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆))%kind :=
    auth_ctx (ext Δ lrel_path).

  Lemma refines_path Θ Δ Γ :
    ⊢ { (Θ ▹ ⋆ ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆))%kind ; merkle_retrieve_ctx Δ; Γ }
      ⊨ path ≤log≤ path ≤log≤ path : t_path.
  Proof.
    iIntros (vs) "#Hvs". iIntros (????) "Hv Hi".
    rewrite ![subst_map _ _]/=.
    wp_pures. iModIntro. iFrame.
    rewrite /lrel_car/=.
    iExists _,_,_,_,_,_. do 3 (iSplit; [done|]).
    iSplit; last first.
    { iIntros (v1 v2 v3) "!# /= (% & %Hv1 & %Hv2 & %Hv3)".
      iIntros (????) "Hv Hi".
      rewrite /path_pop.
      i_pures; v_pures; wp_pures.
      i_bind (list_head _).
      iMod (gwp_list_head_opt (g := gwp_spec_ideal) ⊤ _ l () (λ w, ⌜w = $(hd_error l)⌝)%I
             with "[//] [] [$Hi //]") as (?) "[Hi ->]".
      { by iIntros "!>" (?). }
      v_bind (list_head _).
      iMod (gwp_list_head_opt (g:= gwp_spec_verifier) ⊤ _ l () (λ w, ⌜w = $(hd_error l)⌝)%I
             with "[] [] [$Hv //]") as (?) "[Hv ->]"; [done| |].
      { by iIntros "!>" (?). }
      wp_apply gwp_list_head; [done|].
      rewrite /list_tail.
      iIntros (? [[-> ->] | (d & l' & -> & ->)]) "/=".
      { i_pures; v_pures; wp_pures. iFrame. iModIntro. iExists _,_,_. eauto. }
      destruct Hv1 as (w1 & -> & Hw1), Hv2 as (w2 & -> & Hw2), Hv3 as (w3 & -> & Hw3).
      i_pures; v_pures; wp_pures. iFrame. iModIntro.
      iExists _, _, _. iRight. do 3 (iSplit; [done|]).
      iExists _, _, _, _, _, _. do 3 (iSplit; [done|]).
      iSplit; [|iFrame "%"].
      iExists _, _, _. destruct d; eauto. }
    iExists _, _, _, _, _, _. do 3 (iSplit; [done|]).
    iSplit; last first.
    { iIntros (v1 v2 v3) "!# /= (% & %Hv1 & %Hv2 & %Hv3)". iIntros (????) "Hv Hi".
      rewrite /path_right.
      i_pures. v_pures. wp_pures.
      iMod (gwp_list_cons (g:= gwp_spec_ideal) (inr tt) l _ ⊤ () (λ w, ⌜is_list ((inr tt) :: l) w⌝)%I
             with "[//] [] [$Hi //]") as (?) "[Hi %]".
      { by iIntros "!>" (?). }
      iMod (gwp_list_cons (g:= gwp_spec_verifier) (inr tt) l _ ⊤ () (λ w, ⌜is_list ((inr tt) :: l) w⌝)%I
             with "[] [] [$Hv //]") as (?) "[Hv %]"; [done| |].
      { by iIntros "!>" (?). }
      wp_apply (gwp_list_cons (inr tt) l); [done|].
      iIntros (??). iFrame. by iExists (_ :: _). }
    iExists _, _, _, _, _, _. do 3 (iSplit; [done|]).
    iSplit; last first.
    { iIntros (v1 v2 v3) "!# /= (% & %Hv1 & %Hv2 & %Hv3)". iIntros (????) "Hv Hi".
      rewrite /path_left.
      i_pures. v_pures. wp_pures.
      iMod (gwp_list_cons (g:= gwp_spec_ideal) (inl tt) l _ ⊤ () (λ w, ⌜is_list ((inl tt) :: l) w⌝)%I
             with "[//] [] [$Hi //]") as (?) "[Hi %]".
      { by iIntros "!>" (?). }
      iMod (gwp_list_cons (g:= gwp_spec_verifier) (inl tt) l _ ⊤ () (λ w, ⌜is_list ((inl tt) :: l) w⌝)%I
             with "[] [] [$Hv //]") as (?) "[Hv %]"; [done| |].
      { by iIntros "!>" (?). }
      wp_apply (gwp_list_cons (inl tt) l); [done|].
      iIntros (??). iFrame. by iExists (_ :: _). }
    by iExists [].
  Qed.
  
  Lemma wp_final_append_retrieve (v lv : val) (l : list string) :
    is_retrieve_proof_list l v → (v = NONEV ∨ (∃ w: val, v = SOMEV w)) →
    ((∃ s: string, lv = InjLV #s) ∨ (∃ s: string, lv = InjRV (InjLV #s)) ∨
       (∃ s1 s2: string, lv = InjRV (InjRV (#s1, #s2)))) →
    {{{ ⌜True⌝ }}}
      (make_retrieve_proof list_first_ser) lv v
      {{{ v', RET v'; ⌜∃ s: string, v' = #s ∧
                         ((some_retrieve_proof l lv s ∧ (∃ s1: string, lv = InjLV #s1)) ∨
                            (none_retrieve_proof l lv s ∧ ((∃ s: string, lv = InjRV (InjLV #s)) ∨
       (∃ s1 s2: string, lv = InjRV (InjRV (#s1, #s2))))))⌝ }}}.
  Proof.
    iIntros (?????) "HΦ".
    wp_rec. wp_pures. destruct H0 as [-> | [? ->]].
    - wp_pures.
      destruct l; last first.
      { simpl in H. destruct l.
        { destruct H as [? [? ?]]. done. }
        { destruct H as [? [? [? [? ?]]]]. done. } }        
      wp_apply s_ser_spec.
      { iExists _. iLeft.
        iSplit; [done|].
        destruct H1 as [[? ->]| [[? ->] | [? [? ->]]]].
        + iExists _. iLeft. iSplit; [done|].
          by iExists _.
        + iExists _. iRight. iSplit; [done|].
          iExists _. iLeft. iSplit; [done|].
          by iExists _.
        + iExists _. iRight. iSplit; [done|].
          iExists _. iRight. iSplit; [done|].
          iExists _, _. iSplit; [done|].
          iSplit; by iExists _. }
      iIntros (s ?).
      iApply "HΦ".
      iExists _. iSplit; [done|].
      destruct H1 as [[? ->]| [[? ->] | [? [? ->]]]]; eauto.
      + iRight. iSplit. { iSimpl. eauto. }
        eauto.
      + iRight. iSplit. { iSimpl. eauto. }
        eauto.
    - wp_pures.
      destruct l.
      { simpl in H. done. }
      wp_apply s_ser_spec.
      { iExists _. iRight. iSplit; [done|].
        iExists _, _. iSplit; [done|].
        iSplit. destruct H1 as [[? ->]| [[? ->] | [? [? ->]]]].
        + iExists _. iLeft. iSplit; [done|].
          by iExists _.
        + iExists _. iRight. iSplit; [done|].
          iExists _. iLeft. iSplit; [done|].
          by iExists _.
        + iExists _. iRight. iSplit; [done|].
          iExists _. iRight. iSplit; [done|].
          iExists _, _. iSplit; [done|].
          iSplit; by iExists _.
        + simpl in H. destruct l.
          { destruct H as [? [? ?]]. simplify_eq.
            by iExists _. }
          { destruct H as [? [? [? [? ?]]]]. simplify_eq.
            by iExists _. } }
      iIntros (s0 ?). iApply "HΦ".
      iExists _. iSplit; [done|].
      destruct H1 as [[? ->]| [[? ->] | [? [? ->]]]].
      + iLeft. simpl in H. destruct l.
        { destruct H as [? [? ?]]. iSplit; [|eauto].
          iExists x1. simplify_eq.
          iSplit; [done|]. iSimpl. eauto. }
        { destruct H as [? [? [? [? [? [? ?]]]]]]. iSplit; [|eauto].
          iExists x1. simplify_eq.
          iSplit; [done|]. iSimpl. iExists x1, x2, _.
          repeat (iSplit; [done|]). simpl in H4. done. }
      + iRight. simpl in H. destruct l.
        { destruct H as [? [? ?]]. iSplit; [|eauto].
          iExists x1. simplify_eq.
          iSplit; [done|]. iSimpl. eauto. }  
        { destruct H as [? [? [? [? [? [? ?]]]]]]. iSplit; [|eauto].
          iExists x1. simplify_eq.
          iSplit; [done|]. iSimpl. iExists x1, x2, _.
          repeat (iSplit; [done|]). simpl in H4. done. }
      + iRight. simpl in H. destruct l.
        { destruct H as [? [? ?]]. iSplit; [|eauto].
          iExists x2. simplify_eq.
          iSplit; [done|]. iSimpl. eauto. }  
        { destruct H as [? [? [? [? [? [? ?]]]]]]. iSplit; [|eauto].
          iExists x2. simplify_eq.
          iSplit; [done|]. iSimpl. iExists x2, x3, _.
          repeat (iSplit; [done|]). simpl in H4. done. }
  Qed.        
        
  (* As for the security proof, this lemma simply unfolds the t_tree_auth
     definition. We state this separately to speed-up compilation.
   *)
  Lemma t_tree_auth_unfold Θ (Δ : ctxO Σ Θ) v1 v2 v3 :
    ⟦ t_tree_auth ⟧ (merkle_retrieve_ctx Δ) v1 v2 v3 ≡
        (∃ (t : evi_type) (a1 a2 : val) (s : string),
          ⌜v1 = (a1, #(hash s))%V⌝ ∗
          ⌜s_is_ser (evi_type_ser t) a2 s⌝ ∗ ⌜v2 = #(hash s)⌝ ∗
          hashed s ∗ ▷ (lrel_sum lrel_string
                          (lrel_prod
                             (⟦ t_tree_auth ⟧ (merkle_retrieve_ctx Δ))
                             (⟦ t_tree_auth ⟧ (merkle_retrieve_ctx Δ)))) a1 a2 v3)%I.
  Proof.
    rewrite /t_tree_auth.
    rewrite /lrel_car /=.
    do 12 f_equiv.
    epose (f := (λne A : lrelC Σ, lrel_sum lrel_string (lrel_prod (lrel_auth A) (lrel_auth A)))
             : kindO Σ ⋆ -n> kindO Σ ⋆).
    replace (interp_rec _) with (interp_rec f) at 1; last first.
    { rewrite /f //=. }
    setoid_rewrite (interp_rec_unfold f).
    done.
  Qed.

  (* This lemma gives the postconditions one obtains after running the prover
     and the ideal versions of the code. The verifier is treated separately,
     as the prophecy variable can only be resolved after the prover
     completely steps through its auxillary function.

     The postconditions reflect the three cases that arise.
   *)
  Lemma prover_retrieve_aux_spec Θ (Δ : ctxO Σ Θ) :
    ∀ ti Ki (l_path: list (()+())) (l_proof: list string) (tree_v: string)
      (tree_p tree_i path_i path_p r_proof: val),
      is_list l_path path_p → is_list l_path path_i →
      is_retrieve_proof_list l_proof r_proof →
      ⟦ t_tree_auth ⟧ (merkle_retrieve_ctx Δ) tree_p #tree_v tree_i -∗
      {{{ spec_ideal ti (fill Ki (retrieve_ideal_aux path_i tree_i)) }}}
        retrieve_magic_prover_aux path_p tree_p r_proof
      {{{ (ret_proof: string) (result: val), RET (#ret_proof, result);
          ∃ (proof_head start_hash: string) (l_proof' l_sub_proof: list string),
            ⌜l_proof' = l_sub_proof ++ l_proof⌝ ∗
              ((⌜result = SOMEV #proof_head ∧ (* Case 1: some result *)
                   (start_hash = (hash (inl_ser_str (string_ser_str proof_head)))) ∧
                   length l_sub_proof = length l_path ∧
                   some_retrieve_proof l_proof' (InjLV #proof_head) ret_proof ∧
                   make_hash (rev l_sub_proof) l_path start_hash = tree_v⌝ ∗
                  spec_ideal ti (fill Ki (SOMEV #proof_head))) ∨
                 (⌜∃ (disc_path keep_path: list (()+())) (last_val: val),
                      l_path = keep_path ++ disc_path ∧ result = NONEV ∧
                        length keep_path = length l_sub_proof ∧
                        none_retrieve_proof l_proof' last_val ret_proof ∧
                        ((∃ proof_head2: string, (* Case 3: shorter path *)
                             start_hash = (hash
                                             (inr_ser_str (prod_ser_str
                                                (string_ser_str proof_head) (string_ser_str proof_head2)))) ∧
                               last_val = InjRV (InjRV (#proof_head, #proof_head2)) ∧ disc_path = []) ∨
                           (start_hash = (hash (inl_ser_str (string_ser_str proof_head))) ∧ (* Case 2 *)
                              last_val = InjRV (InjLV #proof_head) ∧ disc_path ≠ [])) ∧
                        (* In case 2, there is some part of the path (disc_path) that is ignored *)
                        make_hash (rev l_sub_proof) keep_path start_hash = tree_v⌝ ∗
                    spec_ideal ti (fill Ki (NONEV))))}}}%I.
  Proof.
    iIntros (?????????? is_path_p is_path_i is_proof) "#HTree".
    iIntros (Φ) "!# Hi HPost".
    iInduction (l_path) as [|h t_path] "IH"
                             forall (Φ path_p path_i l_proof tree_v tree_p tree_i r_proof is_path_p
                                       is_path_i is_proof)
                                    "Hi HPost HTree".
    - rewrite /retrieve_magic_prover_aux /path_pop.
      wp_pures.
      wp_apply (gwp_list_head_nil); [done|].
      iIntros (_). wp_pures.
      fold path_pop. fold retrieve_magic_prover_aux.
      iEval (rewrite t_tree_auth_unfold) in "HTree".
      iDestruct "HTree" as (t_tree tree_p_sum tree_v_val tree_v_string)
                             "(-> & %Hser & % & #HashTree & #HTree)"; simplify_eq.
      wp_pures.
      iDestruct "HTree" as (tree_p tree_v tree_i_sum) "[(-> & -> & -> & HLeaf)|(-> & -> & -> & HNode)]".
      + rewrite /retrieve_ideal_aux /path_pop. (* Case 1 base *)
        i_pures.
        i_bind (list_head _).
        iMod (gwp_list_head_nil (g:= gwp_spec_ideal) ⊤ path_i () (λ w, ⌜w=NONEV⌝)%I
               with "[//] [] [$Hi //]") as (v) "[Hi ->]".
        { by iIntros "!>" (?). }
        iSimpl in "Hi". i_pures.
        iDestruct "HLeaf" as (s) "(-> & -> & ->)".
        wp_pures. wp_apply wp_final_append_retrieve.
        { done. }
        { destruct l_proof.
          { simpl in is_proof. eauto. }
          { simpl in is_proof. right.
            destruct l_proof.
            { destruct is_proof as [? [? ?]].
              simplify_eq. by exists #x. }
            { destruct is_proof as [? [? [? [? ?]]]].
              simplify_eq. by exists #x. } } }
        { eauto. } { done. }

        iIntros (? H). destruct H as [? [-> ?]].
        wp_pures; iModIntro; iApply "HPost".
        destruct H as [[? ?]|[? ?]]; last first.
        { destruct H0 as [[? ?]|[? [? ?]]]; done. }            
        iExists s, _, _, [].
        iSplit; [done|]. iFrame "#".
        iLeft.
        iSplit; [|done].
        repeat (iSplit; [done|]).
        iPureIntro. simpl.
        destruct t_tree; destruct! Hser; simplify_eq.
        destruct t_tree1; destruct! H4; simplify_eq.
        done.

      + rewrite /retrieve_ideal_aux /path_pop. (* Case 3 base *)
        i_pures.
        i_bind (list_head _).
        iMod (gwp_list_head_nil (g:= gwp_spec_ideal) ⊤ path_i () (λ w, ⌜w=NONEV⌝)%I
               with "[//] [] [$Hi //]") as (v) "[Hi ->]".
        { by iIntros "!>" (?). }
        iSimpl in "Hi". i_pures.
        iDestruct "HNode" as (child1_p child1_v child1_i child2_p child2_v child2_i) "(-> & -> & -> & #HChild1Auth & #HChild2Auth)".
        iPoseProof "HChild1Auth" as (t_child1 child1_p_sum child1_v_val child1_v_string)
                                      "(-> & %Hserc1 & % & #HashChild1 & #HChild1)"; simplify_eq.
        iPoseProof "HChild2Auth" as (t_child2 child2_p_sum child2_v_val child2_v_string)
                                      "(-> & %Hserc2 & % & #HashChild2 & #HChild2)"; simplify_eq.
        rewrite -/interp. wp_pures.
        wp_apply wp_final_append_retrieve.
        { done. }
        { destruct l_proof.
          { simpl in is_proof. eauto. }
          { simpl in is_proof. right.
            destruct l_proof.
            { destruct is_proof as [? [? ?]].
              simplify_eq. by exists #x. }
            { destruct is_proof as [? [? [? [? ?]]]].
              simplify_eq. by exists #x. } } }
        { eauto. } { done. }

        iIntros (? H). destruct H as [? [-> ?]].
        destruct H as [[? ?]|[? ?]].
        { destruct H0 as [? ?]. done. }
        destruct H0 as [[? ?]|[? [? ?]]]; [done|]. simplify_eq.
        wp_pures; iModIntro; iApply "HPost".
        iExists _, _, _, [].
        iSplit; [done|].
        iFrame "#". iRight.
        iSplit; [|done].
        iExists [], [], _.
        repeat (iSplit; [done|]).
        iSplit.
        { iLeft. iExists _. repeat (iSplit; [|done]).
          done. }
        iSimpl.
        destruct t_tree; destruct! Hser; simplify_eq.
        destruct t_tree2; destruct! H3; simplify_eq.
        destruct t_tree2_1; destruct! H6; simplify_eq.
        destruct t_tree2_2; destruct! H7; simplify_eq.
        done.

    - rewrite /retrieve_magic_prover_aux /path_pop.
      wp_pures.
      wp_apply (gwp_list_head); [done|].
      iIntros (path_head [[Hf ->] | (?&?&Ht&->)]); [done|]. simplify_eq.
      fold path_pop; fold retrieve_magic_prover_aux.
      iEval (rewrite t_tree_auth_unfold) in "HTree".
      iDestruct "HTree" as (t_tree tree_p_sum tree_v_val tree_v_string)
                             "(-> & %Hser & % & #HashTree & #HTree)"; simplify_eq.
      wp_pure.
      iDestruct "HTree" as (tree_p tree_v tree_i_sum) "[(-> & -> & -> & HLeaf)|(-> & -> & -> & HNode)]".
      + destruct x. (* Case 2 base *)
        (* Destruct on whether the path is left or right. *)
        * wp_pures.
          wp_apply (gwp_list_tail); [done|].
          iIntros (tail_p is_tail_p).
          wp_pures.
          rewrite /retrieve_ideal_aux /path_pop.
          i_pures.
          i_bind (list_head _).
          iMod (gwp_list_head_cons (g:= gwp_spec_ideal) ⊤ path_i (inl u) x0 () (λ w, ⌜w=SOMEV (inject (inl u))⌝)%I
                 with "[//] [] [$Hi //]") as (v) "[Hi ->]".
          { by iIntros "!>" (?). }
          iSimpl in "Hi". i_pures.
          i_bind (list_tail _).
          iMod (gwp_list_tail (g:= gwp_spec_ideal) ⊤ path_i (inl u::x0) () (λ w, ⌜is_list x0 w⌝)%I
                 with "[//] [] [$Hi //]") as (path_tail_i) "[Hi %is_list_tail_path_i]".
          { by iIntros "!>" (?). }
          iSimpl in "Hi". i_pures.
          iDestruct "HLeaf" as (?) "(-> & -> & ->)".

          wp_apply wp_final_append_retrieve.
          { done. }
          { destruct l_proof.
            { simpl in is_proof. eauto. }
            { simpl in is_proof. right.
              destruct l_proof.
              { destruct is_proof as [? [? ?]].
                simplify_eq. by exists #x. }
              { destruct is_proof as [? [? [? [? ?]]]].
                simplify_eq. by exists #x. } } }
          { eauto. } { done. }

          iIntros (? H). destruct H as [? [-> ?]].
          destruct H as [[? ?]|[? ?]].
          { destruct H0 as [? ?]. done. }
          destruct H0 as [[? ?]|[? [? ?]]]; [|done]. simplify_eq.
          wp_pures; iModIntro; iApply "HPost".
          iExists _, _, _, [].
          iSplit; [done|].
          iFrame "#". iRight.
          iSplit; [|done].
          iExists _, [], _.
          repeat (iSplit; [done|]).
          iSplit.
          { iRight. eauto. }
          simpl.
          destruct t_tree; destruct! Hser; simplify_eq.
          destruct t_tree1; destruct! H3; simplify_eq.
          done.         

        * wp_pures.
          wp_apply (gwp_list_tail); [done|].
          iIntros (tail_p is_tail_p).
          wp_pures.
          rewrite /retrieve_ideal_aux /path_pop.
          i_pures.
          i_bind (list_head _).
          iMod (gwp_list_head_cons (g:= gwp_spec_ideal) ⊤ path_i (inr u) x0 () (λ w, ⌜w=SOMEV (inject (inr u))⌝)%I
                 with "[//] [] [$Hi //]") as (v) "[Hi ->]".
          { by iIntros "!>" (?). }
          iSimpl in "Hi".
          i_pures.
          i_bind (list_tail _).
          iMod (gwp_list_tail (g:= gwp_spec_ideal) ⊤ path_i (inr u::x0) () (λ w, ⌜is_list x0 w⌝)%I
                 with "[//] [] [$Hi //]") as (path_tail_i) "[Hi %is_list_tail_path_i]".
          { by iIntros "!>" (?). }
          iSimpl in "Hi".
          i_pures.

          iDestruct "HLeaf" as (?) "(-> & -> & ->)".

          wp_apply wp_final_append_retrieve.
          { done. }
          { destruct l_proof.
            { simpl in is_proof. eauto. }
            { simpl in is_proof. right.
              destruct l_proof.
              { destruct is_proof as [? [? ?]].
                simplify_eq. by exists #x. }
              { destruct is_proof as [? [? [? [? ?]]]].
                simplify_eq. by exists #x. } } }
          { eauto. } { done. }

          iIntros (? H). destruct H as [? [-> ?]].
          destruct H as [[? ?]|[? ?]].
          { destruct H0 as [? ?]. done. }
          destruct H0 as [[? ?]|[? [? ?]]]; [|done]. simplify_eq.
          wp_pures. iModIntro. iApply "HPost".
          iExists _, _, _, [].
          iSplit; [done|].
          iFrame "#". iRight.
          iSplit; [|done].
          iExists _, [], _.
          repeat (iSplit; [done|]).
          iSplit.
          { iRight. eauto. }
          simpl.
          destruct t_tree; destruct! Hser; simplify_eq.
          destruct t_tree1; destruct! H3; simplify_eq.
          done.

      + destruct x. (* all cases are possible depending on the recursive call. *)
        * wp_pures.
          wp_apply (gwp_list_tail); [done|].
          iIntros (tail_p is_tail_p).
          iDestruct "HNode" as (child1_p child1_v child1_i child2_p child2_v child2_i) "(-> & -> & -> & #HChild1Auth & #HChild2Auth)".
          iPoseProof "HChild1Auth" as (t_child1 child1_p_sum child1_v_val child1_v_string)
                                        "(-> & %Hserc1 & % & #HashChild1 & #HChild1)"; simplify_eq.
          iPoseProof "HChild2Auth" as (t_child2 child2_p_sum child2_v_val child2_v_string)
                                        "(-> & %Hserc2 & % & #HashChild2 & #HChild2)"; simplify_eq.
          rewrite -/interp.
          wp_pures.

          rewrite /retrieve_ideal_aux /path_pop.
          i_pures.
          i_bind (list_head _).
          iMod (gwp_list_head_cons (g:= gwp_spec_ideal) ⊤ path_i (inl u) x0 () (λ w, ⌜w=SOMEV (inject (inl u))⌝)%I
                 with "[//] [] [$Hi //]") as (v) "[Hi ->]".
          { by iIntros "!>" (?). }
          iSimpl in "Hi". i_pures.
          i_bind (list_tail _).
          iMod (gwp_list_tail (g:= gwp_spec_ideal) ⊤ path_i (inl u::x0) () (λ w, ⌜is_list x0 w⌝)%I
                 with "[//] [] [$Hi //]") as (path_tail_i) "[Hi %is_list_tail_path_i]".
          { by iIntros "!>" (?). }
          iSimpl in "Hi".
          fold path_pop. fold retrieve_ideal_aux.
          i_pures.

          wp_bind (make_retrieve_proof _ _ _).
          wp_apply (gwp_append_retrieve_proof_list with "[//]").
          iIntros (r_proof' is_proof'). wp_pures.

          iApply ("IH" with "[] [] [] Hi [HPost] HChild1Auth").
          { done. }
          { iPureIntro. apply is_list_tail_path_i. }
          { done. }
          iNext.

          iIntros (ret_proof result) "(% & % & % & % & HTemp)".
          iDestruct "HTemp" as (Hlproof) "[HSome|HNone]".
          -- iApply "HPost".
             iDestruct "HSome" as "((-> & -> & %Hl & %Hsomeres & %Hvalidhash) & Hi)".
             iExists proof_head, _, l_proof', (l_sub_proof ++ [(hash child2_v_string)]).
             iSplit.
             { simplify_eq. iPureIntro.
               assert (hash child2_v_string :: l_proof = [hash child2_v_string] ++ l_proof).
               { done. }
               rewrite H. symmetry. rewrite app_assoc //. }
             iFrame "#".
             iLeft. iFrame.
             repeat (iSplit; [done|]).
             iPureIntro. rewrite distr_rev. simpl.
             unfold some_retrieve_proof in Hsomeres.
             destruct l_proof'.
             { destruct l_sub_proof; simpl in Hlproof; discriminate. }
             rewrite Hvalidhash.
             destruct t_tree; destruct! Hser; simplify_eq.
             destruct t_tree2; destruct! H2; simplify_eq.
             destruct t_tree2_1; destruct! H5; simplify_eq.
             destruct t_tree2_2; destruct! H6; simplify_eq.
             rewrite app_length. split. { simpl. lia. }
             done.
          -- iApply "HPost".
             iDestruct "HNone" as "((% & % & % & -> & -> & %Hl & %Hnoneres & %Hval & %Hvalidhash) & Hi)".
             iExists proof_head, start_hash, l_proof', (l_sub_proof ++ [(hash child2_v_string)]).
             iSplit.
             { simplify_eq. iPureIntro.
               assert (hash child2_v_string :: l_proof = [hash child2_v_string] ++ l_proof).
               { done. }
               rewrite H. symmetry. rewrite app_assoc //. }
             iFrame "#".
             iRight. iFrame. iExists _, (inl u :: keep_path), _.
             repeat (iSplit; [done|]).
             iSplit.
             { iPureIntro.
               simpl. rewrite app_length.
               simpl. lia. }
             destruct Hvalidhash.
             iSplit; [done|].
             iPureIntro. rewrite distr_rev. simpl.
             destruct t_tree; destruct! Hser; simplify_eq.
             destruct t_tree2; destruct! H2; simplify_eq.
             destruct t_tree2_1; destruct! H5; simplify_eq.
             destruct t_tree2_2; destruct! H6; simplify_eq.
             done.

        * wp_pures.
          wp_apply (gwp_list_tail); [done|].
          iIntros (tail_p is_tail_p).
          iDestruct "HNode" as (child1_p child1_v child1_i child2_p child2_v child2_i) "(-> & -> & -> & #HChild1Auth & #HChild2Auth)".
          iPoseProof "HChild1Auth" as (t_child1 child1_p_sum child1_v_val child1_v_string)
                                        "(-> & %Hserc1 & % & #HashChild1 & #HChild1)"; simplify_eq.
          iPoseProof "HChild2Auth" as (t_child2 child2_p_sum child2_v_val child2_v_string)
                                        "(-> & %Hserc2 & % & #HashChild2 & #HChild2)"; simplify_eq.
          wp_pures.

          rewrite /retrieve_ideal_aux /path_pop.
          i_pures.
          i_bind (list_head _).
          iMod (gwp_list_head_cons (g:= gwp_spec_ideal) ⊤ path_i (inr u) x0 () (λ w, ⌜w=SOMEV (inject (inr u))⌝)%I
                 with "[//] [] [$Hi //]") as (v) "[Hi ->]".
          { by iIntros "!>" (?). }
          iSimpl in "Hi". i_pures.
          i_bind (list_tail _).
          iMod (gwp_list_tail (g:= gwp_spec_ideal) ⊤ path_i (inr u::x0) () (λ w, ⌜is_list x0 w⌝)%I
                 with "[//] [] [$Hi //]") as (path_tail_i) "[Hi %is_list_tail_path_i]".
          { by iIntros "!>" (?). }
          iSimpl in "Hi".
          fold path_pop. fold retrieve_ideal_aux.
          i_pures.

          wp_bind (make_retrieve_proof _ _ _).
          wp_apply (gwp_append_retrieve_proof_list with "[//]").
          iIntros (r_proof' is_proof'). wp_pures.

          iApply ("IH" with "[] [] [] Hi [HPost] HChild2Auth").
          { done. }
          { iPureIntro. apply is_list_tail_path_i. }
          { done. }
          iNext.

          iIntros (ret_proof result) "(% & % & % & % & HTemp)".
          iDestruct "HTemp" as (Hlproof) "[HSome|HNone]".
          -- iApply "HPost".
             iDestruct "HSome" as "((-> & -> & %Hl & %Hsomeres & %Hvalidhash) & Hi)".
             iExists proof_head, _, l_proof', (l_sub_proof ++ [(hash child1_v_string)]).
             iSplit.
             { simplify_eq. iPureIntro.
               assert (hash child1_v_string :: l_proof = [hash child1_v_string] ++ l_proof).
               { done. }
               rewrite H. symmetry. rewrite app_assoc //. }
             iFrame "#".
             iLeft. iFrame.
             repeat (iSplit; [done|]).
             iPureIntro. rewrite distr_rev. simpl.
             unfold some_retrieve_proof in Hsomeres.
             destruct l_proof'.
             { destruct l_sub_proof; simpl in Hlproof; discriminate. }
             rewrite Hvalidhash.
             destruct t_tree; destruct! Hser; simplify_eq.
             destruct t_tree2; destruct! H2; simplify_eq.
             destruct t_tree2_1; destruct! H5; simplify_eq.
             destruct t_tree2_2; destruct! H6; simplify_eq.
             split. { rewrite app_length. simpl. lia. }
             done.
          -- iApply "HPost".
             iDestruct "HNone" as "((% & % & % & -> & -> & %Hl & %Hnoneres & %Hval & %Hvalidhash) & Hi)".
             iExists proof_head, start_hash, l_proof', (l_sub_proof ++ [(hash child1_v_string)]).
             iSplit.
             { simplify_eq. iPureIntro.
               assert (hash child1_v_string :: l_proof = [hash child1_v_string] ++ l_proof).
               { done. }
               rewrite H. symmetry. rewrite app_assoc //. }
             iFrame "#".
             iRight. iFrame. iExists _, (inr u :: keep_path), _.
             repeat (iSplit; [done|]).
             iSplit.
             { iPureIntro.
               simpl. rewrite app_length.
               simpl. lia. }
             destruct Hvalidhash.
             iSplit; [done|].
             iPureIntro. rewrite distr_rev. simpl.
             destruct t_tree; destruct! Hser; simplify_eq.
             destruct t_tree2; destruct! H2; simplify_eq.
             destruct t_tree2_1; destruct! H5; simplify_eq.
             destruct t_tree2_2; destruct! H6; simplify_eq.
             done.
  Qed.

  (* The verifier auxillary code is not aware of the different cases, and only
     says that the given path, proof combination computes to a target_hash.
     The < make_hash ... = ... > proposition is recursive.
   *)
  Lemma refines_verifier_retrieve_aux :
    ∀ t K (l_path: list (()+())) (l_proof: list val) (l_proof_s: list string)
      (cur_hash target_hash: string) (path_v r_proof: val),
      ⌜is_list l_path path_v⌝ ∗ 
        ⌜is_list l_proof r_proof⌝ ∗ ⌜(length l_proof = length l_path)⌝ ∗
        ⌜l_proof = (fun (x : string) => #x) <$> l_proof_s⌝ ∗
        ⌜(make_hash l_proof_s l_path cur_hash = target_hash)⌝ ∗
        spec_verifier t (fill K (retrieve_magic_verifier_aux path_v r_proof #cur_hash))
        ⊢ |={⊤}=> ∃ (tree_hash: string),
            spec_verifier t (fill K (SOMEV #tree_hash)) ∗
              ⌜(tree_hash = target_hash)⌝.
  Proof.
    iIntros (?????????) "(%path_list & %proof_list & %Hlength & %Hequi &
                             %Hvalidhash & Hv)".

    iInduction (l_path) as [|h t_path] "IH"
                             forall (K l_proof l_proof_s cur_hash target_hash path_v r_proof
                                       Hequi path_list proof_list Hlength Hvalidhash)
                                    "Hv".
    - rewrite /retrieve_magic_verifier_aux /path_pop. v_pures.

      v_bind (list_head _).
      iMod (gwp_list_head_nil ⊤ path_v () (λ w, ⌜w=NONEV⌝)%I
             with "[//] [] [$Hv //]") as (v) "[Hv ->] /=".
      { by iIntros "!>" (?). }
      v_pures.

      fold path_pop. fold retrieve_magic_verifier_aux.

      simpl in Hlength. destruct l_proof; [|done].

      v_bind (list_head _).
      iMod (gwp_list_head_nil ⊤ r_proof () (λ w, ⌜w=NONEV⌝)%I
             with "[//] [] [$Hv //]") as (v) "[Hv ->] /=".
      { by iIntros "!>" (?). } v_pures.

      iFrame. simplify_list_eq. done.

    - rewrite /retrieve_magic_verifier_aux /path_pop. v_pures.

      v_bind (list_head _).
      iMod (gwp_list_head_cons ⊤ path_v h t_path () (λ w, ⌜w=SOMEV (inject h)⌝)%I
             with "[//] [] [$Hv //]") as (v) "[Hv ->] /=".
      { by iIntros "!>" (?). } v_pures.

      fold path_pop. fold retrieve_magic_verifier_aux.

      v_bind (list_tail _).
      iMod (gwp_list_tail ⊤ path_v (h::t_path) () (λ w, ⌜is_list t_path w⌝)%I
             with "[//] [] [$Hv //]") as (v) "[Hv %path_tail_list] /=".
      { by iIntros "!>" (?). } v_pures.

      simpl in Hlength.
      destruct l_proof; [done|].

      v_bind (list_head _).
      iMod (gwp_list_head_cons ⊤ r_proof v0 l_proof () (λ w, ⌜w=SOMEV (inject v0)⌝)%I
             with "[//] [] [$Hv //]") as (p) "[Hv ->] /=".
      { by iIntros "!>" (?). } v_pures.

      v_bind (list_tail _).
      iMod (gwp_list_tail ⊤ r_proof (v0::l_proof) () (λ w, ⌜is_list l_proof w⌝)%I
             with "[//] [] [$Hv //]") as (p) "[Hv %proof_tail_list] /=".
      { by iIntros "!>" (?). } v_pures.

      v_bind (retrieve_magic_verifier_aux _ _ _).
      destruct l_proof_s; [simplify_list_eq|].
      simpl in Hlength. simplify_eq.
      iMod ("IH" with "[] [//] [//] [//] [//] Hv") as (subtree_hash) "(Hv & ->) /=".
      { instantiate (1 := l_proof_s). simplify_list_eq. done. }
      v_pures.      
      destruct h.
      + v_pures.

        v_bind (s_serializer _ _).
        iMod (s_ser_spec merkle_ser ⊤ (InjRV (#(make_hash l_proof_s t_path cur_hash), v0)) ()
                (λ v, ⌜∃ s': string, v=#s' ∧
                     s_is_ser merkle_ser (InjRV (#(make_hash l_proof_s t_path cur_hash), v0)) s'⌝)%I
               with "[] [] [$Hv //]") as (?) "[Hv %Hser] /=".
        { iModIntro. iExists _. iRight.
          iSplit; [done|]. iExists _, _.
          iSplit; [done|]. simplify_list_eq. iSplit; by iExists _. }
        { iIntros "!>" (?) "%". iExists s0. done. }
        destruct Hser as [s' [-> Hser]].

        v_bind (Hash _).
        iMod (step_verifier_hash with "[$]") as "Hv /="; [done|].
        v_pures.

        iFrame.
        destruct! Hser; simplify_eq.
        destruct! H2; simplify_eq. simplify_list_eq.
        destruct! H5; destruct! H6; simplify_eq.
        iPureIntro.
        destruct l_proof_s; [done|].
        simpl. done. 

      + v_pures.

        v_bind (s_serializer _ _).
        iMod (s_ser_spec merkle_ser ⊤ (InjRV (v0, #(make_hash l_proof_s t_path cur_hash))) ()
                (λ v, ⌜∃ s': string, v=#s' ∧ s_is_ser merkle_ser (InjRV (v0, #(make_hash l_proof_s t_path cur_hash))) s'⌝)%I
               with "[] [] [$Hv //]") as (?) "[Hv %Hser] /=".
        { iModIntro. iExists _. iRight.
          iSplit; [done|]. iExists _, _.
          iSplit; [done|]. simplify_list_eq. iSplit; by iExists _. }
        { iIntros "!>" (?) "%". iExists s0. done. }
        destruct Hser as [s' [-> Hser]].

        v_bind (Hash _).
        iMod (step_verifier_hash with "[$]") as "Hv /="; [done|].
        v_pures.

        iFrame.
        destruct! Hser; simplify_eq.
        destruct! H2; simplify_eq. simplify_list_eq.
        destruct! H5; destruct! H6; simplify_eq.
        iPureIntro.
        destruct l_proof_s; [done|].
        simpl. done. 
  Qed.

  (* For some reason, I used "rev" instead of "reverse". However, all lemmas in the
     standard library are for "reverse".
   *)
  Lemma reverse_rev {A} (l: list A) :
    reverse l = rev l.
  Proof.
    unfold reverse. rewrite rev_alt. done.
  Qed.

  Lemma v_first_parse_retrieve (v : val) (l : list string) (s : string) :
    ∀ t K,
    ⌜(some_retrieve_proof l v s ∧ ∃ proof_head: string, v = InjLV #proof_head) ∨
      (none_retrieve_proof l v s ∧
         (∃ proof_head: string, v = InjRV (InjLV #proof_head)
                                ∨ ∃ proof_head2: string, v = InjRV (InjRV (#proof_head, #proof_head2))))⌝ ∗
      spec_verifier t (fill K ((parse_retrieve_proof list_first_ser) #s))
      ⊢ |={⊤}=> ∃ proof_v: val, spec_verifier t (fill K (InjRV (v, proof_v))) ∗
                                  ⌜is_retrieve_proof_list l proof_v⌝.
  Proof.
    iIntros (??) "(% & Hv)". v_rec t.
    v_bind (s_deserializer _ _).
    destruct H as [?|?].
    - destruct H as [? [? ->]].
      destruct l; simpl in H.
      + iMod (s_deser_complete (g := gwp_spec_verifier) list_first_ser ⊤ (InjLV (InjLV #x)) s ()
                (λ w, ⌜w = SOMEV (InjLV (InjLV #x))⌝)%I with "[//] [//] [$Hv //]") as (?) "[Hv ->]".
        iSimpl in "Hv". v_pures. iExists _.
        iModIntro. iFrame. done.
      + destruct H as [? [? ?]].
        iMod (s_deser_complete (g := gwp_spec_verifier) list_first_ser ⊤ (InjRV (InjLV #x, #x0)) s ()
                (λ w, ⌜w = SOMEV (InjRV (InjLV #x, #x0))⌝)%I with "[//] [//] [$Hv //]") as (?) "[Hv ->]".
        iSimpl in "Hv". v_pures. iExists _.
        iModIntro. iFrame. done.
    - destruct H as [? [? [->|[? ->]]]]; destruct l; simpl in H.
      + iMod (s_deser_complete (g := gwp_spec_verifier) list_first_ser ⊤ (InjLV (InjRV (InjLV #x))) s ()
                (λ w, ⌜w = SOMEV (InjLV (InjRV (InjLV #x)))⌝)%I with "[//] [//] [$Hv //]") as (?) "[Hv ->]".
        iSimpl in "Hv". v_pures. iExists _.
        iModIntro. iFrame. done.
      + destruct H as [? [? ?]].
        iMod (s_deser_complete (g := gwp_spec_verifier) list_first_ser ⊤ (InjRV (InjRV (InjLV #x), #x0)) s ()
                (λ w, ⌜w = SOMEV (InjRV (InjRV (InjLV #x), #x0))⌝)%I with "[//] [//] [$Hv //]") as (?) "[Hv ->]".
        iSimpl in "Hv". v_pures. iExists _.
        iModIntro. iFrame. done.
      + iMod (s_deser_complete (g := gwp_spec_verifier) list_first_ser ⊤ (InjLV (InjRV (InjRV (#x, #x0)))) s ()
                (λ w, ⌜w = SOMEV (InjLV (InjRV (InjRV (#x, #x0))))⌝)%I with "[//] [//] [$Hv //]") as (?) "[Hv ->]".
        iSimpl in "Hv". v_pures. iExists _.
        iModIntro. iFrame. done.
      + destruct H as [? [? ?]].
        iMod (s_deser_complete (g := gwp_spec_verifier) list_first_ser ⊤ (InjRV (InjRV (InjRV (#x, #x0)), #x1)) s ()
                (λ w, ⌜w = SOMEV (InjRV (InjRV (InjRV (#x, #x0)), #x1))⌝)%I with "[//] [//] [$Hv //]") as (?) "[Hv ->]".
        iSimpl in "Hv". v_pures. iExists _.
        iModIntro. iFrame. done.
  Qed.
    
  Lemma refines_retrieve Θ Δ Γ :
    ⊢ { (Θ ▹ ⋆ ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆))%kind ; merkle_retrieve_ctx Δ; Γ }
      ⊨ p_retrieve ≤log≤ v_retrieve ≤log≤ i_retrieve : t_retrieve.
  Proof.
    iIntros (vs) "#Hvs". iIntros (????) "Hv Hi".
    rewrite /p_retrieve /v_retrieve /i_retrieve.
    wp_pures. iModIntro. iFrame.
    iIntros (path_p path_v path_i) "!# Hpath". rewrite -/interp.
    iDestruct "Hpath" as (?) "(%is_list_path_p & %is_list_path_v & %is_list_path_i)".
    iIntros (????) "Hv Hi".
    wp_pures; v_pures; i_pures.
    iModIntro. iFrame.
    iIntros (tree_p tree_v tree_i) "!# #Htree_auth". rewrite -!/interp.
    iPoseProof "Htree_auth" as "Htree_auth'".
    iEval (rewrite t_tree_auth_unfold) in "Htree_auth".
    iDestruct "Htree_auth" as (t_tree tree_p_val tree_v_val tree_hashed -> Hser_tree ->) "(#Hash_tree & Htree)".
    iIntros (????) "Hv Hi".
    wp_pures; v_pures; i_pures.
    iModIntro. iFrame.
    iIntros (????????) "!# (Hv & Hi & [%Hprf Hp]) H".
    wp_pures; v_pures; i_pures.
    wp_apply
     (prover_retrieve_aux_spec _ _ with "Htree_auth' Hi [Hp H Hv]").
    { apply is_list_path_p. }
    { apply is_list_path_i. }
    { by instantiate (1 := []). }
    iNext.

    iIntros (??) "HPost". wp_pures.
    wp_apply (wp_resolve_proph_string with "Hp").
    iIntros (?) "(-> & Hprf)". wp_pures.
    wp_apply (gwp_list_cons (#ret_proof) [] with "[//]").
    iIntros (??). wp_pures.
    v_bind (list_head _).
    iMod (gwp_list_head (g := gwp_spec_verifier) ⊤ w (ret_proof :: _) ()
            (λ v, ⌜v = SOMEV #ret_proof⌝)%I with "[//] [] [$Hv //]") as (?) "[Hv ->]".
    { iIntros "!>" (? [[] | (?&?&?&?)]); simplify_eq. eauto. }
    iSimpl in "Hv".
    v_pures.

    v_bind (parse_retrieve_proof _ _).
    iDestruct "HPost" as (?????) "[HPost|HPost]".
    - iDestruct "HPost" as "((-> & -> & %Hl & %HSome & %Hvalidhash) & Hi)". (* Case 1 *)
      iMod (v_first_parse_retrieve (InjLV #proof_head) l_proof' ret_proof with "[$Hv]") as (?) "[Hv %is_ret_proof]".
      { iLeft. eauto. }
      iSimpl in "Hv". v_pures.

      v_bind (deserialize_list_proof _ _).
      iMod (gwp_deserialize_list_proof (g := gwp_spec_verifier) proof_v (InjLV #()) [] l_proof' ⊤ ()
              is_ret_proof _
              (λ w, ⌜∃ (l'' ret_l: list val) (w': val),
                         w = SOMEV w' ∧ 
                           ret_l = (fun (x : string) => #x) <$> l_proof' ∧
                           is_list l'' w' ∧ l'' = (rev ret_l) ++ []⌝)%I
             with "[//] [] [$Hv //]") as (?) "[Hv (% & % & % & -> & %Hretrev & %is_list_des & ->)]".
      { by iIntros "!>" (?) "%". }
      iSimpl in "Hv". v_pures. Unshelve. 2: done.

      v_bind (s_serializer _ _).
      iMod (s_ser_spec merkle_ser ⊤ (InjLV #proof_head) ()
              (λ v, ⌜∃ s': string, v=#s' ∧ s_is_ser merkle_ser (InjLV #proof_head) s'⌝)%I
             with "[] [] [$Hv //]") as (?) "[Hv %Hserin]".
      { iModIntro. iExists _. iLeft.
        iSplit; [done|]. by iExists _. }
      { iIntros "!>" (?) "%". iExists s. done. }
      iSimpl in "Hv".
      destruct Hserin as [s' [-> Hserin]].

      v_bind (Hash _).
      iMod (step_verifier_hash with "[$]") as "Hv"; [done|].
      iSimpl in "Hv".
      v_pures.

      v_bind (retrieve_magic_verifier_aux _ _ _).
      iMod (refines_verifier_retrieve_aux _ _ with "[Hv]") as (?) "(Hv & ->)".
      { iFrame.
        iSplit; [done|].
        iFrame "#". iFrame.
        iFrame "%".
        iSplit; [iPureIntro|].
        { simplify_list_eq. 
          rewrite rev_length. by rewrite length_fmap. }
        instantiate (2 := rev(l_proof')).
        simplify_list_eq.
        iPureIntro.
        split; [|done].
        rewrite rev_alt. rewrite rev_alt.
        rewrite fmap_reverse. unfold reverse. done. }
      iSimpl in "Hv". v_pures.
      { solve_vals_compare_safe. }

      destruct! Hserin; simplify_eq.
      rewrite <- reverse_rev. rewrite <- reverse_rev in Hvalidhash.
      destruct! H4; simplify_eq.
      rewrite Hvalidhash.

      iEval (rewrite bool_decide_eq_true_2 //) in "Hv". v_pures.

      v_bind (list_tail _).
      iMod (gwp_list_tail ⊤ w (ret_proof::vs') () (λ w, ⌜is_list vs' w⌝)%I
             with "[//] [] [$Hv //]") as (w'') "[Hv %rem_proof]".
      { by iIntros "!>" (?). }
      iSimpl in "Hv". v_pures.

      iApply "H".

      iFrame "% ∗".
      instantiate (1 := [ret_proof]).
      iModIntro.
      iSplit; [done|].
      iSplit; [done|].
      iExists _, _, _. iRight.
      repeat (iSplit; [done|]). by iExists _.

    - iDestruct "HPost" as "((% & % & % & -> & -> & %Hl & %HNone & %Hhead & %Hvalidhash) & Hi)".
      iMod (v_first_parse_retrieve last_val l_proof' ret_proof with "[$Hv]") as (?) "[Hv %is_ret_proof]".
      { iRight. iSplit; [done|]. iExists proof_head.
        destruct Hhead as [[? [? [? ?]]]|[? [? ?]]].
        { iRight. by iExists x. }
        { by iLeft. } }
      iSimpl in "Hv". v_pures.

      v_bind (deserialize_list_proof _ _).
      iMod (gwp_deserialize_list_proof (g := gwp_spec_verifier) proof_v (InjLV #()) [] l_proof' ⊤ ()
              is_ret_proof _
              (λ w, ⌜∃ (l'' ret_l: list val) (w': val),
                         w = SOMEV w' ∧ 
                           ret_l = (fun (x : string) => #x) <$> l_proof' ∧
                           is_list l'' w' ∧ l'' = (rev ret_l) ++ []⌝)%I
             with "[//] [] [$Hv //]") as (?) "[Hv (% & % & % & -> & %Hretrev & %is_list_des & ->)]".
      { by iIntros "!>" (?) "%". }
      iSimpl in "Hv". v_pures. Unshelve. 2: done.
      destruct Hhead as [[? [? [-> ->]]]|[? [-> ?]]].
      + v_pures. (* Case 3 *)
        v_bind (s_serializer _ _).
        iMod (s_ser_spec merkle_ser ⊤ (InjRV (#proof_head, #x)) ()
                (λ v, ⌜∃ s': string, v=#s' ∧ s_is_ser merkle_ser (InjRV (#proof_head, #x)) s'⌝)%I
               with "[] [] [$Hv //]") as (?) "[Hv %Hserin]".
        { iModIntro. iExists _. iRight.
          iSplit; [done|]. iExists _, _.
          iSplit; [done|]. iSplit;  by iExists _. }
        { iIntros "!>" (?) "%". iExists s. done. }
        iSimpl in "Hv".
        destruct Hserin as [s' [-> Hserin]].

        v_bind (Hash _).
        iMod (step_verifier_hash with "[$]") as "Hv"; [done|].
        iSimpl in "Hv".
        v_pures.

        v_bind (retrieve_magic_verifier_aux _ _ _).
        iMod (refines_verifier_retrieve_aux _ _
               with "[Hv]") as (?) "(Hv & ->)".
        { iFrame "∗ #". simplify_list_eq.
          repeat (iSplit; [done|]).
          rewrite <- reverse_rev.
          rewrite length_reverse.
          rewrite length_fmap.
          rewrite <- fmap_reverse.
          repeat (iSplit; [done|]).
          done. }
        iSimpl in "Hv". v_pures.
        { solve_vals_compare_safe. }
        rewrite reverse_rev. simplify_eq.

        destruct! Hserin; simplify_eq.
        destruct! H3; simplify_eq.
        destruct! H6; destruct! H7; simplify_eq. rewrite Hvalidhash.
        iEval (rewrite bool_decide_eq_true_2 //) in "Hv".
        v_pures.

        v_bind (list_tail _).
        iMod (gwp_list_tail (g := gwp_spec_verifier) ⊤ w (ret_proof :: vs') ()
                (λ v, ⌜is_list vs' v⌝)%I with "[//] [] [$Hv //]") as (?) "[Hv %proof_tail]".
        { by iIntros "!>" (?). }
        iSimpl in "Hv". v_pures.

        iApply "H".
        iFrame. iModIntro.
        instantiate (1 := [ret_proof]).
        repeat (iSplit; [done|]).
        iExists _, _, _. iLeft.
        repeat (iSplit; [done|]). done.

      + v_pures. (* Case 2 *)
        v_bind (list_length _).
        iMod (gwp_list_length (g := gwp_spec_verifier) ⊤ (rev ret_l ++ []) w' ()
                (λ w, ⌜w = #(length l_sub_proof)⌝)%I
               with "[//] [] [$Hv //]") as (?) "[Hv ->]".
        { iIntros "!>" (?) "%". simplify_list_eq.
          rewrite <- reverse_rev. rewrite length_reverse.
          rewrite length_fmap. done. }
        iSimpl in "Hv".

        v_bind (list_sub _ _).
        iMod (gwp_list_sub (g := gwp_spec_verifier) ⊤ (length l_sub_proof) (keep_path ++ disc_path) path_v ()
                (λ w, ⌜is_list (keep_path) w⌝)%I
               with "[//] [] [$Hv //]") as (?) "[Hv %Hsubl]".
        { iIntros "!>" (?) "%".
          iPureIntro. simplify_list_eq. done. }
        iSimpl in "Hv". v_pures.

        v_bind (list_length _). simpl in is_list_path_v.
        iMod (gwp_list_length (g := gwp_spec_verifier) ⊤ keep_path v0 () (λ w, ⌜w = #(length keep_path)⌝)%I
               with "[//] [] [$Hv //]") as (?) "[Hv ->]".
        { iIntros "!>" (?) "%". rewrite H3. done. }
        iSimpl in "Hv".

        v_bind (list_length _).
        iMod (gwp_list_length (g := gwp_spec_verifier) ⊤ (keep_path ++ disc_path) path_v ()
                (λ w, ⌜w = #(length keep_path + length disc_path)⌝)%I
               with "[//] [] [$Hv //]") as (?) "[Hv ->]".
        { iIntros "!>" (?) "%". rewrite app_length in H3.
          iPureIntro. f_equal. rewrite H3. f_equal. lia. }
        iSimpl in "Hv". v_pures.

        assert (length keep_path + length disc_path > length keep_path).
        { destruct disc_path; [done|]. simpl. lia. }
        case_bool_decide; [lia|].

        v_bind (s_serializer _ _).
        iMod (s_ser_spec merkle_ser ⊤ (InjLV #proof_head) ()
                (λ v, ⌜∃ s': string, v=#s' ∧ s_is_ser merkle_ser (InjLV #proof_head) s'⌝)%I
               with "[] [] [$Hv //]") as (?) "[Hv %Hserin]".
        { iModIntro. iExists _. iLeft.
          iSplit; [done|]. by iExists _. }
        { iIntros "!>" (?) "%". iExists s. done. }
        iSimpl in "Hv".
        destruct Hserin as [s' [-> Hserin]].

        v_bind (Hash _).
        iMod (step_verifier_hash with "[$]") as "Hv"; [done|].
        iSimpl in "Hv". v_pures.

        v_bind (retrieve_magic_verifier_aux _ _ _).
        iMod (refines_verifier_retrieve_aux _ _
               with "[Hv]") as (?) "(Hv & ->)".
        { iFrame "∗ #". repeat (iSplit; [done|]).
          simplify_list_eq. rewrite <- reverse_rev.
          rewrite length_reverse. rewrite length_fmap.
          rewrite <- fmap_reverse.
          repeat (iSplit; [done|]). done. }
        iSimpl in "Hv". v_pures.
        { solve_vals_compare_safe. }

        rewrite <- Hvalidhash. rewrite reverse_rev.
        rewrite H1. destruct! Hserin; simplify_eq.
        destruct! H8; simplify_eq.
        iEval (rewrite bool_decide_eq_true_2 //) in "Hv".
        v_pures.

        v_bind (list_tail _).
        iMod (gwp_list_tail (g := gwp_spec_verifier) ⊤ w (ret_proof :: vs') ()
                (λ v, ⌜is_list vs' v⌝)%I with "[//] [] [$Hv //]") as (?) "[Hv %proof_tail]".
        { by iIntros "!>" (?). }
        iSimpl in "Hv".
        v_pures.

        iApply "H".
        iFrame. iModIntro.
        instantiate (1 := [ret_proof]).
        repeat (iSplit; [done|]).
        iExists _, _, _. iLeft.
        repeat (iSplit; [done|]). done.
  Qed.

End semantic.
