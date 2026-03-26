From stdpp Require Import strings list pretty gmap.
From iris.base_logic.lib Require Import fancy_updates.
From auth.heap_lang Require Export lang notation gen_weakestpre lib.inject lib.list.

Section map_code.
Definition map_empty : val := λ: <>, [].

Definition map_remove : val :=
  λ: "key",
    rec: "loop" "m" :=
      match: "m" with
        NONE => NONE
      | SOME "x" =>
          let, ("p", "m") := "x" in
          if: Fst "p" = "key"
          then "m"
          else "p" :: "loop" "m"
      end.

Definition map_insert : val :=
  λ: "key" "value" "m", ("key", "value") :: map_remove "key" "m".

Definition map_lookup : val :=
  λ: "key", rec: "loop" "m" :=
  match: "m" with
    NONE => NONE
  | SOME "x" =>
      let, ("p", "m") := "x" in
      if: Fst "p" = "key"
      then SOME (Snd "p")
      else "loop" "m"
  end.

Definition map_mem : val :=
  λ: "k" "m",
  match: map_lookup "k" "m" with
    NONE => #false
  | SOME "_p" => #true
  end.

Definition map_iter : val :=
  rec: "map_iter" "f" "m" :=
  match: "m" with
    NONE => #()
  | SOME "x" =>
      let, ("p", "m") := "x" in
      "f" (Fst "p") (Snd "x");;
      "map_iter" "f" "m"
  end.

Definition map_forall : val :=
  rec: "map_forall" "f" "m" :=
  match: "m" with
    NONE => #true
  | SOME "x" =>
      let, ("p", "m") := "x" in
      ("f" (Fst "p") (Snd "p")) && "map_forall" "f" "m"
  end.

Definition map_is_empty : val :=
  λ: "m",
    match: "m" with
      NONE => #true
    | SOME "x" => #false
    end.

End map_code.

Section map_specs.
  Context `{invGS_gen hlc Σ} `{g : !GenWp Σ}.
  Context `[Countable K, !Inject K val].
  Context `[V : Type, !Inject V val].

  Implicit Types s : gwp_type g.
  Implicit Types k : K.

  Definition is_map (d : val) (m : gmap K V) (s : nat) : Prop :=
    ∃ l, m = list_to_map l ∧ d = $l ∧ NoDup (fst <$> l) ∧ s = length l.

  Definition map_length (m : gmap K V) : nat := length (map_to_list m).

  Lemma gwp_map_is_empty s E d m si :
    G{{{ ⌜is_map d m si⌝ }}}
      map_is_empty (Val d) @ s; E
    {{{ v, RET #v; ⌜v = Nat.eqb 0 si⌝ }}} ? gwp_laters g.
  Proof.
    iIntros (Φ (l & -> & -> & Hdup & Hlen)) "HΦ".
    rewrite /map_is_empty /map_length.
    destruct l; gwp_pures; iModIntro; iApply "HΦ";
      iPureIntro; simpl; simpl in Hlen; by simplify_eq.
  Qed.
      
  Lemma gwp_map_empty s E :
    G{{{ True }}}
      map_empty #() @ s; E
    {{{ v, RET v; ⌜is_map v ∅ 0⌝}}} ? gwp_laters g.
  Proof.
    iIntros (Φ) "_ HΦ".
    gwp_rec. gwp_pures. iApply "HΦ".
    iModIntro. iPureIntro.
    exists []. do 2 (split; [done|]). split; [constructor|done].
  Qed.

  Lemma gwp_map_remove_some s E k v d m si :
    val_is_unboxed $ k → m !! k = Some v →
    G{{{ ⌜is_map d m si⌝ }}}
      map_remove $k (Val d) @ s; E
    {{{ d', RET d'; ⌜is_map d' (delete k m) (si-1)⌝ }}} ? gwp_laters g.
  Proof.
    iIntros (? ? Φ (l & -> & -> & Hdup & Hl)) "HΦ".
    gwp_rec. gwp_closure.
    iInduction l as [|[k' v'] l] "IH" forall (Hdup Φ si Hl) "HΦ".
    - gwp_pures. iApply "HΦ". iIntros "!%".
      exists []. rewrite delete_empty //=.
    - inversion Hdup; simplify_eq.
      gwp_pures.
      case_bool_decide as Heq; simplify_eq.
      + gwp_pures. iApply "HΦ".
        iIntros "!> /= !%".
        rewrite delete_insert.
        * eexists. do 3 (split; [done|]). lia.
        * by apply not_elem_of_list_to_map.
      + gwp_if.
        gwp_apply ("IH" with "[]").
        { admit. }
        { admit. }
        { done. }
        iIntros (d' (l' & Hl' & -> & ? & Hsi)).
        gwp_pures.
        gwp_apply (gwp_list_cons (k',v')).
        { rewrite is_list_inject //. }
        iIntros (? ->%is_list_inject). iApply "HΦ". iPureIntro.
        destruct (decide (k = k')); simplify_eq.
        eexists ((k', v') :: l') => /=.
        rewrite delete_insert_ne //=.
        split; [congruence|].
        split; [done|].
        constructor; last first. { admit. }
        constructor; [|done].
        apply not_elem_of_list_to_map_2.
        rewrite -Hl' lookup_delete_ne //.
        by apply not_elem_of_list_to_map_1.
  Admitted.

  Lemma gwp_map_remove_none s E k d m si :
    val_is_unboxed $ k → m !! k = None →
    G{{{ ⌜is_map d m si⌝ }}}
      map_remove $k (Val d) @ s; E
    {{{ d', RET d'; ⌜is_map d' (delete k m) si⌝ }}} ? gwp_laters g.
  Proof.
    iIntros (? ? Φ (l & -> & -> & Hdup & Hl)) "HΦ".
    gwp_rec. gwp_closure.
    iInduction l as [|[k' v] l] "IH" forall (Hdup Φ si Hl) "HΦ".
    - gwp_pures. iApply "HΦ". iIntros "!%".
      exists []. rewrite delete_empty //=.
    - apply not_elem_of_list_to_map_2 in H2 as ?.
      simpl in H2. assert (k ≠ k'). { admit. }
      inversion Hdup; simplify_eq.
      gwp_pures.
      case_bool_decide as Heq; simplify_eq.
      + gwp_if.
        gwp_apply ("IH" with "[]").
        { admit. }
        { done. }
        { done. }
        iIntros (d' (l' & Hl' & -> & ? & Hsi)).
        gwp_pures.
        gwp_apply (gwp_list_cons (k',v)).
        { rewrite is_list_inject //. }
        iIntros (? ->%is_list_inject). iApply "HΦ". iPureIntro.
        destruct (decide (k = k')); simplify_eq.
        eexists ((k', v) :: l') => /=.
        rewrite delete_insert_ne //=.
        split; [congruence|].
        split; [done|].
        constructor; last first. { lia. }
        constructor; [|done].
        apply not_elem_of_list_to_map_2.
        rewrite -Hl' lookup_delete_ne //.
        by apply not_elem_of_list_to_map_1.
  Admitted.

  Lemma gwp_map_insert_some (k : K) v d m s E si v' :
    val_is_unboxed $ k → m !! k = Some v' →
    G{{{ ⌜is_map d m si⌝ }}}
      map_insert $k $v d @ s; E
    {{{ d', RET d'; ⌜is_map d' (<[ k := v ]> m) si⌝ }}} ? gwp_laters g.
  Proof.
    iIntros (?? Φ (l & -> & -> & Hdup & Hl)) "HΦ".
    gwp_rec. gwp_closure.
    gwp_rec. gwp_pures.
    gwp_apply (gwp_map_remove_some).
    - done.
    - done.
    - iPureIntro. exists l.
      split; [done|].
      split; [|done].
      by simpl.
    - iIntros (d' (l' & Hl' & -> & ? & ?)). gwp_pures.
      gwp_apply (gwp_list_cons (k, v)).
      { rewrite is_list_inject //. }
      iIntros (? ->%is_list_inject). iApply "HΦ". iPureIntro.
      exists ((k, v) :: l').
      split.
      + rewrite <- insert_delete_insert.
        rewrite Hl'. symmetry. apply list_to_map_cons.
      + split; [done|].
        split; last first.
        { simpl. rewrite <- H4. admit. }
        constructor; last done.
        eapply (not_elem_of_list_to_map_2).
        rewrite -Hl' lookup_delete //.
  Admitted.

  Lemma gwp_map_insert_none (k : K) v d m s E si :
    val_is_unboxed $ k → m !! k = None →
    G{{{ ⌜is_map d m si⌝ }}}
      map_insert $k $v d @ s; E
    {{{ d', RET d'; ⌜is_map d' (<[ k := v ]> m) (si+1)⌝ }}} ? gwp_laters g.
  Proof.
    iIntros (?? Φ (l & -> & -> & Hdup & Hl)) "HΦ".
    gwp_rec. gwp_closure.
    gwp_rec. gwp_pures.
    gwp_apply (gwp_map_remove_none).
    - done.
    - done.
    - iPureIntro. exists l.
      split; [done|].
      split; [|done].
      by simpl.
    - iIntros (d' (l' & Hl' & -> & ? & ?)). gwp_pures.
      gwp_apply (gwp_list_cons (k, v)).
      { rewrite is_list_inject //. }
      iIntros (? ->%is_list_inject). iApply "HΦ". iPureIntro.
      exists ((k, v) :: l').
      split.
      + rewrite <- insert_delete_insert.
        rewrite Hl'. symmetry. apply list_to_map_cons.
      + split; [done|].
        split; last first.
        { simpl. rewrite <- H4. lia. }
        constructor; last done.
        eapply (not_elem_of_list_to_map_2).
        rewrite -Hl' lookup_delete //.
  Qed.

  Lemma gwp_map_lookup k d m s E si :
    val_is_unboxed $ k →
    G{{{ ⌜is_map d m si⌝ }}}
      map_lookup $k d @ s; E
     {{{ v, RET v; ⌜from_option (λ p, v = SOMEV $p) (v = NONEV) (m !! k)⌝ }}}
     ? gwp_laters g.
  Proof.
    iIntros (? Φ (l & -> & -> & Hdup & Hsi)) "HΦ".
    gwp_rec. gwp_closure.
    iInduction l as [|[k' v] l'] "IH" forall (Hdup Φ si Hsi) "HΦ".
    - gwp_pures. iApply "HΦ". iIntros "!%".
      unfold from_option. simpl. by rewrite lookup_empty.
    - gwp_pures.
      case_bool_decide as Heq; simplify_eq.
      + gwp_if. gwp_pures.
        iModIntro. iApply ("HΦ").
        iPureIntro. unfold from_option.
        rewrite lookup_insert //.
      + gwp_if. gwp_apply ("IH").
        * inversion Hdup. by subst.
        * done.
        * iIntros (v' Hres). iApply "HΦ".
          iPureIntro. simpl.
          rewrite lookup_insert_ne; [done| ].
          intros ->. done.
  Qed.

  Lemma gwp_map_mem k d m s E si :
    val_is_unboxed $ k →
    G{{{ ⌜is_map d m si⌝ }}}
      map_mem $k d @ s; E
     {{{ (b : bool), RET #b; if b then ⌜∃ v, m !! k = Some v⌝ else True }}}
     ? gwp_laters g.
  Proof.
    iIntros (? Φ (l & -> & -> & Hdup & Hsi)) "HΦ".
    gwp_rec. gwp_pure. gwp_pure.
    gwp_apply gwp_map_lookup; [done| |].
    - iPureIntro. by eexists.
    - destruct ((list_to_map l)!!k) eqn:Heq.
      + iIntros (v0 ->).
        gwp_pures. iModIntro. iApply ("HΦ").
        iPureIntro. by eexists.
      + iIntros (v0 ->). gwp_pures.
        iModIntro. iApply ("HΦ"). done.
  Qed.

  (* Lemma gwp_map_iter (Φ Ψ : K → V → iProp Σ) P ip d m f : *)
  (*   (∀ (k : K) (v : V), *)
  (*       {{{ P ∗ Φ k v }}} *)
  (*         (Val f) $k $v @[ip] *)
  (*       {{{ RET #(); P ∗ Ψ k v }}}) -∗ *)
  (*   {{{ ⌜is_map d m⌝ ∗ P ∗ [∗ map] k↦v ∈ m, Φ k v }}} *)
  (*     map_iter (Val f) d @[ip] *)
  (*   {{{ RET #(); P ∗ [∗ map] k↦v ∈ m, Ψ k v }}}. *)
  (* Proof. *)
  (*   iIntros "#Hf" (Ξ) "!# (%Hd & HP & HΦ) HΞ". *)
  (*   iLöb as "IH" forall (Ξ d m Hd); gwp_rec. *)
  (*   gwp_pures. *)
  (*   destruct Hd as (? & -> & -> & Hnodup). *)
  (*   destruct x as [|[k v] l]. *)
  (*   - gwp_pures. iApply "HΞ". by iFrame. *)
  (*   - gwp_pures. simpl. *)
  (*     iDestruct (big_sepM_insert with "HΦ") as "[Hkv Hrest]". *)
  (*     { apply not_elem_of_list_to_map_1. *)
  (*       inversion Hnodup; simplify_eq. set_solver. } *)
  (*     gwp_apply ("Hf" with "[$HP $Hkv]"). *)
  (*     iIntros "[HP HΨ]". *)
  (*     gwp_pures. *)
  (*     gwp_apply ("IH" with "[] HP Hrest"). *)
  (*     { inversion Hnodup. subst. by iExists l. } *)
  (*     iIntros "[HP Hrest]". *)
  (*     iApply "HΞ". *)
  (*     iFrame. *)
  (*     iApply (big_sepM_insert with "[$Hrest $HΨ]"). *)
  (*     apply not_elem_of_list_to_map_1. *)
  (*     inversion Hnodup; simplify_eq. *)
  (*     set_solver. *)
  (*  Qed. *)

  (* Lemma gwp_map_forall Φ Ψ ip d m (f : val) : *)
  (*   (∀ (k : K) (v : V), *)
  (*       {{{ True }}} *)
  (*         f $k $v @[ip] *)
  (*       {{{ (b : bool), RET #b; if b then Φ k v else Ψ k v }}}) -∗ *)
  (*   {{{ ⌜is_map d m⌝ }}} *)
  (*     map_forall f d @[ip] *)
  (*   {{{ (b : bool), RET #b; *)
  (*         if b then [∗ map] k↦v ∈ m, Φ k v *)
  (*         else ∃ k v , ⌜m !! k = Some v⌝ ∗ Ψ k v }}}. *)
  (* Proof. *)
  (*   iIntros "#Hf" (Ξ) "!# %Hd HΞ". *)
  (*   iLöb as "IH" forall (Ξ d m Hd). gwp_rec. *)
  (*   gwp_pures. *)
  (*   destruct Hd as (? & -> & -> & Hnodup). *)
  (*   destruct x as [|[k v] l]. *)
  (*   - gwp_pures. by iApply "HΞ". *)
  (*   - gwp_pures. gwp_apply "Hf"; [done|]. *)
  (*     iIntros ([]) "Hb". *)
  (*     + gwp_pures. *)
  (*       gwp_apply "IH". *)
  (*       { inversion Hnodup. subst. by iExists l. } *)
  (*       iIntros ([]) "HΦ". *)
  (*       { iApply "HΞ". simpl. *)
  (*         iApply (big_sepM_insert with "[$HΦ $Hb]"). *)
  (*         apply not_elem_of_list_to_map_1. *)
  (*         inversion Hnodup; simplify_eq. *)
  (*         set_solver. } *)
  (*       iApply "HΞ". *)
  (*       iDestruct "HΦ" as (??) "[% ?]". *)
  (*       iExists _, _. iFrame. iPureIntro. *)
  (*       simpl. *)
  (*       rewrite lookup_insert_ne //. *)
  (*       inversion Hnodup; simplify_map_eq. *)
  (*       apply elem_of_list_to_map in H1; [|set_solver]. *)
  (*       intros ->. apply H4. *)
  (*       apply elem_of_list_fmap. *)
  (*       exists (k0, v0); done. *)
  (*     + gwp_pures. *)
  (*       iApply "HΞ". *)
  (*       iExists _, _. iFrame. iPureIntro. *)
  (*       rewrite lookup_insert //. *)
  (* Qed. *)

End map_specs.

Global Arguments gwp_map_empty {_ _ _ _} _ {_ _ _} _.
