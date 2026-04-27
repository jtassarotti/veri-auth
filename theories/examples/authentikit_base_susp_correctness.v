From auth.prelude Require Import stdpp.
From auth.rel_logic_tern_susp Require Export model interp spec_tactics.
From auth.heap_lang Require Import typedproph.
From auth.heap_lang.lib Require Import serialization_susp list.
From auth.examples Require Export authentikit_susp authenticatable_base_susp.
From iris.base_logic.lib Require Export na_invariants.
From iris.algebra Require Import gmap.
From iris.algebra.lib Require Import dfrac_agree.


(** * Prophesied stream *)
Section proph.
  Context `{heapGS Σ}.

  Fixpoint take_until {A B : Type} (f : A → option B) (xs : list A) : list B :=
    match xs with
    | []      => []
    | x :: xs =>
      match f x with
      | Some y => y :: (take_until f xs)
      | None   => []
      end
    end.

  Definition longest_valid_prefix_bool (us : list val) : list bool :=
    take_until (λ u, match u with InjRV (LitV (LitBool b)) => Some b | _ => None end) us.

  Definition proph_bs (p : proph_id) (bs : list bool) : iProp Σ :=
    (∃ (us : list (val * val)), proph p us ∗ ⌜bs = longest_valid_prefix_bool (map snd us)⌝)%I.

  Definition longest_valid_prefix_string (us : list val) : list string :=
    take_until (λ u, match u with InjRV (LitV (LitString s)) => Some s | _ => None end) us.

  Definition proph_proof (p : proph_id) (vs : list string) : iProp Σ :=
    (∃ (us : list (val * val)), proph p us ∗ ⌜vs = longest_valid_prefix_string (map snd us)⌝)%I.

  Definition longest_valid_prefix_val (us : list val) : list val :=
    take_until (λ u, match u with InjRV v => Some v | _ => None end) us.

  Definition proph_as (p : proph_id) (vs : list val) : iProp Σ :=
    (∃ (us : list (val * val)), proph p us ∗ ⌜vs = longest_valid_prefix_val (map snd us)⌝)%I.

  Lemma wp_resolve_proph_bool p bs (b : bool) :
    {{{ proph_bs p bs }}}
      resolve_proph: #p to: (SOMEV #b)
    {{{ bs', RET #(); ⌜bs = b :: bs'⌝ ∗ proph_bs p bs' }}}.
  Proof.
    iIntros (Φ) "(%us & Hp & %) HΦ".
    wp_apply (wp_resolve_proph with "Hp").
    iIntros (?) "[% Hp]". iApply "HΦ".
    iFrame. by simplify_eq.
  Qed.

  Lemma wp_resolve_proph_nil_bool p bs :
    {{{ proph_bs p bs }}} resolve_proph: #p to: NONEV {{{ RET #(); ⌜bs = []⌝ }}}.
  Proof.
    iIntros (Φ) "(%us & Hp & %) HΦ".
    wp_apply (wp_resolve_proph with "Hp").
    iIntros (?) "[% Hp]". iApply "HΦ".
    by simplify_eq.
  Qed.

  Lemma wp_resolve_proph_string p vs (s : string) :
    {{{ proph_proof p vs }}}
      resolve_proph: #p to: (SOMEV #s)
    {{{ vs', RET #(); ⌜vs = s :: vs'⌝ ∗ proph_proof p vs' }}}.
  Proof.
    iIntros (Φ) "(%us & Hp & %) HΦ".
    wp_apply (wp_resolve_proph with "Hp").
    iIntros (?) "[% Hp]". iApply "HΦ".
    iFrame. by simplify_eq.
  Qed.

  Lemma wp_resolve_proph_nil_string p vs :
    {{{ proph_proof p vs }}} resolve_proph: #p to: NONEV {{{ RET #(); ⌜vs = []⌝ }}}.
  Proof.
    iIntros (Φ) "(%us & Hp & %) HΦ".
    wp_apply (wp_resolve_proph with "Hp").
    iIntros (?) "[% Hp]". iApply "HΦ".
    by simplify_eq.
  Qed.

  Lemma wp_resolve_proph_val p vs (v : val) :
    {{{ proph_as p vs }}}
      resolve_proph: #p to: (SOMEV v)
    {{{ vs', RET #(); ⌜vs = v :: vs'⌝ ∗ proph_as p vs' }}}.
  Proof.
    iIntros (Φ) "(%us & Hp & %) HΦ".
    wp_apply (wp_resolve_proph with "Hp").
    iIntros (?) "[% Hp]". iApply "HΦ".
    iFrame. by simplify_eq.
  Qed.

  Lemma wp_resolve_proph_nil_val p vs :
    {{{ proph_as p vs }}} resolve_proph: #p to: NONEV {{{ RET #(); ⌜vs = []⌝ }}}.
  Proof.
    iIntros (Φ) "(%us & Hp & %) HΦ".
    wp_apply (wp_resolve_proph with "Hp").
    iIntros (?) "[% Hp]". iApply "HΦ".
    by simplify_eq.
  Qed.

  Definition is_proof (v : val) (ps : list string) : Prop :=
    is_list ps v.

  Definition is_proph_proof (v : val) (p : proph_id) (ps : list string) : iProp Σ :=
    ⌜is_proof v ps⌝ ∗ proph_proof p ps.

End proph.


(* Nat is going to be the id assigned by the verifier. We are going to show that
  for some value in the verifier's map, the ctr must be > 0. These values are either
  yet to be seen or are in the map. oneshot_done denotes values have been seen.
  In the end we will say that for the highest id value in the map all values must
  have been seen (because of flush_buf_stream), and since this is the highest
  id, and children's ids are higher, we have a contradiction. *)
Definition oneshotUR := authUR (optionUR (agreeR nat)).
Class oneshotG Σ := OneshotG { oneshot_inG :> inG Σ oneshotUR; oneshotG_name : gname }.

Section oneshot_res.
  Context `{!oneshotG Σ}.

  Definition oneshot_type := optionUR (agreeR nat).

  Definition oneshot_pending γ : iProp Σ :=
    own γ (●{DfracOwn (1/2)} None).

  Definition oneshot_done γ n : iProp Σ :=
    own γ (●{DfracDiscarded} Some (to_agree n)).

  Lemma oneshot_transition γ n :
    oneshot_pending γ ∗ oneshot_pending γ ==∗ oneshot_done γ n.
  Proof.
    rewrite /oneshot_pending /oneshot_done.
    iIntros "[H1 H2]". iCombine "H1 H2" as "H".
    iMod (own_update _ _ (●□ Some (to_agree n)) with "H") as "$"; last done.
    etrans; last apply auth_update_auth_persist.
    apply (auth_update_auth None (Some (to_agree n)) (Some (to_agree n))),
      alloc_option_local_update. done.
  Qed.

  Lemma oneshot_invalid γ n :
    oneshot_pending γ ∗ oneshot_done γ n -∗ False.
  Proof.
    rewrite /oneshot_pending /oneshot_done.
    iIntros "[H1 H2]". iCombine "H1 H2" as "H".
    iDestruct (own_valid with "H") as %Hv. iPureIntro.
    apply auth_auth_dfrac_op_valid in Hv as (_ & Heq & _). inversion Heq.
  Qed.

  Lemma oneshot_agree γ n1 n2 :
    oneshot_done γ n1 ∗ oneshot_done γ n2 -∗ ⌜n1 = n2⌝.
  Proof.
    rewrite /oneshot_done.
    iIntros "[H1 H2]". iCombine "H1 H2" as "H".
    iDestruct (own_valid with "H") as %Hv. iPureIntro.
    apply auth_auth_dfrac_op_valid in Hv as (_ & Heq & _).
    fold_leibniz. by apply (inj Some), to_agree_inj in Heq.
  Qed.

End oneshot_res.

Definition lg_mapUR := authR (gmapUR loc (agreeR (leibnizO gname))).
Class lg_mapG Σ := Lg_mapG { lg_map_inG :> inG Σ lg_mapUR; lg_mapG_name : gname }.

Section lg_map.
  Context `{!lg_mapG Σ}.

  Definition lg_mapg_type := gmap loc (agree gname).

  Definition lg_mapg_auth (m : lg_mapg_type) : iProp Σ :=
    own lg_mapG_name (● m).

  Definition lg_mapg_frag l γ : iProp Σ :=
    own lg_mapG_name (◯ {[ l := to_agree γ ]}).

  Lemma lg_mapg_agree l γ1 γ2 :
    lg_mapg_frag l γ1 -∗ lg_mapg_frag l γ2 -∗ ⌜γ1 = γ2⌝ ∗ lg_mapg_frag l γ1 ∗ lg_mapg_frag l γ2.
  Proof.
    rewrite /lg_mapg_frag. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hv.
    iFrame. iPureIntro.
    rewrite -auth_frag_op auth_frag_valid singleton_op singleton_valid in Hv.
    fold_leibniz. by apply to_agree_op_inv_L in Hv.
  Qed.

  Lemma lg_mapg_insert m l γ :
    m !! l = None →
    lg_mapg_auth m ==∗ lg_mapg_auth (<[ l:= to_agree γ ]> m) ∗ lg_mapg_frag l γ.
  Proof.
    rewrite /lg_mapg_auth /lg_mapg_frag. iIntros (Hfresh) "H".
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


Definition prover_susp_set (N : namespace) : namespace := N .@ "psusp".
Definition prover_susp_n (N : namespace) (v : val) : namespace := (prover_susp_set N) .@ v.

Definition ver_susp_set (N : namespace) : namespace := N .@ "vsusp".
Definition ver_susp_n (N : namespace) (v : val) : namespace := (ver_susp_set N) .@ v.

Section authenticatable.
  Context `{!authG Σ, !seqG Σ, !oneshotG Σ, !lg_mapG Σ, !mapG Σ, !capG Σ} (N : namespace).

  Inductive evi_type : Type :=
  | tprod (t1 t2 : evi_type)
  | tsum (t1 t2 : evi_type)
  | tstring
  | tint
  | tauth.

  #[global] Instance : Inhabited evi_type.
  Proof. constructor. apply tstring. Qed.

  (* Fixpoint evi_type_ser (t : evi_type) : serialization_scheme :=
    match t with
    | tprod t1 t2 => prod_serialization_scheme (evi_type_ser t1) (evi_type_ser t2)
    | tsum t1 t2 => sum_serialization_scheme (evi_type_ser t1) (evi_type_ser t2)
    | tstring => string_serialization_scheme
    | tint => int_serialization_scheme
    end.

  Lemma evi_type_ser_inj_str (t1 t2 : evi_type) v s1 s2 :
    s_is_ser (g := gwp_upto_bad) (evi_type_ser t1) v s1 -∗
    s_is_ser (g := gwp_upto_bad) (evi_type_ser t2) v s2 -∗
    ⌜s1 = s2⌝.
  Proof. Admitted. *)
    (* induction t1 in t2, v, s1, s2 |-* => /=.
    - intros Ht1 Ht2. destruct! Ht1; simplify_eq.
      destruct t2 => /=; destruct! Ht2; simplify_eq; eauto.
      erewrite (IHt1_1 t2_1 _ H0); [|done|done].
      erewrite (IHt1_2 t2_2 _ H2); [|done|done]. done.
    - intros Ht1 Ht2. destruct! Ht1; simplify_eq.
      + destruct t2 => /=; destruct! Ht2; simplify_eq; auto.
        by erewrite (IHt1_1 t2_1 _ H1).
      + destruct t2 => /=; destruct! Ht2; simplify_eq; auto.
        by erewrite (IHt1_2 t2_2 _ H1).
    - intros Ht1 Ht2. destruct! Ht1; simplify_eq.
      destruct t2 => /=; destruct! Ht2; simplify_eq => //; auto.
    - intros Ht1 Ht2. destruct! Ht1; simplify_eq.
      destruct t2 => /=; destruct! Ht2; simplify_eq => //; auto.
  Qed. *)

  (* Lemma evi_type_ser_inj_val (t1 t2 : evi_type) v1 v2 s :
    s_is_ser (g := gwp_upto_bad) (evi_type_ser t1) v1 s -∗
    s_is_ser (g := gwp_upto_bad) (evi_type_ser t2) v2 s -∗
    ⌜v1 = v2⌝.
  Proof. Admitted. *)
    (* induction t1 in t2, v1, v2, s |-* => /=.
    - intros Ht1 Ht2. destruct! Ht1; simplify_eq.
      destruct t2 => /=; destruct! Ht2; simplify_eq; eauto.
      + f_equal; [by eapply IHt1_1|]. by eapply IHt1_2.
      + exfalso. by eapply prod_ser_inl_ser_neq.
      + exfalso. by eapply prod_ser_inr_ser_neq.
      + exfalso. by eapply prod_ser_string_ser_neq.
      + exfalso. by eapply prod_ser_int_ser_neq.
    - intros Ht1 Ht2. destruct! Ht1; simplify_eq.
      + destruct t2 => /=; destruct! Ht2; simplify_eq; auto.
        * exfalso. by eapply prod_ser_inl_ser_neq.
        * f_equal. by eapply IHt1_1.
      + destruct t2 => /=; destruct! Ht2; simplify_eq; auto.
        * exfalso. by eapply prod_ser_inr_ser_neq.
        * f_equal. by eapply IHt1_2.
    - intros Ht1 Ht2. destruct! Ht1; simplify_eq.
      destruct t2 => /=; destruct! Ht2; simplify_eq => //; auto.
      exfalso. by eapply prod_ser_string_ser_neq.
    - intros Ht1 Ht2. destruct! Ht1; simplify_eq.
      destruct t2 => /=; destruct! Ht2; simplify_eq => //; auto.
      exfalso. by eapply prod_ser_int_ser_neq.
  Qed. *)

  (* Definition proph_br (p : proph_id) (b : bool) : iProp Σ :=
    (typed_proph1_prop BoolTypedProph) p b. *)

  Definition proph_s (p : proph_id) (ls : list string) : iProp Σ :=
    (typed_proph_prop StringTypedProph) p ls.

  (* For verifier *)
  Fixpoint sub_obj (t : evi_type) (v sv: val) :=
    match t with
    | tprod t1 t2 =>
        ∃ v1 v2, v = (v1, v2)%V ∧ (sv = v1 ∨ sv = v2 ∨ sub_obj t1 v1 sv ∨ sub_obj t2 v2 sv)
    | tsum t1 t2 =>
        ∃ v', ((v = InjLV v' ∧ sub_obj t1 v' sv ∧ v = v') ∨
                 (v = InjRV v' ∧ sub_obj t2 v' sv ∧ v = v'))
    | tstring => False
    | tint => False
    | tauth =>
        ∃ v', (v = SOMEV (InjLV v') ∨ (v = SOMEV (InjRV v'))) ∧ v' = sv
  end.

  Definition suspended_string : string := none_ser_str.

  Definition simple_string (s : string) : string := string_ser_str s.

  Definition filled_string (s : string) : string := some_ser_str (simple_string s).

  Definition empty_proph_bs (p : proph_id) : iProp Σ :=
    proph_bs p [].

  Definition fill_proph_bs (p : proph_id) (bs : list bool) : iProp Σ :=
    proph_bs p bs ∗ ⌜~ In true bs⌝.

  Definition unfill_proph_bs (p : proph_id) (bs : list bool) : iProp Σ :=
    proph_bs p bs ∗ ⌜∃ bs', bs = true :: bs'⌝.

  (* Definition proph_p_susp (p : proph_id) (bs : bool list) : iProp Σ :=
    (typed_proph_prop IntTypedProph) p bs. *)

  Definition proph_v_susp (p : proph_id) (s : string) : iProp Σ :=
    (typed_proph1_prop StringTypedProph) p s.

  (* Definition auth_p_unsusp (v : val) : iProp Σ :=
    ∃ (a : val) (s : string), 
      ⌜v = (a, #(hash s))%V⌝ ∗ hashed s ∗
      s_is_ser (g:=gwp_upto_bad) auth_scheme a s.

  (* ps true denotes going to suspend, false otherwise *)
  Definition auth_p_susp (v : val) : iProp Σ :=
    ∃ (b r ord : bool) (lb lr : loc) (ps : proph_id) (a : val) (s : string),
      ⌜v = (#ps, #lb, #lr, a, #(hash s))%V⌝ ∗ hashed s ∗
      lb ↦ #b ∗ lb ↦ #r ∗ proph_susp ps ord ∗
      s_is_ser (g:=gwp_upto_bad) auth_scheme a s. *)

  Definition auth_unsusp_ser_p (v : val) (s : string) : iProp Σ :=
    ∃ (a : val) (h : string),
      ⌜v = (a, #h)%V ∧ s = simple_string h⌝.

  Definition susp_p_fill_inv (ps : proph_id) (lb lr : loc) : iProp Σ :=
    lb ↦ #false ∗ ((∃ (bs : list bool), lr ↦ #false ∗ fill_proph_bs ps bs) ∨
      (lr ↦ #true ∗ empty_proph_bs ps)).

  Definition auth_susp_ser_p_fill (v : val) (s : string) : iProp Σ :=
    ∃ (p : proph_id) (lb lr : loc) (a : val) (h : string) (r : bool),
      ⌜v = (#lb, #lr, a, #h, #p)%V ∧ s = simple_string h⌝ ∗
      seq_inv (prover_susp_n N v) (susp_p_fill_inv p lb lr).

  Definition susp_p_unfill_inv (ps : proph_id) (lb lr : loc) : iProp Σ :=
    ∃ (γ : gname), (* 1-1 relation between lb, γ and pid *)
      lg_mapg_frag lb γ ∗
      ((∃ (bs : list bool),
        lb ↦ #false ∗ lr ↦ #false ∗ unfill_proph_bs ps bs ∗ oneshot_pending γ) ∨
      (∃ (r : bool) (bs : list bool) (n : nat),
        lb ↦ #true ∗ lr ↦ #r ∗ proph_bs ps bs ∗ oneshot_done γ n)).

  Definition auth_susp_ser_p_emp (v : val) (s : string) : iProp Σ :=
    ∃ (p : proph_id) (lb lr : loc) (a : val) (h : string) (r : bool),
      ⌜v = (#lb, #lr, a, #h, #p)%V ∧ s = suspended_string⌝ ∗
      seq_inv (prover_susp_n N v) (susp_p_unfill_inv p lb lr).

  (* What it will actually serialize to *)
  Definition auth_susp_ser_p_real (v : val) (s : string) : iProp Σ :=
    auth_susp_ser_p_fill v s ∨ auth_susp_ser_p_emp v s.

  (* What it would serialize to without suspension *)
  Definition auth_susp_ser_p (v : val) (s : string) : iProp Σ :=
    ∃ (p : proph_id) (lb lr : loc) (a : val) (h : string),
      ⌜v = (#lb, #lr, a, #h, #p)%V ∧ s = simple_string h⌝.

  Definition auth_fill_ser_v (v : val) (s : string) : iProp Σ :=
    ∃ (h : string), ⌜s = filled_string h ∧ v = InjLV #h⌝.

  Definition auth_susp_fill_v (v : val) (s : string) : iProp Σ :=
    ∃ (h : string) (susp : loc), 
      ⌜s = filled_string h ∧ v = InjRV #susp⌝ ∗ susp ↦ᵥ{#(3/4)} InjRV #h.

  Definition auth_susp_emp_v (v : val) (s : string) : iProp Σ :=
    ∃ (h : string) (susp : loc) (pid: nat) (p : proph_id),
      ⌜s = suspended_string ∧ v = InjRV #susp⌝ ∗ 
      susp ↦ᵥ{#(3/4)} InjLV (#pid, #p) ∗ proph_v_susp p h.

  Definition auth_susp_emp_v_proph (v : val) : iProp Σ :=
    ∃ (h : string) (susp : loc) (pid: nat) (p : proph_id) pv pt (q : Qp),
      ⌜v = InjRV #susp⌝ ∗ mapg_frag #pid q pv ∗
      ⌜sub_obj pt pv v⌝ ∗ susp ↦ᵥ{#(3/4)} InjLV (#pid, #p) ∗ proph_v_susp p h.

  Definition auth_susp_v_ser_proph_inv (v : val) (s : string) : iProp Σ :=
    (∃ (s1 : string), 
      ⌜s = filled_string (hash s1)⌝ ∗
      auth_susp_fill_v v s) ∨ 
    auth_susp_emp_v_proph v.

  Definition auth_susp_v_ser_proph (v : val) (s : string) : iProp Σ :=
    seq_inv (ver_susp_n N v) (auth_susp_v_ser_proph_inv v s).

  Fixpoint unsusp (t : evi_type) (v un_v : val) : Prop :=
    match t with
    | tprod t1 t2 =>
      ∃ v1 v2 un_v1 un_v2,
        v = (v1, v2)%V ∧ un_v = (un_v1, un_v2)%V ∧
          unsusp t1 v1 un_v1 ∧ unsusp t2 v2 un_v2
    | tsum t1 t2 =>
      (∃ v1 un_v1,
        v = InjLV v1 ∧ un_v = InjLV un_v1 ∧ unsusp t1 v1 un_v1) ∨
      (∃ v2 un_v2,
        v = InjRV v2 ∧ un_v = InjRV un_v2 ∧ unsusp t2 v2 un_v2)
    | tstring | tint => v = un_v
    | tauth =>
      ∃ (lb lr : loc) (a : val) (h : string) (p : proph_id),
        v = (#lb, #lr, a, #h, #p)%V ∧ un_v = (a, #h)%V
    end.

  (* unsuspended *)
  Fixpoint unsusp_ser_p (t : evi_type) (v : val) (s : string) : iProp Σ :=
    match t with
    | tprod t1 t2 => prod_is_ser' v s (unsusp_ser_p t1) (unsusp_ser_p t2)
    | tsum t1 t2 => sum_is_ser' v s (unsusp_ser_p t1) (unsusp_ser_p t2)
    | tstring => string_is_ser v s
    | tint => int_is_ser v s
    | tauth => auth_unsusp_ser_p v s
    end.

  #[global] Instance unsusp_ser_p_persistent t v s : Persistent (unsusp_ser_p t v s).
  Proof. revert v s. induction t => v s; simpl; apply _. Qed.

  (* suspended real *)
  Fixpoint susp_ser_p_real (t : evi_type) (v : val) (s : string) : iProp Σ :=
    match t with
    | tprod t1 t2 => prod_is_ser' v s (susp_ser_p_real t1) (susp_ser_p_real t2)
    | tsum t1 t2 => sum_is_ser' v s (susp_ser_p_real t1) (susp_ser_p_real t2)
    | tstring => string_is_ser v s
    | tint => int_is_ser v s
    | tauth => auth_susp_ser_p_real v s
    end.
 
  #[global] Instance susp_ser_p_real_persistent t v s : Persistent (susp_ser_p_real t v s).
  Proof. revert v s. induction t => v s; simpl; apply _. Qed.

  (* suspended proph *)
  Fixpoint susp_ser_p (t : evi_type) (v : val) (s : string) : iProp Σ :=
    match t with
    | tprod t1 t2 => prod_is_ser' v s (susp_ser_p t1) (susp_ser_p t2)
    | tsum t1 t2 => sum_is_ser' v s (susp_ser_p t1) (susp_ser_p t2)
    | tstring => string_is_ser v s
    | tint => int_is_ser v s
    | tauth => auth_susp_ser_p v s
    end.
 
  #[global] Instance susp_ser_p_proph_persistent t v s : Persistent (susp_ser_p t v s).
  Proof. revert v s. induction t => v s; simpl; apply _. Qed.

  Fixpoint ser_v (t : evi_type) (v : val) (s : string) : iProp Σ :=
    match t with
    | tprod t1 t2 => prod_is_ser' v s (ser_v t1) (ser_v t2)
    | tsum t1 t2 => sum_is_ser' v s (ser_v t1) (ser_v t2)
    | tstring => string_is_ser v s
    | tint => int_is_ser v s
    | tauth => ∃ v1, ⌜v = SOMEV v1⌝ ∗ 
                  (auth_fill_ser_v v1 s ∨ auth_susp_emp_v v1 s)
    end.

  Fixpoint ser_v_proph (t : evi_type) (v : val) (s : string) : iProp Σ :=
    match t with
    | tprod t1 t2 => prod_is_ser' v s (ser_v_proph t1) (ser_v_proph t2)
    | tsum t1 t2 => sum_is_ser' v s (ser_v_proph t1) (ser_v_proph t2)
    | tstring => string_is_ser v s
    | tint => int_is_ser v s
    | tauth => ∃ v1, ⌜v = SOMEV v1⌝ ∗
                       (auth_fill_ser_v v1 s ∨ auth_susp_v_ser_proph v1 s)
  end.
 
  #[global] Instance ser_v_proph_persistent t v s : Persistent (ser_v_proph t v s).
  Proof. revert v s. induction t => v s; simpl; apply _. Qed.

  (* For both prover/verifier
  Fixpoint invalid_value (t : evi_type) (v : val) :=
    match t with
    | tprod t1 t2 =>
      ∃ v1 v2, v = (v1, v2)%V ∧ (invalid_value t1 v1 ∨ invalid_value t2 v2)
    | tsum t1 t2 =>
      (∃ v1, v = InjLV v1 ∧ invalid_value t1 v1) ∨
      (∃ v2, v = InjLV v2 ∧ invalid_value t2 v2)
    | tstring => False
    | tint => False
    | tauth => v = NONEV
    end. *)

  (* Tauth leaf with fragment: unfilled susps carry a [1/N] piece of
     [mapg_frag #pid _ v_outer]. [N] is the total number of B2 leaves
     created at deser time; [v_outer] is the outer value. *)
  Definition auth_sub_susp_count_frags
      (v : val) (c pid N : nat) (v_outer : val) : iProp Σ :=
    ∃ v1, ⌜v = SOMEV v1⌝ ∧
      ((∃ (h : string), ⌜v1 = InjLV #h ∧ c = 0⌝) ∨
        (∃ (susp : loc),
          ⌜v1 = InjRV #susp⌝ ∗
            ((∃ (h : string), susp ↦ᵥ{#1/4} (InjRV #h) ∗ ⌜c = 0⌝) ∨
              (∃ (p : proph_id) γ,
                lg_mapg_frag susp γ ∗
                susp ↦ᵥ{#1/4} InjLV (#pid, #p) ∗ ⌜c = 1⌝ ∗
                mapg_frag #pid (1 / pos_to_Qp (Pos.of_nat N))%Qp v_outer ∗
                cap_frag pid N ∗
                (oneshot_pending γ ∨ ∃ n, ⌜n > pid⌝ ∗ oneshot_done γ n))))).

  Fixpoint sub_susp_count
      (t : evi_type) (v : val) (c id N : nat) (v_outer : val) : iProp Σ :=
    match t with
    | tprod t1 t2 =>
        ∃ (c1 c2 : nat) (v1 v2 : val),
          ⌜v = (v1, v2)%V ∧ (c1 + c2)%nat = c⌝ ∗
          sub_susp_count t1 v1 c1 id N v_outer ∗
          sub_susp_count t2 v2 c2 id N v_outer
    | tsum t1 t2 =>
        (∃ (v1 : val), ⌜v = InjLV v1⌝ ∗ sub_susp_count t1 v1 c id N v_outer) ∨
        (∃ (v2 : val), ⌜v = InjRV v2⌝ ∗ sub_susp_count t2 v2 c id N v_outer)
    | tstring => string_valid_val v ∧ ⌜c = 0⌝
    | tint => int_valid_val v ∧ ⌜c = 0⌝
    | tauth => auth_sub_susp_count_frags v c id N v_outer
    end.

  (* Accumulated fragment at the top level. The invariant is that every
     filled susp has returned its [1/N] piece here, so the aggregator holds
     [(N - c)/N]. When [c = N] nothing has been returned yet (left disjunct,
     no fragment). When [c = 0] the aggregator holds the full fraction. *)
  Definition count_aggregator (c id N : nat) (v : val) : iProp Σ :=
    ⌜c = N⌝ ∨
    (⌜c < N⌝ ∗ ∃ q,
      ⌜(q * pos_to_Qp (Pos.of_nat N))%Qp = pos_to_Qp (Pos.of_nat (N - c))⌝ ∗
      mapg_frag #id q v).

  Definition sub_susp_count_frags
      (t : evi_type) (v : val) (c id N : nat) : iProp Σ :=
    cap_frag id N ∗ ⌜c ≤ N⌝ ∗
    sub_susp_count t v c id N v ∗
    count_aggregator c id N v.

  Lemma mapg_remove_count_0 :
    ∀ t v id N m,
      sub_susp_count_frags t v 0 id N -∗
      mapg_auth m
      ==∗ 
        sub_susp_count t v 0 id N v ∗
        mapg_auth (delete #id m).
  Proof. Admitted.

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
      (susp : loc) (p : proph_id) (v_outer : val) :
    id > pid →
    lg_mapg_frag susp γ -∗
    susp ↦ᵥ{#3/4} InjLV (#pid, #p) -∗
    sub_susp_count t (InjRV (InjRV #susp)) c pid Nc v_outer -∗
    oneshot_pending γ ==∗
    oneshot_done γ id ∗
    sub_susp_count t (InjRV (InjRV #susp)) c pid Nc v_outer ∗
    susp ↦ᵥ{#3/4} InjLV (#pid, #p).
Proof. Admitted.
    (* iIntros (Hid) "#Hlg Hsusp Hcount Hpending".
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
          -- iMod (oneshot_transition γ id with "[$Hpending $Hpen]") as "#Hdone".
             iModIntro. iSplitR; [iExact "Hdone"|].
             iSplitR "Hsusp"; [|iExact "Hsusp"].
             simpl.
             iExists (InjRV #susp). iSplit; [done|].
             iRight. iExists susp. iSplit; [done|].
             iRight. iExists p, γ.
             iFrame "Hlg' Hsusp_s Hfrag Hcap'". iSplit; [done|].
             iRight. iExists id. iFrame "Hdone". iPureIntro. done.
          -- iDestruct "Hdone" as (n) "[%Hn #Hdone]".
             by iDestruct (oneshot_invalid with "[$Hpending $Hdone]") as %[].
  Qed. *)

  Lemma oneshot_update (id : nat) :
    ∀ t t' v (c pid Nc : nat) γ (susp : loc) (p : proph_id),
      ⌜id > pid⌝ -∗
      ⌜sub_obj t' v (InjRV #susp)⌝ -∗
      lg_mapg_frag susp γ -∗
      susp ↦ᵥ{#3/4} InjLV (#pid, #p) -∗
      sub_susp_count_frags t v c pid Nc -∗
      oneshot_pending γ ==∗
      oneshot_done γ id ∗ sub_susp_count_frags t v c pid Nc ∗
      susp ↦ᵥ{#3/4} InjLV (#pid, #p).
Proof. Admitted.
    (* iIntros (t t' v c pid Nc γ susp p) "%Hid %Hsub #Hlg Hsusp (#Hcap & %Hle & Hinner & Hagg) Hpending".
    iAssert (∀ v_outer (tind : evi_type) (v : val) (c : nat) (t' : evi_type),
               ⌜sub_obj t' v (InjRV #susp)⌝ -∗
               lg_mapg_frag susp γ -∗
               susp ↦ᵥ{#3/4} InjLV (#pid, #p) -∗
               sub_susp_count tind v c pid Nc v_outer -∗
               oneshot_pending γ ==∗
               oneshot_done γ id ∗
               sub_susp_count tind v c pid Nc v_outer ∗
               susp ↦ᵥ{#3/4} InjLV (#pid, #p))%I
      with "[]" as "Hlem".
    { iClear "Hcap Hlg".
      iIntros (v_outer t0).
      iInduction t0 as [t1 t2 | t1 t2 | | | ] "IH".
      all: iIntros (vind cind tind') "%Hsubind #Hlg Hsusp Hinner Hpending".
      - (* tprod *)
        simpl. iDestruct "Hinner" as (c1 c2 v1 v2 [-> <-]) "[Hc1 Hc2]".
        destruct tind' as [t1' t2' | | | | ]; simpl in Hsubind; try done.
        + destruct Hsubind as (v1' & v2' & Heq & Hdisj). injection Heq as <- <-.
          destruct Hdisj as [<- | [<- | [Hsub1 | Hsub2]]].
          * by iDestruct (sub_susp_count_ne_injr_loc with "Hc1") as %[].
          * by iDestruct (sub_susp_count_ne_injr_loc with "Hc2") as %[].
          * iMod ("IH" $! v1 c1 t1' Hsub1 with "Hlg Hsusp Hc1 Hpending")
              as "(#Hdone & Hc1' & Hsusp')".
            iModIntro. iFrame "Hdone Hsusp'".
            iExists c1, c2, v1, v2. by iFrame.
          * iMod ("IH1" $! v2 c2 t2' Hsub2 with "Hlg Hsusp Hc2 Hpending")
              as "(#Hdone & Hc2' & Hsusp')".
            iModIntro. iFrame "Hdone Hsusp'".
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
               iMod (sub_susp_count_eats_susp id _ cind pid Nc γ susp p v_outer
                 with "Hlg Hsusp Hc Hpending") as "(#Hdone & Hc' & Hsusp')";
                 [done|].
               iModIntro. iFrame "Hdone Hsusp'".
               iRight. iExists (InjRV (InjRV #susp)). by iFrame.
      - (* tstring *)
        simpl. iDestruct "Hinner" as "[Hv %Hc]". iDestruct "Hv" as (s) "->".
        destruct tind'; simpl in Hsubind; try done.
        + destruct Hsubind as (? & ? & Heq & _); discriminate.
        + destruct Hsubind as (? & [(Heq & _) | (Heq & _)]); discriminate.
        + destruct Hsubind as (? & [Heq|Heq] & _); discriminate.
      - (* tint *)
        simpl. iDestruct "Hinner" as "[Hv %Hc]". iDestruct "Hv" as (z) "->".
        destruct tind'; simpl in Hsubind; try done.
        + destruct Hsubind as (? & ? & Heq & _); discriminate.
        + destruct Hsubind as (? & [(Heq & _) | (Heq & _)]); discriminate.
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
    iMod ("Hlem" $! v t v c t' Hsub with "Hlg Hsusp Hinner Hpending")
      as "(#Hdone & Hinner & Hsusp)".
    iModIntro. iFrame "Hdone Hsusp Hcap Hinner Hagg". done.
  Qed. *)

  (* When [c = 0] (all susps filled) and [Nc ≠ 0], the aggregator has
     accumulated every [1/Nc] piece, giving the full fragment. *)
  Lemma sub_susp_count_frags_terminated t v id Nc :
    Nc ≠ 0 →
    sub_susp_count_frags t v 0 id Nc -∗ mapg_frag #id 1 v.
Proof. Admitted.
    (* iIntros (HN) "(_ & %Hle & _ & Hagg)".
    iDestruct "Hagg" as "[%Heq | [%Hlt Hq]]".
    - lia.
    - iDestruct "Hq" as (q Heqq) "Hfrag".
      replace (Nc - 0) with Nc in Heqq by lia.
      assert (q = 1%Qp) as ->; last done.
      rewrite (Qp.mul_comm q) in Heqq.
      apply (Qp.mul_inj_r (pos_to_Qp (Pos.of_nat Nc))).
      rewrite Qp.mul_1_r. exact Heqq.
  Qed. *)

  (* Substantive tauth B2 update: reached via tsum's right branch when the
     external [susp] matches a B2 leaf. Consumes [c = 1] for the leaf,
     releases the [1/Nc] fragment, steps the verifier store. *)
  Lemma count_update_eats_susp K tᵥ v' t (susp : loc) (c pid Nc : nat) (h : string) (v_outer : val) :
    sub_susp_count t (InjRV (InjRV #susp)) c pid Nc v_outer -∗
    susp ↦ᵥ{#(3/4)} InjLV (#pid, v') -∗
    spec_verifier tᵥ (fill K (#susp <- InjRV #h))
    ={⊤}=∗
      ⌜c = 1⌝ ∗
      sub_susp_count t (InjRV (InjRV #susp)) (c-1) pid Nc v_outer ∗
      susp ↦ᵥ{#(3/4)} InjRV #h ∗
      spec_verifier tᵥ (fill K (#())) ∗
      mapg_frag #pid (1 / pos_to_Qp (Pos.of_nat Nc))%Qp v_outer.
Proof. Admitted.
    (* iIntros "Hinner Hsusp Hspec".
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
          iDestruct (pointstoS_agree with "Hsusp Hsusp_s") as %[_ Heqvals].
          injection Heqvals as Heqv'. subst v'.
          iCombine "Hsusp Hsusp_s" as "Hsusp_full".
          rewrite Qp.three_quarter_quarter.
          iMod (step_verifier_store with "[$Hsusp_full $Hspec]") as "(Hspec & Hsusp_full)"; [done|].
          iEval (rewrite -Qp.three_quarter_quarter) in "Hsusp_full".
          iDestruct "Hsusp_full" as "[Hsusp Hsusp_s]".
          iModIntro.
          iSplitR; [done|].
          iSplitR "Hsusp Hspec Hfrag".
          { iExists (InjRV #susp). iSplit; [done|].
            iRight. iExists susp. iSplit; [done|].
            iLeft. iExists h. iFrame "Hsusp_s". subst c. done. }
          iFrame "Hsusp Hspec Hfrag".
  Qed. *)

  Lemma count_update :
    ∀ K tᵥ v v' (t t' : evi_type) (susp : loc) (c pid Nc : nat) (h : string),
      ⌜sub_obj t' v (InjRV #susp)⌝ -∗
      sub_susp_count_frags t v c pid Nc -∗
      susp ↦ᵥ{#(3/4)} InjLV (#pid, v') -∗
      spec_verifier tᵥ (fill K (#susp <- InjRV #h))
      ={⊤}=∗ sub_susp_count_frags t v (c-1) pid Nc ∗
        susp ↦ᵥ{#(3/4)} InjRV #h ∗
        spec_verifier tᵥ (fill K (#())).
  Proof. Admitted.
    (* iIntros (K tᵥ v v' t t' susp c pid Nc h) "%Hsub (#Hcap & %Hle & Hinner & Hagg) Hsusp Hspec".
    (* Run the inner structural induction to produce a fresh [1/Nc] fragment
       and a decremented inner predicate. v_outer is threaded unchanged. *)
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
               iMod (count_update_eats_susp with "Hc Hsusp' Hspec'") as
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
      - (* tind = tauth — sub_obj at tauth forces v to be SOMEV (InjL/InjR v')
           with v' = InjRV #susp, which doesn't match any B1/B2 case (those
           have v1 = InjRV #loc_literal). *)
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
    (* Combine the new [1/Nc] fragment with the existing aggregator. *)
    iModIntro. iFrame "Hsusp Hspec Hcap".
    iSplit; [iPureIntro; lia|]. iFrame "Hinner".
    (* Aggregator update: (Nc-c)/Nc + 1/Nc = (Nc-(c-1))/Nc. *)
    iDestruct "Hagg" as "[%HcN | [%HcN Hq]]".
    - (* old aggregator empty (c = Nc); new has [1/Nc]. *)
      iRight. iSplit; [iPureIntro; lia|].
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

  (* Fixpoint coherent_t (t t' : evi_type) (v : val) : Prop :=
    match t, t' with
    | tprod t1 t2, tprod t1' t2' =>
      ∃ v1 v2, v = (v1, v2) ∧
          coherent_t t1 t1' v1 ∧ coherent_t t2 t2' v2
    | tsum t1 t2, tsum t1' t2' =>
      ∃ v',
        (v = InjLV v' ∧ coherent_t t1 t1' v') ∨
        (v = InjRV v' ∧ coherent_t t2 t2' v')
    | tstring, _ | tint, _ | tauth, _ => t = t'
    end. *)

  Definition susp_p_ser_spec (ser : val) (t : evi_type) : iProp Σ :=
    ∀ (E : coPset) (a1 : val) (s : string),
      ⌜↑prover_susp_set N ⊆ E⌝ -∗
      {{{ susp_ser_p_real t a1 s }}}
        ser a1
      {{{ RET #s; True }}}.

  Definition unsusp_p_ser_spec (ser : val) (t : evi_type) : iProp Σ :=
    ∀ (v : val) (s : string),
      {{{ unsusp_ser_p t v s }}}
        ser v
      {{{ RET #s; True }}}.

  Definition suspend_spec (suspend : val) (A : lrel Σ) (t : evi_type) : iProp Σ :=
    ∀ t' (v un_v a2 a3 : val) s,
      {{{ ⌜unsusp t' v un_v⌝ ∗ ▷ A v a2 a3 ∗ susp_ser_p t' v s }}}
        suspend un_v
      {{{ v', RET v'; A v' a2 a3 ∗ susp_ser_p t v' s ∗
          ∃ s', susp_ser_p_real t v' s' }}}.

  Definition unsuspend_spec (unsuspend : val) (A : lrel Σ) (t : evi_type) : iProp Σ :=
    ∀ E (a1 a2 a3 : val),
      ⌜↑prover_susp_set N ⊆ E⌝ -∗
      {{{ ▷ A a1 a2 a3 ∗ seq_tok E }}}
        unsuspend a1
      {{{ un_v s, RET un_v; seq_tok E ∗
          ⌜unsusp t a1 un_v⌝ ∗ unsusp_ser_p t un_v s }}}.
            (* if o is Some v then ∃ s, unsusp_ser_p t v s (* ∗ s_is_ser_p_proph t a1 s'*)
            else ⌜invalid_value t a1⌝ ∨ (∃ s, unsusp_ser_p t a1 s) }}}. *)

  Definition suspend_spec_bin (suspend : val) (A : lrel_bin Σ) (t : evi_type) : iProp Σ :=
    ∀ t' (v un_v a3 : val),
      {{{ ⌜unsusp t' v un_v⌝ ∗ ▷ A v a3 }}}
        suspend un_v
      {{{ v', RET v'; A v' a3 ∗ ∃ s', susp_ser_p_real t v' s' }}}.

  Definition unsuspend_spec_bin (unsuspend : val) (A : lrel_bin Σ) (t : evi_type) : iProp Σ :=
    ∀ E (a1 a3 : val),
      ⌜↑prover_susp_set N ⊆ E⌝ -∗
      {{{ ▷ A a1 a3 ∗ seq_tok E }}}
        unsuspend a1
      {{{ un_v, RET un_v; seq_tok E ∗ ⌜unsusp t a1 un_v⌝ }}}.

  Definition v_deser_spec (v_deser : val) (A : lrel_tern Σ) (t : evi_type) : iProp Σ :=
    □(∀ K tᵥ (id : nat) a1 a2 a3 (s s' : string) t' m,
      spec_verifier tᵥ (fill K (v_deser #id))
      ={⊤}=∗ ∃ (v_deser_par: val),
        spec_verifier tᵥ (fill K v_deser_par) ∗
        □(∀ K tᵥ,
          A a1 a2 a3 -∗ susp_ser_p_real t' a1 s -∗
          susp_ser_p t' a1 s' -∗
          spec_verifier tᵥ (fill K (v_deser_par #s)) -∗
          mapg_auth m
          ={⊤}=∗ ∃ (c : nat) (a2' : val) m',
            mapg_auth m' ∗
            spec_verifier tᵥ (fill K (SOMEV a2')) ∗
            sub_susp_count_frags t a2' c id c ∗
              (⌜(c = 0 ∧ m = m') ∨
                (c ≠ 0 ∧ m' = mapg_insert_def m #id a2')⌝) ∗
            A a1 a2' a3 ∗ ser_v_proph t a2' s')).

  Definition v_deser_spec_un (v_deser : val) (A : lrel_un Σ) (t : evi_type) : iProp Σ :=
    □(∀ K tᵥ (id : nat) (s' : string),
      spec_verifier tᵥ (fill K (v_deser #id))
      ={⊤}=∗ ∃ (v_deser_par: val),
        spec_verifier tᵥ (fill K v_deser_par) ∗
        □(∀ K tᵥ,
          spec_verifier tᵥ (fill K (v_deser_par #s'))
          ={⊤}=∗
            (∃ (c : nat) (a2' : val) s'',
              spec_verifier tᵥ (fill K (SOMEV a2')) ∗
              ser_v_proph t a2' s'' ∗ sub_susp_count_frags t a2' c id c ∗
              A a2') ∨
            spec_verifier tᵥ (fill K NONEV))).

  Definition v_count_spec (v_count : val) (t : evi_type) : iProp Σ :=
    □(∀ K tᵥ a c id Nc v_outer,
      sub_susp_count t a c id Nc v_outer -∗
      spec_verifier tᵥ (fill K (v_count a))
      ={⊤}=∗
        sub_susp_count t a c id Nc v_outer ∗
        spec_verifier tᵥ (fill K #c)).

  Definition v_ser_spec (v_ser : val) (t : evi_type) : iProp Σ :=
    □(∀ K tᵥ a s id Nc v_outer,
      sub_susp_count t a 0 id Nc v_outer -∗ ser_v_proph t a s -∗
      spec_verifier tᵥ (fill K (v_ser a))
      ={⊤}=∗
        sub_susp_count t a 0 id Nc v_outer ∗ ser_v_proph t a s ∗
        spec_verifier tᵥ (fill K (SOMEV #s))).
      
  Definition v_auth_ser_spec (v_ser : val) (A : lrel_tern Σ) (t : evi_type) : iProp Σ :=
    □(∀ K tᵥ a1 a2 a3,
      ▷ (lrel_tern_tern A) a1 a2 a3 -∗
      spec_verifier tᵥ (fill K (v_ser a2))
      ={⊤}=∗ ∃ s,
        ser_v t a2 s ∗ spec_verifier tᵥ (fill K (SOMEV #s))).
      
  Definition v_auth_ser_spec_un (v_ser : val) (A : lrel_un Σ) (t : evi_type) : iProp Σ :=
    □(∀ K tᵥ a2 s,
      A a2 -∗
      spec_verifier tᵥ (fill K (v_ser a2))
      ={⊤}=∗ 
        ser_v t a2 s ∗ spec_verifier tᵥ (fill K (SOMEV #s))).

  Definition invalid_val (A : lrel_tern Σ) : iProp Σ :=
    □ ∀ (p : proph_id) v2 v3,
      (lrel_tern_tern A) #p v2 v3 -∗ False.

  #[global] Instance invalid_val_persistent A : Persistent (invalid_val A).
  Proof. apply _. Qed.

  Definition lrel_tern_evidence (A : lrel_tern Σ) : lrel Σ := LRel (λ v1 v2 _,
    ∃ (t : evi_type) (p_ser_susp p_ser_unsusp p_susp p_unsusp v_ser v_deser v_count : val),
      ⌜v1 = (p_ser_susp, p_ser_unsusp, p_susp, p_unsusp)%V⌝ ∗ ⌜v2 = (v_ser, v_deser, v_count)%V⌝ ∗
      invalid_val A ∗
      unsusp_p_ser_spec p_ser_unsusp t ∗ susp_p_ser_spec p_ser_susp t ∗
      suspend_spec p_susp A t ∗ unsuspend_spec p_unsusp A t ∗
      v_ser_spec v_ser t ∗ v_auth_ser_spec v_ser A t ∗
      v_deser_spec v_deser A t ∗ v_count_spec v_count t)%I.

  Definition lrel_bi_evidence (A : lrel_bin Σ) : lrel_bin Σ := LRelBin (λ v1 _,
    ∃ (t : evi_type) (p_ser_susp p_ser_unsusp p_susp p_unsusp v_ser v_deser v_count : val),
      ⌜v1 = (p_ser_susp, p_ser_unsusp, p_susp, p_unsusp)%V⌝ ∗
      unsusp_p_ser_spec p_ser_unsusp t ∗ susp_p_ser_spec p_ser_susp t ∗
      suspend_spec_bin p_susp A t ∗ unsuspend_spec_bin p_unsusp A t)%I.

  Definition lrel_un_evidence (A : lrel_un Σ) : lrel_un Σ := LRelUn (λ v2,
    ∃ (t : evi_type) (v_ser v_deser v_count : val),
      ⌜v2 = (v_ser, v_deser, v_count)%V⌝ ∗
      v_ser_spec v_ser t ∗ v_auth_ser_spec_un v_ser A t ∗
      v_deser_spec_un v_deser A t ∗ v_count_spec v_count t)%I.

  Definition lrel_evidence' (A : lrel_tern Σ) : lrel_ternC Σ :=
    LRelTern (lrel_tern_evidence A)
             (lrel_bi_evidence (lrel_tern_bin A))
             (lrel_un_evidence (lrel_tern_un A)).

  Program Definition lrel_evidence : kindO Σ (⋆ ⇒ ⋆)%kind := λne A, lrel_evidence' A.
  Next Obligation.
    intros ????.
  Admitted.
  

  (* refines_Auth_pair proof outline.

     The statement is the relational interpretation of
       ∀ α β, evidence α → evidence β → evidence (α * β)
     applied to the prover/verifier/ideal pair-combinators.  After the
     [lrel_tern_as_lrel] coercion the goal is a 3-way conjunction

       lrel_tern_tern (⟦…⟧ Δ) p v i
       ∧ lrel_tern_bin  (⟦…⟧ Δ) p i
       ∧ lrel_tern_un   (⟦…⟧ Δ) v

     We split these via [iSplit; [|iSplit]] and only attempt the
     ternary branch; the binary and unary branches are [admit]ed per
     the task scope.

     The ternary branch itself fans out further.  At each intermediate
     arrow (outer ∀α, inner ∀β, after introducing the evidence for α,
     after introducing the evidence for β) the return relation is
     again a [lrel_tern_as_lrel] applied to three values, producing
     another 3-way conjunction that must be split; the binary and
     unary sub-goals at each level are locally [admit]ed.

     Finally, at the innermost ternary obligation the goal is
     [lrel_tern_evidence (lrel_tern_prod A B)] applied to the
     pair-building closures, which bundles eight specs (see
     [lrel_tern_evidence] at line ~1173):

       1. unsusp_p_ser_spec  — [prod_ser''] on fully-unsuspended pair
       2. susp_p_ser_spec    — [prod_ser''] on real-suspended pair
       3. suspend_spec       — pair-[suspend] preserves A
       4. unsuspend_spec     — pair-[unsuspend] preserves A
       5. v_ser_spec         — verifier [prod_ser''] on pair after proph
       6. v_auth_ser_spec    — verifier ser from A pointer
       7. v_deser_spec       — verifier [prod_deser] reconstruction
       8. v_count_spec       — [prod_count] sums component counts

     Each sub-proof destructures a [prod_is_ser' / prod_valid_val' /
     sub_susp_count] witness at the [tprod] case, steps through the
     combinator wrapper, chains the corresponding component spec from
     [HA]/[HB], and reassembles the pair at the post-condition.  The
     deserialization obligation (7) routes through
     [prod_deser'_complete] (serialization_susp.v:837).

     This is a substantial piece of work (on the order of several
     hundred Iris tactic lines); the structure is recorded here in
     comments and in the plan file for follow-up, and the whole lemma
     stays [Admitted] for now. *)
  Lemma refines_Auth_pair Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆; ⋆, var2 var1 → var2 var0 → var2 (var1 * var0) ⟧
      (ext Δ lrel_evidence) p_Auth_pair v_Auth_pair i_Auth_pair.
  Proof.
    iSplit; [|iSplit]; interp_unfold!; last first.
    { (* unary  *) admit. }
    { (* binary *) admit. }
    (* ternary *)
    iIntros (A v1 v2 v3) "!# _"; rewrite -/interp.
    iIntros (????) "Hv Hi Htok".
    rewrite /p_Auth_pair /v_Auth_pair /i_Auth_pair.
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iSplit; [|iSplit]; interp_unfold!; last first.
    { (* inner-after-A unary *) admit. }
    { (* inner-after-A binary *) admit. }
    iIntros (B w1 w2 w3) "!# _"; rewrite -/interp.
    iIntros (????) "Hv Hi Htok". v_pures; i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iSplit; [|iSplit]; interp_unfold!; last first.
    { (* inner-after-B unary *) admit. }
    { (* inner-after-B binary *) admit. }
    iIntros (vA1 vA2 vA3) "!# #HA".
    interp_unfold! in "HA".
    iDestruct "HA" as "(HA_tern & #HA_bin & #HA_un)".
    rewrite interp_var2_ext3 interp_var1_ext2.
    iDestruct "HA_tern" as (tA p_ssA p_usA p_spA p_uspA v_sA v_dA v_cA -> ->)
      "(#HinvA & #HusserA & #HsserA & #HsuspA & #HunsuspA & HvserA & HvauthserA & HvdeserA & HvcountA)".
    fold v_ser_spec.
    iIntros (????) "Hv Hi Htok". v_pures; i_pures; wp_pures. 
    iModIntro. iFrame. clear.
    iSplit; [|iSplit]; interp_unfold!; last first.
    { (* inner-after-HA unary *) admit. }
    { (* inner-after-HA binary *) admit. }
    iIntros (vB1 vB2 vB3) "!# #HB".
    interp_unfold! in "HB".
    iDestruct "HB" as "(HB_tern & #HB_bin & #HB_un)".
    rewrite interp_var2_ext3 interp_var0_ext1.
    iDestruct "HB_tern" as (tB p_ssB p_usB p_spB p_uspB v_sB v_dB v_cB -> ->)
      "(#HinvB & #HusserB & #HsserB & #HsuspB & #HunsuspB & HvserB & HvauthserB & HvdeserB & HvcountB)".
    iIntros (????) "Hv Hi Htok".
    rewrite /prod_ser'' /prod_ser /prod_count.
    v_pures; i_pures; wp_pures. 
    iModIntro. iFrame.
    (* Final 3-way split: prove only the ternary [lrel_tern_evidence]. *)
    iSplit; [|iSplit]; interp_unfold!; last first.
    { (* final unary  *) admit. }
    { (* final binary *) admit. }
    (* Ternary evidence for the product. *)
    rewrite interp_var2_ext3.
    iExists (tprod tA tB), _, _, _, _, _, _, _.
    iSplit; [done|]. iSplit; [done|].
    iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit]]]]]]].
    - (* 0. invalid_val *)
      iIntros "!#" (p v2 v3) "#HA".
      rewrite interp_tern_prod_unfold.
      iDestruct "HA" as (? ? ? ? ? ? ?) "H". discriminate.
    - (* 1. unsusp_p_ser_spec *)
      iIntros (v s Ψ) "!# Hser HΨ".
      iDestruct "Hser" as (a1 a2 sa sb [-> ->]) "[Hussera Husserb]".
      wp_pures.
      wp_apply ("HusserA" with "Hussera"). iIntros "_". wp_pures.
      wp_apply ("HusserB" with "Husserb"). iIntros "_". wp_pures.
      unfold prod_ser_str. iApply "HΨ". by iModIntro.
    - (* 2. susp_p_ser_spec *)
      iIntros (E a1 s HE Ψ) "!# Hser HΨ". simpl. wp_pures.
      iDestruct "Hser" as (ua ub s1 s2 [-> ->]) "[#Hser1 #Hser2]".
      wp_pures.
      wp_apply ("HsserA" with "[//] Hser1"). iIntros "_". wp_pures.
      wp_apply ("HsserB" with "[//] Hser2"). iIntros "_". wp_pures.
      unfold prod_ser_str. iApply "HΨ". by iModIntro.
    - (* 3. suspend_spec *)
      iIntros (t v un_v a2 a3 sa Ψ) "!# (%Hunsusp & #HA' & #Hser) HΨ".
      wp_pures.
      iDestruct "HA'" as "[#HA1 [#HA2 #HA3]]".
      interp_unfold! in "HA1".
      (* iEval (cbv [lrel_tern_tern lrel_tern_prod lrel_car]) in "HA1". *)
      iDestruct "HA1" as (wa1 wa2 wa3 wb1 wb2 wb3) "(-> & -> & -> & H1 & H2)".
      destruct t; simpl in Hunsusp.
      { (* tprod *)
        destruct Hunsusp as (? & ? & un_v1 & un_v2 & [= -> ->] & -> & Hunsusp1 & Hunsusp2).
        iSimpl in "Hser".
        iDestruct "Hser" as (? ? sa1 sa2 [[= -> ->] ->]) "[#Hser1 #Hser2]".
        rewrite interp_bin_prod_unfold. rewrite interp_un_prod_unfold.
        (* iEval (cbv [lrel_tern_bin lrel_tern_prod lrel_bin_car]) in "HA2".
        iEval (cbv [lrel_tern_un lrel_tern_prod lrel_un_car]) in "HA3".
        interp_unfold! in "HA2". *)
        iDestruct "HA2" as (? ? ? ?) "(%Heq1 & %Heq2 & #HA2a & #HA2b)".
        injection Heq1 as -> ->. injection Heq2 as -> ->.
        iDestruct "HA3" as (? ? Heq3) "[#HA3a #HA3b]". injection Heq3 as -> ->.
        wp_pures.
        wp_bind (p_spB _).
        wp_apply ("HsuspB" with "[]").
        { iSplit; [done|]. iFrame "Hser2". iNext.
          rewrite interp_var0_ext1.
          iSplit; [|iSplit]. 
          - destruct B; iExact "H2".
          - destruct B; iExact "HA2b".
          - destruct B; iExact "HA3b". }
        iIntros (vb') "(#HBv' & #Hserv'b & Hreal_b)".
        wp_bind (p_spA _).
        wp_apply ("HsuspA" with "[]").
        { iSplit; [done|]. iFrame "Hser1". iNext.
          rewrite interp_var1_ext2.
          iSplit; [|iSplit].
          - destruct A; iExact "H1".
          - destruct A; iExact "HA2a".
          - destruct A; iExact "HA3a". }
        iIntros (va') "(#HAv' & #Hserv'a & Hreal_a)".
        wp_pures. iApply "HΨ". iModIntro. iSplit; [|iSplit].
        - iDestruct "HAv'" as "[#Av1 [#Av2 #Av3]]".
          iDestruct "HBv'" as "[#Bv1 [#Bv2 #Bv3]]".
          iSplit; [|iSplit]; interp_unfold!;
            rewrite interp_var0_ext1; rewrite interp_var1_ext2.
          { iExists _, _, _, _, _, _. do 3 (iSplit; [done|]).
            iSplit; [destruct A; iExact "Av1"|destruct B; iExact "Bv1"]. }
          { iExists _, _, _, _. iSplit; [done|]. iSplit; [done|].
            iSplit; [destruct A; iExact "Av2"|destruct B; iExact "Bv2"]. }
          { iExists _, _. iSplit; [done|].
            iSplit; [destruct A; iExact "Av3"|destruct B; iExact "Bv3"]. }
        - iExists _, _, _, _. iSplit; [done|]. by iSplit.
        - iDestruct "Hreal_a" as (sra) "Hra". iDestruct "Hreal_b" as (srb) "Hrb".
          iExists (prod_ser_str sra srb), _, _, _, _. iSplit; [done|].
          by iFrame "Hra Hrb". }
      { (* tsum *)
        destruct Hunsusp as [(? & ? & Habs & _) | (? & ? & Habs & _)]; discriminate. }
      { (* tstring *)
        iDestruct "Hser" as %(? & Habs & _); discriminate. }
      { (* tint *)
        iDestruct "Hser" as %(? & Habs & _); discriminate. }
      { (* tauth *) 
        destruct! Hunsusp. simplify_eq.
        rewrite interp_var0_ext1.
        iExFalso. by iApply "HinvB". }
    - (* 4. unsuspend_spec *)
      iIntros (E a1 a2 a3 HE Ψ) "!# [#HA Htok] HΨ".
      wp_pures.
      iDestruct "HA" as "[#HA1 [#HA2 #HA3]]".
      interp_unfold! in "HA1".
      iDestruct "HA1" as (wa1 wa2 wa3 wb1 wb2 wb3) "(-> & -> & -> & H1 & H2)".
      rewrite interp_bin_prod_unfold. rewrite interp_un_prod_unfold.
      iDestruct "HA2" as (? ? ? ?) "(%Heq1 & %Heq2 & #HA2a & #HA2b)".
      injection Heq1 as -> ->. injection Heq2 as -> ->.
      iDestruct "HA3" as (? ? Heq3) "[#HA3a #HA3b]". injection Heq3 as -> ->.
      wp_pures.
      wp_bind (p_uspB _).
      wp_apply ("HunsuspB" with "[//] [$Htok]").
      { rewrite interp_var0_ext1.
        iSplit; [|iSplit]; iNext.
        - destruct B; iExact "H2".
        - destruct B; iExact "HA2b".
        - destruct B; iExact "HA3b". }
      iIntros (un_vb sb) "(Htok & %Hunsuspb & #Hsserb)".
      wp_bind (p_uspA _).
      wp_apply ("HunsuspA" with "[//] [$Htok]").
      { rewrite interp_var1_ext2.
        iSplit; [|iSplit]; iNext.
        - destruct A; iExact "H1".
        - destruct A; iExact "HA2a".
        - destruct A; iExact "HA3a". }
      iIntros (un_va sa) "(Htok & %Hunsuspa & #Hssera)".
      wp_pures. iApply ("HΨ" $! (un_va, un_vb)%V (prod_ser_str sa sb)).
      iFrame. iModIntro. iSplit.
      { iPureIntro. eexists _, _, un_va, un_vb. done. }
      iExists _, _, sa, sb. iFrame "#". done.
    - (* 5. v_ser_spec *)
      iIntros (K tᵥ3 a s id Nc v_outer) "!# Hcnt #Hser Hspec".
      iDestruct "Hcnt" as (c1 c2 pv1 pv2 [-> Hsum]) "[Hcnt1 Hcnt2]".
      iDestruct "Hser" as (? ? s1 s2 [Heqv ->]) "[#Hser1 #Hser2]".
      injection Heqv as -> ->.
      assert (c1 = 0%nat) as -> by lia.
      assert (c2 = 0%nat) as -> by lia.
      v_pures.
      v_bind tᵥ3 (v_sA _).
      iMod ("HvserA" with "Hcnt1 Hser1 Hspec") as "(Hcnt1 & _ & Hspec) /=".
      v_pures.
      v_bind tᵥ3 (v_sB _).
      iMod ("HvserB" with "Hcnt2 Hser2 Hspec") as "(Hcnt2 & _ & Hspec) /=".
      simpl. v_pures.
      iModIntro. iFrame "#". rewrite /prod_ser_str.
      iSplitL "Hcnt1 Hcnt2".
      { iExists 0%nat, 0%nat, _, _. iFrame. iPureIntro. done. }
      repeat (iSplit; eauto).
    - (* 6. v_auth_ser_spec *)
      iIntros (K tᵥ3 a1 a2 a3) "!# #HA Hv".
      rewrite /prod_ser''. v_pures.
      rewrite interp_tern_prod_unfold.
      rewrite interp_var1_ext2 interp_var0_ext1.
      iDestruct "HA" as (??????) "(>-> & >-> & >-> & Ha & Hb)".
      v_pures. v_bind (v_sA _).
      iMod ("HvauthserA" with "Ha Hv") as (?) "[Hserav Hv] /=".
      v_pures. v_bind (v_sB _).
      iMod ("HvauthserB" with "Hb Hv") as (?) "[Hserbv Hv] /=".
      v_pures.
      iModIntro. iFrame.
      iSplit; eauto.
    - (* 7. v_deser_spec      *) admit.
    - (* 8. v_count_spec *)
      iIntros (K tᵥ3 a c id Nc v_outer) "!# Hcnt Hspec".
      iDestruct "Hcnt" as (c1 c2 pv1 pv2 [-> Hsum]) "[Hcnt1 Hcnt2]".
      v_pures.
      v_bind tᵥ3 (v_cB pv2).
      iMod ("HvcountB" with "Hcnt2 Hspec") as "[Hcnt2 Hspec]".
      v_bind tᵥ3 (v_cA _).
      v_pures.
      v_bind tᵥ3 (v_cA _).
      iMod ("HvcountA" with "Hcnt1 Hspec") as "[Hcnt1 Hspec]".
      simpl. v_pures.
      assert ((c1 + c2)%Z = c) as -> by lia.
      iModIntro. iFrame.
      iPureIntro. split; [reflexivity|lia].
  Admitted.

  Lemma refines_Auth_sum Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆; ⋆, var2 var1 → var2 var0 → var2 (var1 + var0) ⟧
      (ext Δ lrel_evidence) p_Auth_sum v_Auth_sum i_Auth_sum.
  Proof.
    iSplit; [|iSplit]; interp_unfold!; last first.
    { (* unary  *) admit. }
    { (* binary *) admit. }
    (* ternary *)
    iIntros (A v1 v2 v3) "!# _"; rewrite -/interp.
    iIntros (????) "Hv Hi Htok".
    rewrite /p_Auth_sum /v_Auth_sum /i_Auth_sum.
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iSplit; [|iSplit]; interp_unfold!; last first.
    { (* inner-after-A unary *) admit. }
    { (* inner-after-A binary *) admit. }
    iIntros (B w1 w2 w3) "!# _"; rewrite -/interp.
    iIntros (????) "Hv Hi Htok". v_pures; i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iSplit; [|iSplit]; interp_unfold!; last first.
    { (* inner-after-B unary *) admit. }
    { (* inner-after-B binary *) admit. }
    iIntros (vA1 vA2 vA3) "!# #HA".
    interp_unfold! in "HA".
    rewrite interp_var2_ext3 interp_var1_ext2.
    iDestruct "HA" as "(HA_tern & #HA_bin & #HA_un)".
    iDestruct "HA_tern" as (tA p_ssA p_usA p_spA p_uspA v_sA v_dA v_cA -> ->)
      "(#HinvA & #HusserA & #HsserA & #HsuspA & #HunsuspA & HvserA & HvauthserA & HvdeserA & HvcountA)".
    iIntros (????) "Hv Hi Htok". v_pures; i_pures; wp_pures. iModIntro. iFrame.
    iSplit; [|iSplit]; interp_unfold!; last first.
    { (* inner-after-HA unary *) admit. }
    { (* inner-after-HA binary *) admit. }
    iIntros (vB1 vB2 vB3) "!# #HB".
    interp_unfold! in "HB".
    rewrite interp_var2_ext3 interp_var0_ext1.
    iDestruct "HB" as "(HB_tern & #HB_bin & #HB_un)".
    iDestruct "HB_tern" as (tB p_ssB p_usB p_spB p_uspB v_sB v_dB v_cB -> ->)
      "(#HinvB & #HusserB & #HsserB & #HsuspB & #HunsuspB & HvserB & HvauthserB & HvdeserB & HvcountB)".
    iIntros (????) "Hv Hi Htok".
    rewrite /sum_ser'' /sum_ser /sum_count.
    v_pures; i_pures; wp_pures. iModIntro. iFrame.
    iSplit; [|iSplit]; interp_unfold!; last first.
    { (* final unary  *) admit. }
    { (* final binary *) admit. }
    rewrite interp_var2_ext3.
    iExists (tsum tA tB), _, _, _, _, _, _, _.
    iSplit; [done|]. iSplit; [done|].
    iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit]]]]]]].
    - (* 0. invalid_val *)
      iIntros "!#" (p v2 v3) "HA".
      rewrite interp_tern_sum_unfold.
      iDestruct "HA" as (? ? ?) "[(%Heq & _) | (%Heq & _)]"; discriminate.
    - (* 1. unsusp_p_ser_spec *)
      iIntros (v s Ψ) "!# Hser HΨ".
      iDestruct "Hser" as (w s') "[[Hsera [-> ->]]|[Hserb [-> ->]]]".
      + wp_pures.
        wp_apply ("HusserA" with "Hsera"). iIntros "_". wp_pures.
        unfold inl_ser_str. iApply "HΨ". by iModIntro.
      + wp_pures.
        wp_apply ("HusserB" with "Hserb"). iIntros "_". wp_pures.
        unfold inr_ser_str. iApply "HΨ". by iModIntro.
    - (* 2. susp_p_ser_spec *)
      iIntros (E a1 s HE Ψ) "!# Hser HΨ". simpl. wp_pures.
      iDestruct "Hser" as (w s') "[[#Hser1 [-> ->]]|[#Hser2 [-> ->]]]".
      + wp_pures.
        wp_apply ("HsserA" with "[//] Hser1"). iIntros "_". wp_pures.
        rewrite /inl_ser_str. iApply "HΨ". by iModIntro.
      + wp_pures.
        wp_apply ("HsserB" with "[//] Hser2"). iIntros "_". wp_pures.
        rewrite /inr_ser_str. iApply "HΨ". by iModIntro.
    - (* 3. suspend_spec      *)
      iIntros (t v un_v a2 a3 sa Ψ) "!# (%Hunsusp & #HA' & #Hser) HΨ".
      wp_pures.
      iDestruct "HA'" as "[#HA1 [#HA2 #HA3]]".
      rewrite interp_tern_sum_unfold.
      rewrite interp_bin_sum_unfold.
      rewrite interp_un_sum_unfold.
      (* iEval (cbv [lrel_tern_tern lrel_tern_sum lrel_car]) in "HA1".
      iEval (cbv [lrel_tern_bin lrel_tern_sum lrel_bin_car]) in "HA2".
      iEval (cbv [lrel_tern_un lrel_tern_sum lrel_un_car]) in "HA3". *)
      iDestruct "HA1" as (wA wV wI) "[(-> & -> & -> & #H1) | (-> & -> & -> & #H1)]".
      + (* InjL case on v *)
        iDestruct "HA2" as (? ?) "[(%Heq1 & %Heq2 & #HA2L) | (%Heq1 & %Heq2 & _)]";
          last discriminate.
        injection Heq1 as ->. injection Heq2 as ->.
        iDestruct "HA3" as (?) "[(%Heq3 & #HA3L) | (%Heq3 & _)]";
          last discriminate.
        injection Heq3 as ->.
        destruct t; simpl in Hunsusp.
        { (* tprod *)
          destruct Hunsusp as (? & ? & ? & ? & Habs & _); discriminate. }
        { (* tsum *)
          destruct Hunsusp as [(? & un_v1 & [= ->] & -> & Hunsusp1)
                              |(? & ? & Habs & _)]; last discriminate.
          iSimpl in "Hser".
          iDestruct "Hser" as (w s') "[[#Hser1 [%Heqv ->]] | [_ [%Heqv _]]]";
            last discriminate.
          injection Heqv as ->.
          wp_pures.
          wp_apply ("HsuspA" with "[]").
          { iSplit; [done|]. iFrame "Hser1". iNext.
            iSplit; [|iSplit]; rewrite interp_var1_ext2.
            - destruct A; iExact "H1".
            - destruct A; iExact "HA2L".
            - destruct A; iExact "HA3L". }
          iIntros (va') "(#HAv' & #Hserv'a & Hreal_a)".
          wp_pures. iApply "HΨ". iModIntro. iSplit; [|iSplit].
          - iDestruct "HAv'" as "[#Av1 [#Av2 #Av3]]".
            iSplit; [|iSplit]; interp_unfold!;
              rewrite interp_var1_ext2; rewrite interp_var0_ext1.
            { iExists _, _, _. iLeft.
              do 3 (iSplit; [done|]).
              destruct A; iExact "Av1". }
            { iExists _, _. iLeft.
              do 2 (iSplit; [done|]).
              destruct A; iExact "Av2". }
            { iExists _. iLeft.
              iSplit; [done|].
              destruct A; iExact "Av3". }
          - iExists _, _. iLeft. iFrame "Hserv'a". done.
          - iDestruct "Hreal_a" as (sra) "Hra".
            iExists (inl_ser_str sra), _, _.
            iLeft. iFrame "Hra". done. }
        { (* tstring *)
          iDestruct "Hser" as %(? & Habs & _); discriminate. }
        { (* tint *)
          iDestruct "Hser" as %(? & Habs & _); discriminate. }
        { (* tauth *)
          destruct Hunsusp as (? & ? & ? & ? & ? & Habs & _); discriminate. }
      + (* InjR case on v *)
        iDestruct "HA2" as (? ?) "[(%Heq1 & _) | (%Heq1 & %Heq2 & #HA2R)]";
          first discriminate.
        injection Heq1 as ->. injection Heq2 as ->.
        iDestruct "HA3" as (?) "[(%Heq3 & _) | (%Heq3 & #HA3R)]";
          first discriminate.
        injection Heq3 as ->.
        destruct t; simpl in Hunsusp.
        { (* tprod *)
          destruct Hunsusp as (? & ? & ? & ? & Habs & _); discriminate. }
        { (* tsum *)
          destruct Hunsusp as [(? & ? & Habs & _)
                              |(? & un_v2 & [= ->] & -> & Hunsusp2)]; first discriminate.
          iSimpl in "Hser".
          iDestruct "Hser" as (w s') "[[_ [%Heqv _]] | [#Hser2 [%Heqv ->]]]";
            first discriminate.
          injection Heqv as ->.
          wp_pures.
          wp_apply ("HsuspB" with "[]").
          { iSplit; [done|]. iFrame "Hser2". iNext.
            iSplit; [|iSplit]; rewrite interp_var0_ext1.
            - destruct B; iExact "H1".
            - destruct B; iExact "HA2R".
            - destruct B; iExact "HA3R". }
          iIntros (vb') "(#HBv' & #Hserv'b & Hreal_b)".
          wp_pures. iApply "HΨ". iModIntro. iSplit; [|iSplit].
          - iDestruct "HBv'" as "[#Bv1 [#Bv2 #Bv3]]".
            iSplit; [|iSplit]; interp_unfold!;
              rewrite interp_var1_ext2; rewrite interp_var0_ext1.
            { iExists _, _, _. iRight.
              do 3 (iSplit; [done|]).
              destruct B; iExact "Bv1". }
            { iExists _, _. iRight.
              do 2 (iSplit; [done|]).
              destruct B; iExact "Bv2". }
            { iExists _. iRight.
              iSplit; [done|].
              destruct B; iExact "Bv3". }
          - iExists _, _. iRight. iFrame "Hserv'b". done.
          - iDestruct "Hreal_b" as (srb) "Hrb".
            iExists (inr_ser_str srb), _, _.
            iRight. iFrame "Hrb". done. }
        { (* tstring *)
          iDestruct "Hser" as %(? & Habs & _); discriminate. }
        { (* tint *)
          iDestruct "Hser" as %(? & Habs & _); discriminate. }
        { (* tauth *)
          destruct Hunsusp as (? & ? & ? & ? & ? & Habs & _); discriminate. }
    - (* 4. unsuspend_spec    *) admit.
    - (* 5. v_ser_spec *)
      iIntros (K tᵥ3 a s id Nc v_outer) "!# Hcnt #Hser Hspec".
      iDestruct "Hcnt" as "[Hcnt|Hcnt]".
      + iDestruct "Hcnt" as (? ->) "Hcnt".
        iDestruct "Hser" as (w s') "[(#Hser1 & %Heqv & ->) | (_ & %Heqv & _)]";
          last discriminate.
        injection Heqv as ->.
        rewrite /sum_ser'' /sum_ser. v_pures.
        v_bind tᵥ3 (v_sA _).
        iMod ("HvserA" with "Hcnt Hser1 Hspec") as "(Hcnt & _ & Hspec)".
        simpl. v_pures. iModIntro.
        iSplitL "Hcnt".
        { iLeft. iExists _. iSplit; [done|]. iFrame. }
        iFrame. rewrite /inl_ser_str. iExists _, s'. iLeft. iFrame "#". done.
      + iDestruct "Hcnt" as (? ->) "Hcnt".
        iDestruct "Hser" as (w s') "[(_ & %Heqv & _) | (#Hser2 & %Heqv & ->)]";
          first discriminate.
        injection Heqv as ->.
        rewrite /sum_ser'' /sum_ser. v_pures.
        v_bind tᵥ3 (v_sB _).
        iMod ("HvserB" with "Hcnt Hser2 Hspec") as "(Hcnt & _ & Hspec)".
        simpl. v_pures. iModIntro.
        iSplitL "Hcnt".
        { iRight. iExists _. iSplit; [done|]. iFrame. }
        iFrame. rewrite /inr_ser_str. iExists _, s'. iRight. iFrame "#". done.
    - (* 6. v_auth_ser_spec *)
      iIntros (K tᵥ3 a1 a2 a3) "!# #HA Hv".
      rewrite /sum_ser''. v_pures.
      rewrite interp_tern_sum_unfold.
      rewrite interp_var1_ext2 interp_var0_ext1.
      iDestruct "HA" as (???) "[(>-> & >-> & >-> & Ha) | (>-> & >-> & >-> & Hb)]".
      + v_pures. v_bind (v_sA _).
        iMod ("HvauthserA" with "Ha Hv") as (sa) "[Hser_a Hv] /=".
        v_pures. iModIntro. iExists (inl_ser_str sa). iFrame.
        iExists _, sa. iLeft. iFrame. done.
      + v_pures. v_bind (v_sB _).
        iMod ("HvauthserB" with "Hb Hv") as (sb) "[Hser_b Hv] /=".
        v_pures. iModIntro. iExists (inr_ser_str sb). iFrame.
        iExists _, sb. iRight. iFrame. done.
    - (* 7. v_deser_spec      *) admit.
    - (* 8. v_count_spec *)
      iIntros (K tᵥ3 a c id Nc v_outer) "!# Hcnt Hspec".
      rewrite /sum_count. v_pures.
      iDestruct "Hcnt" as "[Hcnt|Hcnt]".
      + iDestruct "Hcnt" as (? ->) "Hcnt".
        v_pures.
        iMod ("HvcountA" with "Hcnt Hspec") as "[Hcnt Hspec]".
        iModIntro. iFrame. iLeft. iExists _. iSplit; [done|]. iFrame.
      + iDestruct "Hcnt" as (? ->) "Hcnt".
        v_pures.
        iMod ("HvcountB" with "Hcnt Hspec") as "[Hcnt Hspec]".
        iModIntro. iFrame. iRight. iExists _. iSplit; [done|]. iFrame.
  Admitted.

  Lemma refines_Auth_string :
    ⊢ lrel_evidence (LRelTern lrel_string lrel_bin_string lrel_un_string)
        p_Auth_string v_Auth_string i_Auth_string.
  Proof.
    iSplit; [|iSplit]; last first.
    { (* unary  *) admit. }
    { (* binary *)
      rewrite /lrel_bi_evidence /=.
      iExists tstring, _, _, _, _, _, _, _.
      iSplit; [done|].
      iSplit.
      { iIntros (vstr sstr Ψ) "!# Hser HΨ".
        iDestruct "Hser" as %(s' & -> & ->).
        rewrite /p_Auth_string /string_ser' /string_ser /string_ser_str.
        wp_pures. by iApply "HΨ". }
      iSplit.
      { iIntros (E a1 s HE Ψ) "!# Hser HΨ".
        iDestruct "Hser" as %(s' & -> & ->).
        rewrite /string_ser' /string_ser /string_ser_str. wp_pures.
        by iApply "HΨ". }
      iSplit.
      { iIntros (t v un_v a3 Ψ) "!# (%Hunsusp & HA) HΨ". wp_pures.
        iDestruct "HA" as ">HA". iSimpl in "HA".
        iDestruct "HA" as %(s0 & -> & ->).
        destruct t as [t1 t2 | t1 t2 | | | ]; simpl in Hunsusp.
        + destruct Hunsusp as (? & ? & ? & ? & Heq & _); discriminate.
        + destruct Hunsusp as [(? & ? & Heq & _ & _) | (? & ? & Heq & _ & _)]; discriminate.
        + subst un_v. rewrite /id. wp_pures. iApply "HΨ". iModIntro.
          iSplit; [iExists s0; done|]. iExists (string_ser_str s0).
          iExists s0. done.
        + subst un_v. rewrite /id. wp_pures. iApply "HΨ". iModIntro.
          iSplit; [iExists s0; done|]. iExists (string_ser_str s0).
          iExists s0. done.
        + destruct Hunsusp as (? & ? & ? & ? & ? & [Heq _]); discriminate. }
      iIntros (E a1 a3 HE Ψ) "!# [HA Htok] HΨ". wp_pures.
      iDestruct "HA" as ">HA". iSimpl in "HA".
      iDestruct "HA" as %(s0 & -> & ->).
      rewrite /id. wp_pures. iApply ("HΨ" $! _). iFrame. iModIntro. done. }
    (* ternary *)
    rewrite /lrel_tern_evidence /=.
    iExists tstring, _, _, _, _, _, _, _.
    iSplit; [done|]. iSplit; [done|].
    iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit]]]]]]].
    - (* 0. invalid_val *)
      iIntros "!#" (p v2 v3) "HA".
      iDestruct "HA" as %(s' & Heq & _). discriminate.
    - (* 1. unsusp_p_ser_spec *)
      iIntros (vstr sstr Ψ) "!# Hser HΨ".
      iDestruct "Hser" as %(s' & -> & ->).
      rewrite /p_Auth_string /string_ser' /string_ser /string_ser_str.
      wp_pures.
      by iApply "HΨ".
    - (* 2. susp_p_ser_spec *)
      iIntros (E a1 s HE Ψ) "!# Hser HΨ".
      iDestruct "Hser" as %(s' & -> & ->).
      rewrite /string_ser' /string_ser /string_ser_str. wp_pures.
      by iApply "HΨ".
    - (* 3. suspend_spec *)
      iIntros (t v un_v a2 a3 sa Ψ) "!# (%Hunsusp & HA & #Hser) HΨ".
      iDestruct "HA" as "[>HAt _]". iSimpl in "HAt".
      iDestruct "HAt" as %(s0 & -> & -> & ->).
      destruct t as [t1 t2 | t1 t2 | | | ]; simpl in Hunsusp; try done.
      + destruct Hunsusp as (? & ? & ? & ? & Heq & _); discriminate.
      + destruct Hunsusp as [(? & ? & Heq & _ & _) | (? & ? & Heq & _ & _)]; discriminate.
      + subst un_v. rewrite /id. wp_pures. iApply "HΨ". iModIntro.
        iSplit; [|iSplit].
        * iSplit; [|iSplit]; iExists s0; done.
        * iExact "Hser".
        * iExists sa. done.
      + iDestruct "Hser" as %(? & Heq & _); done.
      + destruct Hunsusp as (? & ? & ? & ? & ? & Heq & _); discriminate.
    - (* 4. unsuspend_spec *)
      iIntros (E a1 a2 a3 HE Ψ) "!# [HA Htok] HΨ".
      iDestruct "HA" as "[>HAt _]". iSimpl in "HAt".
      iDestruct "HAt" as %(s0 & -> & -> & ->).
      rewrite /id. wp_pures.
      iApply ("HΨ" $! _ (string_ser_str s0)).
      iFrame. iModIntro. iSplit; [done|]. iExists s0. done.
    - (* 5. v_ser_spec *)
      iIntros (K tᵥ a s id Nc v_outer) "!# Hcnt Hser Hspec".
      iDestruct "Hser" as %(s' & -> & ->).
      rewrite /string_ser' /string_ser. v_pures. iFrame.
      iModIntro. iExists s'. done.
    - (* 6. v_auth_ser_spec *)
      iIntros (K tᵥ a1 a2 a3) "!# #HA Hspec".
      iEval (rewrite /lrel_tern_tern /lrel_string /=) in "HA".
      iDestruct "HA" as ">%H". destruct H as (s' & -> & -> & ->).
      rewrite /string_ser' /string_ser. v_pures. iModIntro.
      iExists (string_ser_str s'). iFrame. iExists s'. done.
    - (* 7. v_deser_spec      *) admit.
    - (* 8. v_count_spec *)
      iIntros (K tᵥ a c id Nc v_outer) "!# Hcnt Hspec".
      iDestruct "Hcnt" as "[Hvv %Hc]". subst c.
      rewrite /string_count /int_count. v_pures.
      iModIntro. iFrame. done.
  Admitted.

  Lemma refines_Auth_int :
    ⊢ lrel_evidence (LRelTern lrel_int lrel_bin_int lrel_un_int)
        p_Auth_int v_Auth_int i_Auth_int.
  Proof.
    iSplit; [|iSplit]; last first.
    { (* unary  *) admit. }
    { (* binary *)
      rewrite /lrel_bi_evidence /=.
      iExists tint, _, _, _, _, _, _, _.
      iSplit; [done|].
      iSplit.
      { iIntros (vint sint Ψ) "!# Hser HΨ".
        iDestruct "Hser" as %(z & -> & ->).
        rewrite /p_Auth_int /int_ser' /int_ser /int_ser_str.
        wp_pures. by iApply "HΨ". }
      iSplit.
      { iIntros (E a1 s HE Ψ) "!# Hser HΨ".
        iDestruct "Hser" as %(z & -> & ->).
        rewrite /int_ser' /int_ser /int_ser_str. wp_pures.
        by iApply "HΨ". }
      iSplit.
      { iIntros (t v un_v a3 Ψ) "!# (%Hunsusp & HA) HΨ". wp_pures.
        iDestruct "HA" as ">HA". iSimpl in "HA".
        iDestruct "HA" as %(z0 & -> & ->).
        destruct t as [t1 t2 | t1 t2 | | | ]; simpl in Hunsusp.
        + destruct Hunsusp as (? & ? & ? & ? & Heq & _); discriminate.
        + destruct Hunsusp as [(? & ? & Heq & _ & _) | (? & ? & Heq & _ & _)]; discriminate.
        + subst un_v. rewrite /id. wp_pures. iApply "HΨ". iModIntro.
          iSplit; [iExists z0; done|]. iExists (int_ser_str z0).
          iExists z0. done.
        + subst un_v. rewrite /id. wp_pures. iApply "HΨ". iModIntro.
          iSplit; [iExists z0; done|]. iExists (int_ser_str z0).
          iExists z0. done.
        + destruct Hunsusp as (? & ? & ? & ? & ? & [Heq _]); discriminate. }
      iIntros (E a1 a3 HE Ψ) "!# [HA Htok] HΨ". wp_pures.
      iDestruct "HA" as ">HA". iSimpl in "HA".
      iDestruct "HA" as %(z0 & -> & ->).
      rewrite /id. wp_pures. iApply ("HΨ" $! _). iFrame. iModIntro. done. }
    (* ternary *)
    rewrite /lrel_tern_evidence /=.
    iExists tint, _, _, _, _, _, _, _.
    iSplit; [done|]. iSplit; [done|].
    iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit]]]]]]].
    - (* 0. invalid_val *)
      iIntros "!#" (p v2 v3) "HA".
      iDestruct "HA" as %(s' & Heq & _). discriminate.
    - (* 1. unsusp_p_ser_spec *)
      iIntros (vint sint Ψ) "!# Hser HΨ".
      iDestruct "Hser" as %(z & -> & ->).
      rewrite /p_Auth_int /int_ser' /int_ser /int_ser_str.
      wp_pures.
      by iApply "HΨ".
    - (* 2. susp_p_ser_spec *)
      iIntros (E a1 s HE Ψ) "!# Hser HΨ".
      iDestruct "Hser" as %(z & -> & ->).
      rewrite /int_ser' /int_ser /int_ser_str. wp_pures.
      by iApply "HΨ".
    - (* 3. suspend_spec *)
      iIntros (t v un_v a2 a3 sa Ψ) "!# (%Hunsusp & HA & #Hser) HΨ".
      iDestruct "HA" as "[>HAt _]". iSimpl in "HAt".
      iDestruct "HAt" as %(z0 & -> & -> & ->).
      destruct t as [t1 t2 | t1 t2 | | | ]; simpl in Hunsusp; try done.
      + destruct Hunsusp as (? & ? & ? & ? & Heq & _); discriminate.
      + destruct Hunsusp as [(? & ? & Heq & _ & _) | (? & ? & Heq & _ & _)]; discriminate.
      + iDestruct "Hser" as %(? & Heq & _); done.
      + subst un_v. rewrite /id. wp_pures. iApply "HΨ". iModIntro.
        iSplit; [|iSplit].
        * iSplit; [|iSplit]; iExists z0; done.
        * iExact "Hser".
        * iExists sa. done.
      + destruct Hunsusp as (? & ? & ? & ? & ? & Heq & _); discriminate.
    - (* 4. unsuspend_spec *)
      iIntros (E a1 a2 a3 HE Ψ) "!# [HA Htok] HΨ".
      iDestruct "HA" as "[>HAt _]". iSimpl in "HAt".
      iDestruct "HAt" as %(z0 & -> & -> & ->).
      rewrite /id. wp_pures.
      iApply ("HΨ" $! _ (int_ser_str z0)).
      iFrame. iModIntro. iSplit; [done|]. iExists z0. done.
    - (* 5. v_ser_spec *)
      iIntros (K tᵥ a s id Nc v_outer) "!# Hcnt Hser Hspec".
      iDestruct "Hser" as %(z & -> & ->).
      rewrite /int_ser' /int_ser. v_pures. iFrame.
      iModIntro. iExists z. done.
    - (* 6. v_auth_ser_spec *)
      iIntros (K tᵥ a1 a2 a3) "!# #HA Hspec".
      iEval (rewrite /lrel_tern_tern /lrel_int /=) in "HA".
      iDestruct "HA" as ">%H". destruct H as (z' & -> & -> & ->).
      rewrite /int_ser' /int_ser. v_pures. iModIntro.
      iExists (int_ser_str z'). iFrame. iExists z'. done.
    - (* 7. v_deser_spec      *) admit.
    - (* 8. v_count_spec *)
      iIntros (K tᵥ a c id Nc v_outer) "!# Hcnt Hspec".
      iDestruct "Hcnt" as "[Hvv %Hc]". subst c.
      rewrite /int_count. v_pures.
      iModIntro. iFrame. done.
  Admitted.

  Lemma refines_Auth_mu Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆ ⇒ ⋆, var1 (var0 (μ: ⋆; var1 var0)) → var1 (μ: ⋆; var1 var0) ⟧
      (ext Δ lrel_evidence) p_Auth_mu v_Auth_mu i_Auth_mu.
  Proof.
    iSplit; [|iSplit]; interp_unfold!; last first.
    { (* unary  *) admit. }
    { (* binary *) admit. }
    (* ternary *)
    iIntros (A v1 v2 v3) "!# _"; rewrite -/interp.
    iIntros (????) "Hv Hi Htok".
    rewrite /p_Auth_mu /v_Auth_mu /i_Auth_mu.
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame.
    iSplit; [|iSplit]; interp_unfold!; last first.
    { (* inner-after-A unary *) admit. }
    { (* inner-after-A binary *) admit. }
    iIntros (vA1 vA2 vA3) "!# #HA".
    interp_unfold! in "HA".
    iDestruct "HA" as "(HA_tern & #HA_bin & #HA_un)".
    rewrite interp_var1_ext2 interp_var0_ext1.
    iDestruct "HA_tern" as (tA p_ssA p_usA p_spA p_uspA v_sA v_dA v_cA -> ->)
      "(HinvA & HusserA & HsserA & HsuspA & HunsuspA & HvserA & HvauthserA & HvdeserA & HvcountA)".
    iIntros (????) "Hv Hi Htok". v_pures; i_pures; wp_pures. 
    iModIntro. iFrame. clear.
    iSplit; [|iSplit]; interp_unfold!; last first.
    { (* final unary  *) admit. }
    { (* final binary *) admit. }
    rewrite interp_var1_ext2.
    iExists tA, _, _, _, _, _, _, _.
    iSplit; [done|]. iSplit; [done|].
    iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit]]]]]]].
    - (* 0. invalid_val *) admit.
    - (* 1. unsusp_p_ser_spec *)
      iIntros (vmu smu Ψ) "!# Hser HΨ".
      rewrite /rec_fold. wp_pures.
      wp_apply ("HusserA" with "Hser"). iIntros "_".
      by iApply "HΨ".
    - (* 2. susp_p_ser_spec *)
      iIntros (E a1 s HE Ψ) "!# Hser HΨ".
      rewrite /rec_fold. wp_pures.
      wp_apply ("HsserA" with "[//] Hser"). iIntros "_".
      by iApply "HΨ".
    - (* 3. suspend_spec *)
      iIntros (t v un_v a2 a3 sa Ψ) "!# (%Hunsusp & #HA' & #Hser) HΨ".
      rewrite /rec_fold. wp_pures.
      iEval (rewrite interp_rec_star_unfold) in "HA'".
      interp_unfold! in "HA'".
      rewrite interp_var1_ext2 interp_var0_ext1.
      wp_apply ("HsuspA" with "[$Hser $HA' //]").
      iIntros (v') "(#HAv' & #Hserv' & Hreal)".
      iApply "HΨ". iFrame "# Hreal".
      iEval (rewrite interp_rec_star_unfold).
      interp_unfold!.
      rewrite interp_var1_ext2 interp_var0_ext1.
      rewrite /interp_rec1 /lrel_ktype. done.
    - (* 4. unsuspend_spec *)
      iIntros (E a1 a2 a3 HE Ψ) "!# [#HA Htok] HΨ".
      rewrite /rec_fold. wp_pures.
      iEval (rewrite interp_rec_star_unfold) in "HA".
      interp_unfold! in "HA".
      rewrite interp_var1_ext2 interp_var0_ext1.
      wp_apply ("HunsuspA" with "[//] [$Htok $HA]").
      iIntros (un_v s) "(Htok & %Hunsusp & #Hser)".
      iApply ("HΨ" $! un_v s). iFrame. iFrame "#". done.
    - (* 5. v_ser_spec *)
      iIntros (K tᵥ1 a s id Nc v_outer) "!# Hcnt Hser Hspec".
      v_pures.
      by iApply ("HvserA" with "Hcnt Hser Hspec").
    - (* 6. v_auth_ser_spec   *) admit.
    - (* 7. v_deser_spec      *) admit.
    - (* 8. v_count_spec *)
      iIntros (K tᵥ1 a c id Nc v_outer) "!# Hcnt Hspec".
      v_pures.
      by iApply ("HvcountA" with "Hcnt Hspec").
  Admitted.

  (* Definition auth_p_fill (a v : val) (s : string) (t : evi_type) : iProp Σ :=
    ⌜v = (a, #(hash s))%V⌝ ∨
    (∃ (lb lr : loc) (ps : proph_id),
      ⌜v = (#ps, #lb, #lr, a, #(hash s))%V⌝ ∗
      seq_inv (suspFill N ps) 
        (∃ (b r : bool), lb ↦ #b ∗ lb ↦ #r ∗ proph_p_susp ps false ∗
          ⌜(b = true ∧ r = true) ∨ (b = false)⌝)).

  Definition auth_v_fill (v : val) (s : string) : iProp Σ :=
    ⌜v = InjLV #(hash s1)⌝.

  Definition auth_p_unfill (a v : val) (s : string) (t : evi_type) : iProp Σ :=
    ∃ (lb lr : loc) (ps : proph_id),
      ⌜v = (#ps, #lb, #lr, a, #(hash s))%V⌝ ∗
      seq_inv (suspFill N ps)  
        (∃ (r : bool), lb ↦ #r ∗
          ((lb ↦ #false ∗ proph_p_susp ps true) ∨ (∃ b, lb ↦ #true ∗ proph_p_susp ps b))).

  Definition auth_v_unfill (v : val) (s : string) : iProp Σ :=
    (∃ (s' : string) (susp : loc),
      ⌜v = InjRV #susp⌝ ∗
      ⌜s' = some_ser_str (string_ser_str (hash s))⌝ ∗
      seq_inv (authN N susp)
        (auth_inv s' susp)). *)

  (* Create correspondence between lb susp here *)
  Definition auth_p (un_a v : val) (s : string) : iProp Σ :=
    ∃ (lb lr : loc) (ps : proph_id),
      ⌜v = (#lb, #lr, un_a, #(hash s), #ps)%V⌝ ∗
        (seq_inv (prover_susp_n N v) (susp_p_fill_inv ps lb lr) ∨
        seq_inv (prover_susp_n N v) (susp_p_unfill_inv ps lb lr)).

  Definition auth_v (v : val) (s : string) : iProp Σ :=
    (⌜v = InjLV #(hash s)⌝) ∨
      (∃ (s' : string) (susp : loc),
        ⌜v = InjRV #susp⌝ ∗
        ⌜s' = some_ser_str (string_ser_str (hash s))⌝ ∗
        seq_inv (ver_susp_n N v) 
          (auth_susp_v_ser_proph_inv v s')).

  Definition susplb_gname (v1 v2 : val) : iProp Σ :=
    (∃ v, ⌜v2 = InjLV v⌝) ∨
      (∃ (γ : gname) (susp lb : loc) v1',
        ⌜v1 = (#lb, v1')%V ∧ v2 = InjRV #susp⌝ ∗ 
          lg_mapg_frag lb γ ∗ lg_mapg_frag susp γ).

  Definition lrel_auth_tern (A : lrel_tern Σ) : lrel Σ := LRel (λ v1 v2 v3,
    ∃ (t : evi_type) (v2' a1 a2 un_a1 : val) (s : string),
      ⌜v2 = SOMEV v2' ∧ unsusp t a1 un_a1⌝ ∗
      susp_ser_p t a1 s ∗ A a1 a2 v3 ∗
      auth_p un_a1 v1 s ∗ auth_v v2' s ∗ susplb_gname v1 v2')%I.

  Definition lrel_auth_bin (A : lrel_bin Σ) : lrel_bin Σ := LRelBin (λ v1 v3,
    ∃ (t : evi_type) (a1 un_a1 : val) (s : string),
      ⌜unsusp t a1 un_a1⌝ ∗
      susp_ser_p t a1 s ∗ A a1 v3 ∗
      auth_p un_a1 v1 s)%I.

  Definition lrel_auth_un (A : lrel_un Σ) : lrel_un Σ := LRelUn (λ v2,
    ∃ (t : evi_type) (v2' a2 : val) (s : string),
      ⌜v2 = SOMEV v2'⌝ ∗ A a2 ∗ auth_v v2' s)%I.

  Definition lrel_auth' (A : lrel_tern Σ) : lrel_tern Σ :=
    LRelTern (lrel_auth_tern A)
             (lrel_auth_bin (lrel_tern_bin A))
             (lrel_auth_un (lrel_tern_un A)).

  Program Definition lrel_auth : kindO Σ (⋆ ⇒ ⋆)%kind := λne A, lrel_auth' A.
  Next Obligation. Admitted.

  Definition auth_ctx {Θ} (Δ : ctxO Σ Θ) (R : kindO Σ (⋆ ⇒ ⋆)) :=
    ext (ext (ext Δ lrel_auth) R) lrel_evidence.

  Lemma refines_Auth_auth Θ (Δ : ctxO Σ Θ) (R : kindO Σ (⋆ ⇒ ⋆)) :
    ⊢ ⟦ ∀: ⋆, var1 (var3 var0) ⟧
      (auth_ctx Δ R) p_Auth_auth v_Auth_auth i_Auth_auth.
  Proof.
    iSplit; [|iSplit]; interp_unfold!; last first.
    { (* unary  *) admit. }
    { (* binary *) admit. }
    (* ternary *)
    iIntros (A v1 v2 v3) "!# _"; rewrite -/interp.
    iIntros (????) "Hv Hi Htok".
    rewrite /p_Auth_auth /v_Auth_auth /i_Auth_auth.
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame.
    iSplit; [|iSplit]; interp_unfold!; last first.
    { (* final unary  *) admit. }
    { (* final binary *) admit. }
    rewrite interp_var1_ext2.
    iExists tauth, _, _, _, _, _, _, _.
    iSplit; [done|]. iSplit; [done|].
    iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit]]]]]]].
    - (* 0. invalid_val *)
      iIntros "!#" (p w2 w3) "HA".
      iSimpl in "HA". rewrite interp_var3_ext4.
      iDestruct "HA" as (t w2' a1 a2 un_a1 s) "(_ & _ & _ & Hauth_p & _)".
      iDestruct "Hauth_p" as (lb lr ps) "[%Heq _]". discriminate.
    - (* 1. unsusp_p_ser_spec *)
      iIntros (vau sau Ψ) "!# Hser HΨ".
      iSimpl in "Hser". iDestruct "Hser" as %(a & h & -> & ->).
      rewrite /authenticatable_base_susp.auth_unsusp_ser_p. wp_pures.
      rewrite /option_serialization /s_serializer' /= /option_ser''' /string_ser' /string_ser.
      wp_pures. rewrite /simple_string /some_ser_str /string_ser_str.
      iApply "HΨ". done.
    - (* 2. susp_p_ser_spec   *) admit.
    - (* 3. suspend_spec      *) admit.
    - (* 4. unsuspend_spec    *) admit.
    - (* 5. v_ser_spec        *) admit.
    - (* 6. v_auth_ser_spec   *) admit.
    - (* 7. v_deser_spec      *) admit.
    - (* 8. v_count_spec *)
      iIntros (K tx a c id Nc v_outer) "!# Hcnt Hspec".
      rewrite /= /auth_sub_susp_count_frags.
      iDestruct "Hcnt" as (w1 ->) "[Hvalid|Hvalid]".
      { iDestruct "Hvalid" as %(h & -> & ->).
        rewrite /auth_count. v_pures. iModIntro. iFrame.
        iExists (InjLV #h). iSplit; [done|].
        iLeft. iExists h. done. }
      iDestruct "Hvalid" as (susp ->) "[Hv|Hv]".
      { iDestruct "Hv" as (h) "[Hsusp ->]".
        rewrite /auth_count. v_pures. v_load. v_pures. iModIntro. iFrame.
        iExists (InjRV #susp).
        iSplit; [done|]. iRight. iExists susp. iSplit; [done|].
        iLeft. iExists h. iFrame. done. }
      iDestruct "Hv" as (p γ) "(Hlg & Hsusp & -> & Hmf & Hcap2 & Hos)".
      rewrite /auth_count. v_pures. v_load. v_pures. iModIntro. iFrame.
      iExists (InjRV #susp).
      iSplit; [done|]. iRight. iExists susp. iSplit; [done|].
      iRight. iExists p, γ. iFrame. done.
  Admitted.

  Lemma refines_auth_auth Θ (Δ : ctxO Σ Θ) (R : kindO Σ (⋆ ⇒ ⋆)) :
    ⊢ ⟦ ∀: ⋆, var1 var0 → var0 → var3 var0 ⟧
      (auth_ctx Δ R) p_auth v_auth i_auth.
  Proof.
    (* iIntros (????) "!# _"; rewrite -/interp.
    iIntros (????) "Hv Hi".
    rewrite /p_auth /v_auth  /i_auth.
    v_pures; i_pures; wp_pures.
    iModIntro. iFrame. clear.
    iIntros (???) "!#"; rewrite -!/interp /=.
    iDestruct 1 as (t ??? -> ->) "#Hser".

    iIntros (????) "Hv Hi".
    v_pures; i_pures; wp_pures.
    iFrame.
    iIntros "!> !>" (w1 w2 w3) "#HA". clear.
    iIntros (????) "Hv Hi".
    v_pures; i_pures; wp_pures.
    v_bind (v_ser _). wp_bind (p_ser _).

    wp_apply ("Hser" with "HA").
    iIntros (s1) "(%Hs1 & #Hser' & #Hdeser)".
    iMod ("Hser'" with "Hv") as "Hv /=".
    wp_apply (wp_hash with "[$]"); iIntros "Hhash".
    wp_pures.
    iMod (step_verifier_hash with "[$]") as "Hv"; [done|].
    iFrame. iModIntro.
    by iFrame "∗ # %".
  Qed. *)
  Admitted.

End authenticatable.
