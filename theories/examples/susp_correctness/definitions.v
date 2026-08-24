From auth.prelude Require Import stdpp.
From auth.rel_logic_tern_susp Require Import model interp.
From auth.heap_lang Require Import typedproph.
From auth.heap_lang.lib Require Import serialization_susp list map.
From auth.examples.susp_correctness Require Export resource_algebras.
From iris.algebra Require Import csum.
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

  Definition is_proph_reverse_proof (v : val) (p : proph_id) (ps : list string) : iProp Σ :=
    ⌜is_proof v (reverse ps)⌝ ∗ proph_proof p ps.

End proph.


Definition authBaseN : namespace := nroot .@ "susp_sec".
Definition tableN : namespace := authBaseN .@ "table".

Definition prover_susp_set : namespace := authBaseN .@ "psusp".
Definition prover_susp_n (v : val) : namespace := prover_susp_set .@ v.

Definition ver_susp_set : namespace := authBaseN .@ "vsusp".
Definition ver_susp_n (l : loc) : namespace := ver_susp_set .@ l.


Section authenticatable_definitions.
  Context `{!authG Σ, !seqG Σ, !correctnessG Σ}.

  Inductive evi_type : Type :=
  | tprod (t1 t2 : evi_type)
  | tsum (t1 t2 : evi_type)
  | tstring
  | tint
  | tauth.

  #[global] Instance : Inhabited evi_type.
  Proof. constructor. apply tstring. Qed.

  Fixpoint p_sub_obj (t : evi_type) (v sv: val) :=
    match t with
    | tprod t1 t2 =>
        ∃ v1 v2, v = (v1, v2)%V ∧ (sv = v1 ∨ sv = v2 ∨ p_sub_obj t1 v1 sv ∨ p_sub_obj t2 v2 sv)
    | tsum t1 t2 =>
        ∃ v', ((v = InjLV v' ∧ p_sub_obj t1 v' sv) ∨
                 (v = InjRV v' ∧ p_sub_obj t2 v' sv))
    | tstring => False
    | tint => False
    | tauth =>
        ∃ (p : proph_id) (lb lr : loc) (a : val) (h : string),
          v = BoxV (#lb, #lr, a, #h, #p)%V ∧ sv = #lb
    end.

  Fixpoint v_sub_obj (t : evi_type) (v sv: val) :=
    match t with
    | tprod t1 t2 =>
        ∃ v1 v2, v = (v1, v2)%V ∧ (sv = v1 ∨ sv = v2 ∨ v_sub_obj t1 v1 sv ∨ v_sub_obj t2 v2 sv)
    | tsum t1 t2 =>
        ∃ v', ((v = InjLV v' ∧ v_sub_obj t1 v' sv) ∨
                 (v = InjRV v' ∧ v_sub_obj t2 v' sv))
    | tstring => False
    | tint => False
    | tauth =>
        ∃ v', (v = SOMEV (InjLV v') ∨ (v = SOMEV (InjRV v'))) ∧ v' = sv
    end.

  Definition suspended_string : string := none_ser_str.

  Definition simple_string (s : string) : string := string_ser_str s.

  Definition filled_string (s : string) : string := some_ser_str (simple_string s).

  (* Captures the structural constraint that [s] is the serialization
     obtained by filling the susp at position (t, v) with value [h].
     This is the precondition that makes [ser_v_proph t pid v s] preserved
     across the empty→filled transition in [count_update].
     Mirrors [v_sub_obj]'s recursion structure (including the [v = v']
     constraint in tsum that makes susp-through-tsum unreachable). *)
  Fixpoint same_ser_for_fill (t : evi_type) (v : val) (s : string)
      (susp : loc) (h : string) : Prop :=
    match t with
    | tprod t1 t2 =>
        ∃ v1 v2 s1 s2, v = (v1, v2)%V ∧ s = prod_ser_str s1 s2 ∧
          (same_ser_for_fill t1 v1 s1 susp h ∨ same_ser_for_fill t2 v2 s2 susp h)
    | tsum t1 t2 =>
        ∃ v',
          (v = InjLV v' ∧
            ∃ s', s = inl_ser_str s' ∧ same_ser_for_fill t1 v' s' susp h) ∨
          (v = InjRV v' ∧
            ∃ s', s = inr_ser_str s' ∧ same_ser_for_fill t2 v' s' susp h)
    | tauth =>
        v = SOMEV (InjRV #susp) ∧ s = filled_string h
    | _ => False
    end.

  Definition empty_proph_bs (p : proph_id) : iProp Σ :=
    proph_bs p [].

  Definition fill_proph_bs (p : proph_id) (bs : list bool) : iProp Σ :=
    proph_bs p bs ∗ ⌜∃ bs', bs = false :: bs'⌝.

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
      ⌜v = (a, #h)%V ∧ s = filled_string h⌝.

  Definition susp_p_fill_inv (ps : proph_id) (lb lr : loc) : iProp Σ :=
    lb ↦ #false ∗
      ((∃ (bs : list bool), lr ↦ #false ∗ fill_proph_bs ps bs) ∨
      (∃ (bs : list bool), lr ↦ #true ∗ proph_bs ps bs) ∨
      (lr ↦ #false ∗ empty_proph_bs ps) ∨
      (∃ (bs : list bool) (q : Qp) (b : bool),
          lr ↦ #b ∗ proph_bs ps bs ∗ intransit q)).

  Definition auth_susp_ser_p_fill (v : val) (s : string) : iProp Σ :=
    ∃ (p : proph_id) (lb lr : loc) (a : val) (h : string) (r : bool),
      ⌜v = BoxV (#lb, #lr, a, #h, #p)%V ∧ s = filled_string h⌝ ∗
      lg_mapg_p_unalloc lb ∗
      seq_inv (prover_susp_n v) (susp_p_fill_inv p lb lr).

  Definition susp_p_unfill_inv (ps : proph_id) (lb lr : loc) : iProp Σ :=
    (∃ (bs : list bool),
      lb ↦ #false ∗ lr ↦ #false ∗ unfill_proph_bs ps bs) ∨
    (∃ (r : bool) (bs : list bool) (n : nat) (γ : gname),
      lb ↦ #true ∗ lr ↦ #r ∗ proph_bs ps bs ∗ lg_mapg_p_frag lb γ ∗
      □ (tern_state -∗ tern_state ∗ visit_reached_done γ)).

  Definition auth_susp_ser_p_emp (v : val) (s : string) : iProp Σ :=
    ∃ (p : proph_id) (lb lr : loc) (a : val) (h : string) (r : bool),
      ⌜v = BoxV (#lb, #lr, a, #h, #p)%V ∧ s = suspended_string⌝ ∗
      seq_inv (prover_susp_n v) (susp_p_unfill_inv p lb lr).

  (* What it will actually serialize to *)
  Definition auth_susp_ser_p_real (v : val) (s : string) c : iProp Σ :=
    (auth_susp_ser_p_fill v s ∧ ⌜c = 0⌝) ∨ (auth_susp_ser_p_emp v s ∧ ⌜c = 1⌝).

  (* What it would serialize to without suspension. SOME-wrapped
     ([filled_string]) so the prover's would-be format coincides with the
     verifier's [auth_ser_v] format (hash-format fix, blocker #2). *)
  Definition auth_susp_ser_p (v : val) (s : string) : iProp Σ :=
    ∃ (p : proph_id) (lb lr : loc) (a : val) (h : string),
      ⌜v = BoxV (#lb, #lr, a, #h, #p)%V ∧ s = filled_string h⌝.

  Definition auth_fill_ser_v (v : val) (s : string) : iProp Σ :=
    ∃ (h : string), ⌜s = filled_string h ∧ v = InjLV #h⌝.

  Definition auth_susp_fill_v (v : val) (s : string) : iProp Σ :=
    ∃ (h : string) (susp : loc) γ,
      ⌜s = filled_string h ∧ v = InjRV #susp⌝ ∗ susp ↦ᵥ{#(1/2)} InjRV #h ∗
      filled susp ∗ lg_mapg_frag susp γ ∗ visit_finished γ.
    (* Can get rid of either filled or visit_finished.
      If keeping filled, need another invariant saying it implies finished. *)

  (* Definition auth_susp_emp_v (v : val) (s : string) : iProp Σ :=
    ∃ (h : string) (susp : loc) (pid: nat) (p : proph_id),
      ⌜s = suspended_string ∧ v = InjRV #susp⌝ ∗ 
      susp ↦ᵥ{#(1/2)} InjLV (#pid, #p) ∗ proph_v_susp p h. *)

  (* No [proph_v_susp]: spec-side prophecies carry no resource
     ([step_verifier_newproph] is a ghost no-op), so the future fill
     value [h] is pinned by the invariant's string ([s = filled_string h],
     itself fixed by [auth_pv]) and by the registered prediction
     ([same_ser_for_fill] forces [ps = filled_string h]) — serpred plays
     the prophecy's role. *)
  Definition auth_susp_emp_v (pid : nat) (v : val) (s : string) : iProp Σ :=
    ∃ (h : string) (susp : loc) (p : proph_id) pv pt ps N,
      ⌜s = filled_string h ∧ v = InjRV #susp⌝ ∗
      cap_frag pid N ∗ unfilled susp ∗
      mapg_frag pid (1 / (2 * pos_to_Qp (Pos.of_nat N)))%Qp pv ∗
      ⌜v_sub_obj pt pv #susp⌝ ∗ ⌜same_ser_for_fill pt pv ps susp h⌝ ∗
      serpred_frag pid ps ∗
      susp ↦ᵥ{#(1/2)} InjLV (#pid, #p).

  Definition auth_susp_fill_ser_v (v : val) (s : string) : iProp Σ :=
    ∃ (h : string) (susp : loc),
      ⌜s = filled_string h ∧ v = InjRV #susp⌝ ∗ susp ↦ᵥ{#(1/4)} InjRV #h.

  Definition auth_susp_emp_ser_v (pid : nat) (v : val) : iProp Σ :=
    ∃ (h : string) (susp : loc) (p : proph_id),
      ⌜v = InjRV #susp⌝ ∗ susp ↦ᵥ{#(1/4)} InjLV (#pid, #p).

  Definition auth_susp_v_inv (pid : nat) (v : val) (s : string) : iProp Σ :=
    auth_susp_fill_v v s ∨ auth_susp_emp_v pid v s.

  #[global] Instance auth_susp_v_inv_timeless pid v s :
      Timeless (auth_susp_v_inv pid v s).
  Proof. rewrite /auth_susp_v_inv /auth_susp_fill_v /auth_susp_emp_v. apply _. Qed.

  Definition auth_susp_ser_v (pid : nat) (v : val) (s : string) : iProp Σ :=
    auth_susp_fill_ser_v v s ∨ auth_susp_emp_ser_v pid v.

  Definition auth_susp_v_transit_inv (pid : nat) (v : val) (s : string) : iProp Σ :=
    (intransit 1 ∗ auth_susp_fill_v v s) ∨
    (∃ γ (susp : loc),
      ⌜v = InjRV #susp⌝ ∗ lg_mapg_frag susp γ ∗ visit_finished γ ∗
        intransit (1/2) ∗ auth_susp_emp_v pid v s).

  (* Definition auth_susp_v_ser_proph (pid : nat) (v : val) (s : string) : iProp Σ :=
    ∃ (susp : loc), ⌜v = InjRV #susp⌝ ∗
      seq_inv (ver_susp_n susp) (auth_susp_v_inv #{1/2} pid v s). *)

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
        v = BoxV (#lb, #lr, a, #h, #p)%V ∧ un_v = (a, #h)%V
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
  Fixpoint susp_ser_p_real (t : evi_type) (c : nat) (v : val) (s : string) : iProp Σ :=
    match t with
    | tprod t1 t2 =>
      (∃ (c1 c2 : nat), ⌜(c = c1 + c2)%nat⌝ ∗
        prod_is_ser' v s (susp_ser_p_real t1 c1) (susp_ser_p_real t2 c2))
    | tsum t1 t2 => sum_is_ser' v s (susp_ser_p_real t1 c) (susp_ser_p_real t2 c)
    | tstring => string_is_ser v s ∧ ⌜c = 0⌝
    | tint => int_is_ser v s ∧ ⌜c = 0⌝
    | tauth => auth_susp_ser_p_real v s c
    end.
 
  #[global] Instance susp_ser_p_real_persistent t c v s : Persistent (susp_ser_p_real t c v s).
  Proof. revert c v s. induction t => c v s; simpl; apply _. Qed.

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
                 (auth_fill_ser_v v1 s ∨
                  (* filled-through-a-susp: the ¼ points-to budget lives
                     with the count/proph structures, not with
                     [auth_ser_spec] — this form is pure. *)
                  ∃ (h : string) (susp : loc),
                    ⌜s = filled_string h ∧ v1 = InjRV #susp⌝)
    end.
 
  #[global] Instance ser_v_persistent t v s : Persistent (ser_v t v s).
  Proof. revert v s. induction t => v s; simpl; apply _. Qed.

  Fixpoint ser_v_proph (t : evi_type) (pid : nat) (v : val) (s : string) : iProp Σ :=
    match t with
    | tprod t1 t2 => prod_is_ser' v s (ser_v_proph t1 pid) (ser_v_proph t2 pid)
    | tsum t1 t2 => sum_is_ser' v s (ser_v_proph t1 pid) (ser_v_proph t2 pid)
    | tstring => string_is_ser v s
    | tint => int_is_ser v s
    | tauth => ∃ v1, ⌜v = SOMEV v1⌝ ∗
                       (auth_fill_ser_v v1 s ∨ auth_susp_ser_v pid v1 s)
  end.
 
  (* #[global] Instance ser_v_proph_persistent t pid v s : Persistent (ser_v_proph t pid v s).
  Proof. revert pid v s. induction t => pid v s; simpl; apply _. Qed. *)

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
                mapg_frag pid (1 / (2 * pos_to_Qp (Pos.of_nat N)))%Qp v_outer ∗
                cap_frag pid N ∗
                pval_snapshot susp pid ∗
                (visit_pending γ ∨
                  (∃ id, ⌜id > pid⌝ ∗ visit_done γ id) ∨
                  (visit_finished γ ∗ intransit (1/2))))))).

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
      mapg_frag id q v).

  Definition sub_susp_count_frags
      (t : evi_type) (v : val) (c id N : nat) : iProp Σ :=
    cap_frag id N ∗ ⌜c ≤ N⌝ ∗
    sub_susp_count t v c id N v ∗
    count_aggregator c id N v.

  Definition susp_p_ser_spec (ser : val) (t : evi_type) : iProp Σ :=
    ∀ (E : coPset) (a1 : val) (s : string) (c : nat) (q : Qp),
      ⌜↑prover_susp_set ⊆ E⌝ -∗
      {{{ susp_ser_p_real t c a1 s ∗ seq_tok E ∗ intransit q }}}
        ser a1
      {{{ RET #s; seq_tok E ∗ intransit (q/2)%Qp ∗
          (∀ (γl : pending_setg_type),
            tern_state -∗ penset_frag γl -∗ ⌜size γl = c⌝ -∗
            ([∗ set] γ ∈ γl,
              ∃ lb, lg_mapg_p_frag lb γ ∗ ⌜p_sub_obj t a1 #lb⌝) -∗
            tern_state ∗ penset_frag γl ∗
            ([∗ set] γ ∈ γl, visit_reached_done γ ∗
              ∃ lb, lg_mapg_p_frag lb γ ∗ ⌜p_sub_obj t a1 #lb⌝)) }}}.

  (* Like [susp_p_ser_spec] but with [c, a, s] as fixed parameters and without
     [susp_ser_p_real] in the precondition (the prover-side serialization-shape
     is internalized when the spec is built). Used as the post-condition payload
     of [suspend_v_deser_spec], wrapped in [∃ t_real, ...]. *)
  Definition susp_p_ser_spec_at
      (ser : val) (t : evi_type) (c : nat) (a : val) (s : string) : iProp Σ :=
    ∀ (E : coPset) (q : Qp),
      ⌜↑prover_susp_set ⊆ E⌝ -∗
      {{{ seq_tok E ∗ intransit q }}}
        ser a
      {{{ RET #s; seq_tok E ∗ intransit (q/2)%Qp ∗
          (∀ (γl : pending_setg_type),
            tern_state -∗ penset_frag γl -∗ ⌜size γl = c⌝ -∗
            ([∗ set] γ ∈ γl,
              ∃ lb, lg_mapg_p_frag lb γ ∗ ⌜p_sub_obj t a #lb⌝) -∗
            tern_state ∗ penset_frag γl ∗
            ([∗ set] γ ∈ γl, visit_reached_done γ ∗
              ∃ lb, lg_mapg_p_frag lb γ ∗ ⌜p_sub_obj t a #lb⌝)) }}}.

  Definition unsusp_p_ser_spec (ser : val) (t : evi_type) : iProp Σ :=
    ∀ (v : val) (s : string),
      {{{ unsusp_ser_p t v s }}}
        ser v
      {{{ RET #s; True }}}.

  (** The ghost bundle (m, vm, pn, ctr, mlg_p, mcap) is quantified in the
      INNER □∀ so that one [v_deser_par] can be invoked repeatedly with
      evolving state — required to compose component calls sequentially
      (e.g. pair runs deserA then deserB). [cap_auth]/[mapg_auth] come with
      freshness of [id] so the match case can register the deser'd value;
      [serpred_frag id s_reg] is the caller's registered prediction, handed
      back in the post. *)
  Definition suspend_v_deser_spec
      (ser suspend v_deser : val) (A : lrel_tern Σ) (t : evi_type) : iProp Σ :=
    □(∀ K tᵥ (id : nat),
      spec_verifier tᵥ (fill K (v_deser #id))
      ={⊤}=∗ ∃ (v_deser_par : val),
        spec_verifier tᵥ (fill K v_deser_par) ∗
        □(∀ t' (a1 un_a1 a2 a3 : val) (s_def s_pred s_reg : string)
             vm mp pn ctr mlg_p K' tᵥ',
          {{{ ⌜unsusp t' a1 un_a1⌝ ∗
              ▷ A a1 a2 a3 ∗ susp_ser_p t' a1 s_def ∗
              serpred_frag id s_reg ∗
              (* The caller's apartness-mint obligation, available at LEAF
                 time (a fresh suspension must mint its [pval_snapshot]
                 BEFORE [visited_susp_register] absorbs the loc's
                 [vmeta_token] into the freshness accumulator). *)
              □(∀ susp : loc, vmeta_token susp ={⊤}=∗
                  vmeta_token susp ∗ pval_snapshot susp id) ∗
              visited_mapg_auth vm mp pn ctr ∗
              lg_p_auth mlg_p ∗
              pencount_frag pn ∗
              spec_verifier tᵥ' (fill K' (v_deser_par #s_pred)) }}}
            suspend un_a1
          {{{ a1' s_real c t_real, RET a1';
              susp_p_ser_spec_at ser t_real c a1' s_real ∗
              susp_ser_p_real t_real c a1' s_real ∗
              serpred_frag id s_reg ∗
              ((⌜s_pred = s_real ∧ t_real = t⌝ ∗
                (lrel_tern_un A) a1' ∗ ∃ γl mlg_p' a2',
                lg_p_auth mlg_p' ∗
                ⌜size γl = c⌝ ∗ penset_frag γl ∗
                susp_ser_p t a1' s_def ∗
                spec_verifier tᵥ' (fill K' (SOMEV a2')) ∗
                ([∗ set] γ ∈ γl,
                  (∃ lb,
                    lg_mapg_p_frag lb γ ∗ ⌜p_sub_obj t a1' #lb⌝) ∗
                  ∃ susp,
                    lg_mapg_frag susp γ ∗ ⌜v_sub_obj t a2' #susp⌝) ∗
                pencount_frag (c + pn) ∗
                visited_map_update_pending vm mp γl pn ctr ∗
                (* Decoration wand — fired by the caller right after
                   [visited_deser_commit_*], whose products are exactly its
                   inputs. Everything with commit-dependent tauth leaves is
                   assembled here: the fresh suspenders' [auth_susp_v_inv]
                   invariants inside [A], the mapg/cap pieces and
                   [pval_snapshot]s inside [sub_susp_count_frags]; the raw
                   points-to halves, [unfilled] tokens, prophecies and
                   [vmeta_token]s are captured in the wand's closure. The □
                   premise is the caller's obligation to mint apartness
                   witnesses ([pval_snapshot]) for freshly allocated
                   verifier locs at the just-committed id. *)
                (cap_frag id c -∗
                 (match c with
                  | 0%nat => emp
                  | _ => mapg_frag id 1 a2'
                  end) -∗
                 (* The registered prediction coincides with the defined
                    serialization — needed only where a suspension was
                    actually created (the tauth leaf's emp_v invariant);
                    [emp] at [c = 0] so compound paths thread it
                    trivially. *)
                 (match c with
                  | 0%nat => emp
                  | _ => ⌜s_reg = s_def⌝
                  end) ={⊤}=∗
                   A a1' a2' a3 ∗
                   sub_susp_count_frags t a2' c id c ∗
                   ser_v_proph t id a2' s_def)) ∨
              (⌜s_pred ≠ s_real⌝ ∗ (lrel_tern_un A) a1')) }}})).

  Definition unsuspend_spec (unsuspend : val) (A : lrel Σ) (t : evi_type) : iProp Σ :=
    ∀ E (a1 a2 a3 : val),
      ⌜↑prover_susp_set ⊆ E⌝ -∗
      {{{ ▷ A a1 a2 a3 ∗ seq_tok E ∗ intransit 1%Qp }}}
        unsuspend a1
      {{{ un_v s, RET un_v; seq_tok E ∗ intransit 1%Qp ∗
          ⌜unsusp t a1 un_v⌝ ∗ unsusp_ser_p t un_v s }}}.
            (* if o is Some v then ∃ s, unsusp_ser_p t v s (* ∗ s_is_ser_p_proph t a1 s'*)
            else ⌜invalid_value t a1⌝ ∨ (∃ s, unsusp_ser_p t a1 s) }}}. *)

  (** [susp_ser_p t' v s_def] ties [t'] to [v]'s shape — without it the
      spec is unprovable at the tauth leaf ([auth_suspend_p] destructs a
      pair, so e.g. [t' = tstring] with [v] a Box would leave the code
      stuck with no refutation available). Mirrors how
      [suspend_v_deser_spec]'s precondition carries the witness. *)
  Definition suspend_spec_bin (suspend : val) (A : lrel_un Σ) (t : evi_type) : iProp Σ :=
    ∀ t' (v un_v : val) (s_def : string),
      {{{ ⌜unsusp t' v un_v⌝ ∗ susp_ser_p t' v s_def ∗ ▷ A v }}}
        suspend un_v
      {{{ v' s c, RET v'; A v' ∗ susp_ser_p_real t c v' s }}}.

  Definition unsuspend_spec_bin (unsuspend : val) (A : lrel_un Σ) (t : evi_type) : iProp Σ :=
    ∀ E (a1 : val),
      ⌜↑prover_susp_set ⊆ E⌝ -∗
      {{{ ▷ A a1 ∗ seq_tok E }}}
        unsuspend a1
      {{{ un_v, RET un_v; seq_tok E ∗ ⌜unsusp t a1 un_v⌝ }}}.

  (* Definition v_deser_spec_un (v_deser : val) (A : lrel_un Σ) (t : evi_type) : iProp Σ :=
    □(∀ K tᵥ (id : nat) (s' : string),
      spec_verifier tᵥ (fill K (v_deser #id))
      ={⊤}=∗ ∃ (v_deser_par: val),
        spec_verifier tᵥ (fill K v_deser_par) ∗
        □(∀ K tᵥ,
          spec_verifier tᵥ (fill K (v_deser_par #s'))
          ={⊤}=∗
            (∃ (c : nat) (a2' : val) s'',
              spec_verifier tᵥ (fill K (SOMEV a2')) ∗
              ser_v_proph t id a2' s'' ∗ sub_susp_count_frags t a2' c id c ∗
              A a2') ∨
            spec_verifier tᵥ (fill K NONEV))). *)

  Definition v_count_spec (v_count : val) (t : evi_type) : iProp Σ :=
    □(∀ K tᵥ a c id Nc v_outer,
      sub_susp_count t a c id Nc v_outer -∗
      spec_verifier tᵥ (fill K (v_count a))
      ={⊤}=∗
        sub_susp_count t a c id Nc v_outer ∗
        spec_verifier tᵥ (fill K #c)).

  Definition v_ser_spec (v_ser : val) (t : evi_type) : iProp Σ :=
    □(∀ K tᵥ a s id Nc v_outer,
      sub_susp_count t a 0 id Nc v_outer -∗
      ser_v_proph t id a s -∗
      spec_verifier tᵥ (fill K (v_ser a))
      ={⊤}=∗
        sub_susp_count t a 0 id Nc v_outer ∗
        ser_v_proph t id a s ∗
        spec_verifier tᵥ (fill K (SOMEV #s))).
      
  (** Step the prover's unsusp-serializer and the verifier's serializer
      together, in the style of [suspend_v_deser_spec]/[unsuspend_spec].
      The WP over [p_ser un_a1] is what pays for interp unfoldings: each
      prover pure step mints a later credit, so recursive wrappers (mu)
      strip exactly as many ▷s as they take steps — a verifier-only fupd
      cannot (and a fixed [£ n] precondition would not scale to nested
      recursion). The post returns the SAME string on both sides, so
      hash agreement in [refines_auth_auth] is by construction. *)
  (** Persistent witness that every susp position under the verifier
      value has been FILLED. Available at the p_auth/v_auth hashing
      site: the fill precedes serialization, and [filled] (persistent)
      comes out of [count_update]. Excludes [auth_susp_emp_v] when
      [auth_ser_spec]'s tauth case opens the ver-susp invariant, so
      [auth_ser_v] never returns NONEV. *)
  Fixpoint ser_v_filled (t : evi_type) (v : val) : iProp Σ :=
    match t with
    | tprod t1 t2 =>
        ∃ v1 v2, ⌜v = (v1, v2)%V⌝ ∗ ser_v_filled t1 v1 ∗ ser_v_filled t2 v2
    | tsum t1 t2 =>
        (∃ v1, ⌜v = InjLV v1⌝ ∗ ser_v_filled t1 v1) ∨
        (∃ v2, ⌜v = InjRV v2⌝ ∗ ser_v_filled t2 v2)
    | tstring | tint => True
    | tauth =>
        ∃ v1, ⌜v = SOMEV v1⌝ ∗
          ((∃ h : string, ⌜v1 = InjLV #h⌝) ∨
           (∃ susp : loc, ⌜v1 = InjRV #susp⌝ ∗ filled susp))
    end.

  #[global] Instance ser_v_filled_persistent t v :
    Persistent (ser_v_filled t v).
  Proof. revert v. induction t => v; simpl; apply _. Qed.

  Definition auth_ser_spec (p_ser v_ser : val) (A : lrel_tern Σ) (t : evi_type) : iProp Σ :=
    ∀ K tᵥ (a1 un_a1 a2 a3 : val) (s : string),
      {{{ ⌜unsusp t a1 un_a1⌝ ∗
          ▷ (lrel_tern_tern A) a1 a2 a3 ∗
          unsusp_ser_p t un_a1 s ∗
          ser_v_filled t a2 ∗
          seq_tok ⊤ ∗
          spec_verifier tᵥ (fill K (v_ser a2)) }}}
        p_ser un_a1
      {{{ RET #s;
          seq_tok ⊤ ∗
          ser_v t a2 s ∗
          spec_verifier tᵥ (fill K (SOMEV #s)) }}}.
      
  (* Definition v_auth_ser_spec_un (v_ser : val) (A : lrel_un Σ) (t : evi_type) : iProp Σ :=
    □(∀ K tᵥ a2 s,
      A a2 -∗
      spec_verifier tᵥ (fill K (v_ser a2))
      ={⊤}=∗ 
        ser_v t a2 s ∗ spec_verifier tᵥ (fill K (SOMEV #s))). *)

  Definition lrel_tern_evidence (A : lrel_tern Σ) : lrel Σ := LRel (λ v1 v2 _,
    ∃ (t : evi_type) (p_ser_susp p_ser_unsusp p_susp p_unsusp v_ser v_deser v_count : val),
      ⌜v1 = (p_ser_susp, p_ser_unsusp, p_susp, p_unsusp)%V⌝ ∗ ⌜v2 = (v_ser, v_deser, v_count)%V⌝ ∗
      unsusp_p_ser_spec p_ser_unsusp t ∗ susp_p_ser_spec p_ser_susp t ∗
      suspend_v_deser_spec p_ser_susp p_susp v_deser A t ∗ unsuspend_spec p_unsusp A t ∗
      v_ser_spec v_ser t ∗ auth_ser_spec p_ser_unsusp v_ser A t ∗
      v_count_spec v_count t)%I.

  Definition lrel_un_evidence (A : lrel_un Σ) : lrel_un Σ := LRelUn (λ v1,
    ∃ (t : evi_type) (p_ser_susp p_ser_unsusp p_susp p_unsusp v_ser v_deser v_count : val),
      ⌜v1 = (p_ser_susp, p_ser_unsusp, p_susp, p_unsusp)%V⌝ ∗
      unsusp_p_ser_spec p_ser_unsusp t ∗ susp_p_ser_spec p_ser_susp t ∗
      suspend_spec_bin p_susp A t ∗ unsuspend_spec_bin p_unsusp A t)%I.

  (* Definition lrel_un_evidence (A : lrel_un Σ) : lrel_un Σ := LRelUn (λ v2,
    ∃ (t : evi_type) (v_ser v_deser v_count : val),
      ⌜v2 = (v_ser, v_deser, v_count)%V⌝ ∗
      v_ser_spec v_ser t ∗ v_auth_ser_spec_un v_ser A t ∗
      v_deser_spec_un v_deser A t ∗ v_count_spec v_count t)%I. *)

  Definition lrel_evidence' (A : lrel_tern Σ) : lrel_ternC Σ :=
    LRelTern (lrel_tern_evidence A)
             (* (lrel_bi_evidence (lrel_tern_bin A)) *)
             (lrel_un_evidence (lrel_tern_un A)).

  Program Definition lrel_evidence : kindO Σ (⋆ ⇒ ⋆)%kind := λne A, lrel_evidence' A.
  Next Obligation.
    intros n A B HAB.
    rewrite /lrel_evidence' /=.
    split; [intros ???|intros ?];
      rewrite /lrel_car/= /lrel_un_car/=
        /lrel_tern_evidence /lrel_un_evidence
        /suspend_v_deser_spec /unsuspend_spec
        /auth_ser_spec /suspend_spec_bin /unsuspend_spec_bin;
      solve_proper.
  Qed.

  Definition auth_p (un_a v : val) (s : string) : iProp Σ :=
    ∃ (lb lr : loc) (ps : proph_id),
      ⌜v = BoxV (#lb, #lr, un_a, #(hash s), #ps)%V⌝ ∗
        (seq_inv (prover_susp_n v) (susp_p_fill_inv ps lb lr) ∨
        seq_inv (prover_susp_n v) (susp_p_unfill_inv ps lb lr)).

  Definition auth_v id (v : val) (s : string) : iProp Σ :=
    (⌜v = InjLV #(hash s)⌝ ∗ id_token id) ∨
      (∃ (s' : string) (susp : loc) pid γ,
        ⌜v = InjRV #susp⌝ ∗ ⌜id > pid⌝ ∗
        pval_frag id susp ∗
        pval_snapshot susp pid ∗
        lg_mapg_frag susp γ ∗ visit_reached_done γ ∗
        (visit_finished γ -∗ id_token id) ∗
        ⌜s' = some_ser_str (string_ser_str (hash s))⌝ ∗
        seq_inv (ver_susp_n susp)
          (auth_susp_v_inv pid v s')).

  Definition auth_transit_v (E : coPset) (id : nat) (v : val) (s : string) : iProp Σ :=
    (⌜v = InjLV #(hash s)⌝ ∗ id_token id ∗ intransit 1 ∗ seq_tok E) ∨
      (∃ (s' : string) (susp : loc) pid γ,
        ⌜v = InjRV #susp⌝ ∗ ⌜id > pid⌝ ∗
        pval_frag id susp ∗
        pval_snapshot susp pid ∗
        lg_mapg_frag susp γ ∗ visit_reached_done γ ∗
        (visit_finished γ -∗ id_token id) ∗
        ⌜s' = some_ser_str (string_ser_str (hash s))⌝ ∗
        seq_inv (ver_susp_n susp)
          (auth_susp_v_inv pid v s') ∗
        auth_susp_v_transit_inv pid v s' ∗
        seq_tok (E ∖ ↑(ver_susp_n susp)) ∗
        (▷ auth_susp_v_inv pid v s' ∗
          seq_tok (E ∖ ↑(ver_susp_n susp))
          ={⊤}=∗ seq_tok E)).

  Definition susplb_gname γ (v1 v2 : val) : iProp Σ :=
    ∃ (susp lb lr : loc) un_a v1' h,
      ⌜v1 = BoxV (#lb, #lr, un_a, #h, v1')%V ∧ v2 = InjRV #susp⌝ ∗
        lg_mapg_p_frag lb γ ∗ lg_mapg_frag susp γ.

  Definition auth_pv (un_vₚ vₚ vᵥ : val) (s : string) : iProp Σ :=
    ∃ (lb lr : loc) (ps : proph_id),
      ⌜vₚ = BoxV (#lb, #lr, un_vₚ, #(hash s), #ps)%V⌝ ∗
      ((⌜vᵥ = InjLV #(hash s)⌝ ∗
        seq_inv (prover_susp_n vₚ) (susp_p_fill_inv ps lb lr)) ∨
      (∃ γ (s' : string) (susp : loc) pid,
        ⌜vᵥ = InjRV #susp⌝ ∗ lg_mapg_p_frag lb γ ∗
        seq_inv (prover_susp_n vₚ) (susp_p_unfill_inv ps lb lr) ∗
        pval_snapshot susp pid ∗
        lg_mapg_frag susp γ ∗
        ⌜s' = some_ser_str (string_ser_str (hash s))⌝ ∗
        seq_inv (ver_susp_n susp)
          (auth_susp_v_inv pid vᵥ s'))).

  Definition lrel_auth_tern (A : lrel_tern Σ) : lrel Σ := LRel (λ v1 v2 v3,
    ∃ (t : evi_type) (v2' a1 a2 un_a1 : val) (s : string),
      ⌜v2 = SOMEV v2' ∧ unsusp t a1 un_a1⌝ ∗
      susp_ser_p t a1 s ∗ A a1 a2 v3 ∗
      auth_pv un_a1 v1 v2' s)%I.

  (* Definition lrel_auth_bin (A : lrel_bin Σ) : lrel_bin Σ := LRelBin (λ v1 v3,
    ∃ (t : evi_type) (a1 un_a1 : val) (s : string),
      ⌜unsusp t a1 un_a1⌝ ∗
      susp_ser_p t a1 s ∗ A a1 v3 ∗
      auth_p un_a1 v1 s)%I. *)

  Definition lrel_auth_un (A : lrel_un Σ) : lrel_un Σ := LRelUn (λ v1,
    ∃ (t : evi_type) (a1 un_a1 : val) (s : string),
      ⌜unsusp t a1 un_a1⌝ ∗
      susp_ser_p t a1 s ∗ A a1 ∗
      auth_p un_a1 v1 s)%I.

  Definition lrel_auth' (A : lrel_tern Σ) : lrel_tern Σ :=
    LRelTern (lrel_auth_tern A)
             (* (lrel_auth_bin (lrel_tern_bin A)) *)
             (lrel_auth_un (lrel_tern_un A)).

  Program Definition lrel_auth : kindO Σ (⋆ ⇒ ⋆)%kind := λne A, lrel_auth' A.
  Next Obligation.
    intros n A B HAB.
    rewrite /lrel_auth' /=.
    split; [intros ???|intros ?];
      rewrite /lrel_car/= /lrel_un_car/=
        /lrel_auth_tern /lrel_auth_un;
      solve_proper.
  Qed.

End authenticatable_definitions.

Class tabseqG (Σ: gFunctors) := {
  tabseqG_na_invG :: na_invG Σ;
  tabseqG_name: gname;
}.

Definition tabseq_inv `{!invGS_gen hlc Σ} `{!tabseqG Σ} (N : namespace) (P : iProp Σ) :=
  na_inv tabseqG_name N P.
Definition tabseq_tok `{!invGS_gen hlc Σ} `{!tabseqG Σ} (E : coPset) :=
  na_own tabseqG_name E.

Section authentikit_definitions.
  Context `{!authG Σ, !seqG Σ, !tabseqG Σ, !correctnessG Σ}.

  Definition v_finish_spec' (finish x a ser : val) : iProp Σ :=
		□(∀ (E: coPset) tᵥ K (s : string) (t : evi_type) id Nc,
      □(∀ pid susp γ, ⌜pid < id⌝ -∗ pval_frag pid susp -∗
        lg_mapg_frag susp γ -∗ visit_reached_done γ -∗ 
        ⌜↑(ver_susp_n susp) ⊆ E⌝) -∗
      tabseq_tok ⊤ -∗ £ 1 -∗ 
      ser_v_proph t id x s -∗ v_ser_spec ser t -∗
			sub_susp_count t x 0 id Nc x -∗ auth_transit_v E id a s -∗
      tern_state -∗
			spec_verifier tᵥ (fill K (finish #()))
			={⊤}=∗ 
        spec_verifier tᵥ (fill K (SOMEV #())) ∗
        tabseq_tok ⊤ ∗ seq_tok E ∗
        tern_state ∗ intransit 1).
         (* ∗
        (∀ γ, visit_reached_done γ id -∗ visit_finished γ id)). *)

  Definition v_susp_big_sep_lam (m : gmap val val) (id : nat) agv : iProp Σ :=
    ∃ (ctr Nc: nat) (finish x a ser : val) (t : evi_type) (s : string) (q : Qp),
      (⌜ctr > 0 ∧ m !! #id = Some (#ctr, finish)%V ∧ agv ≡ to_frac_agree q x⌝ ∗
      £ 1 ∗ ser_v_proph t id x s ∗ serpred_frag id s ∗
      v_ser_spec ser t ∗ auth_v id a s ∗
      sub_susp_count_frags t x ctr id Nc ∗ v_finish_spec' finish x a ser)%I.

  Definition v_susp_big_sep (m : gmap val val) (m' : mapg_type) : iProp Σ :=
    [∗ map] id ↦ agv ∈ mapg_alive m', v_susp_big_sep_lam m id agv.

  Definition ctr_inv (ctr : nat) (m : gmap val val) : Prop :=
    ∀ (ctr' : nat), ctr' ≥ ctr → m !! #ctr' = None.

  Definition vm_big_sep_lam_unset 
    (m : gmap val val) (γ : gname) v : iProp Σ :=
      ∀ id, ⌜v = done_val id⌝ -∗ ∃ v', ⌜m !! #id = Some v'⌝.

  (* Definition vm_big_sep_lam_set 
    (m : gmap val val) (id' : nat) (γ : gname) v : iProp Σ :=
      ∀ id, ⌜id ≠ id'⌝ -∗ ⌜v = done_val id⌝ -∗ ∃ v', ⌜m !! #id = Some v'⌝. *)

  Definition vm_big_sep (m : gmap val val) (vm : state_mapg_type) : iProp Σ :=
    [∗ map] γ ↦ v ∈ vm, vm_big_sep_lam_unset m γ v.

  Definition is_v_susp_table (l : loc) : iProp Σ :=
    (∃ (d : val) (m : gmap val val) (m' : mapg_type) (vm : state_mapg_type)
        (ctr pn : nat) (msp : serpred_type),
      l ↦ᵥ d ∗ ⌜is_map d m⌝ ∗ v_susp_big_sep m m' ∗
      ⌜size (mapg_alive m') = size m⌝ ∗ visited_mapg_auth vm m' pn ctr ∗
      ⌜ctr_inv ctr m⌝ ∗ vm_big_sep m vm ∗ tern_state ∗ serpred_auth msp ∗
      ⌜dom msp ⊆ set_seq 0 ctr⌝)
    ∨ un_state.

  Definition inv_v_susp_table (l: loc) := tabseq_inv tableN (is_v_susp_table l).


  Definition p_finish_spec (finish ser a : val) (s : string) (c : nat) : iProp Σ :=
    ∀ E pr_s ls t q,
      ⌜↑prover_susp_set ⊆ E⌝ -∗
      {{{ seq_tok E ∗ intransit q ∗ proph_proof pr_s ls ∗
          susp_p_ser_spec_at ser t c a s }}}
          finish #pr_s
      {{{ ls', RET #s;
            seq_tok E ∗ proph_proof pr_s ls' ∗
            ⌜ls = s :: ls'⌝ ∗
            (∀ vm mp pn ctr (γl : pending_setg_type),
              tern_state -∗ penset_frag γl -∗
              pencount_frag pn -∗
              visited_mapg_auth vm mp pn ctr -∗
              ⌜size γl = c⌝ -∗
              ([∗ set] γ ∈ γl, ∃ lb,
                lg_mapg_p_frag lb γ ∗ ⌜p_sub_obj t a #lb⌝) ==∗
              tern_state ∗ pencount_frag (pn - size γl) ∗
              visited_mapg_pending_removed vm mp γl pn ctr) }}}.

  Definition p_buffer_elem (finish_s_pn : (val * string * nat)) : iProp Σ :=
    ∃ (finish ser a : val) (s : string) (pn : nat) (t : evi_type),
      ⌜finish_s_pn = (finish, s, pn)⌝ ∗
      susp_p_ser_spec_at ser t pn a s ∗
      p_finish_spec finish ser a s pn ∗ 
      (tern_state -∗ ∃ γl, tern_state ∗ penset_frag γl ∗ ⌜pn = size γl⌝ ∗
        ([∗ set] γ ∈ γl, ∃ lb, lg_mapg_p_frag lb γ ∗ ⌜p_sub_obj t a #lb⌝)).

  Definition p_buffer (buf : list (val * string * nat)) : iProp Σ :=
    [∗ list] k ↦ finish_s_pn ∈ buf, p_buffer_elem finish_s_pn.

  Definition sum_list (l : list nat) : nat :=
    fold_right Nat.add 0 l.

  Definition p_proof_state (v : val) (ps ps_fix : list string) (lpn : list nat) : iProp Σ :=
    ∃ (prf1 buf1 : val) (bufl : list val) (pn : nat),
      ⌜List.length ps = List.length bufl⌝ ∗
      ⌜List.length ps = List.length lpn⌝ ∗ ⌜pn = sum_list lpn⌝ ∗
      ⌜v = (prf1, buf1)%V⌝ ∗ p_buffer (List.combine (List.combine bufl ps) lpn) ∗
      ⌜is_proof prf1 ps_fix⌝ ∗ ⌜is_list bufl buf1⌝.

  Definition v_proof_state (v : val) (ps : list string) : iProp Σ :=
    ∃ (prf : val) (cntr : nat),
      ⌜v = (prf, #cntr)%V ∧ is_proof prf ps⌝ ∗ id_ctr_frag cntr.

  Definition lastn {A} (n : nat) (l : list A) : list A :=
    List.skipn (length l - n) l.

  Definition lrel_auth_comp_tern (A : lrel_tern Σ) : lrel Σ := LRel (λ v1 v2 v3,
    ∀ t2 K2 t3 K3 p (ps ps1 ps2 ps_fix : list string) (lpn : list nat) (w1 w2 : val),
      {{{ tabseq_tok ⊤ ∗ seq_tok ⊤ ∗ spec_verifier t2 (fill K2 (v2 w2)) ∗
          spec_ideal t3 (fill K3 (v3 #())) ∗ pencount_frag (sum_list lpn) ∗
          p_proof_state w1 ps1 ps_fix lpn ∗ v_proof_state w2 ps2 ∗
          proph_proof p ps ∗ ⌜ps = reverse ps2 ++ ps1⌝ ∗
          intransit 1%Qp ∗ tern_state
      }}}
        v1 w1
      {{{ ps1' lpn' (w1' a1 a3 : val), RET (w1', a1)%V;
          tabseq_tok ⊤ ∗ seq_tok ⊤ ∗ spec_ideal t3 (fill K3 a3) ∗ 
          intransit 1%Qp ∗ proph_proof p ps ∗ 
          p_proof_state w1' ps1' ps_fix lpn' ∗
          
          ((∃ ps2' (w2' a2 : val),
            pencount_frag (sum_list lpn') ∗
            ⌜ps = reverse ps2' ++ ps1'⌝ ∗ A a1 a2 a3 ∗ 
            spec_verifier t2 (fill K2 (SOMEV (w2', a2)%V)) ∗
            v_proof_state w2' ps2' ∗ tern_state) ∨
              
            ((⌜List.length ps < List.length ps1'⌝) ∨
              ⌜lastn (List.length ps1') ps ≠ ps1'⌝ ∗
              (lrel_tern_un A) a1 ∗ un_state))
      }}})%I.

  Definition lrel_auth_comp_un (A : lrel_un Σ) : lrel_un Σ := LRelUn (λ v1,
    ∀ p (ps ps1 ps_fix : list string) (lpn : list nat) (w1 : val),
      {{{ seq_tok ⊤ ∗
          p_proof_state w1 ps1 ps_fix lpn ∗ proph_proof p ps ∗
          ⌜lastn (List.length ps1) ps ≠ ps1⌝
      }}}
        v1 w1
      {{{ ps1' (w1' a1 : val), RET (w1', a1)%V;
          ⌜lastn (List.length ps1') ps ≠ ps1'⌝ ∗
          proph_proof p ps ∗ 
          seq_tok ⊤ ∗ p_proof_state w1' ps1' ps_fix lpn ∗
          A a1
      }}})%I.

  (* Definition lrel_auth_comp_un (A : lrel_un Σ) : lrel_un Σ := LRelUn (λ v2,
    (□ ∀ t2 K2 (ps2 : list string) (w2 : val),
      seq_tok ⊤ ∗ spec_verifier t2 (fill K2 (v2 w2)) ∗
      v_proof_state w2 ps2
      ={⊤}=∗ 
        seq_tok ⊤ ∗ 
        ((∃ ps2' (w2' a2 : val), 
          v_proof_state w2' ps2' ∗
          spec_verifier t2 (fill K2 (SOMEV (w2', a2)%V)) ∗ A a2) ∨
          spec_verifier t2 (fill K2 NONEV))))%I. *)

  Definition lrel_auth_comp' (A : lrel_tern Σ) : lrel_tern Σ :=
    LRelTern (lrel_auth_comp_tern A)
             (* (lrel_auth_comp_bin (lrel_tern_bin A)) *)
             (lrel_auth_comp_un (lrel_tern_un A)).

  Program Definition lrel_auth_comp : kindO Σ (⋆ ⇒ ⋆)%kind := λne A, lrel_auth_comp' A.
  Next Obligation.
    intros n A B HAB.
    rewrite /lrel_auth_comp' /=.
    split.
    - intros ???. rewrite /lrel_car/= /lrel_auth_comp_tern.
      solve_proper.
    - intros ?. rewrite /lrel_un_car/= /lrel_auth_comp_un.
      solve_proper.
  Qed.

  Definition auth_ctx {Θ} (Δ : ctxO Σ Θ) := ext (ext Δ lrel_auth) lrel_auth_comp.

End authentikit_definitions.
  