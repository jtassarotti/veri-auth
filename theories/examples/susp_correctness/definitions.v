From auth.prelude Require Import stdpp.
From auth.rel_logic_tern_susp Require Import model interp.
From auth.heap_lang Require Import typedproph.
From auth.heap_lang.lib Require Import serialization_susp list.
From auth.examples.susp_correctness Require Export resource_algebras.

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


Definition prover_susp_set (N : namespace) : namespace := N .@ "psusp".
Definition prover_susp_n (N : namespace) (v : val) : namespace := (prover_susp_set N) .@ v.

Definition ver_susp_set (N : namespace) : namespace := N .@ "vsusp".
Definition ver_susp_n (N : namespace) (v : val) : namespace := (ver_susp_set N) .@ v.

Section authenticatable_definitions.
  Context `{!authG Σ, !seqG Σ, !visited_mapG Σ, !lg_mapG Σ, !mapG Σ, !capG Σ, !intransitG Σ, !stateG Σ} (N : namespace).

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
        ∃ v', ((v = InjLV v' ∧ p_sub_obj t1 v' sv ∧ sv = v') ∨
                 (v = InjRV v' ∧ p_sub_obj t2 v' sv ∧ sv = v'))
    | tstring => False
    | tint => False
    | tauth =>
        ∃ (p : proph_id) (lb lr : loc) (a : val) (h : string),
          v = (#lb, #lr, a, #h, #p)%V ∧ sv = #lb
    end.

  Fixpoint v_sub_obj (t : evi_type) (v sv: val) :=
    match t with
    | tprod t1 t2 =>
        ∃ v1 v2, v = (v1, v2)%V ∧ (sv = v1 ∨ sv = v2 ∨ v_sub_obj t1 v1 sv ∨ v_sub_obj t2 v2 sv)
    | tsum t1 t2 =>
        ∃ v', ((v = InjLV v' ∧ v_sub_obj t1 v' sv ∧ v = v') ∨
                 (v = InjRV v' ∧ v_sub_obj t2 v' sv ∧ v = v'))
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
      ⌜v = (a, #h)%V ∧ s = simple_string h⌝.

  Definition susp_p_fill_inv (ps : proph_id) (lb lr : loc) : iProp Σ :=
    lb ↦ #false ∗
      ((∃ (bs : list bool), lr ↦ #false ∗ fill_proph_bs ps bs) ∨
      (∃ (bs : list bool), lr ↦ #true ∗ proph_bs ps bs) ∨
      (lr ↦ #false ∗ empty_proph_bs ps) ∨
      (∃ (bs : list bool) (q : Qp) (b : bool),
          lr ↦ #b ∗ proph_bs ps bs ∗ intransit q)).

  Definition auth_susp_ser_p_fill (v : val) (s : string) : iProp Σ :=
    ∃ (p : proph_id) (lb lr : loc) (a : val) (h : string) (r : bool),
      ⌜v = (#lb, #lr, a, #h, #p)%V ∧ s = filled_string h⌝ ∗
      lg_mapg_unalloc lb ∗
      seq_inv (prover_susp_n N v) (susp_p_fill_inv p lb lr).

  Definition susp_p_unfill_inv (ps : proph_id) (lb lr : loc) : iProp Σ :=
    (∃ (bs : list bool),
      lb ↦ #false ∗ lr ↦ #false ∗ unfill_proph_bs ps bs) ∨
    (∃ (r : bool) (bs : list bool) (n : nat) (γ : gname),
      lb ↦ #true ∗ lr ↦ #r ∗ proph_bs ps bs ∗ lg_mapg_frag lb γ ∗
      □ (good_state -∗ good_state ∗ visit_reached_done γ n)).

  Definition auth_susp_ser_p_emp (v : val) (s : string) : iProp Σ :=
    ∃ (p : proph_id) (lb lr : loc) (a : val) (h : string) (r : bool),
      ⌜v = (#lb, #lr, a, #h, #p)%V ∧ s = suspended_string⌝ ∗
      seq_inv (prover_susp_n N v) (susp_p_unfill_inv p lb lr).

  (* What it will actually serialize to *)
  Definition auth_susp_ser_p_real (v : val) (s : string) c : iProp Σ :=
    (auth_susp_ser_p_fill v s ∧ ⌜c = 0⌝) ∨ (auth_susp_ser_p_emp v s ∧ ⌜c = 1⌝).

  (* What it would serialize to without suspension *)
  Definition auth_susp_ser_p (v : val) (s : string) : iProp Σ :=
    ∃ (p : proph_id) (lb lr : loc) (a : val) (h : string),
      ⌜v = (#lb, #lr, a, #h, #p)%V ∧ s = simple_string h⌝.

  Definition auth_fill_ser_v (v : val) (s : string) : iProp Σ :=
    ∃ (h : string), ⌜s = filled_string h ∧ v = InjLV #h⌝.

  Definition auth_susp_fill_v (v : val) (s : string) : iProp Σ :=
    ∃ (h : string) (susp : loc), 
      ⌜s = filled_string h ∧ v = InjRV #susp⌝ ∗ susp ↦ᵥ{#(3/4)} InjRV #h.

  (* Definition auth_susp_emp_v (v : val) (s : string) : iProp Σ :=
    ∃ (h : string) (susp : loc) (pid: nat) (p : proph_id),
      ⌜s = suspended_string ∧ v = InjRV #susp⌝ ∗ 
      susp ↦ᵥ{#(3/4)} InjLV (#pid, #p) ∗ proph_v_susp p h. *)

  Definition auth_susp_emp_v_proph (pid : nat) (v : val) : iProp Σ :=
    ∃ (h : string) (susp : loc) (p : proph_id) pv pt (q : Qp) γ,
      ⌜v = InjRV #susp⌝ ∗ mapg_frag #pid q pv ∗ lg_mapg_frag susp γ ∗
      ⌜v_sub_obj pt pv #susp⌝ ∗ susp ↦ᵥ{#(3/4)} InjLV (#pid, #p) ∗ proph_v_susp p h.

  Definition auth_susp_v_ser_proph_inv (pid : nat) (v : val) (s : string) : iProp Σ :=
    (∃ (s1 : string), 
      ⌜s = filled_string (hash s1)⌝ ∗
      auth_susp_fill_v v s) ∨ 
    auth_susp_emp_v_proph pid v.

  Definition auth_susp_v_ser_proph (pid : nat) (v : val) (s : string) : iProp Σ :=
    seq_inv (ver_susp_n N v) (auth_susp_v_ser_proph_inv pid v s).

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
    | tauth => ∃ v1, ⌜v = SOMEV v1⌝ ∗ auth_fill_ser_v v1 s
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
                       (auth_fill_ser_v v1 s ∨ auth_susp_v_ser_proph pid v1 s)
  end.
 
  #[global] Instance ser_v_proph_persistent t pid v s : Persistent (ser_v_proph t pid v s).
  Proof. revert pid v s. induction t => pid v s; simpl; apply _. Qed.

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
                (visit_pending γ ∨ (∃ id, ⌜id > pid⌝ ∗ visit_done γ id)))))).

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

  Definition susp_p_ser_spec (ser : val) (t : evi_type) : iProp Σ :=
    ∀ (E : coPset) (a1 : val) (s : string) (c : nat) (q : Qp),
      ⌜↑prover_susp_set N ⊆ E⌝ -∗
      {{{ susp_ser_p_real t c a1 s ∗ seq_tok E ∗ intransit q }}}
        ser a1
      {{{ RET #s; seq_tok E ∗ intransit (q/2)%Qp ∗
          (∀ (γl : pending_setg_type),
            good_state -∗ penset_frag γl -∗ ⌜size γl = c⌝ -∗
            ([∗ set] γ ∈ γl,
              ∃ lb, lg_mapg_frag lb γ ∗ ⌜p_sub_obj t a1 #lb⌝) -∗
            good_state ∗ penset_frag γl ∗
            ([∗ set] γ ∈ γl, (∃ n, visit_reached_done γ n) ∗
              ∃ lb, lg_mapg_frag lb γ ∗ ⌜p_sub_obj t a1 #lb⌝)) }}}.

  (* Like [susp_p_ser_spec] but with [c, a, s] as fixed parameters and without
     [susp_ser_p_real] in the precondition (the prover-side serialization-shape
     is internalized when the spec is built). Used as the post-condition payload
     of [suspend_v_deser_spec], wrapped in [∃ t_real, ...]. *)
  Definition susp_p_ser_spec_at
      (ser : val) (t : evi_type) (c : nat) (a : val) (s : string) : iProp Σ :=
    ∀ (E : coPset) (q : Qp),
      ⌜↑prover_susp_set N ⊆ E⌝ -∗
      {{{ seq_tok E ∗ intransit q }}}
        ser a
      {{{ RET #s; seq_tok E ∗ intransit (q/2)%Qp ∗
          (∀ (γl : pending_setg_type),
            good_state -∗ penset_frag γl -∗ ⌜size γl = c⌝ -∗
            ([∗ set] γ ∈ γl,
              ∃ lb, lg_mapg_frag lb γ ∗ ⌜p_sub_obj t a #lb⌝) -∗
            good_state ∗ penset_frag γl ∗
            ([∗ set] γ ∈ γl, (∃ n, visit_reached_done γ n) ∗
              ∃ lb, lg_mapg_frag lb γ ∗ ⌜p_sub_obj t a #lb⌝)) }}}.

  Definition unsusp_p_ser_spec (ser : val) (t : evi_type) : iProp Σ :=
    ∀ (v : val) (s : string),
      {{{ unsusp_ser_p t v s }}}
        ser v
      {{{ RET #s; True }}}.

  Definition suspend_v_deser_spec
      (ser suspend v_deser : val) (A : lrel_tern Σ) (t : evi_type) : iProp Σ :=
    □(∀ t' (a1 un_a1 a2 a3 : val) (s_def s_pred : string)
         K tᵥ (id : nat) m d ps pn mlg,
      spec_verifier tᵥ (fill K (v_deser #id))
      ={⊤}=∗ ∃ (v_deser_par : val),
        spec_verifier tᵥ (fill K v_deser_par) ∗
        □(∀ K' tᵥ',
          {{{ ⌜unsusp t' a1 un_a1⌝ ∗
              ▷ (lrel_tern_as_lrel A) a1 a2 a3 ∗
              susp_ser_p t' a1 s_def ∗
              visited_mapg_auth m d ps pn ∗
              lg_mapg_auth mlg ∗
              spec_verifier tᵥ' (fill K' (v_deser_par #s_pred)) }}}
            suspend un_a1
          {{{ a1' s_real c, RET a1';
              (∃ t_real, susp_p_ser_spec_at ser t_real c a1' s_real) ∗
              ((⌜s_pred = s_real⌝ ∗ ∃ γl mlg' a2',
                lg_mapg_auth mlg' ∗
                ⌜size γl = c⌝ ∗ penset_frag γl ∗
                (lrel_tern_as_lrel A) a1' a2' a3 ∗
                susp_ser_p t a1' s_def ∗
                spec_verifier tᵥ' (fill K' (SOMEV a2')) ∗
                ([∗ set] γ ∈ γl, ∃ susp lb,
                  lg_mapg_frag lb γ ∗ lg_mapg_frag susp γ ∗
                  ⌜p_sub_obj t a1' #lb⌝ ∗ ⌜v_sub_obj t a2' #susp⌝) ∗
                sub_susp_count t a2' c id c a2' ∗
                ser_v_proph t id a2' s_def ∗
                visited_map_update_pending m d ps pn γl) ∨
              (⌜s_pred ≠ s_real⌝ ∗ (lrel_tern_bin A) a1' a3)) }}})).

  Definition unsuspend_spec (unsuspend : val) (A : lrel Σ) (t : evi_type) : iProp Σ :=
    ∀ E (a1 a2 a3 : val),
      ⌜↑prover_susp_set N ⊆ E⌝ -∗
      {{{ ▷ A a1 a2 a3 ∗ seq_tok E ∗ intransit 1%Qp }}}
        unsuspend a1
      {{{ un_v s, RET un_v; seq_tok E ∗ intransit 1%Qp ∗
          ⌜unsusp t a1 un_v⌝ ∗ unsusp_ser_p t un_v s }}}.
            (* if o is Some v then ∃ s, unsusp_ser_p t v s (* ∗ s_is_ser_p_proph t a1 s'*)
            else ⌜invalid_value t a1⌝ ∨ (∃ s, unsusp_ser_p t a1 s) }}}. *)

  Definition suspend_spec_bin (suspend : val) (A : lrel_bin Σ) (t : evi_type) : iProp Σ :=
    ∀ t' (v un_v a3 : val),
      {{{ ⌜unsusp t' v un_v⌝ ∗ ▷ A v a3 }}}
        suspend un_v
      {{{ v' s c, RET v'; A v' a3 ∗ susp_ser_p_real t c v' s }}}.

  Definition unsuspend_spec_bin (unsuspend : val) (A : lrel_bin Σ) (t : evi_type) : iProp Σ :=
    ∀ E (a1 a3 : val),
      ⌜↑prover_susp_set N ⊆ E⌝ -∗
      {{{ ▷ A a1 a3 ∗ seq_tok E }}}
        unsuspend a1
      {{{ un_v, RET un_v; seq_tok E ∗ ⌜unsusp t a1 un_v⌝ }}}.

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
              ser_v_proph t id a2' s'' ∗ sub_susp_count_frags t a2' c id c ∗
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
      sub_susp_count t a 0 id Nc v_outer -∗ ser_v_proph t id a s -∗
      spec_verifier tᵥ (fill K (v_ser a))
      ={⊤}=∗
        sub_susp_count t a 0 id Nc v_outer ∗ ser_v_proph t id a s ∗
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
      suspend_v_deser_spec p_ser_susp p_susp v_deser A t ∗ unsuspend_spec p_unsusp A t ∗
      v_ser_spec v_ser t ∗ v_auth_ser_spec v_ser A t ∗
      v_count_spec v_count t)%I.

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

  Definition auth_p (un_a v : val) (s : string) : iProp Σ :=
    ∃ (lb lr : loc) (ps : proph_id),
      ⌜v = (#lb, #lr, un_a, #(hash s), #ps)%V⌝ ∗
        (seq_inv (prover_susp_n N v) (susp_p_fill_inv ps lb lr) ∨
        seq_inv (prover_susp_n N v) (susp_p_unfill_inv ps lb lr)).

  Definition auth_v (v : val) (s : string) (id : nat) : iProp Σ :=
    (⌜v = InjLV #(hash s)⌝) ∨
      (∃ (s' : string) (susp : loc) pid γ,
        ⌜v = InjRV #susp⌝ ∗ lg_mapg_frag susp γ ∗
        visit_reached_done γ id ∗ ⌜id > pid⌝ ∗
        ⌜s' = some_ser_str (string_ser_str (hash s))⌝ ∗
        seq_inv (ver_susp_n N v) 
          (auth_susp_v_ser_proph_inv pid v s')).

  Definition susplb_gname (v1 v2 : val) : iProp Σ :=
    (∃ v, ⌜v2 = InjLV v⌝) ∨
      (∃ γ (susp lb lr : loc) un_a v1' h,
        ⌜v1 = (#lb, #lr, un_a, #h, v1')%V ∧ v2 = InjRV #susp⌝ ∗ 
          lg_mapg_frag lb γ ∗ lg_mapg_frag susp γ).

  Definition auth_pv (un_vₚ vₚ vᵥ : val) (s : string) : iProp Σ :=
    ∃ (lb lr : loc) (ps : proph_id),
      ⌜vₚ = (#lb, #lr, un_vₚ, #(hash s), #ps)%V⌝ ∗
      ((⌜vᵥ = InjLV #(hash s)⌝ ∗ 
        seq_inv (prover_susp_n N vₚ) (susp_p_fill_inv ps lb lr)) ∨
      (∃ (s' : string) (susp : loc) pid,
        ⌜vᵥ = InjRV #susp⌝ ∗ susplb_gname vₚ vᵥ ∗
        seq_inv (prover_susp_n N vₚ) (susp_p_unfill_inv ps lb lr) ∗
        ⌜s' = some_ser_str (string_ser_str (hash s))⌝ ∗
        seq_inv (ver_susp_n N vᵥ) 
          (auth_susp_v_ser_proph_inv pid vᵥ s'))).

  Definition lrel_auth_tern (A : lrel_tern Σ) : lrel Σ := LRel (λ v1 v2 v3,
    ∃ (t : evi_type) (v2' a1 a2 un_a1 : val) (s : string),
      ⌜v2 = SOMEV v2' ∧ unsusp t a1 un_a1⌝ ∗
      susp_ser_p t a1 s ∗ A a1 a2 v3 ∗
      auth_pv un_a1 v1 v2' s)%I.

  Definition lrel_auth_bin (A : lrel_bin Σ) : lrel_bin Σ := LRelBin (λ v1 v3,
    ∃ (t : evi_type) (a1 un_a1 : val) (s : string),
      ⌜unsusp t a1 un_a1⌝ ∗
      susp_ser_p t a1 s ∗ A a1 v3 ∗
      auth_p un_a1 v1 s)%I.

  Definition lrel_auth_un (A : lrel_un Σ) : lrel_un Σ := LRelUn (λ v2,
    ∃ (t : evi_type) (v2' a2 : val) (s : string),
      ⌜v2 = SOMEV v2'⌝ ∗ A a2)%I.

  Definition lrel_auth' (A : lrel_tern Σ) : lrel_tern Σ :=
    LRelTern (lrel_auth_tern A)
             (lrel_auth_bin (lrel_tern_bin A))
             (lrel_auth_un (lrel_tern_un A)).

  Program Definition lrel_auth : kindO Σ (⋆ ⇒ ⋆)%kind := λne A, lrel_auth' A.
  Next Obligation. Admitted.

End authenticatable_definitions.
  