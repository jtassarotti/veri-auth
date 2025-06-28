From auth.prelude Require Import stdpp.
From auth.examples Require Import authentikit.
From auth.heap_lang Require Import notation lib.list.
From auth.typing Require Import types typing.

(** * Authenticated pair client  *)

(* TODO: fix the broken 5-let-binding *)

Definition pair_module : val :=
  λ: "Authentikit",
    let, ("return", "bind", "Authenticatable") := "Authentikit" in
    unpack: "A" := "Authenticatable" in

    let, ("...", "Auth_string", "Auth_int", "auth", "unauth") := "A" in
    let, ("Auth_auth", "Auth_pair", "Auth_sum") := "..." in

    let: "pair" := "Auth_pair" #~ #~ "Auth_string" "Auth_string" in

    let: "make_pair" := "auth" #~ "pair" in
    let: "get_fst" := λ: "c", "bind" #~ #~ ("unauth" #~ "pair" "c") (λ: "p", "return" #~ (Fst "p")) in
    let: "get_snd" := λ: "c", "bind" #~ #~ ("unauth" #~ "pair" "c") (λ: "p", "return" #~ (Snd "p")) in

    ("make_pair", "get_fst", "get_snd").

Definition pair_module_type_open {Θ} : type (Θ ▹ (⋆ ⇒ ⋆)%kind ▹ (⋆ ⇒ ⋆)%kind) ⋆ :=
   ((t_string * t_string → var1 (t_string * t_string)) *
   (var1 (t_string * t_string) → var0 t_string) *
   (var1 (t_string * t_string) → var0 t_string))%ty.

Definition pair_module_type : type (ε ▹ (⋆ ⇒ ⋆)%kind ▹ (⋆ ⇒ ⋆)%kind) ⋆ :=
  (Authentikit_func var1 var0 → pair_module_type_open)%ty.

Lemma pair_module_typed Γ :
  ε ▹ (⋆ ⇒ ⋆)%kind ▹ (⋆ ⇒ ⋆)%kind |ₜ Γ ⊢ₜ pair_module : pair_module_type.
Proof.
  rewrite /pair_module /pair_module_type /pair_module_type_open /Authentikit_func.
  do 2 t_beta.
  typecheck.
Qed.

Definition pair_client_comp : val :=
  λ: "pair_module",
    unpack: "x" := "pair_module" in
    let, ("make_pair", "get_fst", "get_snd") := "x" in
    "get_fst".

Definition pair_client_data : val :=
  λ: "pair_module",
    unpack: "x" := "pair_module" in
    let, ("make_pair", "get_fst", "get_snd") := "x" in
    "make_pair" (#"hello", #"world").

Definition pair_client : val :=
  λ: "pair_module",
    let: "data" := pair_client_data "pair_module" in
    let: "comp" := pair_client_comp "pair_module" "data" in
    "comp".

Lemma pair_client_typed Γ :
  (ε ▹ (⋆ ⇒ ⋆)%kind ▹ (⋆ ⇒ ⋆)%kind) |ₜ Γ ⊢ₜ
  pair_client : (pair_module_type_open → var0 t_string).
Proof. repeat econstructor. Qed.

Definition pair_client_closed : expr :=
  Λ: Λ: λ: "AK", pair_client (pair_module "AK").

Lemma pair_client_closed_typed :
  ε |ₜ ∅ ⊢ₜ pair_client_closed : (∀: ⋆ ⇒ ⋆; ⋆ ⇒ ⋆, Authentikit_func var1 var0 → var0 t_string).
Proof.
  do 4 econstructor.
  - eapply pair_client_typed.
  - econstructor; [|by econstructor].
    eapply pair_module_typed.
Qed.

(** * Security of instantiation with the naive list implementation of Authentikit *)
From auth.examples Require Import authentikit_list.

Definition p_run_pair_client v := p_run #~ v (pair_client_closed #~ #~ p_Authentikit).
Definition v_run_pair_client := v_run #~ (pair_client_closed #~ #~ v_Authentikit).

From auth.examples Require Import authentikit_list_security.

Definition i_run_pair_client := i_run #~ (pair_client_closed #~ #~ i_Authentikit).

Lemma pair_client_secure σ (l : list string) prf :
  is_list l prf →
  adequate hash_collision NotStuck (v_run_pair_client prf) σ
    (λ vᵥ σᵥ, ∃ thpᵢ σᵢ vᵢ o,
        vᵥ = $o ∧
        if o is Some wᵥ then
          rtc erased_step ([i_run_pair_client], σ) (of_val vᵢ :: thpᵢ, σᵢ) ∧
           wᵥ = vᵢ
        else True).
Proof.
  intros Hprf.
  rewrite /v_run_pair_client /i_run_pair_client.
  eapply (authentikit_security_syntactic _ _ t_string); [constructor| |done].
  apply pair_client_closed_typed.
Qed.

(** Simple example of a 'semantic' security proof that breaks the Authentikit library abstraction and *)
(**  maniplates the proof stream manually; basically corresponds to just inlining function calls *)

(** type 'a auth = string *)
(** type 'a authenticated_computation = proof -> (proof * 'a) option *)
Definition pair_ser : serialization_scheme :=
  prod_serialization_scheme string_serialization_scheme string_serialization_scheme.

Arguments s_serializer : simpl never.
Arguments s_deserializer : simpl never.

(** (string * string) auth → string authenticated_computation) *)
Definition v_pair_fst : val :=
  λ: "pair_auth",
    λ: "proof",
    match: list_head "proof" with
      NONE => NONE
    | SOME "p" =>
        if: Hash "p" = "pair_auth" then
          match: pair_ser.(s_deserializer) "p" with
            NONE => NONE
          | SOME "a" => SOME (list_tail "proof", Fst "a")
          end
        else NONE
    end.

Definition i_pair_fst : val :=
  λ: "pair_auth" <>, Fst "pair_auth".

Section semantic.
  Context `{!authG Σ}.

  Lemma refines_fst_security Θ Δ Γ :
    ⊢ { (Θ ▹ (⋆ ⇒ ⋆)%kind ▹ (⋆ ⇒ ⋆)%kind); auth_ctx Δ; Γ }
      ⊨ v_pair_fst ≤log≤ i_pair_fst : var1 (t_string * t_string) → var0 t_string.
  Proof.
    iIntros (vs) "#Hvs %Kᵢ %tᵢ Hi /=".
    rewrite /i_pair_fst /v_pair_fst.

    wp_pures. iModIntro. iFrame. clear.
    iIntros (v1 v2) "!# Hauth".
    interp_unfold in "Hauth".
    iDestruct "Hauth" as (a1 t s Hser ->) "(Hp & #Hs)".
    iDestruct "Hp" as (w1 w2 u1 u2 -> ->) "[Hs1 Hs2]".
    interp_unfold in "Hs1 Hs2".
    iDestruct "Hs1" as "(%s1 & -> & ->)".
    iDestruct "Hs2" as "(%s2 & -> & ->)".
    iIntros (??) "Hi". i_pures.
    wp_pures. iModIntro. iFrame.
    interp_unfold!.
    iIntros "!# % [%prf %Hprf] % % Hi".
    wp_pures. i_pures.
    wp_apply (gwp_list_head with "[//]").
    iIntros (v [[-> ->] | (?&?&->&->)]).
    { wp_pures. by iExists None. }
    wp_pures.
    wp_apply wp_hash; [done|]. iIntros "#Hs'".
    wp_pures. case_bool_decide as Heq; simplify_eq; wp_pures; last first.
    { by iExists None. }
    destruct t; destruct! Hser; simplify_eq.

    wp_apply s_deser_sound; [done|].
    iIntros ([] Hser); wp_pures; last first.
    { by iExists None. }

    (* TODO: don't use auto-generated names... *)
    destruct (decide (collision x (prod_ser_str H0 H2))) as [|Hnc%not_collision].
    { iExFalso. by iApply (hashes_auth.hashed_inj_or_coll with "Hs' Hs"). }
    destruct Hnc as [-> |?]; [|simplify_eq].
    destruct! Hser; simplify_eq.
    destruct t1; destruct! H4; simplify_eq.
    destruct t2; destruct! H5; simplify_eq.
    destruct! H8; destruct! H9; simplify_eq.

    wp_pures.
    wp_apply gwp_list_tail; [done|].
    iIntros "/=" (??). wp_pures.
    iFrame. iModIntro.
    iExists (Some _). iSplit; [done|].
    iFrame.
    iExists _, _. iFrame "# %".
    iSplit; [done|]. by iExists _.
  Qed.

End semantic.

From auth.examples Require Import authentikit_list_correctness.

(** * Correctness of instantiation with the naive list implementation of Authentikit *)

Definition i_run_pair_client' := i_run #~ (pair_client_closed #~ #~ i_Authentikit).

Lemma pair_client_correct σ (p : proph_id) :
  p ∈ σ.(used_proph_id) →
  adequate hash_collision NotStuck (p_run_pair_client #p) σ
    (λ vₚ σₚ, ∃ thpᵥ thpᵢ σᵥ σᵢ a prf,
        vₚ = (prf, a)%V ∧
          rtc erased_step ([v_run_pair_client prf], σ) (of_val (SOMEV a) :: thpᵥ, σᵥ) ∧
          (** and a valid ideal execution returning [a] *)
          rtc erased_step ([i_run_pair_client'], σ) (of_val a :: thpᵢ, σᵢ)).
Proof.
  intros Hp.
  eapply (authentikit_correctness_syntactic _ _ t_string); [done|constructor|].
  eapply pair_client_closed_typed.
Qed.

(** Simple example of a 'semantic' correctness proof that breaks the Authentikit library abstraction and *)
(** maniplates the proof stream manually; basically corresponds to just inlining function calls *)

(** type 'a auth = 'a * string *)
(** type 'a authenticated_computation = proph -> unit -> proof * 'a *)
(** (string * string) auth → string authenticated_computation) *)
Definition p_pair_fst : val :=
  λ: "pair_auth",
    λ: "p" <>,
      let, ("pair", "h") := "pair_auth" in
      let: "s" := pair_ser.(s_serializer) "pair" in
      resolve_proph: "p" to: (SOME "s");;
      (["s"], Fst "pair").

Definition i_pair_fst' : val :=
  λ: "pair_auth" <>, Fst "pair_auth".

Section semantic.
  Context `{!authG Σ}.

  Lemma refines_fst_correctness Θ Δ Γ :
    ⊢ { (Θ ▹ (⋆ ⇒ ⋆)%kind ▹ (⋆ ⇒ ⋆)%kind); auth_ctx Δ; Γ }
      ⊨ p_pair_fst ≤log≤ v_pair_fst ≤log≤ i_pair_fst' : var1 (t_string * t_string) → var0 t_string.
  Proof.
    iIntros (vs) "#Hvs". iIntros (????) "Hv Hi".
    rewrite /p_pair_fst /v_pair_fst /i_pair_fst'.
    wp_pures. iModIntro. iFrame. clear.
    iIntros (v1 v2 v3) "!# Hauth /=".
    iDestruct "Hauth" as (t a1 a2 s -> Hser ->) "(#Hs & Hp)".
    iDestruct "Hp" as (w1 w2 w3 u1 u2 u3 -> -> ->) "[(% & -> & -> & ->) (% & -> & -> & ->)]".
    iIntros (????) "Hv Hi".
    i_pures. v_pures. wp_pures.
    iModIntro. iFrame.
    iIntros (????????) "!# (Hv & Hi & [%Hprf Hp]) H".
    i_pures. v_pures. wp_pures.
    wp_apply s_ser_spec.
    { iExists _, _. iSplit; [done|]. by iSplit; iExists _. }
    iIntros (s2 Hs2). wp_pures.
    wp_apply (wp_resolve_proph_string with "Hp").
    iIntros (?) "[-> Hp]". wp_pures.
    wp_apply (gwp_list_cons s2 [] with "[//]").
    iIntros (??). wp_pures.
    v_bind (list_head _).
    iMod (gwp_list_head (g := gwp_spec_verifier) ⊤ w (s2 :: _) ()
            (λ v, ⌜v = SOMEV #s2⌝)%I with "[//] [] [$Hv //]") as (?) "[Hv ->] /=".
    { iIntros "!>" (? [[] | (?&?&?&?)]); simplify_eq. eauto. }
    v_pures.
    v_bind (Hash _).
    iMod (step_verifier_hash with "Hv") as "Hv /="; [done|].
    v_pures.
    { (* TODO: fix *) solve_vals_compare_safe. }

    (* TODO: don't use auto-generated names *)
    destruct t; destruct! Hser; simplify_eq.
    destruct! Hs2; simplify_eq.
    destruct! H9; destruct !H10; simplify_eq.
    assert (prod_ser_str (string_ser_str H0) (string_ser_str H4) = prod_ser_str H1 H3) as Heq.
    { destruct t1; destruct! H5; destruct t4; destruct! H6; by simplify_eq. }
    simplify_eq.
    iEval (rewrite bool_decide_eq_true_2 //) in "Hv".
    v_pures.

    v_bind (s_deserializer _ _).
    iMod (s_deser_complete (g := gwp_spec_verifier) _ ⊤ _ _ () (λ v, ⌜v = SOMEV (#H0, #H4)⌝)%I
           with "[] [] [$Hv //]") as (?) "[Hv ->] /=".
    { iPureIntro. do 4 eexists. split; [done|]. repeat split; eexists; eauto. }
    { by iIntros "_". }

    v_pures.
    v_bind (list_tail _).
    destruct Hprf as (? & -> & ?).
    iMod (gwp_list_tail (g := gwp_spec_verifier) ⊤ _ ((_ : string) :: _) ()
            (λ v, ⌜is_proof _ vs'⌝)%I with "[] [] [$Hv //]") as (u) "[Hv %Hprf'] /=".
    { iPureIntro. eexists; eauto. }
    { by iIntros "!>" (?). }
    v_pures.

    iApply "H". iModIntro. iFrame "∗ %".
    iSplit; [done|].
    by iExists _.
  Qed.

End semantic.
