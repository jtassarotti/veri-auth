From auth.prelude Require Import stdpp.
From auth.rel_logic_bin_susp Require Export model interp spec_tactics.
From auth.heap_lang Require Import typedproph.
From auth.heap_lang.lib Require Import list serialization_susp.
From auth.examples Require Export authentikit_susp authenticatable_base_susp.
From iris.base_logic.lib Require Export na_invariants fancy_updates.
From iris.algebra Require Import gmap.

Definition authSet (N : namespace) : namespace := N .@ "auth".
Definition authN (N : namespace) (l : loc) : namespace := (authSet N) .@ l.

(* This file defines lrel_evidence and lrel_auth.
  lrel_evidence holds tells us what we get from the ser/deser/count functions.
  lrel_auth tells what the auth type looks like. 
  
  For the suspended security proof, we need separate binary and unary logical relations,
  for reasons which become more clear in the authentikit_susp_security.v file.
  So, we essentially need to define and prove unary versions of lrel_evidence and lrel_auth.
  To give a brief intuition here, the verifier doesn't immediately know that the proof it has
  received is bad until possibly much later (finish may be called much later). The unary
  branch denotes the case where we decide that the computation has to return None.

  This proof also makes heavy use of non-atomic invariants. For this proof it is very reasonable
  to assume that there is no concurrency.
*)

Section authenticatable.
  Context `{!authG Σ, !seqG Σ} (N : namespace).
  
  Inductive evi_type : Type :=
  | tprod (t1 t2 : evi_type)
  | tsum (t1 t2 : evi_type)
  | tstring
  | tint
  | tauth.

  #[global] Instance : Inhabited evi_type.
  Proof. constructor. apply tstring. Qed.

  Definition proph_susp (p : proph_id) (h : string) : iProp Σ :=
    (typed_proph1_prop StringTypedProph) p h.
                
  (* When the auth value is initialized with a hash. *)
  Definition auth_is_ser_1 (v : val) (s : string) : iProp Σ :=
    ∃ (h : string), ⌜v = InjLV #h⌝ ∗ s_is_ser (g:=gwp_upto_bad) auth_scheme (SOMEV #h) s.

  (* When the auth value is initialized with a suspension, and filled-in later. *)
  Definition auth_is_ser_2 (s : string) (susp : loc) : iProp Σ :=
    ∃ (h : string), susp ↦□ InjRV #h ∗ 
      s_is_ser (g:=gwp_upto_bad) auth_scheme (SOMEV #h) s.

  (* When the auth value is initialized with a suspension, and not yet filled.
    We prophesize what the value will be filled to. *)
  Definition auth_is_ser_3 (s : string) (susp : loc) : iProp Σ :=
    ∃ (pid: nat) (p : proph_id) (h : string),
      susp ↦ InjLV (#pid, #p) ∗ proph_susp p h ∗
        s_is_ser (g:=gwp_upto_bad) auth_scheme (SOMEV #h) s.

  (* The invariant for the suspension case. Note that we fix the string, i.e.,
    we make sure that the string that is eventually filled-in is the one we
    use to resolve the prophecy. Note that this string is actually the hash of
    some string. *)
  Definition auth_inv (s : string) (susp : loc) : iProp Σ :=
    (∃ (s1 : string), 
      ⌜s = some_ser_str (string_ser_str (hash s1))⌝ ∗ 
      hashed s1 ∗ auth_is_ser_2 s susp) ∨ 
      auth_is_ser_3 s susp.

  (* Recursive serialization relation. This doesn't include the prophecy case for auth. *)
  Fixpoint s_is_ser'' (t : evi_type) (v : val) (s : string) : iProp Σ :=
    match t with
    | tprod t1 t2 => prod_is_ser' v s (s_is_ser'' t1) (s_is_ser'' t2)
    | tsum t1 t2 => sum_is_ser' v s (s_is_ser'' t1) (s_is_ser'' t2)
    | tstring => string_is_ser v s
    | tint => int_is_ser v s
    | tauth => ∃ v1, ⌜v = SOMEV v1⌝ ∗ (auth_is_ser_1 v1 s ∨ 
                                        (∃ (susp : loc), ⌜v1 = InjRV #susp⌝ ∗ auth_is_ser_2 s susp))
  end.

  #[global] Instance s_is_ser''_persistent t v s: Persistent (s_is_ser'' t v s).
  Proof. revert v s; induction t => v s; simpl; apply _. Qed.

  (* This tells what the value will serialize to, or prophesizes what the value serializes to. *)
  Fixpoint s_is_ser_proph (t : evi_type) (v : val) (s : string) : iProp Σ :=
    match t with
    | tprod t1 t2 => prod_is_ser' v s (s_is_ser_proph t1) (s_is_ser_proph t2)
    | tsum t1 t2 => sum_is_ser' v s (s_is_ser_proph t1) (s_is_ser_proph t2)
    | tstring => string_is_ser v s
    | tint => int_is_ser v s
    | tauth => ∃ v1, ⌜v = SOMEV v1⌝ ∗
                       (auth_is_ser_1 v1 s ∨
                          (∃ (susp : loc), ⌜v1 = InjRV #susp⌝ ∗
                            seq_inv (authN N susp) (auth_inv s susp)))
  end.

  #[global] Instance s_is_ser_proph_persistent t v s : Persistent (s_is_ser_proph t v s).
  Proof. revert v s. induction t => v s; simpl; apply _. Qed.
                    
  (* If this returns some string, it must not include the prophecy case.
    Here, it was easier to use the serialization relation for the value.
    This essentially serves the same purpose as the logical relation as in previous cases. *)
  Definition ser_spec (ser : val) (t : evi_type) : iProp Σ :=
    ∀ (v1 : val) (s : string) E,
      ⌜↑authSet N ⊆ E⌝ -∗
      {{{ s_is_ser_proph t v1 s ∗ seq_tok E }}}
        ser v1
      {{{ o, RET $o; seq_tok E ∗ 
          ((⌜o = Some #s⌝ ∗ s_is_ser'' t v1 s) ∨ ⌜o = None⌝) }}}.
        
  (* We use this definition for the auth function, and the one above for all other uses. *)
  Definition ser_spec_un (A : lrel_un Σ) (ser : val) (t : evi_type) : iProp Σ :=
    ∀ (v : val) E,
      ⌜↑authSet N ⊆ E⌝ -∗
      {{{ ▷ (A v) ∗ seq_tok E }}}
        ser v
      {{{ o, RET $o; seq_tok E ∗ 
          if o is Some s then s_is_ser'' t v s else True }}}.

  (* Note in the post-condition that we get that deserialization returns a valid value
    for the unary logical relation A. Further, we also prophesize what the value will
    serialize to, if there were any suspensions. Note that the spec ignores what the
    input string was. 
    Also, the deserialization function now first passes a #pid to all sub-deserialization
    routines. We then use the returned partial deserialization function. *)
  Definition deser_spec_un (A : lrel_un Σ) (deser : val) (t : evi_type) : iProp Σ :=
    ∀ (pid : nat),
      {{{ True }}}
      deser #pid
      {{{ (deser_partial : val), RET deser_partial;
          ∀ (s : string),
            {{{ True }}}
              deser_partial #s
              {{{ o, RET $o;
                  if o is Some v then
                    A v ∗ (∃ s', s_is_ser_proph t v s')
                  else True }}}
      }}}.

  (* This does the same as above, and then some. Probably the most crucial specification
    in the proof.
    In the precondition, it takes in what verifier-value the logical relation holds for, 
    and what it serializes to. We then say that if for the deserialized object, the
    prophesized string is the same as the input-serialization string, we will get the
    logical relation for the deserialized value also.
    
    In earlier proofs, to derive the same kind of relations, we usually made some arguments
    that if s' = s'', vᵥ = v. However, that may no longer be the case because
    auth_is_ser_1 vᵥ s' and auth_is_ser_2 v s'' may both hold for different kinds of values. *)
  Definition deser_spec_bin (A : lrel_bi Σ) (deser : val) (t : evi_type) : iProp Σ :=
    ∀ (pid : nat),
      {{{ True }}}
      deser #pid
      {{{ (deser_partial : val), RET deser_partial;
          ∀ (s s' : string) vᵥ vᵢ t1,
            {{{ ▷ A vᵥ vᵢ ∗ s_is_ser'' t1 vᵥ s' }}}
              deser_partial #s
              {{{ o, RET $o;
                  if o is Some v then
                    ∃ s'', s_is_ser_proph t v s'' ∗ (lrel_bi_un A) v ∗ 
                      (∀ E, ⌜↑authSet N ⊆ E⌝ -∗ ⌜s' = s''⌝ -∗ seq_tok E
                        ={⊤}=∗ seq_tok E ∗ (lrel_bi_bin A) v vᵢ)
                  else True }}}
      }}}.
  
  (* For the security proof, we don't care what the count_spec returns. *)
  Definition count_spec (count : val) (t : evi_type) : iProp Σ :=
    ∀ (x : val) (s : string) (E : coPset),
      ⌜↑authSet N ⊆ E⌝ →
      {{{ (s_is_ser_proph t x s ∗ seq_tok E) }}}
        count x
      {{{ (c : nat), RET #c; s_is_ser_proph t x s ∗ seq_tok E }}}.


  Definition lrel_un_evidence' (A : lrel_un Σ) : lrel_un Σ :=
    LRelUn (λ v,
      ∃ (t : evi_type) (ser deser count : val),
        ⌜v = (ser, deser, count)%V⌝ ∗ ser_spec ser t ∗ ser_spec_un A ser t ∗
          count_spec count t ∗ deser_spec_un A deser t)%I.
  
  Definition lrel_bin_evidence' (A : lrel_bi Σ) : lrel Σ :=
    LRel (λ v1 v2, 
      ∃ (t : evi_type) (ser deser count : val),
          ⌜v1 = (ser, deser, count)%V⌝ ∗ ser_spec ser t ∗
            count_spec count t ∗ deser_spec_bin A deser t)%I.

  Definition lrel_bi_evidence' (A : lrel_bi Σ) : lrel_bi Σ :=
    LRelBi (lrel_un_evidence' (lrel_bi_un A))
      (lrel_bin_evidence' A).

  Program Definition lrel_evidence : kindO Σ (⋆ ⇒ ⋆)%kind := λne A, lrel_bi_evidence' A.
  Next Obligation.
    intros ????.
    rewrite /lrel_bi_evidence' /=.
    split; [intros ?|intros ??];
      rewrite /lrel_car/= /lrel_un_car/= /ser_spec /ser_spec_un /count_spec /deser_spec_un /deser_spec_bin;
      solve_proper.
  Qed.

  (* Have to define these again because of the different serialization relation, and the
    seq_tok's. *)
  Lemma prod_ser'_spec_ser (HA HB : val → iProp Σ) (tA tB : evi_type) (serA serB v vA vB : val) :
    ∀ E,
    (▷ ⌜v = (vA, vB)%V⌝) -∗
    ({{{ ▷ HA vA ∗ seq_tok E }}}
       serA vA
       {{{ o, RET $o; seq_tok E ∗ if o is Some s then s_is_ser'' tA vA s else True }}}) -∗
    ({{{ ▷ HB vB ∗ seq_tok E }}}
       serB vB
       {{{ o, RET $o; seq_tok E ∗ if o is Some s then s_is_ser'' tB vB s else True }}}) -∗
    {{{ ▷ prod_valid_val' v HA HB ∗ seq_tok E }}}
    prod_ser''' serA serB v
    {{{ o, RET $o; seq_tok E ∗ if o is Some s then prod_is_ser' v s (s_is_ser'' tA) (s_is_ser'' tB) else True }}}.
  Proof.
    iIntros (?) "#Hv #HA #HB % !# (Hp & Htok) HΦ".
    rewrite /prod_ser''' /prod_is_ser.
    wp_pures.
    iDestruct "Hp" as (???) "[H1 H2]". iSimplifyEq.
    wp_pures.
    wp_apply ("HA" with "[$H1 $Htok]").
    iIntros ([]); last first.
    { iIntros "(Htok & _)". wp_pures. iApply ("HΦ" $! None). by iFrame. }
    iIntros "(Htok & HserA)".
    wp_pures.
    wp_apply ("HB" with "[$H2 $Htok]").
    iIntros ([]); last first.
    { iIntros "(Htok & _)". wp_pures. iApply ("HΦ" $! None). by iFrame. }
    iIntros "(Hotk & HserB)".
    wp_pures.
    iApply ("HΦ" $! (Some _)).
    iModIntro. iFrame. eauto.
  Qed.

  Lemma sum_ser'_spec_ser (HA HB : val → iProp Σ) (tA tB : evi_type) (serA serB v : val) :
    ∀ E,
    (∀ v', {{{ ▷ HA v' ∗ seq_tok E }}}
       serA v'
       {{{ o, RET $o; seq_tok E ∗ if o is Some s then s_is_ser'' tA v' s else True }}}) -∗
    (∀ v', {{{ ▷ HB v' ∗ seq_tok E }}}
       serB v'
       {{{ o, RET $o; seq_tok E ∗ if o is Some s then s_is_ser'' tB v' s else True }}}) -∗
    {{{ ▷ sum_valid_val' v HA HB ∗ seq_tok E }}}
    sum_ser''' serA serB v
    {{{ o, RET $o; seq_tok E ∗ if o is Some s then sum_is_ser' v s (s_is_ser'' tA) (s_is_ser'' tB) else True }}}.
  Proof.
    iIntros (?) "#HA #HB % !# (Hp & Htok) HΦ".
    rewrite /sum_ser'''.
    wp_pures.
    iDestruct "Hp" as (w) "[[-> Hw]|[-> Hw]]"; wp_pures.
    - wp_apply ("HA" with "[$Hw $Htok]").
      iIntros ([sA|]) "(Htok & HserA)"; wp_pures; last first.
      { iApply ("HΦ" $! None). by iFrame. }
      iApply ("HΦ" $! (Some _)). iFrame. iModIntro.
      iExists w, sA. iLeft. by iFrame.
    - wp_apply ("HB" with "[$Hw $Htok]").
      iIntros ([sB|]) "(Htok & HserB)"; wp_pures; last first.
      { iApply ("HΦ" $! None). by iFrame. }
      iApply ("HΦ" $! (Some _)). iFrame. iModIntro.
      iExists w, sB. iRight. by iFrame.
  Qed.

End authenticatable.

Section proof.
  Context `{!authG Σ, !seqG Σ} (N : namespace).

  (* These specs are very ugly right now. Ideally, it would have been nice to have something like
    lrel_bi_un (lrel_evidence N A) (serA, deserA, countA)%V -∗
    lrel_bi_un (lrel_evidence N B) (serB, deserB, countB)%V -∗
    lrel_bi_un (⟦ var2 (var1 * var0)%ty ⟧ (ext (ext (ext Δ (lrel_evidence N)) A) B))
      v_Auth_pair.
      
    But I had to step through some of v_Auth_pair in refines_Auth_pair to make this work.
    This seems to be the minimum spec that I could reuse across all cases.
  *)
  Lemma refines_un_Auth_pair Θ (Δ : ctxO Σ Θ) (A B : kindO Σ ⋆) serA serB deserA deserB countA countB :
    lrel_bi_un (lrel_evidence N A) (serA, deserA, countA)%V -∗
    lrel_bi_un (lrel_evidence N B) (serB, deserB, countB)%V -∗
    lrel_bi_un (⟦ var2 (var1 * var0)%ty ⟧ (ext (ext (ext Δ (lrel_evidence N)) A) B))
      (prod_ser''' serA serB, λ: "pid", prod_deser (deserA "pid") (deserB "pid"), λ: "v", countA (Fst "v") + countB (Snd "v"))%V.
  Proof.
    iIntros "HA HB".
    rewrite /prod_ser''' /prod_deser.
    iDestruct "HA" as (tA_un serA_un deserA_un countA_un ?) "(#HserprA_un & #HserA_un & #HcountA_un & #HdeserA_un)".
    iDestruct "HB" as (tB_un serB_un deserB_un countB_un ?) "(#HserprB_un & #HserB_un & #HcountB_un & #HdeserB_un)".
    interp_unfold!.
    iExists (tprod tA_un tB_un), _, _, _. simplify_eq.
    iSplit; [done|]. clear. iSplit; [|iSplit; [|iSplit]].
    + iIntros (v ????) "!# (Hser & Htok) H".
      iDestruct "Hser" as (????) "((-> & ->) & Hsera & Hserb)".
      wp_pures.
      wp_apply ("HserprA_un" with "[//] [$Hsera $Htok]").
      iIntros (oa) "(Htok & [[% Hsera]|%])"; simplify_eq.
      - wp_pures.
        wp_apply ("HserprB_un" with "[//] [$Hserb $Htok]").
        iIntros (ob) "(Htok & [[% Hserb]|%])"; simplify_eq.
        * wp_pures. iApply ("H" $! (Some _)). iModIntro. iFrame. iLeft.
          iSplit; [done|]. iExists v1, v2, s1, s2. iSplit; [done|]. iFrame.
        * wp_pures. iApply ("H" $! None). iFrame. iRight. done.
      - wp_pures. iApply ("H" $! None). iFrame. iRight. done.
    + iIntros (v ???) "!# (Hp & Htok) H". rewrite interp_un_prod_unfold.
      iDestruct "Hp" as (w u) "(>-> & #Ha & #Hb)".
      rewrite interp_tvar_unfold. iSimpl in "Ha".
      rewrite interp_tvar_unfold. iSimpl in "Hb".
      iSimpl in "H".
      wp_apply (prod_ser'_spec_ser (λ v, lrel_bi_un A v) (λ v, lrel_bi_un B v) with "[] [] [] [$Htok]") => /=; [done| | | |done].
      { iIntros (?) "!# Hp H". by wp_apply ("HserA_un" with "[//] Hp"). }
      { iIntros (?) "!# Hp H". by wp_apply ("HserB_un" with "[//] Hp"). }
      iExists _, _. iModIntro.
      eauto.
    + iIntros (?????) "!# (Hser & Htok) HΨ".  wp_pures.
      iDestruct "Hser" as (????) "((-> & ->) & HA & HB)".
      wp_pures. rewrite /count_spec.
      wp_bind (countB_un _).
      wp_apply ("HcountB_un" $! v2 with "[//] [$HB $Htok]").
      iIntros (?) "[HB Htok]".
      wp_pures.
      wp_apply ("HcountA_un" $! v1 with "[//] [$HA $Htok]").
      iIntros (?) "[HA Htok]".
      simplify_eq. wp_pures. iModIntro.
      iSpecialize ("HΨ" $! (c0+c)).
      assert (#(c0 + c) = #(c0 + c)%nat).
      { by rewrite Nat2Z.inj_add. }
      rewrite H0. iApply "HΨ".
      by iFrame.
    + iIntros (pid ?) "!# _ HΨ".
      wp_pures.
      wp_apply "HdeserB_un"; [done|]. iIntros "%deparB #HdeparB".
      wp_apply "HdeserA_un"; [done|]. iIntros "%deparA #HdeparA".
      wp_pures. iModIntro. iApply "HΨ".
      iIntros (s ?) "!# _ HΨ".
      wp_apply prod_deser'_sound; try auto.
      iIntros ([]) "H"; last first; iApply "HΨ"; try done.
      iDestruct "H" as (????[??]) "[[Ha Hsera][Hb Hserb]]".
      simplify_eq. iFrame. iSplit.
      * (* TODO: fix interp_unfold! so I don't have to do all these rewrites.
          Mostly a problem for the unary specs. *)
        rewrite interp_un_prod_unfold. interp_unfold!.
        do 2 iExists _. by iFrame.
      * iDestruct "Hsera" as (?) "Hsera".
        iDestruct "Hserb" as (?) "Hserb".
        iFrame. eauto.
  Qed.

  Lemma refines_Auth_pair Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆; ⋆, var2 var1 → var2 var0 → var2 (var1 * var0) ⟧
      (ext Δ (lrel_evidence N)) v_Auth_pair i_Auth_pair.
  Proof.
    (* Unfortunately for bigger type specs like above, we need to split for
      unary/binary several times.
      
      TODO: Is there a specification that allows us to say that we don't need to
      do this for certain kinds of types? 
      Or can we say that we only prove the binary specification (assuming both unary
      and binary), and only prove the unary specification (assuming only unary),
      and the combine them to get the final lemma above with minimal code-use?
      Another thing to note is that for all unary branches we create later, we don't
      use any of the binary specs. *)
    iSplit.
    - interp_unfold.
      iIntros (A ??) "!# _".
      iIntros (??) "(Hi & Htok)".
      rewrite /v_Auth_pair /i_Auth_pair.
      i_pures; wp_pures.
      iModIntro. iFrame.
      iSplit.
      { interp_unfold.
        iIntros (B ??) "!# _".
        iIntros (??) "(Hi & Htok)".
        i_pures; wp_pures.
        iModIntro. iFrame.
        iSplit.
        { interp_unfold.
          iIntros (??) "!# #HA".
          interp_unfold! in "HA".
          iDestruct "HA" as "[HA HA_un]".
          iPoseProof "HA" as (tA serA deserA countA ->) "(#HserA & #HcountA & #HdeserA)".
          clear. iIntros (??) "(Hi & Htok)".
          i_pures; wp_pures.
          iModIntro. iFrame.
          iSplit.
          { interp_unfold.
            iIntros (??) "!# #HB".
            interp_unfold! in "HB".
            iDestruct "HB" as "[HB HB_un]".
            iPoseProof "HB" as (tB serB deserB countB ->) "(#HserB & #HcountB & #HdeserB)".
            clear. iIntros (??) "(Hi & Htok)".
            i_pures; wp_pures. clear.
            rewrite /prod_ser'' /prod_count.
            wp_pures. iFrame. iModIntro.
            iSplit.
            { interp_unfold!.
              iExists (tprod tA tB), _, _, _. iSplit; try done.
              iSplit; [|iSplit].
              - iIntros (v ????) "!# (Hser & Htok) H".
                iDestruct "Hser" as (????) "((-> & ->) & Hsera & Hserb)".
                wp_pures.
                wp_apply ("HserA" with "[//] [$Hsera $Htok]").
                iIntros (oa) "(Htok & [[% Hsera]|%])"; simplify_eq.
                + wp_pures.
                  wp_apply ("HserB" with "[//] [$Hserb $Htok]").
                  iIntros (ob) "(Htok & [[% Hserb]|%])"; simplify_eq.
                  * wp_pures. iApply ("H" $! (Some _)). iModIntro. iFrame. iLeft.
                    iSplit; [done|]. by iFrame.
                  * wp_pures. iApply ("H" $! None). iFrame. iRight. done.
                + wp_pures. iApply ("H" $! None). iFrame. iRight. done.
              - iIntros (?????) "!# (Hser & Htok) HΨ".  wp_pures.
                iDestruct "Hser" as (????) "((-> & ->) & Hsera & Hserb)".
                wp_pures. rewrite /count_spec.
                wp_bind (countB _).
                wp_apply ("HcountB" $! v0 with "[//] [$Hserb $Htok]").
                iIntros (?) "[Hserb Htok]".
                wp_pures.
                wp_apply ("HcountA" $! v1 with "[//] [$Hsera $Htok]").
                iIntros (?) "[Hsera Htok]".
                simplify_eq. wp_pures. iModIntro.
                iSpecialize ("HΨ" $! (c0+c)).
                assert (#(c0 + c) = #(c0 + c)%nat).
                { by rewrite Nat2Z.inj_add. }
                rewrite H0. iApply "HΨ".
                by iFrame.
              - iIntros (pid ?) "!# _ HΨ".
                wp_pures.
                wp_apply "HdeserB"; [done|]. iIntros "%deparB #HdeparB".
                wp_apply "HdeserA"; [done|]. iIntros "%deparA #HdeparA".

                (* The following basically ended up being a copy-paste of the
                  deserialization proof from the serialization.v file since the
                  pre/post conds are very different. Don't think there is a
                  workaround here. *)
                rewrite /prod_deser. wp_pures.
                iModIntro. iApply "HΨ".
                iIntros (s s' ?? ? ?) "!# [Hr Hrser] HΨ". wp_pures.
                iDestruct "Hr" as (??????) "[#Hra #Hrb]".
                rewrite interp_var0_ext1 interp_var1_ext2.
                rewrite /option_nat_to_val.
                case_match eqn:Htag; wp_pures; [|iApply ("HΨ" $! None); by iFrame].
                case_match eqn:Hlen; wp_pures; [|iApply ("HΨ" $! None); by iFrame].
                case_bool_decide as Hs; wp_pures; [|iApply ("HΨ" $! None); by iFrame].
                case_bool_decide as Hz; wp_pures; [iApply ("HΨ" $! None); by iFrame|].
                case_bool_decide as Hl; wp_pures; [iApply ("HΨ" $! None); by iFrame|].

                simplify_eq. destruct t1.
                2: { simpl. iDestruct "Hrser" as (??) "[[_ %]|[_ %]]"; naive_solver. }
                2: { simpl. iDestruct "Hrser" as %(? & ? & ?); naive_solver. }
                2: { simpl. iDestruct "Hrser" as %(? & ? & ?); naive_solver. }
                2: { simpl. iDestruct "Hrser" as (?) "[% _]"; naive_solver. }
                
                iDestruct "Hrser" as (????[??]) "[Hrsera Hrserb]". simplify_eq.
                
                wp_apply ("HdeparA" with "[$Hra $Hrsera]").
                iIntros ([a|]) "Ha"; wp_pures; [|by iApply ("HΨ" $! None)].
                iDestruct "Ha" as "[% [Hsera [Hun_a Heqa]]]".

                wp_apply ("HdeparB" with "[$Hrb $Hrserb]").
                iIntros ([b|]) "Hb"; wp_pures; [|by iApply ("HΨ" $! None)].
                iDestruct "Hb" as "[% [Hserb [Hun_b Heqb]]]".

                iApply ("HΨ" $! (Some _)).
                iFrame. iModIntro. iExists _. iSplit; eauto.
                iSplit.
                + rewrite interp_un_prod_unfold. 
                  rewrite interp_var0_ext1 interp_var1_ext2.
                  by iFrame.
                + iIntros (???) "Htok". simplify_eq.
                  iDestruct ("Heqa" with "[//] [//] Htok") as ">[Htok Ha]".
                  iDestruct ("Heqb" with "[//] [//] Htok") as ">[Htok Hb]".
                  interp_unfold!. by iFrame. }

            { iApply (refines_un_Auth_pair with "HA_un HB_un"). } }
          { iPoseProof "HA_un" as (tA_un serA_un deserA_un countA_un ?) "(#HserA_un & #HcountA_un & #HdeserA_un)".
            rewrite interp_un_arr_unfold.
            iIntros (?) "!# #HB_un".
            interp_unfold! in "HB_un".
            iPoseProof "HB_un" as (tB_un serB_un deserB_un countB_un ?) "(#HserB_un & #HcountB_un & #HdeserB_un)".
            simplify_eq. iIntros "Htok".
            wp_pures.
            rewrite /prod_ser'' /prod_count.
            wp_pures. iFrame. iModIntro.
            iApply (refines_un_Auth_pair with "HA_un HB_un"). } }
        { rewrite interp_un_arr_unfold.
          iIntros (?) "!# #HA_un".
          interp_unfold! in "HA_un".
          iPoseProof "HA_un" as (tA_un serA_un deserA_un countA_un ->) "(#HserA_un & #HcountA_un & #HdeserA_un)".
          iIntros "Htok".
          wp_pures.
          iModIntro. iFrame.
          rewrite interp_un_arr_unfold.
          iIntros (?) "!# #HB_un".
          interp_unfold! in "HB_un".
          iPoseProof "HB_un" as (tB_un serB_un deserB_un countB_un ->) "(#HserB_un & #HcountB_un & #HdeserB_un)".
          iIntros "Htok".
          wp_pures.
          rewrite /prod_ser'' /prod_count.
          wp_pures. iFrame. iModIntro.
          iApply (refines_un_Auth_pair with "HA_un HB_un"). } }
      { rewrite interp_un_forall_unfold.
        iIntros (B ??) "!# Htok".
        wp_pures.
        iModIntro. iFrame.
        rewrite interp_un_arr_unfold.
        iIntros (?) "!# #HA_un".
        interp_unfold! in "HA_un".
        iPoseProof "HA_un" as (tA_un serA_un deserA_un countA_un ->) "(#HserA_un & #HcountA_un & #HdeserA_un)".
        iIntros "Htok".
        wp_pures.
        iModIntro. iFrame.
        rewrite interp_un_arr_unfold.
        iIntros (?) "!# #HB_un".
        interp_unfold! in "HB_un".
        iPoseProof "HB_un" as (tB_un serB_un deserB_un countB_un ->) "(#HserB_un & #HcountB_un & #HdeserB_un)".
        iIntros "Htok".
        wp_pures.
        rewrite /prod_ser'' /prod_count.
        wp_pures. iFrame. iModIntro.
        iApply (refines_un_Auth_pair with "HA_un HB_un"). }
    - rewrite interp_un_forall_unfold.
      iIntros (A ??) "!# Htok".
      rewrite /v_Auth_pair.
      wp_pures.
      iModIntro. iFrame.
      rewrite interp_un_forall_unfold.
      iIntros (B ??) "!# Htok".
      wp_pures.
      iModIntro. iFrame.
      rewrite interp_un_arr_unfold.
      iIntros (?) "!# #HA_un".
      interp_unfold! in "HA_un".
      iPoseProof "HA_un" as (tA_un serA_un deserA_un countA_un ->) "(#HserA_un & #HcountA_un & #HdeserA_un)".
      iIntros "Htok".
      wp_pures.
      iModIntro. iFrame.
      rewrite interp_un_arr_unfold.
      iIntros (?) "!# #HB_un".
      interp_unfold! in "HB_un".
      iPoseProof "HB_un" as (tB_un serB_un deserB_un countB_un ->) "(#HserB_un & #HcountB_un & #HdeserB_un)".
      iIntros "Htok".
      wp_pures.
      rewrite /prod_ser'' /prod_count.
      wp_pures. iFrame. iModIntro.
      iApply (refines_un_Auth_pair with "HA_un HB_un").
  Qed.

  Lemma refines_un_Auth_sum Θ (Δ : ctxO Σ Θ) (A B : kindO Σ ⋆) serA serB deserA deserB countA countB :
    lrel_bi_un (lrel_evidence N A) (serA, deserA, countA)%V -∗
    lrel_bi_un (lrel_evidence N B) (serB, deserB, countB)%V -∗
    lrel_bi_un (⟦ var2 (var1 + var0)%ty ⟧ (ext (ext (ext Δ (lrel_evidence N)) A) B))
      (sum_ser''' serA serB,
       λ: "pid", sum_deser (deserA "pid") (deserB "pid"),
       λ: "v", match: "v" with InjL "a" => countA "a" | InjR "b" => countB "b" end)%V.
  Proof.
    iIntros "HA HB".
    rewrite /sum_ser''' /sum_deser.
    iDestruct "HA" as (tA_un serA_un deserA_un countA_un ?) "(#HserprA_un & #HserA_un & #HcountA_un & #HdeserA_un)".
    iDestruct "HB" as (tB_un serB_un deserB_un countB_un ?) "(#HserprB_un & #HserB_un & #HcountB_un & #HdeserB_un)".
    interp_unfold!.
    iExists (tsum tA_un tB_un), _, _, _. simplify_eq.
    iSplit; [done|]. clear. iSplit; [|iSplit; [|iSplit]].
    + iIntros (v ????) "!# (Hser & Htok) H".
      iDestruct "Hser" as (w s') "[[Hsera [-> ->]]|[Hserb [-> ->]]]".
      - wp_pures.
        wp_apply ("HserprA_un" with "[//] [$Hsera $Htok]").
        iIntros (oa) "(Htok & [[% Hsera]|%])"; simplify_eq.
        * wp_pures. iApply ("H" $! (Some _)). iModIntro. iFrame. iLeft.
          iSplit; [done|]. iExists w, s'. iLeft. by iFrame.
        * wp_pures. iApply ("H" $! None). iFrame. iRight. done.
      - wp_pures.
        wp_apply ("HserprB_un" with "[//] [$Hserb $Htok]").
        iIntros (ob) "(Htok & [[% Hserb]|%])"; simplify_eq.
        * wp_pures. iApply ("H" $! (Some _)). iModIntro. iFrame. iLeft.
          iSplit; [done|]. iExists w, s'. iRight. by iFrame.
        * wp_pures. iApply ("H" $! None). iFrame. iRight. done.
    + iIntros (v ???) "!# (Hp & Htok) H". rewrite interp_un_sum_unfold.
      iDestruct "Hp" as (w) "[[>-> #Ha]|[>-> #Hb]]".
      - rewrite interp_tvar_unfold. iSimpl in "Ha".
        iSimpl in "H".
        wp_apply (sum_ser'_spec_ser (λ v, lrel_bi_un A v) (λ v, lrel_bi_un B v) with "[] [] [$Htok]") => /=; [| | |done].
        { iIntros (?) "!#". iIntros (?) "Hp H". by wp_apply ("HserA_un" with "[//] Hp"). }
        { iIntros (?) "!#". iIntros (?) "Hp H". by wp_apply ("HserB_un" with "[//] Hp"). }
        iModIntro. iExists w. iLeft. by iFrame "Ha".
      - rewrite interp_tvar_unfold. iSimpl in "Hb".
        iSimpl in "H".
        wp_apply (sum_ser'_spec_ser (λ v, lrel_bi_un A v) (λ v, lrel_bi_un B v) with "[] [] [$Htok]") => /=; [| | |done].
        { iIntros (?) "!#". iIntros (?) "Hp H". by wp_apply ("HserA_un" with "[//] Hp"). }
        { iIntros (?) "!#". iIntros (?) "Hp H". by wp_apply ("HserB_un" with "[//] Hp"). }
        iModIntro. iExists w. iRight. by iFrame "Hb".
    + iIntros (?????) "!# (Hser & Htok) HΨ". wp_pures.
      iDestruct "Hser" as (w s') "[[Hsera [-> ->]]|[Hserb [-> ->]]]".
      - wp_pures.
        wp_apply ("HcountA_un" $! w with "[//] [$Hsera $Htok]").
        iIntros (?) "[Hsera Htok]".
        iApply "HΨ". iFrame. iExists w, s'. iLeft. by iFrame.
      - wp_pures.
        wp_apply ("HcountB_un" $! w with "[//] [$Hserb $Htok]").
        iIntros (?) "[Hserb Htok]".
        iApply "HΨ". iFrame. iExists w, s'. iRight. by iFrame.
    + iIntros (pid ?) "!# _ HΨ".
      wp_pures.
      wp_apply "HdeserB_un"; [done|]. iIntros "%deparB #HdeparB".
      wp_apply "HdeserA_un"; [done|]. iIntros "%deparA #HdeparA".
      wp_pures. iModIntro. iApply "HΨ".
      iIntros (s ?) "!# _ HΨ".
      wp_apply sum_deser'_sound; try auto.
      iIntros ([]) "H"; last first; iApply "HΨ"; try done.
      iDestruct "H" as (w s'') "[[[Ha Hsera] [-> ->]]|[[Hb Hserb] [-> ->]]]".
      * iFrame. iSplit.
        -- rewrite interp_un_sum_unfold. iExists w. iLeft.
           iSplit; [done|]. rewrite interp_tvar_unfold. iSimpl. done.
        -- iDestruct "Hsera" as (?) "Hsera".
           iExists _. iExists w, _. iLeft. by iFrame.
      * iFrame. iSplit.
        -- rewrite interp_un_sum_unfold. iExists w. iRight.
           iSplit; [done|]. rewrite interp_tvar_unfold. iSimpl. done.
        -- iDestruct "Hserb" as (?) "Hserb".
           iExists _. iExists w, _. iRight. by iFrame.
  Qed.
      
  Lemma refines_Auth_sum Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆; ⋆, var2 var1 → var2 var0 → var2 (var1 + var0) ⟧
      (ext Δ (lrel_evidence N)) v_Auth_sum i_Auth_sum.
  Proof.
    iSplit.
    - interp_unfold.
      iIntros (A ??) "!# _".
      iIntros (??) "(Hi & Htok)".
      rewrite /v_Auth_sum /i_Auth_sum.
      i_pures; wp_pures.
      iModIntro. iFrame.
      iSplit.
      { interp_unfold.
        iIntros (B ??) "!# _".
        iIntros (??) "(Hi & Htok)".
        i_pures; wp_pures.
        iModIntro. iFrame.
        iSplit.
        { interp_unfold.
          iIntros (??) "!# #HA".
          interp_unfold! in "HA".
          iDestruct "HA" as "[HA HA_un]".
          iPoseProof "HA" as (tA serA deserA countA ->) "(#HserA & #HcountA & #HdeserA)".
          clear. iIntros (??) "(Hi & Htok)".
          i_pures; wp_pures.
          iModIntro. iFrame.
          iSplit.
          { interp_unfold.
            iIntros (??) "!# #HB".
            interp_unfold! in "HB".
            iDestruct "HB" as "[HB HB_un]".
            iPoseProof "HB" as (tB serB deserB countB ->) "(#HserB & #HcountB & #HdeserB)".
            clear. iIntros (??) "(Hi & Htok)".
            i_pures; wp_pures. clear.
            rewrite /sum_ser'' /sum_count.
            wp_pures. iFrame. iModIntro.
            iSplit.
            { interp_unfold!.
              iExists (tsum tA tB), _, _, _. iSplit; try done.
              iSplit; [|iSplit].
              - iIntros (v ????) "!# (Hser & Htok) H".
                iDestruct "Hser" as (w s') "[[Hsera [-> ->]]|[Hserb [-> ->]]]".
                + wp_pures.
                  wp_apply ("HserA" with "[//] [$Hsera $Htok]").
                  iIntros (oa) "(Htok & [[% Hsera]|%])"; simplify_eq.
                  * wp_pures. iApply ("H" $! (Some _)). iModIntro. iFrame. iLeft.
                    iSplit; [done|]. iExists w, s'. iLeft. by iFrame.
                  * wp_pures. iApply ("H" $! None). iFrame. iRight. done.
                + wp_pures.
                  wp_apply ("HserB" with "[//] [$Hserb $Htok]").
                  iIntros (ob) "(Htok & [[% Hserb]|%])"; simplify_eq.
                  * wp_pures. iApply ("H" $! (Some _)). iModIntro. iFrame. iLeft.
                    iSplit; [done|]. iExists w, s'. iRight. by iFrame.
                  * wp_pures. iApply ("H" $! None). iFrame. iRight. done.
              - iIntros (?????) "!# (Hser & Htok) HΨ". wp_pures.
                iDestruct "Hser" as (w s') "[[Hsera [-> ->]]|[Hserb [-> ->]]]".
                + wp_pures.
                  wp_apply ("HcountA" $! w with "[//] [$Hsera $Htok]").
                  iIntros (?) "[Hsera Htok]".
                  iApply "HΨ". iFrame. iExists w, s'. iLeft. by iFrame.
                + wp_pures.
                  wp_apply ("HcountB" $! w with "[//] [$Hserb $Htok]").
                  iIntros (?) "[Hserb Htok]".
                  iApply "HΨ". iFrame. iExists w, s'. iRight. by iFrame.
              - iIntros (pid ?) "!# _ HΨ".
                wp_pures.
                wp_apply "HdeserB"; [done|]. iIntros "%deparB #HdeparB".
                wp_apply "HdeserA"; [done|]. iIntros "%deparA #HdeparA".
                rewrite /sum_deser. wp_pures.
                iModIntro. iApply "HΨ".
                iIntros (s s' ?? ? ?) "!# [Hr Hrser] HΨ". wp_pures.
                iDestruct "Hr" as (rv1 rv2) "[(-> & -> & #Hra)|(-> & -> & #Hrb)]".
                + destruct t1.
                  1: { simpl. iDestruct "Hrser" as (????[? Heq]) "_"; naive_solver. }
                  2: { simpl. iDestruct "Hrser" as %(? & ? & ?); naive_solver. }
                  2: { simpl. iDestruct "Hrser" as %(? & ? & ?); naive_solver. }
                  2: { simpl. iDestruct "Hrser" as (?) "[% _]"; naive_solver. }
                  iDestruct "Hrser" as (w s'') "[[Hrsera [%Hv %Hs]]|[Hrserb [%Hv %Hs]]]"; simplify_eq.
                  Admitted.
                  (* 2: { exfalso. by apply (inl_ser_inr_ser_neq _ _ Hs). }
                  wp_apply sum_deser'_sound; try auto.
                  iIntros ([v|]) "H"; last first; [iApply ("HΨ" $! None); by iFrame|].
                  iDestruct "H" as (w0 s0) "[[[Hw0 Heq0] [%Hv0 %Hs0]]|[[Hw0 Heq0] [%Hv0 %Hs0]]]"; simplify_eq.
                  2: { exfalso. by apply (inl_ser_inr_ser_neq _ _ Hs0). }
                  assert (s0 = s'') as -> by (by apply (inj inl_ser_str)).
                  wp_pures.
                  wp_apply ("HdeparA" with "[$Hra $Hrsera]").
                  iIntros ([a|]) "Ha"; wp_pures; [|by iApply ("HΨ" $! None)].
                  iDestruct "Ha" as "[% [Hsera [Hun_a Heqa]]]".
                  iApply ("HΨ" $! (Some _)).
                  iFrame. iModIntro. iExists _. iSplit; eauto.
                  iSplit.
                  * rewrite interp_un_sum_unfold. iExists _. iLeft. iSplit; [done|].
                    rewrite interp_var0_ext1 interp_var1_ext2. done.
                  * iIntros (???) "Htok". simplify_eq.
                    iDestruct ("Heqa" with "[//] [//] Htok") as ">[Htok Ha]".
                    interp_unfold!. iFrame. iExists _, _. iLeft. by iFrame.
                + destruct t1.
                  1: { simpl. iDestruct "Hrser" as (????[? Heq]) "_"; naive_solver. }
                  2: { simpl. iDestruct "Hrser" as %(? & ? & ?); naive_solver. }
                  2: { simpl. iDestruct "Hrser" as %(? & ? & ?); naive_solver. }
                  2: { simpl. iDestruct "Hrser" as (?) "[% _]"; naive_solver. }
                  iDestruct "Hrser" as (w s'') "[[Hrsera [%Hv %Hs]]|[Hrserb [%Hv %Hs]]]"; simplify_eq.
                  1: { exfalso. by apply (inl_ser_inr_ser_neq _ _ (eq_sym Hs)). }
                  wp_apply sum_deser'_sound; try auto.
                  iIntros ([v|]) "H"; last first; [iApply ("HΨ" $! None); by iFrame|].
                  iDestruct "H" as (w0 s0) "[[[Hw0 Heq0] [%Hv0 %Hs0]]|[[Hw0 Heq0] [%Hv0 %Hs0]]]"; simplify_eq.
                  1: { exfalso. by apply (inl_ser_inr_ser_neq _ _ (eq_sym Hs0)). }
                  assert (s0 = s'') as -> by (by apply (inj inr_ser_str)).
                  wp_pures.
                  wp_apply ("HdeparB" with "[$Hrb $Hrserb]").
                  iIntros ([b|]) "Hb"; wp_pures; [|by iApply ("HΨ" $! None)].
                  iDestruct "Hb" as "[% [Hserb [Hun_b Heqb]]]".
                  iApply ("HΨ" $! (Some _)).
                  iFrame. iModIntro. iExists _. iSplit; eauto.
                  iSplit.
                  * rewrite interp_un_sum_unfold. iExists _. iRight. iSplit; [done|].
                    rewrite interp_var0_ext1 interp_var1_ext2. done.
                  * iIntros (???) "Htok". simplify_eq.
                    iDestruct ("Heqb" with "[//] [//] Htok") as ">[Htok Hb]".
                    interp_unfold!. iFrame. iExists _, _. iRight. by iFrame. }
            
            { iApply (refines_un_Auth_sum with "HA_un HB_un"). } }
          { iPoseProof "HA_un" as (tA_un serA_un deserA_un countA_un ?) "(#HserA_un & #HcountA_un & #HdeserA_un)".
            rewrite interp_un_arr_unfold.
            iIntros (?) "!# #HB_un".
            interp_unfold! in "HB_un".
            iPoseProof "HB_un" as (tB_un serB_un deserB_un countB_un ?) "(#HserB_un & #HcountB_un & #HdeserB_un)".
            simplify_eq. iIntros "Htok".
            wp_pures.
            rewrite /sum_ser'' /sum_count.
            wp_pures. iFrame. iModIntro.
            iApply (refines_un_Auth_sum with "HA_un HB_un"). } }
        { rewrite interp_un_arr_unfold.
          iIntros (?) "!# #HA_un".
          interp_unfold! in "HA_un".
          iPoseProof "HA_un" as (tA_un serA_un deserA_un countA_un ->) "(#HserA_un & #HcountA_un & #HdeserA_un)".
          iIntros "Htok".
          wp_pures.
          iModIntro. iFrame.
          rewrite interp_un_arr_unfold.
          iIntros (?) "!# #HB_un".
          interp_unfold! in "HB_un".
          iPoseProof "HB_un" as (tB_un serB_un deserB_un countB_un ->) "(#HserB_un & #HcountB_un & #HdeserB_un)".
          iIntros "Htok".
          wp_pures.
          rewrite /sum_ser'' /sum_count.
          wp_pures. iFrame. iModIntro.
          iApply (refines_un_Auth_sum with "HA_un HB_un"). } }
      { rewrite interp_un_forall_unfold.
        iIntros (B ??) "!# Htok".
        wp_pures.
        iModIntro. iFrame.
        rewrite interp_un_arr_unfold.
        iIntros (?) "!# #HA_un".
        interp_unfold! in "HA_un".
        iPoseProof "HA_un" as (tA_un serA_un deserA_un countA_un ->) "(#HserA_un & #HcountA_un & #HdeserA_un)".
        iIntros "Htok".
        wp_pures.
        iModIntro. iFrame.
        rewrite interp_un_arr_unfold.
        iIntros (?) "!# #HB_un".
        interp_unfold! in "HB_un".
        iPoseProof "HB_un" as (tB_un serB_un deserB_un countB_un ->) "(#HserB_un & #HcountB_un & #HdeserB_un)".
        iIntros "Htok".
        wp_pures.
        rewrite /sum_ser'' /sum_count.
        wp_pures. iFrame. iModIntro.
        iApply (refines_un_Auth_sum with "HA_un HB_un"). }
    - rewrite interp_un_forall_unfold.
      iIntros (A ??) "!# Htok".
      rewrite /v_Auth_sum.
      wp_pures.
      iModIntro. iFrame.
      rewrite interp_un_forall_unfold.
      iIntros (B ??) "!# Htok".
      wp_pures.
      iModIntro. iFrame.
      rewrite interp_un_arr_unfold.
      iIntros (?) "!# #HA_un".
      interp_unfold! in "HA_un".
      iPoseProof "HA_un" as (tA_un serA_un deserA_un countA_un ->) "(#HserA_un & #HcountA_un & #HdeserA_un)".
      iIntros "Htok".
      wp_pures.
      iModIntro. iFrame.
      rewrite interp_un_arr_unfold.
      iIntros (?) "!# #HB_un".
      interp_unfold! in "HB_un".
      iPoseProof "HB_un" as (tB_un serB_un deserB_un countB_un ->) "(#HserB_un & #HcountB_un & #HdeserB_un)".
      iIntros "Htok".
      wp_pures.
      rewrite /sum_ser'' /sum_count.
      wp_pures. iFrame. iModIntro.
      iApply (refines_un_Auth_sum with "HA_un HB_un").
  Qed. *)

  Lemma refines_Auth_string :
    ⊢ (lrel_evidence N) (LRelBi lrel_un_string lrel_string) v_Auth_string i_Auth_string.
  Proof. Admitted.

  Lemma refines_Auth_int :
    ⊢ (lrel_evidence N) (LRelBi lrel_un_int lrel_int) v_Auth_int i_Auth_int.
  Proof. Admitted.

  Lemma refines_un_Auth_mu Θ (Δ : ctxO Σ Θ) (A : kindO Σ (⋆ ⇒ ⋆)) ser deser count :
    lrel_bi_un (lrel_evidence N (A (⟦ μ: ⋆; var1 var0 ⟧ (ext (ext Δ (lrel_evidence N)) A)))) (ser, deser, count)%V -∗
    lrel_bi_un (lrel_evidence N (⟦ μ: ⋆; var1 var0 ⟧ (ext (ext Δ (lrel_evidence N)) A)))
      (λ: "x", ser "x", λ: "pid" "x", deser "pid" "x", λ: "x", count "x")%V.
  Proof.
    iIntros "H_un".
    iDestruct "H_un" as "(%t_un & %ser_un & %deser_un & %count_un & % & #Hserpr_un & #Hser_un & #Hcount_un & #Hdeser_un)".
    simplify_eq.
    iExists t_un, _, _, _. iSplit; first done.
    clear. iSplit; [|iSplit; [|iSplit]].
    - iIntros (v1 ??? Ψ) "!# (Hs & Htok) HΨ".
      wp_pures. by wp_apply ("Hserpr_un" with "[//] [$Hs $Htok]").
    - iIntros (v ?? Ψ) "!# (#Hs & Htok) HΨ".
      wp_pures.
      rewrite interp_rec_star_un_unfold.
      rewrite interp_unseal /=.
      wp_apply ("Hser_un" with "[//] [$Htok]"); [by iFrame|done].
    - iIntros (?????) "!# Hp HΨ". wp_pures.
      by iApply ("Hcount_un" with "[//] Hp").
    - iIntros (pid Ψ) "!# _ HΨ". wp_pures.
      iApply "HΨ". iModIntro.
      iIntros (s ?) "!# _ HΨ". wp_pures.
      wp_apply "Hdeser_un"; [done|].
      iIntros (depar) "HΨ1".
      iApply "HΨ1"; [done|].
      iModIntro.
      iIntros ([]) "H"; last first.
      { by iApply "HΨ". }
      iApply "HΨ".
      iDestruct "H" as "[Hser HA]".
      iFrame.
      rewrite interp_rec_star_un_unfold.
      rewrite interp_unseal /=. iFrame.
  Qed.

  Lemma refines_Auth_mu Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆ ⇒ ⋆, var1 (var0 (μ: ⋆; var1 var0)) → var1 (μ: ⋆; var1 var0) ⟧
      (ext Δ (lrel_evidence N)) v_Auth_mu i_Auth_mu.
  Proof.
    rewrite /lrel_car /lrel_un_car/=. iSplit; interp_unfold !.
    { iIntros (A v1 v2) "!# _". iIntros (??) "(Hi & Htok)".
      rewrite /i_Auth_mu /v_Auth_mu.
      i_pures. wp_pures.
      iFrame. iModIntro. clear.
      interp_unfold!.
      iSplit; interp_unfold!.
      { iIntros (??) "!# #HA".
        iIntros (??) "(Hi & Htok)".
        interp_unfold! in "HA".
        iDestruct "HA" as "[HA HA_un]".
        iPoseProof "HA" as (tA serA deserA countA ->) "(#HserA & #HcountA & #HdeserA)".
        i_pures. wp_pures.
        iFrame. iModIntro.
        iSplit; interp_unfold!.
        { iExists tA, _, _, _.
          iSplit; try done.
          iSplit; [|iSplit].
          - iIntros (v1 ??? Ψ) "!# (Hs & Htok) HΨ".
            wp_pures. by wp_apply ("HserA" with "[//] [$Hs $Htok]").
          - iIntros (?????) "!# Hp HΨ". wp_pures.
            by iApply ("HcountA" with "[//] Hp").
          - iIntros (pid Ψ) "!# _ HΨ". wp_pures.
            iApply "HΨ". iModIntro.
            iIntros (s s' ?? ? ?) "!# [#Hr #Hrser] HΨ". wp_pures.
            rewrite interp_rec_star_unfold.
            wp_apply "HdeserA"; [done|].
            iIntros (depar) "HΨ1".
            iApply ("HΨ1" with "[Hr $Hrser]").
            { rewrite interp_unseal //. }
            iNext. iIntros ([]) "Ha"; last first.
            { by iApply "HΨ". }
            iApply "HΨ".
            iDestruct "Ha" as "[% [Hsera [Hun_a Heqa]]]".
            iFrame.
            iSplit. 
            { rewrite interp_rec_star_un_unfold.
              rewrite interp_unseal /=. done. }
            iIntros (?? ->) "Htok".
            rewrite interp_rec_star_bin_unfold.
            rewrite interp_unseal /=.
            by iMod ("Heqa" with "[//] [//] Htok") as "[$ $]". }

        { iApply (refines_un_Auth_mu with "HA_un"). }}
      { rewrite interp_un_arr_unfold.
        iIntros (?) "!# #H Htok".
        interp_unfold! in "H".
        simplify_eq. wp_pures.
        iPoseProof "H" as "(%t_un & %ser_un & %deser_un & %count_un & % & #Hser_un & #Hcount_un & #Hdeser_un)".
        simplify_eq. wp_pures.
        iFrame. iModIntro.
        interp_unfold!.
        iApply (refines_un_Auth_mu with "H"). }}
    { rewrite interp_un_forall_unfold.
      iIntros (A v) "!# _ Htok".
      rewrite /v_Auth_mu.
      wp_pures.
      iFrame. iModIntro. clear.
      rewrite interp_un_arr_unfold.
      iIntros (?) "!# #H Htok".
      interp_unfold! in "H".
      iPoseProof "H" as "(%t_un & %ser_un & %deser_un & %count_un & % & #Hser_un & #Hcount_un & #Hdeser_un)".
      simplify_eq. wp_pures.
      iFrame. iModIntro.
      interp_unfold!.
      iApply (refines_un_Auth_mu with "H"). }
  Qed.
  

  Definition auth_some (A : lrel_bi Σ) (v1 v2 : val) : iProp Σ :=
    (∃ (a1 : val) (t : evi_type) (s1 : string),
        hashed s1 ∗ s_is_ser'' t a1 s1 ∗ A a1 v2 ∗
          ((⌜v1 = InjLV #(hash s1)⌝) ∨
             (∃ (s : string) (susp : loc),
                ⌜v1 = InjRV #susp⌝ ∗
                ⌜s = some_ser_str (string_ser_str (hash s1))⌝ ∗
                seq_inv (authN N susp)
                  (auth_inv s susp)))).

  #[global] Instance auth_some_persistent A v1 v2 : Persistent (auth_some A v1 v2).
  Proof. unfold auth_some. apply _. Qed.

  Definition lrel_auth_some (A : lrel_bi Σ) : lrel Σ :=
    LRel (λ v1 v2, auth_some A v1 v2)%I.

  (* The auth function can technically return None for malformed strings.
    So we could have either changed the spec of auth, or done this. Changing the
    spec was probably smarter. *)
  Definition lrel_bin_auth' (A : lrel_bi Σ) : lrel Σ :=
    LRel (λ a1 v2, (∃ v1, ⌜a1 = SOMEV v1⌝ ∗ auth_some A v1 v2) ∨ ⌜a1 = NONEV⌝)%I.

  (* We don't care about the ideal value here. Only that we don't get stuck anywhere. *)
  Definition auth_some_un (A : lrel_un Σ) (v1 : val) : iProp Σ :=
    ((∃ (s1 : string), ⌜v1 = InjLV #s1⌝) ∨
      (∃ (s : string) (susp : loc),
        ⌜v1 = InjRV #susp⌝ ∗ 
        seq_inv (authN N susp)
          (auth_inv s susp))).
  
  #[global] Instance auth_some_un_persistent A v1 : Persistent (auth_some_un A v1).
  Proof. unfold auth_some_un. apply _. Qed.

  Definition lrel_un_auth_some (A : lrel_un Σ) : lrel_un Σ :=
    LRelUn (λ v, auth_some_un A v)%I.

  Definition lrel_un_auth' (A : lrel_un Σ) : lrel_un Σ :=
    LRelUn (λ a, (∃ v, ⌜a = SOMEV v⌝ ∗ auth_some_un A v) ∨ ⌜a = NONEV⌝)%I.

  Definition lrel_auth' (A : lrel_bi Σ) : lrel_bi Σ :=
    LRelBi (lrel_un_auth' (lrel_bi_un A)) (lrel_bin_auth' A).
  
  Program Definition lrel_auth : kindO Σ (⋆ ⇒ ⋆)%kind := λne A, lrel_auth' A.
  Next Obligation.
    intros ????.
    rewrite /lrel_auth' /=.
    split; [intros ?|intros ??];
      rewrite /lrel_car/= /lrel_un_car/= /auth_some_un /auth_some; solve_proper.
  Qed.

  Definition auth_ctx {Θ} (Δ : ctxO Σ Θ) (R : kindO Σ (⋆ ⇒ ⋆)) :=
    ext (ext (ext Δ lrel_auth) R) (lrel_evidence N).

  Lemma refines_un_Auth_auth (A : kindO Σ ⋆) :
    ⊢ lrel_bi_un (lrel_evidence N (lrel_auth A))
        (auth_ser_v, auth_deser_v, auth_count)%V.
  Proof.
    iExists tauth, _, _, _.
    iSplit; [done|]. clear. iSplit; [|iSplit; [|iSplit]].
    - iIntros (?????) "!# (Hser & Htok) HΦ".
      rewrite /auth_ser_v. wp_pure. iSimpl in "Hser".
      iDestruct "Hser" as (?->) "[(% & -> & Hser)|(% & ->& Hser)]".
      + wp_pures. wp_apply s_ser_spec'.
        { iRight. eauto. }
        iIntros (o) "#Ho". destruct o; last first.
        { iApply ("HΦ"  $! None). iFrame. by iRight. }
        iApply ("HΦ" $! (Some _)). iFrame.
        iPoseProof (s_is_ser_inj with "Hser Ho") as "->".
        iLeft. iSplit; first done.
        simpl. iExists _. iSplit; [done|].
        iLeft. iExists _. eauto.
      + simplify_eq. wp_pures. wp_bind (!_)%E.
        iMod (na_inv_acc with "Hser Htok") as "(Hinv & Htok & Hclose)"; [solve_ndisj|solve_ndisj|].
        iDestruct "Hinv" as ">[(%&%& #hashs & %& #Hsusp & #Hser)|(%& %& %& Hsusp & Hproph & #Hser)]".
        * wp_load.
          iMod ("Hclose" with "[$Htok]") as "Htok".
          { iNext. iLeft. by iFrame "#". }
          wp_pures.
          wp_apply s_ser_spec'.
          { iRight. eauto. }
          iIntros (o) "#Ho". destruct o; last first.
          { iApply ("HΦ" $! None). iFrame. by iRight. }
          iApply ("HΦ" $! (Some _)). iFrame. iLeft.
          iPoseProof (s_is_ser_inj with "Hser Ho") as "->".
          iSplit; first done. simpl.
          iExists _. iSplit; [done|].
          iRight. iExists _. iSplit; first done.
          iExists _. eauto.
        * wp_load. wp_pures.
          iMod ("Hclose" with "[$Htok Hsusp Hproph]") as "Htok".
          { iNext. iRight. iFrame "∗ #". }
          iApply ("HΦ" $! None). iFrame. by iRight.

    - iIntros (????) "!# (#Hauth & Htok) H".
      rewrite /auth_ser_v. wp_pure.
      iDestruct "Hauth" as "[(% & -> & Hauth)|->]"; wp_pures; last first.
      { iApply ("H" $! None). by iFrame. }
      iDestruct "Hauth" as "[[%%]|(%&%&%&Hinv)]";
        simplify_eq; wp_pures.
      + wp_apply s_ser_spec'.
        { iRight. eauto. }
        iIntros (o) "#Ho". destruct o; last first.
        { iApply ("H"  $! None). by iFrame. }
        iApply ("H" $! (Some _)). iFrame.
        iExists _. iSplit; [done|].
        iLeft. iExists _. eauto.
      + wp_bind (!_)%E.
        iMod (na_inv_acc with "Hinv Htok") as "(Hinv1 & Htok & Hclose)"; [solve_ndisj|solve_ndisj|].
        iDestruct "Hinv1" as ">[(%&%& #hashs1& %& #Hsusp & #Hser1)|(%& %& %& Hsusp & Hproph & #Hser1)]".
        * wp_load.
          iMod ("Hclose" with "[Hsusp Htok Hser1]") as "Htok".
          { iFrame. iNext. iLeft. iExists _. iSplit; first done. by iFrame "∗ #". }
          wp_pures.
          wp_apply s_ser_spec'.
          { iRight. eauto. }
          iIntros (o) "#Ho". destruct o; last first.
          { iApply ("H" $! None). iFrame. }
          iApply ("H" $! (Some _)). iFrame.
          iExists _. iSplit; [done|].
          iRight. iExists _. iSplit; first done.
          iExists _. eauto.
        * wp_load.
        iMod ("Hclose" with "[Hsusp Hproph Hser1 $Htok]") as "Htok".
        { iNext. iRight. do 3 iExists _. iFrame "# ∗". }
        wp_pures.
        iApply ("H" $! None). by iFrame.
        
    - iIntros (?????) "!# (Hser & Htok) H".
      rewrite /auth_count. wp_pures.
      iDestruct "Hser" as (?->) "[(%& ->& Hser)|(%& ->& #Hinv)]"; simplify_eq; wp_pures.
      { iApply ("H" $! 0%nat). iFrame. iModIntro. iExists _. iSplit; first done.
        iLeft. iExists _. eauto. }
      iMod (na_inv_acc with "Hinv Htok") as "(Hinv' & Htok & Hclose)"; [solve_ndisj|solve_ndisj|].
      iDestruct "Hinv'" as ">[(%&%& #hashs & %& #Hsusp & #Hser)|(%& %& %& Hsusp & Hproph & #Hser)]";
        simplify_eq; wp_load; wp_pures.
      + iMod ("Hclose" with "[$Htok]") as "Htok".
        { iNext. iLeft. by iFrame "#". }
        iApply ("H" $! 0%nat). iFrame. iModIntro. iExists _.  
        iSplit; first done. iRight. iExists _. iSplit; done. 
      + iMod ("Hclose" with "[$Htok Hsusp Hproph]") as "Htok".
        { iNext. iRight. iFrame "∗ #". }
        iApply ("H" $! (1%nat)). iFrame. iModIntro. iExists _. 
        iSplit; first done. iRight. iExists _. iSplit; done.
          
    - iIntros (??) "!# _ H".
      rewrite /auth_deser_v. wp_pures.
      iModIntro. iApply "H".
      iIntros (s?) "!# _ H".
      wp_pures. wp_apply s_deser_sound; [done|].
      iIntros ([] ?); wp_pures; last (by iApply ("H" $! None)).
      destruct H as [(->&H)|(?&?&(->&H)&[?[??]])]; wp_pures.
      * wp_apply (typed_proph_wp_new_proph1 StringTypedProph); first done.
        iIntros (??) "Hproph".
        wp_alloc susp as "Hsusp".
        wp_pures. iApply ("H" $! (Some _)).
        iMod (na_inv_alloc seqG_name ⊤ (authN N susp) (auth_inv _ susp)
          with "[Hsusp Hproph]") as "#Hinv".
        { iNext. iRight. iFrame. iRight. 
          do 2 iExists _. eauto. }
        iModIntro. iFrame "#". simplify_eq.
        iSplitL; try iLeft; iExists _; iSplit; eauto.
      * iModIntro. iApply ("H" $! (Some _)). simplify_eq.
        iSplit; try iLeft; iExists _.
        { iSplit; eauto. iLeft. eauto. }
        iExists _. iSplit; eauto.
        iLeft. iExists _. iSplit; eauto.
        iRight. do 2 iExists _. eauto.
  Qed.

  Lemma refines_Auth_auth Θ (Δ : ctxO Σ Θ) R :
    ⊢ ⟦ ∀: ⋆, var1 (var3 var0) ⟧
      (auth_ctx Δ R) v_Auth_auth i_Auth_auth.
  Proof.
    iSplit; interp_unfold!.
    { iIntros (A ??) "!# _"; rewrite -!/interp.
      iIntros (??) "(Hi & Htok)".
      rewrite /v_Auth_auth /i_Auth_auth.
      i_pures; wp_pures.
      iModIntro. iFrame.
      rewrite /auth_ctx.
      iSplit; interp_unfold!.
      { iExists tauth, _, _, _.
        iSplit; [done|]. clear. iSplit; [|iSplit].
        - iIntros (?????) "!# (Hser & Htok) HΦ".
          rewrite /auth_ser_v. wp_pure. iSimpl in "Hser".
          iDestruct "Hser" as (?->) "[(% & -> & Hser)|(% & ->& Hser)]".
          + wp_pures. wp_apply s_ser_spec'.
            { iRight. eauto. }
            iIntros (o) "#Ho". destruct o; last first.
            { iApply ("HΦ"  $! None). iFrame. by iRight. }
            iApply ("HΦ" $! (Some _)). iFrame.
            iPoseProof (s_is_ser_inj with "Hser Ho") as "->".
            iLeft. iSplit; first done.
            simpl. iExists _. iSplit; [done|].
            iLeft. iExists _. eauto.
          + simplify_eq. wp_pures. wp_bind (!_)%E.
            iMod (na_inv_acc with "Hser Htok") as "(Hinv & Htok & Hclose)"; [solve_ndisj|solve_ndisj|].
            iDestruct "Hinv" as ">[(%&%& #hashs & %& #Hsusp & #Hser)|(%& %& %& Hsusp & Hproph & #Hser)]".
            * wp_load.
              iMod ("Hclose" with "[$Htok]") as "Htok".
              { iNext. iLeft. by iFrame "#". }
              wp_pures.
              wp_apply s_ser_spec'.
              { iRight. eauto. }
              iIntros (o) "#Ho". destruct o; last first.
              { iApply ("HΦ" $! None). iFrame. by iRight. }
              iApply ("HΦ" $! (Some _)). iFrame. iLeft.
              iPoseProof (s_is_ser_inj with "Hser Ho") as "->".
              iSplit; first done. simpl.
              iExists _. iSplit; [done|].
              iRight. iExists _. iSplit; first done.
              iExists _. eauto.
            * wp_load. wp_pures.
              iMod ("Hclose" with "[$Htok Hsusp Hproph]") as "Htok".
              { iNext. iRight. iFrame "∗ #". }
              iApply ("HΦ" $! None). iFrame. by iRight.

        - iIntros (?????) "!# (Hser & Htok) H".
          rewrite /auth_count. wp_pures.
          iDestruct "Hser" as (?->) "[(%& ->& Hser)|(%& ->& #Hinv)]"; simplify_eq; wp_pures.
          { iApply ("H" $! 0%nat). iFrame. iModIntro. iExists _. iSplit; first done.
            iLeft. iExists _. eauto. }
          iMod (na_inv_acc with "Hinv Htok") as "(Hinv' & Htok & Hclose)"; [solve_ndisj|solve_ndisj|].
          iDestruct "Hinv'" as ">[(%&%& #hashs & %& #Hsusp & #Hser)|(%& %& %& Hsusp & Hproph & #Hser)]";
            simplify_eq; wp_load; wp_pures.
          + iMod ("Hclose" with "[$Htok]") as "Htok".
            { iNext. iLeft. by iFrame "#". }
            iApply ("H" $! 0%nat). iFrame. iModIntro. iExists _.  
            iSplit; first done. iRight. iExists _. iSplit; done. 
          + iMod ("Hclose" with "[$Htok Hsusp Hproph]") as "Htok".
            { iNext. iRight. iFrame "∗ #". }
            iApply ("H" $! (1%nat)). iFrame. iModIntro. iExists _. 
            iSplit; first done. iRight. iExists _. iSplit; done.
              
        - (* Lot of grinding follows... *)
          iIntros (??) "!# _ H".
          rewrite /auth_deser_v. wp_pures.
          iModIntro. iApply "H".
          iIntros (s s' ?? ? ?) "!# [#Hauth #Hser] H".
          wp_pures. wp_apply s_deser_sound; [done|].

          iDestruct "Hauth" as "[Hauth _]".
          iDestruct "Hauth" as "[(%&%& Hauth)|%]"; last first.
          { destruct t1.
            { iDestruct "Hser" as (????[??]) "Hser". simplify_eq. }
            { iDestruct "Hser" as (??) "[(Hser & % & %)|(Hser & % & %)]";
              simplify_eq. destruct t1_1.
              { iDestruct "Hser" as (????[??]) "Hser". simplify_eq. }
              { iDestruct "Hser" as (??) "[(Hser & % & %)|(Hser & % & %)]";
                simplify_eq. }
              { iDestruct "Hser" as "%Hser". destruct !Hser. done. }
              { iDestruct "Hser" as "%Hser". destruct !Hser. done. }
              { iDestruct "Hser" as (??) "Hser". done. } }
            { iDestruct "Hser" as "%Hser". destruct !Hser. simplify_eq. }
            { iDestruct "Hser" as "%Hser". destruct !Hser. simplify_eq. }
            { iDestruct "Hser" as (??) "Hser". simplify_eq. } }

          iIntros ([] Hser); wp_pures; last (iApply ("H" $! None); by iFrame).
          destruct! Hser; simplify_eq; wp_pures.
          + wp_apply (typed_proph_wp_new_proph1 StringTypedProph); first done.
            iIntros (??) "Hproph".
            wp_alloc susp as "Hsusp".
            
            wp_pures. iApply ("H" $! (Some _)).
            iMod (na_inv_alloc seqG_name ⊤ (authN N susp) (auth_inv _ susp)
              with "[Hsusp Hproph]") as "#Hinv".
            { iNext. iRight. iFrame. iRight. 
              do 2 iExists _. eauto. }

            iFrame "∗ #". iModIntro. iSplit.
            { iExists _. iSplit; eauto. }
            iSplit.
            { iLeft. iExists _. iSplit; eauto. }

            iDestruct "Hauth" as "(%&%&%& #hashs1 & #Hser' & #HAb & [%|(%&%&%&%& #Hinv')])".
            * iIntros (?? ->) "$". iLeft.
              destruct t1.
              { iDestruct "Hser" as (????[??]) "Hser". simplify_eq. }
              { iDestruct "Hser" as (??) "[[Hser %Hser]|[Hser %Hser]]";
                  destruct! Hser; simplify_eq. }
              { iDestruct "Hser" as (??) "Hser". simplify_eq. }
              { iDestruct "Hser" as (??) "Hser". simplify_eq. }
              iDestruct "Hser" as (??) "[Hser|Hser]"; simplify_eq; last first.
              { iDestruct "Hser" as (??) "Hser". done. }
              iDestruct "Hser" as (??) "[[% Hser]|[% Hser]]"; simplify_eq.
              iDestruct "Hser" as (?[??]) "%Hser". destruct! Hser.
              simplify_eq. iFrame "#".
              iModIntro. eauto.
            
            * iIntros (?? <-) "Htok". simplify_eq.
              destruct t1.
              { iDestruct "Hser" as (????[??]) "Hser". done. }
              { iDestruct "Hser" as (??) "[[Hser %Hser]|[Hser %Hser]]";
                  destruct! Hser; simplify_eq.
                destruct t1_2.
                { iDestruct "Hser" as (????[??]) "Hser". simplify_eq. }
                { iDestruct "Hser" as (??) "[[Hser %Hser]|[Hser %Hser]]";
                    destruct! Hser; simplify_eq.
                  destruct t1_2_2.
                  { iDestruct "Hser" as (????[??]) "Hser". simplify_eq. }
                  { iDestruct "Hser" as (??) "[[Hser %Hser]|[Hser %Hser]]";
                      destruct! Hser; simplify_eq. }
                  { iDestruct "Hser" as (??) "Hser". simplify_eq. }
                  { iDestruct "Hser" as (??) "Hser". simplify_eq. }
                  iDestruct "Hser" as (??) "[Hser|Hser]"; simplify_eq; last first. }
                { iDestruct "Hser" as (??) "Hser". simplify_eq. }
                { iDestruct "Hser" as (??) "Hser". simplify_eq. }
                { iDestruct "Hser" as (??) "[Hser|Hser]"; simplify_eq;
                    iDestruct "Hser" as (??) "Hser"; done. } }
              { iDestruct "Hser" as (??) "Hser". done. }
              { iDestruct "Hser" as (??) "Hser". done. }
              iDestruct "Hser" as (??) "[Hser|Hser]"; simplify_eq.
              { iDestruct "Hser" as (??) "Hser". done. }
              iDestruct "Hser" as (???) "[Hsusp %Hser]". simplify_eq.
              destruct! Hser; simplify_eq.

              iMod (na_inv_acc with "Hinv' Htok") as "(Hinv'o & Htok & Hclose_inv)"; 
                try solve_ndisj.
              iDestruct "Hinv'o" as "[>(%& %& #hashs & (%& #Hsusp1 & %Hser1))|Hinv'o]";
                last first.
              { iDestruct "Hinv'o" as (???) "[>Hsusp1 Hinv'o]".
                iPoseProof (pointsto_agree with "Hsusp Hsusp1") as "%". done. }
              
              simplify_eq.
              iPoseProof (hashes_auth.hashed_s_equal with "[//] hashs1 hashs") as "->".
              iMod ("Hclose_inv" with "[$Htok]") as "Htok".
              { iNext. iLeft. by iFrame "#". }
              
              iPoseProof (pointsto_agree with "Hsusp Hsusp1") as "%". 
              destruct! Hser1; simplify_eq.
              iFrame "Hinv # ∗". iModIntro. eauto.
              
          + iApply ("H" $! (Some _)). iModIntro. iExists _.
            iSplit.
            { iExists _. iSplit; eauto.
              iLeft. iExists _. iSplit; eauto.
              iRight. do 2 iExists _. eauto. }
            iSplit.
            { iLeft. iExists _. iSplit; eauto.
              iLeft. eauto. }
            iIntros (???) "Htok".

            iDestruct "Hauth" as "(%&%&%& #hashs1 & #Hser' & #HAb & [%|(%&%&%&%& #Hinv')])";
              last first.
            * simplify_eq.
              destruct t1.
              { iDestruct "Hser" as (????[??]) "Hser". done. }
              { iDestruct "Hser" as (??) "[[Hser %Hser]|[Hser %Hser]]";
                  destruct! Hser; simplify_eq. }
              { iDestruct "Hser" as (??) "Hser". done. }
              { iDestruct "Hser" as (??) "Hser". done. }
              iDestruct "Hser" as (??) "[Hser|Hser]"; simplify_eq.
              { iDestruct "Hser" as (??) "Hser". done. }
              iDestruct "Hser" as (???) "[Hsusp %Hser]".

              iMod (na_inv_acc with "Hinv' Htok") as "(Hinv'o & Htok & Hclose_inv)"; 
                try solve_ndisj.
              iDestruct "Hinv'o" as "[>(%& %& #hashs & (%& #Hsusp1 & %Hser1))|Hinv'o]";
                last first.
              { iDestruct "Hinv'o" as (???) "[>Hsusp1 Hinv'o]". simplify_eq.
                iPoseProof (pointsto_agree with "Hsusp Hsusp1") as "%". done. }

              simplify_eq.
              iPoseProof (hashes_auth.hashed_s_equal with "[//] hashs1 hashs") as "->".
              iMod ("Hclose_inv" with "[$Htok]") as "Htok".
              { iNext. iLeft. by iFrame "#". }

              iPoseProof (pointsto_agree with "Hsusp Hsusp1") as "%". 
              destruct! Hser1; simplify_eq.
              destruct! Hser; simplify_eq.
              iFrame. iModIntro. iFrame "#".
              iLeft. eauto.
            
            * simplify_eq.
              destruct t1.
              { iDestruct "Hser" as (????[??]) "Hser". done. }
              { iDestruct "Hser" as (??) "[[Hser %Hser]|[Hser %Hser]]";
                  destruct! Hser; simplify_eq. }
              { iDestruct "Hser" as (??) "Hser". done. }
              { iDestruct "Hser" as (??) "Hser". done. }
              iDestruct "Hser" as (??) "[%Hser|Hser]"; simplify_eq; last first.
              { iDestruct "Hser" as (??) "Hser". done. }
              destruct! Hser; simplify_eq.
              iFrame "# ∗". iModIntro. iLeft. eauto. }
        
      { iApply refines_un_Auth_auth. } }
    { rewrite interp_un_forall_unfold.
      iIntros (A ?) "!# _ Htok"; rewrite -!/interp.
      rewrite /v_Auth_auth.
      wp_pures.
      iModIntro. iFrame.
      rewrite /auth_ctx. interp_unfold!.
      iApply refines_un_Auth_auth. }
  Qed.

  Lemma refines_un_auth_auth Θ (Δ : ctxO Σ Θ) (R : kindO Σ (⋆ ⇒ ⋆) ) (A : kindO Σ ⋆) :
    ∀ tA ser deser count,
    ser_spec_un N (lrel_bi_un A) ser tA -∗
    ser_spec N ser tA -∗
    count_spec N deser tA -∗
    deser_spec_un N (lrel_bi_un A) count tA -∗
    lrel_bi_un (⟦ var0 → var3 var0 ⟧ (ext (ext (ext (ext Δ lrel_auth) R) (lrel_evidence N)) A))
      (λ: "a",
      let: "serialize" := (ser, count, deser)%V in
      let: "deserialize" := Snd (Fst "serialize") in
      let: "count" := Snd "serialize" in
      let: "serialize" := Fst (Fst "serialize") in
      match: "serialize" "a" with InjL <> => InjLV #() | InjR "sera" => InjR (InjL (Hash "sera")) end)%V.
  Proof.
    iIntros (????) "#Hser #Hser2 #Hcount #Hdeser".
    rewrite interp_un_arr_unfold. simplify_eq.
    iIntros (w1) "!# #HA Htok". clear.
    wp_pures. rewrite interp_tvar_unfold.
    wp_apply ("Hser" with "[] [$Htok]"); [done|done|].
    iIntros ([]) "(Htok & Hs)"; wp_pures; last first.
    { iFrame. interp_unfold!. iModIntro. by iRight. }
    wp_apply (wp_hash with "[$]"). iIntros "#Hh1".
    wp_pures. iFrame. interp_unfold!.
    iModIntro. iLeft; iExists _; iSplit; first done.
    iLeft. eauto.
  Qed.

  Lemma refines_auth_auth Θ (Δ : ctxO Σ Θ) R :
    ⊢ ⟦ ∀: ⋆, var1 var0 → var0 → var3 var0 ⟧
      (auth_ctx Δ R) v_auth i_auth.
  Proof.
    iSplit; interp_unfold!.
    - iIntros (???) "!# _"; rewrite -/interp.
      iIntros (??) "(Hi & Htok)".
      rewrite /v_auth  /i_auth.
      i_pures; wp_pures.
      iModIntro. iFrame. clear.
      iSplit; interp_unfold!.
      + iIntros (??) "!# #HeviA".
        rewrite /auth_ctx.
        interp_unfold! in "HeviA".
        iDestruct "HeviA" as "[HeviA HeviA_un]".
        iDestruct "HeviA_un" as (tA ser count deser ->) "(#Hser & #Hser3 & #Hcount & #Hdeser)".
        iIntros (??) "(Hi & Htok)".
        i_pures; wp_pures.
        iFrame. iModIntro. iSplit; interp_unfold!.
        * iIntros (w1 w2) "!# #HA'". clear.
          iIntros (??) "(Hi & Htok)".
          i_pures; wp_pures. iPoseProof "HA'" as "[HA HA_un]".
          wp_apply ("Hser3" with "[] [$Htok]"); try done.
          iIntros ([]) "(Htok & Hs)"; wp_pures; last first.
          { iFrame. interp_unfold!. iModIntro. 
            iSplit; by iRight. }
          wp_apply (wp_hash with "[$]"). iIntros "#Hh1".
          wp_pures.
          iFrame.
          interp_unfold!. iModIntro. iSplit; iLeft; iExists _; iSplit; try done;
            [|iLeft]; repeat (iExists _); iFrame "# ∗ %"; eauto.
        * iApply refines_un_auth_auth; done.
      + rewrite interp_un_arr_unfold.
        iIntros (?) "!# #HeviA Htok".
        rewrite /auth_ctx.
        interp_unfold! in "HeviA".
        iDestruct "HeviA" as (tA_un ser_un count_un deser_un ->) 
          "(#Hser_un & #Hser3_un & #Hcount_un & #Hdeser_un)".
        wp_pures. iModIntro. iFrame.
        iApply refines_un_auth_auth; done.        
    - rewrite interp_un_forall_unfold.
      iIntros (??) "!# _ Htok"; rewrite -/interp.
      rewrite /v_auth. wp_pures.
      iModIntro. iFrame. clear.
      rewrite interp_un_arr_unfold.
      iIntros (?) "!# #HeviA Htok".
      rewrite /auth_ctx.
      interp_unfold! in "HeviA".
      iDestruct "HeviA" as (tA_un ser_un count_un deser_un ->) 
        "(#Hser_un & #Hser3_un & #Hcount_un & #Hdeser_un)".
      wp_pures. iModIntro. iFrame.
      iApply refines_un_auth_auth; done.
  Qed.

End proof.

