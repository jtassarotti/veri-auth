From auth.prelude Require Import stdpp.
From auth.rel_logic_bin Require Export model spec_rules spec_tactics interp lib adequacy fundamental.
From auth.heap_lang Require Import gen_weakestpre typedproph.
From auth.heap_lang.lib Require Import list serialization.
From auth.examples Require Export authentikit_susp authenticatable_base_susp.
From iris.base_logic.lib Require Export invariants na_invariants.
From iris.algebra Require Import gmap agree.
  
Inductive evi_type : Type :=
| tprod (t1 t2 : evi_type)
| tsum (t1 t2 : evi_type)
| tstring
| tint
| tauth.

Definition authSet (N : namespace) : namespace := N .@ "auth".
Definition authN (N : namespace) (l : loc) : namespace := (authSet N) .@ l.

Section authenticatable.
  Context `{!heapGS_gen hlc Σ, !seqG Σ} (N : namespace).

  Definition proph_susp (p : proph_id) (h : string) : iProp Σ :=
    (typed_proph1_prop StringTypedProph) p h.
                                             
  Definition auth_is_ser_1 (v : val) (s : string) : iProp Σ :=
    ∃ (h : string), ⌜v = InjLV #h⌝ ∗ s_is_ser (g:=gwp_upto_bad) auth_scheme (SOMEV #h) s.

  Definition auth_is_ser_2 (s : string) (susp : loc) : iProp Σ :=
    ∃ (h : string), susp ↦□ InjRV #h ∗ 
      s_is_ser (g:=gwp_upto_bad) auth_scheme (SOMEV #h) s.

  Definition auth_is_ser_3 (s : string) (susp : loc) : iProp Σ :=
    ∃ (pid: nat) (p : proph_id) (h : string),
      susp ↦ InjLV (#pid, #p) ∗ proph_susp p h ∗
        s_is_ser (g:=gwp_upto_bad) auth_scheme NONEV s.

  Definition auth_is_ser_3_proph (s : string) (susp : loc) : iProp Σ :=
    ∃ (pid: nat) (p : proph_id) (h : string),
      susp ↦ InjLV (#pid, #p) ∗ proph_susp p h ∗
        s_is_ser (g:=gwp_upto_bad) auth_scheme (SOMEV #h) s.

  Definition auth_inv (s : string) (susp : loc) : iProp Σ :=
    (∃ (s1 : string), 
      ⌜s = some_ser_str (string_ser_str (hash s1))⌝ ∗ 
      hashed s1 ∗ auth_is_ser_2 s susp) ∨ 
      auth_is_ser_3_proph s susp.
  
  
  Fixpoint s_is_ser_deser (t : evi_type) (v : val) (s : string) : iProp Σ :=
    match t with
    | tprod t1 t2 => prod_is_ser' v s (s_is_ser_deser t1) (s_is_ser_deser t2)
    | tsum t1 t2 => sum_is_ser' v s (s_is_ser_deser t1) (s_is_ser_deser t2)
    | tstring => string_is_ser v s
    | tint => int_is_ser v s
    | tauth => ∃ v1, ⌜v = SOMEV v1⌝ ∗ (auth_is_ser_1 v1 s ∨ 
                                        (∃ (susp : loc), ⌜v1 = InjRV #susp⌝ ∗ auth_is_ser_3 s susp))
    end.

  Fixpoint s_is_ser'' (t : evi_type) (v : val) (s : string) : iProp Σ :=
    match t with
    | tprod t1 t2 => prod_is_ser' v s (s_is_ser'' t1) (s_is_ser'' t2)
    | tsum t1 t2 => sum_is_ser' v s (s_is_ser'' t1) (s_is_ser'' t2)
    | tstring => string_is_ser v s
    | tint => int_is_ser v s
    | tauth => ∃ v1, ⌜v = SOMEV v1⌝ ∗ (auth_is_ser_1 v1 s ∨ 
                                        (∃ (susp : loc), ⌜v1 = InjRV #susp⌝ ∗ auth_is_ser_2 s susp))
  end.

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

  #[global] Instance s_is_ser''_persistent t v s: Persistent (s_is_ser'' t v s).
  Proof. revert v s; induction t => v s; simpl; apply _. Qed.

  #[global] Instance : Inhabited evi_type.
  Proof. constructor. apply tstring. Qed.

                                               
  Definition ser_spec_3 (ser : val) (t : evi_type) : iProp Σ :=
    ∀ (v1 : val) (s : string) E,
      ⌜↑authSet N ⊆ E⌝ -∗
      {{{ ▷ (s_is_ser_proph t v1 s ∗ seq_tok E) }}}
        ser v1
      {{{ o, RET $o; seq_tok E ∗ ((⌜o = Some #s⌝ ∗ s_is_ser'' t v1 s) ∨ ⌜o = None⌝) }}}.
        
  Definition ser_spec_un (A : lrel_un Σ) (ser : val) (t : evi_type) : iProp Σ :=
    ∀ (v : val) E,
      ⌜↑authSet N ⊆ E⌝ -∗
      {{{ ▷ (A v ∗ seq_tok E) }}}
        ser v
      {{{ o, RET $o; seq_tok E ∗ if o is Some s then s_is_ser'' t v s else True }}}.
  
  Definition ser_spec (A : lrel Σ) (ser : val) (t : evi_type) : iProp Σ :=
    ∀ (v1 v2 : val) E,
      ⌜↑authSet N ⊆ E⌝ -∗
      {{{ ▷ (A v1 v2 ∗ seq_tok E) }}}
        ser v1
      {{{ o, RET $o; seq_tok E ∗ if o is Some s then s_is_ser'' t v1 s else True }}}.

  Definition deser_spec (A : lrel_un Σ) (deser : val) (t : evi_type) : iProp Σ :=
    ∀ (pid : nat),
      {{{ True }}}
      deser #pid
      {{{ (deser_partial : val), RET deser_partial;
          ∀ (s : string),
            {{{ True }}}
              deser_partial #s
              {{{ o, RET $o;
                  if o is Some v then
                    s_is_ser_deser t v s ∗ 
                      (∀ E, s_is_ser_deser t v s ={E}=∗ A v ∗ (∃ s', s_is_ser_proph t v s'))
                  else True }}}
      }}}.
  
  Definition count_spec (count : val) (t : evi_type) : iProp Σ :=
    ∀ (x : val) (s : string) (E : coPset),
      ⌜↑authSet N ⊆ E⌝ →
      {{{ (s_is_ser_proph t x s ∗ seq_tok E) }}}
        count x
      {{{ (c : nat), RET #c; s_is_ser_proph t x s ∗ seq_tok E }}}.

  Definition val_eq_rel (A : lrel Σ) : iProp Σ :=
    ∀ (E : coPset) (v1 v2 b1 : val) (s : string) (t1 t2 : evi_type),
      ⌜↑authSet N ⊆ E⌝ →
      □ (seq_tok E -∗ (s_is_ser'' t1 v1 s ∨ s_is_ser_proph t1 v1 s) -∗ 
          s_is_ser'' t2 v2 s -∗ A v2 b1 ={⊤}=∗ 
            seq_tok E ∗ A v1 b1).


  Definition lrel_un_evidence' (A : lrel_un Σ) : lrel_un Σ :=
    LRelUn (λ v,
        ∃ (t : evi_type) (ser deser count : val),
          ⌜v = (ser, deser, count)%V⌝ ∗ ser_spec_un A ser t ∗ ser_spec_3 ser t ∗
            count_spec count t ∗ deser_spec A deser t)%I.
  
  Definition lrel_bin_evidence' (A : lrel_bi Σ) : lrel Σ :=
    LRel (λ v1 v2, val_eq_rel A)%I.

  Definition lrel_bi_evidence' (A : lrel_bi Σ) : lrel_bi Σ :=
    LRelBi (lrel_un_evidence' (lrel_bi_un A))
      (lrel_bin_evidence' A).

  Program Definition lrel_evidence : kindO Σ (⋆ ⇒ ⋆)%kind := λne A, lrel_bi_evidence' A.
  Next Obligation.
    intros ????.
    rewrite /lrel_bi_evidence' /=.
    split; [intros ?|intros ??];
      rewrite /lrel_car/= /lrel_un_car/= /ser_spec_un /ser_spec /count_spec /deser_spec /val_eq_rel;
      solve_proper.
  Qed.

  Lemma prod_ser'_spec_ser (HA HB : val → iProp Σ) (tA tB : evi_type) (serA serB v vA vB : val) :
    ∀ E,
    (▷ ⌜v = (vA, vB)%V⌝) -∗
    ({{{ ▷ (HA vA ∗ seq_tok E) }}}
       serA vA
       {{{ o, RET $o; seq_tok E ∗ if o is Some s then s_is_ser'' tA vA s else True }}}) -∗
    ({{{ ▷ (HB vB ∗ seq_tok E) }}}
       serB vB
       {{{ o, RET $o; seq_tok E ∗ if o is Some s then s_is_ser'' tB vB s else True }}}) -∗
    {{{ ▷ (prod_valid_val' v HA HB ∗ seq_tok E) }}}
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
  
End authenticatable.

Section proof.
  Context `{!authG Σ, !seqG Σ} (N : namespace).

  Lemma refines_un_Auth_pair Θ (Δ : ctxO Σ Θ) (A B : kindO Σ ⋆) serA serB deserA deserB countA countB :
    lrel_bi_un (lrel_evidence N A) (serA, deserA, countA)%V -∗
    lrel_bi_un (lrel_evidence N B) (serB, deserB, countB)%V -∗
    lrel_bi_un (⟦ var2 (var1 * var0)%ty ⟧ (ext (ext (ext Δ (lrel_evidence N)) A) B))
      (prod_ser''' serA serB, λ: "pid", prod_deser (deserA "pid") (deserB "pid"), λ: "v", countA (Fst "v") + countB (Snd "v"))%V.
  Proof.
    iIntros "HA HB".
    rewrite /prod_ser''' /prod_deser.
    iDestruct "HA" as (tA_un serA_un deserA_un countA_un ?) "(#HserA_un & #Hser3A_un & #HcountA_un & #HdeserA_un)".
    iDestruct "HB" as (tB_un serB_un deserB_un countB_un ?) "(#HserB_un & #Hser3B_un & #HcountB_un & #HdeserB_un)".
    interp_unfold!.
    iExists (tprod tA_un tB_un), _, _, _. simplify_eq.
    iSplit; [done|]. clear. iSplit; [|iSplit; [|iSplit]].
    + iIntros (v ???) "!# (Hp & Htok) H". rewrite interp_un_prod_unfold.
      iDestruct "Hp" as (w u) "(>-> & #HA & #HB)".
      rewrite interp_tvar_unfold. iSimpl in "HA".
      rewrite interp_tvar_unfold. iSimpl in "HB".
      iSimpl in "H".
      wp_apply (prod_ser'_spec_ser (λ v, lrel_bi_un A v) (λ v, lrel_bi_un B v) with "[] [] [] [$Htok]") => /=; [done| | | |done].
      { iIntros (?) "!# Hp H". by wp_apply ("HserA_un" with "[//] Hp"). }
      { iIntros (?) "!# Hp H". by wp_apply ("HserB_un" with "[//] Hp"). }
      iExists _, _. iModIntro.
      eauto.
    + iIntros (v ????) "!# (Hser & Htok) H".
      iDestruct "Hser" as (????) "((>-> & >->) & HA & HB)".
      wp_pures.
      wp_apply ("Hser3A_un" with "[//] [$HA $Htok]").
      iIntros (oa) "(Htok & [[% HserA]|%])"; simplify_eq.
      - wp_pures.
        wp_apply ("Hser3B_un" with "[//] [$HB $Htok]").
        iIntros (ob) "(Htok & [[% HserB]|%])"; simplify_eq.
        * wp_pures. iApply ("H" $! (Some _)). iModIntro. iFrame. iLeft.
          iSplit; [done|]. iExists v1, v2, s1, s2. iSplit; [done|]. iFrame.
        * wp_pures. iApply ("H" $! None). iFrame. iRight. done.
      - wp_pures. iApply ("H" $! None). iFrame. iRight. done.
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
      iDestruct "H" as (????[??]) "[[HserA HA][HserB HB]]".
      simplify_eq. iFrame. iSplit; eauto. iIntros (?).
      rewrite interp_un_prod_unfold. interp_unfold!. 
      iIntros "(%&%&%&%&[%%]& HserA & HserB)". simplify_eq.
      iMod ("HA" with "HserA") as "[HA [% HserpA]]".
      iMod ("HB" with "HserB") as "[HB [% HserpB]]".
      iFrame. eauto.
  Qed.

  Lemma refines_Auth_pair Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆; ⋆, var2 var1 → var2 var0 → var2 (var1 * var0) ⟧
      (ext Δ (lrel_evidence N)) v_Auth_pair i_Auth_pair.
  Proof.
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
          iDestruct "HA" as "[HrelA HA]".
          iPoseProof "HA" as (tA serA deserA countA ->) "(#HserA & #Hser3A & #HcountA & #HdeserA)".
          clear. iIntros (??) "(Hi & Htok)".
          i_pures; wp_pures.
          iModIntro. iFrame.
          iSplit.
          { interp_unfold.
            iIntros (??) "!# #HB".
            interp_unfold! in "HB".
            iDestruct "HB" as "[HrelB HB]".
            iPoseProof "HB" as (tB serB deserB countB ->) "(#HserB & #Hser3B & #HcountB & #HdeserB)".
            clear. iIntros (??) "(Hi & Htok)".
            i_pures; wp_pures. clear.
            rewrite /prod_ser'' /prod_count.
            wp_pures. iFrame. iModIntro.
            iSplit.
            { interp_unfold!.
              iIntros (E v1 ? b1 s t1 t2) "%HE !# Htok Hser1 Hser2 HA'".
                interp_unfold!.
                iDestruct "HA'" as (w1 w2 u1 u2) "(-> & -> & #HA' & #HB')".
                interp_unfold! in "HA'".
                interp_unfold! in "HB'".
                destruct t2 as [t2A t2B | t2A t2B | | |]; iSimpl in "Hser2".
                all: try (iDestruct "Hser2" as %(? & Habs & ?); done).
                2: { iDestruct "Hser2" as "(%w & %s' & [(_ & [%Hv _]) | (_ & [%Hv _])])"; done. }
                2: { iDestruct "Hser2" as (?) "[%Hv _]"; done. }
                iDestruct "Hser2" as (x1 x2 s1 s2) "[%Hpq [HS21 HS22]]".
                destruct Hpq as [Hv Hs]. simplify_eq.
                iDestruct "Hser1" as "[Hser1|Hser1]"; destruct t1 as [t1A t1B | t1A t1B | | |]; iSimpl in "Hser1".
                all: try (iDestruct "Hser1" as %(? & ? & Habs); exfalso;
                          first [exact (prod_ser_string_ser_neq _ s1 s2 Habs) |
                                 exact (prod_ser_int_ser_neq _ s1 s2 Habs)]).
                2: { iDestruct "Hser1" as "(%w & %s' & [(_ & [%Hv %Habs]) | (_ & [%Hv %Habs])])".
                     - exfalso. exact (prod_ser_inl_ser_neq s' s1 s2 Habs).
                     - exfalso. exact (prod_ser_inr_ser_neq s' s1 s2 Habs). }
                4: { iDestruct "Hser1" as "(%w & %s' & [(_ & [%Hv %Habs]) | (_ & [%Hv %Habs])])".
                     - exfalso. exact (prod_ser_inl_ser_neq s' s1 s2 Habs).
                     - exfalso. exact (prod_ser_inr_ser_neq s' s1 s2 Habs). }
                2: { iDestruct "Hser1" as (v0 ?) "[Hauth | (%susp & ? & Hauth)]".
                     - iDestruct "Hauth" as (h ?) "Hser".
                       iPoseProof (auth_scheme.(s_is_ser_eq) with "Hser") as "#Hstr".
                       iDestruct "Hstr" as "[%Habs | (%s' & %Habs & _)]".
                       + exfalso. exact (prod_ser_none_ser_neq s1 s2 Habs).
                       + exfalso. exact (prod_ser_some_ser_neq _ s1 s2 Habs).
                     - iDestruct "Hauth" as (h) "[_ Hser]".
                       iPoseProof (auth_scheme.(s_is_ser_eq) with "Hser") as "#Hstr".
                       iDestruct "Hstr" as "[%Habs | (%s' & %Habs & _)]".
                       + exfalso. exact (prod_ser_none_ser_neq s1 s2 Habs).
                       + exfalso. exact (prod_ser_some_ser_neq _ s1 s2 Habs). }
                3: { iDestruct "Hser1" as (v0 ?) "[Hauth | (%susp & ? & Hinv)]".
                     - iDestruct "Hauth" as (h ?) "Hser".
                       iPoseProof (auth_scheme.(s_is_ser_eq) with "Hser") as "#Hstr".
                       iDestruct "Hstr" as "[%Habs | (%s' & %Habs & _)]".
                       + exfalso. exact (prod_ser_none_ser_neq s1 s2 Habs).
                       + exfalso. exact (prod_ser_some_ser_neq _ s1 s2 Habs).
                     - iMod (na_inv_acc with "Hinv Htok") as "(Hinv1 & Htok & Hclose)"; [solve_ndisj|solve_ndisj|].
                       iDestruct "Hinv1" as ">[(%&%& hashs & %& Hsusp & Hser)|Hser]".
                       * iPoseProof (auth_scheme.(s_is_ser_eq) with "Hser") as "#Hstr".
                         iDestruct "Hstr" as "[%Habs | (%s' & %Habs & _)]".
                         + exfalso. exact (prod_ser_none_ser_neq s1 s2 Habs).
                         + exfalso. exact (prod_ser_some_ser_neq _ s1 s2 Habs).
                       * iDestruct "Hser" as (?? h) "[_ [_ Hser]]".
                         iPoseProof (auth_scheme.(s_is_ser_eq) with "Hser") as "#Hstr".
                         iDestruct "Hstr" as "[%Habs | (%s' & %Habs & _)]".
                         + exfalso. exact (prod_ser_none_ser_neq s1 s2 Habs).
                         + exfalso. exact (prod_ser_some_ser_neq _ s1 s2 Habs). }
                * iDestruct "Hser1" as (y1 y2 s1' s2') "[%Hpq [HT1 HT2]]".
                  destruct Hpq as [Hv Hs]. apply (inj2 prod_ser_str) in Hs as [<- <-]. subst v1.
                  iPoseProof ("HrelA" with "[//] Htok [HT1] HS21 HA'") as "> (Htok & #HA'')".
                  { by iLeft. }
                  iPoseProof ("HrelB" with "[//] Htok [HT2] HS22 HB'") as "> (Htok & #HB'')".
                  { by iLeft. }
                  iModIntro. iFrame "Htok".
                  iDestruct "HA''" as "[HA'b HA'u]". iDestruct "HB''" as "[HB'b HB'u]".
                  iSplit.
                  { interp_unfold!. iFrame "∗ #". done. }
                  rewrite interp_un_prod_unfold. interp_unfold!. iFrame "∗ #". done.
                * iDestruct "Hser1" as (y1 y2 s1' s2') "[%Hpq [HT1 HT2]]".
                  destruct Hpq as [Hv Hs]. apply (inj2 prod_ser_str) in Hs as [<- <-]. subst v1.
                  iPoseProof ("HrelA" with "[//] Htok [HT1] HS21 HA'") as "> (Htok & #HA'')".
                  { by iRight. }
                  iPoseProof ("HrelB" with "[//] Htok [HT2] HS22 HB'") as "> (Htok & #HB'')".
                  { by iRight. }
                  iModIntro. iFrame "Htok".
                  iDestruct "HA''" as "[HA'b HA'u]". iDestruct "HB''" as "[HB'b HB'u]".
                  iSplit.
                  { interp_unfold!. iFrame "∗ #". done. }
                  rewrite interp_un_prod_unfold. interp_unfold!. iFrame "∗ #". done. }
            { iApply (refines_un_Auth_pair with "HA HB"). } }
          { iPoseProof "HA" as (tA_un serA_un deserA_un countA_un ?) "(#HserA_un & #Hser3A_un & #HcountA_un & #HdeserA_un)".
            rewrite interp_un_arr_unfold.
            iIntros (?) "!# #HB".
            interp_unfold! in "HB".
            iPoseProof "HB" as (tB_un serB_un deserB_un countB_un ?) "(#HserB_un & #Hser3B_un & #HcountB_un & #HdeserB_un)".
            simplify_eq. iIntros "Htok".
            wp_pures.
            rewrite /prod_ser'' /prod_count.
            wp_pures. iFrame. iModIntro.
            iApply (refines_un_Auth_pair with "HA HB"). } }
        { rewrite interp_un_arr_unfold.
          iIntros (?) "!# #HA".
          interp_unfold! in "HA".
          iPoseProof "HA" as (tA_un serA_un deserA_un countA_un ->) "(#HserA_un & #Hser3A_un & #HcountA_un & #HdeserA_un)".
          iIntros "Htok".
          wp_pures.
          iModIntro. iFrame.
          rewrite interp_un_arr_unfold.
          iIntros (?) "!# #HB".
          interp_unfold! in "HB".
          iPoseProof "HB" as (tB_un serB_un deserB_un countB_un ->) "(#HserB_un & #Hser3B_un & #HcountB_un & #HdeserB_un)".
          iIntros "Htok".
          wp_pures.
          rewrite /prod_ser'' /prod_count.
          wp_pures. iFrame. iModIntro.
          iApply (refines_un_Auth_pair with "HA HB"). } }
      { rewrite interp_un_forall_unfold.
        iIntros (B ??) "!# Htok".
        wp_pures.
        iModIntro. iFrame.
        rewrite interp_un_arr_unfold.
        iIntros (?) "!# #HA".
        interp_unfold! in "HA".
        iPoseProof "HA" as (tA_un serA_un deserA_un countA_un ->) "(#HserA_un & #Hser3A_un & #HcountA_un & #HdeserA_un)".
        iIntros "Htok".
        wp_pures.
        iModIntro. iFrame.
        rewrite interp_un_arr_unfold.
        iIntros (?) "!# #HB".
        interp_unfold! in "HB".
        iPoseProof "HB" as (tB_un serB_un deserB_un countB_un ->) "(#HserB_un & #Hser3B_un & #HcountB_un & #HdeserB_un)".
        iIntros "Htok".
        wp_pures.
        rewrite /prod_ser'' /prod_count.
        wp_pures. iFrame. iModIntro.
        iApply (refines_un_Auth_pair with "HA HB"). }
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
      iIntros (?) "!# #HA".
      interp_unfold! in "HA".
      iPoseProof "HA" as (tA_un serA_un deserA_un countA_un ->) "(#HserA_un & #Hser3A_un & #HcountA_un & #HdeserA_un)".
      iIntros "Htok".
      wp_pures.
      iModIntro. iFrame.
      rewrite interp_un_arr_unfold.
      iIntros (?) "!# #HB".
      interp_unfold! in "HB".
      iPoseProof "HB" as (tB_un serB_un deserB_un countB_un ->) "(#HserB_un & #Hser3B_un & #HcountB_un & #HdeserB_un)".
      iIntros "Htok".
      wp_pures.
      rewrite /prod_ser'' /prod_count.
      wp_pures. iFrame. iModIntro.
      iApply (refines_un_Auth_pair with "HA HB").
  Qed.
      
  Lemma refines_Auth_sum Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆; ⋆, var2 var1 → var2 var0 → var2 (var1 + var0) ⟧
      (ext Δ (lrel_evidence N)) v_Auth_sum i_Auth_sum.
  Proof. Admitted.

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
    iDestruct "H_un" as "(%t_un & %ser_un & %deser_un & %count_un & % & #Hser_un & #Hser3_un & #Hcount_un & #Hdeser_un)".
    simplify_eq.
    iExists t_un, _, _, _. iSplit; first done.
    clear. iSplit; [|iSplit; [|iSplit]].
    - iIntros (v ?? Ψ) "!# (#Hs & Htok) HΨ".
      wp_pures.
      rewrite interp_rec_star_un_unfold.
      rewrite interp_unseal /=.
      wp_apply ("Hser_un" with "[//] [$Htok]"); [by iFrame|done].
    - iIntros (v1 ??? Ψ) "!# (Hs & Htok) HΨ".
      wp_pures.
      by wp_apply ("Hser3_un" with "[//] [$Hs $Htok]").
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
      iFrame. iIntros (?).
      rewrite interp_rec_star_un_unfold.
      rewrite interp_unseal /=.
      iIntros "Hser".
      by iMod ("HA" with "Hser") as "[$ $]".
  Qed.

  Lemma refines_Auth_mu Θ (Δ : ctxO Σ Θ) :
    ⊢ ⟦ ∀: ⋆ ⇒ ⋆, var1 (var0 (μ: ⋆; var1 var0)) → var1 (μ: ⋆; var1 var0) ⟧
      (ext Δ (lrel_evidence N)) v_Auth_mu i_Auth_mu.
  Proof.
    rewrite /lrel_car /lrel_un_car/=. iSplit; interp_unfold !.
    - iIntros (A v1 v2) "!# _". iIntros (??) "(Hi & Htok)".
      rewrite /i_Auth_mu /v_Auth_mu.
      i_pures. wp_pures.
      iFrame. iModIntro. clear.
      iSplit; interp_unfold!.
      + iIntros (??) "!# #H".
        iIntros (??) "(Hi & Htok)".
        interp_unfold! in "H".
        iDestruct "H" as "[Hrel H]".
        iPoseProof "H" as "(%t & %ser & %deser & %count & -> & H')".
        i_pures. wp_pures.
        iFrame. iModIntro.
        iSplit; interp_unfold!.
        * iIntros (????????) "!# Htok Hser Hser' #Hmu". 
          rewrite interp_rec_star_unfold.
          rewrite interp_unseal /=.
          admit.
        * iApply (refines_un_Auth_mu with "H").
      + rewrite interp_un_arr_unfold.
        iIntros (?) "!# #H Htok".
        interp_unfold! in "H".
        simplify_eq. wp_pures.
        iPoseProof "H" as "(%t_un & %ser_un & %deser_un & %count_un & % & #Hser_un & #Hser3_un & #Hcount_un & #Hdeser_un)".
        simplify_eq. wp_pures.
        iFrame. iModIntro.
        interp_unfold!.
        iApply (refines_un_Auth_mu with "H").
    - rewrite interp_un_forall_unfold.
      iIntros (A v) "!# _ Htok".
      rewrite /v_Auth_mu.
      wp_pures.
      iFrame. iModIntro. clear.
      rewrite interp_un_arr_unfold.
      iIntros (?) "!# #H Htok".
      interp_unfold! in "H".
      iPoseProof "H" as "(%t_un & %ser_un & %deser_un & %count_un & % & #Hser_un & #Hser3_un & #Hcount_un & #Hdeser_un)".
      simplify_eq. wp_pures.
      iFrame. iModIntro.
      interp_unfold!.
      iApply (refines_un_Auth_mu with "H").
  Admitted.
  

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

  Definition lrel_bin_auth' (A : lrel_bi Σ) : lrel Σ :=
    LRel (λ a1 v2, (∃ v1, ⌜a1 = SOMEV v1⌝ ∗ auth_some A v1 v2) ∨ ⌜a1 = NONEV⌝)%I.

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
    iSplit; [done|]. clear. iSplit; [|iSplit]; [| |iSplit].
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
        Print auth_inv.
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
        iModIntro. iFrame "#". simplify_eq.
        iSplitL. 
        { iExists _. iSplit; [done|].
          iRight. iFrame. eauto. }
        iIntros (?) "Hser".
        iDestruct "Hser" as (??) "[(%&%& Hser)|(%&%&%&%&%& Hsusp & Hproph & Hser)]"; simplify_eq.
        iMod (na_inv_alloc seqG_name E (authN N susp0) (auth_inv _ susp0)
          with "[Hser Hsusp Hproph]") as "#Hinv".
        { iNext. iRight. iFrame. iRight. do 2 iExists _. eauto. }
        iModIntro. iFrame "#". iSplit; [iLeft|]; eauto.
      * iModIntro. iApply ("H" $! (Some _)). simplify_eq.
        iSplitL.
        { iExists _. iSplit; [done|].
          iLeft. rewrite /auth_is_ser_1.
          iExists _. iSplit; [done|].
          iRight. iExists _, _. eauto. }
        iIntros (?) "Hser".
        iDestruct "Hser" as (??) "[(%&%& Hser)|(%&%&%&%&%& Hsusp & Hproph & Hser)]"; simplify_eq.
        iModIntro. iSplit; [iLeft|]; iExists _; try iSplit; try done.
        { iLeft. eauto. }
        iExists _. iSplit; first done. iLeft.
        iExists _. eauto.
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
      { iIntros (????????) "!# Htok Hser1 Hser2 #[HAb HAu]".
        destruct t1 as [| | | |]. 1,2,3,4 : admit.
        destruct t2 as [| | | |]. 1,2,3,4 : admit.
        iDestruct "Hser1" as "[Hser1|Hser1]".
        - iDestruct "Hser1" as (??) "[(%&%&#Hser1)|(%&%&(%&#Hsusp2&#Hser1))]";
            iDestruct "Hser2" as (??) "[(%&%&#Hser2)|(%&%&(%&#Hsusp1&#Hser2))]";
            iDestruct "HAb" as "[(%&%& HAb)|%]"; simplify_eq;
            iDestruct "HAb" as "(%&%&%& #hashs1 & #Hser & #HAb & [%|(%&%&%&%& #Hinv)])";
            simplify_eq.
          + assert (h = hash s1) as ->; first admit.
            iFrame. iModIntro.
            iSplit; iLeft; iExists _; iSplit; try done; 
              iFrame "#"; iLeft; eauto.
          + iMod (na_inv_acc with "Hinv Htok") as "(Hinv' & Htok & Hclose)"; [solve_ndisj|solve_ndisj|].
            iDestruct "Hinv'" as ">[(%& %Heq & #hashs2 & %& #Hsusp & #Hser')|(%& %& %& Hsusp & Hproph & #Hser')]";
              last first.
            { iExFalso. iDestruct (pointsto_agree with "Hsusp Hsusp1") as %Hcontra. simplify_eq. }
            iDestruct (pointsto_agree with "Hsusp Hsusp1") as %Heq'. simplify_eq.
            iPoseProof (hashes_auth.hashed_s_equal s1 s0 with "[] hashs1 hashs2") as "->";
              try by simplify_eq.
            iAssert (⌜h0 = h⌝)%I as %->.
            { iDestruct "Hser1" as %H1. iDestruct "Hser2" as %H2. iPureIntro. naive_solver. }
            iMod ("Hclose" with "[$Htok]") as "$".
            { iNext. iLeft. iExists s0. iSplit; [done|]. iFrame "#". }
            iModIntro. iSplit.
            * iLeft. iExists (InjLV #h). iSplit; [done|].
              iExists a1, t, s0. iFrame "#". iLeft.
              iDestruct "Hser'" as %HSer'. iPureIntro.
              destruct! HSer'; try discriminate. by simplify_eq.
            * iLeft. iExists (InjLV #h). iSplit; [done|]. iLeft. eauto.
          + assert (h = hash s1) as ?; first admit.
            iMod (na_inv_alloc seqG_name _ (authN N susp) (auth_inv (some_ser_str (string_ser_str h)) susp) with "[Hser1 Hsusp2]") as "#Hinv".
            { iModIntro. iLeft. iFrame "# ∗". admit. }
            iFrame. iModIntro.
            iSplit; iLeft; iExists _; iSplit; try done; try iRight;
              iExists _; iFrame "#"; try done; iRight. by subst.
          + iMod (na_inv_acc with "Hinv Htok") as "(Hinv' & Htok & Hclose)"; [solve_ndisj|solve_ndisj|].
            iDestruct "Hinv'" as ">[(%&%& #hashs2 & %& #Hsusp & #Hser')|(%& %& %& Hsusp & Hproph & #Hser')]";
              last first; iDestruct (pointsto_agree with "Hsusp Hsusp1") as %Heq'; try done.
            iPoseProof (hashes_auth.hashed_s_equal s1 s0 with "[] hashs1 hashs2") as "%";
              simplify_eq; try done.
            assert (h = h0) as ?; first admit. simplify_eq.
            assert (h0 = hash s0) as ?; first admit. simplify_eq.
            iMod ("Hclose" with "[$Htok]") as "$".
            { iNext. iLeft. by iFrame "#". }
            iMod (na_inv_alloc seqG_name _ (authN N susp) (auth_inv (some_ser_str (string_ser_str (hash s0))) susp) with "[Hser1 Hsusp2]") as "#Hinv'".
            { iModIntro. iLeft. by iFrame "# ∗". }
            iModIntro. iSplit; iLeft; iExists _; iSplit; try done;
              try iRight; iFrame "#"; eauto.
        - iDestruct "Hser1" as (??) "[(%&%&#Hser1)|(%&%&#Hinv)]";
            iDestruct "Hser2" as (??) "[(%&%&#Hser2)|(%&%&(%&#Hsusp1&#Hser2))]";
            simplify_eq.
          + assert (h = h0) as ->; first admit.
            by iFrame "# ∗".
          + iAssert (⌜h = h0⌝)%I as %->.
            { iDestruct "Hser1" as %H1. iDestruct "Hser2" as %H2. iPureIntro. naive_solver. }
            iDestruct "HAb" as "[(%w & % & auth_ab)|%]"; simplify_eq.
            iDestruct "auth_ab" as "(%ab & %tb & %sb & #hashsb & #Hser_ab & #HA_rel & [% | (%& %& % & % & #Hinv_ab)])"; simplify_eq.
            iMod (na_inv_acc with "Hinv_ab Htok") as "(Hinv1 & Htok & Hclose)"; [solve_ndisj|solve_ndisj|].
            iDestruct "Hinv1" as ">[(%s1' & % & #hashss1 & (% & #Hsusp' & #Hser')) | (%& %& %& Hsusp' & _ & _)]"; last first.
            { iExFalso. iDestruct (pointsto_agree with "Hsusp' Hsusp1") as %?. done. }
            iDestruct (pointsto_agree with "Hsusp' Hsusp1") as %Heqh. simplify_eq.
            iMod ("Hclose" with "[$Htok]") as "Htok".
            { iNext. iLeft. iExists s1'. iSplit; [iPureIntro; congruence|]. iSplit; [iFrame "#"|].
              iExists h0. iFrame "#". }
            iModIntro. iFrame "Htok".
            iSplit.
            * iAssert (⌜h0 = hash sb⌝)%I as %->.
              { iDestruct "Hser'" as %H'. iPureIntro. naive_solver. }
              iLeft. iExists (InjLV #(hash sb)). iSplit; [done|].
              iExists ab, tb, sb. iFrame "#". iLeft. done.
            * iLeft. iExists (InjLV #h0). iSplit; [done|]. iLeft. iExists h0. done.
          + iFrame "# ∗".
            iModIntro. iSplit; iLeft; iExists _; iSplit; try eauto.
            iDestruct "HAb" as "[(%&%& (%&%&%& #hashs & #Hser & #HA & HAb))|%]"; simplify_eq.
            iFrame "#". iRight. admit.
          + iDestruct "HAb" as "[(%&%& (%&%&%& #hashs1 & #Hser & #HA & [%|(%&%&%&%& #Hinv')]))|%]"; simplify_eq.
            iFrame "Hser #".
            iMod (na_inv_acc with "Hinv' Htok") as "(Hinv1 & Htok & Hclose)"; [solve_ndisj|solve_ndisj|].
            iDestruct "Hinv1" as ">[(%&%& #hashs2 & %& #Hsusp & #Hser')|(%& %& %& Hsusp & Hproph & #Hser')]";
              simplify_eq.
            * assert (h = h0) as ->; first admit.
              assert (s1 = s0) as ->; first admit.
              assert (s = some_ser_str (string_ser_str (hash s0))) as ->; first admit.
              iMod ("Hclose" with "[$Htok]") as "$".
              { iNext. iLeft. iFrame "#". by iFrame "#". }
              iModIntro. iSplit; iLeft; iExists _; iSplit; try done; [|iRight; eauto].
              eauto.
            * iPoseProof (pointsto_agree with "Hsusp1 Hsusp") as "%". done. }
      { iApply refines_un_Auth_auth. } }
    { rewrite interp_un_forall_unfold.
      iIntros (A ?) "!# _ Htok"; rewrite -!/interp.
      rewrite /v_Auth_auth.
      wp_pures.
      iModIntro. iFrame.
      rewrite /auth_ctx. interp_unfold!.
      iApply refines_un_Auth_auth. }
  Admitted.

  Lemma refines_un_auth_auth Θ (Δ : ctxO Σ Θ) (R : kindO Σ (⋆ ⇒ ⋆) ) (A : kindO Σ ⋆) :
    ∀ tA ser deser count,
    ser_spec_un N (lrel_bi_un A) ser tA -∗
    ser_spec_3 N ser tA -∗
    count_spec N deser tA -∗
    deser_spec N (lrel_bi_un A) count tA -∗
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
        iDestruct "HeviA" as "[Hrel HeviA_un]".
        iDestruct "HeviA_un" as (tA ser count deser ->) "(#Hser & #Hser3 & #Hcount & #Hdeser)".
        iIntros (??) "(Hi & Htok)".
        i_pures; wp_pures.
        iFrame. iModIntro. iSplit; interp_unfold!.
        * iIntros (w1 w2) "!# #HA'". clear.
          iIntros (??) "(Hi & Htok)".
          i_pures; wp_pures. iPoseProof "HA'" as "[HA HA_un]".
          wp_apply ("Hser" with "[] [$Htok]"); [done|done|].
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

