From Coq Require Import Ascii.
From iris.base_logic.lib Require Import fancy_updates.
From auth.prelude Require Import strings.
From auth.heap_lang Require Export lang notation.
From auth.heap_lang Require Export gen_weakestpre.
From auth.heap_lang.lib Require Export inject.

Record serialization := Serialization {
  s_valid_val `{invGS_gen hlc Σ} `{g : !GenWp Σ} : val → iProp Σ;
  s_serializer : val;
  s_is_ser `{invGS_gen hlc Σ} `{g : !GenWp Σ} : val → string → iProp Σ;

  s_valid_val_Persistent `{invGS_gen hlc Σ} `{g : !GenWp Σ} v ::
    Persistent (s_valid_val (g := g) v);
  s_is_ser_Persisten `{invGS_gen hlc Σ} `{g : !GenWp Σ} v s ::
    Persistent (s_is_ser (g := g) v s);
  s_is_ser_inj `{invGS_gen hlc Σ} `{g : !GenWp Σ} v s1 s2 :
    s_is_ser (g := g) v s1 -∗ s_is_ser (g := g) v s2 -∗ ⌜s1 = s2⌝;
  s_is_ser_valid `{invGS_gen hlc Σ} `{g : !GenWp Σ} v s :
    s_is_ser (g := g) v s ⊢ s_valid_val (g := g) v;

  s_ser_spec `{invGS_gen hlc Σ} `{g : !GenWp Σ} E v (a : gwp_type g) :
    G{{{ ▷?(gwp_laters g) s_valid_val (g := g) v }}}
      s_serializer v @ a ; E
     {{{ s, RET #s; s_is_ser (g := g) v s }}} ? gwp_laters g;
}.

Record deserialization (ser : serialization) := Deserialization {
  s_deserializer : val;

  s_deser_sound `{invGS_gen hlc Σ} `{g : !GenWp Σ} E s (a : gwp_type g) :
    G{{{ True }}}
      s_deserializer #s @ a ; E
     {{{ o, RET $o; if o is Some v then s_is_ser (g := g) ser v s else ⌜True⌝ }}} ? gwp_laters g;

  s_deser_complete `{invGS_gen hlc Σ} `{g : !GenWp Σ} E v s (a : gwp_type g) :
    G{{{ s_is_ser (g := g) ser v s }}}
      s_deserializer #s @ a ; E
     {{{ RET (SOMEV v); True }}} ? gwp_laters g;
}.

Arguments s_deserializer {_}.
Arguments s_deser_sound {_} _ {_ _ _ _}.
Arguments s_deser_complete {_} _ {_ _ _ _}.

Record serialization_scheme := SerializationScheme {
  s_ser :> serialization;
  s_deser :> deserialization s_ser
}.

Arguments s_ser {_}.
Arguments s_deser {_}.

Local Hint Resolve s_is_ser_valid : core.

(** Misc.  *)
Definition s_scheme `(s : serialization_scheme) : val := (s.(s_serializer), s.(s_deserializer)).

(** We add tags to all serialization schemes to make them unambiguous (e.g. we can tell apart the
    serialization of a string ["42"] from the serialization of the integer [42]) *)

(** * Integer serialization *)
Definition int_ser : val := λ: "v", #"i_" ^ z2s "v".
Definition int_deser : val :=
  λ: "s",
    let: "tag" := strsub #0 #2 "s" in
    let: "rest" := strsub #2 ((strlen "s") - #2) "s" in
    if: "tag" = #"i_" then
      let: "mz" := s2z "rest" in
      (* this check is in principle unnecssary, but it rules out the case [i = "-0"] which ruins
         invertaibility of [ZOfString], i.e. [ZOfString s = Some z → s = StringOfZ z] does not
         hold if [s = "-0"]. This is a quick and dirty fix. *)
      match: "mz" with
        SOME "z" => if: z2s "z" = "rest" then "mz" else NONE
      | NONE => NONE
      end
    else NONE.

Definition int_scheme : val := (int_ser, int_deser).

Definition int_ser_str (z : Z) : string := "i_" +:+ StringOfZ z.

Section int_specs.
Context `{invGS_gen hlc Σ} `{g : !GenWp Σ}.

Definition int_is_ser (v : val) (s : string) : iProp Σ :=
  ⌜∃ (z : Z), v = #z ∧ s = int_ser_str z⌝.

Lemma int_is_ser_inj v s1 s2 :
  int_is_ser v s1 -∗ int_is_ser v s2 -∗ ⌜s1 = s2⌝.
Proof.
  iIntros "(% & -> & ->)". iIntros "(% & % & %)".
  subst. inversion H0. done.
Qed.
  
Lemma int_is_ser_inj_2 v1 v2 s :
  int_is_ser v1 s -∗ int_is_ser v2 s -∗ ⌜v1 = v2⌝.
Proof.
  iIntros "(% & -> & ->)". iIntros "(% & % & %)".
  by simplify_eq.
Qed.

Definition int_valid_val (v : val) : iProp Σ := ∃ (z : Z), ⌜v = #z⌝.
Lemma int_is_ser_valid (v : val) (s : string) :
  int_is_ser v s ⊢ int_valid_val v.
Proof. iIntros ([I [-> _]]). iExists _. eauto. Qed.

Implicit Types a : gwp_type g.

Lemma int_ser_spec E v a :
  G{{{ ▷?(gwp_laters g) int_valid_val v }}}
    int_ser v @ a ; E
  {{{ (s : string), RET #s; int_is_ser v s }}} ? gwp_laters g.
Proof.
  iIntros (Φ) "Hv HΦ".
  rewrite /int_scheme /int_ser /int_is_ser.
  gwp_pures. iDestruct "Hv" as "[% ->]".
  gwp_pures. iApply "HΦ". iPureIntro. eauto.
 Qed.

Lemma int_deser_spec E s a :
  G{{{ True }}}
    int_deser #(LitString s) @ a ; E
  {{{ o, RET $o; if o is Some v then int_is_ser v s else ⌜True⌝ }}} ? gwp_laters g.
Proof.
  iIntros (Φ) "_ HΦ".
  rewrite /int_deser /int_is_ser.
  gwp_pures.
  case_bool_decide as Htag; last first.
  { gwp_pures. by iApply ("HΦ" $! None). }
  gwp_pures.
  destruct (ZOfString _) eqn:Heq; last first.
  { gwp_pures. by iApply ("HΦ" $! None). }
  gwp_pures.
  case_bool_decide as Hz; last first.
  { gwp_pures. by iApply ("HΦ" $! None). }
  gwp_pures.
  iApply ("HΦ" $! (Some _)).
  iModIntro. iPureIntro.
  simplify_eq. eexists. split; [done|].
  replace (Z.to_nat 2) with 2 in *; [|done].
  rewrite Z2Nat.inj_0 in Htag.
  rewrite {1}(substring_split_from_O s 2).
  { rewrite /int_ser_str Htag Hz. do 2 f_equal. lia. }
  replace 2 with (String.length "i_"); [|done].
  rewrite -Htag.
  apply length_substring_le.
Qed.

Lemma int_deser_spec' E v s a :
  G{{{ int_is_ser v s }}}
    int_deser #(LitString s) @ a ; E
  {{{ RET (SOMEV v); True }}} ? gwp_laters g.
Proof.
  iIntros (Φ (i & -> & ->)) "HΦ".
  rewrite /int_deser /int_is_ser.
  gwp_pures.
  rewrite substring_n_0 bool_decide_eq_true_2 //.
  gwp_pures.
  assert (Z.to_nat (S (S (String.length (StringOfZ i))) - 2) = String.length (StringOfZ i)) as ->.
  { lia. }
  rewrite substring_0_length.
  rewrite ZOfString_inv.
  gwp_pures. rewrite bool_decide_eq_true_2 //.
  gwp_pures. by iApply "HΦ".
Qed.

End int_specs.

Definition int_serialization : serialization :=
  {| s_valid_val := λ _ Σ _ _, @int_valid_val Σ;
     s_serializer := int_ser;
     s_is_ser := λ _ Σ _ _, @int_is_ser Σ;
     s_is_ser_inj := λ _ Σ _ _, @int_is_ser_inj Σ;
     s_is_ser_valid := λ  _ Σ _ _, @int_is_ser_valid Σ ;
     s_ser_spec := @int_ser_spec;
  |}.

Program Definition int_deserialization : deserialization int_serialization :=
  {| s_deserializer := int_deser;
     s_deser_sound := @int_deser_spec;
     s_deser_complete := @int_deser_spec';
  |}.

Definition int_serialization_scheme :=
  SerializationScheme int_serialization int_deserialization.

(** * Boolean serialization *)
Definition bool_ser : val :=
  λ: "b", if: "b" then #"b_1" else #"b_0" .
Definition bool_deser : val :=
  λ: "v",
    if: "v" = #"b_1" then SOME #true else
    if: "v" = #"b_0" then SOME #false else
    NONE.
Definition bool_scheme : val :=
  (bool_ser, bool_deser).

Definition bool_to_int (b : bool) : Z := if b then 1 else 0.
Definition bool_ser_str (b : bool) : string :=
  if b then "b_1" else "b_0".

Section bool_specs.
Context `{invGS_gen hlc Σ} `{g : !GenWp Σ}.

Implicit Types a : gwp_type g.

Definition bool_is_ser (v : val) (s : string) : iProp Σ :=
  ⌜∃ (b : bool), v = #b ∧ s = bool_ser_str b⌝.

Lemma bool_is_ser_inj v s1 s2 :
  bool_is_ser v s1 -∗ bool_is_ser v s2 -∗ ⌜s1 = s2⌝.
Proof.
  iIntros "(% & -> & ->) (% & % & ->)".
  by simplify_eq.
Qed.

Lemma bool_is_ser_inj_2 v1 v2 s :
  bool_is_ser v1 s -∗ bool_is_ser v2 s -∗ ⌜v1 = v2⌝.
Proof.
  iIntros "(% & % & %) (% & % & %)". subst.
  unfold bool_ser_str in H3.
  destruct b eqn:Eb in H3; destruct b0 eqn:Eb0 in H3; by simplify_eq.
Qed.

Definition bool_valid_val (v : val) : iProp Σ := ∃ (b : bool), ⌜v = #b⌝.

Lemma bool_is_ser_valid (v : val) (s : string) :
  bool_is_ser v s ⊢ bool_valid_val v.
Proof. iIntros ([I [-> _]]). iExists _; eauto. Qed.

Lemma bool_ser_spec E v a :
  G{{{ ▷?(gwp_laters g) bool_valid_val v }}}
    bool_ser v @ a ; E
  {{{ (s : string), RET #s; bool_is_ser v s }}} ? gwp_laters g.
Proof.
  iIntros (Φ) "Hb HΦ".
  rewrite /bool_scheme /bool_ser /bool_is_ser.
  gwp_pures. iDestruct "Hb" as "[% ->]".
  destruct b; gwp_pures; iApply "HΦ"; eauto.
Qed.

Lemma bool_deser_spec E s a :
  G{{{ True }}}
    bool_deser #s @ a ; E
  {{{ o, RET $o; if o is Some v then bool_is_ser v s else ⌜True⌝ }}} ? gwp_laters g.
Proof.
  iIntros (Φ) "_ HΦ".
  rewrite /bool_scheme /bool_deser /bool_is_ser.
  gwp_pures.
  case_bool_decide; simplify_eq; gwp_pures.
  { iApply ("HΦ" $! (Some _)). eauto. }
  case_bool_decide; simplify_eq; gwp_pures.
  { iApply ("HΦ" $! (Some _)). eauto. }
  by iApply ("HΦ" $! None).
Qed.

Lemma bool_deser_spec' E v s a :
  G{{{ bool_is_ser v s }}}
    bool_deser #s @ a; E
  {{{ RET (SOMEV v); True }}} ? gwp_laters g.
Proof.
  iIntros (Φ [b [-> ->]]) "HΦ".
  rewrite /bool_scheme /bool_deser /bool_is_ser.
  gwp_pures.
  destruct b.
  - rewrite bool_decide_eq_true_2 //.
    gwp_pures. by iApply "HΦ".
  - rewrite bool_decide_eq_false_2 //.
    gwp_pures. by iApply "HΦ".
Qed.
End bool_specs.

Definition bool_serialization : serialization :=
  {| s_valid_val := λ _ _ Σ _, bool_valid_val;
     s_serializer := bool_ser;
     s_is_ser := λ _ _ Σ _, bool_is_ser;
     s_is_ser_inj := λ _ _ Σ _, bool_is_ser_inj;
     s_is_ser_valid := λ _ Σ _ _, @bool_is_ser_valid Σ;
     s_ser_spec := @bool_ser_spec;
  |}.

Program Definition bool_deserialization : deserialization bool_serialization :=
  {| s_deserializer := bool_deser;
     s_deser_sound := @bool_deser_spec;
     s_deser_complete := @bool_deser_spec'; |}.

Definition bool_serialization_scheme :=
  SerializationScheme bool_serialization bool_deserialization.

(** * String serialization *)
Definition string_ser : val := λ: "x", #"s_" ^ "x".
Definition string_deser : val := λ: "s",
    let: "tag" := strsub #0 #2 "s" in
    let: "rest" := strsub #2 (strlen "s" - #2) "s" in
    if: "tag" = #"s_" then SOME "rest"
    else NONE.
Definition string_scheme : val := (string_ser, string_deser).

Definition string_ser_str (s : string) : string := "s_" +:+ s.

Section string_specs.
Context `{invGS_gen hlc Σ} `{g : !GenWp Σ}.

Definition string_is_ser (v : val) (s : string) : iProp Σ :=
  ⌜∃ (s' : string), v = #s' ∧ s = string_ser_str s'⌝.

Lemma string_is_ser_inj v s1 s2 :
  string_is_ser v s1 -∗ string_is_ser v s2 -∗ ⌜s1 = s2⌝.
Proof.
  iIntros "(% & -> & ->) (% & % & %)".
  by simplify_eq.
Qed.
  
Lemma string_is_ser_inj_2 v1 v2 s :
  string_is_ser v1 s -∗ string_is_ser v2 s -∗ ⌜v1 = v2⌝.
Proof.
  iIntros "(% & % & %) (% & % & %)". by simplify_eq. Qed.

Definition string_valid_val (v : val) : iProp Σ := ∃ (s : string), ⌜v = #s⌝.
Lemma string_is_ser_valid v s : string_is_ser v s ⊢ string_valid_val v.
Proof. iIntros ([I [-> _]]). iExists _; eauto. Qed.

Implicit Types a : gwp_type g.

Lemma string_ser_spec E v a :
  G{{{ ▷?(gwp_laters g) string_valid_val v }}}
    string_ser v @ a; E
  {{{ (s : string), RET #s; string_is_ser v s }}} ? gwp_laters g.
Proof.
  iIntros (Φ) "Hs HΦ".
  rewrite /string_ser /string_is_ser.
  gwp_pures. iDestruct "Hs" as "[% ->]". gwp_pures.
  iApply "HΦ"; eauto.
Qed.

Lemma string_deser_spec E s a :
  G{{{ True }}}
    string_deser #s @ a; E
  {{{ o, RET $o; if o is Some v then string_is_ser v s else ⌜True⌝ }}} ? gwp_laters g.
Proof.
  iIntros (Φ) "_ HΦ".
  rewrite /string_deser /string_is_ser.
  gwp_pures.
  case_bool_decide as Htag; last first.
  { gwp_pures. by iApply ("HΦ" $! None). }
  gwp_pures. iModIntro.
  iApply ("HΦ" $! (Some _)). iPureIntro.
  eexists. split; [done|].
  simplify_eq.
  replace (Z.to_nat 2) with 2 in *; [|done].
  rewrite Z2Nat.inj_0 in Htag.
  rewrite {1}(substring_split_from_O s 2).
  { rewrite /string_ser_str Htag. do 2 f_equal. lia. }
  replace 2 with (String.length "s_"); [|done].
  rewrite -Htag.
  apply length_substring_le.
Qed.

Lemma string_deser_spec' E v s a :
  G{{{ string_is_ser v s }}}
    string_deser #s @ a; E
  {{{ RET (SOMEV v); True }}} ? gwp_laters g.
Proof.
  iIntros (Φ (s' & -> & ->)) "HΦ".
  rewrite /string_deser /string_is_ser.
  gwp_pures.
  rewrite substring_n_0 bool_decide_eq_true_2 //.
  gwp_pures. iModIntro.
  assert (Z.to_nat (S (S (String.length s')) - 2) = String.length s') as ->.
  { lia. }
  rewrite substring_0_length.
  by iApply "HΦ".
Qed.
End string_specs.

Definition string_serialization : serialization :=
  {| s_valid_val := λ _ Σ _ _, @string_valid_val Σ;
     s_serializer := string_ser;
     s_is_ser := λ _ Σ _ _, string_is_ser;
     s_is_ser_inj := λ _ Σ _ _, string_is_ser_inj;
     s_is_ser_valid := λ _ Σ _ _, @string_is_ser_valid Σ;
     s_ser_spec := @string_ser_spec; |}.

Program Definition string_deserialization : deserialization string_serialization :=
  {| s_deserializer := string_deser;
     s_deser_sound := @string_deser_spec;
     s_deser_complete := @string_deser_spec'; |}.

Definition string_serialization_scheme :=
  SerializationScheme string_serialization string_deserialization.

(** * Product serialization *)

Definition prod_ser : val :=
  λ: "serA" "serB" "v",
  let: "s1" := "serA" (Fst "v") in
  let: "s2" := "serB" (Snd "v") in
  (z2s (strlen "s1")) ^ (#"_" ^ ("s1" ^ "s2")).

Definition prod_deser : val :=
  λ: "deserA" "deserB" "s",
  match: strindex #0 #"_" "s" with
    SOME "i" =>
      let: "Alen_str" := strsub #0 "i" "s" in
      let: "Alen?" := s2z "Alen_str" in
      match: "Alen?" with
        SOME "Alen" =>
          (* this check is in principle unnecssary, but it rules out the case [i = "-0"] which ruins
             invertaibility of [ZOfString], i.e. [ZOfString s = Some z → s = StringOfZ z] does not
             hold if [s = "-0"]. *)
          if: z2s "Alen" ≠ "Alen_str" then NONEV else
          if: "Alen" < #0 then NONEV else
          let: "slen" := strlen "s" in
          if: "slen" - "i" - #1 < "Alen" then NONEV else
          let: "s1" := strsub ("i" + #1) "Alen" "s" in
          let: "s2" := strsub (("i" + #1) + "Alen") ("slen" - (("i" + #1) + "Alen")) "s" in
          let: "v1?" := "deserA" "s1" in
          match: "v1?" with
            SOME "v1" =>
              let: "v2?" := "deserB" "s2" in
              match: "v2?" with
                SOME "v2" => SOME ("v1", "v2")
              | NONE => NONEV
              end
          | NONE => NONEV
          end
      | NONE => NONEV
      end
  | NONE => NONEV
  end.

Definition prod_ser' (serA serB : val) : val :=
  λ: "v",
  let: "s1" := serA (Fst "v") in
  let: "s2" := serB (Snd "v") in
  (z2s (strlen "s1")) ^ (#"_" ^ ("s1" ^ "s2")).

Definition prod_deser' (deserA deserB : val) : val :=
  λ: "s",
  match: strindex #0 #"_" "s" with
    SOME "i" =>
      let: "Alen_str" := strsub #0 "i" "s" in
      let: "Alen?" := s2z "Alen_str" in
      match: "Alen?" with
        SOME "Alen" =>
          (* this check is in principle unnecssary, but it rules out the case [i = "-0"] which ruins *)
(*              invertaibility of [ZOfString], i.e. [ZOfString s = Some z → s = StringOfZ z] does not *)
(*              hold if [s = "-0"]. *)
          if: z2s "Alen" ≠ "Alen_str" then NONEV else
          if: "Alen" < #0 then NONEV else
          let: "slen" := strlen "s" in
          if: "slen" - "i" - #1 < "Alen" then NONEV else
          let: "s1" := strsub ("i" + #1) "Alen" "s" in
          let: "s2" := strsub (("i" + #1) + "Alen") ("slen" - (("i" + #1) + "Alen")) "s" in
          let: "v1?" := deserA "s1" in
          match: "v1?" with
            SOME "v1" =>
              let: "v2?" := deserB "s2" in
              match: "v2?" with
                SOME "v2" => SOME ("v1", "v2")
              | NONE => NONEV
              end
          | NONE => NONEV
          end
      | NONE => NONEV
      end
  | NONE => NONEV
  end.

Definition prod_scheme : val :=
  λ: "schemeA" "schemeB",
    let, ("serA", "deserA") := "schemeA" in
    let, ("serB", "deserB") := "schemeB" in
    (prod_ser "serA" "serB", prod_deser "deserA" "deserB").

Definition prod_ser_str (s1 s2 : string) :=
  StringOfZ (String.length s1) +:+ "_" +:+ s1 +:+ s2.

#[global] Instance prod_ser_str_inj :
  Inj2 (=) (=) (=) prod_ser_str.
Proof.
  intros ????. rewrite /prod_ser_str.
  intros Heq.
  cut (String.length (StringOfZ (String.length x1))
       = String.length (StringOfZ (String.length y1))).
  { intros Hlen.
    destruct (append_eq_length_inv _ _ _ _ Hlen Heq) as [? Hrest].
    simplify_eq.
    by apply append_eq_length_inv in Hrest. }
  eapply (not_elem_of_string_app_cons_inv_l "_"%char "_"%char) in Heq.
  { by destruct Heq as [-> ?]. }
  { by intros ?%StringOfZ_not_sep. }
  { by intros ?%StringOfZ_not_sep. }
Qed.

Section prod_serialization.
  Context (A B : serialization).
  Context `{invGS_gen hlc Σ} `{g : !GenWp Σ}.

  Definition prod_is_ser' (v : val) (s : string) (HA HB : val → string → iProp Σ) : iProp Σ :=
    ∃ (v1 v2 : val) (s1 s2 : string), ⌜v = (v1, v2)%V ∧ s = prod_ser_str s1 s2⌝ ∗ HA v1 s1 ∗ HB v2 s2.

  Definition prod_is_ser (v : val) (s : string) : iProp Σ :=
    prod_is_ser' v s (s_is_ser (g := g) A) (s_is_ser (g := g) B).

  Lemma prod_is_ser_inj v s1 s2 :
    prod_is_ser v s1 -∗ prod_is_ser v s2 -∗ ⌜s1 = s2⌝.
  Proof.
    iIntros "(%v1A & %v1B & %s1A & %s1B & [-> ->] & HA1 & HB1) (%v2A & %v2B & %s2A & %s2B & [% ->] & HA2 & HB2)".
    simplify_eq.
    iPoseProof (A.(s_is_ser_inj) with "HA1 HA2") as "->".
    by iPoseProof (B.(s_is_ser_inj) with "HB1 HB2") as "->".
  Qed.

  Implicit Types c : gwp_type g.

  Definition prod_valid_val' (v : val) (HA HB : val → iProp Σ) : iProp Σ :=
    ∃ v1 v2, ⌜v = (v1, v2)%V⌝ ∗ HA v1 ∗ HB v2.

  Definition prod_valid_val (v : val) : iProp Σ :=
    prod_valid_val' v (s_valid_val (g := g) A)  (s_valid_val (g := g) B).

  Lemma prod_is_ser_valid v s : prod_is_ser v s ⊢ prod_valid_val v.
  Proof.
    iIntros "(%&%&%&%&[% %]&(HA & HB))". 
    iExists _, _.
    iSplit; [done|]. iSplitL "HA"; by iApply s_is_ser_valid.
  Qed.

  Lemma prod_ser'_spec (HA HB : val → iProp Σ) E c (serA serB v vA vB : val) :
    ▷?(gwp_laters g) ⌜v = (vA, vB)%V⌝ -∗
    (G{{{ ▷?(gwp_laters g) HA vA }}}
        serA vA @ c; E
      {{{ (s : string), RET #s; s_is_ser (g := g) A vA s }}} ? gwp_laters g) -∗
    (G{{{ ▷?(gwp_laters g) HB vB }}}
        serB vB @ c; E
      {{{ (s : string), RET #s; s_is_ser (g := g) B vB s }}} ? gwp_laters g) -∗
    G{{{ ▷?(gwp_laters g) prod_valid_val' v HA HB }}}
      prod_ser' serA serB v @ c; E
    {{{ (s : string), RET #s; prod_is_ser v s }}} ? gwp_laters g.
  Proof.
    iIntros "#Hv #HA #HB" (Φ) "!# Hp HΦ".
    rewrite /prod_ser' /prod_is_ser.
    gwp_pures.
    iDestruct "Hp" as (???) "[H1 H2]". iSimplifyEq.
    gwp_pures.
    gwp_apply ("HA" with "H1").
    iIntros (s1) "Hs1".
    gwp_pures.
    gwp_apply ("HB" with "H2").
    iIntros (s2) "Hs2".
    gwp_pures.
    iApply "HΦ".
    iModIntro.
    iExists vA, vB, s1, s2; iSplit; auto.
  Qed.

  Lemma prod_ser'_spec_closed E v c :
    G{{{ ▷?(gwp_laters g) prod_valid_val v }}}
      prod_ser' A.(s_serializer) B.(s_serializer) v @ c; E
    {{{ (s : string), RET #s; prod_is_ser v s }}} ? gwp_laters g.
  Proof.
    iIntros (?) "#(% & % & Heq) H".
    gwp_apply (prod_ser'_spec (s_valid_val (g := g) A)  (s_valid_val (g := g) B)).
    - by iDestruct "Heq" as (?) "H".
    - iIntros (?) "!# Hv H". by gwp_apply (s_ser_spec with "Hv").
    - iIntros (?) "!# Hv H". by gwp_apply (s_ser_spec with "Hv").
    - by iExists _, _.
    - done.
  Qed.

  Lemma prod_ser_spec E v c (serA serB : val) :
    (∀ vA,
      G{{{ ▷?(gwp_laters g) s_valid_val (g := g) A vA }}}
        serA vA @ c; E
       {{{ (s : string), RET #s; s_is_ser (g := g) A vA s }}} ? gwp_laters g) -∗
    (∀ vB,
      G{{{ ▷?(gwp_laters g) s_valid_val (g := g) B vB }}}
        serB vB @ c; E
       {{{ (s : string), RET #s; s_is_ser (g := g) B vB s }}} ? gwp_laters g) -∗
    G{{{ ▷?(gwp_laters g) prod_valid_val v }}}
      prod_ser serA serB v @ c; E
    {{{ (s : string), RET #s; prod_is_ser v s }}} ? gwp_laters g.
  Proof.
    iIntros "#HA #HB" (Φ) "!# (% & % & #Heq & #Hp) HΦ".
    rewrite /prod_ser /prod_is_ser.
    do 4 gwp_pure _. iSimplifyEq.
    gwp_apply (prod_ser'_spec (s_valid_val (g := g) A)  (s_valid_val (g := g) B)
                with "[//] HA HB"); [iExists _,_;eauto|done].
  Qed.

End prod_serialization.

Program Definition prod_serialization (A B : serialization) : serialization :=
  {| s_valid_val := λ _ Σ, @prod_valid_val A B _ Σ;
     s_serializer := prod_ser' _ _;
     s_is_ser := λ _ Σ, @prod_is_ser A B _ Σ;
     s_is_ser_inj := λ _ Σ, @prod_is_ser_inj A B _ Σ;
     s_is_ser_valid := λ _ Σ, @prod_is_ser_valid A B _ Σ;
     s_ser_spec := @prod_ser'_spec_closed A B; |}.

Section prod_deserialization.
  Context `{invGS_gen hlc Σ} `{g : !GenWp Σ}.

  Implicit Types c : gwp_type g.

  Lemma prod_deser'_sound (HA HB : val → string → iProp Σ) E s c (deserA deserB : val) :
    (∀ s,
      G{{{ True }}}
        deserA #s @ c; E
       {{{ o, RET $o; if o is Some v then HA v s else ⌜True⌝ }}} ? gwp_laters g) -∗
    (∀ s,
      G{{{ True }}}
        deserB #s @ c; E
       {{{ o, RET $o; if o is Some v then HB v s else ⌜True⌝ }}} ? gwp_laters g) -∗
    G{{{ True }}}
      prod_deser' deserA deserB #s @ c; E
    {{{ o, RET $o; if o is Some v then prod_is_ser' v s HA HB else ⌜True⌝ }}} ? gwp_laters g.
  Proof.
    iIntros "#HA #HB" (Φ) "!# _ HΦ".
    rewrite /prod_deser' /prod_is_ser /prod_is_ser' /prod_ser_str.
    gwp_pures. rewrite /option_nat_to_val.
    case_match eqn:Htag; gwp_pures; [|by iApply ("HΦ" $! None)].
    case_match eqn:Hlen; gwp_pures; [|by iApply ("HΦ" $! None)].
    case_bool_decide as Hs; gwp_pures; [|by iApply ("HΦ" $! None)].
    case_bool_decide as Hz; gwp_pures; [by iApply ("HΦ" $! None)|].
    case_bool_decide as Hl; gwp_pures; [by iApply ("HΦ" $! None)|].

    rewrite Z2Nat.inj_0 Nat2Z.id in Hs.
    rewrite Z2Nat.inj_0 in Htag.
    simplify_eq.

    gwp_apply "HA"; [done|].
    iIntros ([a|]) "Ha"; gwp_pures; [|by iApply ("HΦ" $! None)].
    gwp_apply "HB"; [done|].
    iIntros ([b|]) "Hb"; gwp_pures; [|by iApply ("HΦ" $! None)].
    iApply ("HΦ" $! (Some _)). iModIntro.
    do 4 iExists _. iSplit; [|iFrame].
    iPureIntro. split; [done|].
      
    rewrite Z2Nat.inj_add; [|lia|lia].
    rewrite !Nat2Z.id.
    replace (Z.to_nat 1) with 1; [|lia].

    set (sA := String.substring (n + 1) (Z.to_nat z) s).
    set (sB := String.substring (Z.to_nat (n + 1 + z)) (Z.to_nat (String.length s - (n + 1 + z))) s).

    apply Znot_lt_ge in Hz, Hl.
    rewrite {1}(substring_split_from_O s n); [|lia].
    f_equal.
    { rewrite /sA -Hs. f_equal.
      rewrite length_substring; lia. }

    rewrite (substring_split (String.length "_")) /=; [|lia].
    rewrite (String.index_correct1 0 _ "_") //.
    f_equal.

    rewrite (substring_split (Z.to_nat z)) /=; [|lia].
    rewrite /sA.
    f_equal.
    rewrite /sB.
    f_equal; lia.
  Qed.

  Lemma prod_deser_sound (HA HB : val → string → iProp Σ) E s c (deserA deserB : val) :
    (∀ s,
      G{{{ True }}}
        deserA #s @ c; E
       {{{ o, RET $o; if o is Some v then HA v s else ⌜True⌝ }}} ? gwp_laters g) -∗
    (∀ s,
      G{{{ True }}}
        deserB #s @ c; E
       {{{ o, RET $o; if o is Some v then HB v s else ⌜True⌝ }}} ? gwp_laters g) -∗
    G{{{ True }}}
      prod_deser deserA deserB #s @ c; E
    {{{ o, RET $o; if o is Some v then prod_is_ser' v s HA HB else ⌜True⌝ }}} ? gwp_laters g.
  Proof.
    iIntros "#HA #HB" (Φ) "!# _ HΦ".
    rewrite /prod_deser. do 4 gwp_pure _.
    by gwp_apply (prod_deser'_sound with "HA HB").
  Qed.

  Lemma prod_deser'_complete (HA HB : val → string → iProp Σ) E v vA vB s c (deserA deserB : val) :
    ▷?(gwp_laters g) ⌜v = (vA, vB)%V⌝ -∗
    (∀ sA,
      G{{{ HA vA sA }}}
        deserA #sA @ c; E
       {{{ RET (SOMEV vA); True }}} ? gwp_laters g) -∗
    (∀ sB,
      G{{{ HB vB sB }}}
        deserB #sB @ c; E
       {{{ RET (SOMEV vB); True }}} ? gwp_laters g) -∗
    G{{{ prod_is_ser' v s HA HB }}}
      prod_deser' deserA deserB #s @ c; E
    {{{ RET (SOMEV v); True }}} ? gwp_laters g.
  Proof.
    iIntros "#Heq #HA #HB" (Φ) "!# (%v1 & %v2 & %s1 & %s2 & [-> ->] & Hv1 & Hv2) HΦ".
    rewrite /prod_deser' /prod_is_ser /prod_ser_str.
    gwp_pures. iSimplifyEq.
    erewrite (index_0_append_char ); auto; last first.
    { apply valid_tag_stringOfZ. }
    gwp_pures.
    rewrite !Z2Nat.inj_0 Nat2Z.id.
    rewrite substring_0_length_append.
    rewrite ZOfString_inv.
    gwp_pures.
    rewrite bool_decide_eq_true_2 //.
    gwp_pures.
    rewrite bool_decide_eq_false_2; last first.
    { apply Zle_not_lt, Zle_0_nat. }
    gwp_pures.
    rewrite bool_decide_eq_false_2; last first.
    { apply Zle_not_lt. rewrite !strings.length_app /=. lia. }
    gwp_pures.

    rewrite !Nat2Z.id.
    replace (Z.to_nat (String.length (StringOfZ (String.length s1)) + 1))
      with (String.length (StringOfZ (String.length s1)) + 1); [|lia].
    rewrite substring_add_length_app /=.
    rewrite substring_0_length_append.
    gwp_apply ("HA" with "Hv1").
    iIntros "_".
    gwp_pures.
    rewrite Z2Nat.inj_add; [|lia..].
    replace (Z.to_nat (String.length (StringOfZ (String.length s1)) + 1) +
               Z.to_nat (String.length s1))
      with (String.length (StringOfZ (String.length s1)) + 1 + String.length s1); [|lia].
    rewrite Z2Nat.inj_sub ?Nat2Z.id; [|lia].
    rewrite !Z2Nat.inj_add ?Nat2Z.id; [|lia..].
    rewrite -Nat.add_assoc.
    rewrite substring_add_length_app /=.
    replace (String.length (StringOfZ (String.length s1) +:+ "_" +:+ s1 +:+ s2) -
                (String.length (StringOfZ (String.length s1)) + S (String.length s1)))
      with (String.length s2); last first.
    { rewrite !strings.length_app /=. lia. }
    rewrite substring_length_append.
    gwp_apply ("HB" with "Hv2"). iIntros "_".
    gwp_pures.
    iApply "HΦ"; done.
  Qed.

  Lemma prod_deser_complete (HA HB : val → string → iProp Σ) E v vA vB s c (deserA deserB : val) :
    ▷?(gwp_laters g) ⌜v = (vA, vB)%V⌝ -∗
    (∀ sA,
      G{{{ HA vA sA }}}
        deserA #sA @ c; E
       {{{ RET (SOMEV vA); True }}} ? gwp_laters g) -∗
    (∀ sB,
      G{{{ HB vB sB }}}
        deserB #sB @ c; E
       {{{ RET (SOMEV vB); True }}} ? gwp_laters g) -∗
    G{{{ prod_is_ser' v s HA HB }}}
      prod_deser deserA deserB #s @ c; E
    {{{ RET (SOMEV v); True }}} ? gwp_laters g.
  Proof.
    iIntros "#Heq #HA #HB" (Φ) "!# (%v1 & %v2 & %s1 & %s2 & [-> ->] & Hv1 & Hv2) HΦ".
    simplify_eq.
    rewrite /prod_deser. do 4 gwp_pure _.
    gwp_apply (prod_deser'_complete _ _ _ (_, _) with "Heq HA HB [Hv1 Hv2]"); [|done].
    do 4 (iExists _). iSplit; [done|iFrame].
  Qed.

End prod_deserialization.

Section prod_deserialization_closed.
  Context `(dA : deserialization A) `(dB : deserialization B).
  Context `{invGS_gen hlc Σ} `{g : !GenWp Σ}.

  Implicit Types c : gwp_type g.

  Lemma prod_deser'_sound_closed E s c :
    G{{{ True }}}
      prod_deser' dA.(s_deserializer) dB.(s_deserializer) #s @ c; E
    {{{ o, RET $o; if o is Some v then prod_is_ser (g := g) A B v s else ⌜True⌝ }}} ? gwp_laters g.
  Proof.
    iIntros (?) "_ H".
    gwp_apply (prod_deser'_sound with "[] [] [//]"); [| |done].
    - iIntros (??) "!# Hv H". by gwp_apply s_deser_sound.
    - iIntros (??) "!# Hv H". by gwp_apply s_deser_sound.
  Qed.

  Lemma prod_deser'_complete_closed E v s c :
    G{{{ prod_is_ser (g := g) A B v s }}}
      prod_deser' dA.(s_deserializer) dB.(s_deserializer) #s @ c; E
    {{{ RET (SOMEV v); True }}} ? gwp_laters g.
  Proof.
    iIntros (?) "(%&%&%&%&(-> & ->)&H1&H2) H".
    gwp_apply (prod_deser'_complete (s_is_ser A) (s_is_ser B) _ (_, _) with "[] [] [] [H1 H2]"); [done| | | |done].
    - iIntros (?) "!# % H1 H2". by gwp_apply (s_deser_complete with "H1").
    - iIntros (?) "!# % H1 H2". by gwp_apply (s_deser_complete with "H1").
    - do 4 (iExists _). iFrame. iPureIntro. eauto.
  Qed.

End prod_deserialization_closed.

Program Definition prod_deserialization `(dA : deserialization A) `(dB : deserialization B) :
  deserialization (prod_serialization A B) :=
  {| s_deserializer := prod_deser' dA.(s_deserializer) dB.(s_deserializer) ;
     s_deser_sound := @prod_deser'_sound_closed A dA B dB;
     s_deser_complete := @prod_deser'_complete_closed _ dA _ dB; |}.

Definition prod_serialization_scheme (A B : serialization_scheme) :=
  SerializationScheme (prod_serialization A B) (prod_deserialization A B).

Definition sum_ser : val :=
  λ: "serA" "serB" "v",
  match: "v" with
    InjL "x" => #"L" ^ (#"_" ^ ("serA" "x"))
  | InjR "x" => #"R" ^ (#"_" ^ ("serB" "x"))
  end.

Definition sum_deser : val :=
  λ: "deserA" "deserB" "s",
  let: "tag" := strsub #0 #2 "s" in
  let: "rest" := strsub #2 ((strlen "s") - #2) "s" in
  if: "tag" = #"L_"
  then
    let: "mA" := "deserA" "rest" in
    match: "mA" with
      SOME "a" => SOME (InjL "a")
    | NONE => NONEV
    end
  else
    (if: "tag" = #"R_"
     then
       let: "mB" := "deserB" "rest" in
       match: "mB" with
         SOME "b" => SOME (InjR "b")
       | NONE => NONEV
       end
     else NONEV).

Definition sum_scheme : val :=
  λ: "schemeA" "schemeB",
    let, ("serA", "deserA") := "schemeA" in
    let, ("serB", "deserB") := "schemeB" in
    (sum_ser "serA" "serB", sum_deser "deserA" "deserB").

Definition sum_ser' (serA serB : val) : val :=
  λ: "v",
  match: "v" with
    InjL "x" => #"L" ^ (#"_" ^ serA "x")
  | InjR "x" => #"R" ^ (#"_" ^ serB "x")
  end.

Definition sum_deser' (deserA deserB : val) : val :=
  λ: "s",
  let: "tag" := strsub #0 #2 "s" in
  let: "rest" := strsub #2 ((strlen "s") - #2) "s" in
  if: "tag" = #"L_"
  then
    let: "mA" := deserA "rest" in
    match: "mA" with
      SOME "a" => SOME (InjL "a")
    | NONE => NONEV
    end
  else
    (if: "tag" = #"R_"
     then
       let: "mB" := deserB "rest" in
       match: "mB" with
         SOME "b" => SOME (InjR "b")
       | NONE => NONEV
       end
     else NONEV).


Definition inl_ser_str (s : string) := "L_" +:+ s.
Definition inr_ser_str (s : string) := "R_" +:+ s.

Section sum_serialization.
  Context (A B : serialization).
  Context `{invGS_gen hlc Σ} `{g : !GenWp Σ}.

  Implicit Types c : gwp_type g.

  Definition sum_valid_val' (v : val) (HA HB : val → iProp Σ) : iProp Σ :=
    ∃ w, (⌜v = InjLV w⌝ ∧ HA w) ∨ (⌜v = InjRV w⌝ ∧ HB w).

  Definition sum_valid_val (v : val) : iProp Σ :=
    sum_valid_val' v (s_valid_val (g := g) A) (s_valid_val (g := g) B).

  Definition sum_is_ser' (v : val) (s : string) (HA HB : val → string → iProp Σ) : iProp Σ :=
    ∃ w s',
      (⌜v = InjLV w ∧ s = inl_ser_str s'⌝ ∧ HA w s') ∨
      (⌜v = InjRV w ∧ s = inr_ser_str s'⌝ ∧ HB w s').

  Definition sum_is_ser (v : val) (s : string) : iProp Σ :=
    sum_is_ser' v s (s_is_ser (g:= g) A) (s_is_ser (g:= g) B).

  Lemma sum_is_ser_inj v s1 s2 :
    sum_is_ser v s1 -∗ sum_is_ser v s2 -∗ ⌜s1 = s2⌝.
  Proof.
    iIntros "(%v1 & %s1' & [((% & %) & Hs1) | ((% & %) & Hs1)])
     (%v2 & %s2' & [((% & %) & Hs2) | ((% & %) & Hs2)])"; simplify_eq.
    - by iPoseProof (A.(s_is_ser_inj) with "Hs1 Hs2") as "->".
    - by iPoseProof (B.(s_is_ser_inj) with "Hs1 Hs2") as "->".
  Qed.

  Lemma sum_is_ser_valid v s : sum_is_ser v s ⊢ sum_valid_val v.
  Proof.
    iIntros "(% & % & [((% & %) & ?) | ((% & %) & ?)])".
    - iExists _. iLeft. iSplit; [done|]. by iApply s_is_ser_valid.
    - iExists _. iRight. iSplit; [done|]. by iApply s_is_ser_valid.
  Qed.

  Lemma sum_ser'_spec (HA HB : val → iProp Σ) E c (serA serB v vA vB : val) :
    ▷?(gwp_laters g) (⌜v = InjLV vA⌝ ∨ ⌜v = InjRV vB⌝) -∗
    (G{{{ ▷?(gwp_laters g) HA vA }}}
       serA vA @ c; E
      {{{ (s : string), RET #s; s_is_ser (g := g) A vA s }}} ? gwp_laters g) -∗
    (G{{{ ▷?(gwp_laters g) HB vB }}}
       serB vB @ c; E
      {{{ (s : string), RET #s; s_is_ser (g := g) B vB s }}} ? gwp_laters g) -∗
    G{{{ ▷?(gwp_laters g) sum_valid_val' v HA HB }}}
      sum_ser' serA serB v @ c ; E
    {{{ (s : string), RET #s; sum_is_ser v s }}} ? gwp_laters g.
  Proof.
    iIntros "#Hsum #HA #HB" (Φ) "!# [%w Hw] HΦ".
    rewrite /sum_ser' /sum_is_ser /sum_is_ser'.
    gwp_pures.
    iDestruct "Hw" as "[[-> Hw]|[-> Hw]]"; gwp_pures.
    - iDestruct "Hsum" as "[% | %]"; simplify_eq.
      gwp_apply ("HA" with "Hw").
      iIntros (s) "Hs"; simpl.
      gwp_pures.
      iApply "HΦ"; eauto 10.
    - iDestruct "Hsum" as "[% | %]"; simplify_eq.
      gwp_apply ("HB" with "Hw").
      iIntros (s) "Hs"; simpl.
      gwp_pures.
      iApply "HΦ"; eauto 10.
  Qed.

  Lemma sum_ser'_spec_closed E v c :
    G{{{ ▷?(gwp_laters g) sum_valid_val v }}}
      sum_ser' A.(s_serializer) B.(s_serializer) v @ c; E
    {{{ (s : string), RET #s; sum_is_ser v s }}} ? gwp_laters g.
  Proof.
    iIntros (?) "[% #Hv] H".
    gwp_apply (sum_ser'_spec (s_valid_val (g := g) A) (s_valid_val (g := g) B)).
    - iDestruct "Hv" as "[(-> &_) | (-> &_)]"; eauto.
    - iIntros (?) "!# Hw H". by gwp_apply (s_ser_spec with "Hw").
    - iIntros (?) "!# Hw H". by gwp_apply (s_ser_spec with "Hw").
    - by iExists _.
    - done.
  Qed.

  Lemma sum_ser_spec E v c (serA serB : val) :
    (∀ vA,
      G{{{ ▷?(gwp_laters g) s_valid_val (g := g) A vA }}}
        serA vA @ c; E
       {{{ (s : string), RET #s; s_is_ser (g := g) A vA s }}} ? gwp_laters g) -∗
    (∀ vB,
      G{{{ ▷?(gwp_laters g) s_valid_val (g := g) B vB }}}
        serB vB @ c; E
       {{{ (s : string), RET #s; s_is_ser (g := g) B vB s }}} ? gwp_laters g) -∗
    G{{{ ▷?(gwp_laters g) sum_valid_val v }}}
      sum_ser serA serB v @ c ; E
    {{{ (s : string), RET #s; sum_is_ser v s }}} ? gwp_laters g.
  Proof.
    iIntros "#HA #HB" (Φ) "!# [% #Hp] HΦ".
    rewrite /sum_ser.
    do 4 gwp_pure _.
    gwp_apply (sum_ser'_spec with "[] HA HB").
    { iDestruct "Hp" as "[(% & _) | (% & _)]"; eauto. }
    { by iExists _. }
    done.
  Qed.
End sum_serialization.

Program Definition sum_serialization (A B : serialization) : serialization :=
  {| s_valid_val := λ _ Σ, @sum_valid_val A B _ Σ;
     s_serializer := sum_ser' _ _;
     s_is_ser := λ _ Σ, @sum_is_ser A B _ Σ;
     s_is_ser_inj := λ _ Σ, @sum_is_ser_inj A B _ Σ;
     s_is_ser_valid := λ _ Σ, @sum_is_ser_valid A B _ Σ;
     s_ser_spec := @sum_ser'_spec_closed A B; |}.

Section sum_deserialization.
  Context `{invGS_gen hlc Σ} `{g : !GenWp Σ}.

  Implicit Types c : gwp_type g.

  Lemma sum_deser'_sound (HA HB : val → string → iProp Σ) E s c (deserA deserB : val) :
    (∀ s,
      G{{{ True }}}
        deserA #s @ c; E
       {{{ o, RET $o; if o is Some v then HA v s else ⌜True⌝ }}} ? gwp_laters g) -∗
    (∀ s,
      G{{{ True }}}
        deserB #s @ c; E
       {{{ o, RET $o; if o is Some v then HB v s else ⌜True⌝ }}} ? gwp_laters g) -∗
    G{{{ True }}}
      sum_deser' deserA deserB #s @ c ; E
    {{{ o, RET $o; if o is Some v then sum_is_ser' v s HA HB else ⌜True⌝ }}} ? gwp_laters g.
  Proof.
    iIntros "#HA #HB" (Φ) "!# _ HΦ".
    rewrite /sum_deser' /sum_is_ser.
    gwp_pures.
    rewrite !Z2Nat.inj_0.
    replace (Z.to_nat 2) with 2; [|done].
    case_bool_decide as Hl; gwp_pures.
    - gwp_apply "HA"; [done|]. simplify_eq.
      iIntros ([a|]) "Ha"; gwp_pures; [|by iApply ("HΦ" $! None)].
      iApply ("HΦ" $! (Some _)).
      iModIntro. do 2 (iExists _).
      iLeft. iSplitR "Ha"; [|iFrame].
      iPureIntro. split; [done|].
      rewrite /inl_ser_str -Hl.
      rewrite {1}(substring_split_from_O s 2).
      { do 2 f_equal. lia. }
      assert (2 = String.length "L_") as -> by reflexivity.
      rewrite -Hl.
      apply length_substring_le.
    - case_bool_decide as Hr; gwp_pures; [|by iApply ("HΦ" $! None)]. simplify_eq.
      gwp_apply "HB"; [done|].
      iIntros ([b|]) "Hb"; gwp_pures; [|by iApply ("HΦ" $! None)].
      iApply ("HΦ" $! (Some _)).
      iModIntro. do 2 (iExists _).
      iRight. iSplitR "Hb"; [|iFrame].
      iPureIntro. split; [done|].
      rewrite /inr_ser_str -Hr.
      rewrite {1}(substring_split_from_O s 2).
      { do 2 f_equal. lia. }
      assert (2 = String.length "R_") as -> by reflexivity.
      rewrite -Hr.
      apply length_substring_le.
  Qed.

  Lemma sum_deser_sound (HA HB : val → string → iProp Σ) E s c (deserA deserB : val) :
    (∀ s,
      G{{{ True }}}
        deserA #s @ c; E
       {{{ o, RET $o; if o is Some v then HA v s else ⌜True⌝ }}} ? gwp_laters g) -∗
    (∀ s,
      G{{{ True }}}
        deserB #s @ c; E
       {{{ o, RET $o; if o is Some v then HB v s else ⌜True⌝ }}} ? gwp_laters g) -∗
    G{{{ True }}}
      sum_deser deserA deserB #s @ c ; E
    {{{ o, RET $o; if o is Some v then sum_is_ser' v s HA HB else ⌜True⌝ }}} ? gwp_laters g.
  Proof.
    iIntros "#HA #HB" (Φ) "!# _ HΦ".
    rewrite /sum_deser. do 4 gwp_pure _.
    by gwp_apply (sum_deser'_sound with "HA HB").
  Qed.

  Lemma sum_deser'_complete (HA HB : val → string → iProp Σ) E v s c (deserA deserB : val) :
    (∀ sA vA,
       ⌜v = InjLV vA⌝ -∗
       G{{{ HA vA sA }}}
        deserA #sA @ c; E
       {{{ RET (SOMEV vA); True }}} ? gwp_laters g) -∗
    (∀ sB vB,
       ⌜v = InjRV vB⌝ -∗
       G{{{ HB vB sB }}}
         deserB #sB @ c; E
       {{{ RET (SOMEV vB); True }}} ? gwp_laters g) -∗
    G{{{ sum_is_ser' v s HA HB }}}
      sum_deser' deserA deserB #s @ c; E
    {{{ RET (SOMEV v); True }}} ? gwp_laters g.
  Proof.
    iIntros "#HA #HB" (Φ) "!# (%w & %s' & Hw) HΦ";
    rewrite /sum_deser' /sum_is_ser.
    gwp_pures.
    rewrite !Z2Nat.inj_0.
    replace (Z.to_nat 2) with 2; [|done].
    iDestruct "Hw" as "[((-> & ->) &Hw)|((->&->)&Hw)]"; simplify_eq.
    - rewrite (substring_0_length_append "L_") /=.
      gwp_pure.
      replace (Z.to_nat (S (S (String.length s')) - 2)) with
          (String.length s') by lia.
      rewrite substring_0_length.
      gwp_apply ("HA" with "[] [Hw]"); [done|done|]. iIntros "_".
      gwp_pures.
      by iApply "HΦ".
    - rewrite (substring_0_length_append "R_") /=.
      gwp_pures.
      replace (Z.to_nat (S (S (String.length s')) - 2)) with
          (String.length s') by lia.
      rewrite substring_0_length.
      gwp_apply ("HB" with "[] [Hw]"); [done|done|]; iIntros "_".
      gwp_pures.
      iApply "HΦ"; done.
  Qed.

  Lemma sum_deser_complete (HA HB : val → string → iProp Σ) E v s c (deserA deserB : val) :
    (∀ sA vA,
      ⌜v = InjLV vA⌝ -∗
      G{{{ HA vA sA }}}
        deserA #sA @ c; E
       {{{ RET (SOMEV vA); True }}} ? gwp_laters g) -∗
    (∀ sB vB,
      ⌜v = InjRV vB⌝ -∗
      G{{{ HB vB sB }}}
        deserB #sB @ c; E
       {{{ RET (SOMEV vB); True }}} ? gwp_laters g) -∗
    G{{{ sum_is_ser' v s HA HB }}}
      sum_deser deserA deserB #s @ c; E
    {{{ RET (SOMEV v); True }}} ? gwp_laters g.
  Proof.
    iIntros "#HA #HB" (Φ) "!# Hw HΦ".
    rewrite /sum_deser. do 4 gwp_pure _.
    by gwp_apply (sum_deser'_complete with "HA HB [Hw]").
  Qed.

End sum_deserialization.

Section sum_deserialization_closed.
  Context `(dA : deserialization A) `(dB : deserialization B).
  Context `{invGS_gen hlc Σ} `{g : !GenWp Σ}.

  Implicit Types c : gwp_type g.

  Lemma sum_deser'_sound_closed E s c :
    G{{{ True }}}
      sum_deser' dA.(s_deserializer) dB.(s_deserializer) #s @ c; E
    {{{ o, RET $o; if o is Some v then sum_is_ser (g := g) A B v s else ⌜True⌝ }}} ? gwp_laters g.
  Proof.
    iIntros (?) "_ H".
    gwp_apply (sum_deser'_sound with "[] [] [//]"); [| |done].
    - iIntros (??) "!# Hv H". by gwp_apply s_deser_sound.
    - iIntros (??) "!# Hv H". by gwp_apply s_deser_sound.
  Qed.

  Lemma sum_deser'_complete_closed E v s c :
    G{{{ sum_is_ser (g := g) A B v s }}}
      sum_deser' dA.(s_deserializer) dB.(s_deserializer) #s @ c; E
    {{{ RET (SOMEV v); True }}} ? gwp_laters g.
  Proof.
    iIntros (?) "Hser H".
    gwp_apply (sum_deser'_complete (s_is_ser A) (s_is_ser B) with "[] [] [Hser]"); [| |done|done].
    - iIntros (??->?) "!# H1 H2". by gwp_apply (s_deser_complete with "H1").
    - iIntros (??->?) "!# H1 H2". by gwp_apply (s_deser_complete with "H1").
  Qed.

End sum_deserialization_closed.

Program Definition sum_deserialization `(dA : deserialization A) `(dB : deserialization B) :
  deserialization (sum_serialization A B) :=
  {| s_deserializer := sum_deser' dA.(s_deserializer) dB.(s_deserializer) ;
     s_deser_sound := @sum_deser'_sound_closed A dA B dB;
     s_deser_complete := @sum_deser'_complete_closed _ dA _ dB; |}.

Definition sum_serialization_scheme (A B : serialization_scheme) :=
  SerializationScheme (sum_serialization A B) (sum_deserialization A B).

Lemma prod_ser_int_ser_neq z s1 s2 :
  prod_ser_str s1 s2 ≠ int_ser_str z.
Proof.
  rewrite -String.get_correct => H.
  specialize (H 0). simpl in H.
  rewrite -String.append_correct1 in H.
  { eapply get_StringOfZ_ne; [|done]. done. }
  apply StringOfZ_length.
Qed.
Lemma prod_ser_string_ser_neq z s1 s2 :
  prod_ser_str s1 s2 ≠ string_ser_str z.
Proof.
  rewrite -String.get_correct => H.
  specialize (H 0). simpl in H.
  rewrite -String.append_correct1 in H.
  { eapply get_StringOfZ_ne; [|done]. done. }
  apply StringOfZ_length.
Qed.
Lemma prod_ser_inl_ser_neq s s1 s2 :
  prod_ser_str s1 s2 ≠ inl_ser_str s.
Proof.
  rewrite -String.get_correct => H.
  specialize (H 0). simpl in H.
  rewrite -String.append_correct1 in H.
  { eapply get_StringOfZ_ne; [|done]. done. }
  apply StringOfZ_length.
Qed.
Lemma prod_ser_inr_ser_neq s s1 s2 :
  prod_ser_str s1 s2 ≠ inr_ser_str s.
Proof.
  rewrite -String.get_correct => H.
  specialize (H 0). simpl in H.
  rewrite -String.append_correct1 in H.
  { eapply get_StringOfZ_ne; [|done]. done. }
  apply StringOfZ_length.
Qed.

Lemma inl_ser_int_ser_neq z s :
  inl_ser_str s ≠ int_ser_str z.
Proof. rewrite -String.get_correct => H. specialize (H 0). simplify_eq. Qed.
Lemma inl_ser_string_ser_neq z s :
  inl_ser_str s ≠ string_ser_str z.
Proof. rewrite -String.get_correct => H. specialize (H 0). simplify_eq. Qed.
Lemma inl_ser_inr_ser_neq s s' :
  inl_ser_str s ≠ inr_ser_str s'.
Proof. rewrite -String.get_correct => H. specialize (H 0). simplify_eq. Qed.

Lemma inr_ser_int_ser_neq z s :
  inr_ser_str s ≠ int_ser_str z.
Proof. rewrite -String.get_correct => H. specialize (H 0). simplify_eq. Qed.
Lemma inr_ser_string_ser_neq z s :
  inr_ser_str s ≠ string_ser_str z.
Proof. rewrite -String.get_correct => H. specialize (H 0). simplify_eq. Qed.

Lemma int_ser_string_ser_neq z s :
  int_ser_str s ≠ string_ser_str z.
Proof. rewrite -String.get_correct => H. specialize (H 0). simplify_eq. Qed.

Create HintDb serialization.

#[global] Hint Resolve
  prod_ser_int_ser_neq prod_ser_string_ser_neq prod_ser_inl_ser_neq prod_ser_inr_ser_neq
  inl_ser_int_ser_neq inl_ser_string_ser_neq inl_ser_inr_ser_neq
  inr_ser_int_ser_neq inr_ser_string_ser_neq
  int_ser_string_ser_neq : serialization.

(** Recursively destructs the definition of the argument [H] of the shape [H : *_is_ser] *)
Ltac destruct_is_ser H :=
  match type of H with
  | s_is_ser _ _ _ => simpl in H; destruct_is_ser H
  | int_is_ser _ _ => destruct H as (?&?&?)
  | string_is_ser _ _ => inversion H; clear H
  | prod_is_ser _ _ _ _ =>
    destruct H as (?&?&?&?&?& ?Hp1 & ?Hp2 &?);
    destruct_is_ser Hp1; destruct_is_ser Hp2
  | sum_is_ser _ _ _ _ =>
    destruct H as (?&?& [(? & ?Hl & ?)|(? & ?Hr &?)]);
    [destruct_is_ser Hl | destruct_is_ser Hr]
  | _ => idtac
  end; simplify_eq.
