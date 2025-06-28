From iris.proofmode Require Import proofmode.
From iris.algebra Require Export auth gset_bij.
From iris.base_logic.lib Require Export own gset_bij.
From iris.prelude Require Import options.
From auth.prelude Require Export hash.

Section gset_bij_algebra.
  Context `{Countable A, Countable B}.
  Implicit Types (a:A) (b:B).
  Implicit Types (L : gset (A*B)).
  Implicit Types dq : dfrac.

  Lemma gset_bij_auth_elem_op_in dq L a b :
    (a, b) ∈ L →
    gset_bij_elem a b ⋅ gset_bij_auth dq L ≡ gset_bij_auth dq L.
  Proof.
    intros ?.
    rewrite /gset_bij_auth /gset_bij_elem.
    rewrite comm -assoc.
    rewrite -view_frag_op.
    assert ((L ⋅ {[(a, b)]}) = L) as Heq by set_solver.
    rewrite Heq //.
  Qed.

End gset_bij_algebra.

Section gset_bij.
  Context `{gset_bijG Σ A B}.
  Implicit Types (L : gset (A * B)) (a : A) (b : B).

  Lemma gset_bij_own_elem_get' {γ q L} a b :
    (a, b) ∈ L →
    gset_bij_own_auth γ q L -∗ gset_bij_own_elem γ a b ∗ gset_bij_own_auth γ q L.
  Proof.
    intros. rewrite gset_bij_own_auth_eq gset_bij_own_elem_eq.
    rewrite -own_op.
    iApply own_mono.
    rewrite gset_bij_auth_elem_op_in //.
  Qed.

End gset_bij.

Section hash_theory.
  Context `{!gset_bijG Σ string string}.

  Definition hashes_auth γ (hs : gset string) : iProp Σ :=
    gset_bij_own_auth γ (DfracOwn 1) (set_map (λ s, (s, hash s)) hs).

  Definition hashed γ (s : string) : iProp Σ :=
    gset_bij_own_elem γ s (hash s).

  Definition collides (s : string) (hs : gset string) :=
    ∃ s', s' ∈ hs ∧ collision s s'.

  Definition has_collision (hs : gset string) :=
    set_Exists (λ s1, set_Exists (λ s2, collision s1 s2) hs) hs.

  Lemma collides_has_collision (s : string) (hs : gset string) :
    collides s hs → has_collision (hs ∪ {[s]}).
  Proof. set_solver. Qed.

  Lemma hashes_auth_update γ (hs : gset string) (s : string):
    hashes_auth γ hs ==∗ ⌜collides s hs⌝ ∨ hashes_auth γ ({[s]} ∪ hs) ∗ hashed γ s.
  Proof.
    iIntros "Hhs".
    destruct (decide (s ∈ hs)).
    { iDestruct (gset_bij_own_elem_get' s (hash s) with "Hhs") as "[? ?]".
      { set_solver. }
      iRight. iFrame.
      assert ({[s]} ∪ hs = hs) as -> by set_solver.
      by iFrame. }
    destruct (decide (collides s hs)) as [|Hcoll]; [by iLeft|iRight].
    iMod (gset_bij_own_extend with "Hhs") as "[? $]".
    { intros ? (? & ? & ?)%elem_of_map. simplify_eq.
      apply Hcoll. eexists. split; [done|]. split; [|done]. set_solver. }
    { intros ? (? & ? & ?)%elem_of_map. simplify_eq.
      apply Hcoll. eexists. split; [done|]. split; [|done]. set_solver. }
    rewrite /hashes_auth.
    rewrite set_map_union_L set_map_singleton_L //.
  Qed.

  Lemma hashed_inj_or_coll γ s1 s2 :
    hashed γ s1 -∗ hashed γ s2 -∗ ⌜collision s1 s2⌝ -∗ False.
  Proof.
    iIntros "Hs1 Hs2".
    iDestruct (gset_bij_own_elem_agree with "Hs1 Hs2") as %?.
    iIntros ([? ?]).
    naive_solver.
  Qed.

End hash_theory.

Lemma hash_auth_alloc `{!gset_bijG Σ string string} hs :
  ¬ has_collision hs →
  ⊢ |==> ∃ (γ : gname), hashes_auth γ hs.
Proof.
  iIntros (Hc).
  iMod gset_bij_own_alloc as (γ) "[$ ?]"; [|done].
  intros a b (s & [= -> ->] & Hs)%elem_of_map; split; [set_solver|].
  intros a' (s' & [= -> Hss] & Hs')%elem_of_map.
  destruct (decide (s = s')); [done|].
  exfalso. apply Hc.
  exists s. split; [done|].
  exists s'. done.
Qed.
