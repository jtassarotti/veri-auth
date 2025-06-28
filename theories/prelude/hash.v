From stdpp Require Export strings gmap.

Parameter hash : string → string.

Definition collision (s1 s2 : string) := s1 ≠ s2 ∧ hash s1 = hash s2.

#[global] Instance collision_dec : RelDecision collision.
Proof. intros s1 s2. unfold collision. apply _. Qed.

Lemma not_collision s1 s2 :
  ¬ collision s1 s2 → s1 = s2 ∨ hash s1 ≠ hash s2.
Proof.
  intros [? | ?]%not_and_l; [|auto].
  destruct (decide (s1 = s2)); auto.
Qed.
