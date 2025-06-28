From stdpp Require Import base. 

Class Inject (A B : Type) := {
  inject : A → B;
  inject_inj : Inj (=) (=) inject;
}.

Notation "$ x" := (inject x) (at level 8).
#[global] Existing Instance inject_inj.
