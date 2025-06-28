From Coq.Unicode Require Import Utf8.
From auth Require Import binding.Core.
From auth Require Import binding.Properties.
From auth Require Import binding.TermSimpl.

Local Open Scope bind_scope.

Ltac auto_map_id :=
  match goal with
  | |- ?f ≡ ı → fmap ?f ?t = ?t =>
      let EQ := fresh "EQ"
      in intros EQ; destruct t; term_simpl;
         try ((progress f_equal; now eauto using @lift_id with typeclass_instances)
              || (f_equal; now apply EQ))
  end.

Ltac auto_map_comp :=
  match goal with
  | |- ?f ∘ ?g ≡ ?h → fmap ?f (fmap ?g ?t) = fmap ?h ?t =>
      let EQ := fresh "EQ"
      in intros EQ; destruct t; term_simpl;
         try ((progress f_equal; now eauto using @lift_comp with typeclass_instances)
              || (f_equal; now apply EQ))
  end.

Ltac auto_map_bind_pure :=
  match goal with
  | |- ?f ̂ ≡ ?g → fmap ?f ?t = bind ?g ?t =>
      let EQ := fresh "EQ"
      in intros EQ; destruct t; term_simpl;
         try ((progress f_equal; now eauto using @lift_of with typeclass_instances)
              || now apply EQ)
  end.

Ltac auto_map_bind_comm :=
  match goal with
  | |- ?g₂ ∘ ?f₂ ̂ ≡ ?f₁ ̂ ∘ ?g₁ → bind ?g₂ (fmap ?f₂ ?t) = fmap ?f₁ (bind ?g₁ ?t) =>
      let EQ := fresh "EQ"
      in intros EQ; destruct t; term_simpl;
         try ((progress f_equal; now eauto using @lift_comm with typeclass_instances)
              || rewrite map_to_bind; now apply EQ)
  end.

Ltac auto_bind_id :=
  match goal with
  | |- ?f ≡ ı → bind ?f ?t = ?t =>
      let EQ := fresh "EQ"
      in intros EQ; destruct t; term_simpl;
         try ((progress f_equal; now eauto using @lift_id with typeclass_instances)
              || now apply EQ)
  end.

Ltac auto_bind_comp :=
  match goal with
  | |- ?f ∘ ?g ≡ ?h → bind ?f (bind ?g ?t) = bind ?h ?t =>
      let EQ := fresh "EQ"
      in intros EQ; destruct t; term_simpl;
         try ((progress f_equal; now eauto using @lift_comp with typeclass_instances)
              || now apply EQ)
  end.
