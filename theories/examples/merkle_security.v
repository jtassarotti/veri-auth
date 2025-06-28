From auth.rel_logic_bin Require Import fundamental.
From auth.examples Require Import authentikit_list_security.

Definition make_leaf : expr := λ: "s", "auth" #~ "tree" (rec_fold (InjL "s")).
Definition make_branch : expr := λ: "l" "r", "auth" #~ "tree" (rec_fold (InjR ("l", "r"))).

Definition evi_tree : expr := "Auth_mu" #~ ("Auth_sum" #~ #~ "Auth_string" ("Auth_pair" #~ #~ ("Auth_auth" #~) ("Auth_auth" #~))).
Definition evi_list : expr := "Auth_mu" #~ ("Auth_sum" #~ #~ "Auth_string" ("Auth_pair" #~ #~ "Auth_string" ("Auth_auth" #~))).

Section merkle.

  Definition t_tree {Θ} : type (Θ ▹ (⋆ ⇒ ⋆)%kind ▹ (⋆ ⇒ ⋆)%kind ▹ (⋆ ⇒ ⋆)%kind) ⋆ :=
    (μ: ⋆; (t_string + (var3 var0 * var3 var0)))%ty.

  Definition t_auth_tree {Θ} : type (Θ ▹ (⋆ ⇒ ⋆)%kind ▹ (⋆ ⇒ ⋆)%kind ▹ (⋆ ⇒ ⋆)%kind) ⋆ :=
    var2 t_tree.

  Definition t_evi_tree {Θ} : type (Θ ▹ (⋆ ⇒ ⋆)%kind ▹ (⋆ ⇒ ⋆)%kind ▹ (⋆ ⇒ ⋆)%kind) ⋆ :=
    var0 (t_tree)%ty.

  Lemma typed_evi_tree {Θ} Γ :
    Γ !! "Auth_mu" = Some (∀: ⋆ ⇒ ⋆, var1 (var0 (μ: ⋆; var1 var0)) → var1 (μ: ⋆; var1 var0))%ty →
    Γ !! "Auth_sum" = Some (∀: ⋆; ⋆, var2 var1 → var2 var0 → var2 (var1 + var0))%ty →
    Γ !! "Auth_string" = Some (var0 t_string) →
    Γ !! "Auth_pair" = Some (∀: ⋆; ⋆, var2 var1 → var2 var0 → var2 (var1 * var0))%ty →
    Γ !! "Auth_auth" = Some (∀: ⋆, var1 (var3 var0))%ty →
    (Θ ▹ (⋆ ⇒ ⋆)%kind ▹ (⋆ ⇒ ⋆)%kind ▹ (⋆ ⇒ ⋆)%kind) |ₜ Γ ⊢ₜ evi_tree : t_evi_tree.
  Proof.
    intros ?????.
    rewrite /evi_tree /t_evi_tree.
    eapply App_typed.
    - eapply TEquiv.
      { apply TEquiv_app; [reflexivity|].
        apply TEquiv_app; [reflexivity|].
        apply TEquiv_app; [reflexivity|].
        rewrite /t_tree. eapply TEquiv_eta. }
      eapply (TApp_typed' _ _ _ _ _ (Λ: (t_string + var3 var0 * var3 var0))).
      + by apply Var_typed.
      + t_simpl. done.
    - t_beta. eapply App_typed.
      + eapply App_typed.
        * eapply TApp_typed'.
          { eapply TApp_typed'; [by apply Var_typed|]. t_simpl. done. }
          t_simpl. done.
        * by eapply Var_typed.
      + eapply App_typed.
        * eapply App_typed.
          { eapply TApp_typed'.
            - eapply TApp_typed'; [by apply Var_typed|]. t_simpl. done.
            - t_simpl. done. }
          eapply TApp_typed'; [by eapply Var_typed|].
          t_simpl. done.
        * eapply TApp_typed'; [by apply Var_typed|]. t_simpl. done.
  Qed.

  Definition t_list {Θ} : type (Θ ▹ (⋆ ⇒ ⋆)%kind ▹ (⋆ ⇒ ⋆)%kind ▹ (⋆ ⇒ ⋆)%kind) ⋆ :=
    (μ: ⋆; (t_string + (t_string * var3 var0)))%ty.

  Definition t_evi_list {Θ} : type (Θ ▹ (⋆ ⇒ ⋆)%kind ▹ (⋆ ⇒ ⋆)%kind ▹ (⋆ ⇒ ⋆)%kind) ⋆ :=
    var0 (t_list)%ty.

  Lemma typed_evi_list {Θ} Γ :
    Γ !! "Auth_mu" = Some (∀: ⋆ ⇒ ⋆, var1 (var0 (μ: ⋆; var1 var0)) → var1 (μ: ⋆; var1 var0))%ty →
    Γ !! "Auth_sum" = Some (∀: ⋆; ⋆, var2 var1 → var2 var0 → var2 (var1 + var0))%ty →
    Γ !! "Auth_string" = Some (var0 t_string) →
    Γ !! "Auth_pair" = Some (∀: ⋆; ⋆, var2 var1 → var2 var0 → var2 (var1 * var0))%ty →
    Γ !! "Auth_auth" = Some (∀: ⋆, var1 (var3 var0))%ty →
    (Θ ▹ (⋆ ⇒ ⋆)%kind ▹ (⋆ ⇒ ⋆)%kind ▹ (⋆ ⇒ ⋆)%kind) |ₜ Γ ⊢ₜ evi_list : t_evi_list.
  Proof.
    intros ?????.
    rewrite /evi_list /t_evi_list.
    eapply App_typed.
    - eapply TEquiv.
      { apply TEquiv_app; [reflexivity|].
        apply TEquiv_app; [reflexivity|].
        apply TEquiv_app; [reflexivity|].
        eapply TEquiv_eta. }
      eapply (TApp_typed' _ _ _ _ _ (Λ: (t_string + t_string * var3 var0))).
      + by apply Var_typed.
      + t_simpl. done.
    - t_beta. eapply App_typed.
      + eapply App_typed.
        * eapply TApp_typed'.
          { eapply TApp_typed'; [by apply Var_typed|]. t_simpl. done. }
          t_simpl. done.
        * by eapply Var_typed.
      + eapply App_typed.
        * eapply App_typed.
          { eapply TApp_typed'.
            - eapply TApp_typed'; [by apply Var_typed|]. t_simpl. done.
            - t_simpl. done. }
          by eapply Var_typed.
        * eapply TApp_typed'; [by apply Var_typed|]. t_simpl. done.
  Qed.

  Lemma typed_make_leaf Θ Γ :
    Γ !! "auth" = Some (∀: ⋆, var1 var0 → var0 → var3 var0)%ty →
    Γ !! "tree" = Some t_evi_tree →
    (Θ ▹ (⋆ ⇒ ⋆)%kind ▹ (⋆ ⇒ ⋆)%kind ▹ (⋆ ⇒ ⋆)%kind) |ₜ Γ ⊢ₜ make_leaf : (t_string → t_auth_tree)%ty.
  Proof.
    intros ??.
    rewrite /t_auth_tree /t_tree /make_leaf.
    eapply Rec_typed. simpl_anon_binders.
    eapply App_typed.
    - eapply App_typed.
      + eapply TApp_typed'.
        * eapply Var_typed. rewrite lookup_insert_ne //.
        * t_simpl. done.
      + eapply Var_typed. rewrite lookup_insert_ne //.
    - rewrite /t_tree.
      eapply (TFold _ _ _ _ _ TElim_empty).
      t_simpl.
      econstructor.
      econstructor.
      rewrite lookup_insert //.
  Qed.

  Lemma typed_make_branch {Θ}  (Γ : stringmap (type _ ⋆)) :
    Γ !! "auth" = Some (∀: ⋆, var1 var0 → var0 → var3 var0)%ty →
    Γ !! "tree" = Some t_evi_tree →
    (Θ ▹ (⋆ ⇒ ⋆)%kind ▹ (⋆ ⇒ ⋆)%kind ▹ (⋆ ⇒ ⋆)%kind) |ₜ Γ ⊢ₜ make_branch : (t_auth_tree → t_auth_tree → t_auth_tree).
  Proof.
    intros ??.
    rewrite /make_branch.
    do 2 eapply Rec_typed. simpl_anon_binders.
    eapply App_typed.
    - eapply App_typed.
      + eapply TApp_typed'.
        * eapply Var_typed. rewrite ?lookup_insert_ne //.
        * t_simpl. done.
      + eapply Var_typed. rewrite ?lookup_insert_ne //.
    - eapply (TFold _ _ _ _ _ TElim_empty).
      t_simpl.
      econstructor.
      econstructor.
      + eapply Var_typed. rewrite lookup_insert_ne // lookup_insert //.
      + eapply Var_typed. rewrite lookup_insert //.
  Qed.

End merkle.
