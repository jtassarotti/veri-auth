From auth.prelude Require Import stdpp.
From auth.examples Require Import authentikit merkle.
From auth.heap_lang Require Import notation lib.list nondet_bool serialization.
From auth.typing Require Import types typing.
From stdpp Require Import fin_maps.

Definition evi_tree : expr := "Auth_mu" #~ ("Auth_sum" #~ #~ "Auth_string" ("Auth_pair" #~ #~ ("Auth_auth" #~) ("Auth_auth" #~))).

Definition make_leaf : expr := λ: "s", "auth" #~ "tree" (rec_fold (InjL "s")).
Definition make_branch : expr := λ: "l" "r", "auth" #~ "tree" (rec_fold (InjR ("l", "r"))).

Definition retrieve : expr :=
  rec: "retrieve" "path" "t" :=
    "bind" #~ #~ ("unauth" #~ "tree" "t")
      (λ: "t",
        let: "t" := rec_unfold "t" in
        match: "t" with
          InjL "s" =>
            match: "path_pop" "path" with
              NONE => "return" #~ (SOME "s")
            | SOME <> => "return" #~ (NONE)
            end
        | InjR "children" =>
            let, ("l", "r") := "children" in
            match: "path_pop" "path" with
              NONE => "return" #~ (NONE)
            | SOME "path" =>
                let, ("head", "tail") := "path" in
                match: "head" with
                  InjL <> => "retrieve" "tail" "l"
                | InjR <> => "retrieve" "tail" "r"
                end
            end
        end).

Definition update : expr :=
  rec: "update" "path" "v" "t" :=
    "bind" #~ #~ ("unauth" #~ "tree" "t")
      (λ: "t",
        let: "t" := rec_unfold "t" in
        match: "t" with
          InjL <> =>
            match: "path_pop" "path" with
              NONE => "return" #~ (SOME ("make_leaf" "v"))
            | SOME <> => "return" #~ (NONE)
            end
        | InjR "children" =>
            let, ("l", "r") := "children" in
            match: "path_pop" "path" with
              NONE => "return" #~ (NONE)
            | SOME "path" =>
                let, ("head", "tail") := "path" in
                match: "head" with
                  InjL <> =>
                    "bind" #~ #~ ("update" "tail" "v" "l")
                      (λ: "l",
                        match: "l" with
                          NONE => "return" #~ (NONE)
                        | SOME "l'" => "return" #~ (SOME ("make_branch" "l'" "r"))
                        end)
                | InjR <> =>
                    "bind" #~ #~ ("update" "tail" "v" "r")
                      (λ: "r",
                        match: "r" with
                          NONE => "return" #~ (NONE)
                        | SOME "r'" => "return" #~ (SOME ("make_branch" "l" "r'"))
                        end)
                end
            end
        end).

Definition merkle_module : val :=
  λ: "Authentikit" "path" "retrieve_magic",

    let, ("return", "bind", "Authenticatable") := "Authentikit" in
    let, ("_1", "_2", "_3", "path_pop") := "path" in
    unpack: "A" := "Authenticatable" in

    let, ("...", "Auth_string", "Auth_int", "auth", "unauth") := "A" in
    let, ("Auth_auth", "Auth_mu", "Auth_pair", "Auth_sum") := "..." in

    let: "tree" := evi_tree in
    
    let: "make_leaf" := make_leaf in
    let: "make_branch" := make_branch in

    let: "retrieve" := retrieve in

    let: "update" := update in

    ("make_leaf", "make_branch", "retrieve", "update", "retrieve_magic").


(** tree *)
Definition t_tree {Θ} : type (Θ ▹ ⋆ ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆))%kind ⋆ :=
  (μ: ⋆; (t_string + (var2 var0 * var2 var0)))%ty.
(** tree_auth  *)
Definition t_tree_auth {Θ} : type (Θ ▹ ⋆ ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆))%kind ⋆ :=
  var1 t_tree.
(** string -> tree_auth *)
Definition t_make_leaf {Θ} : type (Θ ▹ ⋆ ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆))%kind ⋆ :=
  t_string → t_tree_auth.
(** tree_auth -> tree_auth -> tree_auth *)
Definition t_make_branch {Θ} : type (Θ ▹ ⋆ ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆))%kind ⋆ :=
  t_tree_auth → t_tree_auth → t_tree_auth.
(** path -> tree_auth -> string option authenticated_computation *)
Definition t_retrieve {Θ} : type (Θ ▹ ⋆ ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆))%kind ⋆ :=
  var2 → t_tree_auth → var0 (t_option t_string).
(** path -> t_string -> tree_auth -> tree_auth option authenticated_computation *)
Definition t_update {Θ} : type (Θ ▹ ⋆ ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆))%kind ⋆ :=
  var2 → t_string → t_tree_auth → var0 (t_option t_tree_auth).

Definition merkle_module_type_open {Θ} : type (Θ ▹ ⋆ ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆))%kind ⋆ :=
  t_make_leaf * t_make_branch * t_retrieve * t_update * t_retrieve.

Definition merkle_module_type : type (ε ▹ ⋆ ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆))%kind ⋆ :=
  (Authentikit_func var1 var0 → t_path → t_retrieve → merkle_module_type_open)%ty.

Definition t_tree' {Θ} : type (Θ ▹ ⋆ ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆))%kind ⋆ :=
  (μ: ⋆; (t_string + (var3 var0 * var3 var0)))%ty.

Definition t_tree_auth' {Θ} : type (Θ ▹ ⋆ ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆))%kind ⋆ :=
  var2 t_tree'.

Definition t_evi_tree' {Θ} : type (Θ ▹ ⋆ ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆))%kind ⋆ :=
  (var0 t_tree')%ty.

Definition t_make_leaf' {Θ} : type (Θ ▹ ⋆ ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆))%kind ⋆ :=
  t_string → t_tree_auth'.

Definition t_make_branch' {Θ} : type (Θ ▹ ⋆ ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆))%kind ⋆ :=
  t_tree_auth' → t_tree_auth' → t_tree_auth'.

Definition t_retrieve' {Θ} : type (Θ ▹ ⋆ ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆))%kind ⋆ :=
  var3 → t_tree_auth' → var1 (t_option t_string).

Definition t_update' {Θ} : type (Θ ▹ ⋆ ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆))%kind ⋆ :=
  var3 → t_string → t_tree_auth' → var1 (t_option t_tree_auth').

Definition t_auth' {Θ} : type (Θ ▹ ⋆ ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆))%kind ⋆ :=
  (∀: ⋆, var1 var0 → var0 → var3 var0).

Definition t_bind' {Θ} : type (Θ ▹ ⋆ ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆))%kind ⋆ :=
  (∀: ⋆; ⋆, var3 var1 → (var1 → var3 var0) → var3 var0).

Definition t_return' {Θ} : type (Θ ▹ ⋆ ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆))%kind ⋆ :=
  (∀: ⋆, var0 → var2 var0).

Definition t_unauth' {Θ} : type (Θ ▹ ⋆ ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆))%kind ⋆ :=
  (∀: ⋆, var1 var0 → var3 var0 → var2 var0).
  
Lemma typed_evi_tree {Θ} Γ :
  Γ !! "Auth_mu" = Some (∀: ⋆ ⇒ ⋆, var1 (var0 (μ: ⋆; var1 var0)) → var1 (μ: ⋆; var1 var0))%ty →
  Γ !! "Auth_sum" = Some (∀: ⋆; ⋆, var2 var1 → var2 var0 → var2 (var1 + var0))%ty →
  Γ !! "Auth_string" = Some (var0 t_string) →
  Γ !! "Auth_pair" = Some (∀: ⋆; ⋆, var2 var1 → var2 var0 → var2 (var1 * var0))%ty →
  Γ !! "Auth_auth" = Some (∀: ⋆, var1 (var3 var0))%ty →
  (Θ ▹ ⋆ ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆))%kind |ₜ Γ ⊢ₜ evi_tree : t_evi_tree'.
Proof.
  intros ?????.
  rewrite /evi_tree /t_evi_tree'.
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

Lemma typed_make_leaf Θ Γ :
  Γ !! "auth" = Some t_auth' →
  Γ !! "tree" = Some t_evi_tree' →
  (Θ ▹ ⋆ ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆))%kind |ₜ Γ ⊢ₜ make_leaf : t_make_leaf'.
Proof.
  intros ??.
  rewrite /t_evi_tree' /t_tree_auth' /t_tree' /make_leaf.
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

Lemma typed_make_branch {Θ} (Γ : stringmap (type _ ⋆)) :
  Γ !! "auth" = Some t_auth' →
  Γ !! "tree" = Some t_evi_tree' →
  (Θ ▹ ⋆ ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆))%kind |ₜ Γ ⊢ₜ make_branch : t_make_branch'.
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

Lemma typed_retrieve {Θ} (Γ : stringmap (type _ ⋆)) :
  Γ !! "auth" = Some t_auth' →
  Γ !! "tree" = Some t_evi_tree' →
  Γ !! "return" = Some t_return' →
  Γ !! "bind" = Some t_bind' →
  Γ !! "unauth" = Some t_unauth' →
  Γ !! "path_pop" = Some (var3 → t_option ((() + ()) * var3))%ty →
  (Θ ▹ ⋆ ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆))%kind |ₜ Γ ⊢ₜ retrieve : t_retrieve'.
Proof.
  intros ??????.
  rewrite /retrieve.
  do 2 eapply Rec_typed. simpl_anon_binders.
  eapply App_typed.
  - eapply App_typed.
    + eapply TApp_typed'.
      * eapply TApp_typed'.
        { eapply Var_typed. rewrite ?lookup_insert_ne //. }
        done.
      * done.
    + eapply App_typed.
      * eapply App_typed.
        { eapply TApp_typed'.
          { eapply Var_typed. rewrite ?lookup_insert_ne //. }
          t_simpl. done. }
        eapply Var_typed. rewrite ?lookup_insert_ne //.
      * eapply Var_typed. rewrite lookup_insert //.
  - eapply Rec_typed. simpl_anon_binders.
    eapply App_typed; last first.
    { eapply (TUnfold _ _ _ _ _ TElim_empty).
      eapply Var_typed. rewrite lookup_insert //. }
    t_simpl.
    eapply Rec_typed. simpl_anon_binders.
    eapply Case_typed.
    { eapply Var_typed. rewrite lookup_insert //. }
    + eapply Rec_typed. simpl_anon_binders.
      eapply Case_typed.
      { eapply App_typed.
        - eapply Var_typed. rewrite ?lookup_insert_ne //.
        - eapply Var_typed. do 5 rewrite lookup_insert_ne //.
          rewrite lookup_insert //. }
      * eapply Rec_typed. simpl_anon_binders.
        eapply App_typed; last first.
        { eapply InjR_typed.
          eapply Var_typed. rewrite lookup_insert //. }
        eapply TApp_typed'.
        { eapply Var_typed. rewrite ?lookup_insert_ne //. }
        done.
      * eapply Rec_typed. simpl_anon_binders.
        eapply App_typed; [|typecheck].
        eapply TApp_typed'.
        { eapply Var_typed. rewrite ?lookup_insert_ne //. }
        done.
    + eapply Rec_typed. simpl_anon_binders.
      eapply App_typed; last first.
      { eapply Var_typed. rewrite lookup_insert //. }
      eapply Rec_typed. simpl_anon_binders.
      eapply App_typed; last first.
      { eapply Fst_typed.
        eapply Var_typed. rewrite lookup_insert //. }
      eapply Rec_typed. simpl_anon_binders.
      eapply App_typed; last first.
      { eapply Snd_typed.
        eapply Var_typed. rewrite lookup_insert_ne //. rewrite lookup_insert //. }
      eapply Rec_typed. simpl_anon_binders.
      eapply Case_typed.
      { eapply App_typed.
        { eapply Var_typed. rewrite ?lookup_insert_ne //. }
        { eapply Var_typed. do 8 rewrite lookup_insert_ne //.
          rewrite lookup_insert //. }}
      * eapply Rec_typed. simpl_anon_binders.
        eapply App_typed; last first.
        { eapply InjL_typed. typecheck. }
        eapply TApp_typed'.
        { eapply Var_typed. rewrite ?lookup_insert_ne //. }
        done.
      * eapply Rec_typed. simpl_anon_binders.
        eapply App_typed; last first.
        { eapply Var_typed. rewrite lookup_insert //. }
        eapply Rec_typed. simpl_anon_binders.
        eapply App_typed; last first.
        { eapply Fst_typed.
          eapply Var_typed. rewrite lookup_insert //. }
        eapply Rec_typed. simpl_anon_binders.
        eapply App_typed; last first.
        { eapply Snd_typed.
          eapply Var_typed. rewrite lookup_insert_ne //. rewrite lookup_insert //. }
        eapply Rec_typed. simpl_anon_binders.
        eapply Case_typed.
        { eapply Var_typed. rewrite lookup_insert_ne //. rewrite lookup_insert //. }
        -- eapply Rec_typed. simpl_anon_binders.
           eapply App_typed; last first.
           { eapply Var_typed. do 5 rewrite lookup_insert_ne //.
             rewrite lookup_insert //. }
           eapply App_typed; last first.
           { eapply Var_typed. rewrite lookup_insert //. }
           eapply Var_typed. do 11 rewrite lookup_insert_ne //.
           rewrite lookup_insert //.
        -- eapply Rec_typed. simpl_anon_binders.
           eapply App_typed; last first.
           { eapply Var_typed. do 4 rewrite lookup_insert_ne //.
             rewrite lookup_insert //. }
           eapply App_typed; last first.
           { eapply Var_typed. rewrite lookup_insert //. }
           eapply Var_typed. do 11 rewrite lookup_insert_ne //.
           rewrite lookup_insert //.
Qed.           

Lemma typed_update {Θ} (Γ : stringmap (type _ ⋆)) :
  Γ !! "auth" = Some t_auth' →
  Γ !! "tree" = Some t_evi_tree' →
  Γ !! "return" = Some t_return' →
  Γ !! "bind" = Some t_bind' →
  Γ !! "unauth" = Some t_unauth' →
  Γ !! "make_leaf" = Some t_make_leaf' →
  Γ !! "make_branch" = Some t_make_branch' →
  Γ !! "path_pop" = Some (var3 → t_option ((() + ()) * var3))%ty →
  (Θ ▹ ⋆ ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆))%kind |ₜ Γ ⊢ₜ update : t_update'.
Proof.
  intros ????????.
  rewrite /retrieve.
  do 3 eapply Rec_typed. simpl_anon_binders.
  eapply App_typed.
  - eapply App_typed.
    + eapply TApp_typed'.
      * eapply TApp_typed'.
        { eapply Var_typed. rewrite ?lookup_insert_ne //. }
        done.
      * done.
    + eapply App_typed.
      * eapply App_typed.
        { eapply TApp_typed'.
          { eapply Var_typed. rewrite ?lookup_insert_ne //. }
          t_simpl. done. }
        eapply Var_typed. rewrite ?lookup_insert_ne //.
      * eapply Var_typed. rewrite lookup_insert //.
  - eapply Rec_typed. simpl_anon_binders.
    eapply App_typed; last first.
    { eapply (TUnfold _ _ _ _ _ TElim_empty).
      eapply Var_typed. rewrite lookup_insert //. }
    t_simpl.
    eapply Rec_typed. simpl_anon_binders.
    eapply Case_typed.
    { eapply Var_typed. rewrite lookup_insert //. }
    + eapply Rec_typed. simpl_anon_binders.
      eapply Case_typed.
      { eapply App_typed.
        - eapply Var_typed. rewrite ?lookup_insert_ne //.
        - eapply Var_typed. do 5 rewrite lookup_insert_ne //.
          rewrite lookup_insert //. }
      * eapply Rec_typed. simpl_anon_binders.
        eapply App_typed; last first.
        { eapply InjR_typed.
          eapply App_typed; last first.
          { eapply Var_typed.
            do 3 rewrite lookup_insert_ne //. rewrite lookup_insert //. }
          eapply Var_typed. rewrite ?lookup_insert_ne //. }
        eapply TApp_typed'.
        { eapply Var_typed. rewrite ?lookup_insert_ne //. }
        done.
      * eapply Rec_typed. simpl_anon_binders.
        eapply App_typed; [|typecheck].
        eapply TApp_typed'.
        { eapply Var_typed. rewrite ?lookup_insert_ne //. }
        done.
    + eapply Rec_typed. simpl_anon_binders.
      eapply App_typed; last first.
      { eapply Var_typed. rewrite lookup_insert //. }
      eapply Rec_typed. simpl_anon_binders.
      eapply App_typed; last first.
      { eapply Fst_typed.
        eapply Var_typed. rewrite lookup_insert //. }
      eapply Rec_typed. simpl_anon_binders.
      eapply App_typed; last first.
      { eapply Snd_typed.
        eapply Var_typed. rewrite lookup_insert_ne //. rewrite lookup_insert //. }
      eapply Rec_typed. simpl_anon_binders.
      eapply Case_typed.
      { eapply App_typed.
        { eapply Var_typed. rewrite ?lookup_insert_ne //. }
        { eapply Var_typed. do 9 rewrite lookup_insert_ne //.
          rewrite lookup_insert //. }}
      * eapply Rec_typed. simpl_anon_binders.
        eapply App_typed; last first.
        { eapply InjL_typed. typecheck. }
        eapply TApp_typed'.
        { eapply Var_typed. rewrite ?lookup_insert_ne //. }
        done.
      * eapply Rec_typed. simpl_anon_binders.
        eapply App_typed; last first.
        { eapply Var_typed. rewrite lookup_insert //. }
        eapply Rec_typed. simpl_anon_binders.
        eapply App_typed; last first.
        { eapply Fst_typed.
          eapply Var_typed. rewrite lookup_insert //. }
        eapply Rec_typed. simpl_anon_binders.
        eapply App_typed; last first.
        { eapply Snd_typed.
          eapply Var_typed. rewrite lookup_insert_ne //. rewrite lookup_insert //. }
        eapply Rec_typed. simpl_anon_binders.
        eapply Case_typed.
        { eapply Var_typed. rewrite lookup_insert_ne //. rewrite lookup_insert //. }
        -- eapply Rec_typed. simpl_anon_binders.
           eapply App_typed; last first.
           { eapply Rec_typed. simpl_anon_binders.
             eapply Case_typed.
             { eapply Var_typed. rewrite lookup_insert //. }
             - eapply Rec_typed. simpl_anon_binders.
               eapply App_typed.
               { eapply TApp_typed'.
                 { eapply Var_typed. rewrite ?lookup_insert_ne //. }
                 done. }
               typecheck. 
             - eapply Rec_typed. simpl_anon_binders.
               eapply App_typed.
               { eapply TApp_typed'.
                 { eapply Var_typed. rewrite ?lookup_insert_ne //. }
                 t_simpl. done. }
               eapply InjR_typed.
               eapply App_typed; last first.
               { eapply Var_typed. do 6 rewrite lookup_insert_ne //.
                 rewrite lookup_insert //. }
               eapply App_typed; last first.
               { eapply Var_typed. rewrite lookup_insert //. }
               eapply Var_typed. rewrite ?lookup_insert_ne //. }
           eapply App_typed.
           { eapply TApp_typed'.
             { eapply TApp_typed'.
               { eapply Var_typed. rewrite ?lookup_insert_ne //. }
               done. }
             t_simpl. done. }
           eapply App_typed; last first.
           { eapply Var_typed. do 5 rewrite lookup_insert_ne //.
             rewrite lookup_insert //. }
           eapply App_typed; last first.
           { eapply Var_typed. do 11 rewrite lookup_insert_ne //.
             rewrite lookup_insert //. }
           eapply App_typed; last first.
           { eapply Var_typed. rewrite lookup_insert //. }
           eapply Var_typed. do 12 rewrite lookup_insert_ne //.
           rewrite lookup_insert //.
        -- eapply Rec_typed. simpl_anon_binders.
           eapply App_typed; last first.
           { eapply Rec_typed. simpl_anon_binders.
             eapply Case_typed.
             { eapply Var_typed. rewrite lookup_insert //. }
             - eapply Rec_typed. simpl_anon_binders.
               eapply App_typed.
               { eapply TApp_typed'.
                 { eapply Var_typed. rewrite ?lookup_insert_ne //. }
                 done. }
               typecheck. 
             - eapply Rec_typed. simpl_anon_binders.
               eapply App_typed.
               { eapply TApp_typed'.
                 { eapply Var_typed. rewrite ?lookup_insert_ne //. }
                 t_simpl. done. }
               eapply InjR_typed.
               eapply App_typed; last first.
               { eapply Var_typed. rewrite lookup_insert //. }
               eapply App_typed; last first.
               { eapply Var_typed. do 7 rewrite lookup_insert_ne //.
                 rewrite lookup_insert //. }
               eapply Var_typed. rewrite ?lookup_insert_ne //. }
           eapply App_typed.
           { eapply TApp_typed'.
             { eapply TApp_typed'.
               { eapply Var_typed. rewrite ?lookup_insert_ne //. }
               done. }
             t_simpl. done. }
           eapply App_typed; last first.
           { eapply Var_typed. do 4 rewrite lookup_insert_ne //.
             rewrite lookup_insert //. }
           eapply App_typed; last first.
           { eapply Var_typed. do 11 rewrite lookup_insert_ne //.
             rewrite lookup_insert //. }
           eapply App_typed; last first.
           { eapply Var_typed. rewrite lookup_insert //. }
           eapply Var_typed. do 12 rewrite lookup_insert_ne //.
           rewrite lookup_insert //.
Qed.           
           
Lemma merkle_module_typed Γ :
  (ε ▹ ⋆ ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆))%kind |ₜ Γ ⊢ₜ merkle_module : merkle_module_type.
Proof.
  rewrite /merkle_module /merkle_module_type /merkle_module_type_open /Authentikit_func.
  do 5 t_beta. 
  eapply Val_typed. eapply Rec_val_typed.
  eapply Rec_typed. eapply Rec_typed. simpl_anon_binders.
  eapply App_typed; [|typecheck].
  eapply Rec_typed. simpl_anon_binders.
  eapply App_typed; [|typecheck]. eapply Rec_typed.
  simpl_anon_binders. eapply App_typed; [|typecheck].
  eapply Rec_typed. simpl_anon_binders.
  do 6 (eapply App_typed; [|typecheck]; eapply Rec_typed).
  eapply TUnpack; [typecheck|].
  simpl_anon_binders. 
  do 11 (eapply App_typed; [|typecheck]; eapply Rec_typed).
  simpl_anon_binders.
  eapply App_typed; last first.
  eapply typed_evi_tree; done.
  eapply Rec_typed. simpl_anon_binders.

  eapply App_typed; last first.
  eapply typed_make_leaf; done.
  eapply Rec_typed. simpl_anon_binders.

  eapply App_typed; last first.
  eapply typed_make_branch; done.
  eapply Rec_typed. simpl_anon_binders.

  eapply App_typed; last first.
  eapply typed_retrieve; done.
  eapply Rec_typed. simpl_anon_binders.

  eapply App_typed; last first.
  eapply typed_update; done.
  eapply Rec_typed. simpl_anon_binders.

  typecheck.
Qed.
  
From auth.examples Require Import authentikit_list_security merkle_retrieve_security.

Section security_semantic.
  Context `{!authG Σ}.

  Lemma refines_merkle_module_security Δ :
    ⊢ {(ε ▹ ⋆ ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆))%kind; merkle_retrieve_ctx Δ; ∅}
      ⊨ merkle_module v_Authentikit path v_retrieve ≤log≤
        merkle_module i_Authentikit path i_retrieve : merkle_module_type_open.
  Proof.
    iIntros (?) "#H". iIntros (??) "Hi".
    rewrite ![subst_map _ _]/=.
    rewrite /merkle_module_type_open.
    iApply refines_app; last first.
    { done. }
    { iApply refines_retrieve. done. }
    iApply refines_app; last first.
    { iApply refines_path. done. }
        
    assert ((⟦ t_path ⟧ (merkle_retrieve_ctx Δ) → ⟦ merkle.t_retrieve ⟧ (merkle_retrieve_ctx Δ) → ⟦ t_make_leaf * t_make_branch * t_retrieve * t_update * t_retrieve ⟧ (merkle_retrieve_ctx Δ))%lrel = ⟦ t_path → merkle.t_retrieve → t_make_leaf * t_make_branch * t_retrieve * t_update * t_retrieve ⟧ (merkle_retrieve_ctx Δ) ).
    { rewrite interp_unseal //. }
    rewrite H.

    iApply refines_app; last first.
    { iIntros (??) "Hi".
      wp_pures. iModIntro. iFrame.
      iApply (refines_authentikit_func _ (ext Δ lrel_path)). }

    assert ((⟦ Authentikit_func var1 var0 ⟧ (merkle_retrieve_ctx Δ) → ⟦ t_path → merkle.t_retrieve → t_make_leaf * t_make_branch * t_retrieve * t_update * t_retrieve ⟧ (merkle_retrieve_ctx Δ))%lrel = ⟦ Authentikit_func var1 var0 → t_path → merkle.t_retrieve → t_make_leaf * t_make_branch * t_retrieve * t_update * t_retrieve ⟧ (merkle_retrieve_ctx Δ)).
    { rewrite interp_unseal //. }

    rewrite H0.
    iApply refines_typed.
    apply merkle_module_typed.
  Qed.
End security_semantic.
  
From auth.examples Require Import authentikit_list_correctness merkle_retrieve_correctness.

Section correctness_semantic.
  Context `{!authG Σ}.

  Lemma refines_merkle_module_correctness Δ :
    ⊢ {(ε ▹ ⋆ ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆))%kind; merkle_retrieve_ctx Δ; ∅}
      ⊨ merkle_module p_Authentikit path p_retrieve ≤log≤
        merkle_module v_Authentikit path v_retrieve ≤log≤
        merkle_module i_Authentikit path i_retrieve : merkle_module_type_open.
  Proof.
    iIntros (?) "#H". iIntros (????) "Hv Hi".
    rewrite ![subst_map _ _]/=.
    rewrite /merkle_module_type_open.
    iApply (refines_app with "[] [] [Hv]"); last first.
    { done. } { done. }
    { iApply refines_retrieve. done. }
    iApply refines_app; last first.
    { iApply refines_path. done. }
        
    assert ((⟦ t_path ⟧ (merkle_retrieve_ctx Δ) → ⟦ merkle.t_retrieve ⟧ (merkle_retrieve_ctx Δ) → ⟦ t_make_leaf * t_make_branch * t_retrieve * t_update * t_retrieve ⟧ (merkle_retrieve_ctx Δ))%lrel = ⟦ t_path → merkle.t_retrieve → t_make_leaf * t_make_branch * t_retrieve * t_update * t_retrieve ⟧ (merkle_retrieve_ctx Δ) ).
    { f_equal. }
    rewrite H.

    iApply refines_app; last first.
    { iIntros (????) "Hv Hi".
      wp_pures. iModIntro. iFrame.
      iApply (refines_authentikit_func _ (ext Δ lrel_path)). }

    assert ((⟦ Authentikit_func var1 var0 ⟧ (merkle_retrieve_ctx Δ) → ⟦ t_path → merkle.t_retrieve → t_make_leaf * t_make_branch * t_retrieve * t_update * t_retrieve ⟧ (merkle_retrieve_ctx Δ))%lrel = ⟦ Authentikit_func var1 var0 → t_path → merkle.t_retrieve → t_make_leaf * t_make_branch * t_retrieve * t_update * t_retrieve ⟧ (merkle_retrieve_ctx Δ)).
    { f_equal. }

    rewrite H0.
    iApply refines_typed.
    apply merkle_module_typed.
  Qed.
End correctness_semantic.

