From auth.typing Require Import types typing.

(** * The AUTHENTIKIT module type *)

(** module type AUTHENTIKIT = sig
    type 'a auth
    type 'a authenticated_computation
    val return : 'a -> 'a authenticated_computation
    val bind : 'a authenticated_computation -> ('a -> 'b authenticated_computation) ->
               'b authenticated_computation

    module Authenticatable : sig
      type 'a evidence
      val auth : 'a auth evidence
      val pair : 'a evidence -> 'b evidence -> ('a * 'b) evidence
      val sum : 'a evidence -> 'b evidence -> [`left of 'a | `right of 'b] evidence
      val string : string evidence
      val int : int evidence
    end

    val auth : 'a Authenticatable.evidence -> 'a -> 'a auth
    val unauth : 'a Authenticatable.evidence -> 'a auth -> 'a authenticated_computation
  end *)

Definition Authenticatable {Θ} : type (Θ ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆))%kind ⋆ :=
  (∃: (* evidence : *) ⋆ ⇒ ⋆,

      ((* Authenticatable.auth   : *) ∀: ⋆, var1 (var3 var0)) *
      ((* Authenticatable.mu     : *) ∀: ⋆ ⇒ ⋆, var1 (var0 (μ: ⋆; var1 var0)) → var1 (μ: ⋆; var1 var0)) *      
      ((* Authenticatable.pair   : *) ∀: ⋆; ⋆, var2 var1 → var2 var0 → var2 (var1 * var0)) *
      ((* Authenticatable.sum    : *) ∀: ⋆; ⋆, var2 var1 → var2 var0 → var2 (var1 + var0)) *
      ((* Authenticatable.string : *) var0 t_string) *
      ((* Authenticatable.int    : *) var0 t_nat) *

      ((* auth   : *) ∀: ⋆, var1 var0 → var0 → var3 var0) *
      ((* unauth : *) ∀: ⋆, var1 var0 → var3 var0 → var2 var0))%ty  .

Definition Authentikit_func {Θ} : type Θ ((⋆ ⇒ ⋆) ⇒ (⋆ ⇒ ⋆) ⇒ ⋆) :=
  (Λ: (* auth : *)
   Λ: (* authenticated_computation : *)

     ((* return : *) ∀: ⋆, var0 → var1 var0) *
     ((* bind   : *) ∀: ⋆; ⋆, var2 var1 → (var1 → var2 var0) → var2 var0) *
     Authenticatable
  )%ty.

Definition Authentikit_func_eq {Θ} : type Θ ((⋆ ⇒ ⋆) ⇒ (⋆ ⇒ ⋆) ⇒ ⋆) :=
  (Λ: (* auth : *)
   Λ: (* authenticated_computation : *)

     ((* return : *) ∀: ⋆, var0 → var1 var0) *
     ((* bind   : *) ∀: ⋆; ⋆, var2 var1 → (var1 → var2 var0) → var2 var0) *
     ((* eqauth : *) ∀: ⋆, var2 var0 → var2 var0 → var1 t_bool) *
     Authenticatable
  )%ty.

Definition Authentikit {Θ} : type Θ ⋆ :=
  (∃: (* auth : *) ⋆ ⇒ ⋆;
      (* authenticated_computation : *) ⋆ ⇒ ⋆,
     Authentikit_func var1 var0)%ty.

Definition Authentikit_eq {Θ} : type Θ ⋆ :=
  (∃: (* auth : *) ⋆ ⇒ ⋆;
      (* authenticated_computation : *) ⋆ ⇒ ⋆,
     Authentikit_func_eq var1 var0)%ty.

(** ** Ideal  *)
(** type 'a auth = 'a *)
(** type 'a authenticated_computation = unit → 'a *)
(** type 'a evidence = unit *)

Definition i_return : val := Λ: λ: "a" <>, "a".
Definition i_bind : val :=
  Λ: Λ: λ: "a" "f" <>, "f" ("a" #()) #().
Definition i_Auth_auth : val := Λ: #().
Definition i_Auth_mu : val := Λ: λ: <>, #() .
Definition i_Auth_pair : val := Λ: Λ: λ: <> <>, #().
Definition i_Auth_sum : val := Λ: Λ: λ: <> <>, #().
Definition i_Auth_string : val := λ: <>, #().
Definition i_Auth_int : val := λ: <>, #().
Definition i_auth : val := Λ: λ: <> "a", "a".
Definition i_unauth : val :=
  Λ: λ: <> "a" <>, "a".

Definition i_Authenticable : val :=
  (i_Auth_auth, i_Auth_mu, i_Auth_pair, i_Auth_sum, i_Auth_string, i_Auth_int, i_auth, i_unauth).
Definition i_Authentikit : val := (i_return, i_bind, i_Authenticable).

Definition i_eqauth : val := Λ: λ: "a" "b" <>, "a" = "b".
             
Definition i_Authenitkit_eq : val := (i_return, i_bind, i_eqauth, i_Authenticable).

Definition i_run : val :=
  Λ: λ: "c", "c" #().
