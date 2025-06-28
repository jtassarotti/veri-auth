From auth.heap_lang.lib Require Export serialization.
From auth.typing Require Export types typing.
From auth.examples Require Export authenticatable_base.

(** type 'a evidence = {serialize : 'a -> string; deserialize : () -> ()} *)
Definition p_Auth_auth : val :=
  Λ: (λ: "v", #"s_" ^ Snd "v", λ: <>, #()).
Definition p_Auth_mu : val :=
  Λ: λ: "ser", (λ: "s", (Fst "ser") "s", λ: <>, (Snd "ser") #()).
Definition p_Auth_pair : val :=
  Λ: Λ: λ: "A" "B", (prod_ser (Fst "A") (Fst "B"), λ: <>, Snd "A" #();; Snd "B" #()).
Definition p_Auth_sum : val :=
  Λ: Λ: λ: "A" "B", (sum_ser (Fst "A") (Fst "B"), λ: <>, Snd "A" #();; Snd "B" #()).
Definition p_Auth_string : val := (string_ser, λ: <>, #()).
Definition p_Auth_int : val := (int_ser, λ:<>, #()).

Definition p_auth : val :=
  Λ: λ: "ser" "a", ("a", Hash ((Fst "ser") "a")).
