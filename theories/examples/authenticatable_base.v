From auth.heap_lang.lib Require Export serialization.
From auth.typing Require Export types typing.

(** type 'a evidence = {serialize : 'a -> string; deserialize : string -> 'a} *)
Definition v_Auth_auth : val :=
  Λ: string_scheme.
Definition v_Auth_mu : val :=
  Λ: λ: "s",
      let, ("ser", "deser") := "s" in
      (λ: "x", "ser" "x", λ: "x", "deser" "x").
Definition v_Auth_pair : val :=
  Λ: Λ: λ: "A" "B", prod_scheme "A" "B".
Definition v_Auth_sum : val :=
  Λ: Λ: λ: "A" "B", sum_scheme "A" "B".
Definition v_Auth_string : val := string_scheme.
Definition v_Auth_int : val := int_scheme.

Definition v_auth : val :=
  Λ: λ: "a_scheme" "a", Hash (Fst "a_scheme" "a").

(** type 'a evidence = 'a -> string *)
Definition p_Auth_auth : val :=
  Λ: λ: "v", #"s_" ^ Snd "v".
Definition p_Auth_mu : val :=
  Λ: λ: "ser", λ: "s", rec_fold "ser" "s".
Definition p_Auth_pair : val :=
  Λ: Λ: λ: "serA" "serB", prod_ser "serA" "serB".
Definition p_Auth_sum : val :=
  Λ: Λ: λ: "serA" "serB", sum_ser "serA" "serB".
Definition p_Auth_string : val := string_ser.
Definition p_Auth_int : val := int_ser.

Definition p_auth : val :=
  Λ: λ: "serializer" "a", ("a", Hash ("serializer" "a")).
