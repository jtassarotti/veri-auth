From auth.prelude Require Import stdpp.
From auth.examples Require Import authentikit.
From auth.heap_lang Require Import notation lib.list nondet_bool serialization.
From auth.typing Require Import types typing.
From stdpp Require Import fin_maps.

(** * Authenticated Merkle client *)

(* We define a separate path module like this as the type system doesn't have support
   for primitive lists.
 *)
Definition t_path {Θ} : type (Θ ▹ ⋆ ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆))%kind ⋆ :=
  var2 * (var2 → var2) * (var2 → var2) * (var2 → t_option ((() + ()) * var2)).

Definition path_empty : val := InjLV #().
Definition path_left : val := λ: "p", InjLV #() :: "p".
Definition path_right : val := λ: "p", InjRV #() :: "p".
Definition path_pop : val :=
  λ: "p",
    match: list_head "p" with
      NONE => NONE
    | SOME "x" =>
        let: "p'" := list_tail "p" in
        SOME ("x", "p'")
    end.
Definition path : val := (path_empty, path_left, path_right, path_pop).

(* This is the serialization scheme for both the tree and the proof string *)
Definition merkle_ser : serialization_scheme :=
  sum_serialization_scheme
    string_serialization_scheme (prod_serialization_scheme string_serialization_scheme string_serialization_scheme).

(* This is the serialization scheme for just the first element of the proof string *)

Definition list_elem_ser : serialization_scheme :=
  sum_serialization_scheme string_serialization_scheme
    (sum_serialization_scheme string_serialization_scheme
       (prod_serialization_scheme string_serialization_scheme string_serialization_scheme)).

Definition list_first_ser : serialization_scheme :=
  sum_serialization_scheme
    list_elem_ser (prod_serialization_scheme list_elem_ser string_serialization_scheme).

Arguments s_serializer : simpl never.
Arguments s_deserializer : simpl never.

Definition make_retrieve_proof (ser: serialization_scheme) : val :=
  λ: "s" "proof",
    match: "proof" with
      NONE => ser.(s_serializer) (InjL "s")
    | SOME "proof" => ser.(s_serializer) (InjR ("s", "proof"))
    end.

Definition parse_retrieve_proof (ser: serialization_scheme) : val :=
  λ: "retrieve_proof_ser",
    match: ser.(s_deserializer) "retrieve_proof_ser" with
      NONE => NONE
    | SOME "v" =>
        match: "v" with
          InjL "tip" => SOME ("tip", NONE)
        | InjR "list" =>
            let, ("v1", "v2") := "list" in
            SOME ("v1", SOME "v2")
        end
    end.

Definition hash_retrieve_proof : expr :=
  λ: "val", Hash (merkle_ser.(s_serializer) "val").

Definition retrieve_magic_prover_aux : val :=
  rec: "retrieve_prover_aux" "path" "t_auth" "r_proof" :=
    let: "popped_path_opt" := path_pop "path" in
    let, ("t", "t_hash") := "t_auth" in
    match: "t" with
      InjL "leaf" =>
        match: "popped_path_opt" with
          (* Case 1 base case. Path's length is same as the height of the tree. *)
          NONE => ((make_retrieve_proof list_first_ser) (InjL "leaf") "r_proof", SOME "leaf")
          (* Case 2 base case. Path's length is longer. *)
        | SOME <> => ((make_retrieve_proof list_first_ser) (InjR (InjL "leaf")) "r_proof", NONE)
        end
    | InjR "children" =>
        let, ("left_auth", "right_auth") := "children" in
        let, ("_", "left_hash") := "left_auth" in
        let, ("_", "right_hash") := "right_auth" in
        match: "popped_path_opt" with
          (* Case 3 base case. Path's length is shorter. *)
          (* Instead of serialized versions of the final seen element, we tried directly hashing
             the element to reduce the verifier's burden. However, then it's possible that an
             attacker sends the hashed version of say, a leaf, instead of a node.
             Then the attacker can fool a verifier by saying that the query returns NONE, when
             it should be returning SOME result.
           *)
          NONE => ((make_retrieve_proof list_first_ser) (InjR (InjR ("left_hash", "right_hash"))) "r_proof", NONE)
          (* Recursive case *)
        | SOME "popped_path" =>
            let, ("path_head", "path_tail") := "popped_path" in
            match: "path_head" with
              InjL <> => "retrieve_prover_aux" "path_tail" "left_auth"
                (SOME ((make_retrieve_proof merkle_ser) "right_hash" "r_proof"))
            | InjR <> => "retrieve_prover_aux" "path_tail" "right_auth"
                (SOME ((make_retrieve_proof merkle_ser) "left_hash" "r_proof"))
            end
        end
    end.

Definition p_retrieve : val :=
  λ: "path" "t" "p" "proof",
    let, ("retrieve_proof", "retrieve_result") := retrieve_magic_prover_aux "path" "t" NONEV in
    resolve_proph: "p" to: (SOME "retrieve_proof");; (["retrieve_proof"], "retrieve_result").

Definition retrieve_magic_verifier_aux : val :=
  rec: "retrieve_verifier_aux" "path" "retrieve_proof" "cur_hash" :=
    let: "popped_path_opt" := path_pop "path" in
    match: list_head "retrieve_proof" with
      NONE =>
        match: "popped_path_opt" with
          NONE => SOME "cur_hash"
        | SOME <> => NONE
        end
    | SOME "proof_head" =>
        let: "proof_tail" := list_tail "retrieve_proof" in
        match: "popped_path_opt" with
          NONE => NONE
        | SOME "popped_path" =>
            let, ("path_head", "path_tail") := "popped_path" in
            let: "node_hash" := "retrieve_verifier_aux" "path_tail" "proof_tail" "cur_hash" in
            match: "node_hash" with
              NONE => NONE
            | SOME "node_hash" =>
                match: "path_head" with
                  InjL <> => SOME (hash_retrieve_proof (InjR ("node_hash", "proof_head")))
                | InjR <> => SOME (hash_retrieve_proof (InjR ("proof_head", "node_hash")))
                end
            end
        end
    end.

Definition deserialize_list_proof : val :=
  rec: "deserialize_list_proof" "proof" "acc" :=
    match: "proof" with
      NONE => SOME "acc"
    | SOME "proof" =>
        match: (parse_retrieve_proof merkle_ser) "proof" with
          NONE => NONE
        | SOME "parsed_retrieve_proof" =>
            let, ("proof_head", "proof_tail") := "parsed_retrieve_proof" in
            "deserialize_list_proof" "proof_tail" ("proof_head" :: "acc")
        end
    end.    

Definition v_retrieve : val :=
  λ: "path" "t_hash" "proof",
    match: list_head "proof" with
      NONE => NONE
    | SOME "retrieve_proof_ser" =>
        match: (parse_retrieve_proof list_first_ser) "retrieve_proof_ser" with
          NONE => NONE
        | SOME "r_proof" =>
            let, ("first_element", "retrieve_proof") := "r_proof" in
            let: "proof_list" := deserialize_list_proof "retrieve_proof" [] in
            match: "proof_list" with
              NONE => NONE
            | SOME "proof_list" =>
                let, ("result", "start_hash", "path", "imm_return") :=
                  match: "first_element" with
                    InjL "tip" => (* Case 1 *)
                      (SOME "tip", hash_retrieve_proof (InjL "tip"), "path", (Val(LitV(LitBool false))))
                  | InjR "v" =>
                      match: "v" with
                        InjL "last_leaf" => (* Case 2 *)
                          let: "trunc_path" := list_sub (list_length "proof_list") "path" in
                          (NONE, hash_retrieve_proof (InjL "last_leaf"), "trunc_path",
                            (* If the proof's length is longer or same as the path's length,
                               We immediately return as the path should be longer in this case.
                             *)
                            (BinOp LeOp (list_length "path") (list_length "trunc_path")))
                      | InjR "last_val" => (* Case 3 *)
                          (NONE, hash_retrieve_proof (InjR "last_val"), "path", (Val(LitV(LitBool false))))
                      end
                  end
                in
                if: "imm_return" then NONE else
                  match: retrieve_magic_verifier_aux "path" "proof_list" "start_hash" with
                    NONE => NONE
                  | SOME "node_hash" =>
                      if: "node_hash" = "t_hash"
                      then SOME (list_tail "proof", "result")
                      else NONE
                  end
            end
        end
    end.

Definition retrieve_ideal_aux : val :=
  rec: "retrieve" "path" "t" :=
    let: "popped_path_opt" := path_pop "path" in
    match: "t" with
      InjL "s" =>
        match: "popped_path_opt" with
          NONE => SOME "s"
        | SOME <> => NONE
        end
    | InjR "children" =>
        match: "popped_path_opt" with
          NONE => NONE
        | SOME "popped_path" =>
            let, ("path_head", "path_tail") := "popped_path" in
            match: "path_head" with
              InjL <> => "retrieve" "path_tail" (Fst "children")
            | InjR <> => "retrieve" "path_tail" (Snd "children")
            end
        end
    end.

Definition i_retrieve : val :=
  λ: "path" "t" <>,
    retrieve_ideal_aux "path" "t".


(** tree *)
Definition t_tree {Θ} : type (Θ ▹ ⋆ ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆))%kind ⋆ :=
  (μ: ⋆; (t_string + (var2 var0 * var2 var0)))%ty.
(** tree_auth  *)
Definition t_tree_auth {Θ} : type (Θ ▹ ⋆ ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆))%kind ⋆ :=
  var1 t_tree.
Definition t_retrieve {Θ} : type (Θ ▹ ⋆ ▹ (⋆ ⇒ ⋆) ▹ (⋆ ⇒ ⋆))%kind ⋆ :=
  var2 → t_tree_auth → var0 (t_option t_string).
