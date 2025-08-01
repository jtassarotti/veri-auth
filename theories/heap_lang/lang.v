(** [HeapLang] as found in the Iris repository, extended with strings and a hash operation *)

From stdpp Require Export binders strings.
From stdpp Require Import gmap.
From iris.algebra Require Export ofe.
From iris.program_logic Require Export language ectx_language ectxi_language.
From auth.prelude Require Export hash strings.
From auth.heap_lang Require Export locations.
From iris.prelude Require Import options.

(** heap_lang.  A fairly simple language used for common Iris examples.

Noteworthy design choices:

- This is a right-to-left evaluated language, like CakeML and OCaml.  The reason
  for this is that it makes curried functions usable: Given a WP for [f a b], we
  know that any effects [f] might have to not matter until after *both* [a] and
  [b] are evaluated.  With left-to-right evaluation, that triple is basically
  useless unless the user let-expands [b].

- Even after deallocating a location, the heap remembers that these locations
  were previously allocated and makes sure they do not get reused. This is
  necessary to ensure soundness of the [meta] feature provided by [gen_heap].
  Also, unlike in languages like C, allocated and deallocated "blocks" do not
  have to match up: you can allocate a large array of locations and then
  deallocate a hole out of it in the middle.

- For prophecy variables, we annotate the reduction steps with an "observation"
  and tweak adequacy such that WP knows all future observations. There is
  another possible choice: Use non-deterministic choice when creating a prophecy
  variable ([NewProph]), and when resolving it ([Resolve]) make the
  program diverge unless the variable matches. That, however, requires an
  erasure proof that this endless loop does not make specifications useless.

The expression [Resolve e p v] attaches a prophecy resolution (for prophecy
variable [p] to value [v]) to the top-level base-reduction step of [e]. The
prophecy resolution happens simultaneously with the base-step being taken.
Furthermore, it is required that the base-step produces a value (otherwise
the [Resolve] is stuck), and this value is also attached to the resolution.
A prophecy variable is thus resolved to a pair containing (1) the result
value of the wrapped expression (called [e] above), and (2) the value that
was attached by the [Resolve] (called [v] above). This allows, for example,
to distinguish a resolution originating from a successful [CmpXchg] from one
originating from a failing [CmpXchg]. For example:
 - [Resolve (CmpXchg #l #n #(n+1)) #p v] will behave as [CmpXchg #l #n #(n+1)],
   which means step to a value-boole pair [(n', b)] while updating the heap, but
   in the meantime the prophecy variable [p] will be resolved to [(n', b), v)].
 - [Resolve (! #l) #p v] will behave as [! #l], that is return the value
   [w] pointed to by [l] on the heap (assuming it was allocated properly),
   but it will additionally resolve [p] to the pair [(w,v)].

Note that the sub-expressions of [Resolve e p v] (i.e., [e], [p] and [v])
are reduced as usual, from right to left. However, the evaluation of [e]
is restricted so that the base-step to which the resolution is attached
cannot be taken by the context. For example:
 - [Resolve (CmpXchg #l #n (#n + #1)) #p v] will first be reduced (with by a
   context-step) to [Resolve (CmpXchg #l #n #(n+1) #p v], and then behave as
   described above.
 - However, [Resolve ((λ: "n", CmpXchg #l "n" ("n" + #1)) #n) #p v] is stuck.
   Indeed, it can only be evaluated using a base-step (it is a β-redex),
   but the process does not yield a value.

The mechanism described above supports nesting [Resolve] expressions to
attach several prophecy resolutions to a base-redex. *)

Delimit Scope expr_scope with E.
Delimit Scope val_scope with V.

Module heap_lang.

(** Expressions and vals. *)
Definition proph_id := positive.

(** We have a notion of "poison" as a variant of unit that may not be compared
with anything. This is useful for erasure proofs: if we erased things to unit,
[<erased> == unit] would evaluate to true after erasure, changing program
behavior. So we erase to the poison value instead, making sure that no legal
comparisons could be affected. *)
Inductive base_lit : Set :=
  | LitInt (n : Z) | LitBool (b : bool) | LitString (s : string) | LitUnit | LitPoison
  | LitLoc (l : loc) | LitProphecy (p : proph_id).
Inductive un_op : Set :=
  | NegOp | MinusUnOp | IntOfStringOp | StringOfIntOp | LengthOp.
Inductive bin_op : Set :=
  (** We use "quot" and "rem" instead of "div" and "mod" to
      better match the behavior of 'real' languages:
      e.g., in Rust, -30/-4 == 7. ("div" would return 8.) *)
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp (* Arithmetic *)
  | AndOp | OrOp | XorOp (* Bitwise *)
  | ShiftLOp | ShiftROp (* Shifts *)
  | LeOp | LtOp | EqOp (* Relations *)
  | OffsetOp (* Pointer offset *)
  | AppendOp. (* Strings  *)
Inductive tern_op : Set :=
  | SubOp | IndexOp. (* Strings *)

Inductive expr :=
  (* Values *)
  | Val (v : val)
  (* Base lambda calculus *)
  | Var (x : string)
  | Rec (f x : binder) (e : expr)
  | App (e1 e2 : expr)
  (* Base types and their operations *)
  | UnOp (op : un_op) (e : expr)
  | BinOp (op : bin_op) (e1 e2 : expr)
  | TernOp (op : tern_op) (e1 e2 e3 : expr)
  | If (e0 e1 e2 : expr)
  (* Products *)
  | Pair (e1 e2 : expr)
  | Fst (e : expr)
  | Snd (e : expr)
  (* Sums *)
  | InjL (e : expr)
  | InjR (e : expr)
  | Case (e0 : expr) (e1 : expr) (e2 : expr)
  (* Heap *)
  | AllocN (e1 e2 : expr) (* array length (positive number), initial value *)
  | Free (e : expr)
  | Load (e : expr)
  | Store (e1 : expr) (e2 : expr)
  | CmpXchg (e0 : expr) (e1 : expr) (e2 : expr) (* Compare-exchange *)
  | Xchg (e0 : expr) (e1 : expr) (* exchange *)
  | FAA (e1 : expr) (e2 : expr) (* Fetch-and-add *)
  (* Concurrency *)
  | Fork (e : expr)
  (* Prophecy *)
  | NewProph
  | Resolve (e0 : expr) (e1 : expr) (e2 : expr) (* wrapped expr, proph, val *)
  | Hash (e : expr)
with val :=
  | LitV (l : base_lit)
  | RecV (f x : binder) (e : expr)
  | PairV (v1 v2 : val)
  | InjLV (v : val)
  | InjRV (v : val).

Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

(** An observation associates a prophecy variable (identifier) to a pair of
values. The first value is the one that was returned by the (atomic) operation
during which the prophecy resolution happened (typically, a boolean when the
wrapped operation is a CmpXchg). The second value is the one that the prophecy
variable was actually resolved to. *)
Definition observation : Set := proph_id * (val * val).

Notation of_val := Val (only parsing).

Definition to_val (e : expr) : option val :=
  match e with
  | Val v => Some v
  | _ => None
  end.

(** We assume the following encoding of values to 64-bit words: The least 3
significant bits of every word are a "tag", and we have 61 bits of payload,
which is enough if all pointers are 8-byte-aligned (common on 64bit
architectures). The tags have the following meaning:

0: Payload is the data for a LitV (LitInt _).
1: Payload is the data for a InjLV (LitV (LitInt _)).
2: Payload is the data for a InjRV (LitV (LitInt _)).
3: Payload is the data for a LitV (LitLoc _).
4: Payload is the data for a InjLV (LitV (LitLoc _)).
4: Payload is the data for a InjRV (LitV (LitLoc _)).
6: Payload is one of the following finitely many values, which 61 bits are more
   than enough to encode:
   LitV LitUnit, InjLV (LitV LitUnit), InjRV (LitV LitUnit),
   LitV LitPoison, InjLV (LitV LitPoison), InjRV (LitV LitPoison),
   LitV (LitBool _), InjLV (LitV (LitBool _)), InjRV (LitV (LitBool _)).
7: Value is boxed, i.e., payload is a pointer to some read-only memory area on
   the heap which stores whether this is a RecV, PairV, InjLV or InjRV and the
   relevant data for those cases. However, the boxed representation is never
   used if any of the above representations could be used.

Ignoring (as usual) the fact that we have to fit the infinite Z/loc into 61
bits, this means every value is machine-word-sized and can hence be atomically
read and written.  Also notice that the sets of boxed and unboxed values are
disjoint. *)
Definition lit_is_unboxed (l: base_lit) : Prop :=
  match l with
  (** Disallow comparing (erased) prophecies with (erased) prophecies, by
  considering them boxed. *)
  | LitProphecy _ | LitPoison => False
  | LitInt _ | LitBool _  | LitString _ | LitLoc _ | LitUnit => True
  end.
Definition val_is_unboxed (v : val) : Prop :=
  match v with
  | LitV l => lit_is_unboxed l
  | InjLV (LitV l) => lit_is_unboxed l
  | InjRV (LitV l) => lit_is_unboxed l
  | _ => False
  end.

Global Instance lit_is_unboxed_dec l : Decision (lit_is_unboxed l).
Proof. destruct l; simpl; exact (decide _). Defined.
Global Instance val_is_unboxed_dec v : Decision (val_is_unboxed v).
Proof. destruct v as [ | | | [] | [] ]; simpl; exact (decide _). Defined.

(** We just compare the word-sized representation of two values, without looking
into boxed data.  This works out fine if at least one of the to-be-compared
values is unboxed (exploiting the fact that an unboxed and a boxed value can
never be equal because these are disjoint sets). *)
Definition vals_compare_safe (vl v1 : val) : Prop :=
  val_is_unboxed vl ∨ val_is_unboxed v1.
Global Arguments vals_compare_safe !_ !_ /.

(** The state: heaps of [option val]s, with [None] representing deallocated locations. *)
Record state : Type := {
  heap: gmap loc (option val);
  used_proph_id: gset proph_id;
  hashed_strings: gset string;
}.

(** Equality and other typeclass stuff *)
Lemma to_of_val v : to_val (of_val v) = Some v.
Proof. by destruct v. Qed.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof. destruct e=>//=. by intros [= <-]. Qed.

Global Instance of_val_inj : Inj (=) (=) of_val.
Proof. intros ??. congruence. Qed.

Global Instance base_lit_eq_dec : EqDecision base_lit.
Proof. solve_decision. Defined.
Global Instance un_op_eq_dec : EqDecision un_op.
Proof. solve_decision. Defined.
Global Instance bin_op_eq_dec : EqDecision bin_op.
Proof. solve_decision. Defined.
Global Instance tern_op_eq_dec : EqDecision tern_op.
Proof. solve_decision. Defined.
Global Instance expr_eq_dec : EqDecision expr.
Proof.
  refine (
   fix go (e1 e2 : expr) {struct e1} : Decision (e1 = e2) :=
     match e1, e2 with
     | Val v, Val v' => cast_if (decide (v = v'))
     | Var x, Var x' => cast_if (decide (x = x'))
     | Rec f x e, Rec f' x' e' =>
        cast_if_and3 (decide (f = f')) (decide (x = x')) (decide (e = e'))
     | App e1 e2, App e1' e2' => cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | UnOp o e, UnOp o' e' => cast_if_and (decide (o = o')) (decide (e = e'))
     | BinOp o e1 e2, BinOp o' e1' e2' =>
         cast_if_and3 (decide (o = o')) (decide (e1 = e1')) (decide (e2 = e2'))
     | TernOp o e1 e2 e3, TernOp o' e1' e2' e3' =>
         cast_if_and4 (decide (o = o')) (decide (e1 = e1')) (decide (e2 = e2')) (decide (e3 = e3'))
     | If e0 e1 e2, If e0' e1' e2' =>
        cast_if_and3 (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
     | Pair e1 e2, Pair e1' e2' =>
        cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | Fst e, Fst e' => cast_if (decide (e = e'))
     | Snd e, Snd e' => cast_if (decide (e = e'))
     | InjL e, InjL e' => cast_if (decide (e = e'))
     | InjR e, InjR e' => cast_if (decide (e = e'))
     | Case e0 e1 e2, Case e0' e1' e2' =>
        cast_if_and3 (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
     | AllocN e1 e2, AllocN e1' e2' =>
        cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | Free e, Free e' =>
        cast_if (decide (e = e'))
     | Load e, Load e' => cast_if (decide (e = e'))
     | Store e1 e2, Store e1' e2' =>
        cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | CmpXchg e0 e1 e2, CmpXchg e0' e1' e2' =>
        cast_if_and3 (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
     | Xchg e0 e1, Xchg e0' e1' =>
        cast_if_and (decide (e0 = e0')) (decide (e1 = e1'))
     | FAA e1 e2, FAA e1' e2' =>
        cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | Fork e, Fork e' => cast_if (decide (e = e'))
     | NewProph, NewProph => left _
     | Resolve e0 e1 e2, Resolve e0' e1' e2' =>
        cast_if_and3 (decide (e0 = e0')) (decide (e1 = e1')) (decide (e2 = e2'))
     | Hash e, Hash e' => cast_if (decide (e = e'))
     | _, _ => right _
     end
   with gov (v1 v2 : val) {struct v1} : Decision (v1 = v2) :=
     match v1, v2 with
     | LitV l, LitV l' => cast_if (decide (l = l'))
     | RecV f x e, RecV f' x' e' =>
        cast_if_and3 (decide (f = f')) (decide (x = x')) (decide (e = e'))
     | PairV e1 e2, PairV e1' e2' =>
        cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
     | InjLV e, InjLV e' => cast_if (decide (e = e'))
     | InjRV e, InjRV e' => cast_if (decide (e = e'))
     | _, _ => right _
     end
   for go); try (clear go gov; abstract intuition congruence).
Defined.
Global Instance val_eq_dec : EqDecision val.
Proof. solve_decision. Defined.

Global Instance base_lit_countable : Countable base_lit.
Proof.
 refine (inj_countable' (λ l, match l with
  | LitInt n => (inl (inl (inl n)), None)
  | LitBool b => (inl (inl (inr b)), None)
  | LitUnit => (inl (inr (inl false)), None)
  | LitPoison => (inl (inr (inl true)), None)
  | LitLoc l => (inl (inr (inr l)), None)
  | LitString s => (inr s, None)
  | LitProphecy p => (inl (inr (inl false)), Some p)
  end) (λ l, match l with
  | (inl (inl (inl n)), None) => LitInt n
  | (inl (inl (inr b)), None) => LitBool b
  | (inl (inr (inl false)), None) => LitUnit
  | (inl (inr (inl true)), None) => LitPoison
  | (inl (inr (inr l)), None) => LitLoc l
  | (inr s, None) => LitString s
  | (_, Some p) => LitProphecy p
  end) _); by intros [].
Qed.
Global Instance un_op_finite : Countable un_op.
Proof.
  refine (inj_countable'
            (λ op, match op with
                     NegOp => 0 | MinusUnOp => 1
                   | IntOfStringOp => 2 | StringOfIntOp => 3 | LengthOp => 4 end)
            (λ n, match n with
                    0 => NegOp | 1 => MinusUnOp
                  | 2 => IntOfStringOp | 3 => StringOfIntOp | _ => LengthOp end) _); by intros [].
Qed.
Global Instance bin_op_countable : Countable bin_op.
Proof.
 refine (inj_countable' (λ op, match op with
  | PlusOp => 0 | MinusOp => 1 | MultOp => 2 | QuotOp => 3 | RemOp => 4
  | AndOp => 5 | OrOp => 6 | XorOp => 7 | ShiftLOp => 8 | ShiftROp => 9
  | LeOp => 10 | LtOp => 11 | EqOp => 12 | OffsetOp => 13 | AppendOp => 14
  end) (λ n, match n with
  | 0 => PlusOp | 1 => MinusOp | 2 => MultOp | 3 => QuotOp | 4 => RemOp
  | 5 => AndOp | 6 => OrOp | 7 => XorOp | 8 => ShiftLOp | 9 => ShiftROp
  | 10 => LeOp | 11 => LtOp | 12 => EqOp | 13 => OffsetOp | _ => AppendOp
  end) _); by intros [].
Qed.
Global Instance tern_op_countable : Countable tern_op.
Proof.
 refine (inj_countable' (λ op, match op with
  | SubOp => 0 | IndexOp => 1
  end) (λ n, match n with
  | 0 => SubOp | _ => IndexOp
  end) _); by intros [].
Qed.

Global Instance expr_countable : Countable expr.
Proof.
 set (enc :=
   fix go e :=
     match e with
     | Val v => GenNode 0 [gov v]
     | Var x => GenLeaf (inl (inl x))
     | Rec f x e => GenNode 1 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); go e]
     | App e1 e2 => GenNode 2 [go e1; go e2]
     | UnOp op e => GenNode 3 [GenLeaf (inr (inr (inl op))); go e]
     | BinOp op e1 e2 => GenNode 4 [GenLeaf (inr (inr (inr (inl op)))); go e1; go e2]
     | TernOp op e1 e2 e3 => GenNode 5 [GenLeaf (inr (inr (inr (inr op)))); go e1; go e2; go e3]
     | If e0 e1 e2 => GenNode 6 [go e0; go e1; go e2]
     | Pair e1 e2 => GenNode 7 [go e1; go e2]
     | Fst e => GenNode 8 [go e]
     | Snd e => GenNode 9 [go e]
     | InjL e => GenNode 10 [go e]
     | InjR e => GenNode 11 [go e]
     | Case e0 e1 e2 => GenNode 12 [go e0; go e1; go e2]
     | Fork e => GenNode 13 [go e]
     | AllocN e1 e2 => GenNode 14 [go e1; go e2]
     | Free e => GenNode 15 [go e]
     | Load e => GenNode 16 [go e]
     | Store e1 e2 => GenNode 17 [go e1; go e2]
     | CmpXchg e0 e1 e2 => GenNode 18 [go e0; go e1; go e2]
     | Xchg e0 e1 => GenNode 19 [go e0; go e1]
     | FAA e1 e2 => GenNode 20 [go e1; go e2]
     | NewProph => GenNode 21 []
     | Resolve e0 e1 e2 => GenNode 22 [go e0; go e1; go e2]
     | Hash e => GenNode 23 [go e]
     end
   with gov v :=
     match v with
     | LitV l => GenLeaf (inr (inl l))
     | RecV f x e =>
        GenNode 0 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); go e]
     | PairV v1 v2 => GenNode 1 [gov v1; gov v2]
     | InjLV v => GenNode 2 [gov v]
     | InjRV v => GenNode 3 [gov v]
     end
   for go).
 set (dec :=
   fix go e :=
     match e with
     | GenNode 0 [v] => Val (gov v)
     | GenLeaf (inl (inl x)) => Var x
     | GenNode 1 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); e] => Rec f x (go e)
     | GenNode 2 [e1; e2] => App (go e1) (go e2)
     | GenNode 3 [GenLeaf (inr (inr (inl op))); e] => UnOp op (go e)
     | GenNode 4 [GenLeaf (inr (inr (inr (inl op)))); e1; e2] => BinOp op (go e1) (go e2)
     | GenNode 5 [GenLeaf (inr (inr (inr (inr op)))); e1; e2; e3] => TernOp op (go e1) (go e2) (go e3)
     | GenNode 6 [e0; e1; e2] => If (go e0) (go e1) (go e2)
     | GenNode 7 [e1; e2] => Pair (go e1) (go e2)
     | GenNode 8 [e] => Fst (go e)
     | GenNode 9 [e] => Snd (go e)
     | GenNode 10 [e] => InjL (go e)
     | GenNode 11 [e] => InjR (go e)
     | GenNode 12 [e0; e1; e2] => Case (go e0) (go e1) (go e2)
     | GenNode 13 [e] => Fork (go e)
     | GenNode 14 [e1; e2] => AllocN (go e1) (go e2)
     | GenNode 15 [e] => Free (go e)
     | GenNode 16 [e] => Load (go e)
     | GenNode 17 [e1; e2] => Store (go e1) (go e2)
     | GenNode 18 [e0; e1; e2] => CmpXchg (go e0) (go e1) (go e2)
     | GenNode 19 [e0; e1] => Xchg (go e0) (go e1)
     | GenNode 20 [e1; e2] => FAA (go e1) (go e2)
     | GenNode 21 [] => NewProph
     | GenNode 22 [e0; e1; e2] => Resolve (go e0) (go e1) (go e2)
     | GenNode 23 [e] => Hash (go e)
     | _ => Val $ LitV LitUnit (* dummy *)
     end
   with gov v :=
     match v with
     | GenLeaf (inr (inl l)) => LitV l
     | GenNode 0 [GenLeaf (inl (inr f)); GenLeaf (inl (inr x)); e] => RecV f x (go e)
     | GenNode 1 [v1; v2] => PairV (gov v1) (gov v2)
     | GenNode 2 [v] => InjLV (gov v)
     | GenNode 3 [v] => InjRV (gov v)
     | _ => LitV LitUnit (* dummy *)
     end
   for go).
 refine (inj_countable' enc dec _).
 refine (fix go (e : expr) {struct e} := _ with gov (v : val) {struct v} := _ for go).
 - destruct e as [v| | | | | | | | | | | | | | | | | | | | | | | |]; simpl; f_equal;
     [exact (gov v)|done..].
 - destruct v; by f_equal.
Qed.
Global Instance val_countable : Countable val.
Proof. refine (inj_countable of_val to_val _); auto using to_of_val. Qed.

Global Instance state_inhabited : Inhabited state :=
  populate {| heap := inhabitant; used_proph_id := inhabitant; hashed_strings := inhabitant |}.
Global Instance val_inhabited : Inhabited val := populate (LitV LitUnit).
Global Instance expr_inhabited : Inhabited expr := populate (Val inhabitant).

Canonical Structure stateO := leibnizO state.
Canonical Structure locO := leibnizO loc.
Canonical Structure valO := leibnizO val.
Canonical Structure exprO := leibnizO expr.

(** Evaluation contexts *)
(** Note that [ResolveLCtx] is not by itself an evaluation context item: we do
not reduce directly under Resolve's first argument. We only reduce things nested
further down. Once no nested contexts exist any more, the expression must take
exactly one more step to a value, and Resolve then (atomically) also uses that
value for prophecy resolution.  *)
Inductive ectx_item :=
  | AppLCtx (v2 : val)
  | AppRCtx (e1 : expr)
  | UnOpCtx (op : un_op)
  | BinOpLCtx (op : bin_op) (v2 : val)
  | BinOpRCtx (op : bin_op) (e1 : expr)
  | TernOp1Ctx (op : tern_op) (v2 v3 : val)
  | TernOp2Ctx (op : tern_op) (e1 : expr) (v3 : val)
  | TernOp3Ctx (op : tern_op) (e1 e2 : expr)
  | IfCtx (e1 e2 : expr)
  | PairLCtx (v2 : val)
  | PairRCtx (e1 : expr)
  | FstCtx
  | SndCtx
  | InjLCtx
  | InjRCtx
  | CaseCtx (e1 : expr) (e2 : expr)
  | AllocNLCtx (v2 : val)
  | AllocNRCtx (e1 : expr)
  | FreeCtx
  | LoadCtx
  | StoreLCtx (v2 : val)
  | StoreRCtx (e1 : expr)
  | XchgLCtx (v2 : val)
  | XchgRCtx (e1 : expr)
  | CmpXchgLCtx (v1 : val) (v2 : val)
  | CmpXchgMCtx (e0 : expr) (v2 : val)
  | CmpXchgRCtx (e0 : expr) (e1 : expr)
  | FaaLCtx (v2 : val)
  | FaaRCtx (e1 : expr)
  | ResolveLCtx (ctx : ectx_item) (v1 : val) (v2 : val)
  | ResolveMCtx (e0 : expr) (v2 : val)
  | ResolveRCtx (e0 : expr) (e1 : expr)
  | HashCtx.

(** Contextual closure will only reduce [e] in [Resolve e (Val _) (Val _)] if
the local context of [e] is non-empty. As a consequence, the first argument of
[Resolve] is not completely evaluated (down to a value) by contextual closure:
no base steps (i.e., surface reductions) are taken. This means that contextual
closure will reduce [Resolve (CmpXchg #l #n (#n + #1)) #p #v] into [Resolve
(CmpXchg #l #n #(n+1)) #p #v], but it cannot context-step any further. *)

Fixpoint fill_item (Ki : ectx_item) (e : expr) : expr :=
  match Ki with
  | AppLCtx v2 => App e (of_val v2)
  | AppRCtx e1 => App e1 e
  | UnOpCtx op => UnOp op e
  | BinOpLCtx op v2 => BinOp op e (Val v2)
  | BinOpRCtx op e1 => BinOp op e1 e
  | TernOp1Ctx op v2 v3 => TernOp op e (Val v2) (Val v3)
  | TernOp2Ctx op e1 v3 => TernOp op e1 e (Val v3)
  | TernOp3Ctx op e1 e2 => TernOp op e1 e2 e
  | IfCtx e1 e2 => If e e1 e2
  | PairLCtx v2 => Pair e (Val v2)
  | PairRCtx e1 => Pair e1 e
  | FstCtx => Fst e
  | SndCtx => Snd e
  | InjLCtx => InjL e
  | InjRCtx => InjR e
  | CaseCtx e1 e2 => Case e e1 e2
  | AllocNLCtx v2 => AllocN e (Val v2)
  | AllocNRCtx e1 => AllocN e1 e
  | FreeCtx => Free e
  | LoadCtx => Load e
  | StoreLCtx v2 => Store e (Val v2)
  | StoreRCtx e1 => Store e1 e
  | XchgLCtx v2 => Xchg e (Val v2)
  | XchgRCtx e1 => Xchg e1 e
  | CmpXchgLCtx v1 v2 => CmpXchg e (Val v1) (Val v2)
  | CmpXchgMCtx e0 v2 => CmpXchg e0 e (Val v2)
  | CmpXchgRCtx e0 e1 => CmpXchg e0 e1 e
  | FaaLCtx v2 => FAA e (Val v2)
  | FaaRCtx e1 => FAA e1 e
  | ResolveLCtx K v1 v2 => Resolve (fill_item K e) (Val v1) (Val v2)
  | ResolveMCtx ex v2 => Resolve ex e (Val v2)
  | ResolveRCtx ex e1 => Resolve ex e1 e
  | HashCtx => Hash e
  end.

(** Substitution *)
Fixpoint subst (x : string) (v : val) (e : expr)  : expr :=
  match e with
  | Val _ => e
  | Var y => if decide (x = y) then Val v else Var y
  | Rec f y e =>
     Rec f y $ if decide (BNamed x ≠ f ∧ BNamed x ≠ y) then subst x v e else e
  | App e1 e2 => App (subst x v e1) (subst x v e2)
  | UnOp op e => UnOp op (subst x v e)
  | BinOp op e1 e2 => BinOp op (subst x v e1) (subst x v e2)
  | TernOp op e1 e2 e3 => TernOp op (subst x v e1) (subst x v e2) (subst x v e3)
  | If e0 e1 e2 => If (subst x v e0) (subst x v e1) (subst x v e2)
  | Pair e1 e2 => Pair (subst x v e1) (subst x v e2)
  | Fst e => Fst (subst x v e)
  | Snd e => Snd (subst x v e)
  | InjL e => InjL (subst x v e)
  | InjR e => InjR (subst x v e)
  | Case e0 e1 e2 => Case (subst x v e0) (subst x v e1) (subst x v e2)
  | AllocN e1 e2 => AllocN (subst x v e1) (subst x v e2)
  | Free e => Free (subst x v e)
  | Load e => Load (subst x v e)
  | Xchg e1 e2 => Xchg (subst x v e1) (subst x v e2)
  | Store e1 e2 => Store (subst x v e1) (subst x v e2)
  | CmpXchg e0 e1 e2 => CmpXchg (subst x v e0) (subst x v e1) (subst x v e2)
  | FAA e1 e2 => FAA (subst x v e1) (subst x v e2)
  | Fork e => Fork (subst x v e)
  | NewProph => NewProph
  | Resolve ex e1 e2 => Resolve (subst x v ex) (subst x v e1) (subst x v e2)
  | Hash e => Hash (subst x v e)
  end.

Definition subst' (mx : binder) (v : val) : expr → expr :=
  match mx with BNamed x => subst x v | BAnon => id end.

(** The stepping relation *)
Definition un_op_eval (op : un_op) (v : val) : option val :=
  match op, v with
  | NegOp, LitV (LitBool b) => Some $ LitV $ LitBool (negb b)
  | NegOp, LitV (LitInt n) => Some $ LitV $ LitInt (Z.lnot n)
  | MinusUnOp, LitV (LitInt n) => Some $ LitV $ LitInt (- n)
  | StringOfIntOp, LitV (LitInt z) => Some $ LitV $ LitString (StringOfZ z)
  | IntOfStringOp, LitV (LitString s) =>
      Some $
        match ZOfString s with
          Some z => InjRV $ LitV (LitInt z)
        | None => InjLV (LitV (LitUnit))
        end
  | LengthOp, LitV (LitString s) => Some $ LitV $ LitInt (String.length s)
  | _, _ => None
  end.

Definition bin_op_eval_int (op : bin_op) (n1 n2 : Z) : option base_lit :=
  match op with
  | PlusOp => Some $ LitInt (n1 + n2)
  | MinusOp => Some $ LitInt (n1 - n2)
  | MultOp => Some $ LitInt (n1 * n2)
  | QuotOp => Some $ LitInt (n1 `quot` n2)
  | RemOp => Some $ LitInt (n1 `rem` n2)
  | AndOp => Some $ LitInt (Z.land n1 n2)
  | OrOp => Some $ LitInt (Z.lor n1 n2)
  | XorOp => Some $ LitInt (Z.lxor n1 n2)
  | ShiftLOp => Some $ LitInt (n1 ≪ n2)
  | ShiftROp => Some $ LitInt (n1 ≫ n2)
  | LeOp => Some $ LitBool (bool_decide (n1 ≤ n2))
  | LtOp => Some $ LitBool (bool_decide (n1 < n2))
  | EqOp => Some $ LitBool (bool_decide (n1 = n2))
  | OffsetOp => None (* Pointer arithmetic *)
  | AppendOp => None
  end%Z.

Definition bin_op_eval_bool (op : bin_op) (b1 b2 : bool) : option base_lit :=
  match op with
  | PlusOp | MinusOp | MultOp | QuotOp | RemOp => None (* Arithmetic *)
  | AndOp => Some (LitBool (b1 && b2))
  | OrOp => Some (LitBool (b1 || b2))
  | XorOp => Some (LitBool (xorb b1 b2))
  | ShiftLOp | ShiftROp => None (* Shifts *)
  | LeOp | LtOp => None (* InEquality *)
  | EqOp => Some (LitBool (bool_decide (b1 = b2)))
  | OffsetOp => None (* Pointer arithmetic *)
  | AppendOp => None
  end.

Definition bin_op_eval_loc (op : bin_op) (l1 : loc) (v2 : base_lit) : option base_lit :=
  match op, v2 with
  | OffsetOp, LitInt off => Some $ LitLoc (l1 +ₗ off)
  | LeOp, LitLoc l2 => Some $ LitBool (bool_decide (l1 ≤ₗ l2))
  | LtOp, LitLoc l2 => Some $ LitBool (bool_decide (l1 <ₗ l2))
  | _, _ => None
  end.

Definition bin_op_eval_string (op : bin_op) (s1 s2 : string) : option base_lit :=
  match op with
  | AppendOp => Some $ LitString (String.append s1 s2)
  | _ => None
  end.

Definition bin_op_eval (op : bin_op) (v1 v2 : val) : option val :=
  if decide (op = EqOp) then
    (* Crucially, this compares the same way as [CmpXchg]! *)
    if decide (vals_compare_safe v1 v2) then
      Some $ LitV $ LitBool $ bool_decide (v1 = v2)
    else
      None
  else
    match v1, v2 with
    | LitV (LitInt n1), LitV (LitInt n2) => LitV <$> bin_op_eval_int op n1 n2
    | LitV (LitBool b1), LitV (LitBool b2) => LitV <$> bin_op_eval_bool op b1 b2
    | LitV (LitLoc l1), LitV v2 => LitV <$> bin_op_eval_loc op l1 v2
    | LitV (LitString s1), LitV (LitString s2) => LitV <$> bin_op_eval_string op s1 s2
    | _, _ => None
    end.

Definition option_nat_to_val (v : option nat) :=
  match v with
  | None => InjLV (LitV LitUnit)
  | Some v' => InjRV (LitV $ LitInt (Z.of_nat v'))
  end.

Definition tern_op_eval (op : tern_op) (v1 v2 v3 : val) : option val :=
  match op, v1, v2, v3 with
  | IndexOp, LitV (LitInt n), LitV (LitString s1), LitV (LitString s2) =>
      Some $ option_nat_to_val $ String.index (Z.to_nat n) s1 s2
  | SubOp, LitV (LitInt n1), LitV (LitInt n2), LitV (LitString s) =>
      Some $ LitV $ LitString $ String.substring (Z.to_nat n1) (Z.to_nat n2) s
  | _, _, _, _ => None
  end .


Definition state_upd_heap (f: gmap loc (option val) → gmap loc (option val)) (σ: state) : state :=
  {| heap := f σ.(heap); used_proph_id := σ.(used_proph_id); hashed_strings := σ.(hashed_strings) |}.
Global Arguments state_upd_heap _ !_ /.

Definition state_upd_used_proph_id (f: gset proph_id → gset proph_id) (σ: state) : state :=
  {| heap := σ.(heap); used_proph_id := f σ.(used_proph_id); hashed_strings := σ.(hashed_strings) |}.
Global Arguments state_upd_used_proph_id _ !_ /.

Definition state_upd_hashed_strings (f: gset string → gset string) (σ: state) : state :=
  {| heap := σ.(heap); used_proph_id := σ.(used_proph_id); hashed_strings := f σ.(hashed_strings) |}.
Global Arguments state_upd_hashed_strings _ !_ /.

Fixpoint heap_array (l : loc) (vs : list val) : gmap loc (option val) :=
  match vs with
  | [] => ∅
  | v :: vs' => {[l := Some v]} ∪ heap_array (l +ₗ 1) vs'
  end.

Lemma heap_array_singleton l v : heap_array l [v] = {[l := Some v]}.
Proof. by rewrite /heap_array right_id. Qed.

Lemma heap_array_lookup l vs ow k :
  heap_array l vs !! k = Some ow ↔
  ∃ j w, (0 ≤ j)%Z ∧ k = l +ₗ j ∧ ow = Some w ∧ vs !! (Z.to_nat j) = Some w.
Proof.
  revert k l; induction vs as [|v' vs IH]=> l' l /=.
  { rewrite lookup_empty. naive_solver lia. }
  rewrite -insert_union_singleton_l lookup_insert_Some IH. split.
  - intros [[-> ?] | (Hl & j & w & ? & -> & -> & ?)].
    { eexists 0, _. rewrite Loc.add_0. naive_solver lia. }
    eexists (1 + j)%Z, _. rewrite Loc.add_assoc !Z.add_1_l Z2Nat.inj_succ; auto with lia.
  - intros (j & w & ? & -> & -> & Hil). destruct (decide (j = 0)); simplify_eq/=.
    { rewrite Loc.add_0; eauto. }
    right. split.
    { rewrite -{1}(Loc.add_0 l). intros ?%(inj (Loc.add _)); lia. }
    assert (Z.to_nat j = S (Z.to_nat (j - 1))) as Hj.
    { rewrite -Z2Nat.inj_succ; last lia. f_equal; lia. }
    rewrite Hj /= in Hil.
    eexists (j - 1)%Z, _. rewrite Loc.add_assoc Z.add_sub_assoc Z.add_simpl_l.
    auto with lia.
Qed.

Lemma heap_array_map_disjoint (h : gmap loc (option val)) (l : loc) (vs : list val) :
  (∀ i, (0 ≤ i)%Z → (i < length vs)%Z → h !! (l +ₗ i) = None) →
  (heap_array l vs) ##ₘ h.
Proof.
  intros Hdisj. apply map_disjoint_spec=> l' v1 v2.
  intros (j&w&?&->&?&Hj%lookup_lt_Some%inj_lt)%heap_array_lookup.
  move: Hj. rewrite Z2Nat.id // => ?. by rewrite Hdisj.
Qed.

(* [h] is added on the right here to make [state_init_heap_singleton] true. *)
Definition state_init_heap (l : loc) (n : Z) (v : val) (σ : state) : state :=
  state_upd_heap (λ h, heap_array l (replicate (Z.to_nat n) v) ∪ h) σ.

Lemma state_init_heap_singleton l v σ :
  state_init_heap l 1 v σ = state_upd_heap <[l:=Some v]> σ.
Proof.
  destruct σ as [h p]. rewrite /state_init_heap /=. f_equiv.
  rewrite right_id insert_union_singleton_l. done.
Qed.

Inductive base_step : expr → state → list observation → expr → state → list expr → Prop :=
  | RecS f x e σ :
     base_step (Rec f x e) σ [] (Val $ RecV f x e) σ []
  | PairS v1 v2 σ :
     base_step (Pair (Val v1) (Val v2)) σ [] (Val $ PairV v1 v2) σ []
  | InjLS v σ :
     base_step (InjL $ Val v) σ [] (Val $ InjLV v) σ []
  | InjRS v σ :
     base_step (InjR $ Val v) σ [] (Val $ InjRV v) σ []
  | BetaS f x e1 v2 e' σ :
     e' = subst' x v2 (subst' f (RecV f x e1) e1) →
     base_step (App (Val $ RecV f x e1) (Val v2)) σ [] e' σ []
  | UnOpS op v v' σ :
     un_op_eval op v = Some v' →
     base_step (UnOp op (Val v)) σ [] (Val v') σ []
  | BinOpS op v1 v2 v' σ :
     bin_op_eval op v1 v2 = Some v' →
     base_step (BinOp op (Val v1) (Val v2)) σ [] (Val v') σ []
  | TernOpS op v1 v2 v3 v' σ :
     tern_op_eval op v1 v2 v3 = Some v' →
     base_step (TernOp op (Val v1) (Val v2) (Val v3)) σ [] (Val v') σ []
  | IfTrueS e1 e2 σ :
     base_step (If (Val $ LitV $ LitBool true) e1 e2) σ [] e1 σ []
  | IfFalseS e1 e2 σ :
     base_step (If (Val $ LitV $ LitBool false) e1 e2) σ [] e2 σ []
  | FstS v1 v2 σ :
     base_step (Fst (Val $ PairV v1 v2)) σ [] (Val v1) σ []
  | SndS v1 v2 σ :
     base_step (Snd (Val $ PairV v1 v2)) σ [] (Val v2) σ []
  | CaseLS v e1 e2 σ :
     base_step (Case (Val $ InjLV v) e1 e2) σ [] (App e1 (Val v)) σ []
  | CaseRS v e1 e2 σ :
     base_step (Case (Val $ InjRV v) e1 e2) σ [] (App e2 (Val v)) σ []
  | AllocNS n v σ l :
     (0 < n)%Z →
     (∀ i, (0 ≤ i)%Z → (i < n)%Z → σ.(heap) !! (l +ₗ i) = None) →
     base_step (AllocN (Val $ LitV $ LitInt n) (Val v)) σ
               []
               (Val $ LitV $ LitLoc l) (state_init_heap l n v σ)
               []
  | FreeS l v σ :
     σ.(heap) !! l = Some $ Some v →
     base_step (Free (Val $ LitV $ LitLoc l)) σ
               []
               (Val $ LitV LitUnit) (state_upd_heap <[l:=None]> σ)
               []
  | LoadS l v σ :
     σ.(heap) !! l = Some $ Some v →
     base_step (Load (Val $ LitV $ LitLoc l)) σ [] (of_val v) σ []
  | StoreS l v w σ :
     σ.(heap) !! l = Some $ Some v →
     base_step (Store (Val $ LitV $ LitLoc l) (Val w)) σ
               []
               (Val $ LitV LitUnit) (state_upd_heap <[l:=Some w]> σ)
               []
  | XchgS l v1 v2 σ :
     σ.(heap) !! l = Some $ Some v1 →
     base_step (Xchg (Val $ LitV $ LitLoc l) (Val v2)) σ
               []
               (Val v1) (state_upd_heap <[l:=Some v2]> σ)
               []

  | CmpXchgS l v1 v2 vl σ b :
     σ.(heap) !! l = Some $ Some vl →
     (* Crucially, this compares the same way as [EqOp]! *)
     vals_compare_safe vl v1 →
     b = bool_decide (vl = v1) →
     base_step (CmpXchg (Val $ LitV $ LitLoc l) (Val v1) (Val v2)) σ
               []
               (Val $ PairV vl (LitV $ LitBool b)) (if b then state_upd_heap <[l:=Some v2]> σ else σ)
               []
  | FaaS l i1 i2 σ :
     σ.(heap) !! l = Some $ Some (LitV (LitInt i1)) →
     base_step (FAA (Val $ LitV $ LitLoc l) (Val $ LitV $ LitInt i2)) σ
               []
               (Val $ LitV $ LitInt i1) (state_upd_heap <[l:=Some $ LitV (LitInt (i1 + i2))]>σ)
               []
  | ForkS e σ :
     base_step (Fork e) σ [] (Val $ LitV LitUnit) σ [e]
  | NewProphS σ p :
     p ∉ σ.(used_proph_id) →
     base_step NewProph σ
               []
               (Val $ LitV $ LitProphecy p) (state_upd_used_proph_id ({[ p ]} ∪.) σ)
               []
  | ResolveS p v e σ w σ' κs ts :
     base_step e σ κs (Val v) σ' ts →
     base_step (Resolve e (Val $ LitV $ LitProphecy p) (Val w)) σ
       (κs ++ [(p, (v, w))]) (Val v) σ' ts
| HashS s σ :
     base_step (Hash (Val $ LitV $ LitString s)) σ
     []
     (Val $ LitV $ LitString (hash s)) (state_upd_hashed_strings ({[ s ]} ∪.) σ)
     [].

(** Basic properties about the language *)
Global Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof. induction Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma fill_item_val Ki e :
  is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
Proof. intros [v ?]. induction Ki; simplify_option_eq; eauto. Qed.

Lemma val_base_stuck e1 σ1 κ e2 σ2 efs : base_step e1 σ1 κ e2 σ2 efs → to_val e1 = None.
Proof. destruct 1; naive_solver. Qed.

Lemma base_ctx_step_val Ki e σ1 κ e2 σ2 efs :
  base_step (fill_item Ki e) σ1 κ e2 σ2 efs → is_Some (to_val e).
Proof. revert κ e2. induction Ki; inversion_clear 1; simplify_option_eq; eauto. Qed.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Proof.
  revert Ki1. induction Ki2; intros Ki1; induction Ki1; naive_solver eauto with f_equal.
Qed.

Lemma alloc_fresh v n σ :
  let l := Loc.fresh (dom σ.(heap)) in
  (0 < n)%Z →
  base_step (AllocN ((Val $ LitV $ LitInt $ n)) (Val v)) σ []
            (Val $ LitV $ LitLoc l) (state_init_heap l n v σ) [].
Proof.
  intros.
  apply AllocNS; first done.
  intros. apply not_elem_of_dom.
  by apply Loc.fresh_fresh.
Qed.

Lemma new_proph_id_fresh σ :
  let p := fresh σ.(used_proph_id) in
  base_step NewProph σ [] (Val $ LitV $ LitProphecy p) (state_upd_used_proph_id ({[ p ]} ∪.) σ) [].
Proof. constructor. apply is_fresh. Qed.

Lemma heap_lang_mixin : EctxiLanguageMixin of_val to_val fill_item base_step.
Proof.
  split; apply _ || eauto using to_of_val, of_to_val, val_base_stuck,
    fill_item_val, fill_item_no_val_inj, base_ctx_step_val.
Qed.
End heap_lang.

(** Language *)
Canonical Structure heap_ectxi_lang := EctxiLanguage heap_lang.heap_lang_mixin.
Canonical Structure heap_ectx_lang := EctxLanguageOfEctxi heap_ectxi_lang.
Canonical Structure heap_lang := LanguageOfEctx heap_ectx_lang.

(* Prefer heap_lang names over ectx_language names. *)
Export heap_lang.

(** The following lemma is not provable using the axioms of [ectxi_language].
The proof requires a case analysis over context items ([destruct i] on the
last line), which in all cases yields a non-value. To prove this lemma for
[ectxi_language] in general, we would require that a term of the form
[fill_item i e] is never a value. *)
Lemma to_val_fill_some K e v : to_val (fill K e) = Some v → K = [] ∧ e = Val v.
Proof.
  intro H. destruct K as [|Ki K]; first by apply of_to_val in H. exfalso.
  assert (to_val e ≠ None) as He.
  { intro A. by rewrite fill_not_val in H. }
  assert (∃ w, e = Val w) as [w ->].
  { destruct e; try done; eauto. }
  assert (to_val (fill (Ki :: K) (Val w)) = None).
  { destruct Ki; simpl; apply fill_not_val; done. }
  by simplify_eq.
Qed.

Lemma prim_step_to_val_is_base_step e σ1 κs w σ2 efs :
  prim_step e σ1 κs (Val w) σ2 efs → base_step e σ1 κs (Val w) σ2 efs.
Proof.
  intro H. destruct H as [K e1 e2 H1 H2].
  assert (to_val (fill K e2) = Some w) as H3; first by rewrite -H2.
  apply to_val_fill_some in H3 as [-> ->]. subst e. done.
Qed.

(** If [e1] makes a base step to a value under some state [σ1] then any base
 step from [e1] under any other state [σ1'] must necessarily be to a value. *)
Lemma base_step_to_val e1 σ1 κ e2 σ2 efs σ1' κ' e2' σ2' efs' :
  base_step e1 σ1 κ e2 σ2 efs →
  base_step e1 σ1' κ' e2' σ2' efs' → is_Some (to_val e2) → is_Some (to_val e2').
Proof. destruct 1; inversion 1; naive_solver. Qed.

Lemma irreducible_resolve e v1 v2 σ :
  irreducible e σ → irreducible (Resolve e (Val v1) (Val v2)) σ.
Proof.
  intros H κs ? σ' efs [Ks e1' e2' Hfill -> step]. simpl in *.
  induction Ks as [|K Ks _] using rev_ind; simpl in Hfill.
  - subst e1'. inversion step. eapply H. by apply base_prim_step.
  - rewrite fill_app /= in Hfill.
    destruct K; (inversion Hfill; subst; clear Hfill; try
      match goal with | H : Val ?v = fill Ks ?e |- _ =>
        (assert (to_val (fill Ks e) = Some v) as HEq by rewrite -H //);
        apply to_val_fill_some in HEq; destruct HEq as [-> ->]; inversion step
      end).
    eapply (H κs (fill_item _ (foldl (flip fill_item) e2' Ks)) σ' efs).
    eapply (Ectx_step (Ks ++ [_])); last done; simpl; by rewrite fill_app.
Qed.
