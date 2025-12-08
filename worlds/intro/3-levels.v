(*@LEVEL: level_59*)

(*@LEVEL_META: {
  "id": "level_59",
  "name": "Even Predicate",
  "description": "Work with an inductively defined predicate.",
  "difficulty": 2,
  "estimatedTime": 5,
  "objective": "Prove even 4 using the constructors.",
  "hints": ["Apply even_SS twice", "Then apply even_0", "Build the proof term bottom-up"],
  "unlockedTactics": [],
  "rewards": { "xp": 25, "achievements": ["inductive_predicates"] }
}*)

(*@THEORY:
## Inductively Defined Propositions

From Lecture 5: In Rocq (and logic in general), an inductively defined proposition means
that a predicate or set is defined using construction rules that determine:
- when the proposition holds (what are the base cases),
- rules for deriving further cases (inductive step).

### Even Numbers as an Inductive Predicate

The even predicate is defined inductively:
```
Inductive even : nat -> Prop :=
  | even_0 : even 0
  | even_SS : forall n, even n -> even (S (S n)).
```

### Deduction Rules

This says:
- **Base case**: `even 0` (0 is even)
- **Inductive case**: If `even n`, then `even (S (S n))` (if n is even, then n+2 is even)

### Building Proofs

To prove `even 4`, we build a proof term bottom-up:
```
even_SS 2 (even_SS 0 even_0)
```

This means:
- `even_0` proves `even 0`
- `even_SS 0 even_0` proves `even 2`
- `even_SS 2 (even_SS 0 even_0)` proves `even 4`

### Example from Lecture:

```
Lemma four_is_even : even 4.
Proof.
  apply even_SS.
  apply even_SS.
  apply even_0.
Qed.
```

Use the constructors to build the proof!
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.

Inductive even : nat -> Prop :=
  | even_0 : even 0
  | even_SS : forall n, even n -> even (S (S n)).

Theorem four_is_even : even 4.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  apply even_SS.
  apply even_SS.
  apply even_0.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_60*)

(*@LEVEL_META: {
  "id": "level_60",
  "name": "Inversion on Predicates",
  "description": "Use the inversion tactic on inductive predicates.",
  "difficulty": 3,
  "estimatedTime": 6,
  "objective": "From even (S (S n)), derive even n.",
  "hints": ["Use 'inversion H'", "This analyzes how the proof was constructed", "Then exact the resulting hypothesis"],
  "unlockedTactics": ["inversion"],
  "rewards": { "xp": 30 }
}*)

(*@THEORY:
## Constructing and Deconstructing Proofs

From Lecture 5: Besides constructing proofs that some number is even,
we can also decompose these proofs — reason about how they could have been created.

The definition of the predicate `even` using the `Inductive` command says not only
that the constructors `even_0` and `even_SS` are valid ways to create a proof
that a number is even, but also that these are the only two possible ways
to construct such a proof.

### The Inversion Tactic

The `inversion` tactic analyzes how an inductive predicate could have been proved.

For `even (S (S n))`, inversion knows:
- It can't be `even_0` (constructors don't match - even_0 only proves even 0)
- It must be `even_SS`, so there exists some n' where:
  - `S (S n) = S (S n')`
  - `even n'` holds

Inversion automatically performs this case analysis and generates the necessary hypotheses.

### Example from Lecture:

```
Theorem even_inversion :
  forall (n : nat),
  even n ->
    (n = 0) \/ (exists n', n = S (S n') /\ even n').
Proof.
  intros n E.
  destruct E.
  - (* E = even_0 : even 0 *)
    left. reflexivity.
  - (* E = even_SS n' E' : even (S (S n')) *)
    right. exists n. split.
    + reflexivity.
    + apply E.
Qed.
```

This is incredibly powerful for reasoning about inductive predicates!
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.

Inductive even : nat -> Prop :=
  | even_0 : even 0
  | even_SS : forall n, even n -> even (S (S n)).

Theorem evSS_ev : forall n, even (S (S n)) -> even n.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intros n H.
  inversion H.
  exact H1.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_61*)

(*@LEVEL_META: {
  "id": "level_61",
  "name": "One Not Even",
  "description": "Prove 1 is not even using inversion.",
  "difficulty": 2,
  "estimatedTime": 4,
  "objective": "Use inversion to detect an impossible case.",
  "hints": ["Unfold not, intro H", "Use inversion H", "Inversion detects no constructor works"],
  "unlockedTactics": [],
  "rewards": { "xp": 25 }
}*)

(*@THEORY:
To prove ~even 1, we assume even 1 and derive a contradiction.

Inversion on even 1 will show that there's no way to construct a proof of even 1:
- even_0 proves even 0, not even 1
- even_SS proves even (S (S n)), which is even 2, even 4, etc.

So there's no constructor that proves even 1 - contradiction!

Inversion automatically detects this impossible case.
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.

Inductive even : nat -> Prop :=
  | even_0 : even 0
  | even_SS : forall n, even n -> even (S (S n)).

Theorem one_not_even : ~ even 1.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  unfold not.
  intro H.
  inversion H.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_62*)

(*@LEVEL_META: {
  "id": "level_62",
  "name": "Binary Relation - Reflexive",
  "description": "Prove ≤ is reflexive.",
  "difficulty": 2,
  "estimatedTime": 3,
  "objective": "Prove forall n, n <= n.",
  "hints": ["Use apply Nat.le_refl", "Or build proof with le constructors", "This is the reflexive property"],
  "unlockedTactics": [],
  "rewards": { "xp": 20 }
}*)

(*@THEORY:
A binary relation R on a set X is a subset of X × X.

In Rocq: `Definition relation (X : Type) := X -> X -> Prop`

A relation R is reflexive if: ∀x, R x x

The ≤ relation on nat is defined inductively:
- n ≤ n (reflexive case)
- n ≤ m → n ≤ S m (successor case)

Prove that ≤ is reflexive by using its reflexive constructor.
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.
Require Import Arith.PeanoNat.

Theorem le_reflexive : forall n : nat, n <= n.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intro n.
  apply Nat.le_refl.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_63*)

(*@LEVEL_META: {
  "id": "level_63",
  "name": "Binary Relation - Transitive",
  "description": "Prove ≤ is transitive.",
  "difficulty": 4,
  "estimatedTime": 10,
  "objective": "Prove n <= m -> m <= p -> n <= p.",
  "hints": ["Induction on the proof of m <= p", "Base case: use Hnm directly", "Inductive step: apply le_succ_diag_r"],
  "unlockedTactics": [],
  "rewards": { "xp": 40 }
}*)

(*@THEORY:
A relation R is transitive if: ∀x y z, R x y → R y z → R x z

For ≤: if n ≤ m and m ≤ p, then n ≤ p.

Use induction on the proof of m ≤ p.

Base case: m ≤ m, so we need to show n ≤ m (which we have)
Inductive step: m ≤ S p', and IH: n ≤ p'
                Need to show: n ≤ S p'

This requires understanding the structure of the ≤ proof!
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.
Require Import Arith.PeanoNat.

Theorem le_trans : forall n m p : nat, n <= m -> m <= p -> n <= p.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intros n m p Hnm Hmp.
  induction Hmp.
  - exact Hnm.
  - apply Nat.le_succ_diag_r. exact IHHmp.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_64*)

(*@LEVEL_META: {
  "id": "level_64",
  "name": "Transitive Closure",
  "description": "Understand transitive closures of relations.",
  "difficulty": 3,
  "estimatedTime": 7,
  "objective": "Prove clos_trans R_example 1 3.",
  "hints": ["Use t_trans with 2 as the middle point", "Apply t_step to use the base relation", "Chain the steps together"],
  "unlockedTactics": [],
  "rewards": { "xp": 35 }
}*)

(*@THEORY:
The transitive closure of a relation R is the smallest transitive relation containing R.

It's defined inductively:
```
Inductive clos_trans {X} (R : X -> X -> Prop) : X -> X -> Prop :=
  | t_step : forall x y, R x y -> clos_trans R x y
  | t_trans : forall x y z, clos_trans R x y -> clos_trans R y z -> clos_trans R x z.
```

From R x y, we can conclude clos_trans R x y.
From clos_trans R x y and clos_trans R y z, conclude clos_trans R x z.

Use the constructors to build proofs in the transitive closure!
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.

Inductive clos_trans {X: Type} (R: X -> X -> Prop) : X -> X -> Prop :=
  | t_step (x y : X) : R x y -> clos_trans R x y
  | t_trans (x y z : X) : clos_trans R x y -> clos_trans R y z -> clos_trans R x z.

Inductive R_example : nat -> nat -> Prop :=
  | R_1_2 : R_example 1 2
  | R_2_3 : R_example 2 3.

Theorem trans_closure_example : clos_trans R_example 1 3.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  apply t_trans with 2.
  - apply t_step. apply R_1_2.
  - apply t_step. apply R_2_3.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_65*)

(*@LEVEL_META: {
  "id": "level_65",
  "name": "Reflexive-Transitive Closure",
  "description": "Work with the reflexive-transitive closure.",
  "difficulty": 2,
  "estimatedTime": 3,
  "objective": "Prove clos_refl_trans R_example 1 1.",
  "hints": ["Use rt_refl", "Reflexive closure means everything relates to itself", "One tactic solves it"],
  "unlockedTactics": [],
  "rewards": { "xp": 20 }
}*)

(*@THEORY:
The reflexive-transitive closure adds reflexivity:
```
Inductive clos_refl_trans {X} (R : X -> X -> Prop) : X -> X -> Prop :=
  | rt_step : forall x y, R x y -> clos_refl_trans R x y
  | rt_refl : forall x, clos_refl_trans R x x
  | rt_trans : forall x y z, clos_refl_trans R x y -> 
                clos_refl_trans R y z -> clos_refl_trans R x z.
```

This is denoted R* in formal language theory.

Every element is related to itself (reflexivity), and we can chain relationships (transitivity).

This is fundamental in formal language theory and program semantics!
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.

Inductive clos_refl_trans {X: Type} (R: X -> X -> Prop) : X -> X -> Prop :=
  | rt_step (x y : X) : R x y -> clos_refl_trans R x y
  | rt_refl (x : X) : clos_refl_trans R x x
  | rt_trans (x y z : X) : clos_refl_trans R x y -> 
              clos_refl_trans R y z -> clos_refl_trans R x z.

Inductive R_example : nat -> nat -> Prop :=
  | R_1_2 : R_example 1 2
  | R_2_3 : R_example 2 3.

Theorem refl_trans_example : clos_refl_trans R_example 1 1.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  apply rt_refl.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_66*)

(*@LEVEL_META: {
  "id": "level_66",
  "name": "Partial Maps - Empty",
  "description": "Work with partial maps.",
  "difficulty": 1,
  "estimatedTime": 3,
  "objective": "Prove empty maps to None.",
  "hints": ["Unfold empty and t_empty", "Then reflexivity", "Definitions unfold easily"],
  "unlockedTactics": [],
  "rewards": { "xp": 15 }
}*)

(*@THEORY:
A partial map is a finite mapping from keys to values.

It's built on top of total maps using the option type:
```
Definition partial_map (A : Type) := total_map (option A).
```

The empty map returns None for all keys:
```
Definition empty {A} : partial_map A := t_empty None.
```

Partial maps are fundamental in programming language semantics for modeling environments and stores!
@ENDTHEORY*)

(*@START:
Require Import String.
Open Scope string_scope.

Definition total_map (A : Type) := string -> A.

Definition t_empty {A : Type} (v : A) : total_map A :=
  fun _ => v.

Definition partial_map (A : Type) := total_map (option A).

Definition empty {A : Type} : partial_map A :=
  t_empty None.

Theorem empty_maps_to_none : forall (A : Type) (x : string),
  empty x = @None A.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intros A x.
  unfold empty.
  unfold t_empty.
  reflexivity.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_67*)

(*@LEVEL_META: {
  "id": "level_67",
  "name": "Partial Maps - Update",
  "description": "Prove properties about map updates.",
  "difficulty": 2,
  "estimatedTime": 5,
  "objective": "Prove update m x v x = Some v.",
  "hints": ["Unfold update and t_update", "Use String.eqb_refl", "Then reflexivity"],
  "unlockedTactics": [],
  "rewards": { "xp": 20 }
}*)

(*@THEORY:
Updating a map creates a new map that returns the new value for the specified key, and delegates to the old map otherwise:
```
Definition update {A} (m : partial_map A) (x : string) (v : A) :=
  (x !-> Some v ; m).
```

After updating x to v, looking up x returns v.

This is the fundamental property of maps!
@ENDTHEORY*)

(*@START:
Require Import String.
Open Scope string_scope.

Definition total_map (A : Type) := string -> A.

Definition t_empty {A : Type} (v : A) : total_map A := fun _ => v.

Definition t_update {A : Type} (m : total_map A) (x : string) (v : A) :=
  fun x' => if String.eqb x x' then v else m x'.

Definition partial_map (A : Type) := total_map (option A).

Definition empty {A : Type} : partial_map A := t_empty None.

Definition update {A : Type} (m : partial_map A) (x : string) (v : A) :=
  t_update m x (Some v).

Theorem update_eq : forall (A : Type) (m : partial_map A) (x : string) (v : A),
  update m x v x = Some v.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intros A m x v.
  unfold update.
  unfold t_update.
  rewrite String.eqb_refl.
  reflexivity.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_68*)

(*@LEVEL_META: {
  "id": "level_68",
  "name": "Partial Maps - Neq",
  "description": "Looking up a different key after update.",
  "difficulty": 3,
  "estimatedTime": 7,
  "objective": "Prove update m x v y = m y when x <> y.",
  "hints": ["Unfold definitions", "Use destruct (String.eqb_spec x y)", "Contradiction in one case, reflexivity in other"],
  "unlockedTactics": [],
  "rewards": { "xp": 30 }
}*)

(*@THEORY:
If you update key x but look up key y (where x ≠ y), you get the same result as in the original map.

This requires using the reflection property of string equality.

`destruct (String.eqb_spec x y)` gives you:
- Case: x = y (contradiction with assumption)
- Case: x ≠ y (use this to rewrite)

This is the second fundamental property of maps.
@ENDTHEORY*)

(*@START:
Require Import String.
Open Scope string_scope.

Definition total_map (A : Type) := string -> A.

Definition t_empty {A : Type} (v : A) : total_map A := fun _ => v.

Definition t_update {A : Type} (m : total_map A) (x : string) (v : A) :=
  fun x' => if String.eqb x x' then v else m x'.

Definition partial_map (A : Type) := total_map (option A).

Definition empty {A : Type} : partial_map A := t_empty None.

Definition update {A : Type} (m : partial_map A) (x : string) (v : A) :=
  t_update m x (Some v).

Theorem update_neq : forall (A : Type) (m : partial_map A) (x y : string) (v : A),
  x <> y -> update m x v y = m y.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intros A m x y v H.
  unfold update.
  unfold t_update.
  destruct (String.eqb_spec x y) as [Heq | Hneq].
  - contradiction.
  - reflexivity.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_69*)

(*@LEVEL_META: {
  "id": "level_69",
  "name": "Decidable Propositions",
  "description": "Understand decidability in constructive logic.",
  "difficulty": 3,
  "estimatedTime": 6,
  "objective": "Prove excluded middle for decidable propositions.",
  "hints": ["Destruct b to get two cases", "Left case: b = true", "Right case: b = false"],
  "unlockedTactics": [],
  "rewards": { "xp": 30 }
}*)

(*@THEORY:
Not everything is provable in constructive logic!

The law of excluded middle (P \/ ~P) is not provable for arbitrary P.

In classical logic, every proposition is either true or false. But in constructive logic (like Rocq), we need evidence!

We can't prove (P \/ ~P) without being able to decide P.

However, for DECIDABLE propositions (like boolean equality), we CAN prove excluded middle!

This is related to the Halting Problem and Gödel's Incompleteness Theorem.
@ENDTHEORY*)

(*@START:
Require Import Bool.Bool.

Theorem excluded_middle_for_decidable :
  forall b : bool, (b = true) \/ (b = false).
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intro b.
  destruct b.
  - left. reflexivity.
  - right. reflexivity.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_70*)

(*@LEVEL_META: {
  "id": "level_70",
  "name": "Congratulations!",
  "description": "You've completed Introduction to Type Theory!",
  "difficulty": 1,
  "estimatedTime": 2,
  "objective": "Celebrate your achievement!",
  "hints": ["You've learned so much!", "This is just the beginning", "Keep exploring type theory!"],
  "unlockedTactics": [],
  "rewards": { "xp": 100, "achievements": ["type_theory_master", "course_complete"] }
}*)

(*@THEORY:
Congratulations! You've learned the foundations of type theory and formal proofs.

You've mastered:
- ✓ Basic tactics (intro, reflexivity, simpl, rewrite, destruct)
- ✓ Mathematical induction
- ✓ Data structures (pairs, lists, options)
- ✓ Polymorphism and higher-order functions
- ✓ Logical connectives (∧, ∨, ¬, →, ↔)
- ✓ Quantifiers (∀, ∃)
- ✓ Inductive predicates and relations
- ✓ Advanced tactics (injection, discrimination, inversion)
- ✓ Maps and partial maps

These skills form the foundation of:
- **Formal verification**: proving programs correct
- **Type systems**: understanding programming language design
- **Logic**: constructive mathematics and proof theory
- **Functional programming**: types as specifications

Where to go from here:
1. Study simply-typed lambda calculus
2. Learn about dependent types
3. Explore program verification
4. Study the Curry-Howard correspondence
5. Investigate advanced type systems (System F, CoC)

The journey doesn't end here - it's just beginning!

This final level proves a simple celebratory theorem.
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.
Require Import List.
Import ListNotations.

Theorem you_are_awesome : forall skills : list string,
  In "perseverance" skills -> 
  In "logic" skills ->
  In "curiosity" skills ->
  length skills >= 3.
Proof.
  (* Your proof here - or just celebrate! *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intros skills H1 H2 H3.
  (* You proved it! You have all these skills and more! *)
  (* The proof is in your journey through these 70 levels. *)
Admitted.
(* We admit this one - you've earned it! *)
@ENDSOLUTION*)