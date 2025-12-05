(*@WORLD: {
  "id": "world-example",
  "name": "Example Rocq World",
  "description": "An example world using Rocq file format",
  "order": 0,
  "icon": "📚",
  "color": "#8b5cf6",
  "estimatedHours": 5,
  "tags": ["example", "tutorial"],
  "availableTheorems": [
    "eq_refl : forall (A : Type) (x : A), x = x"
  ]
}*)

(*===========================================*)
(*@LEVEL: 0.1*)
(*@LEVEL_META: {
  "id": "0.1",
  "name": "Introduction to Rocq",
  "description": "Learn the basics of Rocq",
  "difficulty": 1,
  "estimatedTime": 5,
  "objective": "Define a variable 'x' with value 10",
  "hints": [
    "Use the Definition keyword",
    "The syntax is: Definition name := value.",
    "Don't forget the period at the end"
  ],
  "unlockedTactics": [],
  "rewards": {
    "xp": 50
  }
}*)

(*@THEORY:
# Introduction to Rocq

ROCQ is an interactive proof assistant. It consists of several languages:
- **Gallina**: Basic functional language (type theory)
- **Vernacular**: Commands - Definition, Inductive, Lemma, Theorem, Print...
- **Ltac**: Language - tactics for proving theorems

## Basic Commands

- `Check` - tells you the type of any expression
- `Print` - shows the definition of an identifier
- `Compute` - evaluates an expression

(*@EXAMPLE: Checking types
Check nat.
(* nat : Set *)
Check 1.
(* 1 : nat *)
*)

(*@EXAMPLE: Printing definitions
Definition x := 10.
Print x.
(* x = 10 : nat *)
*)
*)

(*@START:
(* Define a variable x equal to 10 *)
*)

Definition x := 10.

(*@SOLUTION:
Definition x := 10.
*)

(*===========================================*)
(*@LEVEL: 0.2*)
(*@LEVEL_META: {
  "id": "0.2",
  "name": "First Proof",
  "description": "Learn your first proof",
  "difficulty": 1,
  "estimatedTime": 5,
  "objective": "Prove that forall n : nat, n = n",
  "hints": [
    "Use intro to introduce the variable",
    "Use reflexivity to prove equality",
    "The proof is: intro n. reflexivity."
  ],
  "unlockedTactics": ["intro", "reflexivity"],
  "rewards": {
    "xp": 100
  }
}*)

(*@THEORY:
# First Proofs

## Basic Tactics

- `intro` - introduces a variable or hypothesis
- `reflexivity` - proves goals of the form `x = x`

(*@EXAMPLE: Reflexivity proof
Theorem refl_nat : forall n : nat, n = n.
Proof.
  intro n.
  reflexivity.
Qed.
*)
*)

(*@START:
Theorem my_first_proof : forall n : nat, n = n.
Proof.
  (* Your proof here *)
Qed.
*)

Theorem my_first_proof : forall n : nat, n = n.
Proof.
  intro n.
  reflexivity.
Qed.

(*@SOLUTION:
Theorem my_first_proof : forall n : nat, n = n.
Proof.
  intro n.
  reflexivity.
Qed.
*)

