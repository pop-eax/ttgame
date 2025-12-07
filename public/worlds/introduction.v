(*@WORLD: {
  "id": "introduction",
  "name": "Introduction to Rocq",
  "description": "Learn the fundamentals of Rocq through interactive lectures and exercises",
  "order": 0,
  "icon": "📖",
  "color": "#3b82f6",
  "estimatedHours": 15,
  "tags": ["introduction", "basics", "tutorial"]
}*)

(*===========================================*)
(*@LEVEL: 1.1*)
(*@LEVEL_META: {
  "id": "1.1",
  "name": "Lecture 1: Introduction to Rocq",
  "description": "Learn what Rocq is and its basic concepts",
  "difficulty": 1,
  "estimatedTime": 20,
  "objective": "Understand the basics of Rocq and its languages",
  "hints": [
    "Read the theory section carefully",
    "Rocq is a proof assistant based on type theory",
    "It consists of multiple languages: Gallina, Vernacular, and Ltac"
  ],
  "rewards": {
    "xp": 50
  }
}*)

(*@THEORY:
# Introduction to Rocq

ROCQ (originally COQ) is an interactive proof assistant (proof assistant).
It consists of several languages:
- **Gallina**: Basic functional language (type theory)
- **Vernacular**: Commands - Definition, Inductive, Lemma, Theorem, Print...
- **Ltac**: Language - tactics for proving theorems

Official website and documentation:
https://rocq-prover.org/ 
https://rocq-prover.org/docs

It is based on type theory:
Calculus of Inductive Constructions
https://en.wikipedia.org/wiki/Calculus_of_constructions

More information on the course page:
- https://kurzy.kpi.fei.tuke.sk/tt/rocq/01.html
@ENDTHEORY*)

(*@START:
(* Define a variable x with value 10 *)
@ENDSTART*)

(*@SOLUTION:
Definition x := 10.
@ENDSOLUTION*)

(*===========================================*)
(*@LEVEL: 1.2*)
(*@LEVEL_META: {
  "id": "1.2",
  "name": "Lecture 1: Basic Definitions and Functions",
  "description": "Learn how to define variables and functions in Rocq",
  "difficulty": 1,
  "estimatedTime": 25,
  "objective": "Define a function that adds 1 to a natural number",
  "hints": [
    "Use the Definition keyword",
    "Functions can take parameters",
    "The syntax is: Definition name (param : type) : return_type := body."
  ],
  "rewards": {
    "xp": 75
  }
}*)

(*@THEORY:
## Basic Definitions

Querying and controlling ROCQ through Vernacular language commands:
- Variable definitions
- Function definitions
- Information about objects and searching for objects.

(*@EXAMPLE: Defining a variable
Definition x := 10.
@ENDEXAMPLE*)

(*@EXAMPLE: Defining a function
Definition succ (x : nat) : nat := x + 1.
@ENDEXAMPLE*)

(*@EXAMPLE: Partial function application
Definition plus x y := x + y.
Definition plus2 := plus 2.
Compute plus2 3. (* Returns 5 *)
@ENDEXAMPLE*)

## Function Definitions

Functions in Rocq:
- Higher-order functions
- Let construction
- Pattern matching

In Rocq, you can only define complete functions,
i.e., those that terminate for every input.
@ENDTHEORY*)

(*@START:
(* Define a function succ that adds 1 to a natural number *)
@ENDSTART*)

(*@SOLUTION:
Definition succ (x : nat) : nat := x + 1.
@ENDSOLUTION*)

(*===========================================*)
(*@LEVEL: 1.3*)
(*@LEVEL_META: {
  "id": "1.3",
  "name": "Lecture 1: Recursive Functions",
  "description": "Learn how to define recursive functions using Fixpoint",
  "difficulty": 2,
  "estimatedTime": 30,
  "objective": "Define a recursive factorial function",
  "hints": [
    "Use Fixpoint for recursive functions",
    "Use pattern matching with match",
    "Handle the base case (0) and recursive case (S n')"
  ],
  "rewards": {
    "xp": 100
  }
}*)

(*@THEORY:
## Recursive Functions

Recursive functions are defined using the `Fixpoint` keyword.

(*@EXAMPLE: Factorial function
Fixpoint factorial (n:nat) := 
  match n with
    | 0 => 1
    | (S n') => n * factorial n'
  end.
@ENDEXAMPLE*)

The pattern matching syntax:
- `match n with` - start pattern matching on n
- `| 0 => ...` - base case when n is 0
- `| (S n') => ...` - recursive case when n is successor of n'
@ENDTHEORY*)

(*@START:
(* Define a recursive factorial function *)
Fixpoint factorial (n:nat) := 
  match n with
    | 0 => (* base case *)
    | (S n') => (* recursive case *)
  end.
@ENDSTART*)

(*@SOLUTION:
Fixpoint factorial (n:nat) := 
  match n with
    | 0 => 1
    | (S n') => n * factorial n'
  end.
@ENDSOLUTION*)

(*===========================================*)
(*@LEVEL: 1.4*)
(*@LEVEL_META: {
  "id": "1.4",
  "name": "Lecture 1: Basic Types and Type Hierarchy",
  "description": "Understand the type system in Rocq",
  "difficulty": 1,
  "estimatedTime": 20,
  "objective": "Understand the type hierarchy",
  "hints": [
    "Set is the universe of data types",
    "Prop is the universe of logical propositions",
    "Type is the universe of all types"
  ],
  "rewards": {
    "xp": 50
  }
}*)

(*@THEORY:
## Basic Types and Type Hierarchy in ROCQ

| Type      | Where it belongs | Meaning                      | Example values |
|-----------|------------------|------------------------------|----------------|
| Set       | Type             | Universe of data types       | nat, bool, list |
| Prop      | Type             | Universe of logical propositions | True, False, n=0|
| Type      | Type1,2,..       | Universe of all types        | Set, Prop, list |
| bool      | Set              | Boolean logic                | true, false     |
| nat       | Set              | Natural numbers (Peano)      | O, S O, S (S O) |
| unit      | Set              | One element (trivial type)   | tt              |
| Empty_set | Set              | Empty type (no elements)     | --              |
| list A    | Set              | List of elements of type A   | nil, cons 1 nil |

(*@EXAMPLE: Checking types
Check Set.              (* Set : Type *)
Check Prop.             (* Prop : Type *)
Check nat.              (* nat : Set *)
Check True.             (* True : Prop *)
Check (3 = 4).          (* 3 = 4 : Prop *)
@ENDEXAMPLE*)
@ENDTHEORY*)

(*@START:
(* Check the type of the boolean value true *)
@ENDSTART*)

(*@SOLUTION:
Check true.
(* true : bool *)
@ENDSOLUTION*)

(*===========================================*)
(*@LEVEL: 1.5*)
(*@LEVEL_META: {
  "id": "1.5",
  "name": "Lecture 1: Inductive Types",
  "description": "Learn how to define custom data types using Inductive",
  "difficulty": 2,
  "estimatedTime": 30,
  "objective": "Define a custom inductive type for days of the week",
  "hints": [
    "Use the Inductive keyword",
    "Each constructor must have a unique name",
    "Constructors can take parameters"
  ],
  "rewards": {
    "xp": 100
  }
}*)

(*@THEORY:
## Custom Data Types

The `Inductive` keyword is used to define custom data types.

Definition:

```
Inductive TypeName : Type :=
  | Constructor1 : Type1 -> TypeName
  | Constructor2 : Type2 -> TypeName
  | ...
  | ConstructorN : TypeN -> TypeName.
```

- Each constructor must have a unique name (can contain parameters).
- Inductive types can have multiple parameters.

(*@EXAMPLE: Days of the week
Inductive day : Type :=
  | Monday
  | Tuesday
  | Wednesday
  | Thursday
  | Friday
  | Saturday
  | Sunday.
@ENDEXAMPLE*)

(*@EXAMPLE: Using pattern matching with inductive types
Definition next_weekday (d : day) : day :=
  match d with
  | Monday    => Tuesday
  | Tuesday   => Wednesday
  | Wednesday => Thursday
  | Thursday  => Friday
  | Friday    => Saturday
  | Saturday  => Sunday
  | Sunday    => Monday
  end.
@ENDEXAMPLE*)
@ENDTHEORY*)

(*@START:
(* Define an inductive type for days of the week with seven constructors *)
@ENDSTART*)

(*@SOLUTION:
Inductive day : Type :=
  | Monday
  | Tuesday
  | Wednesday
  | Thursday
  | Friday
  | Saturday
  | Sunday.
@ENDSOLUTION*)

(*===========================================*)
(*@LEVEL: 1.6*)
(*@LEVEL_META: {
  "id": "1.6",
  "name": "Lecture 1: First Proofs - Intro and Reflexivity",
  "description": "Learn your first proof tactics: intro and reflexivity",
  "difficulty": 2,
  "estimatedTime": 30,
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
## First Proofs

Ltac: Language of tactics for constructing proofs

### Basic Tactics

- `intro` - introduces a variable or hypothesis
  - The intro tactic has optional parameters to name the introduced objects
- `reflexivity` - proves goals of the form `x = x`
- `simpl` - simplifies expressions

(*@EXAMPLE: Reflexivity proof
Theorem refl_nat : forall n : nat, n = n.
Proof.
  intro n.         (* take any n *)
  reflexivity.     (* trivial equality n = n *)
Qed.
@ENDEXAMPLE*)

(*@EXAMPLE: Using simpl
Theorem dva_plus_tri : 2 + 3 = 5.
Proof.
  simpl.           (* simplifies 2 + 3 to 5 *)
  reflexivity.     (* 5 = 5 *)
Qed.
@ENDEXAMPLE*)
@ENDTHEORY*)

(*@START:
Theorem my_first_proof : forall n : nat, n = n.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
Theorem my_first_proof : forall n : nat, n = n.
Proof.
  intro n.
  reflexivity.
Qed.
@ENDSOLUTION*)

(*===========================================*)
(*@LEVEL: 1.7*)
(*@LEVEL_META: {
  "id": "1.7",
  "name": "Lecture 1: Proof by Rewriting",
  "description": "Learn how to use the rewrite tactic",
  "difficulty": 2,
  "estimatedTime": 30,
  "objective": "Prove a theorem using rewrite",
  "hints": [
    "rewrite is used when we have an equality in context",
    "Use rewrite H to replace one side with the other",
    "Use rewrite <- H for the opposite direction"
  ],
  "unlockedTactics": ["rewrite"],
  "rewards": {
    "xp": 100
  }
}*)

(*@THEORY:
## Proof by Rewriting

The `rewrite` tactic is used when we have an equality in context
and want to use it to replace one side of the equation with the other.

(*@EXAMPLE: Basic rewrite
Theorem example_rewrite :
  forall n m : nat, n = m -> n + 1 = m + 1.
Proof.
  intros n m H.       (* n, m and assumption H: n = m *)
  rewrite H.          (* replace n with m in the goal *)
  reflexivity.        (* m + 1 = m + 1 *)
Qed.
@ENDEXAMPLE*)

(*@EXAMPLE: Rewrite backwards
Theorem example_rewrite_backwards :
  forall n m : nat, n = m -> m + 1 = n + 1.
Proof.
  intros n m H.
  rewrite <- H.       (* replace m back with n *)
  reflexivity.
Qed.
@ENDEXAMPLE*)
@ENDTHEORY*)

(*@START:
Theorem rewrite_exercise : forall n m : nat, n = m -> n + 2 = m + 2.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
Theorem rewrite_exercise : forall n m : nat, n = m -> n + 2 = m + 2.
Proof.
  intros n m H.
  rewrite H.
  reflexivity.
Qed.
@ENDSOLUTION*)

(*===========================================*)
(*@LEVEL: 1.8*)
(*@LEVEL_META: {
  "id": "1.8",
  "name": "Lecture 1: Proof by Case Analysis - Destruct",
  "description": "Learn how to use destruct for case analysis",
  "difficulty": 2,
  "estimatedTime": 30,
  "objective": "Prove a theorem using destruct",
  "hints": [
    "destruct is used for case analysis without recursion",
    "It generates subgoals for each possible constructor",
    "Use destruct b for bool, destruct n for nat"
  ],
  "unlockedTactics": ["destruct"],
  "rewards": {
    "xp": 100
  }
}*)

(*@THEORY:
## Proof by Case Analysis - Destruct

The `destruct` tactic is used to perform case analysis without recursion.
The tactic generates subgoals for each possible constructor of the term.
Suitable for inductive types without recursion.

(*@EXAMPLE: Destruct on bool
Theorem example_destruct_bool :
  forall b : bool, b = b. 
Proof.
  intros b.
  destruct b.      (* split into cases true and false *)
  - reflexivity.   (* case true *)
  - reflexivity.   (* case false *)
Qed.
@ENDEXAMPLE*)

(*@EXAMPLE: Destruct on nat
Theorem example_destruct_nat :
  forall n : nat, n = n.
Proof.
  intros n.
  destruct n as [| n'].  (* split into O and S n' *)
  - reflexivity.          (* case O *)
  - reflexivity.          (* case S n' *)
Qed.
@ENDEXAMPLE*)
@ENDTHEORY*)

(*@START:
Theorem destruct_exercise : forall b : bool, b = b.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
Theorem destruct_exercise : forall b : bool, b = b.
Proof.
  intros b.
  destruct b.
  - reflexivity.
  - reflexivity.
Qed.
@ENDSOLUTION*)

(*===========================================*)
(*@LEVEL: 2.1*)
(*@LEVEL_META: {
  "id": "2.1",
  "name": "Lecture 2: Proof by Induction",
  "description": "Learn how to prove theorems using induction",
  "difficulty": 3,
  "estimatedTime": 40,
  "objective": "Prove a theorem using induction",
  "hints": [
    "induction generates base case and inductive step",
    "Base case: prove P(0)",
    "Inductive step: prove P(n) -> P(S n) using inductive hypothesis"
  ],
  "unlockedTactics": ["induction"],
  "rewards": {
    "xp": 150
  }
}*)

(*@THEORY:
## Proof by Induction

Induction proof for a statement that some property P(n) holds for all n : nat:

1. Base case: show that P(0) holds.
2. Inductive step: show that if P(n') holds, then P(S n') also holds.
3. Conclusion: from 1. and 2. it follows that P(n) holds for all n.

Formally, the principle of proof by induction can be expressed as:
    (P(0) ∧ ∀n.(P(n) → P(S n))) → ∀n.P(n)

Difference between tactics destruct and induction:

- **destruct**:
  * Used for case analysis according to constructors.
  * Does not extend the proof with an inductive hypothesis.
  * Typical for bool, small cases of nat, or when dividing into finite possibilities is sufficient.

- **induction**:
  * Used when the property requires recursion.
  * In addition to dividing into cases, we also get an inductive hypothesis.
  * Typical for proofs about nat, list, or other recursive structures.
@ENDTHEORY*)

(*@START:
Theorem induction_exercise : forall n : nat, 0 + n = n.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
Theorem induction_exercise : forall n : nat, 0 + n = n.
Proof.
  intro n.
  simpl.
  reflexivity.
Qed.
@ENDSOLUTION*)

(*===========================================*)
(*@LEVEL: 3.1*)
(*@LEVEL_META: {
  "id": "3.1",
  "name": "Lecture 3: Data Structures - Pairs",
  "description": "Learn about pairs and how to work with them",
  "difficulty": 2,
  "estimatedTime": 30,
  "objective": "Define a pair type and projection functions",
  "hints": [
    "Use Inductive to define the pair type",
    "Create projection functions fst and snd",
    "Use pattern matching to extract values"
  ],
  "rewards": {
    "xp": 100
  }
}*)

(*@THEORY:
## Data Structures - Pairs

In this section we will get acquainted with some basic data structures
in the Rocq environment, which are the foundation for data representation
and logical reasoning about programs.

We will cover:
- Simple structures like **pairs**,
- Dynamic structures like **lists**,
- We will reason about these structures formally using logical proofs,
- We will show their **polymorphic versions** that work for any type,
- And finally introduce the **option** type, which is used to represent
  partially defined functions.

Important note:
- The standard Rocq library contains definitions of basic structures
  like **pair** and **list**.
- However, we will first define them ourselves from scratch,
  to better understand the principles of their operation.

### Pair

The only way to create a pair of natural numbers
is to apply the natpair constructor to two arguments of type nat.

To extract values of type natpair we need two projections: fst and snd.

(*@EXAMPLE: Defining a pair type
Inductive natpair: Type :=
| pair (n m :nat).
@ENDEXAMPLE*)

(*@EXAMPLE: Projection functions
Definition fst (x: natpair) : nat := 
  match x with
  | pair n m => n
  end.

Definition snd (x: natpair) : nat := 
  match x with
  | pair n m => m
  end.
@ENDEXAMPLE*)
@ENDTHEORY*)

(*@START:
(* Define a pair type for natural numbers and projection functions *)
Inductive natpair: Type :=
| pair (n m :nat).

(* Define fst function *)
Definition fst (x: natpair) : nat := 
  (* Your code here *)

(* Define snd function *)
Definition snd (x: natpair) : nat := 
  (* Your code here *)
@ENDSTART*)

(*@SOLUTION:
Inductive natpair: Type :=
| pair (n m :nat).

Definition fst (x: natpair) : nat := 
  match x with
  | pair n m => n
  end.

Definition snd (x: natpair) : nat := 
  match x with
  | pair n m => m
  end.
@ENDSOLUTION*)

(*===========================================*)
(*@LEVEL: 3.2*)
(*@LEVEL_META: {
  "id": "3.2",
  "name": "Lecture 3: Lists",
  "description": "Learn about lists and list operations",
  "difficulty": 2,
  "estimatedTime": 35,
  "objective": "Define list operations like length and append",
  "hints": [
    "Lists are defined inductively with nil and cons",
    "Use Fixpoint for recursive list functions",
    "Pattern match on the list structure"
  ],
  "rewards": {
    "xp": 100
  }
}*)

(*@THEORY:
## Lists

Lists are dynamic data structures that can grow or shrink.

(*@EXAMPLE: Defining a list type
Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.
@ENDEXAMPLE*)

(*@EXAMPLE: List length function
Fixpoint length (l:natlist) : nat := 
  match l with 
  | [] => 0
  | head :: tail => 1 + (length tail)
  end.
@ENDEXAMPLE*)

(*@EXAMPLE: List append function
Fixpoint append (l1 l2: natlist) : natlist :=
  match l1 with
  | [] => l2
  | head::tail => head::(append tail l2)
  end.
@ENDEXAMPLE*)
@ENDTHEORY*)

(*@START:
(* Define a length function for lists *)
Fixpoint length (l:natlist) : nat := 
  (* Your code here *)
@ENDSTART*)

(*@SOLUTION:
Fixpoint length (l:natlist) : nat := 
  match l with 
  | [] => 0
  | head :: tail => 1 + (length tail)
  end.
@ENDSOLUTION*)

(*===========================================*)
(*@LEVEL: 5.1*)
(*@LEVEL_META: {
  "id": "5.1",
  "name": "Lecture 5: Inductively Defined Propositions",
  "description": "Learn about inductively defined propositions and relations",
  "difficulty": 3,
  "estimatedTime": 40,
  "objective": "Define an inductive proposition for even numbers",
  "hints": [
    "Use Inductive to define propositions",
    "Define base cases and inductive steps",
    "Use constructors to build proofs"
  ],
  "rewards": {
    "xp": 150
  }
}*)

(*@THEORY:
## Inductively Defined Propositions

In Rocq (and logic in general), an inductively defined proposition means
that a predicate or set is defined using construction rules that determine:
- when the proposition holds (what are the base cases),
- rules for deriving further cases (inductive step).

### Example: Even Numbers

Deduction rules:

```
------------ (ev_0)
   even 0

     even n
----------------- (ev_SS)
  even (S (S n))
```

Definition: n is even if it is 0, or if n-2 is even.

(*@EXAMPLE: Defining even numbers
Inductive even : nat -> Prop :=
  | even_O : even 0
  | even_SS : forall n, even n -> even (S (S n)).
@ENDEXAMPLE*)

(*@EXAMPLE: Proving 4 is even
Lemma four_is_even : even 4.
Proof.
  apply even_SS.
  apply even_SS.
  apply even_O.
Qed.
@ENDEXAMPLE*)
@ENDTHEORY*)

(*@START:
(* Define an inductive proposition for even numbers *)
Inductive even : nat -> Prop :=
  (* Your constructors here *)
@ENDSTART*)

(*@SOLUTION:
Inductive even : nat -> Prop :=
  | even_O : even 0
  | even_SS : forall n, even n -> even (S (S n)).
@ENDSOLUTION*)

(*===========================================*)
(*@LEVEL: 5.2*)
(*@LEVEL_META: {
  "id": "5.2",
  "name": "Lecture 5: Binary Relations - Less or Equal",
  "description": "Learn about binary relations and how to define them",
  "difficulty": 3,
  "estimatedTime": 40,
  "objective": "Prove a theorem about the less-or-equal relation",
  "hints": [
    "Use apply to use constructors",
    "le_n proves n <= n",
    "le_S proves n <= m -> n <= S m"
  ],
  "rewards": {
    "xp": 150
  }
}*)

(*@THEORY:
## Binary Relations

### Less or Equal Relation

Inductive definition of the less-or-equal relation:

Deduction rules:

```
-------------- (le_n)
    n <= n

    n <= m
-------------- (le_S)
    n <= S m
```

(*@EXAMPLE: Defining le
Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat) : le n n
  | le_S (n m : nat) : le n m -> le n (S m).

Notation "n <= m" := (le n m) (at level 70).
@ENDEXAMPLE*)

(*@EXAMPLE: Proving 3 <= 5
Example le_3_5 : 3 <= 5.
Proof.
  apply le_S.
  apply le_S.
  apply le_n.
Qed.
@ENDEXAMPLE*)
@ENDTHEORY*)

(*@START:
(* Prove that 2 <= 4 *)
Example le_2_4 : 2 <= 4.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
Example le_2_4 : 2 <= 4.
Proof.
  apply le_S.
  apply le_S.
  apply le_n.
Qed.
@ENDSOLUTION*)

(*===========================================*)
(*@LEVEL: 6.1*)
(*@LEVEL_META: {
  "id": "6.1",
  "name": "Lecture 6: Maps and Total Maps",
  "description": "Learn about maps as data structures",
  "difficulty": 3,
  "estimatedTime": 40,
  "objective": "Define a total map and update operation",
  "hints": [
    "Total maps are functions from keys to values",
    "Use string as the key type",
    "Update creates a new function that checks for the key"
  ],
  "rewards": {
    "xp": 150
  }
}*)

(*@THEORY:
## Maps and Total Maps

### Total Maps

A total map is a function from keys to values that always returns a value,
even when the key is not explicitly defined.

(*@EXAMPLE: Defining total map
Definition total_map (A : Type) := string -> A.
@ENDEXAMPLE*)

(*@EXAMPLE: Empty total map
Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).
@ENDEXAMPLE*)

(*@EXAMPLE: Updating a total map
Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if String.eqb x x' then v else m x'.
@ENDEXAMPLE*)
@ENDTHEORY*)

(*@START:
(* Define a total map update function *)
Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  (* Your code here *)
@ENDSTART*)

(*@SOLUTION:
Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if String.eqb x x' then v else m x'.
@ENDSOLUTION*)

