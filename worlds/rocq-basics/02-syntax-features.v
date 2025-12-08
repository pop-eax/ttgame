(*===========================================*)
(*@LEVEL: basics_11*)
(*@LEVEL_META: {
  "id": "basics_11",
  "name": "Notations and Custom Syntax",
  "description": "Learn how to define custom notations",
  "difficulty": 2,
  "estimatedTime": 20,
  "objective": "Understand how notations work in Rocq",
  "hints": [
    "Notations make code more readable",
    "Use the Notation command",
    "You can define infix operators"
  ],
  "rewards": {
    "xp": 30
  }
}*)

(*@THEORY:
## Notations and Custom Syntax

From Lecture 1: Rocq allows you to define custom notations to make code more readable.

### Notation Command

```
Notation "symbol" := (expression) (at level N, associativity).
```

### Example: Custom Pair Notation

```
Notation "( x , y )" := (pair x y).
```

### Infix Operators

You can define infix operators:

```
Notation "x ++ y" := (append x y) 
                     (at level 60, right associativity).
```

### Precedence Levels

The `at level N` specifies operator precedence (higher = tighter binding).

Common levels:
- 0-10: Lowest precedence
- 50-60: Arithmetic operators (+, *)
- 70: Comparison operators (<=, =)
- 100: Application (function calls)

### Associativity

- `left associativity`: `a + b + c` = `(a + b) + c`
- `right associativity`: `a -> b -> c` = `a -> (b -> c)`
- `no associativity`: Must use parentheses

### Example from Lecture

```
Notation "x + y" := (plus x y) (at level 50, left associativity).
Notation "x * y" := (mult x y) (at level 40, left associativity).
```

Notations are syntactic sugar - they don't change the meaning, just the appearance!
@ENDTHEORY*)

(*@START:
(* This is a knowledge level about notations *)
(* No code to write, just understand the concept *)
@ENDSTART*)

(*@SOLUTION:
(* Informational level - no solution needed *)
@ENDSOLUTION*)

(*===========================================*)
(*@LEVEL: basics_12*)
(*@LEVEL_META: {
  "id": "basics_12",
  "name": "Modules and Namespaces",
  "description": "Learn how to organize code with modules",
  "difficulty": 2,
  "estimatedTime": 20,
  "objective": "Understand modules and how to use them",
  "hints": [
    "Modules group related definitions",
    "Use Module Name. ... End Name.",
    "Access with ModuleName.definition"
  ],
  "rewards": {
    "xp": 30
  }
}*)

(*@THEORY:
## Modules and Namespaces

From Lecture 1: Modules allow you to organize code and avoid name conflicts.

### Module Syntax

```
Module ModuleName.
  (* definitions here *)
End ModuleName.
```

### Accessing Module Contents

Access definitions from a module using dot notation:

```
ModuleName.definition_name
```

### Example

```
Module NatPlayground.
  Inductive nat : Type :=
    | O
    | S (n : nat).
  
  Fixpoint plus (n m : nat) : nat :=
    match n with
    | O => m
    | S n' => S (plus n' m)
    end.
End NatPlayground.

Check NatPlayground.plus.  (* NatPlayground.plus : ... *)
```

### Benefits

- **Namespace isolation**: Avoid name conflicts
- **Code organization**: Group related definitions
- **Experimentation**: Test definitions without affecting global namespace
- **Libraries**: Organize large codebases

### Opening Modules

You can open a module to use its contents without the prefix:

```
Open Scope ModuleName.
```

Modules are essential for organizing larger Rocq developments!
@ENDTHEORY*)

(*@START:
(* Create a module called MyMath with a function square *)
Module MyMath.
  (* Your definition here *)
End MyMath.

(* Use the square function from the module *)
(* Your code here *)
@ENDSTART*)

(*@SOLUTION:
Module MyMath.
  Definition square (n : nat) : nat := n * n.
End MyMath.

Check MyMath.square.
(* MyMath.square : nat -> nat *)
@ENDSOLUTION*)

(*===========================================*)
(*@LEVEL: basics_13*)
(*@LEVEL_META: {
  "id": "basics_13",
  "name": "Require and Import",
  "description": "Learn how to use libraries and modules",
  "difficulty": 1,
  "estimatedTime": 15,
  "objective": "Import standard library modules",
  "hints": [
    "Require Import loads a module",
    "Import brings notations into scope",
    "Use Require Import for standard library"
  ],
  "rewards": {
    "xp": 25
  }
}*)

(*@THEORY:
## Require and Import

From Lecture 1 & 2: Rocq has a rich standard library that you can import.

### Require Import

Loads a module and makes its definitions available:

```
Require Import Init.Nat.        (* Natural numbers *)
Require Import Bool.Bool.       (* Booleans *)
Require Import List.            (* Lists *)
```

### Import

Brings notations into scope:

```
Import ListNotations.           (* Enables [1;2;3] syntax *)
```

### Common Imports

- `Init.Nat`: Natural numbers and arithmetic
- `Bool.Bool`: Boolean operations
- `List`: Lists and list operations
- `Arith.PeanoNat`: Additional arithmetic lemmas
- `Strings.String`: String operations

### Open Scope

Opens a notation scope:

```
Open Scope string_scope.        (* Enables string operations *)
Open Scope nat_scope.           (* Enables nat operations *)
```

### Example from Lectures

```
Require Import Init.Nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Import ListNotations.
```

This gives you access to:
- Natural number operations
- List functions and notations
- Arithmetic lemmas and theorems

Proper imports are essential for using Rocq's standard library!
@ENDTHEORY*)

(*@START:
(* Import the necessary modules to work with lists *)
(* Your imports here *)

(* Now you can use list notation like [1;2;3] *)
Check [1; 2; 3].
@ENDSTART*)

(*@SOLUTION:
Require Import List.
Import ListNotations.

Check [1; 2; 3].
(* [1; 2; 3] : list nat *)
@ENDSOLUTION*)

(*===========================================*)
(*@LEVEL: basics_14*)
(*@LEVEL_META: {
  "id": "basics_14",
  "name": "Complete Functions Requirement",
  "description": "Understand why all functions must be complete",
  "difficulty": 2,
  "estimatedTime": 20,
  "objective": "Understand the requirement for complete functions",
  "hints": [
    "All functions must terminate",
    "Pattern matching must cover all cases",
    "This ensures mathematical rigor"
  ],
  "rewards": {
    "xp": 30
  }
}*)

(*@THEORY:
## Complete Functions Requirement

From Lecture 1: In Rocq, you can only define **complete functions** - functions that terminate for every input.

### What This Means

Unlike languages like Haskell or OCaml, you cannot have:
- Partial pattern matching
- Non-terminating functions
- Undefined cases

### Example: Invalid Definition

This would be valid in Haskell/OCaml but **invalid** in Rocq:

```
Definition negb (b : bool) : bool :=
  match b with
  | true => false
  (* Missing false case! *)
  end.
```

### Why This Matters

This requirement ensures:
- **Mathematical rigor**: All functions are well-defined
- **Termination**: Programs always finish
- **Type safety**: No runtime errors from undefined cases
- **Verification**: Properties can be proven about all inputs

### Structural Recursion

Recursive functions must be **structurally recursive** - the recursive call must be on a structurally smaller argument.

This is automatically checked by Rocq and ensures termination.

### Example: Valid Complete Function

```
Definition negb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.
```

All cases are covered!

This design choice makes Rocq suitable for formal verification and mathematical proofs.
@ENDTHEORY*)

(*@START:
Require Import Bool.Bool.

(* Define a complete function that returns true for true, false for false *)
(* Make sure to handle all cases! *)
Definition identity_bool (b : bool) : bool :=
  (* Your code here *)
@ENDSTART*)

(*@SOLUTION:
Require Import Bool.Bool.

Definition identity_bool (b : bool) : bool :=
  match b with
  | true => true
  | false => false
  end.
@ENDSOLUTION*)

(*===========================================*)
(*@LEVEL: basics_15*)
(*@LEVEL_META: {
  "id": "basics_15",
  "name": "Basic Proof Tactics Overview",
  "description": "Introduction to proof tactics in Rocq",
  "difficulty": 1,
  "estimatedTime": 20,
  "objective": "Understand the basic proof tactics",
  "hints": [
    "Tactics are commands that build proofs",
    "intro introduces variables",
    "reflexivity proves equalities"
  ],
  "rewards": {
    "xp": 30
  }
}*)

(*@THEORY:
## Basic Proof Tactics

From Lecture 1: Ltac is the tactic language for constructing proofs interactively.

### The Proof Environment

When you write:
```
Theorem name : statement.
Proof.
  (* tactics here *)
Qed.
```

You enter "proof mode" where you use tactics to build the proof.

### Basic Tactics

**intro / intros**: Introduces variables or hypotheses
```
intro n.              (* Introduce one variable *)
intros n m H.         (* Introduce multiple *)
```

**reflexivity**: Proves goals of the form `x = x`
```
reflexivity.          (* Proves n = n *)
```

**simpl**: Simplifies expressions by computation
```
simpl.                (* Computes 2 + 3 to 5 *)
```

**exact**: Uses a hypothesis or lemma that exactly matches the goal
```
exact H.              (* When H : P and goal is P *)
```

**rewrite**: Uses an equality to transform the goal
```
rewrite H.            (* Replace left side with right *)
rewrite <- H.         (* Replace right side with left *)
```

**destruct**: Case analysis on a value
```
destruct b.           (* Split into true and false cases *)
```

**induction**: Proof by induction (gives inductive hypothesis)
```
induction n.          (* Base case and inductive step *)
```

### Proof Structure

```
Theorem example : forall n, n = n.
Proof.
  intro n.            (* Bring n into context *)
  reflexivity.        (* Prove n = n *)
Qed.                  (* Complete the proof *)
```

Tactics are the building blocks of interactive theorem proving!
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.

(* Prove that 5 = 5 *)
Theorem five_equals_five : 5 = 5.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
Require Import Init.Nat.

Theorem five_equals_five : 5 = 5.
Proof.
  reflexivity.
Qed.
@ENDSOLUTION*)

(*===========================================*)
(*@LEVEL: basics_16*)
(*@LEVEL_META: {
  "id": "basics_16",
  "name": "Theorem vs Lemma vs Example",
  "description": "Understand the different ways to state theorems",
  "difficulty": 1,
  "estimatedTime": 15,
  "objective": "Know when to use Theorem, Lemma, or Example",
  "hints": [
    "Theorem for main results",
    "Lemma for helper results",
    "Example for demonstrations"
  ],
  "rewards": {
    "xp": 20
  }
}*)

(*@THEORY:
## Theorem, Lemma, and Example

From Lecture 1 & 2: Rocq provides different keywords for stating mathematical results.

### Theorem

Used for main, important results:

```
Theorem main_result : forall n, n + 0 = n.
Proof.
  (* proof *)
Qed.
```

### Lemma

Used for helper results that support main theorems:

```
Lemma helper_lemma : forall n, 0 + n = n.
Proof.
  (* proof *)
Qed.

Theorem main_result : forall n, n + 0 = n.
Proof.
  (* uses helper_lemma *)
Qed.
```

### Example

Used for demonstrations and exercises:

```
Example simple_example : 2 + 2 = 4.
Proof.
  reflexivity.
Qed.
```

### When to Use Which?

- **Theorem**: Important, reusable results
- **Lemma**: Supporting facts used in proofs
- **Example**: Demonstrations, exercises, test cases

### All Are Equivalent

From Rocq's perspective, `Theorem`, `Lemma`, and `Example` are all equivalent.
The choice is purely for documentation and code organization.

### Fact, Remark, Corollary

Rocq also supports:
- `Fact`: Similar to Example
- `Remark`: For observations
- `Corollary`: For consequences of theorems

Choose the keyword that best describes your result's role!
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.

(* Write an Example showing that 3 + 2 = 5 *)
(* Your example here *)
@ENDSTART*)

(*@SOLUTION:
Require Import Init.Nat.

Example three_plus_two : 3 + 2 = 5.
Proof.
  reflexivity.
Qed.
@ENDSOLUTION*)

(*===========================================*)
(*@LEVEL: basics_17*)
(*@LEVEL_META: {
  "id": "basics_17",
  "name": "Searching the Library",
  "description": "Learn how to find existing theorems and definitions",
  "difficulty": 1,
  "estimatedTime": 20,
  "objective": "Use Search to find library functions",
  "hints": [
    "Search finds definitions by name or pattern",
    "SearchPattern finds by type signature",
    "Locate finds where notations are defined"
  ],
  "rewards": {
    "xp": 30
  }
}*)

(*@THEORY:
## Searching the Library

From Lecture 1: Rocq's standard library is vast. Use search commands to find what you need.

### Search Command

Finds definitions related to a term:

```
Search nat.           (* All definitions mentioning nat *)
Search plus.          (* All definitions mentioning plus *)
```

### SearchPattern

Finds by type pattern:

```
SearchPattern (_ + _ = _ + _).    (* Theorems about addition *)
SearchPattern (nat -> nat -> nat). (* Functions nat -> nat -> nat *)
```

### Locate

Finds where a notation is defined:

```
Locate "+".           (* Shows where + is defined *)
Locate "++".          (* Shows where ++ is defined *)
```

### About

Shows information about a specific identifier:

```
About plus.           (* Information about plus function *)
```

### Print

Shows the definition:

```
Print plus.           (* Full definition of plus *)
```

### Example from Lecture

```
Search nat.           (* Returns list of values related to nat *)
Search "_ + _".       (* Search by pattern *)
Locate "+".           (* Shows: "x + y" := Nat.add x y *)
```

These commands are essential for exploring Rocq's extensive standard library!
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.

(* Use Search to find theorems about multiplication *)
(* Your command here *)

(* Use Locate to find where * is defined *)
(* Your command here *)
@ENDSTART*)

(*@SOLUTION:
Require Import Init.Nat.

SearchPattern (nat -> nat -> nat).  (* Finds functions like mult *)
Locate "*".                          (* Shows where * is defined *)
@ENDSOLUTION*)

(*===========================================*)
(*@LEVEL: basics_18*)
(*@LEVEL_META: {
  "id": "basics_18",
  "name": "Proof by Computation",
  "description": "Learn when reflexivity can prove equalities automatically",
  "difficulty": 1,
  "estimatedTime": 15,
  "objective": "Use reflexivity to prove computational equalities",
  "hints": [
    "reflexivity can prove things that compute to the same value",
    "It automatically simplifies both sides",
    "Works for any decidable equality"
  ],
  "rewards": {
    "xp": 25
  }
}*)

(*@THEORY:
## Proof by Computation

From Lecture 1: Rocq can automatically prove many equalities by computation.

### Reflexivity and Computation

The `reflexivity` tactic can prove goals where both sides compute to the same value:

```
Theorem two_plus_two : 2 + 2 = 4.
Proof.
  reflexivity.        (* Automatically computes 2+2 to 4 *)
Qed.
```

### Simpl Before Reflexivity

Sometimes you need `simpl` first:

```
Theorem example : 2 + 3 = 5.
Proof.
  simpl.              (* Simplifies 2 + 3 to 5 *)
  reflexivity.        (* Proves 5 = 5 *)
Qed.
```

### When It Works

Reflexivity works when:
- Both sides are syntactically equal: `n = n`
- Both sides compute to the same value: `2 + 2 = 4`
- The equality is definitionally equal

### When You Need More

For non-computational equalities, you need other tactics:
- `rewrite` for using hypotheses
- `induction` for recursive properties
- `destruct` for case analysis

### Example from Lecture

```
Theorem dva_plus_tri : 2 + 3 = 5.
Proof.
  simpl.              (* zjednoduší 2 + 3 na 5 *)
  reflexivity.        (* 5 = 5 *)
Qed.

Theorem dva_plus_tri' : 2 + 3 = 5.
Proof.
  reflexivity.        (* Also works directly! *)
Qed.
```

Computation is a powerful tool for proving equalities!
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.

(* Prove that 10 + 5 = 15 using reflexivity *)
Theorem ten_plus_five : 10 + 5 = 15.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
Require Import Init.Nat.

Theorem ten_plus_five : 10 + 5 = 15.
Proof.
  reflexivity.
Qed.
@ENDSOLUTION*)

(*===========================================*)
(*@LEVEL: basics_19*)
(*@LEVEL_META: {
  "id": "basics_19",
  "name": "Admitted and Incomplete Proofs",
  "description": "Learn about Admitted for incomplete proofs",
  "difficulty": 1,
  "estimatedTime": 10,
  "objective": "Understand when to use Admitted",
  "hints": [
    "Admitted accepts a proof without proving it",
    "Useful during development",
    "Creates a 'hole' in the proof"
  ],
  "rewards": {
    "xp": 15
  }
}*)

(*@THEORY:
## Admitted and Incomplete Proofs

From Lecture 1: The `Admitted` keyword allows you to accept a theorem without proving it.

### Syntax

```
Theorem incomplete : statement.
Proof.
  (* some tactics *)
  Admitted.           (* Accept without proof *)
```

### When to Use

- **During development**: When you want to use a lemma before proving it
- **Prototyping**: To test the structure of a larger proof
- **Learning**: To focus on one part while temporarily accepting others

### Warning

`Admitted` creates a "hole" in your proof - Rocq accepts it as if it were proven,
but it's not actually verified. Use with caution!

### Example from Lecture

```
Theorem example_rewrite_chain' :
  forall n, n = n + 0 -> n + 1 = (n + 0) + 1.
Proof.
  intros n H.
  rewrite H.          (* rewrite in wrong direction *)
  Admitted.           (* Incomplete proof *)
```

### Best Practice

- Mark admitted proofs clearly
- Replace with actual proofs before finalizing
- Use for development, not in production code

Admitted is a useful development tool, but always complete your proofs!
@ENDTHEORY*)

(*@START:
(* This is informational - understand when Admitted is used *)
(* No code to write *)
@ENDSTART*)

(*@SOLUTION:
(* Informational level - no solution needed *)
@ENDSOLUTION*)

(*===========================================*)
(*@LEVEL: basics_20*)
(*@LEVEL_META: {
  "id": "basics_20",
  "name": "Rocq File Structure",
  "description": "Understand how Rocq files are organized",
  "difficulty": 1,
  "estimatedTime": 15,
  "objective": "Understand Rocq file organization",
  "hints": [
    "Files typically start with Require Import",
    "Then definitions and theorems",
    "Comments use (* ... *)"
  ],
  "rewards": {
    "xp": 20
  }
}*)

(*@THEORY:
## Rocq File Structure

From Lecture 1 & 2: Rocq files follow a typical structure.

### Typical File Organization

1. **Imports** (at the top):
```
Require Import Init.Nat.
Require Import Bool.Bool.
Import ListNotations.
```

2. **Definitions**:
```
Definition x := 10.
Fixpoint factorial (n : nat) : nat := ...
```

3. **Inductive Types**:
```
Inductive day : Type := ...
```

4. **Theorems and Proofs**:
```
Theorem example : statement.
Proof.
  (* tactics *)
Qed.
```

### Comments

Rocq uses `(* ... *)` for comments:

```
(* This is a comment *)
Definition x := 10.  (* Inline comment *)
```

Multi-line comments nest:
```
(* Outer comment
   (* Inner comment *)
   More outer comment *)
```

### Modules

You can organize code in modules:

```
Module MyModule.
  (* definitions *)
End MyModule.
```

### Best Practices

- Group related definitions together
- Use modules for organization
- Comment complex definitions
- Import only what you need

Good organization makes Rocq code maintainable and readable!
@ENDTHEORY*)

(*@START:
(* This is informational - understand file structure *)
(* No code to write *)
@ENDSTART*)

(*@SOLUTION:
(* Informational level - no solution needed *)
@ENDSOLUTION*)

