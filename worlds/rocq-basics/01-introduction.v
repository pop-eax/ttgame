(*@WORLD: {
  "id": "rocq-basics",
  "name": "Rocq Basics",
  "description": "Learn the fundamentals of the Rocq proof assistant: its languages, syntax, and core features",
  "order": 1,
  "icon": "🔧",
  "color": "#10b981",
  "estimatedHours": 8,
  "tags": ["basics", "syntax", "features", "rocq"],
  "availableTheorems": []
}*)

(*===========================================*)
(*@LEVEL: basics_1*)
(*@LEVEL_META: {
  "id": "basics_1",
  "name": "What is Rocq?",
  "description": "Introduction to Rocq and its components",
  "difficulty": 1,
  "estimatedTime": 10,
  "objective": "Understand what Rocq is and its main components",
  "hints": [
    "Rocq is an interactive proof assistant",
    "It consists of multiple languages",
    "It's based on type theory"
  ],
  "rewards": {
    "xp": 20
  }
}*)

(*@THEORY:
# What is Rocq?

**Rocq** (originally **Coq**) is an interactive proof assistant (proof assistant).

## Components of Rocq

Rocq consists of several languages:

1. **Gallina**: The basic functional language based on type theory
   - Used for writing programs and definitions
   - Strongly typed functional programming
   - Based on the Calculus of Inductive Constructions

2. **Vernacular**: The command language
   - Commands like: `Definition`, `Inductive`, `Lemma`, `Theorem`, `Print`, `Check`, `Compute`
   - Used to define objects, state theorems, and query the system

3. **Ltac**: The tactic language
   - Tactics for constructing proofs interactively
   - Examples: `intro`, `reflexivity`, `rewrite`, `induction`, `destruct`
   - Allows step-by-step proof construction

## Type Theory Foundation

Rocq is based on **type theory**, specifically the **Calculus of Inductive Constructions** (CIC).

This provides:
- Strong type safety
- Mathematical rigor
- Ability to prove properties of programs
- Integration of programming and proving

## Official Resources

- Official website: https://rocq-prover.org/
- Documentation: https://rocq-prover.org/docs
- Wikipedia: https://en.wikipedia.org/wiki/Calculus_of_constructions

## Key Features

- **Interactive theorem proving**: Build proofs step by step
- **Program verification**: Prove properties about your programs
- **Extraction**: Extract verified programs to other languages
- **Rich standard library**: Extensive mathematical and computational libraries
@ENDTHEORY*)

(*@START:
(* This is a knowledge level - no code to write *)
(* Just read the theory and understand Rocq's components *)
@ENDSTART*)

(*@SOLUTION:
(* This level is informational - no solution needed *)
@ENDSOLUTION*)

(*===========================================*)
(*@LEVEL: basics_2*)
(*@LEVEL_META: {
  "id": "basics_2",
  "name": "Basic Vernacular Commands",
  "description": "Learn the essential Vernacular commands for querying and defining",
  "difficulty": 1,
  "estimatedTime": 15,
  "objective": "Use Check, Print, and Compute commands",
  "hints": [
    "Check tells you the type of an expression",
    "Print shows the definition",
    "Compute evaluates an expression"
  ],
  "rewards": {
    "xp": 25
  }
}*)

(*@THEORY:
## Basic Vernacular Commands

From Lecture 1: Querying and controlling Rocq through Vernacular language commands.

### Check Command

The `Check` command tells you the type of any expression:

```
Check 1.              (* 1 : nat *)
Check nat.            (* nat : Set *)
Check (1 + 1).        (* 1 + 1 : nat *)
```

### Print Command

The `Print` command shows the definition of an identifier:

```
Definition x := 10.
Print x.              (* Shows: x = 10 : nat *)
```

### Compute Command

The `Compute` command evaluates an expression:

```
Compute (1 + 1).      (* = 2 : nat *)
Compute (succ 10).    (* = 11 : nat *)
```

### About Command

The `About` command provides information about an identifier:

```
About plus.           (* Shows information about the plus function *)
```

### Search Command

The `Search` command finds definitions related to a pattern:

```
Search nat.           (* Returns list of values related to nat *)
Search "_ + _".       (* Search by pattern *)
```

### Locate Command

The `Locate` command finds where a notation is defined:

```
Locate "+".           (* Shows where + is defined *)
```

These commands are essential for exploring and understanding Rocq's type system and library!
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.

(* Use Check to find the type of the number 5 *)
(* Your command here *)

(* Use Compute to evaluate 2 + 3 *)
(* Your command here *)

(* Use Print to see the definition of nat *)
(* Your command here *)
@ENDSTART*)

(*@SOLUTION:
Require Import Init.Nat.

Check 5.
(* 5 : nat *)

Compute (2 + 3).
(* = 5 : nat *)

Print nat.
(* Shows the definition of nat *)
@ENDSOLUTION*)

(*===========================================*)
(*@LEVEL: basics_3*)
(*@LEVEL_META: {
  "id": "basics_3",
  "name": "Defining Variables and Functions",
  "description": "Learn how to define variables and functions using Definition",
  "difficulty": 1,
  "estimatedTime": 15,
  "objective": "Define a variable and a simple function",
  "hints": [
    "Use Definition for both variables and functions",
    "Function syntax: Definition name (param : type) : return_type := body.",
    "Don't forget the period at the end"
  ],
  "rewards": {
    "xp": 30
  }
}*)

(*@THEORY:
## Defining Variables and Functions

From Lecture 1: The `Definition` keyword is used to define both variables and functions.

### Defining Variables

```
Definition x := 10.
Definition name := value.
```

### Defining Functions

Functions can take parameters:

```
Definition succ (x : nat) : nat := x + 1.
```

Syntax: `Definition name (param : type) : return_type := body.`

### Function Types

Functions in Rocq have types like `nat -> nat` (function from nat to nat).

For multiple parameters: `nat -> nat -> nat` (curried function).

### Examples

```
Definition x := 10.
Definition succ (x : nat) : nat := x + 1.
Definition plus x y := x + y.  (* plus : nat -> nat -> nat *)
```

### Partial Application

Functions are curried, so you can partially apply them:

```
Definition plus2 := plus 2.    (* plus2 : nat -> nat *)
Compute plus2 3.               (* = 5 *)
```

This is a fundamental feature of functional programming!
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.

(* Define a variable y with value 20 *)
(* Your definition here *)

(* Define a function double that multiplies a number by 2 *)
(* Your definition here *)
@ENDSTART*)

(*@SOLUTION:
Require Import Init.Nat.

Definition y := 20.

Definition double (x : nat) : nat := x * 2.
@ENDSOLUTION*)

(*===========================================*)
(*@LEVEL: basics_4*)
(*@LEVEL_META: {
  "id": "basics_4",
  "name": "Type System and Type Hierarchy",
  "description": "Understand Rocq's type system and the type hierarchy",
  "difficulty": 2,
  "estimatedTime": 20,
  "objective": "Understand the difference between Set, Prop, and Type",
  "hints": [
    "Set is the universe of data types",
    "Prop is the universe of logical propositions",
    "Type is the universe of all types"
  ],
  "rewards": {
    "xp": 30
  }
}*)

(*@THEORY:
## Type System and Type Hierarchy

From Lecture 1: Rocq has a rich type system with a hierarchy of universes.

### Type Hierarchy

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

### Key Concepts

- **Set**: The universe of computational types (data types)
- **Prop**: The universe of logical propositions (proofs)
- **Type**: The universe containing both Set and Prop

### Examples

```
Check Set.              (* Set : Type *)
Check Prop.             (* Prop : Type *)
Check Type.             (* Type : Type1 *)

Check bool.             (* bool : Set *)
Check nat.              (* nat : Set *)
Check True.             (* True : Prop *)
Check (3 = 4).          (* 3 = 4 : Prop *)
```

This separation between data (Set) and proofs (Prop) is fundamental to Rocq's design!
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.
Require Import Bool.Bool.

(* Check the type of Set *)
(* Your command here *)

(* Check the type of a boolean value *)
(* Your command here *)

(* Check the type of a proposition (equality) *)
(* Your command here *)
@ENDSTART*)

(*@SOLUTION:
Require Import Init.Nat.
Require Import Bool.Bool.

Check Set.
(* Set : Type *)

Check true.
(* true : bool *)

Check (3 = 4).
(* 3 = 4 : Prop *)
@ENDSOLUTION*)

(*===========================================*)
(*@LEVEL: basics_5*)
(*@LEVEL_META: {
  "id": "basics_5",
  "name": "Pattern Matching",
  "description": "Learn pattern matching with match expressions",
  "difficulty": 2,
  "estimatedTime": 20,
  "objective": "Write a function using pattern matching",
  "hints": [
    "Use match ... with to pattern match",
    "Each case is separated by |",
    "End with end."
  ],
  "rewards": {
    "xp": 35
  }
}*)

(*@THEORY:
## Pattern Matching

From Lecture 1: Pattern matching is a fundamental feature for working with inductive types.

### Match Syntax

```
match expression with
| pattern1 => result1
| pattern2 => result2
| ...
end
```

### Pattern Matching on Booleans

```
Definition negb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.
```

### Pattern Matching on Natural Numbers

Natural numbers have two constructors:
- `O` (zero)
- `S n` (successor of n)

```
Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.
```

### Complete Functions

**Important**: In Rocq, all functions must be complete - they must handle all possible cases.
Unlike languages like Haskell or OCaml, you cannot have partial pattern matching.

This ensures all functions terminate and are well-defined for all inputs.
@ENDTHEORY*)

(*@START:
Require Import Bool.Bool.

(* Define a function is_zero that returns true if n is 0, false otherwise *)
(* Use pattern matching on nat *)
Definition is_zero (n : nat) : bool :=
  (* Your code here *)
@ENDSTART*)

(*@SOLUTION:
Require Import Bool.Bool.

Definition is_zero (n : nat) : bool :=
  match n with
  | O => true
  | S _ => false
  end.
@ENDSOLUTION*)

(*===========================================*)
(*@LEVEL: basics_6*)
(*@LEVEL_META: {
  "id": "basics_6",
  "name": "Recursive Functions with Fixpoint",
  "description": "Learn how to define recursive functions using Fixpoint",
  "difficulty": 2,
  "estimatedTime": 25,
  "objective": "Define a recursive function using Fixpoint",
  "hints": [
    "Use Fixpoint for recursive functions",
    "The function must be structurally recursive",
    "Pattern match to handle base and recursive cases"
  ],
  "rewards": {
    "xp": 40
  }
}*)

(*@THEORY:
## Recursive Functions

From Lecture 1: Recursive functions are defined using the `Fixpoint` keyword.

### Fixpoint Syntax

```
Fixpoint function_name (params) : return_type :=
  match param with
  | base_case => base_result
  | recursive_case => recursive_call
  end.
```

### Example: Factorial

```
Fixpoint factorial (n : nat) : nat :=
  match n with
  | 0 => 1
  | S n' => n * factorial n'
  end.
```

### Structural Recursion

Rocq requires **structural recursion** - the recursive call must be on a structurally smaller argument.
This ensures termination.

In the factorial example:
- Base case: `0` (smallest)
- Recursive case: `factorial n'` where `n'` is smaller than `S n'`

### Mutual Recursion

You can define mutually recursive functions using `with`:

```
Fixpoint is_even (n : nat) : bool :=
  match n with
  | 0 => true
  | S n => is_odd n
  end
with is_odd (n : nat) : bool :=
  match n with
  | 0 => false
  | S n => is_even n
  end.
```

This allows functions to call each other recursively!
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.

(* Define a recursive function sum that adds all numbers from 0 to n *)
(* sum 0 = 0, sum 1 = 1, sum 2 = 3, etc. *)
Fixpoint sum (n : nat) : nat :=
  (* Your code here *)
@ENDSTART*)

(*@SOLUTION:
Require Import Init.Nat.

Fixpoint sum (n : nat) : nat :=
  match n with
  | O => O
  | S n' => S n' + sum n'
  end.
@ENDSOLUTION*)

(*===========================================*)
(*@LEVEL: basics_7*)
(*@LEVEL_META: {
  "id": "basics_7",
  "name": "Inductive Types",
  "description": "Learn how to define custom inductive types",
  "difficulty": 2,
  "estimatedTime": 25,
  "objective": "Define a custom inductive type",
  "hints": [
    "Use Inductive keyword",
    "Each constructor must have a unique name",
    "Constructors can take parameters"
  ],
  "rewards": {
    "xp": 40
  }
}*)

(*@THEORY:
## Inductive Types

From Lecture 1: The `Inductive` keyword is used to define custom data types.

### Basic Syntax

```
Inductive TypeName : Type :=
  | Constructor1 : Type1 -> TypeName
  | Constructor2 : Type2 -> TypeName
  | ...
  | ConstructorN : TypeN -> TypeName.
```

### Key Points

- Each constructor must have a unique name
- Constructors can take parameters
- Inductive types can have multiple parameters
- The type defines all possible ways to create values of that type

### Example: Days of the Week

```
Inductive day : Type :=
  | Monday
  | Tuesday
  | Wednesday
  | Thursday
  | Friday
  | Saturday
  | Sunday.
```

### Example: Natural Numbers

Even `nat` is defined inductively:

```
Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.
```

This says: a natural number is either:
- `O` (zero), or
- `S n` (successor of some natural number n)

### Pattern Matching with Inductive Types

Once defined, you can pattern match on inductive types:

```
Definition next_day (d : day) : day :=
  match d with
  | Monday => Tuesday
  | Tuesday => Wednesday
  | ...
  | Sunday => Monday
  end.
```

Inductive types are the foundation of data structures in Rocq!
@ENDTHEORY*)

(*@START:
(* Define an inductive type for colors: Red, Green, Blue *)
(* Your definition here *)

(* Define a function that returns the next color in sequence *)
(* Red -> Green -> Blue -> Red *)
Definition next_color (c : color) : color :=
  (* Your code here *)
@ENDSTART*)

(*@SOLUTION:
Inductive color : Type :=
  | Red
  | Green
  | Blue.

Definition next_color (c : color) : color :=
  match c with
  | Red => Green
  | Green => Blue
  | Blue => Red
  end.
@ENDSOLUTION*)

(*===========================================*)
(*@LEVEL: basics_8*)
(*@LEVEL_META: {
  "id": "basics_8",
  "name": "Polymorphic Functions",
  "description": "Learn how to write functions that work with any type",
  "difficulty": 2,
  "estimatedTime": 20,
  "objective": "Define a polymorphic identity function",
  "hints": [
    "Use type parameters: (A : Type)",
    "The function works for any type A",
    "This is called polymorphism"
  ],
  "rewards": {
    "xp": 35
  }
}*)

(*@THEORY:
## Polymorphic Functions

From Lecture 1: Polymorphic functions work with any type, making code reusable.

### Type Parameters

You can parameterize functions by type:

```
Definition id_poly (A : Type) (x : A) : A := x.
```

This function works for any type `A`!

### Type Inference

Rocq can often infer types:

```
Compute id_poly nat 3.     (* 3 : nat *)
Compute id_poly _ 3.       (* _ means "infer the type" *)
```

### Implicit Type Arguments

You can make type arguments implicit using curly braces:

```
Definition id_poly3 {A : Type} (x : A) : A := x.
Compute id_poly3 3.        (* Type is inferred automatically *)
```

### Explicit Type Application

Use `@` to make implicit arguments explicit:

```
Compute @id_poly3 nat 3.   (* Explicitly provide the type *)
```

### Example: Polymorphic List Functions

```
Definition head {A : Type} (l : list A) (default : A) : A :=
  match l with
  | [] => default
  | h :: _ => h
  end.
```

This works for lists of any type: `list nat`, `list bool`, `list (list nat)`, etc.

Polymorphism is essential for writing reusable, generic code!
@ENDTHEORY*)

(*@START:
(* Define a polymorphic function that returns the first element of a pair *)
(* It should work for pairs of any type *)
Definition first {A B : Type} (p : A * B) : A :=
  (* Your code here *)
@ENDSTART*)

(*@SOLUTION:
Definition first {A B : Type} (p : A * B) : A :=
  match p with
  | (x, y) => x
  end.
@ENDSOLUTION*)

(*===========================================*)
(*@LEVEL: basics_9*)
(*@LEVEL_META: {
  "id": "basics_9",
  "name": "Lambda Functions",
  "description": "Learn anonymous (lambda) functions",
  "difficulty": 1,
  "estimatedTime": 15,
  "objective": "Use lambda functions",
  "hints": [
    "Syntax: fun x => expression",
    "Lambda functions are anonymous",
    "They can be used anywhere a function is expected"
  ],
  "rewards": {
    "xp": 30
  }
}*)

(*@THEORY:
## Anonymous (Lambda) Functions

From Lecture 1: Lambda functions allow you to define functions inline without naming them.

### Syntax

```
fun x => expression
```

### Examples

```
Definition id_nat : nat -> nat := fun x => x.
```

This is equivalent to:

```
Definition id_nat' (x : nat) : nat := x.
```

### Using Lambdas

Lambdas are useful for:
- Passing functions as arguments
- Returning functions from functions
- Defining functions inline

### Example: Higher-Order Functions

```
Definition apply_twice {A : Type} (f : A -> A) (x : A) : A :=
  f (f x).

Compute apply_twice (fun n => n + 1) 5.
(* = 7 : nat *)
```

### Multiple Parameters

```
fun x y => x + y
```

This is equivalent to:

```
fun x => fun y => x + y
```

Lambda functions are a fundamental feature of functional programming!
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.

(* Define a function that adds 5 to a number using a lambda *)
Definition add_five : nat -> nat :=
  (* Your code here *)
@ENDSTART*)

(*@SOLUTION:
Require Import Init.Nat.

Definition add_five : nat -> nat :=
  fun x => x + 5.
@ENDSOLUTION*)

(*===========================================*)
(*@LEVEL: basics_10*)
(*@LEVEL_META: {
  "id": "basics_10",
  "name": "Let Expressions",
  "description": "Learn local definitions with let",
  "difficulty": 1,
  "estimatedTime": 15,
  "objective": "Use let to define local variables",
  "hints": [
    "Syntax: let name := value in expression",
    "You can nest multiple lets",
    "Useful for intermediate calculations"
  ],
  "rewards": {
    "xp": 25
  }
}*)

(*@THEORY:
## Let Expressions

From Lecture 1: The `let` construction allows you to define local variables within an expression.

### Syntax

```
let name := value in
expression
```

### Example

```
Definition add_xy : nat :=
  let x := 10 in
  let y := 20 in
  x + y.
```

### Nested Lets

You can nest multiple `let` expressions:

```
let x := 5 in
let y := 10 in
let z := x + y in
z * 2
```

### Scope

Variables defined with `let` are only available in the expression after `in`.

### Use Cases

- Breaking down complex calculations
- Naming intermediate results for clarity
- Avoiding repetition in expressions

Let expressions make code more readable and maintainable!
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.

(* Use let to compute (2 + 3) * (4 + 5) with intermediate variables *)
Definition result : nat :=
  (* Your code here *)
@ENDSTART*)

(*@SOLUTION:
Require Import Init.Nat.

Definition result : nat :=
  let a := 2 + 3 in
  let b := 4 + 5 in
  a * b.
@ENDSOLUTION*)

