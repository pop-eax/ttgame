(*@LEVEL: level_19*)

(*@LEVEL_META: {
  "id": "level_19",
  "name": "Double Function",
  "description": "Prove a property about the double function.",
  "difficulty": 3,
  "estimatedTime": 6,
  "objective": "Prove that double n = n + n.",
  "hints": ["Use induction on n", "You'll need plus_n_Sm", "Simpl will compute double"],
  "unlockedTactics": [],
  "rewards": { "xp": 25 }
}*)

(*@THEORY:
## Proof by Induction

The `Fixpoint` keyword defines recursive functions.

For double:
```
Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.
```

### Induction Principle

Proof by induction for a statement that some property P(n) holds for all n : nat:

1. **Base case**: Show that P(0) holds.
2. **Inductive step**: Show that if P(n') holds, then P(S n') also holds.
3. **Conclusion**: From 1. and 2. it follows that P(n) holds for all n.

Formally: (P(0) ∧ ∀n.(P(n) → P(S n))) → ∀n.P(n)

### Difference between destruct and induction:

- **destruct**: Used for case analysis according to constructors. Does not extend the proof with an inductive hypothesis. Typical for bool, small cases of nat.

- **induction**: Used when the property requires recursion. In addition to dividing into cases, we also get an inductive hypothesis. Typical for proofs about nat, list, or other recursive structures.

### Example from Lecture:

```
Theorem plus_n_O : forall n : nat, n + 0 = n.
Proof.
  intro n.
  induction n as [| n' IH].
  - (* Base case: n = 0 *)
    simpl. reflexivity.
  - (* Inductive step: assume n' + 0 = n' (IH),
       then prove (S n') + 0 = S n' *)
    simpl.
    rewrite IH.
    reflexivity.
Qed.
```

Prove that double n = n + n using induction on n.
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.
Require Import Arith.PeanoNat.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma plus_n_Sm : forall n m, S (n + m) = n + (S m).
Proof. intros. induction n. reflexivity. simpl. rewrite IHn. reflexivity. Qed.

Lemma double_plus : forall n, double n = n + n.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intro n.
  induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. rewrite plus_n_Sm. reflexivity.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_20*)

(*@LEVEL_META: {
  "id": "level_20",
  "name": "Even Successor",
  "description": "Prove even (S n) = negb (even n).",
  "difficulty": 3,
  "estimatedTime": 7,
  "objective": "Work with the even function from the standard library.",
  "hints": ["Use induction on n", "Destruct (even n') in the inductive step", "Both cases lead to reflexivity"],
  "unlockedTactics": [],
  "rewards": { "xp": 30 }
}*)

(*@THEORY:
The `even` function from the standard library is defined as:
- even 0 = true
- even (S n) = negb (even n)

But we need to prove this property holds!

Use induction and case analysis on what even computes to.
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.
Require Import Bool.Bool.
Require Import Arith.PeanoNat.

Theorem even_S : forall n : nat, even (S n) = negb (even n).
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intro n.
  induction n as [| n' IH].
  - simpl. reflexivity.
  - rewrite IH. 
    destruct (even n').
    + simpl. reflexivity.
    + simpl. reflexivity.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_21*)

(*@LEVEL_META: {
  "id": "level_21",
  "name": "Addition Shuffle",
  "description": "Prove n + (m + p) = m + (n + p).",
  "difficulty": 3,
  "estimatedTime": 6,
  "objective": "Use commutativity and associativity together.",
  "hints": ["Use add_assoc to group differently", "Use add_comm to swap n and m", "Chain the rewrites together"],
  "unlockedTactics": [],
  "rewards": { "xp": 25 }
}*)

(*@THEORY:
This can be proved using:
- Commutativity: a + b = b + a
- Associativity: a + (b + c) = (a + b) + c

Think about the structure:
n + (m + p) = (n + m) + p = (m + n) + p = m + (n + p)

You can use `rewrite add_comm` and `rewrite add_assoc`.
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.
Require Import Arith.PeanoNat.

Lemma add_comm : forall n m, n + m = m + n.
Proof. 
  intros. induction n. 
  - simpl. induction m. reflexivity. simpl. rewrite <- IHm. reflexivity.
  - simpl. rewrite IHn. induction m. reflexivity. simpl. rewrite <- IHm. reflexivity.
Qed.

Lemma add_assoc : forall n m p, n + (m + p) = (n + m) + p.
Proof. intros. induction n. reflexivity. simpl. rewrite IHn. reflexivity. Qed.

Theorem add_shuffle3 : forall n m p : nat, n + (m + p) = m + (n + p).
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intros n m p.
  rewrite add_assoc.
  rewrite (add_comm n m).
  rewrite <- add_assoc.
  reflexivity.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_22*)

(*@LEVEL_META: {
  "id": "level_22",
  "name": "Commutativity of Multiplication",
  "description": "The big theorem: multiplication is commutative!",
  "difficulty": 5,
  "estimatedTime": 15,
  "objective": "Prove m * n = n * m.",
  "hints": ["You'll need several helper lemmas", "Use mul_n_Sm lemma in the inductive step", "This is challenging - take your time!"],
  "unlockedTactics": [],
  "rewards": { "xp": 100, "achievements": ["multiplication_master"] }
}*)

(*@THEORY:
This is significantly more complex than addition.

You'll need helper lemmas:
- n * 0 = 0
- n * 1 = n
- n * (S m) = n + (n * m)

Strategy: Induction on n, then use the helper lemmas.

This is a challenging proof - take your time!
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.
Require Import Arith.PeanoNat.

Lemma mul_0_r : forall n, n * 0 = 0.
Proof. intro. induction n. reflexivity. simpl. exact IHn. Qed.

Lemma add_comm : forall n m, n + m = m + n.
Proof. 
  intros. induction n. 
  - simpl. induction m. reflexivity. simpl. rewrite <- IHm. reflexivity.
  - simpl. rewrite IHn. induction m. reflexivity. simpl. rewrite <- IHm. reflexivity.
Qed.

Lemma add_assoc : forall n m p, n + (m + p) = (n + m) + p.
Proof. intros. induction n. reflexivity. simpl. rewrite IHn. reflexivity. Qed.

Lemma mul_n_Sm : forall n m, n * (S m) = n + (n * m).
Proof.
  intros. induction n.
  - reflexivity.
  - simpl. rewrite IHn. 
    rewrite <- (add_assoc n m (n * m)).
    rewrite (add_comm n m).
    rewrite add_assoc.
    reflexivity.
Qed.

Theorem mul_comm : forall m n : nat, m * n = n * m.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intros m n.
  induction n as [| n' IH].
  - rewrite mul_0_r. reflexivity.
  - rewrite mul_n_Sm. simpl. rewrite IH. reflexivity.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_23*)

(*@LEVEL_META: {
  "id": "level_23",
  "name": "Pairs - First Projection",
  "description": "Work with pairs and the fst function.",
  "difficulty": 1,
  "estimatedTime": 3,
  "objective": "Prove that fst (n, m) = n.",
  "hints": ["Simpl will unfold the fst definition", "Then reflexivity", "Pairs are simple!"],
  "unlockedTactics": [],
  "rewards": { "xp": 15 }
}*)

(*@THEORY:
## Data Structures - Pairs

From Lecture 3: In this section we get acquainted with basic data structures
in the Rocq environment, which are the foundation for data representation
and logical reasoning about programs.

### Pairs

A pair is a product type containing two values. In Rocq, pairs are defined as:

```
Inductive prod (A B : Type) : Type :=
| pair : A -> B -> prod A B.
```

The only way to create a pair is to apply the `pair` constructor to two arguments.

### Projection Functions

To extract values from a pair, we need projection functions:

```
Definition fst {A B} (p : A * B) : A :=
  match p with
  | (x, y) => x
  end.

Definition snd {A B} (p : A * B) : B :=
  match p with
  | (x, y) => y
  end.
```

The notation `(x, y)` is syntactic sugar for `(pair x y)`.

### Standard Notation

The standard library provides the notation `(x, y)` for pairs, and you can use it
in pattern matching as well.
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.

Theorem fst_pair : forall (n m : nat), fst (n, m) = n.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intros n m.
  simpl.
  reflexivity.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_24*)

(*@LEVEL_META: {
  "id": "level_24",
  "name": "Pair Reconstruction",
  "description": "Prove p = (fst p, snd p).",
  "difficulty": 2,
  "estimatedTime": 5,
  "objective": "Use destruct to expose pair structure.",
  "hints": ["Use 'destruct p as [n m]'", "This splits the pair into components", "Then simpl and reflexivity"],
  "unlockedTactics": [],
  "rewards": { "xp": 20 }
}*)

(*@THEORY:
For any pair p, we have: p = (fst p, snd p)

This requires `destruct` on the pair to expose its structure.

When you `destruct p`, it splits into `(a, b)` for some a and b, then you can reason about the components.
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.

Theorem pair_reconstruction : forall (p : nat * nat),
  p = (fst p, snd p).
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intro p.
  destruct p as [n m].
  simpl.
  reflexivity.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_25*)

(*@LEVEL_META: {
  "id": "level_25",
  "name": "Swap Involution",
  "description": "Prove swap (swap p) = p.",
  "difficulty": 2,
  "estimatedTime": 4,
  "objective": "Prove that swap is an involution.",
  "hints": ["Destruct the pair", "Simpl will compute swap twice", "Should simplify to reflexivity"],
  "unlockedTactics": [],
  "rewards": { "xp": 20 }
}*)

(*@THEORY:
The swap function is defined as:
Definition swap (p : nat * nat) : nat * nat :=
match p with
| (a, b) => (b, a)
end.
An involution is a function where f(f(x)) = x.

Prove that swap is an involution.
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.

Definition swap (p : nat * nat) : nat * nat :=
  match p with
  | (a, b) => (b, a)
  end.

Theorem swap_swap : forall (p : nat * nat), swap (swap p) = p.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intro p.
  destruct p as [n m].
  simpl.
  reflexivity.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_26*)

(*@LEVEL_META: {
  "id": "level_26",
  "name": "Lists - Nil Append",
  "description": "Prove [] ++ l = l.",
  "difficulty": 1,
  "estimatedTime": 3,
  "objective": "Work with list append.",
  "hints": ["Simpl evaluates [] ++ l directly", "The definition makes this easy", "Then reflexivity"],
  "unlockedTactics": [],
  "rewards": { "xp": 15 }
}*)

(*@THEORY:
## Introduction to Lists

From Lecture 3: Lists are dynamic data structures that can grow or shrink.
They are one of the most fundamental data structures in functional programming.

### List Definition

Lists are defined inductively:
```
Inductive list (A : Type) : Type :=
  | nil : list A
  | cons : A -> list A -> list A.
```

Notation:
- `[]` for `nil` (empty list)
- `h :: t` for `cons h t` (head and tail)
- `[1;2;3]` for `cons 1 (cons 2 (cons 3 nil))`

### Append Function

The append function (`++`) joins two lists:
```
Fixpoint append (l1 l2: list A) : list A :=
  match l1 with
  | [] => l2
  | head::tail => head::(append tail l2)
  end.
```

So `[] ++ l` simplifies directly to `l` by the definition - when the first list is empty,
append just returns the second list.
@ENDTHEORY*)

(*@START:
Require Import List.
Import ListNotations.

Theorem nil_app : forall (l : list nat), [] ++ l = l.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intro l.
  simpl.
  reflexivity.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_27*)

(*@LEVEL_META: {
  "id": "level_27",
  "name": "Lists - App Nil",
  "description": "Prove l ++ [] = l.",
  "difficulty": 2,
  "estimatedTime": 5,
  "objective": "Use induction on lists.",
  "hints": ["This requires induction on l", "Base case: [] ++ [] = []", "Inductive step: use IH after simpl"],
  "unlockedTactics": [],
  "rewards": { "xp": 20 }
}*)

(*@THEORY:
## Induction on Lists

From Lecture 3: The principle of induction over lists is completely analogous
to induction over natural numbers, just the constructor `x::xs` replaces the successor `n+1`.

### Induction Principle for Lists

Rocq automatically generates two subgoals when using `induction l`:
- **Base case**: `[]` (empty list)
- **Inductive case**: `x::xs` (head and tail)

The pattern:
- **Base case**: P([])
- **Inductive hypothesis**: ∀x.∀xs.(P(xs) => P(x::xs))
- **Goal**: ∀l.P(l)

### This Exercise

This requires induction because append recurses on the first argument!

**Base case**: `[] ++ [] = []` - both sides are the empty list.

**Inductive step**: 
```
(h :: t) ++ [] = h :: (t ++ [])    [by definition of append]
               = h :: t             [by IH: t ++ [] = t]
```

The pattern: when the recursive structure is on the left, you need induction.

### Example from Lecture:

```
Theorem l_app_nil : forall l, l++[]=l.
Proof.
  intros. 
  induction l.
  - reflexivity.                    (* base case *)
  - simpl. rewrite IHl. reflexivity. (* inductive step *)
Qed.
```
@ENDTHEORY*)

(*@START:
Require Import List.
Import ListNotations.

Theorem app_nil : forall (l : list nat), l ++ [] = l.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intro l.
  induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_28*)

(*@LEVEL_META: {
  "id": "level_28",
  "name": "Associativity of Append",
  "description": "Prove list append is associative.",
  "difficulty": 3,
  "estimatedTime": 6,
  "objective": "Prove (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).",
  "hints": ["Induction on l1", "Notice the parallel with addition", "Base case is simple, inductive step uses IH"],
  "unlockedTactics": [],
  "rewards": { "xp": 25 }
}*)

(*@THEORY:
## Lists and Induction

### Lists in Rocq

Lists are dynamic data structures that can grow or shrink. They are defined inductively:

```
Inductive list (A : Type) : Type :=
  | nil : list A
  | cons : A -> list A -> list A.
```

Notation: `[]` for nil, `h :: t` for cons h t, `[1;2;3]` for lists.

### List Functions

**Append** (`++`) joins two lists:
```
Fixpoint append (l1 l2: list A) : list A :=
  match l1 with
  | [] => l2
  | head::tail => head::(append tail l2)
  end.
```

### Induction on Lists

From Lecture 3: The principle of induction over lists is completely analogous to induction over natural numbers, just the constructor `x::xs` replaces the successor `n+1`.

- **Base case**: P([])
- **Inductive hypothesis**: ∀x.∀xs.(P(xs) => P(x::xs))
- **Goal**: ∀l.P(l)

Rocq automatically generates two subgoals when using `induction l`:
- Base case: []
- Inductive case: x::xs

### Associativity of Append

Just like addition, append is associative:
(l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)

Use induction on l1. Notice the parallel with addition:
- [] is like 0
- (::) is like S
- (++) is like (+)

This is not a coincidence - they're all monoids!
@ENDTHEORY*)

(*@START:
Require Import List.
Import ListNotations.

Theorem app_assoc : forall (l1 l2 l3 : list nat),
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intros l1 l2 l3.
  induction l1 as [| h t IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_29*)

(*@LEVEL_META: {
  "id": "level_29",
  "name": "Length of Tail",
  "description": "Relate length and tail.",
  "difficulty": 2,
  "estimatedTime": 4,
  "objective": "Prove pred (length l) = length (tail l).",
  "hints": ["Destruct l into cases", "Case []: both sides are 0", "Case h::t: both sides are length t"],
  "unlockedTactics": [],
  "rewards": { "xp": 20 }
}*)

(*@THEORY:
The `pred` function returns the predecessor (n - 1, or 0 if n=0).

For a non-empty list, length (tail l) = pred (length l).

Use `destruct` on the list:
- If l = [], both sides equal 0
- If l = h :: t, length t = pred (S (length t))
@ENDTHEORY*)

(*@START:
Require Import List.
Import ListNotations.
Require Import Init.Nat.

Theorem pred_length : forall (l : list nat),
  pred (length l) = length (tail l).
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intro l.
  destruct l as [| h t].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_30*)

(*@LEVEL_META: {
  "id": "level_30",
  "name": "Reverse Length",
  "description": "Prove reversing doesn't change length.",
  "difficulty": 4,
  "estimatedTime": 10,
  "objective": "Prove length l = length (rev l).",
  "hints": ["You need a helper lemma first!", "Prove: length (l ++ [x]) = S (length l)", "Then use induction on main theorem"],
  "unlockedTactics": [],
  "rewards": { "xp": 40 }
}*)

(*@THEORY:
## Reverse and Helper Lemmas

### Reverse Function

From Lecture 3, the reverse function flips the order of elements:
```
Fixpoint reverse (l : list A) : list A :=
  match l with 
  | [] => []
  | hd::tl => (reverse tl) ++ [hd]
  end.
```

### Helper Lemmas

When proving properties about reverse, you often need helper lemmas first.

**Helper Lemma**: `length (l ++ [x]) = S (length l)`

This says: appending a single element increases the length by one.

### Main Theorem: Reverse Preserves Length

You'll need the helper lemma first, then use induction on l for the main theorem.

**Base case**: `length (rev []) = length []` - both are 0.

**Inductive step**: 
```
length (rev (h :: t)) = length ((rev t) ++ [h])
                      = S (length (rev t))      [by helper lemma]
                      = S (length t)            [by IH]
                      = length (h :: t)
```

The key insight: reversing a list doesn't change its length, but the proof requires understanding how reverse builds the result by appending elements.
@ENDTHEORY*)

(*@START:
Require Import List.
Import ListNotations.
Require Import Init.Nat.

Lemma length_app_one : forall (l : list nat) (n : nat),
  length (l ++ [n]) = S (length l).
Proof.
  intros l n.
  induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Theorem rev_length : forall (l : list nat),
  length l = length (rev l).
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intro l.
  induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. rewrite length_app_one. rewrite <- IH. reflexivity.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_31*)

(*@LEVEL_META: {
  "id": "level_31",
  "name": "Reverse Distribution",
  "description": "Prove rev (l1 ++ l2) = rev l2 ++ rev l1.",
  "difficulty": 4,
  "estimatedTime": 10,
  "objective": "Prove that reverse distributes over append.",
  "hints": ["Induction on l1", "Use app_assoc in the inductive step", "Base case needs app_nil"],
  "unlockedTactics": [],
  "rewards": { "xp": 40 }
}*)

(*@THEORY:
## Reverse Distribution Over Append

This is a beautiful theorem from Lecture 3:
```
rev (l1 ++ l2) = (rev l2) ++ (rev l1)
```

### Intuitive Understanding

Think about it intuitively: 
- Reversing `[1;2;3;4;5]` gives `[5;4;3;2;1]`
- If we split it as `[1;2] ++ [3;4;5]`
- Reversing gives `[5;4;3] ++ [2;1]`

Notice: the order of l1 and l2 is swapped in the result!

### Proof Strategy

Use induction on l1 and the associativity of append (`app_assoc`).

**Base case** (l1 = []):
```
rev ([] ++ l2) = rev l2 = (rev l2) ++ [] = (rev l2) ++ (rev [])
```

**Inductive step** (l1 = h :: t):
```
rev ((h :: t) ++ l2) = rev (h :: (t ++ l2))
                     = (rev (t ++ l2)) ++ [h]
                     = ((rev l2) ++ (rev t)) ++ [h]  [by IH]
                     = (rev l2) ++ ((rev t) ++ [h])  [by app_assoc]
                     = (rev l2) ++ (rev (h :: t))
```

This theorem shows how reverse interacts with list concatenation!
@ENDTHEORY*)

(*@START:
Require Import List.
Import ListNotations.

Lemma app_assoc : forall (l1 l2 l3 : list nat),
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros. induction l1. reflexivity. simpl. rewrite IHl1. reflexivity.
Qed.

Lemma app_nil : forall (l : list nat), l ++ [] = l.
Proof.
  intro. induction l. reflexivity. simpl. rewrite IHl. reflexivity.
Qed.

Theorem rev_app_distr : forall (l1 l2 : list nat),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intros l1 l2.
  induction l1 as [| h t IH].
  - simpl. rewrite app_nil. reflexivity.
  - simpl. rewrite IH. rewrite app_assoc. reflexivity.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_32*)

(*@LEVEL_META: {
  "id": "level_32",
  "name": "Reverse Involution",
  "description": "Prove rev (rev l) = l.",
  "difficulty": 3,
  "estimatedTime": 7,
  "objective": "Prove that reversing twice gives the original.",
  "hints": ["Induction on l", "Use rev_app_distr", "Simpl in the inductive step"],
  "unlockedTactics": [],
  "rewards": { "xp": 30 }
}*)

(*@THEORY:
This is a classic theorem: rev (rev l) = l

Use:
- Induction on l
- The distribution property you just proved
- The fact that rev [x] = [x]

This completes our understanding of reverse!
@ENDTHEORY*)

(*@START:
Require Import List.
Import ListNotations.

Lemma rev_app_distr : forall (l1 l2 : list nat),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros. induction l1.
  - simpl. induction l2. reflexivity. simpl. rewrite <- IHl2. reflexivity.
  - simpl. rewrite IHl1. 
    induction l2. simpl. induction (rev l1). reflexivity. simpl. rewrite <- IHl. reflexivity.
    simpl. rewrite <- IHl2. simpl. 
    assert (H: forall l1 l2 l3, (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)).
    { intros. induction l0. reflexivity. simpl. rewrite IHl0. reflexivity. }
    rewrite H. reflexivity.
Qed.

Theorem rev_involutive : forall (l : list nat),
  rev (rev l) = l.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intro l.
  induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. rewrite rev_app_distr. simpl. rewrite IH. reflexivity.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_33*)

(*@LEVEL_META: {
  "id": "level_33",
  "name": "Option Type - None Case",
  "description": "Work with the Option type.",
  "difficulty": 3,
  "estimatedTime": 8,
  "objective": "Prove nth_error returns None past the end.",
  "hints": ["Use 'generalize dependent n'", "Then induction on l", "Use injection when needed"],
  "unlockedTactics": ["generalize dependent", "injection"],
  "rewards": { "xp": 35 }
}*)

(*@THEORY:
The Option type represents computations that might fail:
Inductive option (A : Type) : Type :=
| Some : A -> option A
| None : option A.
It's used for functions that aren't defined everywhere.

For example, nth_error returns None when the index is out of bounds.

Prove that accessing past the end of a list returns None.
@ENDTHEORY*)

(*@START:
Require Import List.
Import ListNotations.
Require Import Init.Nat.

Theorem nth_error_after_last : forall (n : nat) (l : list nat),
  length l = n -> nth_error l n = None.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intros n l.
  generalize dependent n.
  induction l as [| h t IH].
  - intros n H. simpl. destruct n. reflexivity. reflexivity.
  - intros n H. destruct n.
    + simpl in H. discriminate H.
    + simpl in H. injection H as H'. simpl. apply IH. exact H'.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_34*)

(*@LEVEL_META: {
  "id": "level_34",
  "name": "Map Preserves Length",
  "description": "Prove map doesn't change length.",
  "difficulty": 2,
  "estimatedTime": 5,
  "objective": "Prove length (map f l) = length l.",
  "hints": ["Induction on l", "Base case is trivial", "Inductive step: simpl then rewrite IH"],
  "unlockedTactics": [],
  "rewards": { "xp": 20 }
}*)

(*@THEORY:
The `map` function applies a function to every element:
```
Fixpoint map {A B} (f : A -> B) (l : list A) : list B :=
match l with
| [] => []
| h :: t => f h :: map f t
end.
```
Prove by induction that length (map f l) = length l.

This makes sense: map transforms elements but preserves structure!
@ENDTHEORY*)

(*@START:
Require Import List.
Import ListNotations.

Theorem map_length : forall (A B : Type) (f : A -> B) (l : list A),
  length (map f l) = length l.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intros A B f l.
  induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_35*)

(*@LEVEL_META: {
  "id": "level_35",
  "name": "Map Distribution",
  "description": "Prove map distributes over append.",
  "difficulty": 3,
  "estimatedTime": 6,
  "objective": "Prove map f (l1 ++ l2) = map f l1 ++ map f l2.",
  "hints": ["Induction on l1", "Base case is simple", "Inductive step uses IH"],
  "unlockedTactics": [],
  "rewards": { "xp": 25 }
}*)

(*@THEORY:
map f (l1 ++ l2) = (map f l1) ++ (map f l2)

Intuitively: mapping over a concatenation is the same as mapping over each part and then concatenating.

Use induction on l1.

This is a fundamental property used in parallel programming!
@ENDTHEORY*)

(*@START:
Require Import List.
Import ListNotations.

Theorem map_app : forall (A B : Type) (f : A -> B) (l1 l2 : list A),
  map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intros A B f l1 l2.
  induction l1 as [| h t IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_36*)

(*@LEVEL_META: {
  "id": "level_36",
  "name": "Map and Reverse",
  "description": "Prove map and reverse commute.",
  "difficulty": 3,
  "estimatedTime": 7,
  "objective": "Prove map f (rev l) = rev (map f l).",
  "hints": ["Induction on l", "Use map_app in the inductive step", "The base case is trivial"],
  "unlockedTactics": [],
  "rewards": { "xp": 30 }
}*)

(*@THEORY:
map f (rev l) = rev (map f l)

Think about it: whether you reverse then map, or map then reverse, you get the same result!

Use induction on l and the map distribution property.

This is another beautiful compositionality property.
@ENDTHEORY*)

(*@START:
Require Import List.
Import ListNotations.

Lemma map_app : forall (A B : Type) (f : A -> B) (l1 l2 : list A),
  map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof.
  intros. induction l1. reflexivity. simpl. rewrite IHl1. reflexivity.
Qed.

Theorem map_rev : forall (A B : Type) (f : A -> B) (l : list A),
  map f (rev l) = rev (map f l).
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intros A B f l.
  induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. rewrite map_app. rewrite IH. reflexivity.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_37*)

(*@LEVEL_META: {
  "id": "level_37",
  "name": "Filter Preserves Order",
  "description": "If filter returns x, then test x = true.",
  "difficulty": 3,
  "estimatedTime": 8,
  "objective": "Prove filter only keeps elements that pass the test.",
  "hints": ["Induction on l", "Use destruct (test h) eqn:E", "Injection helps in one case"],
  "unlockedTactics": ["eqn"],
  "rewards": { "xp": 30 }
}*)

(*@THEORY:
The filter function:
Fixpoint filter {A} (test : A -> bool) (l : list A) : list A :=
match l with
| [] => []
| h :: t => if test h then h :: filter test t
else filter test t
end.
Prove: if x appears in filter test l, then test x = true.

Use induction and case analysis with destruct.
@ENDTHEORY*)

(*@START:
Require Import List.
Import ListNotations.
Require Import Bool.Bool.

Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                                 (x : X) (l lf : list X),
  filter test l = x :: lf -> test x = true.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intros X test x l lf H.
  induction l as [| h t IH].
  - simpl in H. discriminate H.
  - simpl in H. destruct (test h) eqn:E.
    + injection H as H1 H2. rewrite <- H1. exact E.
    + apply IH. exact H.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_38*)

(*@LEVEL_META: {
  "id": "level_38",
  "name": "Conjunction Introduction",
  "description": "Enter the world of logic!",
  "difficulty": 2,
  "estimatedTime": 4,
  "objective": "Prove P -> Q -> P /\\ Q.",
  "hints": ["Use split to prove a conjunction", "This creates two subgoals", "Use exact for each"],
  "unlockedTactics": ["split"],
  "rewards": { "xp": 20, "achievements": ["logic_beginner"] }
}*)

(*@THEORY:
In Rocq, logical AND is written P /\\ Q.

To prove P /\\ Q, use the `split` tactic, which creates two subgoals:
- Prove P
- Prove Q

This is the introduction rule for conjunction.

From premises P and Q, conclude P /\\ Q.
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.

Theorem and_intro : forall P Q : Prop, P -> Q -> P /\ Q.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intros P Q HP HQ.
  split.
  - exact HP.
  - exact HQ.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_39*)

(*@LEVEL_META: {
  "id": "level_39",
  "name": "Conjunction Elimination",
  "description": "Extract information from a conjunction.",
  "difficulty": 2,
  "estimatedTime": 4,
  "objective": "From P /\\ Q, derive P.",
  "hints": ["Use destruct H as [HP HQ]", "This splits the conjunction", "Then use exact HP"],
  "unlockedTactics": [],
  "rewards": { "xp": 20 }
}*)

(*@THEORY:
To use a hypothesis H : P /\\ Q, you can:
- Use `destruct H as [HP HQ]` to split it into two hypotheses
- Or use `destruct H` which will auto-name them

This is the elimination rule for conjunction.

From P /\\ Q, derive both P and Q.
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.

Theorem and_elim_left : forall P Q : Prop, P /\ Q -> P.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intros P Q H.
  destruct H as [HP HQ].
  exact HP.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_40*)

(*@LEVEL_META: {
  "id": "level_40",
  "name": "Conjunction Commutativity",
  "description": "Prove AND is commutative.",
  "difficulty": 2,
  "estimatedTime": 5,
  "objective": "Prove P /\\ Q -> Q /\\ P.",
  "hints": ["Destruct the hypothesis", "Split the goal", "Match them up correctly"],
  "unlockedTactics": [],
  "rewards": { "xp": 20 }
}*)

(*@THEORY:
P /\\ Q implies Q /\\ P.

Strategy:
1. Destruct the hypothesis P /\\ Q into HP and HQ
2. Split the goal Q /\\ P
3. Prove Q using HQ, then prove P using HP

This shows the symmetry of conjunction.
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.

Theorem and_commut : forall P Q : Prop, P /\ Q -> Q /\ P.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intros P Q H.
  destruct H as [HP HQ].
  split.
  - exact HQ.
  - exact HP.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_41*)

(*@LEVEL_META: {
  "id": "level_41",
  "name": "Disjunction Introduction",
  "description": "Learn the introduction rules for OR.",
  "difficulty": 2,
  "estimatedTime": 4,
  "objective": "From P, prove P \\/ Q.",
  "hints": ["Use 'left' to prove the left side", "Then exact HP", "You don't need Q!"],
  "unlockedTactics": ["left", "right"],
  "rewards": { "xp": 20 }
}*)

(*@THEORY:
OR has two introduction rules:
- From P, conclude P \\/ Q (use `left`)
- From Q, conclude P \\/ Q (use `right`)

This proof demonstrates the left introduction.

If you have P, you can conclude P \\/ Q for any Q!
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.

Theorem or_intro_left : forall P Q : Prop, P -> P \/ Q.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intros P Q HP.
  left.
  exact HP.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_42*)

(*@LEVEL_META: {
  "id": "level_42",
  "name": "Disjunction Elimination",
  "description": "Reason by cases with OR.",
  "difficulty": 3,
  "estimatedTime": 6,
  "objective": "Prove (P \\/ Q) -> (P -> R) -> (Q -> R) -> R.",
  "hints": ["Destruct H as [HP | HQ]", "This creates two cases", "Apply the appropriate implication in each"],
  "unlockedTactics": ["apply"],
  "rewards": { "xp": 25 }
}*)

(*@THEORY:
To use H : P \\/ Q, use `destruct H as [HP | HQ]`.

This creates two subgoals:
- One assuming HP : P
- One assuming HQ : Q

This is proof by cases: if either P or Q leads to R, then (P \\/ Q) → R.

This is the elimination rule for disjunction.
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.

Theorem or_elim : forall P Q R : Prop, 
  P \/ Q -> (P -> R) -> (Q -> R) -> R.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intros P Q R H HPR HQR.
  destruct H as [HP | HQ].
  - apply HPR. exact HP.
  - apply HQR. exact HQ.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_43*)

(*@LEVEL_META: {
  "id": "level_43",
  "name": "Disjunction Commutativity",
  "description": "Prove OR is commutative.",
  "difficulty": 2,
  "estimatedTime": 5,
  "objective": "Prove P \\/ Q -> Q \\/ P.",
  "hints": ["Destruct into two cases", "Case P: use right", "Case Q: use left"],
  "unlockedTactics": [],
  "rewards": { "xp": 20 }
}*)

(*@THEORY:
P \\/ Q implies Q \\/ P.

Strategy:
1. Destruct P \\/ Q into two cases
2. Case P: use `right` to prove Q \\/ P
3. Case Q: use `left` to prove Q \\/ P

This combines introduction and elimination of disjunction.
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.

Theorem or_commut : forall P Q : Prop, P \/ Q -> Q \/ P.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intros P Q H.
  destruct H as [HP | HQ].
  - right. exact HP.
  - left. exact HQ.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_44*)

(*@LEVEL_META: {
  "id": "level_44",
  "name": "Negation Introduction",
  "description": "Learn about negation in constructive logic.",
  "difficulty": 2,
  "estimatedTime": 5,
  "objective": "Understand ~P as P -> False.",
  "hints": ["Use 'unfold not'", "This expands ~P to P -> False", "Then exact H"],
  "unlockedTactics": ["unfold"],
  "rewards": { "xp": 20 }
}*)

(*@THEORY:
In Rocq, ~P is defined as P -> False.

To prove ~P, assume P and derive a contradiction (False).

The `unfold not` tactic expands ~P to P -> False.

Then you can use standard implication reasoning.
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.

Theorem not_intro : forall P : Prop, (P -> False) -> ~P.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intros P H.
  unfold not.
  exact H.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_45*)

(*@LEVEL_META: {
  "id": "level_45",
  "name": "Contrapositive",
  "description": "Prove the law of contrapositive.",
  "difficulty": 3,
  "estimatedTime": 7,
  "objective": "Prove (P -> Q) -> (~Q -> ~P).",
  "hints": ["Unfold not in the goal", "Assume P to prove False", "Chain: P gives Q, Q with ~Q gives False"],
  "unlockedTactics": [],
  "rewards": { "xp": 30 }
}*)

(*@THEORY:
The contrapositive: (P → Q) → (¬Q → ¬P)

If P implies Q, then not-Q implies not-P.

Strategy:
1. Assume P → Q and ¬Q
2. Assume P (to prove ¬P)
3. From P and P → Q, derive Q
4. From Q and ¬Q, derive False

This is a fundamental law of logic!
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.

Theorem contrapositive : forall P Q : Prop, (P -> Q) -> (~Q -> ~P).
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intros P Q HPQ HnQ.
  unfold not.
  intro HP.
  apply HnQ.
  apply HPQ.
  exact HP.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_46*)

(*@LEVEL_META: {
  "id": "level_46",
  "name": "No Contradiction",
  "description": "Prove the law of non-contradiction.",
  "difficulty": 3,
  "estimatedTime": 6,
  "objective": "Prove ~ (P /\\ ~P).",
  "hints": ["Unfold not and intro", "Destruct the conjunction", "Apply ~P to P"],
  "unlockedTactics": [],
  "rewards": { "xp": 25 }
}*)

(*@THEORY:
~ (P /\\ ~P)

This is the law of non-contradiction.

A proposition and its negation cannot both be true.

Strategy:
1. Assume P /\\ ~P
2. Destruct to get P and ~P
3. Apply ~P to P to get False
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.

Theorem not_both_true_and_false : forall P : Prop, ~ (P /\ ~P).
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intro P.
  unfold not.
  intro H.
  destruct H as [HP HnP].
  apply HnP.
  exact HP.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_47*)

(*@LEVEL_META: {
  "id": "level_47",
  "name": "De Morgan's Law",
  "description": "Prove one of De Morgan's laws.",
  "difficulty": 4,
  "estimatedTime": 8,
  "objective": "Prove ~(P \\/ Q) -> ~P /\\ ~Q.",
  "hints": ["Split the conjunction", "For each part, unfold not", "Show that assuming P or Q leads to contradiction"],
  "unlockedTactics": [],
  "rewards": { "xp": 35 }
}*)

(*@THEORY:
~(P \\/ Q) → (~P /\\ ~Q)

If neither P nor Q is true, then both are false.

Strategy:
1. Assume ~(P \\/ Q)
2. To prove ~P: assume P, derive P \\/ Q, get contradiction
3. To prove ~Q: assume Q, derive P \\/ Q, get contradiction

De Morgan's laws connect negation with conjunction/disjunction.
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.

Theorem de_morgan_not_or : forall P Q : Prop,
  ~ (P \/ Q) -> ~P /\ ~Q.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intros P Q H.
  split.
  - unfold not. intro HP. apply H. left. exact HP.
  - unfold not. intro HQ. apply H. right. exact HQ.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_48*)

(*@LEVEL_META: {
  "id": "level_48",
  "name": "Distributivity of OR over AND",
  "description": "Prove a fundamental law of propositional logic.",
  "difficulty": 4,
  "estimatedTime": 10,
  "objective": "Prove P \\/ (Q /\\ R) <-> (P \\/ Q) /\\ (P \\/ R).",
  "hints": ["Split into two directions", "Forward: destruct the disjunction", "Backward: destruct both conjuncts"],
  "unlockedTactics": [],
  "rewards": { "xp": 40 }
}*)

(*@THEORY:
P \\/ (Q /\\ R) <-> (P \\/ Q) /\\ (P \\/ R)

The `<->` means "if and only if" (iff), which requires proving both directions.

Use `split` to separate into:
- Forward direction: →
- Backward direction: ←

Each direction requires its own proof strategy.

This is a fundamental law of propositional logic.
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.

Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intros P Q R.
  split.
  - intro H. destruct H as [HP | [HQ HR]].
    + split. left. exact HP. left. exact HP.
    + split. right. exact HQ. right. exact HR.
  - intro H. destruct H as [[HP | HQ] [HP' | HR]].
    + left. exact HP.
    + left. exact HP.
    + left. exact HP'.
    + right. split. exact HQ. exact HR.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_49*)

(*@LEVEL_META: {
  "id": "level_49",
  "name": "Existential Introduction",
  "description": "Learn about existential quantification.",
  "difficulty": 2,
  "estimatedTime": 4,
  "objective": "Prove ∃m, n + 2 = m.",
  "hints": ["Use 'exists (n + 2)'", "Provide a concrete witness", "Then reflexivity"],
  "unlockedTactics": ["exists"],
  "rewards": { "xp": 20 }
}*)

(*@THEORY:
To prove ∃x, P(x), use `exists t` where t is a concrete value.

Then prove P(t).

Example: To prove ∃n, n + 2 = 5, use `exists 3` and prove 3 + 2 = 5.

The `exists` tactic is the introduction rule for ∃.
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.

Theorem exists_intro : forall n : nat, exists m : nat, n + 2 = m.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intro n.
  exists (n + 2).
  reflexivity.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_50*)

(*@LEVEL_META: {
  "id": "level_50",
  "name": "Existential Elimination",
  "description": "Extract information from an existential.",
  "difficulty": 3,
  "estimatedTime": 6,
  "objective": "Use an existential hypothesis.",
  "hints": ["Destruct H as [n HP]", "This gives you a witness and a proof", "Apply H2 to get Q"],
  "unlockedTactics": [],
  "rewards": { "xp": 25 }
}*)

(*@THEORY:
To use H : ∃x, P(x), use `destruct H as [x HP]`.

This gives you:
- A witness x
- A proof HP that P(x) holds

This is the elimination rule for ∃.

From ∃x P(x) and the assumption that ∀x (P(x) → Q) where Q doesn't mention x, derive Q.
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.

Theorem exists_elim : forall (P : nat -> Prop) (Q : Prop),
  (exists n, P n) -> (forall n, P n -> Q) -> Q.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intros P Q H1 H2.
  destruct H1 as [n HP].
  apply H2.
  exact HP.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_51*)

(*@LEVEL_META: {
  "id": "level_51",
  "name": "Exists and Or",
  "description": "Prove existence distributes over disjunction.",
  "difficulty": 4,
  "estimatedTime": 10,
  "objective": "Prove (∃x, P x \\/ Q x) <-> (∃x, P x) \\/ (∃x, Q x).",
  "hints": ["Split into two directions", "Forward: destruct existential then disjunction", "Backward: destruct outer disjunction"],
  "unlockedTactics": [],
  "rewards": { "xp": 40 }
}*)

(*@THEORY:
(∃x, P x \\/ Q x) <-> (∃x, P x) \\/ (∃x, Q x)

If there exists an x satisfying P or Q, then either:
- There exists an x satisfying P, or
- There exists an x satisfying Q

This requires proof in both directions.

Forward: destruct the existential and the disjunction.
Backward: destruct the outer disjunction, then the inner existential.
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.

Theorem dist_exists_or : forall (P Q : nat -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intros P Q.
  split.
  - intro H. destruct H as [x [HP | HQ]].
    + left. exists x. exact HP.
    + right. exists x. exact HQ.
  - intro H. destruct H as [[x HP] | [x HQ]].
    + exists x. left. exact HP.
    + exists x. right. exact HQ.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_52*)

(*@LEVEL_META: {
  "id": "level_52",
  "name": "Discrimination",
  "description": "Learn about constructor discrimination.",
  "difficulty": 2,
  "estimatedTime": 4,
  "objective": "Use discriminate to solve impossible equations.",
  "hints": ["Use 'discriminate H'", "Different constructors are never equal", "This solves the goal immediately"],
  "unlockedTactics": ["discriminate"],
  "rewards": { "xp": 20 }
}*)

(*@THEORY:
Different constructors of an inductive type are never equal.

For example: 0 ≠ S n, true ≠ false, [] ≠ h :: t

The `discriminate` tactic recognizes this and solves goals where the hypothesis assumes such an equality.

If you have H : 0 = S n, then `discriminate H` solves the goal (because H is contradictory).
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.

Theorem discriminate_example : forall n : nat, 0 = S n -> 2 = 3.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intros n H.
  discriminate H.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_53*)

(*@LEVEL_META: {
  "id": "level_53",
  "name": "Injection",
  "description": "Learn about constructor injectivity.",
  "difficulty": 2,
  "estimatedTime": 5,
  "objective": "Use injection to peel off constructors.",
  "hints": ["Use 'injection H as H''", "This removes the outer S", "Then exact H'"],
  "unlockedTactics": [],
  "rewards": { "xp": 20 }
}*)

(*@THEORY:
Constructors are injective: if S n = S m, then n = m.

The `injection` tactic uses this fact.

`injection H as H'` takes H : S n = S m and produces H' : n = m.

Similarly for other constructors like (::): If h1 :: t1 = h2 :: t2, then h1 = h2 and t1 = t2.
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.

Theorem injection_example : forall n m : nat, S n = S m -> n = m.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intros n m H.
  injection H as H'.
  exact H'.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_54*)

(*@LEVEL_META: {
  "id": "level_54",
  "name": "Using Injection",
  "description": "Apply injection to a complex problem.",
  "difficulty": 4,
  "estimatedTime": 10,
  "objective": "Combine injection with rewriting.",
  "hints": ["Use injection twice", "Rewrite with H2", "Then another injection"],
  "unlockedTactics": [],
  "rewards": { "xp": 40 }
}*)

(*@THEORY:
When you have an equality of complex constructors, injection can peel off the outer constructor.

For lists: if x :: y :: l = z :: j and j = z :: l, you can inject to get the components.

Combine injection with other tactics to solve the goal.
@ENDTHEORY*)

(*@START:
Require Import List.
Import ListNotations.

Theorem injection_ex3 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  j = z :: l ->
  x = y.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intros X x y z l j H1 H2.
  injection H1 as H3 H4.
  rewrite H2 in H4.
  injection H4 as H5 H6.
  rewrite H3.
  exact H5.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_55*)

(*@LEVEL_META: {
  "id": "level_55",
  "name": "Leibniz Equality",
  "description": "Prove a deep property about equality.",
  "difficulty": 2,
  "estimatedTime": 4,
  "objective": "Prove f preserves equality.",
  "hints": ["Rewrite H to change n to m", "Then reflexivity", "Equality is substitutive"],
  "unlockedTactics": [],
  "rewards": { "xp": 20 }
}*)

(*@THEORY:
Leibniz's principle: if a = b, then P(a) = P(b) for any property P.

This means equal things are indistinguishable.

Use the `f_equal` tactic: if the goal is f x = f y, it reduces to proving x = y.

This is the substitutivity of equality.
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.

Theorem f_equal_example : forall (f : nat -> nat) (n m : nat),
  n = m -> f n = f m.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intros f n m H.
  rewrite H.
  reflexivity.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_56*)

(*@LEVEL_META: {
  "id": "level_56",
  "name": "Boolean Equality",
  "description": "Relate boolean and propositional equality.",
  "difficulty": 3,
  "estimatedTime": 7,
  "objective": "Prove n =? m = true implies n = m.",
  "hints": ["Use destruct (Nat.eqb_spec n m)", "This gives you reflection", "One case is exact, other is discriminate"],
  "unlockedTactics": [],
  "rewards": { "xp": 30 }
}*)

(*@THEORY:
For natural numbers, we have two notions of equality:
- Propositional: n = m (type Prop)
- Boolean: n =? m (type bool, returns true/false)

The `eqb_spec` provides a bridge between them.

`destruct (Nat.eqb_spec n m)` gives you cases:
- If n =? m = true, you get a proof that n = m
- If n =? m = false, you get a proof that n ≠ m

This is called "reflection" - reflecting computation into logic.
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.
Require Import Arith.PeanoNat.

Theorem eqb_true : forall n m, n =? m = true -> n = m.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intros n m H.
  destruct (Nat.eqb_spec n m) as [Heq | Hneq].
  - exact Heq.
  - discriminate H.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_57*)

(*@LEVEL_META: {
  "id": "level_57",
  "name": "Injectivity of Plus",
  "description": "If n + n = m + m, then n = m.",
  "difficulty": 5,
  "estimatedTime": 15,
  "objective": "Prove addition preserves distinctness.",
  "hints": ["Induction on n", "Base case: destruct m", "Inductive step needs multiple injections"],
  "unlockedTactics": [],
  "rewards": { "xp": 60 }
}*)

(*@THEORY:
This requires careful reasoning with induction and injection.

Strategy:
1. Use induction on n
2. Base case: 0 + 0 = m + m implies m = 0
3. Inductive step is trickier - you need to use injection carefully

This shows that addition preserves distinctness.
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.
Require Import Arith.PeanoNat.

Lemma plus_n_Sm : forall n m, S (n + m) = n + (S m).
Proof. intros. induction n. reflexivity. simpl. rewrite IHn. reflexivity. Qed.

Theorem plus_n_n_injective : forall n m, n + n = m + m -> n = m.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intro n.
  induction n as [| n' IH].
  - intros m H. destruct m. reflexivity. discriminate H.
  - intros m H. destruct m.
    + discriminate H.
    + apply f_equal. apply IH. 
      simpl in H. rewrite plus_n_Sm in H. rewrite plus_n_Sm in H.
      injection H as H'. injection H' as H''. exact H''.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_58*)

(*@LEVEL_META: {
  "id": "level_58",
  "name": "Boolean Functions",
  "description": "Prove a deep property about boolean functions.",
  "difficulty": 4,
  "estimatedTime": 10,
  "objective": "Prove f (f (f b)) = f b for any boolean function.",
  "hints": ["Destruct (f b) eqn:E", "Then destruct b", "Case analysis on all possibilities"],
  "unlockedTactics": [],
  "rewards": { "xp": 45 }
}*)

(*@THEORY:
For any boolean function f and boolean b: f (f (f b)) = f b

Why? There are only 4 boolean functions:
- constant true: f(x) = true
- constant false: f(x) = false  
- identity: f(x) = x
- negation: f(x) = not x

For each, verify that f(f(f(b))) = f(b).

Use destruct on f b to consider both possible values.
@ENDTHEORY*)

(*@START:
Require Import Bool.Bool.

Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intros f b.
  destruct (f b) eqn:E.
  - rewrite E. exact E.
  - destruct b.
    + destruct (f true) eqn:E2.
      * rewrite E2. exact E2.
      * rewrite E2. exact E.
    + destruct (f false) eqn:E2.
      * rewrite E2. exact E2.
      * rewrite E2. exact E.
Qed.
@ENDSOLUTION*)

