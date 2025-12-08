(*@WORLD: {
  "id": "introduction",
  "name": "Introduction to Type Theory",
  "description": "A comprehensive introduction to functional programming, formal proofs, and type theory using the Rocq proof assistant. Master the foundations of theorem proving through 70 carefully designed levels.",
  "order": 1,
  "icon": "🎓",
  "color": "#3B82F6",
  "estimatedHours": 15,
  "tags": ["basics", "induction", "logic", "data-structures"],
  "availableTheorems": ["plus_n_O", "add_comm", "add_assoc", "mul_comm", "app_assoc", "rev_app_distr"]
}*)

(*@LEVEL: level_1*)

(*@LEVEL_META: {
  "id": "level_1",
  "name": "Your First Proof",
  "description": "Welcome to Type Theory! Learn the most basic proof tactics.",
  "difficulty": 1,
  "estimatedTime": 3,
  "objective": "Prove that any natural number equals itself using intro and reflexivity.",
  "hints": ["Use 'intro n' to introduce the variable", "Use 'reflexivity' to prove n = n", "Remember to end with 'Qed.'"],
  "unlockedTactics": ["intro", "reflexivity"],
  "rewards": { "xp": 10 }
}*)

(*@THEORY:
In Rocq, we prove statements using tactics. The most basic tactics are:

**intro**: introduces a variable or hypothesis
**reflexivity**: proves that something equals itself

For example, to prove `forall n : nat, n = n`, we:
1. Use `intro n` to bring n into our context
2. Use `reflexivity` to prove `n = n`

The `forall` keyword means "for all" - we're proving something about ALL natural numbers.
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.

Theorem refl_nat : forall n : nat, n = n.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intro n.
  reflexivity.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_2*)

(*@LEVEL_META: {
  "id": "level_2",
  "name": "Using Hypotheses",
  "description": "Learn to use the exact tactic with hypotheses.",
  "difficulty": 1,
  "estimatedTime": 3,
  "objective": "Prove a simple implication using hypotheses.",
  "hints": ["Use 'intros' to introduce multiple things at once", "Use 'exact H' when you have exactly what you need", "The hypothesis H is your friend!"],
  "unlockedTactics": ["intros", "exact"],
  "rewards": { "xp": 10 }
}*)

(*@THEORY:
The `exact` tactic finishes a proof when you have exactly what you need.

When you have a hypothesis `H : P` and your goal is also `P`, you can write `exact H` to complete the proof.

The `intros` tactic (with an 's') can introduce multiple things at once:
- `intros n m` introduces both n and m
- `intros n m H` introduces n, m, and hypothesis H
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.

Theorem use_hypothesis : forall (n m : nat), n = m -> n = m.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intros n m H.
  exact H.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_3*)

(*@LEVEL_META: {
  "id": "level_3",
  "name": "Simple Computation",
  "description": "Use the simpl tactic to perform computation.",
  "difficulty": 1,
  "estimatedTime": 2,
  "objective": "Prove that 2 + 3 = 5 using computation.",
  "hints": ["Use 'simpl' to compute 2 + 3", "After simpl, use 'reflexivity'", "Let Rocq do the arithmetic!"],
  "unlockedTactics": ["simpl"],
  "rewards": { "xp": 10 }
}*)

(*@THEORY:
The `simpl` tactic performs computation. It evaluates expressions:
- `2 + 3` → `5`
- `S (S O)` → `2`

In Rocq, natural numbers are built from:
- `O` (zero)
- `S n` (successor of n)

So `2` is actually `S (S O)`, and `5` is `S (S (S (S (S O))))`.

After simplification, use `reflexivity` to complete the proof.
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.

Theorem two_plus_three : 2 + 3 = 5.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  simpl.
  reflexivity.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_4*)

(*@LEVEL_META: {
  "id": "level_4",
  "name": "Rewriting",
  "description": "Learn the powerful rewrite tactic.",
  "difficulty": 1,
  "estimatedTime": 4,
  "objective": "Use rewrite to transform the goal using an equality.",
  "hints": ["When you have H : a = b, use 'rewrite H'", "This replaces a with b in the goal", "Then use reflexivity"],
  "unlockedTactics": ["rewrite"],
  "rewards": { "xp": 15 }
}*)

(*@THEORY:
## Proof by Rewriting

From Lecture 1: The `rewrite` tactic is used when we have an equality in context
and want to use it to replace one side of the equation with the other.

When you have a hypothesis `H : a = b`, the `rewrite` tactic replaces `a` with `b`:

- `rewrite H` replaces left-to-right (a → b)
- `rewrite <- H` replaces right-to-left (b → a)

### Example from Lecture:

```
Theorem example_rewrite :
  forall n m : nat, n = m -> n + 1 = m + 1.
Proof.
  intros n m H.       (* n, m and assumption H: n = m *)
  rewrite H.          (* replace n with m in the goal *)
  reflexivity.        (* m + 1 = m + 1 *)
Qed.
```

This is one of the most powerful tactics in theorem proving!

The key insight: equality is preserved under function application. If `n = m`, then `f(n) = f(m)` for any function `f`.
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.

Theorem example_rewrite : forall n m : nat, n = m -> n + 1 = m + 1.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intros n m H.
  rewrite H.
  reflexivity.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_5*)

(*@LEVEL_META: {
  "id": "level_5",
  "name": "Backward Rewriting",
  "description": "Use rewrite in the opposite direction.",
  "difficulty": 1,
  "estimatedTime": 3,
  "objective": "Use backward rewrite with the <- arrow.",
  "hints": ["Use 'rewrite <- H' to rewrite from right to left", "This replaces m with n", "The arrow shows direction"],
  "unlockedTactics": [],
  "rewards": { "xp": 10 }
}*)

(*@THEORY:
The `<-` arrow reverses the direction of rewriting.

If `H : n = m`, then:
- `rewrite H` changes n to m
- `rewrite <- H` changes m to n

This is useful when you need to introduce complexity rather than simplify.
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.

Theorem example_rewrite_backwards : forall n m : nat, n = m -> m + 1 = n + 1.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intros n m H.
  rewrite <- H.
  reflexivity.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_6*)

(*@LEVEL_META: {
  "id": "level_6",
  "name": "Boolean Self-Equality",
  "description": "Learn case analysis with destruct.",
  "difficulty": 2,
  "estimatedTime": 5,
  "objective": "Prove that every boolean equals itself using case analysis.",
  "hints": ["Use 'destruct b' to split into cases", "Use '-' to mark each case", "Both cases can be solved with reflexivity"],
  "unlockedTactics": ["destruct"],
  "rewards": { "xp": 15 }
}*)

(*@THEORY:
The `destruct` tactic performs case analysis on an inductive type.

For `bool`, there are two cases: `true` and `false`.

Syntax: `destruct b.` creates two subgoals:
- One where b = true
- One where b = false

Use `-` to mark each case in your proof.
@ENDTHEORY*)

(*@START:
Require Import Bool.Bool.

Theorem bool_self : forall b : bool, b = b.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intro b.
  destruct b.
  - reflexivity.
  - reflexivity.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_7*)

(*@LEVEL_META: {
  "id": "level_7",
  "name": "OR with True",
  "description": "Prove a boolean property using destruct and simpl.",
  "difficulty": 2,
  "estimatedTime": 4,
  "objective": "Prove that b || true = true for any boolean b.",
  "hints": ["Destruct b into two cases", "Use simpl in each case to compute the OR", "Both cases should simplify nicely"],
  "unlockedTactics": [],
  "rewards": { "xp": 15 }
}*)

(*@THEORY:
Boolean OR (written ||) returns true if either operand is true.

When you destruct a boolean in the goal, simpl will compute the result:
- true || true = true
- false || true = true

This is a good pattern: destruct, then simpl, then reflexivity.
@ENDTHEORY*)

(*@START:
Require Import Bool.Bool.

Theorem orb_true : forall b : bool, b || true = true.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intro b.
  destruct b.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_8*)

(*@LEVEL_META: {
  "id": "level_8",
  "name": "Zero Plus N",
  "description": "Work with addition on natural numbers.",
  "difficulty": 1,
  "estimatedTime": 3,
  "objective": "Prove that 0 + n = n using simplification.",
  "hints": ["Addition on the left simplifies easily", "Use simpl to evaluate 0 + n", "Then reflexivity finishes it"],
  "unlockedTactics": [],
  "rewards": { "xp": 10 }
}*)

(*@THEORY:
Addition on natural numbers is defined recursively on the first argument:
0 + n = n
(S m) + n = S (m + n)
So `0 + n` simplifies directly to `n`.

This is why `simpl` works here without induction.
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intro n.
  simpl.
  reflexivity.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_9*)

(*@LEVEL_META: {
  "id": "level_9",
  "name": "One Plus N",
  "description": "Prove that 1 + n = S n.",
  "difficulty": 1,
  "estimatedTime": 3,
  "objective": "Use computation to prove a property about successor.",
  "hints": ["Remember 1 = S 0", "Simpl will compute (S 0) + n", "This is just applying the definition"],
  "unlockedTactics": [],
  "rewards": { "xp": 10 }
}*)

(*@THEORY:
Since 1 = S 0, we have:
1 + n = (S 0) + n

By the definition of addition:
(S 0) + n = S (0 + n) = S n

The `simpl` tactic will perform this computation for you.
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.

Theorem one_plus_n : forall n : nat, 1 + n = S n.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intro n.
  simpl.
  reflexivity.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_10*)

(*@LEVEL_META: {
  "id": "level_10",
  "name": "Chaining Rewrites",
  "description": "Use multiple rewrites in sequence.",
  "difficulty": 2,
  "estimatedTime": 4,
  "objective": "Prove transitivity of equality by chaining rewrites.",
  "hints": ["Use rewrite twice, once for each hypothesis", "First rewrite H1, then H2", "You can chain: rewrite H1, H2."],
  "unlockedTactics": [],
  "rewards": { "xp": 15 }
}*)

(*@THEORY:
You can use `rewrite` multiple times in sequence.

Each rewrite transforms the goal step by step until you can finish with `reflexivity`.

Tip: You can also chain rewrites with `rewrite H1, H2, H3.`
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.

Theorem trans_eq : forall n m k : nat, n = m -> m = k -> n = k.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intros n m k H1 H2.
  rewrite H1.
  rewrite H2.
  reflexivity.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_11*)

(*@LEVEL_META: {
  "id": "level_11",
  "name": "Plus Two",
  "description": "Apply rewrite to a function application.",
  "difficulty": 1,
  "estimatedTime": 3,
  "objective": "If n = m, then n + 2 = m + 2.",
  "hints": ["Rewrite H to change n to m", "Equality is preserved under functions", "Then reflexivity"],
  "unlockedTactics": [],
  "rewards": { "xp": 10 }
}*)

(*@THEORY:
This is a straightforward application of rewrite.

The key insight: equality is preserved under function application. If n = m, then f(n) = f(m) for any function f.

Here, f(x) = x + 2.
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.

Theorem plus_two : forall (n m : nat), n = m -> n + 2 = m + 2.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intros n m H.
  rewrite H.
  reflexivity.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_12*)

(*@LEVEL_META: {
  "id": "level_12",
  "name": "Your First Induction",
  "description": "Enter the realm of mathematical induction!",
  "difficulty": 3,
  "estimatedTime": 8,
  "objective": "Prove n + 0 = n using induction.",
  "hints": ["Use 'induction n as [| n' IH]'", "Base case: 0 + 0 = 0", "Inductive step: use IH in the rewrite"],
  "unlockedTactics": ["induction"],
  "rewards": { "xp": 25, "achievements": ["first_induction"] }
}*)

(*@THEORY:
Proof by induction on natural numbers has two steps:

**Base case**: Prove P(0)
**Inductive step**: Assume P(n') (the inductive hypothesis IH), then prove P(S n')

The tactic is: `induction n as [| n' IH].`

This creates two subgoals:
- Base: where n = 0
- Inductive: where n = S n', and you have IH : P(n')

The principle: P(0) ∧ (∀n. P(n) → P(S n)) → ∀n. P(n)
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.
Require Import Arith.PeanoNat.

Theorem plus_n_O : forall n : nat, n + 0 = n.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intro n.
  induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_13*)

(*@LEVEL_META: {
  "id": "level_13",
  "name": "Minus n n",
  "description": "Prove that n - n = 0.",
  "difficulty": 2,
  "estimatedTime": 5,
  "objective": "Use induction to prove a subtraction property.",
  "hints": ["Induction on n", "Base case is trivial", "In inductive step, use exact IH"],
  "unlockedTactics": [],
  "rewards": { "xp": 20 }
}*)

(*@THEORY:
## Your First Induction Proof

From Lecture 2: Proof by induction for a statement that some property P(n) holds for all n : nat:

1. **Base case**: Show that P(0) holds.
2. **Inductive step**: Show that if P(n') holds, then P(S n') also holds.
3. **Conclusion**: From 1. and 2. it follows that P(n) holds for all n.

### The Induction Tactic

When you use `induction n as [| n' IH]`:
- The first case `|` is the base case (n = 0)
- The second case `| n' IH` is the inductive step, where:
  - `n'` is the predecessor
  - `IH` is the inductive hypothesis: P(n') holds

### This Exercise

This requires induction because subtraction is defined recursively.

**Base case**: `0 - 0 = 0` (by definition)

**Inductive step**: 
```
(S n') - (S n') = n' - n' = 0  [by IH]
```

Remember to use your inductive hypothesis `IH`!

### Example Pattern from Lecture:

```
Theorem plus_n_O : forall n : nat, n + 0 = n.
Proof.
  intro n.
  induction n as [| n' IH].
  - (* Base case: n = 0 *)
    simpl. reflexivity.
  - (* Inductive step *)
    simpl.
    rewrite IH.
    reflexivity.
Qed.
```
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.
Require Import Arith.PeanoNat.

Theorem minus_n_n : forall n, minus n n = 0.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intro n.
  induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. exact IH.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_14*)

(*@LEVEL_META: {
  "id": "level_14",
  "name": "Multiplication by Zero",
  "description": "Prove that n * 0 = 0.",
  "difficulty": 2,
  "estimatedTime": 5,
  "objective": "Use induction to prove a multiplication property.",
  "hints": ["Induction on n", "Base: 0 * 0 = 0", "Step: (S n') * 0 = 0 + (n' * 0)"],
  "unlockedTactics": [],
  "rewards": { "xp": 20 }
}*)

(*@THEORY:
Multiplication is defined as:
- 0 * m = 0
- (S n) * m = m + (n * m)

So for n * 0, we need induction on n:
- Base: 0 * 0 = 0
- Step: (S n') * 0 = 0 + (n' * 0) = 0 + 0 = 0
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.
Require Import Arith.PeanoNat.

Theorem mul_0_r : forall n : nat, n * 0 = 0.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intro n.
  induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. exact IH.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_15*)

(*@LEVEL_META: {
  "id": "level_15",
  "name": "Multiplication by One",
  "description": "Prove that n * 1 = n.",
  "difficulty": 3,
  "estimatedTime": 7,
  "objective": "Combine induction with the plus_n_O lemma.",
  "hints": ["You'll need induction on n", "Use the lemma plus_n_O", "Base: 0 * 1 = 0, Step needs rewriting"],
  "unlockedTactics": [],
  "rewards": { "xp": 25 }
}*)

(*@THEORY:
## Combining Induction with Lemmas

From Lecture 2: In more complex proofs, you'll combine induction with previously proven lemmas.

### Using Existing Lemmas

When you have a lemma like `plus_n_O : forall n, n + 0 = n`, you can use it in your proofs with `rewrite plus_n_O`.

### This Exercise

You'll need:
- **Induction on n**
- **The fact that n + 0 = n** (which you proved earlier as `plus_n_O`!)

**Base case**: `0 * 1 = 0`

**Inductive step**: 
```
(S n') * 1 = 1 + (n' * 1)    [by definition of multiplication]
           = 1 + n'           [by IH: n' * 1 = n']
           = S n'             [by definition]
           = S n' + 0         [by plus_n_O]
```

### Pattern from Lecture:

```
Theorem example_rewrite_with_theorem :
  forall n, 0 + n + 1 = n + 1.
Proof.
  intro n.
  rewrite plus_O_n.   (* use lemma plus_O_n *)
  reflexivity.
Qed.
```

The key is recognizing when to apply your previously proven lemmas!
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.
Require Import Arith.PeanoNat.

Lemma plus_n_O : forall n, n + 0 = n.
Proof. intro. induction n. reflexivity. simpl. rewrite IHn. reflexivity. Qed.

Theorem mult_n_1 : forall n, n * 1 = n.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intro n.
  induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. rewrite plus_n_O. reflexivity.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_16*)

(*@LEVEL_META: {
  "id": "level_16",
  "name": "Successor Equality",
  "description": "Prove S (n + m) = n + (S m).",
  "difficulty": 3,
  "estimatedTime": 6,
  "objective": "Prove a key lemma about successor and addition.",
  "hints": ["Use induction on n", "Base case simplifies nicely", "f_equal can help in the inductive step"],
  "unlockedTactics": ["f_equal"],
  "rewards": { "xp": 25 }
}*)

(*@THEORY:
This is a key lemma about the interaction of successor and addition.

Use induction on n:
- Base: S (0 + m) = S m = 0 + (S m)
- Step: S ((S n') + m) = S (S (n' + m)) = S (n' + (S m)) = (S n') + (S m)

The `f_equal` tactic can be useful: if you need to prove `f a = f b`, it reduces the goal to proving `a = b`.
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.
Require Import Arith.PeanoNat.

Theorem plus_n_Sm : forall n m : nat, S (n + m) = n + (S m).
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intros n m.
  induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_17*)

(*@LEVEL_META: {
  "id": "level_17",
  "name": "Commutativity of Addition",
  "description": "The classic theorem: addition is commutative!",
  "difficulty": 4,
  "estimatedTime": 10,
  "objective": "Prove n + m = m + n.",
  "hints": ["Use induction on n", "You'll need plus_n_O for base case", "You'll need plus_n_Sm for inductive step"],
  "unlockedTactics": [],
  "rewards": { "xp": 50, "achievements": ["commutativity_master"] }
}*)

(*@THEORY:
This is one of the fundamental theorems of arithmetic.

Strategy:
1. Induction on n
2. Base case: 0 + m = m + 0 (use plus_n_O)
3. Inductive step: (S n') + m = m + (S n') 
   - Use IH: n' + m = m + n'
   - Use plus_n_Sm: m + (S n') = S (m + n')

This proof shows the beauty of induction!
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.
Require Import Arith.PeanoNat.

Lemma plus_n_O : forall n, n + 0 = n.
Proof. intro. induction n. reflexivity. simpl. rewrite IHn. reflexivity. Qed.

Lemma plus_n_Sm : forall n m, S (n + m) = n + (S m).
Proof. intros. induction n. reflexivity. simpl. rewrite IHn. reflexivity. Qed.

Theorem add_comm : forall n m : nat, n + m = m + n.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intros n m.
  induction n as [| n' IH].
  - simpl. rewrite plus_n_O. reflexivity.
  - simpl. rewrite IH. rewrite plus_n_Sm. reflexivity.
Qed.
@ENDSOLUTION*)

(*@LEVEL: level_18*)

(*@LEVEL_META: {
  "id": "level_18",
  "name": "Associativity of Addition",
  "description": "Prove that addition is associative.",
  "difficulty": 3,
  "estimatedTime": 7,
  "objective": "Prove n + (m + p) = (n + m) + p.",
  "hints": ["Induction on n", "Base case is straightforward", "Inductive step uses IH directly"],
  "unlockedTactics": [],
  "rewards": { "xp": 30 }
}*)

(*@THEORY:
Associativity is another fundamental property.

Use induction on n:
- Base: 0 + (m + p) = m + p = (0 + m) + p
- Step: (S n') + (m + p) = S (n' + (m + p)) 
                         = S ((n' + m) + p)  [by IH]
                         = (S (n' + m)) + p
                         = ((S n') + m) + p

The structure of the proof mirrors the recursive definition of addition.
@ENDTHEORY*)

(*@START:
Require Import Init.Nat.
Require Import Arith.PeanoNat.

Theorem add_assoc : forall n m p : nat, n + (m + p) = (n + m) + p.
Proof.
  (* Your proof here *)
Qed.
@ENDSTART*)

(*@SOLUTION:
  intros n m p.
  induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.
@ENDSOLUTION*)