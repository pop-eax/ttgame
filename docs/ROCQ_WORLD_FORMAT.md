# Rocq World Format

This document describes the Rocq-based world configuration format, which allows you to define game worlds directly in Rocq files (`.v` files) instead of JSON.

## Benefits

1. **Single Source of Truth**: Theory, examples, and code all in one file
2. **Executable**: Rocq files can be validated and executed directly
3. **Maintainable**: Edit one file instead of maintaining separate JSON
4. **Leverages Existing Structure**: Use your existing lecture files with minimal changes

## Format Overview

A Rocq world file contains:
- World metadata in a special comment
- Multiple levels, each marked with special comments
- Theory sections with markdown and examples
- Starting code and solutions

## World Metadata

World metadata is defined at the top of the file:

```coq
(*@WORLD: {
  "id": "world-example",
  "name": "Example World",
  "description": "An example world",
  "order": 0,
  "icon": "📚",
  "color": "#8b5cf6",
  "estimatedHours": 5,
  "tags": ["example"],
  "availableTheorems": [
    "eq_refl : forall (A : Type) (x : A), x = x"
  ]
}*)
```

## Level Structure

Each level is marked with a level identifier:

```coq
(*@LEVEL: 0.1*)
```

### Level Metadata

Level metadata follows the level marker:

```coq
(*@LEVEL_META: {
  "id": "0.1",
  "name": "Introduction",
  "description": "Learn the basics",
  "difficulty": 1,
  "estimatedTime": 5,
  "objective": "Define a variable x = 10",
  "hints": [
    "Use the Definition keyword",
    "The syntax is: Definition name := value.",
    "Don't forget the period"
  ],
  "unlockedTactics": [],
  "rewards": {
    "xp": 50
  }
}*)
```

### Theory Section

Theory content uses markdown in comments:

```coq
(*@THEORY:
# Introduction

This is markdown content.

(*@EXAMPLE: Example Title
Definition x := 10.
Print x.
*)
*)
```

Examples are embedded within the theory section using `(*@EXAMPLE: title ... *)`.

### Starting Code

The starting code template:

```coq
(*@START:
(* Define a variable x equal to 10 *)
*)
```

### Solution

The solution code:

```coq
(*@SOLUTION:
Definition x := 10.
*)
```

### Full Code Context

Any code between `(*@START:*)` and `(*@SOLUTION:*)` (or after solution) is included as context. This allows you to include imports, helper definitions, etc.

## Complete Example

```coq
(*@WORLD: {
  "id": "world-example",
  "name": "Example World",
  "description": "An example",
  "order": 0
}*)

(*@LEVEL: 0.1*)
(*@LEVEL_META: {
  "id": "0.1",
  "name": "Introduction",
  "description": "Basics",
  "difficulty": 1,
  "objective": "Define x = 10",
  "hints": ["Hint 1", "Hint 2", "Hint 3"]
}*)

(*@THEORY:
# Theory Content
*)

(*@START:
(* Your code here *)
*)

Definition x := 10.

(*@SOLUTION:
Definition x := 10.
*)
```

## Migration from JSON

To convert an existing JSON world to Rocq format:

1. Create a new `.v` file
2. Add world metadata at the top
3. For each level:
   - Add `(*@LEVEL: id*)` marker
   - Add level metadata
   - Add theory section (convert markdown)
   - Add starting code
   - Add solution
   - Include any context code

## Usage in Application

The application supports both formats:

- **JSON**: `world2-lectures.json` (legacy, still supported)
- **Rocq**: `world2-lectures.v` (new format)

The loader automatically detects the format based on file extension and parses accordingly.

## Advantages Over JSON

1. **No Duplication**: Code examples in theory are the actual code
2. **Validation**: Can check syntax with Rocq compiler
3. **IDE Support**: Full syntax highlighting and autocomplete
4. **Version Control**: Better diffs for code changes
5. **Documentation**: Theory and code live together

## Converting Lecture Files

To convert existing lecture files:

1. Add world metadata at the top
2. Mark level boundaries with `(*@LEVEL: id*)`
3. Add level metadata for each level
4. Mark theory sections with `(*@THEORY: ... *)`
5. Mark starting code with `(*@START: ... *)`
6. Mark solutions with `(*@SOLUTION: ... *)`

The parser will extract everything else automatically.

