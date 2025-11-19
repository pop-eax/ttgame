# Rocq Type Theory Game - Project Specification

## 1. Executive Summary

### 1.1 Project Overview
A browser-based, gamified learning platform for the Rocq proof assistant (formerly Coq) that teaches type theory fundamentals through interactive levels and progressive difficulty. Inspired by the Natural Number Game (NNG4) for Lean, this platform will make type theory accessible and engaging for students and newcomers.

### 1.2 Project Goals
- **Primary**: Create an engaging, self-paced learning environment for type theory using Rocq
- **Secondary**: Build a reusable framework for creating additional proof assistant games
- **Tertiary**: Lower the barrier to entry for formal verification and theorem proving

### 1.3 Target Audience
- **Primary**: Undergraduate CS/Math students (2nd-4th year)
- **Secondary**: Graduate students beginning research in formal methods
- **Tertiary**: Self-taught programmers interested in type theory

### 1.4 Core Architecture Principles
- **Serverless SPA**: Pure client-side application, no backend required
- **Zero Hosting Costs**: Static hosting (GitHub Pages, Netlify, Vercel free tier)
- **Local-First**: All progress saved in browser localStorage
- **Portable Proofs**: Export/import JSON files for assignment submission
- **Modular Content**: Educators can easily add custom worlds via configuration files

---

## 2. Core Concept & Mechanics

### 2.1 Game Structure

#### World System
- **Worlds**: Thematic collections of levels (5-7 worlds total)
- **Levels**: Individual proof challenges (5-10 per world)
- **Progressive Unlocking**: Complete all levels in a world to unlock the next
- **Non-linear within worlds**: Can attempt levels in any order within an unlocked world

#### Example World Progression
0. **Rocq Basics (Tutorial)** - Syntax, basic commands, proof structure, QED
1. **Type Foundations** - Basic types, function types, product types
2. **Propositions as Types** - Curry-Howard correspondence, logical connectives
3. **Dependent Types** - ∀, ∃, dependent pairs (Σ-types)
4. **Inductive Types** - Natural numbers, lists, custom inductive definitions
5. **Equality & Rewriting** - Definitional vs propositional equality, transport
6. **Higher-Order Logic** - Predicates, relations, quantifier manipulation
7. **Advanced Topics** - Polymorphism, type universe hierarchies

### 2.2 Level Structure

Each level consists of:

```
┌─────────────────────────────────────────┐
│ Level Header                            │
│ - Title                                 │
│ - World name                            │
│ - Difficulty indicator (1-5 stars)     │
└─────────────────────────────────────────┘

┌─────────────────────────────────────────┐
│ Objective Section                       │
│ - Clear goal statement                  │
│ - Expected learning outcome             │
│ - Prerequisites (if any)                │
└─────────────────────────────────────────┘

┌──────────────────┬──────────────────────┐
│ Theory Panel     │ Proof Editor         │
│ - Explanation    │ - Starting code      │
│ - Definitions    │ - User input area    │
│ - Examples       │ - Syntax hints       │
│ (collapsible)    │                      │
└──────────────────┴──────────────────────┘

┌─────────────────────────────────────────┐
│ Proof State Display                     │
│ - Current goal(s)                       │
│ - Hypotheses/Context                    │
│ - Type information                      │
└─────────────────────────────────────────┘

┌─────────────────────────────────────────┐
│ Hints & Actions                         │
│ - Progressive hints (3 levels)          │
│ - Available tactics sidebar             │
│ - Solution reveal (penalty)             │
└─────────────────────────────────────────┘
```

### 2.3 Tactic Unlocking System

**Core Mechanic**: Tactics are unlocked progressively as students complete levels.

#### Unlock Categories
1. **Basic Tactics** (World 1)
   - `exact`: Provide a direct proof term
   - `intro` / `intros`: Introduce assumptions
   - `apply`: Apply a lemma or hypothesis
   - `reflexivity`: Prove equality by computation

2. **Structural Tactics** (World 2)
   - `split`: Break conjunctions
   - `left` / `right`: Choose disjunction side
   - `destruct`: Case analysis
   - `exists`: Provide existential witness

3. **Reasoning Tactics** (World 3-4)
   - `induction`: Proof by induction
   - `simpl`: Simplify expressions
   - `unfold`: Expand definitions
   - `rewrite`: Use equality hypotheses

4. **Advanced Tactics** (World 5+)
   - `assert`: Introduce intermediate lemmas
   - `generalize`: Generalize the goal
   - `specialize`: Instantiate universal quantifiers
   - `discriminate` / `injection`: Injectivity reasoning

#### Unlock Mechanics
- **Visual feedback**: New tactic appears with animation and description
- **Tactic library**: Persistent sidebar showing all unlocked tactics with hover documentation
- **Just-in-time unlocking**: New tactic unlocks immediately when level is completed
- **Tooltip education**: First use of a tactic shows interactive tutorial overlay

---

## 3. User Interface Design

### 3.1 Main Screen Layout

```
┌────────────────────────────────────────────────────────────┐
│ [Logo] Rocq Type Theory Game  [User] [Export] [Help] [⚙️]  │
├────────────────────────────────────────────────────────────┤
│                                                            │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐   │
│  │   WORLD 0    │  │   WORLD 1    │  │   WORLD 2    │   │
│  │  ★★★★★ 7/7   │  │  ★★★★★ 8/8   │  │  ★★☆☆☆ 2/7   │   │
│  │   Tutorial   │  │  Foundations │  │ Propositions │   │
│  └──────────────┘  └──────────────┘  └──────────────┘   │
│                                                            │
│  ┌──────────────┐  ┌──────────────┐  ┌──────────────┐   │
│  │   WORLD 3    │  │   WORLD 4    │  │   WORLD 5    │   │
│  │   🔒 LOCKED  │  │   🔒 LOCKED  │  │   🔒 LOCKED  │   │
│  │  Dependent   │  │  Inductive   │  │   Equality   │   │
│  └──────────────┘  └──────────────┘  └──────────────┘   │
│                                                            │
│  [Current World: Propositions as Types]                   │
│  Progress: 2/7 levels ████░░░░░░░ 28%                    │
│                                                            │
│  ┌─────┐ ┌─────┐ ┌─────┐ ┌─────┐ ┌─────┐               │
│  │  1  │ │  2  │ │  3  │ │  4  │ │  5  │               │
│  │  ✓  │ │  ✓  │ │ ▶   │ │     │ │ 🔒  │               │
│  └─────┘ └─────┘ └─────┘ └─────┘ └─────┘               │
│                                                            │
│  ┌─────────────────────────────────────────────────────┐ │
│  │ Level 3: Conjunction Elimination                    │ │
│  │ Difficulty: ★★☆☆☆                                  │ │
│  │ Description: Learn to break apart conjunctions     │ │
│  │ [START LEVEL →]                                     │ │
│  └─────────────────────────────────────────────────────┘ │
│                                                            │
│  User Menu (click [User]):                                │
│  ┌─────────────────────────┐                             │
│  │ 👤 Guest User           │                             │
│  │ Level 5 | 450 XP        │                             │
│  ├─────────────────────────┤                             │
│  │ 📊 View Progress        │                             │
│  │ 📥 Import Progress      │                             │
│  │ 📤 Export Progress      │                             │
│  │ 🏆 Achievements         │                             │
│  │ 📚 Tactic Reference     │                             │
│  │ ⚙️  Settings            │                             │
│  │ ❓ Help & Tutorial      │                             │
│  └─────────────────────────┘                             │
└────────────────────────────────────────────────────────────┘
```

### 3.2 Level Screen Layout

```
┌──────────────────────────────────────────────────────────────┐
│ ← Back to World | Level 3: Conjunction Elimination    🎯 2/5 │
├──────────────────────────────────────────────────────────────┤
│                                                              │
│ ┌────────────────────┐ ┌──────────────────────────────────┐ │
│ │ 📚 Theory          │ │ Objective                        │ │
│ │                    │ │ Prove: ∀ P Q, P ∧ Q → Q ∧ P     │ │
│ │ Conjunction (∧)    │ │                                  │ │
│ │ represents "and"   │ │ Use destruct to break the ∧     │ │
│ │ in logic...        │ │ Then rebuild with split          │ │
│ │ [Show More ▼]      │ └──────────────────────────────────┘ │
│ └────────────────────┘                                       │
│                                                              │
│ ┌──────────────────────────────────────────────────────────┐ │
│ │ Proof Editor                               [Run Proof] │ │
│ ├──────────────────────────────────────────────────────────┤ │
│ │ Theorem and_comm : forall P Q : Prop,                  │ │
│ │   P /\ Q -> Q /\ P.                                    │ │
│ │ Proof.                                                 │ │
│ │   intros P Q H.                                        │ │
│ │   █                                                    │ │
│ │                                                        │ │
│ └──────────────────────────────────────────────────────────┘ │
│                                                              │
│ ┌────────────────────┐ ┌──────────────────────────────────┐ │
│ │ 🎯 Proof State     │ │ 💡 Hints (1/3)                   │ │
│ ├────────────────────┤ │                                  │ │
│ │ 1 goal             │ │ [Show Hint 1]                    │ │
│ │                    │ │                                  │ │
│ │ P, Q : Prop        │ │ Available Tactics:               │ │
│ │ H : P ∧ Q          │ │ • destruct - break apart AND     │ │
│ │ ─────────────      │ │ • split - prove AND              │ │
│ │ Q ∧ P              │ │ • exact - provide term           │ │
│ │                    │ │ • intro(s) - assume hypothesis   │ │
│ └────────────────────┘ └──────────────────────────────────┘ │
│                                                              │
│ [💡 Hint] [📖 Tactic Reference] [🏆 Achievements]          │
└──────────────────────────────────────────────────────────────┘
```

### 3.3 Key UI Components

#### 3.3.1 Code Editor
- **Syntax highlighting**: Rocq-specific syntax
- **Auto-completion**: Available tactics and hypotheses
- **Line numbers**: For reference in hints
- **Error highlighting**: Real-time syntax checking
- **Keyboard shortcuts**: 
  - `Ctrl+Enter`: Run proof to current position
  - `Ctrl+Down`: Step through proof line-by-line
  - `Ctrl+Shift+Enter`: Run entire proof

#### 3.3.2 Proof State Display
- **Live updates**: Updates as proof progresses
- **Hypothesis list**: All assumptions in context
- **Goal highlighting**: Current goal(s) emphasized
- **Type annotations**: Hover to see full type information
- **Context folding**: Collapse long hypothesis lists

#### 3.3.3 Hints System
Three-tier progressive hint system:
1. **Hint 1**: General strategic direction ("Break down the conjunction first")
2. **Hint 2**: More specific guidance ("Use 'destruct H' to split P ∧ Q into P and Q")
3. **Hint 3**: Nearly complete solution ("After destruct, use 'split' and provide H0 and H")

**Penalty System**:
- Hint 1: No penalty
- Hint 2: Reduces score by 10%
- Hint 3: Reduces score by 30%
- View Solution: No completion credit, but can proceed

#### 3.3.4 Tactic Reference Sidebar
- **Searchable list**: All unlocked tactics
- **Quick reference**: Syntax and usage
- **Examples**: Short example for each tactic
- **Locked preview**: Shows upcoming tactics (grayed out)

---

## 4. Gamification System

### 4.1 Progress Tracking

#### Experience Points (XP)
- **Per level completion**: 100 XP base
- **Bonus XP**:
  - No hints used: +50 XP
  - First attempt success: +25 XP
  - Speed bonus (under 5 min): +25 XP
  - Elegant proof (fewer lines): +15 XP

#### Level System
- **Levels 1-20**: Each level requires 500 XP
- **Title progression**:
  - Lv 1-5: "Type Novice"
  - Lv 6-10: "Proof Apprentice"
  - Lv 11-15: "Type Theorist"
  - Lv 16-20: "Proof Master"

### 4.2 Achievements

#### Category: Foundations
- ✓ **First Proof**: Complete first level
- ✓ **Type Constructor**: Use 5 different type constructors
- ✓ **Function Master**: Complete all function type levels
- ✓ **Product Expert**: Master product types
- ✓ **Sum Specialist**: Master sum types

#### Category: Mastery
- 🏆 **World Conqueror**: Complete all levels in a world
- 🏆 **No Assistance**: Complete 5 levels without hints
- 🏆 **Speed Runner**: Complete 10 levels in under 3 minutes each
- 🏆 **Perfectionist**: 10 first-attempt successes
- 🏆 **Minimalist**: Use fewer tactics than suggested in 5 levels

#### Category: Exploration
- 🔍 **Curious Mind**: Read all theory sections
- 🔍 **Tactic Collector**: Unlock 20 different tactics
- 🔍 **Alternative Solution**: Find a different proof than the expected solution

#### Category: Social (if multiplayer features added)
- 👥 **Helpful Peer**: Provide hints to 10 other players
- 👥 **Code Review**: Comment on 20 other proofs
- 👥 **Leaderboard Top 10**: Reach top 10 in any world

### 4.3 Visual Feedback

#### Success Animations
- ✅ **Level Complete**: Checkmark animation + confetti
- 🌟 **Achievement Unlocked**: Badge slides in from right
- 🔓 **New Tactic**: Tactic card flips to reveal information
- 🎯 **Proof Step Success**: Subtle green glow on proof state

#### Progress Indicators
- **World map**: Nodes fill with color as levels complete
- **Progress bars**: Animated transitions
- **Streak counters**: Days active, consecutive completions

---

## 5. Content Structure

### 5.0 World 0: Rocq Basics (Tutorial)

**Learning Objectives**: Understand Rocq syntax, proof structure, and basic commands

| Level | Name | Goal | New Tactics | Difficulty |
|-------|------|------|-------------|------------|
| 0.1 | Welcome to Rocq | Run first command | - | ★☆☆☆☆ |
| 0.2 | Check Command | Query types | Check | ★☆☆☆☆ |
| 0.3 | Definitions | Define constants | Definition | ★☆☆☆☆ |
| 0.4 | Theorem Statement | Write theorem | Theorem | ★☆☆☆☆ |
| 0.5 | Proof Structure | Proof...Qed | Proof, Qed | ★☆☆☆☆ |
| 0.6 | Your First Tactic | Use exact | exact | ★★☆☆☆ |
| 0.7 | Comments & Style | Code organization | - | ★☆☆☆☆ |

**Special Features**:
- **Guided walkthrough**: Each step explained with animations
- **No penalties**: Can't fail, only learn
- **Interactive tooltips**: Hover over syntax for explanations
- **Auto-advancement**: Moves to next step automatically

### 5.1 World 1: Type Foundations

**Learning Objectives**: Understand basic type constructors and function types

| Level | Name | Goal | New Tactics | Difficulty |
|-------|------|------|-------------|------------|
| 1.1 | Basic Types | Construct Type | exact | ★☆☆☆☆ |
| 1.2 | Function Types | Build A → B | intro | ★☆☆☆☆ |
| 1.3 | Simple Functions | Identity function | - | ★★☆☆☆ |
| 1.4 | Function Composition | Compose functions | apply | ★★☆☆☆ |
| 1.5 | Product Types | Pairs (A × B) | split | ★★★☆☆ |
| 1.6 | Projections | Extract from pairs | destruct | ★★☆☆☆ |
| 1.7 | Sum Types | Either (A + B) | left, right | ★★★☆☆ |
| 1.8 | Unit and Empty | Special types | - | ★★☆☆☆ |

### 5.2 World 2: Propositions as Types

**Learning Objectives**: Understand Curry-Howard correspondence

| Level | Name | Goal | New Tactics | Difficulty |
|-------|------|------|-------------|------------|
| 2.1 | Implication | P → P | - | ★☆☆☆☆ |
| 2.2 | Conjunction | P ∧ Q → Q ∧ P | - | ★★☆☆☆ |
| 2.3 | Disjunction | P ∨ Q → Q ∨ P | - | ★★☆☆☆ |
| 2.4 | True & False | Work with ⊤ and ⊥ | exfalso | ★★★☆☆ |
| 2.5 | Negation | ¬¬P → P (classical) | - | ★★★★☆ |
| 2.6 | Modus Ponens | (P → Q) ∧ P → Q | - | ★★☆☆☆ |
| 2.7 | Contrapositive | (P → Q) → (¬Q → ¬P) | - | ★★★★☆ |

### 5.3 World 3: Dependent Types

**Learning Objectives**: Master ∀ and ∃

| Level | Name | Goal | New Tactics | Difficulty |
|-------|------|------|-------------|------------|
| 3.1 | Universal Quantifier | ∀n:nat, n=n | - | ★★☆☆☆ |
| 3.2 | Existential Quantifier | Prove ∃n, n>0 | exists | ★★★☆☆ |
| 3.3 | Dependent Pairs | Σ-types | - | ★★★★☆ |
| 3.4 | Quantifier Swap | ∀∃ ↔ ∃∀ cases | - | ★★★★☆ |
| 3.5 | DeMorgan's Laws | Quantifier negation | - | ★★★★★ |

### 5.4 World 4: Inductive Types

**Learning Objectives**: Define and reason about inductive types

| Level | Name | Goal | New Tactics | Difficulty |
|-------|------|------|-------------|------------|
| 4.1 | Natural Numbers | Basic nat proofs | induction | ★★★☆☆ |
| 4.2 | Addition Properties | Commutativity | simpl, rewrite | ★★★☆☆ |
| 4.3 | List Introduction | Define lists | - | ★★★★☆ |
| 4.4 | List Operations | Map, fold properties | unfold | ★★★★☆ |
| 4.5 | Custom Inductives | Binary trees | - | ★★★★★ |

### 5.5 Worlds 5-7 (Advanced)

- **World 5**: Equality & Rewriting
- **World 6**: Higher-Order Logic
- **World 7**: Universe Hierarchies & Polymorphism

---

## 6. Technical Requirements

### 6.1 Architecture Overview

**Pure Single-Page Application (SPA)**
- No backend server required
- All logic runs client-side in browser
- Static files only (HTML, CSS, JS, WASM)
- Can be hosted on any static file hosting service

**Key Benefits**:
- ✅ Zero hosting costs (free tier static hosting)
- ✅ Works offline after initial load
- ✅ No database management
- ✅ Instant scaling (CDN handles traffic)
- ✅ Privacy-friendly (no data sent to servers)

### 6.2 Frontend Stack

#### Core Technologies
- **Framework**: React 18+ with TypeScript
- **State Management**: React Context + Hooks (or Zustand for complex state)
- **Styling**: Tailwind CSS for utility-first styling
- **Code Editor**: Monaco Editor (VS Code's editor) or CodeMirror 6
- **Syntax Highlighting**: Custom Rocq/Coq grammar
- **Build Tool**: Vite (fast builds, optimized bundling)
- **Static Hosting**: GitHub Pages / Netlify / Vercel (free tier)

#### Rocq Integration
- **Primary**: jsCoq (browser-based Coq) - https://github.com/jscoq/jscoq
- **Version**: Target Coq 8.17+ (latest stable jsCoq)
- **Loading Strategy**: Lazy-load jsCoq WASM bundles per world

#### Additional Libraries
- **Animations**: Framer Motion
- **Icons**: Lucide React
- **Toast Notifications**: React Hot Toast
- **Markdown Rendering**: React Markdown (for theory sections)
- **File Export/Import**: Browser File System API

### 6.3 Data Persistence (LocalStorage)

#### Storage Structure
```typescript
// localStorage key: 'rocq_game_data'
interface GameData {
  version: string;
  user: {
    id: string; // UUID generated client-side
    name?: string;
    createdAt: string;
    lastActive: string;
  };
  progress: {
    completedLevels: string[]; // level IDs
    currentWorld: string;
    currentLevel: string;
    xp: number;
    level: number;
  };
  proofs: {
    [levelId: string]: {
      code: string;
      completedAt: string;
      timeSpent: number; // seconds
      hintsUsed: number;
      attempts: number;
      correct: boolean;
    };
  };
  unlockedTactics: string[];
  achievements: {
    [achievementId: string]: {
      unlockedAt: string;
    };
  };
  settings: {
    theme: 'light' | 'dark';
    fontSize: number;
    autoSave: boolean;
  };
}
```

#### Storage API Wrapper
```typescript
class GameStorage {
  private static KEY = 'rocq_game_data';
  
  static save(data: GameData): void {
    localStorage.setItem(this.KEY, JSON.stringify(data));
  }
  
  static load(): GameData | null {
    const raw = localStorage.getItem(this.KEY);
    return raw ? JSON.parse(raw) : null;
  }
  
  static exportJSON(): string {
    return localStorage.getItem(this.KEY) || '{}';
  }
  
  static importJSON(json: string): boolean {
    try {
      const data = JSON.parse(json);
      // Validate structure
      if (this.validate(data)) {
        localStorage.setItem(this.KEY, json);
        return true;
      }
      return false;
    } catch {
      return false;
    }
  }
  
  static clear(): void {
    localStorage.removeItem(this.KEY);
  }
}
```

### 6.4 Export/Import for Teachers & Students

#### Use Case Flow
```
Teacher assigns World 2
    ↓
Student completes levels on website
    ↓
Student clicks "Export Progress" → downloads rocq_progress.json
    ↓
Student submits JSON file to teacher (email/LMS)
    ↓
Teacher uses validation tool to verify:
  - Which levels completed
  - Proof code for each level
  - Time spent & hints used
  - Authenticity (hash validation)
```

#### Export Format
```json
{
  "exportVersion": "1.0",
  "exportedAt": "2024-11-18T10:30:00Z",
  "studentInfo": {
    "name": "John Doe",
    "id": "optional-student-id"
  },
  "assignment": {
    "worldId": "world2",
    "requiredLevels": ["2.1", "2.2", "2.3"]
  },
  "proofs": {
    "2.1": {
      "code": "intros P H. exact H.",
      "completedAt": "2024-11-18T09:15:00Z",
      "timeSpent": 180,
      "hintsUsed": 0,
      "correct": true
    },
    "2.2": {
      "code": "intros P Q H. destruct H. split. exact H0. exact H.",
      "completedAt": "2024-11-18T09:45:00Z",
      "timeSpent": 420,
      "hintsUsed": 1,
      "correct": true
    }
  },
  "checksum": "sha256hash" // prevents tampering
}
```

#### Import UI
```
┌────────────────────────────────────────┐
│ Import Progress                        │
├────────────────────────────────────────┤
│                                        │
│  📁 Drag & drop JSON file here         │
│     or click to browse                 │
│                                        │
│  [Browse Files]                        │
│                                        │
│  ⚠️  Warning: This will overwrite      │
│     your current progress              │
│                                        │
│  [ Cancel ]  [ Import & Merge ]       │
│              [ Import & Replace ]      │
│                                        │
└────────────────────────────────────────┘
```

### 6.5 Content Definition System (Modular Worlds)

#### Directory Structure
```
/public/
  /worlds/
    world0-tutorial.json
    world1-foundations.json
    world2-propositions.json
    world3-dependent.json
    /custom/
      my-custom-world.json
  /config/
    worlds-manifest.json
```

#### World Definition Format
```json
{
  "id": "world1",
  "name": "Type Foundations",
  "description": "Learn about basic type constructors",
  "order": 1,
  "prerequisites": ["world0"],
  "levels": [
    {
      "id": "1.1",
      "name": "Basic Types",
      "description": "Construct simple types",
      "difficulty": 1,
      "estimatedTime": 5,
      "objective": "Define a type and prove it's inhabited",
      "theory": {
        "markdown": "# Types in Rocq\n\nTypes are the foundation...",
        "examples": [
          {
            "title": "Natural Numbers",
            "code": "Check nat.\n(* nat : Set *)"
          }
        ]
      },
      "startingCode": "(* Your task *)\nTheorem first_type : Type.\nProof.\n  (* Your proof here *)\n",
      "solution": "exact nat.",
      "hints": [
        "You need to provide a concrete type",
        "Try using 'nat' (natural numbers)",
        "Use the 'exact' tactic: exact nat."
      ],
      "unlockedTactics": ["exact"],
      "rewards": {
        "xp": 100,
        "achievements": ["first_proof"]
      }
    }
  ]
}
```

#### Worlds Manifest
```json
{
  "version": "1.0",
  "worlds": [
    {
      "file": "world0-tutorial.json",
      "enabled": true
    },
    {
      "file": "world1-foundations.json",
      "enabled": true
    },
    {
      "file": "world2-propositions.json",
      "enabled": true
    },
    {
      "file": "custom/advanced-category-theory.json",
      "enabled": false,
      "requiresUnlock": true
    }
  ]
}
```

#### Adding Custom Worlds

**For Educators/Content Creators**:

1. **Create JSON file** following the world definition schema
2. **Place in `/public/worlds/custom/` directory**
3. **Update `worlds-manifest.json`** to include your world
4. **Build and deploy** (or share JSON file for others to add)

**Validation Tool** (built into app):
```
Settings → Content Management → Validate World File
- Upload JSON file
- Shows validation errors/warnings
- Preview levels before adding
```

**Example: Creating a Custom World**
```bash
# 1. Copy template
cp public/worlds/world-template.json public/worlds/custom/my-world.json

# 2. Edit with your content
# 3. Validate
npm run validate-world public/worlds/custom/my-world.json

# 4. Add to manifest
# Edit public/config/worlds-manifest.json

# 5. Rebuild
npm run build
```

### 6.6 Performance Requirements

- **Initial Load**: < 3 seconds on 3G connection
- **jsCoq Load**: < 5 seconds
- **Proof Execution**: < 500ms for simple proofs
- **UI Responsiveness**: 60 FPS animations
- **Mobile Support**: Responsive down to 768px width (tablet)

### 6.4 Browser Compatibility

- **Minimum**: ES2017 support
- **Primary Targets**: 
  - Chrome 90+
  - Firefox 88+
  - Safari 14+
  - Edge 90+
- **Mobile**: iOS Safari 14+, Chrome Android 90+

---

## 7. User Interactions & Flows

### 7.1 First-Time User Experience (FTUE)

#### Step 1: Landing Page
```
User arrives → Sees hero section with:
- "Learn Type Theory Through Interactive Proofs"
- Preview of tutorial level
- [Start Learning] button (no account required)
- [Import Progress] button (for returning users)
```

#### Step 2: Tutorial World (World 0)
```
Automatic entry into World 0:
1. "Welcome! This is Rocq..." (animated intro)
2. Level 0.1: "Type this command: Check nat."
3. Interactive guided steps through 7 tutorial levels
4. "You're ready! Let's begin World 1" → World Selection
```

#### Step 3: World Selection
```
User sees all worlds:
- World 0: Completed ✓ 7/7
- World 1: Unlocked, 0/8 complete
- Worlds 2-7: Locked
- Clear progression path indicated
```

### 7.2 Core Game Loop

```
┌─────────────────────────────────────────────┐
│                                             │
│  Select Level → Read Objective              │
│       ↓                                     │
│  Read Theory (optional)                     │
│       ↓                                     │
│  Write Proof ←──────────────┐              │
│       ↓                      │              │
│  Run Proof                   │              │
│       ↓                      │              │
│  Success? ──NO─→ Get Feedback/Hints ──────┘│
│       ↓                                     │
│      YES                                    │
│       ↓                                     │
│  [Auto-save to localStorage]                │
│       ↓                                     │
│  Unlock Tactic (if new)                     │
│       ↓                                     │
│  Award XP & Achievements                    │
│       ↓                                     │
│  Unlock Next Level                          │
│       ↓                                     │
│  Return to World Map ────────────────┐     │
│       ↓                               │     │
│  Select Next Level ←──────────────────┘    │
│                                             │
└─────────────────────────────────────────────┘
```

### 7.3 Export/Import Workflow

#### Student Workflow
```
┌──────────────────────────────────────────┐
│ User Menu (Top Right)                    │
├──────────────────────────────────────────┤
│ • View Progress                          │
│ • Export Progress → Download JSON        │
│ • Import Progress                        │
│ • Settings                               │
│ • Help                                   │
└──────────────────────────────────────────┘

Export Dialog:
┌──────────────────────────────────────────┐
│ Export Your Progress                     │
├──────────────────────────────────────────┤
│ Choose what to export:                   │
│ ☑ All worlds                            │
│ ☑ Include proof code                    │
│ ☑ Include timestamps                    │
│ ☐ Include personal notes (if added)    │
│                                          │
│ Optional: Student Name/ID                │
│ [________________]                       │
│                                          │
│ [Cancel]  [Download JSON]                │
└──────────────────────────────────────────┘

File downloads as: rocq_progress_2024-11-18.json
```

#### Teacher Verification Workflow
```
Teacher receives JSON file from student
        ↓
Opens validation tool (can be separate page or built-in)
        ↓
┌──────────────────────────────────────────┐
│ Verify Student Progress                  │
├──────────────────────────────────────────┤
│ [Drop JSON file here or browse]          │
│                                          │
│ ✓ Valid JSON structure                  │
│ ✓ Checksum verified (not tampered)      │
│                                          │
│ Student: John Doe                        │
│ Date Range: 2024-11-15 to 2024-11-18    │
│                                          │
│ Completed Levels:                        │
│ • World 2, Level 1 ✓ (3 min, 0 hints)  │
│ • World 2, Level 2 ✓ (7 min, 1 hint)   │
│ • World 2, Level 3 ✓ (5 min, 0 hints)  │
│                                          │
│ [View Proof Code]  [Export Report]      │
└──────────────────────────────────────────┘

Click "View Proof Code" shows actual code:
┌──────────────────────────────────────────┐
│ Level 2.1 - Proof Code                   │
├──────────────────────────────────────────┤
│ Theorem implies_itself :                 │
│   forall P : Prop, P -> P.               │
│ Proof.                                   │
│   intros P H.                            │
│   exact H.                               │
│ Qed.                                     │
│                                          │
│ Hints Used: 0                            │
│ Time: 3m 15s                             │
│ Attempts: 1                              │
└──────────────────────────────────────────┘
```

### 7.4 Proof Writing Flow

#### Real-Time Feedback
1. **User types tactic** → Syntax highlighting activates
2. **User presses Run** → jsCoq executes line-by-line
3. **Each line executes** → Proof state updates
4. **Error occurs** → Error message displays with line highlight
5. **Proof completes** → Success animation triggers

#### Syntax Help
- **Auto-complete**: Typing `de` suggests `destruct`, `destructs`
- **Hover tooltips**: Hovering on hypothesis shows type
- **Parameter hints**: Typing `destruct ` shows expected parameter
- **Error squiggles**: Red underline for syntax errors

### 7.4 Help & Learning Resources

#### In-Level Help
1. **Hints Button**: Progressive hints (3 levels)
2. **Tactic Reference**: Sidebar with all unlocked tactics
3. **Theory Section**: Collapsible explanation panel
4. **Show Solution**: Last resort (penalty applies)

#### Global Help
1. **Help Menu**:
   - Getting Started Guide
   - Rocq Syntax Reference
   - Keyboard Shortcuts
   - FAQ
2. **Glossary**: Searchable term definitions
3. **Community**: Link to forum/Discord (if available)

### 7.6 Mobile Considerations

#### Adapted UI for Mobile
- **Vertical layout**: Editor on top, proof state below
- **Swipe gestures**: Swipe hints panel in from right
- **Virtual keyboard**: Custom tactic buttons above keyboard
- **Simplified view**: Hide theory panel by default
- **Touch-friendly**: Larger tap targets (44x44px minimum)

---

## 8. Content Creation System

### 8.1 Level Definition Format

```typescript
interface Level {
  id: string;
  worldId: string;
  order: number;
  metadata: {
    title: string;
    description: string;
    difficulty: 1 | 2 | 3 | 4 | 5;
    estimatedTime: number; // minutes
    prerequisites: string[]; // level IDs
  };
  content: {
    theory: {
      markdown: string;
      examples: CodeExample[];
    };
    objective: string;
    startingCode: string;
    solution: string; // canonical solution
    alternativeSolutions?: string[]; // other valid approaches
  };
  pedagogy: {
    hints: [string, string, string]; // 3-tier hints
    commonMistakes: CommonMistake[];
    learningOutcomes: string[];
  };
  rewards: {
    xpBase: number;
    unlockedTactics: string[];
    achievements?: string[];
  };
  validation: {
    checkFunction?: string; // custom validation if needed
    timeoutMs: number;
  };
}
```

### 8.2 Tactic Definition Format

```typescript
interface Tactic {
  id: string;
  name: string;
  syntax: string;
  category: 'basic' | 'structural' | 'reasoning' | 'advanced';
  unlockedInLevel: string;
  documentation: {
    shortDescription: string;
    longDescription: string;
    examples: CodeExample[];
    parameters: Parameter[];
    relatedTactics: string[];
  };
  autoComplete: {
    triggerChars: string[];
    completionItems: CompletionItem[];
  };
}
```

---

## 9. Success Metrics & Analytics

### 9.1 Key Performance Indicators (KPIs)

#### User Engagement
- **Daily Active Users (DAU)**: Target 500+ within 6 months
- **Average Session Duration**: Target 15+ minutes
- **Return Rate**: 40% next-day return, 20% 7-day return
- **Completion Rate**: 60% complete World 1, 30% complete all worlds

#### Learning Effectiveness
- **First-Attempt Success Rate**: 30-40% per level (indicates good difficulty)
- **Hint Usage**: 50% of users use <2 hints per level
- **Time to Completion**: Average 8-10 minutes per level
- **Concept Retention**: Measured through periodic "checkpoint" levels

#### Technical Performance
- **Load Time**: 95th percentile < 5 seconds
- **Crash Rate**: < 0.1% of sessions
- **jsCoq Errors**: < 5% of proof executions fail unexpectedly

### 9.2 Analytics Events to Track

```javascript
// User actions
track('level_started', { worldId, levelId, userId });
track('level_completed', { worldId, levelId, timeSpent, hintsUsed, attempts });
track('hint_viewed', { levelId, hintNumber });
track('solution_viewed', { levelId });
track('proof_executed', { levelId, success, errorType });

// Engagement
track('session_started', { userId, timestamp });
track('session_ended', { duration, levelsCompleted });
track('achievement_unlocked', { achievementId, userId });
track('tactic_unlocked', { tacticId, levelId });

// Content interaction
track('theory_opened', { levelId });
track('tactic_reference_viewed', { tacticId });
track('code_typed', { levelId, characterCount });
```

### 9.3 A/B Testing Opportunities

- **Hint phrasing**: Test different hint wordings for effectiveness
- **Difficulty curve**: Adjust level ordering based on completion data
- **UI layouts**: Test different arrangements of editor/proof state
- **Gamification**: Test XP amounts, achievement triggers
- **FTUE**: Test different tutorial approaches

---

## 10. Development Phases

### 10.1 Phase 1: MVP (Months 1-3)

**Deliverables**:
- ✅ World 0 (Tutorial - 7 levels) fully functional
- ✅ World 1 (8 levels) fully functional
- ✅ Basic UI: World map, level screen, proof editor
- ✅ jsCoq integration working
- ✅ localStorage progress saving
- ✅ Export/Import JSON functionality
- ✅ 5 basic tactics unlocking system
- ✅ Simple hint system (3 tiers)
- ✅ Basic achievements (5 total)

**Technical Stack**:
- React + TypeScript + Vite
- Tailwind CSS
- Monaco Editor
- jsCoq 0.17+
- Pure SPA (no backend)

**Success Criteria**:
- 50 alpha testers complete Worlds 0-1
- Average rating: 4/5 stars
- No critical bugs
- Works on Chrome, Firefox, Safari
- Export/import works reliably

### 10.2 Phase 2: Content Expansion (Months 4-6)

**Deliverables**:
- ✅ Worlds 2-3 (15 more levels)
- ✅ 15 more tactics unlocked
- ✅ Enhanced UI: Better syntax highlighting, autocomplete
- ✅ Theory sections with markdown + examples
- ✅ 15 more achievements
- ✅ Mobile-responsive design (tablet support)
- ✅ World validation tool for educators
- ✅ World template and documentation

**Success Criteria**:
- 200 active users
- 40% complete all 3 worlds
- Mobile usage: 20% of sessions
- 5+ educators create custom worlds
- Deployed on free static hosting (Netlify/Vercel)

### 10.3 Phase 3: Advanced Features (Months 7-9)

**Deliverables**:
- ✅ Worlds 4-5 (20 more levels)
- ✅ Advanced analytics dashboard (client-side)
- ✅ Community world repository (GitHub-based)
- ✅ Enhanced export: Teacher verification tool (separate page)
- ✅ Proof comparison tool (compare solutions)
- ✅ Performance optimizations (code splitting, lazy loading)
- ✅ Accessibility improvements (keyboard navigation, screen reader support)

**Success Criteria**:
- 500 active users
- 20+ community-submitted worlds
- Featured in academic conference (poster/demo)
- Used in 3+ university courses

### 10.4 Phase 4: Polish & Scale (Months 10-12)

**Deliverables**:
- ✅ Worlds 6-7 (final 15 levels)
- ✅ Custom level editor (JSON GUI builder)
- ✅ Comprehensive documentation site
- ✅ Video tutorials for educators
- ✅ Integration guides for LMS (Canvas, Moodle) via JSON export
- ✅ WCAG 2.1 AA accessibility compliance
- ✅ Multi-language UI support (i18n)
- ✅ Offline PWA support

**Success Criteria**:
- 1000+ active users
- Used in 10+ university courses
- 50+ community worlds available
- Published paper about the platform
- Self-sustaining community of educators

---

## 11. Risk Assessment & Mitigation

### 11.1 Technical Risks

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| jsCoq browser compatibility issues | Medium | High | Maintain fallback instructions for desktop Coq |
| Performance issues on mobile | High | Medium | Optimize bundle size, lazy load worlds |
| jsCoq stability/bugs | Medium | High | Report bugs upstream, maintain workaround list |
| Proof execution timeouts | Low | Medium | Set reasonable timeout limits, provide feedback |

### 11.2 User Experience Risks

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| Difficulty curve too steep | High | High | Extensive playtesting, adjust levels based on data |
| Users stuck without proper hints | Medium | High | Iterative hint improvement based on common mistakes |
| Boring content/not engaging | Low | High | Gamification, storytelling elements, visual polish |
| Unclear error messages | High | Medium | Custom error interpretation layer over jsCoq |

### 11.3 Content Risks

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| Pedagogical inaccuracies | Low | High | Review by type theory experts |
| Scope too ambitious | Medium | Medium | Prioritize core worlds, defer advanced content |
| Inconsistent difficulty | Medium | Medium | Beta testing with target audience |

---

## 11. Educator's Guide: Creating Custom Worlds

### 11.1 Overview

The platform is designed to be easily extensible by educators who want to create custom worlds for their courses. No programming knowledge is required - just edit JSON files following the provided schema.

### 11.2 Quick Start Guide

#### Step 1: Get the Template
```bash
# Download the world template
curl -O https://your-domain.com/templates/world-template.json
```

#### Step 2: Edit the JSON
```json
{
  "id": "world-custom-1",
  "name": "My Custom World",
  "description": "Advanced topics for CS 420",
  "order": 8,
  "prerequisites": ["world3"],
  "levels": [ /* see below */ ]
}
```

#### Step 3: Define Your Levels

Each level needs:
- **Unique ID**: `"id": "custom1.1"`
- **Clear goal**: What should students prove?
- **Starting code**: Template with `(* Your proof here *)`
- **Solution**: At least one correct proof
- **Hints**: 3 progressive hints
- **Theory**: Optional markdown explanation

**Example Level Definition**:
```json
{
  "id": "custom1.1",
  "name": "Custom Property",
  "description": "Prove a custom theorem",
  "difficulty": 3,
  "estimatedTime": 10,
  "objective": "Prove that your custom property holds",
  "theory": {
    "markdown": "# Custom Theory\n\nThis level teaches...",
    "examples": [
      {
        "title": "Example 1",
        "code": "Definition custom := ...\nCheck custom."
      }
    ]
  },
  "startingCode": "Theorem my_theorem : forall n, custom_property n.\nProof.\n  (* Your proof here *)\n",
  "solution": "intro n. unfold custom_property. reflexivity.",
  "hints": [
    "Think about what custom_property means",
    "Try unfolding the definition",
    "Use reflexivity to finish"
  ],
  "unlockedTactics": [],
  "rewards": {
    "xp": 150,
    "achievements": []
  }
}
```

#### Step 4: Validate Your World

Use the built-in validator:
```
Settings → Content Management → Validate World File
[Upload JSON] → [Validate]

✓ Valid JSON syntax
✓ All required fields present
✓ Level IDs unique
✓ Solutions compile correctly
⚠ Warning: Level custom1.3 has no examples
```

#### Step 5: Deploy

**Option A: Add to your hosted version**
```bash
# Copy to public directory
cp my-world.json public/worlds/custom/

# Update manifest
# Edit public/config/worlds-manifest.json
# Add: {"file": "custom/my-world.json", "enabled": true}

# Rebuild
npm run build
```

**Option B: Share JSON file**
```
Share your .json file with students
Students import via: Settings → Import Custom World
```

### 11.3 World Schema Reference

```typescript
interface World {
  // Required fields
  id: string;              // Unique: "world-custom-1"
  name: string;            // Display name
  description: string;     // Short description
  order: number;           // Display order (1-999)
  levels: Level[];         // Array of levels
  
  // Optional fields
  prerequisites?: string[]; // World IDs that must be completed first
  icon?: string;           // Emoji or icon name
  color?: string;          // Hex color for UI
  estimatedHours?: number; // Total estimated time
  tags?: string[];         // ["advanced", "category-theory"]
}

interface Level {
  // Required fields
  id: string;              // Unique: "custom1.1"
  name: string;            // Display name
  description: string;     // Brief description
  difficulty: 1 | 2 | 3 | 4 | 5;
  objective: string;       // What to prove
  startingCode: string;    // Initial editor content
  solution: string;        // At least one valid solution
  hints: [string, string, string]; // Exactly 3 hints
  
  // Optional fields
  estimatedTime?: number;  // Minutes
  theory?: {
    markdown: string;
    examples?: Array<{
      title: string;
      code: string;
    }>;
  };
  prerequisites?: string[]; // Level IDs
  unlockedTactics?: string[];
  rewards?: {
    xp?: number;
    achievements?: string[];
  };
  validation?: {
    checkFunction?: string;
    timeoutMs?: number;
  };
  commonMistakes?: Array<{
    pattern: string;
    explanation: string;
    suggestion: string;
  }>;
}
```

### 11.4 Best Practices

#### Pedagogical Guidelines
1. **Progressive difficulty**: Start easy, build up gradually
2. **One concept per level**: Don't introduce too much at once
3. **Good hints**: Hint 1 = strategy, Hint 2 = tactic suggestion, Hint 3 = almost complete
4. **Clear objectives**: Students should know exactly what to prove
5. **Theory sections**: Explain *why* before showing *how*

#### Technical Guidelines
1. **Test solutions**: Make sure your solution actually works in jsCoq
2. **Unique IDs**: Use format `worldId.levelNumber` (e.g., `custom1.1`)
3. **Realistic time estimates**: Test with real students
4. **Handle edge cases**: What if students use unexpected tactics?
5. **Validate JSON**: Always run through validator before deploying

#### Content Structure
```
Good Level Structure:
1. Title: Clear, descriptive (e.g., "Function Composition")
2. Description: 1-2 sentences about what you'll learn
3. Theory: 2-3 paragraphs + 1-2 examples
4. Objective: Crystal clear goal statement
5. Starting code: Helpful template, not blank slate
6. Hints: Strategic → Tactical → Specific
7. Solution: Clean, well-commented

Bad Level Structure:
- Vague title ("Advanced Stuff")
- No theory section
- Blank starting code
- Hints that just give away the answer
- Overly complex solution
```

### 11.5 Example: Creating a "Category Theory" World

```json
{
  "id": "world-category-theory",
  "name": "Introduction to Category Theory",
  "description": "Learn basic category theory concepts through proofs",
  "order": 10,
  "prerequisites": ["world3", "world4"],
  "estimatedHours": 8,
  "icon": "🔄",
  "tags": ["advanced", "category-theory", "abstract-algebra"],
  "levels": [
    {
      "id": "cat1.1",
      "name": "Categories Basics",
      "description": "Define your first category",
      "difficulty": 3,
      "estimatedTime": 15,
      "objective": "Define a category and prove identity laws",
      "theory": {
        "markdown": "# Categories\n\nA category consists of:\n- Objects\n- Morphisms between objects\n- Composition of morphisms\n- Identity morphisms\n\nSubject to:\n- Associativity: (f ∘ g) ∘ h = f ∘ (g ∘ h)\n- Identity: id ∘ f = f = f ∘ id",
        "examples": [
          {
            "title": "Category Definition",
            "code": "Record Category := {\n  obj : Type;\n  mor : obj -> obj -> Type;\n  compose : forall {A B C}, mor B C -> mor A B -> mor A C;\n  id : forall {A}, mor A A;\n  (* laws omitted *)\n}."
          }
        ]
      },
      "startingCode": "(* Prove left identity law *)\nTheorem left_id : forall (C : Category) (A B : C.obj) (f : C.mor A B),\n  C.compose C.id f = f.\nProof.\n  (* Your proof here *)\n",
      "solution": "intros C A B f. destruct C. simpl. apply id_left.",
      "hints": [
        "Destruct the category to access its components",
        "Use the identity law from the category definition",
        "Apply the left identity axiom"
      ],
      "unlockedTactics": ["destruct"],
      "rewards": {
        "xp": 200,
        "achievements": ["category_theorist"]
      }
    }
    // ... more levels
  ]
}
```

### 11.6 Sharing Custom Worlds

#### Method 1: GitHub Repository
```bash
# Create repository
git init rocq-custom-worlds
cd rocq-custom-worlds

# Add your worlds
mkdir worlds
cp my-world.json worlds/

# Add README
echo "# Custom Rocq Worlds" > README.md
echo "To use: Download JSON and import via Settings" >> README.md

# Push to GitHub
git add .
git commit -m "Add custom world"
git push
```

#### Method 2: Course Website
```html
<!-- Add download link to your course website -->
<a href="/downloads/world-advanced-types.json" download>
  Download Advanced Types World
</a>

<!-- Students click, then import in app -->
```

#### Method 3: Direct Import URL
```javascript
// Students can import directly from URL
Settings → Import Custom World → Enter URL
https://your-course-site.edu/worlds/custom-world.json
```

### 11.7 Community World Repository

We maintain a community repository of custom worlds:
```
https://github.com/rocq-game/community-worlds

Worlds available:
- Category Theory (by Dr. Smith)
- Homotopy Type Theory (by Prof. Jones)
- Software Verification (by CS 525 team)
- Logic Puzzles (by community)
```

**Contributing your world**:
1. Fork the repository
2. Add your world JSON to `/worlds/`
3. Add metadata to `/worlds/index.json`
4. Submit pull request
5. After review, world is added to community library

---

## 12. Appendices

### 12.1 Glossary of Terms

- **Rocq/Coq**: A proof assistant based on the Calculus of Inductive Constructions
- **Tactic**: A command that transforms proof goals
- **Proof State**: Current goals and hypotheses in a proof
- **Curry-Howard**: Correspondence between programs and proofs
- **jsCoq**: JavaScript port of Coq running in browser
- **Dependent Type**: Types that depend on values
- **Universe**: Type of types in Rocq's type hierarchy

### 12.2 References

1. Natural Number Game (Lean): https://adam.math.hhu.de/#/g/leanprover-community/nng4
2. jsCoq Documentation: https://github.com/jscoq/jscoq
3. Software Foundations: https://softwarefoundations.cis.upenn.edu/
4. Coq Reference Manual: https://rocq-prover.org/refman/
5. Type Theory Resources: Various academic papers

### 12.3 Competitive Analysis

| Platform | Strength | Weakness | Our Advantage |
|----------|----------|----------|---------------|
| NNG4 (Lean) | Excellent UX, Natural Numbers focus | Limited to one topic | Broader type theory coverage |
| Software Foundations | Comprehensive content | Not gamified, requires local setup | Browser-based, game mechanics |
| Coq Tutorial | Official, accurate | Dry presentation, no progression | Engaging, visual, progressive |
| Proof School | Good pedagogy | Paid, desktop only | Free, browser-based |

---

## 13. Sign-off

This specification represents the complete vision for Rocq Type Theory Game v1.0 - a serverless, educator-friendly, browser-based learning platform. Implementation should follow phases outlined in Section 10, with regular stakeholder review after each milestone.

**Key Architecture Decisions**:
- ✅ Pure SPA (no backend/database)
- ✅ Zero hosting costs (static hosting)
- ✅ LocalStorage for all data persistence
- ✅ Export/Import for assignment submission
- ✅ Modular world system for educators
- ✅ jsCoq for in-browser proof checking

**Next Review**: After Phase 1 MVP completion