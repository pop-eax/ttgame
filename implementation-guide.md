# Rocq Type Theory Game - Technical Implementation Guide

> **For AI Coding Agents**: This guide provides concrete implementation details, file structures, and code examples to complement the project specification.

---

## 1. Project Structure

```
rocq-type-theory-game/
├── public/
│   ├── worlds/
│   │   ├── world0-tutorial.json
│   │   ├── world1-foundations.json
│   │   ├── world2-propositions.json
│   │   ├── world3-dependent.json
│   │   ├── world4-inductive.json
│   │   ├── world5-equality.json
│   │   ├── world6-higher-order.json
│   │   ├── world7-advanced.json
│   │   └── custom/
│   │       └── .gitkeep
│   ├── config/
│   │   ├── worlds-manifest.json
│   │   ├── tactics.json
│   │   └── achievements.json
│   ├── assets/
│   │   ├── logo.svg
│   │   └── icons/
│   └── index.html
├── src/
│   ├── components/
│   │   ├── common/
│   │   │   ├── Button.tsx
│   │   │   ├── Modal.tsx
│   │   │   ├── Toast.tsx
│   │   │   └── Spinner.tsx
│   │   ├── layout/
│   │   │   ├── Header.tsx
│   │   │   ├── Footer.tsx
│   │   │   └── Layout.tsx
│   │   ├── worlds/
│   │   │   ├── WorldMap.tsx
│   │   │   ├── WorldCard.tsx
│   │   │   └── LevelList.tsx
│   │   ├── level/
│   │   │   ├── LevelView.tsx
│   │   │   ├── ProofEditor.tsx
│   │   │   ├── ProofState.tsx
│   │   │   ├── TheoryPanel.tsx
│   │   │   ├── HintsPanel.tsx
│   │   │   ├── TacticReference.tsx
│   │   │   └── SuccessModal.tsx
│   │   ├── profile/
│   │   │   ├── UserMenu.tsx
│   │   │   ├── ProgressView.tsx
│   │   │   ├── AchievementsView.tsx
│   │   │   ├── ExportModal.tsx
│   │   │   └── ImportModal.tsx
│   │   └── tutorial/
│   │       └── TutorialOverlay.tsx
│   ├── hooks/
│   │   ├── useGameState.ts
│   │   ├── useLocalStorage.ts
│   │   ├── useJsCoq.ts
│   │   ├── useProofExecution.ts
│   │   └── useAchievements.ts
│   ├── context/
│   │   ├── GameContext.tsx
│   │   ├── JsCoqContext.tsx
│   │   └── ThemeContext.tsx
│   ├── services/
│   │   ├── storage.ts
│   │   ├── worldLoader.ts
│   │   ├── proofValidator.ts
│   │   ├── exportService.ts
│   │   └── achievementEngine.ts
│   ├── types/
│   │   ├── game.ts
│   │   ├── world.ts
│   │   ├── level.ts
│   │   ├── proof.ts
│   │   └── jscoq.d.ts
│   ├── utils/
│   │   ├── checksum.ts
│   │   ├── dateHelpers.ts
│   │   └── validators.ts
│   ├── pages/
│   │   ├── HomePage.tsx
│   │   ├── WorldMapPage.tsx
│   │   ├── LevelPage.tsx
│   │   ├── ProgressPage.tsx
│   │   └── HelpPage.tsx
│   ├── styles/
│   │   └── globals.css
│   ├── App.tsx
│   ├── main.tsx
│   └── vite-env.d.ts
├── .gitignore
├── package.json
├── tsconfig.json
├── vite.config.ts
├── tailwind.config.js
├── postcss.config.js
└── README.md
```

---

## 2. Complete Type Definitions

```typescript
// src/types/world.ts
export interface World {
  id: string;
  name: string;
  description: string;
  order: number;
  prerequisites?: string[];
  icon?: string;
  color?: string;
  estimatedHours?: number;
  tags?: string[];
  levels: Level[];
}

export interface Level {
  id: string;
  name: string;
  description: string;
  difficulty: 1 | 2 | 3 | 4 | 5;
  estimatedTime?: number;
  objective: string;
  startingCode: string;
  solution: string;
  alternativeSolutions?: string[];
  hints: [string, string, string];
  theory?: Theory;
  prerequisites?: string[];
  unlockedTactics?: string[];
  rewards?: Rewards;
  validation?: ValidationConfig;
  commonMistakes?: CommonMistake[];
}

export interface Theory {
  markdown: string;
  examples?: CodeExample[];
}

export interface CodeExample {
  title: string;
  code: string;
}

export interface Rewards {
  xp?: number;
  achievements?: string[];
}

export interface ValidationConfig {
  checkFunction?: string;
  timeoutMs?: number;
}

export interface CommonMistake {
  pattern: string;
  explanation: string;
  suggestion: string;
}

// src/types/game.ts
export interface GameData {
  version: string;
  user: User;
  progress: Progress;
  proofs: Record<string, ProofRecord>;
  unlockedTactics: string[];
  achievements: Record<string, Achievement>;
  settings: Settings;
}

export interface User {
  id: string;
  name?: string;
  createdAt: string;
  lastActive: string;
}

export interface Progress {
  completedLevels: string[];
  currentWorld: string;
  currentLevel: string;
  xp: number;
  level: number;
}

export interface ProofRecord {
  code: string;
  completedAt: string;
  timeSpent: number;
  hintsUsed: number;
  attempts: number;
  correct: boolean;
}

export interface Achievement {
  id: string;
  name: string;
  description: string;
  icon: string;
  unlockedAt?: string;
}

export interface Settings {
  theme: 'light' | 'dark';
  fontSize: number;
  autoSave: boolean;
}

// src/types/proof.ts
export interface ProofState {
  goals: Goal[];
  hypotheses: Hypothesis[];
  messages: Message[];
  isComplete: boolean;
  hasError: boolean;
}

export interface Goal {
  id: string;
  type: string;
  context: Hypothesis[];
}

export interface Hypothesis {
  name: string;
  type: string;
}

export interface Message {
  level: 'info' | 'warning' | 'error';
  text: string;
  location?: {
    line: number;
    column: number;
  };
}

// src/types/export.ts
export interface ExportData {
  exportVersion: string;
  exportedAt: string;
  studentInfo?: {
    name?: string;
    id?: string;
  };
  assignment?: {
    worldId: string;
    requiredLevels: string[];
  };
  proofs: Record<string, ProofRecord>;
  checksum: string;
}
```

---

## 3. Example World JSON Files

### World 0: Tutorial (Complete)

```json
{
  "id": "world0",
  "name": "Rocq Basics",
  "description": "Learn the fundamentals of Rocq syntax and proof structure",
  "order": 0,
  "icon": "🎓",
  "color": "#3b82f6",
  "estimatedHours": 0.5,
  "tags": ["tutorial", "beginner"],
  "levels": [
    {
      "id": "0.1",
      "name": "Welcome to Rocq",
      "description": "Run your first Rocq command",
      "difficulty": 1,
      "estimatedTime": 2,
      "objective": "Type 'Check nat.' and see what Rocq responds",
      "theory": {
        "markdown": "# Welcome to Rocq!\n\nRocq (formerly Coq) is a proof assistant that helps you write mathematical proofs.\n\n## The Check Command\n\nThe `Check` command tells you the type of any expression.\n\nTry typing: `Check nat.`",
        "examples": [
          {
            "title": "Checking types",
            "code": "Check nat.\n(* nat : Set *)"
          },
          {
            "title": "Checking functions",
            "code": "Check (fun x : nat => x).\n(* fun x : nat => x : nat -> nat *)"
          }
        ]
      },
      "startingCode": "(* Type the Check command below *)\n",
      "solution": "Check nat.",
      "hints": [
        "Type 'Check' followed by what you want to check",
        "Try 'Check nat.' (don't forget the period!)",
        "The exact answer is: Check nat."
      ],
      "unlockedTactics": [],
      "rewards": {
        "xp": 50,
        "achievements": ["first_command"]
      }
    },
    {
      "id": "0.2",
      "name": "Definitions",
      "description": "Define a constant",
      "difficulty": 1,
      "estimatedTime": 3,
      "objective": "Define a constant called 'five' equal to the number 5",
      "theory": {
        "markdown": "# Definitions\n\nYou can define constants using the `Definition` keyword.\n\n## Syntax\n\n```\nDefinition name : type := value.\n```",
        "examples": [
          {
            "title": "Simple definition",
            "code": "Definition three : nat := 3.\nCheck three.\n(* three : nat *)"
          }
        ]
      },
      "startingCode": "(* Define 'five' here *)\n",
      "solution": "Definition five : nat := 5.",
      "hints": [
        "Use the Definition keyword",
        "The syntax is: Definition name : type := value.",
        "Try: Definition five : nat := 5."
      ],
      "unlockedTactics": [],
      "rewards": {
        "xp": 50
      }
    },
    {
      "id": "0.3",
      "name": "Your First Theorem",
      "description": "State a theorem",
      "difficulty": 1,
      "estimatedTime": 3,
      "objective": "State a theorem that nat is a Type",
      "theory": {
        "markdown": "# Theorems\n\nTheorems are statements we want to prove.\n\n## Syntax\n\n```\nTheorem name : statement.\n```\n\nWe'll prove it in the next level!",
        "examples": [
          {
            "title": "Theorem statement",
            "code": "Theorem example : nat."
          }
        ]
      },
      "startingCode": "(* State a theorem that nat is a Type *)\n",
      "solution": "Theorem nat_is_type : Type.",
      "hints": [
        "Use the Theorem keyword",
        "The statement should be just 'Type'",
        "Try: Theorem nat_is_type : Type."
      ],
      "unlockedTactics": [],
      "rewards": {
        "xp": 75
      }
    },
    {
      "id": "0.4",
      "name": "Proof Structure",
      "description": "Learn about Proof...Qed",
      "difficulty": 1,
      "estimatedTime": 3,
      "objective": "Start and end a proof (we'll fill it in next)",
      "theory": {
        "markdown": "# Proof Structure\n\nEvery proof has the same structure:\n\n```\nTheorem name : statement.\nProof.\n  (* proof steps here *)\nQed.\n```\n\n- `Proof.` starts the proof\n- `Qed.` ends the proof (after it's complete)",
        "examples": []
      },
      "startingCode": "Theorem nat_is_type : Type.\n(* Add Proof. and Qed. with tactics between them *)\n",
      "solution": "Theorem nat_is_type : Type.\nProof.\n  exact nat.\nQed.",
      "hints": [
        "Start with 'Proof.'",
        "You need a tactic in between (use 'exact nat.')",
        "End with 'Qed.'"
      ],
      "unlockedTactics": ["exact"],
      "rewards": {
        "xp": 100,
        "achievements": ["first_proof"]
      }
    },
    {
      "id": "0.5",
      "name": "The Exact Tactic",
      "description": "Provide a proof term directly",
      "difficulty": 2,
      "estimatedTime": 5,
      "objective": "Use 'exact' to prove nat is a Type",
      "theory": {
        "markdown": "# The exact Tactic\n\nThe `exact` tactic provides a proof term directly.\n\n## Syntax\n\n```\nexact term.\n```\n\nIf `term` has exactly the type you need to prove, you're done!",
        "examples": [
          {
            "title": "Using exact",
            "code": "Theorem example : nat.\nProof.\n  exact 42.\nQed."
          }
        ]
      },
      "startingCode": "Theorem nat_is_type : Type.\nProof.\n  (* Use exact here *)\nQed.",
      "solution": "Theorem nat_is_type : Type.\nProof.\n  exact nat.\nQed.",
      "hints": [
        "You need to provide something that has type 'Type'",
        "nat is a Type!",
        "Use: exact nat."
      ],
      "unlockedTactics": [],
      "rewards": {
        "xp": 100
      }
    },
    {
      "id": "0.6",
      "name": "Comments",
      "description": "Learn to write comments",
      "difficulty": 1,
      "estimatedTime": 2,
      "objective": "Add a comment to your proof",
      "theory": {
        "markdown": "# Comments\n\nComments help document your code.\n\n## Syntax\n\n```\n(* This is a comment *)\n```\n\nComments are ignored by Rocq but help humans understand your code!",
        "examples": [
          {
            "title": "Using comments",
            "code": "(* This theorem shows nat is a Type *)\nTheorem nat_is_type : Type.\nProof.\n  (* Just provide nat directly *)\n  exact nat.\nQed."
          }
        ]
      },
      "startingCode": "Theorem nat_is_type : Type.\nProof.\n  exact nat.\nQed.\n\n(* Add a comment above explaining what this proves *)",
      "solution": "(* nat is a Type *)\nTheorem nat_is_type : Type.\nProof.\n  exact nat.\nQed.",
      "hints": [
        "Comments use (* and *)",
        "Put a comment above the Theorem line",
        "Any comment works - just add (* your text *)"
      ],
      "unlockedTactics": [],
      "rewards": {
        "xp": 50
      }
    },
    {
      "id": "0.7",
      "name": "Tutorial Complete!",
      "description": "You're ready for the real challenges",
      "difficulty": 2,
      "estimatedTime": 5,
      "objective": "Prove that functions exist",
      "theory": {
        "markdown": "# Congratulations!\n\nYou've learned:\n- The Check command\n- How to define constants\n- How to state theorems\n- Proof structure (Proof...Qed)\n- The exact tactic\n- Comments\n\nNow let's prove something more interesting: that function types exist!",
        "examples": []
      },
      "startingCode": "(* Prove that the function type nat -> nat exists *)\nTheorem function_type_exists : Type.\nProof.\n  (* Your proof here *)\nQed.",
      "solution": "Theorem function_type_exists : Type.\nProof.\n  exact (nat -> nat).\nQed.",
      "hints": [
        "Function types use the arrow: A -> B",
        "You need to provide a function type",
        "Try: exact (nat -> nat)."
      ],
      "unlockedTactics": [],
      "rewards": {
        "xp": 150,
        "achievements": ["tutorial_complete"]
      }
    }
  ]
}
```

### World 1: Type Foundations (First 2 Levels)

```json
{
  "id": "world1",
  "name": "Type Foundations",
  "description": "Learn about basic type constructors and function types",
  "order": 1,
  "prerequisites": ["world0"],
  "icon": "🏗️",
  "color": "#10b981",
  "estimatedHours": 2,
  "tags": ["types", "functions", "foundational"],
  "levels": [
    {
      "id": "1.1",
      "name": "Function Types",
      "description": "Understand arrow types (→)",
      "difficulty": 2,
      "estimatedTime": 5,
      "objective": "Construct a function that takes a nat and returns it",
      "theory": {
        "markdown": "# Function Types\n\nFunction types are written with arrows: `A -> B`\n\nThis means: a function that takes an `A` and returns a `B`.\n\n## The intro Tactic\n\nThe `intro` tactic introduces a function argument.\n\n```\nintro name.\n```\n\nThis gives you a variable to work with in your proof.",
        "examples": [
          {
            "title": "Identity function",
            "code": "Theorem id_nat : nat -> nat.\nProof.\n  intro n.  (* Now we have n : nat *)\n  exact n.  (* Return it *)\nQed."
          }
        ]
      },
      "startingCode": "Theorem identity : nat -> nat.\nProof.\n  (* Your proof here *)\nQed.",
      "solution": "Theorem identity : nat -> nat.\nProof.\n  intro n.\n  exact n.\nQed.",
      "hints": [
        "Use 'intro' to get the argument",
        "Give it a name like 'intro n'",
        "Then use 'exact n' to return it"
      ],
      "unlockedTactics": ["intro"],
      "rewards": {
        "xp": 100
      }
    },
    {
      "id": "1.2",
      "name": "Product Types",
      "description": "Learn about pairs (A × B)",
      "difficulty": 3,
      "estimatedTime": 8,
      "objective": "Construct a pair of natural numbers",
      "theory": {
        "markdown": "# Product Types\n\nProduct types represent pairs: `A * B`\n\nThis is a value that contains both an `A` and a `B`.\n\n## The split Tactic\n\nThe `split` tactic breaks a product goal into two subgoals:\n\n```\nsplit.\n(* Now you have two goals to prove *)\n```",
        "examples": [
          {
            "title": "Making a pair",
            "code": "Theorem make_pair : nat * nat.\nProof.\n  split.\n  - exact 0.  (* First component *)\n  - exact 1.  (* Second component *)\nQed."
          }
        ]
      },
      "startingCode": "Theorem pair_zero_one : nat * nat.\nProof.\n  (* Your proof here *)\nQed.",
      "solution": "Theorem pair_zero_one : nat * nat.\nProof.\n  split.\n  - exact 0.\n  - exact 1.\nQed.",
      "alternativeSolutions": [
        "Theorem pair_zero_one : nat * nat.\nProof.\n  split.\n  exact 0.\n  exact 1.\nQed."
      ],
      "hints": [
        "Use 'split' to create two goals",
        "Provide a number for each goal with 'exact'",
        "Try 'exact 0.' for the first, 'exact 1.' for the second"
      ],
      "unlockedTactics": ["split"],
      "rewards": {
        "xp": 150
      },
      "commonMistakes": [
        {
          "pattern": "exact (0, 1)",
          "explanation": "You can't use tuple syntax directly in Rocq",
          "suggestion": "Use the 'split' tactic to break it into two goals"
        }
      ]
    }
  ]
}
```

---

## 4. Key Service Implementations

### Storage Service

```typescript
// src/services/storage.ts
import { GameData, ExportData } from '../types/game';
import { generateChecksum, verifyChecksum } from '../utils/checksum';

const STORAGE_KEY = 'rocq_game_data';
const CURRENT_VERSION = '1.0';

export class GameStorage {
  static save(data: GameData): void {
    try {
      const json = JSON.stringify(data);
      localStorage.setItem(STORAGE_KEY, json);
    } catch (error) {
      console.error('Failed to save game data:', error);
      throw new Error('Storage quota exceeded or localStorage unavailable');
    }
  }

  static load(): GameData | null {
    try {
      const json = localStorage.getItem(STORAGE_KEY);
      if (!json) return null;
      
      const data = JSON.parse(json) as GameData;
      
      // Migrate if necessary
      if (data.version !== CURRENT_VERSION) {
        return this.migrate(data);
      }
      
      return data;
    } catch (error) {
      console.error('Failed to load game data:', error);
      return null;
    }
  }

  static exportJSON(options?: {
    studentName?: string;
    studentId?: string;
    worldId?: string;
    requiredLevels?: string[];
  }): string {
    const data = this.load();
    if (!data) throw new Error('No data to export');

    const exportData: ExportData = {
      exportVersion: CURRENT_VERSION,
      exportedAt: new Date().toISOString(),
      studentInfo: options?.studentName || options?.studentId ? {
        name: options.studentName,
        id: options.studentId,
      } : undefined,
      assignment: options?.worldId ? {
        worldId: options.worldId,
        requiredLevels: options.requiredLevels || [],
      } : undefined,
      proofs: data.proofs,
      checksum: '', // Will be calculated
    };

    // Calculate checksum
    exportData.checksum = generateChecksum(exportData);

    return JSON.stringify(exportData, null, 2);
  }

  static importJSON(json: string): boolean {
    try {
      const exportData = JSON.parse(json) as ExportData;
      
      // Verify checksum
      if (!verifyChecksum(exportData)) {
        throw new Error('Invalid checksum - data may be corrupted or tampered');
      }

      const currentData = this.load() || this.createEmpty();
      
      // Merge proofs
      currentData.proofs = {
        ...currentData.proofs,
        ...exportData.proofs,
      };

      // Update completed levels
      const completedLevels = Object.keys(exportData.proofs).filter(
        levelId => exportData.proofs[levelId].correct
      );
      currentData.progress.completedLevels = [
        ...new Set([...currentData.progress.completedLevels, ...completedLevels])
      ];

      this.save(currentData);
      return true;
    } catch (error) {
      console.error('Failed to import data:', error);
      return false;
    }
  }

  static clear(): void {
    localStorage.removeItem(STORAGE_KEY);
  }

  private static createEmpty(): GameData {
    return {
      version: CURRENT_VERSION,
      user: {
        id: crypto.randomUUID(),
        createdAt: new Date().toISOString(),
        lastActive: new Date().toISOString(),
      },
      progress: {
        completedLevels: [],
        currentWorld: 'world0',
        currentLevel: '0.1',
        xp: 0,
        level: 1,
      },
      proofs: {},
      unlockedTactics: [],
      achievements: {},
      settings: {
        theme: 'light',
        fontSize: 14,
        autoSave: true,
      },
    };
  }

  private static migrate(data: GameData): GameData {
    // Handle version migrations here
    return { ...data, version: CURRENT_VERSION };
  }
}
```

### Checksum Utility

```typescript
// src/utils/checksum.ts
import { ExportData } from '../types/export';

export function generateChecksum(data: ExportData): string {
  // Create a stable string representation (excluding checksum field)
  const { checksum, ...dataToHash } = data;
  const jsonString = JSON.stringify(dataToHash, Object.keys(dataToHash).sort());
  
  // Simple SHA-256 implementation using Web Crypto API
  return hashString(jsonString);
}

export function verifyChecksum(data: ExportData): boolean {
  const providedChecksum = data.checksum;
  const calculatedChecksum = generateChecksum(data);
  return providedChecksum === calculatedChecksum;
}

async function hashString(str: string): Promise<string> {
  const encoder = new TextEncoder();
  const data = encoder.encode(str);
  const hashBuffer = await crypto.subtle.digest('SHA-256', data);
  const hashArray = Array.from(new Uint8Array(hashBuffer));
  return hashArray.map(b => b.toString(16).padStart(2, '0')).join('');
}

// Synchronous fallback for non-async contexts
export function hashString(str: string): string {
  // Simple hash for demo - use proper SHA-256 in production
  let hash = 0;
  for (let i = 0; i < str.length; i++) {
    const char = str.charCodeAt(i);
    hash = ((hash << 5) - hash) + char;
    hash = hash & hash;
  }
  return hash.toString(16);
}
```

---

## 5. jsCoq Integration Hook

```typescript
// src/hooks/useJsCoq.ts
import { useState, useEffect, useRef } from 'react';
import { ProofState } from '../types/proof';

declare global {
  interface Window {
    jsCoq: any;
    CoqManager: any;
  }
}

export function useJsCoq() {
  const [isLoaded, setIsLoaded] = useState(false);
  const [isInitializing, setIsInitializing] = useState(false);
  const coqManagerRef = useRef<any>(null);

  useEffect(() => {
    loadJsCoq();
  }, []);

  const loadJsCoq = async () => {
    if (window.jsCoq) {
      setIsLoaded(true);
      return;
    }

    setIsInitializing(true);

    try {
      // Load jsCoq script
      const script = document.createElement('script');
      script.src = 'https://coq.vercel.app/node_modules/jscoq/ui-js/jscoq-loader.js';
      script.async = true;
      
      script.onload = async () => {
        // Initialize jsCoq
        await window.jsCoq.start('/node_modules/jscoq/', null, {
          show: false, // Don't show default UI
          focus: false,
        });

        coqManagerRef.current = window.CoqManager;
        setIsLoaded(true);
        setIsInitializing(false);
      };

      document.body.appendChild(script);
    } catch (error) {
      console.error('Failed to load jsCoq:', error);
      setIsInitializing(false);
    }
  };

  const executeProof = async (code: string): Promise<ProofState> => {
    if (!isLoaded || !coqManagerRef.current) {
      throw new Error('jsCoq not loaded');
    }

    try {
      // Execute code
      const result = await coqManagerRef.current.execute(code);
      
      return parseProofState(result);
    } catch (error: any) {
      return {
        goals: [],
        hypotheses: [],
        messages: [{
          level: 'error',
          text: error.message || 'Proof execution failed',
        }],
        isComplete: false,
        hasError: true,
      };
    }
  };

  const parseProofState = (result: any): ProofState => {
    // Parse jsCoq result into our ProofState format
    const goals = result.goals || [];
    const hypotheses = result.context || [];
    
    return {
      goals: goals.map((g: any) => ({
        id: g.id,
        type: g.type,
        context: g.context || [],
      })),
      hypotheses: hypotheses.map((h: any) => ({
        name: h.name,
        type: h.type,
      })),
      messages: result.messages || [],
      isComplete: goals.length === 0 && !result.error,
      hasError: !!result.error,
    };
  };

  return {
    isLoaded,
    isInitializing,
    executeProof,
  };
}
```

---

## 6. Package.json

```json
{
  "name": "rocq-type-theory-game",
  "version": "1.0.0",
  "description": "Interactive gamified learning platform for type theory using Rocq",
  "type": "module",
  "scripts": {
    "dev": "vite",
    "build": "tsc && vite build",
    "preview": "vite preview",
    "lint": "eslint . --ext ts,tsx",
    "deploy": "npm run build && gh-pages -d dist"
  },
  "dependencies": {
    "react": "^18.2.0",
    "react-dom": "^18.2.0",
    "react-router-dom": "^6.20.0",
    "framer-motion": "^10.16.0",
    "lucide-react": "^0.294.0",
    "react-hot-toast": "^2.4.1",
    "react-markdown": "^9.0.1",
    "zustand": "^4.4.7",
    "@monaco-editor/react": "^4.6.0"
  },
  "devDependencies": {
    "@types/react": "^18.2.0",
    "@types/react-dom": "^18.2.0",
    "@typescript-eslint/eslint-plugin": "^6.0.0",
    "@typescript-eslint/parser": "^6.0.0",
    "@vitejs/plugin-react": "^4.2.0",
    "autoprefixer": "^10.4.16",
    "eslint": "^8.0.0",
    "gh-pages": "^6.1.0",
    "postcss": "^8.4.32",
    "tailwindcss": "^3.3.6",
    "typescript": "^5.3.0",
    "vite": "^5.0.0"
  }
}
```

---

## 7. Vite Configuration

```typescript
// vite.config.ts
import { defineConfig } from 'vite';
import react from '@vitejs/plugin-react';
import path from 'path';

export default defineConfig({
  plugins: [react()],
  resolve: {
    alias: {
      '@': path.resolve(__dirname, './src'),
    },
  },
  build: {
    outDir: 'dist',
    sourcemap: true,
    rollupOptions: {
      output: {
        manualChunks: {
          'react-vendor': ['react', 'react-dom', 'react-router-dom'],
          'ui-vendor': ['framer-motion', 'lucide-react', 'react-hot-toast'],
          'editor': ['@monaco-editor/react'],
        },
      },
    },
  },
  base: './', // Use relative paths for any hosting
  server: {
    port: 3000,
    open: true,
  },
});
```

---

## 8. Tailwind Configuration

```javascript
// tailwind.config.js
/** @type {import('tailwindcss').Config} */
export default {
  content: [
    "./index.html",
    "./src/**/*.{js,ts,jsx,tsx}",
  ],
  theme: {
    extend: {
      colors: {
        primary: {
          50: '#eff6ff',
          500: '#3b82f6',
          600: '#2563eb',
          700: '#1d4ed8',
        },
        success: {
          500: '#10b981',
          600: '#059669',
        },
        warning: {
          500: '#f59e0b',
        },
        error: {
          500: '#ef4444',
        },
      },
      animation: {
        'bounce-slow': 'bounce 2s infinite',
        'pulse-slow': 'pulse 3s infinite',
      },
    },
  },
  plugins: [],
  darkMode: 'class',
}
```

---

## 9. World Manifest

```json
{
  "version": "1.0",
  "lastUpdated": "2024-11-18",
  "worlds": [
    {
      "file": "world0-tutorial.json",
      "enabled": true,
      "alwaysUnlocked": true
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
      "file": "world3-dependent.json",
      "enabled": true
    },
    {
      "file": "world4-inductive.json",
      "enabled": true
    },
    {
      "file": "world5-equality.json",
      "enabled": true
    },
    {
      "file": "world6-higher-order.json",
      "enabled": false,
      "comingSoon": true
    },
    {
      "file": "world7-advanced.json",
      "enabled": false,
      "comingSoon": true
    }
  ]
}
```

---

## 10. Component Example: LevelView

```tsx
// src/components/level/LevelView.tsx
import React, { useState, useEffect } from 'react';
import { useParams, useNavigate } from 'react-router-dom';
import { Level } from '@/types/world';
import { ProofEditor } from './ProofEditor';
import { ProofState as ProofStateComponent } from './ProofState';
import { TheoryPanel } from './TheoryPanel';
import { HintsPanel } from './HintsPanel';
import { SuccessModal } from './SuccessModal';
import { useJsCoq } from '@/hooks/useJsCoq';
import { useGameState } from '@/hooks/useGameState';
import { Button } from '@/components/common/Button';
import toast from 'react-hot-toast';

export function LevelView() {
  const { worldId, levelId } = useParams();
  const navigate = useNavigate();
  const { executeProof, isLoaded } = useJsCoq();
  const { getLevel, completeLevel, saveProof } = useGameState();
  
  const [level, setLevel] = useState<Level | null>(null);
  const [code, setCode] = useState('');
  const [proofState, setProofState] = useState<any>(null);
  const [hintsUsed, setHintsUsed] = useState(0);
  const [attempts, setAttempts] = useState(0);
  const [startTime] = useState(Date.now());
  const [showSuccess, setShowSuccess] = useState(false);
  const [showTheory, setShowTheory] = useState(false);

  useEffect(() => {
    if (worldId && levelId) {
      const loadedLevel = getLevel(worldId, levelId);
      if (loadedLevel) {
        setLevel(loadedLevel);
        setCode(loadedLevel.startingCode);
      }
    }
  }, [worldId, levelId]);

  const handleRunProof = async () => {
    if (!isLoaded) {
      toast.error('jsCoq is still loading...');
      return;
    }

    setAttempts(prev => prev + 1);

    try {
      const result = await executeProof(code);
      setProofState(result);

      if (result.isComplete && !result.hasError) {
        // Success!
        const timeSpent = Math.floor((Date.now() - startTime) / 1000);
        
        saveProof(level!.id, {
          code,
          completedAt: new Date().toISOString(),
          timeSpent,
          hintsUsed,
          attempts,
          correct: true,
        });

        completeLevel(level!.id);
        setShowSuccess(true);
      } else if (result.hasError) {
        toast.error('Proof has errors - check the messages below');
      }
    } catch (error: any) {
      toast.error(error.message || 'Failed to execute proof');
    }
  };

  const handleHintRequest = (hintNumber: number) => {
    setHintsUsed(Math.max(hintsUsed, hintNumber));
  };

  if (!level) {
    return <div>Loading...</div>;
  }

  return (
    <div className="min-h-screen bg-gray-50">
      {/* Header */}
      <div className="bg-white border-b">
        <div className="max-w-7xl mx-auto px-4 py-4 flex items-center justify-between">
          <Button onClick={() => navigate(`/worlds/${worldId}`)}>
            ← Back to World
          </Button>
          <div className="text-center">
            <h1 className="text-2xl font-bold">{level.name}</h1>
            <p className="text-gray-600">{'★'.repeat(level.difficulty)}</p>
          </div>
          <Button onClick={handleRunProof} disabled={!isLoaded}>
            Run Proof
          </Button>
        </div>
      </div>

      {/* Main Content */}
      <div className="max-w-7xl mx-auto px-4 py-6">
        <div className="grid grid-cols-3 gap-6">
          {/* Left Column: Theory */}
          <div className="col-span-1">
            <TheoryPanel 
              theory={level.theory}
              objective={level.objective}
              show={showTheory}
              onToggle={() => setShowTheory(!showTheory)}
            />
          </div>

          {/* Middle Column: Editor */}
          <div className="col-span-2">
            <div className="bg-white rounded-lg shadow p-4 mb-4">
              <h3 className="font-semibold mb-2">Objective</h3>
              <p>{level.objective}</p>
            </div>

            <ProofEditor
              value={code}
              onChange={setCode}
              isLoaded={isLoaded}
            />

            {proofState && (
              <ProofStateComponent state={proofState} />
            )}
          </div>
        </div>

        {/* Bottom: Hints */}
        <HintsPanel
          hints={level.hints}
          onHintRequest={handleHintRequest}
        />
      </div>

      {/* Success Modal */}
      {showSuccess && (
        <SuccessModal
          level={level}
          hintsUsed={hintsUsed}
          timeSpent={Math.floor((Date.now() - startTime) / 1000)}
          onNext={() => {
            // Navigate to next level
            navigate(`/worlds/${worldId}`);
          }}
        />
      )}
    </div>
  );
}
```

---

## 11. Build & Deployment Commands

```bash
# Development
npm install
npm run dev        # Start dev server at localhost:3000

# Build for production
npm run build      # Output to dist/

# Preview production build
npm run preview

# Deploy to GitHub Pages
npm run deploy     # Automatically builds and pushes to gh-pages branch

# Manual deployment to Netlify
npm run build
# Then drag dist/ folder to netlify.com

# Manual deployment to Vercel
npm run build
vercel --prod      # Or connect GitHub repo in Vercel dashboard
```

---

## 12. Critical Implementation Notes

### For the AI Coding Agent:

1. **jsCoq Integration Priority**:
   - Start with a mock implementation that simulates proof checking
   - Integrate real jsCoq only after core UI is working
   - jsCoq loading is slow - show spinner and cache aggressively

2. **localStorage First**:
   - Implement all storage via localStorage
   - Auto-save after every completed level
   - Handle quota exceeded errors gracefully

3. **World Loading**:
   - Load worlds lazily (only load current world)
   - Cache parsed JSON in memory
   - Validate JSON schema on load

4. **Error Handling**:
   - Wrap all localStorage access in try-catch
   - Show user-friendly error messages
   - Provide fallback UI if jsCoq fails to load

5. **Performance**:
   - Code-split by world (don't load all 8 worlds at once)
   - Lazy load Monaco Editor
   - Use React.memo for expensive components

6. **Testing Strategy**:
   - Test with localStorage disabled
   - Test import/export with real JSON files
   - Test all 7 tutorial levels manually
   - Verify checksums can't be bypassed

7. **Critical Path for MVP**:
   1. Basic routing (Home → World Map → Level)
   2. World JSON loading
   3. localStorage save/load
   4. Mock proof validation (accept solution === code)
   5. Level completion and unlocking
   6. Export/Import functionality
   7. Real jsCoq integration (can be last!)

---

## 13. Testing Checklist

Before marking MVP complete, verify:

- [ ] All 7 tutorial levels load and work
- [ ] localStorage persists across page refreshes
- [ ] Export downloads valid JSON file
- [ ] Import accepts valid JSON and merges data
- [ ] Checksum validation prevents tampering
- [ ] World unlocking works correctly
- [ ] Tactic unlocking shows animations
- [ ] Hints deduct points correctly
- [ ] Achievements trigger on conditions
- [ ] Works on Chrome, Firefox, Safari
- [ ] Mobile responsive (tablet size minimum)
- [ ] No console errors
- [ ] Builds successfully with `npm run build`
- [ ] Deployed version loads in <5 seconds

---

## 14. Common Pitfalls to Avoid

1. **Don't** try to implement all 8 worlds at once - start with World 0
2. **Don't** make jsCoq integration block other development
3. **Don't** use any backend/API calls - everything client-side
4. **Don't** overcomplicate the UI - keep it clean and functional
5. **Don't** skip the checksum validation - it's critical for teacher verification
6. **Don't** hardcode world data - load from JSON files
7. **Don't** forget to handle localStorage quota exceeded
8. **Don't** make the export button hard to find - teachers need it
9. **Don't** skip mobile responsiveness testing
10. **Don't** deploy without testing import/export thoroughly

---

## 15. Success Criteria

The implementation is complete when:

✅ A new user can complete all 7 tutorial levels  
✅ Progress persists across browser sessions  
✅ Export creates a valid JSON file  
✅ Import loads the JSON and updates progress  
✅ Teachers can verify student work from JSON  
✅ The app loads and works in all major browsers  
✅ The app can be deployed to free static hosting  
✅ No errors in browser console  
✅ All worlds are defined in JSON files  
✅ jsCoq successfully validates real proofs  

Good luck! 🚀