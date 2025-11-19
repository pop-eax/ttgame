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

