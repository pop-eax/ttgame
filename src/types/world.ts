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

