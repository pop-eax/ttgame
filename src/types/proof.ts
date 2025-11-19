export interface ProofState {
  goals: Goal[];
  hypotheses: Hypothesis[];
  messages: Message[];
  isComplete: boolean;
  hasError: boolean;
  rawState?: any; // Raw jsCoq state for detailed formatting
}

export interface Goal {
  id: string;
  type: string;
  context: Hypothesis[];
  rawGoal?: any; // Raw jsCoq goal for formatting
  goalCountText?: string; // "X goal" or "X goals" text from jsCoq
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

