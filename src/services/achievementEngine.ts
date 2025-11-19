import { GameData } from '../types/game';
import { Achievement } from '../types/game';

const ACHIEVEMENTS: Record<string, Achievement> = {
  first_command: {
    id: 'first_command',
    name: 'First Command',
    description: 'Ran your first Rocq command',
    icon: '🎯',
  },
  first_proof: {
    id: 'first_proof',
    name: 'First Proof',
    description: 'Completed your first proof',
    icon: '✨',
  },
  tutorial_complete: {
    id: 'tutorial_complete',
    name: 'Tutorial Master',
    description: 'Completed the tutorial world',
    icon: '🎓',
  },
  no_hints: {
    id: 'no_hints',
    name: 'Independent',
    description: 'Completed 5 levels without hints',
    icon: '🏆',
  },
  speed_runner: {
    id: 'speed_runner',
    name: 'Speed Runner',
    description: 'Completed 10 levels in under 3 minutes each',
    icon: '⚡',
  },
};

export function checkAchievements(gameData: GameData): string[] {
  const newlyUnlocked: string[] = [];
  
  // Check first command
  if (!gameData.achievements.first_command && gameData.proofs['0.1']) {
    newlyUnlocked.push('first_command');
  }
  
  // Check first proof
  if (!gameData.achievements.first_proof && gameData.proofs['0.4']) {
    newlyUnlocked.push('first_proof');
  }
  
  // Check tutorial complete
  const tutorialLevels = ['0.1', '0.2', '0.3', '0.4', '0.5', '0.6', '0.7'];
  if (!gameData.achievements.tutorial_complete && 
      tutorialLevels.every(id => gameData.progress.completedLevels.includes(id))) {
    newlyUnlocked.push('tutorial_complete');
  }
  
  // Check no hints achievement
  const noHintCompletions = Object.values(gameData.proofs).filter(p => p.correct && p.hintsUsed === 0).length;
  if (!gameData.achievements.no_hints && noHintCompletions >= 5) {
    newlyUnlocked.push('no_hints');
  }
  
  // Check speed runner
  const fastCompletions = Object.values(gameData.proofs).filter(
    p => p.correct && p.timeSpent < 180
  ).length;
  if (!gameData.achievements.speed_runner && fastCompletions >= 10) {
    newlyUnlocked.push('speed_runner');
  }
  
  return newlyUnlocked;
}

export function getAchievement(id: string): Achievement | undefined {
  return ACHIEVEMENTS[id];
}

export function getAllAchievements(): Achievement[] {
  return Object.values(ACHIEVEMENTS);
}

