import { useEffect, useState } from 'react';
import { Achievement } from '../types/game';
import { getAllAchievements, getAchievement } from '../services/achievementEngine';
import { useGameState } from './useGameState';

export function useAchievements() {
  const { gameData } = useGameState();
  const [achievements, setAchievements] = useState<Achievement[]>([]);

  useEffect(() => {
    const allAchievements = getAllAchievements();
    const unlocked = allAchievements.map(ach => {
      const unlockedAt = gameData?.achievements[ach.id]?.unlockedAt;
      return { ...ach, unlockedAt };
    });
    setAchievements(unlocked);
  }, [gameData]);

  const getUnlockedAchievements = () => {
    return achievements.filter(ach => ach.unlockedAt);
  };

  const getAchievementById = (id: string) => {
    return getAchievement(id);
  };

  return {
    achievements,
    unlockedAchievements: getUnlockedAchievements(),
    getAchievementById,
  };
}

