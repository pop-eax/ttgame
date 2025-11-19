import { useState, useEffect, useCallback } from 'react';
import { GameData, ProofRecord } from '../types/game';
import { World, Level } from '../types/world';
import { GameStorage } from '../services/storage';
import { loadWorld } from '../services/worldLoader';
import { checkAchievements } from '../services/achievementEngine';

export function useGameState() {
  const [gameData, setGameData] = useState<GameData | null>(null);
  const [worlds, setWorlds] = useState<Map<string, World>>(new Map());
  const [loading, setLoading] = useState(true);

  useEffect(() => {
    // Load game data
    const data = GameStorage.load() || GameStorage.createEmpty();
    setGameData(data);
    setLoading(false);
  }, []);

  const saveGameData = useCallback((data: GameData) => {
    setGameData(data);
    GameStorage.save(data);
  }, []);

  const getLevel = useCallback((worldId: string, levelId: string): Level | null => {
    const world = worlds.get(worldId);
    if (!world) return null;
    return world.levels.find(l => l.id === levelId) || null;
  }, [worlds]);

  const loadWorldData = useCallback(async (worldId: string) => {
    const world = await loadWorld(worldId);
    if (world) {
      setWorlds(prev => new Map(prev).set(worldId, world));
    }
    return world;
  }, []);

  const completeLevel = useCallback((levelId: string) => {
    if (!gameData) return;
    
    const updated = { ...gameData };
    if (!updated.progress.completedLevels.includes(levelId)) {
      updated.progress.completedLevels.push(levelId);
    }
    
    // Check for newly unlocked achievements
    const newAchievements = checkAchievements(updated);
    newAchievements.forEach(achId => {
      updated.achievements[achId] = {
        id: achId,
        name: '',
        description: '',
        icon: '',
        unlockedAt: new Date().toISOString(),
      };
    });
    
    saveGameData(updated);
  }, [gameData, saveGameData]);

  const saveProof = useCallback((levelId: string, proof: ProofRecord) => {
    if (!gameData) return;
    
    const updated = { ...gameData };
    updated.proofs[levelId] = proof;
    
    // Update XP
    if (proof.correct) {
      let xpGain = proof.hintsUsed === 0 ? 150 : 100;
      if (proof.attempts === 1) xpGain += 25;
      if (proof.timeSpent < 300) xpGain += 25;
      
      updated.progress.xp += xpGain;
      updated.progress.level = Math.floor(updated.progress.xp / 500) + 1;
    }
    
    // Unlock tactics
    const level = Array.from(worlds.values())
      .flatMap(w => w.levels)
      .find(l => l.id === levelId);
    
    if (level?.unlockedTactics && proof.correct) {
      level.unlockedTactics.forEach(tactic => {
        if (!updated.unlockedTactics.includes(tactic)) {
          updated.unlockedTactics.push(tactic);
        }
      });
    }
    
    saveGameData(updated);
  }, [gameData, worlds, saveGameData]);

  const isLevelCompleted = useCallback((levelId: string): boolean => {
    if (!gameData) return false;
    return gameData.progress.completedLevels.includes(levelId);
  }, [gameData]);

  const isWorldUnlocked = useCallback((worldId: string, world: World): boolean => {
    if (!gameData) return worldId === 'world0';
    if (world.prerequisites && world.prerequisites.length > 0) {
      return world.prerequisites.every(prereq => {
        const prereqWorld = worlds.get(prereq);
        if (!prereqWorld) return false;
        return prereqWorld.levels.every(level => 
          gameData.progress.completedLevels.includes(level.id)
        );
      });
    }
    return true;
  }, [gameData, worlds]);

  return {
    gameData,
    loading,
    worlds,
    getLevel,
    loadWorldData,
    completeLevel,
    saveProof,
    isLevelCompleted,
    isWorldUnlocked,
    saveGameData,
  };
}

