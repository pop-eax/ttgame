import React, { createContext, useContext, ReactNode } from 'react';
import { useGameState } from '../hooks/useGameState';
import { GameData } from '../types/game';
import { World } from '../types/world';

interface GameContextType {
  gameData: GameData | null;
  loading: boolean;
  worlds: Map<string, World>;
  getLevel: (worldId: string, levelId: string) => import('../types/world').Level | null;
  loadWorldData: (worldId: string) => Promise<World | null>;
  completeLevel: (levelId: string) => void;
  saveProof: (levelId: string, proof: import('../types/game').ProofRecord) => void;
  isLevelCompleted: (levelId: string) => boolean;
  isWorldUnlocked: (worldId: string, world: World) => boolean;
  saveGameData: (data: GameData) => void;
}

const GameContext = createContext<GameContextType | undefined>(undefined);

export function GameProvider({ children }: { children: ReactNode }) {
  const gameState = useGameState();

  return (
    <GameContext.Provider value={gameState}>
      {children}
    </GameContext.Provider>
  );
}

export function useGame() {
  const context = useContext(GameContext);
  if (context === undefined) {
    throw new Error('useGame must be used within a GameProvider');
  }
  return context;
}

