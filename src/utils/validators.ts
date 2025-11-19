import { World, Level } from '../types/world';
import { GameData } from '../types/game';

export function validateWorld(world: any): world is World {
  if (!world || typeof world !== 'object') return false;
  if (!world.id || !world.name || !world.description) return false;
  if (typeof world.order !== 'number') return false;
  if (!Array.isArray(world.levels)) return false;
  
  return world.levels.every((level: any) => validateLevel(level));
}

export function validateLevel(level: any): level is Level {
  if (!level || typeof level !== 'object') return false;
  if (!level.id || !level.name || !level.description) return false;
  if (!level.objective || !level.startingCode || !level.solution) return false;
  if (!Array.isArray(level.hints) || level.hints.length !== 3) return false;
  if (typeof level.difficulty !== 'number' || level.difficulty < 1 || level.difficulty > 5) return false;
  
  return true;
}

export function validateGameData(data: any): data is GameData {
  if (!data || typeof data !== 'object') return false;
  if (!data.version || !data.user || !data.progress) return false;
  if (!data.proofs || !data.unlockedTactics || !data.achievements || !data.settings) return false;
  
  return true;
}

