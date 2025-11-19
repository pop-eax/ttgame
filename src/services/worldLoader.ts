import { World } from '../types/world';
import { validateWorld } from '../utils/validators';

const WORLDS_CACHE = new Map<string, World>();

export async function loadWorld(worldId: string): Promise<World | null> {
  // Check cache first
  if (WORLDS_CACHE.has(worldId)) {
    return WORLDS_CACHE.get(worldId)!;
  }

  try {
    // Get filename from manifest
    const manifest = await loadWorldsManifest();
    const worldInfo = manifest.worlds.find((w: any) => {
      const idFromFile = w.file.replace('.json', '').split('-')[0];
      return idFromFile === worldId;
    });
    
    const filename = worldInfo ? worldInfo.file : `${worldId}.json`;
    const response = await fetch(`/worlds/${filename}`);
    
    if (!response.ok) {
      throw new Error(`Failed to load world: ${response.statusText}`);
    }
    
    const data = await response.json();
    
    if (!validateWorld(data)) {
      throw new Error('Invalid world data structure');
    }
    
    WORLDS_CACHE.set(worldId, data);
    return data;
  } catch (error) {
    console.error(`Error loading world ${worldId}:`, error);
    return null;
  }
}

export async function loadWorldsManifest(): Promise<any> {
  try {
    const response = await fetch('/config/worlds-manifest.json');
    if (!response.ok) {
      throw new Error('Failed to load worlds manifest');
    }
    return await response.json();
  } catch (error) {
    console.error('Error loading worlds manifest:', error);
    return { worlds: [] };
  }
}

export function clearWorldsCache(): void {
  WORLDS_CACHE.clear();
}

