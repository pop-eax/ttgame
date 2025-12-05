import { World } from '../types/world';
import { validateWorld } from '../utils/validators';
import { loadRocqWorld, rocqToJsonWorld } from './rocqWorldParser';

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
      const idFromFile = w.file.replace(/\.(json|v)$/, '').split('-')[0];
      return idFromFile === worldId;
    });
    
    if (!worldInfo) {
      throw new Error(`World ${worldId} not found in manifest`);
    }
    
    const filename = worldInfo.file;
    const isRocqFormat = filename.endsWith('.v');
    
    if (isRocqFormat) {
      // Load Rocq format
      const parsed = await loadRocqWorld(filename);
      if (!parsed) {
        throw new Error('Failed to parse Rocq world');
      }
      
      const data = rocqToJsonWorld(parsed);
      
      if (!validateWorld(data)) {
        throw new Error('Invalid world data structure');
      }
      
      WORLDS_CACHE.set(worldId, data);
      return data;
    } else {
      // Load JSON format (legacy)
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
    }
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

