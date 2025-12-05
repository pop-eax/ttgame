import React, { useEffect, useState } from 'react';
import { useNavigate } from 'react-router-dom';
import { WorldCard } from '../components/worlds/WorldCard';
import { useGame } from '../context/GameContext';
import { loadWorldsManifest, loadWorld } from '../services/worldLoader';
import { Spinner } from '../components/common/Spinner';

export function WorldMapPage() {
  const navigate = useNavigate();
  const { gameData, isWorldUnlocked, loadWorldData } = useGame();
  const [worlds, setWorlds] = useState<any[]>([]);
  const [loadedWorlds, setLoadedWorlds] = useState<Map<string, any>>(new Map());
  const [loading, setLoading] = useState(true);

  useEffect(() => {
    async function loadWorlds() {
      try {
        const manifest = await loadWorldsManifest();
        const enabledWorlds = manifest.worlds.filter((w: any) => w.enabled);
        
        setWorlds(enabledWorlds);
        
        // Load world data for enabled worlds
        for (const worldInfo of enabledWorlds) {
          // Extract worldId from filename (e.g., "world0-tutorial.json" or "world0-tutorial.v" -> "world0")
          const worldId = worldInfo.file.replace(/\.(json|v)$/, '').split('-')[0];
          const world = await loadWorld(worldId);
          if (world) {
            setLoadedWorlds(prev => new Map(prev).set(world.id, world));
            loadWorldData(world.id);
          }
        }
      } catch (error) {
        console.error('Failed to load worlds:', error);
      } finally {
        setLoading(false);
      }
    }
    
    loadWorlds();
  }, [loadWorldData]);

  if (loading) {
    return (
      <div className="flex items-center justify-center min-h-screen">
        <Spinner size="lg" />
      </div>
    );
  }

  const getCompletedCount = (world: any) => {
    if (!gameData) return 0;
    const worldData = loadedWorlds.get(world.id);
    if (!worldData) return 0;
    return worldData.levels.filter((l: any) =>
      gameData.progress.completedLevels.includes(l.id)
    ).length;
  };

  return (
    <div className="max-w-7xl mx-auto px-4 py-8">
      <h1 className="text-3xl font-bold text-gray-900 mb-8">Worlds</h1>
      
      <div className="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-3 gap-6">
        {worlds.map((worldInfo) => {
          const worldId = worldInfo.file.replace(/\.(json|v)$/, '').split('-')[0];
          const world = loadedWorlds.get(worldId);
          if (!world) return null;
          
          const isUnlocked = worldInfo.alwaysUnlocked || isWorldUnlocked(world.id, world);
          const completedCount = getCompletedCount(world);
          const totalCount = world.levels.length;
          
          return (
            <WorldCard
              key={world.id}
              world={world}
              isUnlocked={isUnlocked}
              completedCount={completedCount}
              totalCount={totalCount}
            />
          );
        })}
      </div>
    </div>
  );
}

