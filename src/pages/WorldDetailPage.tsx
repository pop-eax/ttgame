import { useEffect, useState } from 'react';
import { useParams, useNavigate } from 'react-router-dom';
import { LevelList } from '../components/worlds/LevelList';
import { useGame } from '../context/GameContext';
import { loadWorld } from '../services/worldLoader';
import { Spinner } from '../components/common/Spinner';
import { Button } from '../components/common/Button';

export function WorldDetailPage() {
  const { worldId } = useParams<{ worldId: string }>();
  const navigate = useNavigate();
  const { gameData, isWorldUnlocked, loadWorldData } = useGame();
  const [world, setWorld] = useState<any>(null);
  const [loading, setLoading] = useState(true);

  useEffect(() => {
    async function fetchWorld() {
      if (!worldId) return;
      
      try {
        const loadedWorld = await loadWorld(worldId);
        if (loadedWorld) {
          setWorld(loadedWorld);
          loadWorldData(worldId);
        } else {
          navigate('/worlds');
        }
      } catch (error) {
        console.error('Failed to load world:', error);
        navigate('/worlds');
      } finally {
        setLoading(false);
      }
    }
    
    fetchWorld();
  }, [worldId, loadWorldData, navigate]);

  if (loading) {
    return (
      <div className="flex items-center justify-center min-h-screen">
        <Spinner size="lg" />
      </div>
    );
  }

  if (!world) {
    return null;
  }

  const isUnlocked = isWorldUnlocked(world.id, world);
  const completedLevels = gameData?.progress.completedLevels || [];

  return (
    <div className="max-w-7xl mx-auto px-4 py-8">
      <div className="mb-6">
        <Button onClick={() => navigate('/worlds')} variant="secondary" className="mb-4">
          ← Back to Worlds
        </Button>
        <div className="flex items-center space-x-3 mb-4">
          <span className="text-4xl">{world.icon}</span>
          <div>
            <h1 className="text-3xl font-bold text-gray-900 dark:text-gray-100">{world.name}</h1>
            <p className="text-gray-600 dark:text-gray-300">{world.description}</p>
          </div>
        </div>
        {world.estimatedHours && (
          <p className="text-sm text-gray-500 dark:text-gray-400">Estimated time: {world.estimatedHours} hours</p>
        )}
      </div>

      {!isUnlocked ? (
        <div className="bg-gray-100 dark:bg-gray-800 rounded-lg p-8 text-center">
          <p className="text-gray-600 dark:text-gray-300 mb-4">This world is locked.</p>
          <p className="text-sm text-gray-500 dark:text-gray-400">
            Complete the previous worlds to unlock this one.
          </p>
        </div>
      ) : (
        <LevelList
          levels={world.levels}
          completedLevels={completedLevels}
          worldId={world.id}
        />
      )}
    </div>
  );
}

