import React from 'react';
import { Link } from 'react-router-dom';
import { useGame } from '../context/GameContext';
import { Button } from '../components/common/Button';

export function ProgressPage() {
  const { gameData } = useGame();

  if (!gameData) {
    return <div>Loading...</div>;
  }

  return (
    <div className="max-w-4xl mx-auto px-4 py-8">
      <h1 className="text-3xl font-bold text-gray-900 mb-6">Your Progress</h1>
      
      <div className="bg-white rounded-lg shadow-sm border border-gray-200 p-6 mb-6">
        <h2 className="text-xl font-semibold mb-4">Statistics</h2>
        <div className="grid grid-cols-2 md:grid-cols-4 gap-4">
          <div>
            <p className="text-sm text-gray-600">Level</p>
            <p className="text-2xl font-bold">{gameData.progress.level}</p>
          </div>
          <div>
            <p className="text-sm text-gray-600">XP</p>
            <p className="text-2xl font-bold">{gameData.progress.xp}</p>
          </div>
          <div>
            <p className="text-sm text-gray-600">Completed</p>
            <p className="text-2xl font-bold">{gameData.progress.completedLevels.length}</p>
          </div>
          <div>
            <p className="text-sm text-gray-600">Tactics</p>
            <p className="text-2xl font-bold">{gameData.unlockedTactics.length}</p>
          </div>
        </div>
      </div>

      <div className="bg-white rounded-lg shadow-sm border border-gray-200 p-6">
        <h2 className="text-xl font-semibold mb-4">Completed Levels</h2>
        {gameData.progress.completedLevels.length === 0 ? (
          <p className="text-gray-600">No levels completed yet. Start with the tutorial!</p>
        ) : (
          <ul className="space-y-2">
            {gameData.progress.completedLevels.map((levelId) => (
              <li key={levelId} className="text-gray-700">
                ✓ {levelId}
              </li>
            ))}
          </ul>
        )}
      </div>

      <div className="mt-6">
        <Link to="/">
          <Button>Back to Home</Button>
        </Link>
      </div>
    </div>
  );
}

