import React from 'react';
import { Link } from 'react-router-dom';
import { Button } from '../components/common/Button';
import { useGame } from '../context/GameContext';

export function HomePage() {
  const { gameData } = useGame();

  return (
    <div className="max-w-4xl mx-auto px-4 py-12">
      <div className="text-center mb-12">
        <h1 className="text-4xl font-bold text-gray-900 dark:text-gray-100 mb-4">
          Welcome to Rocq Type Theory Game
        </h1>
        <p className="text-xl text-gray-600 dark:text-gray-300 mb-8">
          Learn type theory through interactive proofs
        </p>
        {gameData && (
          <div className="bg-white dark:bg-gray-800 rounded-lg p-6 shadow-sm border border-gray-200 dark:border-gray-700 inline-block">
            <p className="text-gray-600 dark:text-gray-300 mb-2">
              Level {gameData.progress.level} | {gameData.progress.xp} XP
            </p>
            <p className="text-sm text-gray-500 dark:text-gray-400">
              {gameData.progress.completedLevels.length} levels completed
            </p>
          </div>
        )}
      </div>

      <div className="flex justify-center space-x-4">
        <Link to="/worlds">
          <Button size="lg">
            {gameData && gameData.progress.completedLevels.length > 0
              ? 'Continue Learning'
              : 'Start Learning'}
          </Button>
        </Link>
      </div>

      <div className="mt-12 grid grid-cols-1 md:grid-cols-3 gap-6">
        <div className="bg-white dark:bg-gray-800 rounded-lg p-6 shadow-sm border border-gray-200 dark:border-gray-700">
          <h3 className="text-lg font-semibold mb-2 dark:text-gray-100">Interactive Learning</h3>
          <p className="text-gray-600 dark:text-gray-300 text-sm">
            Learn type theory through hands-on proof writing with immediate feedback.
          </p>
        </div>
        <div className="bg-white dark:bg-gray-800 rounded-lg p-6 shadow-sm border border-gray-200 dark:border-gray-700">
          <h3 className="text-lg font-semibold mb-2 dark:text-gray-100">Progressive Difficulty</h3>
          <p className="text-gray-600 dark:text-gray-300 text-sm">
            Start with basics and gradually build up to advanced concepts.
          </p>
        </div>
        <div className="bg-white dark:bg-gray-800 rounded-lg p-6 shadow-sm border border-gray-200 dark:border-gray-700">
          <h3 className="text-lg font-semibold mb-2 dark:text-gray-100">Gamified Experience</h3>
          <p className="text-gray-600 dark:text-gray-300 text-sm">
            Earn XP, unlock achievements, and track your progress.
          </p>
        </div>
      </div>
    </div>
  );
}

