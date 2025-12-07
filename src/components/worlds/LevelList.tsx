import { Link } from 'react-router-dom';
import { Level } from '../../types/world';
import { CheckCircle2, Lock, Play } from 'lucide-react';

interface LevelListProps {
  levels: Level[];
  completedLevels: string[];
  worldId: string;
}

export function LevelList({ levels, completedLevels, worldId }: LevelListProps) {
  const getDifficultyStars = (difficulty: number) => {
    return '★'.repeat(difficulty) + '☆'.repeat(5 - difficulty);
  };

  return (
    <div className="grid grid-cols-1 md:grid-cols-2 lg:grid-cols-3 gap-4">
      {levels.map((level, index) => {
        const isCompleted = completedLevels.includes(level.id);
        const isUnlocked = index === 0 || completedLevels.includes(levels[index - 1].id);

        return (
          <div
            key={level.id}
            className={`bg-white dark:bg-gray-800 rounded-lg p-4 border-2 ${
              isUnlocked
                ? 'border-gray-200 dark:border-gray-700 hover:border-primary-500 dark:hover:border-primary-400'
                : 'border-gray-300 dark:border-gray-600 opacity-60'
            } transition-colors`}
          >
            {isUnlocked ? (
              <Link to={`/worlds/${worldId}/levels/${level.id}`}>
                <div className="flex items-start justify-between mb-2">
                  <div>
                    <h4 className="font-semibold text-gray-900 dark:text-gray-100">{level.name}</h4>
                    <p className="text-xs text-gray-500 dark:text-gray-400 mt-1">{getDifficultyStars(level.difficulty)}</p>
                  </div>
                  {isCompleted ? (
                    <CheckCircle2 className="text-success-500 dark:text-success-400 flex-shrink-0" size={20} />
                  ) : (
                    <Play className="text-primary-500 dark:text-primary-400 flex-shrink-0" size={20} />
                  )}
                </div>
                <p className="text-sm text-gray-600 dark:text-gray-300 mb-2">{level.description}</p>
                {level.estimatedTime && (
                  <p className="text-xs text-gray-500 dark:text-gray-400">~{level.estimatedTime} min</p>
                )}
              </Link>
            ) : (
              <>
                <div className="flex items-start justify-between mb-2">
                  <div>
                    <h4 className="font-semibold text-gray-500 dark:text-gray-400">{level.name}</h4>
                    <p className="text-xs text-gray-400 dark:text-gray-500 mt-1">{getDifficultyStars(level.difficulty)}</p>
                  </div>
                  <Lock className="text-gray-400 dark:text-gray-500 flex-shrink-0" size={20} />
                </div>
                <p className="text-sm text-gray-400 dark:text-gray-500 mb-2">{level.description}</p>
              </>
            )}
          </div>
        );
      })}
    </div>
  );
}

