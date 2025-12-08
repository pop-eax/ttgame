import { Link } from 'react-router-dom';
import { World } from '../../types/world';
import { Lock, CheckCircle2 } from 'lucide-react';

interface WorldCardProps {
  world: World;
  isUnlocked: boolean;
  completedCount: number;
  totalCount: number;
}

export function WorldCard({ world, isUnlocked, completedCount, totalCount }: WorldCardProps) {
  const progress = totalCount > 0 ? (completedCount / totalCount) * 100 : 0;

  if (!isUnlocked) {
    return (
      <div className="bg-gray-100 dark:bg-gray-800 rounded-lg p-6 border-2 border-gray-300 dark:border-gray-600 opacity-60">
        <div className="flex items-center justify-between mb-2">
          <div className="flex items-center space-x-2">
            <span className="text-3xl">{world.icon || '🔒'}</span>
            <h3 className="text-xl font-bold text-gray-500 dark:text-gray-400">{world.name}</h3>
          </div>
          <Lock className="text-gray-400 dark:text-gray-500" size={24} />
        </div>
        <p className="text-gray-500 dark:text-gray-400 text-sm mb-2">{world.description}</p>
        <div className="text-gray-400 dark:text-gray-500 text-sm">Locked - Complete previous worlds to unlock</div>
      </div>
    );
  }

  return (
    <Link
      to={`/worlds/${world.id}`}
      className="block bg-white dark:bg-gray-800 rounded-lg p-6 border-2 border-gray-200 dark:border-gray-700 hover:border-primary-500 dark:hover:border-primary-400 transition-colors shadow-sm hover:shadow-md"
    >
      <div className="flex items-center justify-between mb-2">
        <div className="flex items-center space-x-2">
          <span className="text-3xl">{world.icon || '🌍'}</span>
          <h3 className="text-xl font-bold text-gray-900 dark:text-gray-100">{world.name}</h3>
        </div>
        {completedCount === totalCount && totalCount > 0 && (
          <CheckCircle2 className="text-success-500 dark:text-success-400" size={24} />
        )}
      </div>
      <p className="text-gray-600 dark:text-gray-300 text-sm mb-4">{world.description}</p>
      <div className="space-y-2">
        <div className="flex items-center justify-between text-sm">
          <span className="text-gray-600 dark:text-gray-300">
            {completedCount} / {totalCount} levels
          </span>
          <span className="text-gray-500 dark:text-gray-400">{Math.round(progress)}%</span>
        </div>
        <div className="w-full bg-gray-200 dark:bg-gray-700 rounded-full h-2">
          <div
            className="bg-primary-500 dark:bg-primary-400 h-2 rounded-full transition-all"
            style={{ width: `${progress}%` }}
          />
        </div>
      </div>
    </Link>
  );
}

