import React from 'react';
import { Modal } from '../common/Modal';
import { Button } from '../common/Button';
import { CheckCircle2, Star } from 'lucide-react';
import { Level } from '../../types/world';
import { formatTime } from '../../utils/dateHelpers';

interface SuccessModalProps {
  level: Level;
  hintsUsed: number;
  timeSpent: number;
  onNext: () => void;
}

export function SuccessModal({ level, hintsUsed, timeSpent, onNext }: SuccessModalProps) {
  const xpGain = hintsUsed === 0 ? 150 : 100;
  const bonusXP = hintsUsed === 0 ? 50 : 0;
  const totalXP = xpGain + bonusXP;

  return (
    <Modal isOpen={true} onClose={onNext} title="Level Complete!">
      <div className="text-center space-y-4">
        <div className="flex justify-center">
          <CheckCircle2 className="text-success-500 dark:text-success-400" size={64} />
        </div>
        
        <h2 className="text-2xl font-bold text-gray-900 dark:text-gray-100">{level.name}</h2>
        
        <div className="bg-gray-50 dark:bg-gray-700/50 rounded-lg p-4 space-y-2">
          <div className="flex items-center justify-center space-x-2">
            <Star className="text-warning-500 dark:text-warning-400" size={20} />
            <span className="text-lg font-semibold dark:text-gray-100">+{totalXP} XP</span>
          </div>
          <div className="text-sm text-gray-600 dark:text-gray-300 space-y-1">
            <p>Time: {formatTime(timeSpent)}</p>
            <p>Hints used: {hintsUsed}</p>
            {bonusXP > 0 && <p className="text-success-600 dark:text-success-400">Bonus: +{bonusXP} XP (no hints!)</p>}
          </div>
        </div>

        <div className="pt-4">
          <Button onClick={onNext} size="lg">
            Continue
          </Button>
        </div>
      </div>
    </Modal>
  );
}

