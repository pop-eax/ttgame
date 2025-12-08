import { useState } from 'react';
import { Lightbulb } from 'lucide-react';
import { Button } from '../common/Button';

interface HintsPanelProps {
  hints: [string, string, string];
  onHintRequest: (hintNumber: number) => void;
}

export function HintsPanel({ hints, onHintRequest }: HintsPanelProps) {
  const [revealedHints, setRevealedHints] = useState<number[]>([]);

  const revealHint = (hintNumber: number) => {
    if (!revealedHints.includes(hintNumber)) {
      setRevealedHints([...revealedHints, hintNumber]);
      onHintRequest(hintNumber);
    }
  };

  return (
    <div className="bg-white dark:bg-gray-800 rounded-lg border border-gray-200 dark:border-gray-700 p-4">
      <div className="flex items-center space-x-2 mb-4">
        <Lightbulb className="text-warning-500 dark:text-warning-400" size={20} />
        <h3 className="font-semibold text-gray-900 dark:text-gray-100">Hints</h3>
      </div>
      
      <div className="space-y-3">
        {hints.map((hint, idx) => {
          const hintNumber = idx + 1;
          const isRevealed = revealedHints.includes(hintNumber);
          
          return (
            <div key={idx} className="border border-gray-200 dark:border-gray-600 rounded p-3">
              <div className="flex items-center justify-between mb-2">
                <span className="text-sm font-semibold text-gray-700 dark:text-gray-300">
                  Hint {hintNumber}
                </span>
                {!isRevealed && (
                  <Button
                    size="sm"
                    variant="secondary"
                    onClick={() => revealHint(hintNumber)}
                  >
                    Reveal
                  </Button>
                )}
              </div>
              {isRevealed && (
                <p className="text-sm text-gray-600 dark:text-gray-300">{hint}</p>
              )}
            </div>
          );
        })}
      </div>
    </div>
  );
}

