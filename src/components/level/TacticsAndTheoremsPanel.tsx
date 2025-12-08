import { useState } from 'react';
import { Zap, BookOpen, X } from 'lucide-react';

interface TacticsAndTheoremsPanelProps {
  unlockedTactics: string[]; // User's unlocked tactics
  availableTheorems?: string[]; // Theorems available in this world's context
}

interface TheoremModalProps {
  isOpen: boolean;
  onClose: () => void;
  theorem: string;
}

function TheoremModal({ isOpen, onClose, theorem }: TheoremModalProps) {
  if (!isOpen) return null;

  // Parse theorem string to extract name and type
  // Format is usually: "name : type" or "name : forall ..."
  const parts = theorem.split(' : ');
  const theoremName = parts[0] || theorem;
  const theoremType = parts.slice(1).join(' : ');

  // Generate a simple example based on the theorem
  const generateExample = (name: string, type: string): string => {
    // Simple example generation
    if (type.includes('->')) {
      return `Example: Use ${name} to apply this theorem in your proof.\n\nrewrite ${name}.\n(* or *)\napply ${name}.`;
    } else if (type.includes('=')) {
      return `Example: Use ${name} to rewrite equalities.\n\nrewrite ${name}.\n(* or *)\nrewrite <- ${name}.`;
    } else {
      return `Example: Use ${name} in your proof.\n\napply ${name}.\n(* or *)\nrewrite ${name}.`;
    }
  };

  const example = generateExample(theoremName, theoremType);

  return (
    <div className="fixed inset-0 z-50 flex items-center justify-center bg-black bg-opacity-50" onClick={onClose}>
      <div 
        className="bg-white dark:bg-gray-800 rounded-lg shadow-xl max-w-2xl w-full mx-4 max-h-[90vh] overflow-hidden flex flex-col"
        onClick={(e) => e.stopPropagation()}
      >
        <div className="flex items-center justify-between p-4 border-b border-gray-200 dark:border-gray-700">
          <div className="flex items-center space-x-2">
            <BookOpen className="text-success-600 dark:text-success-400" size={20} />
            <h2 className="text-lg font-semibold text-gray-900 dark:text-gray-100">Theorem Details</h2>
          </div>
          <button
            onClick={onClose}
            className="text-gray-400 hover:text-gray-600 dark:text-gray-500 dark:hover:text-gray-300 transition-colors"
          >
            <X size={20} />
          </button>
        </div>
        
        <div className="p-6 overflow-y-auto flex-1">
          <div className="space-y-4">
            {/* Theorem Name */}
            <div>
              <h3 className="text-sm font-semibold text-gray-700 dark:text-gray-300 mb-2">Theorem Name</h3>
              <code className="text-sm font-mono text-gray-900 dark:text-gray-100 bg-gray-50 dark:bg-gray-700 p-2 rounded block">
                {theoremName}
              </code>
            </div>

            {/* Theorem Type/Description */}
            <div>
              <h3 className="text-sm font-semibold text-gray-700 dark:text-gray-300 mb-2">Type / Description</h3>
              <div className="bg-gray-50 dark:bg-gray-700 p-3 rounded">
                <code className="text-sm font-mono text-gray-900 dark:text-gray-100 whitespace-pre-wrap break-words">
                  {theoremType || theorem}
                </code>
              </div>
            </div>

            {/* Example */}
            <div>
              <h3 className="text-sm font-semibold text-gray-700 dark:text-gray-300 mb-2">Example Usage</h3>
              <div className="bg-success-50 dark:bg-success-900/30 border border-success-200 dark:border-success-800 p-3 rounded">
                <pre className="text-xs font-mono text-success-900 dark:text-success-200 whitespace-pre-wrap">
                  {example}
                </pre>
              </div>
            </div>
          </div>
        </div>

        <div className="p-4 border-t border-gray-200 dark:border-gray-700 flex justify-end">
          <button
            onClick={onClose}
            className="px-4 py-2 bg-primary-600 dark:bg-primary-500 text-white rounded hover:bg-primary-700 dark:hover:bg-primary-600 transition-colors"
          >
            Close
          </button>
        </div>
      </div>
    </div>
  );
}

export function TacticsAndTheoremsPanel({ 
  unlockedTactics, 
  availableTheorems = [] 
}: TacticsAndTheoremsPanelProps) {
  const [selectedTheorem, setSelectedTheorem] = useState<string | null>(null);

  // Extract theorem name for display (first part before ':')
  const getTheoremDisplayName = (theorem: string): string => {
    const parts = theorem.split(' : ');
    return parts[0] || theorem;
  };

  return (
    <>
      <div className="space-y-6">
        {/* Tactics Section */}
        <div className="bg-white dark:bg-gray-800 rounded-lg border border-gray-200 dark:border-gray-700">
          <div className="flex items-center space-x-2 p-4 border-b border-gray-200 dark:border-gray-700">
            <Zap className="text-primary-600 dark:text-primary-400" size={20} />
            <h3 className="font-semibold text-gray-900 dark:text-gray-100">Tactics Unlocked</h3>
          </div>
          <div className="p-4">
            {unlockedTactics.length === 0 ? (
              <p className="text-sm text-gray-500 dark:text-gray-400 italic">
                No tactics unlocked yet. Complete levels to unlock new tactics!
              </p>
            ) : (
            <div className="grid grid-cols-2 md:grid-cols-3 lg:grid-cols-3 gap-2">
              {unlockedTactics.map((tactic, idx) => (
                <div
                  key={idx}
                  className="bg-primary-50 dark:bg-primary-900/30 border border-primary-200 dark:border-primary-800 rounded p-1.5 text-center"
                >
                  <code className="text-[10px] font-mono text-primary-900 dark:text-primary-200 break-words leading-tight">{tactic}</code>
                </div>
              ))}
            </div>
            )}
          </div>
        </div>

        {/* Theorems Section */}
        <div className="bg-white dark:bg-gray-800 rounded-lg border border-gray-200 dark:border-gray-700">
          <div className="flex items-center space-x-2 p-4 border-b border-gray-200 dark:border-gray-700">
            <BookOpen className="text-success-600 dark:text-success-400" size={20} />
            <h3 className="font-semibold text-gray-900 dark:text-gray-100">Theorems Available</h3>
          </div>
          <div className="p-4">
            {availableTheorems.length === 0 ? (
              <p className="text-sm text-gray-500 dark:text-gray-400 italic">
                No theorems available in this world's context.
              </p>
            ) : (
              <div className="grid grid-cols-2 md:grid-cols-3 lg:grid-cols-3 gap-2">
                {availableTheorems.map((theorem, idx) => (
                  <button
                    key={idx}
                    onClick={() => setSelectedTheorem(theorem)}
                    className="bg-success-50 dark:bg-success-900/30 border border-success-200 dark:border-success-800 rounded p-1.5 text-center hover:bg-success-100 dark:hover:bg-success-900/50 hover:border-success-300 dark:hover:border-success-700 transition-colors cursor-pointer"
                  >
                    <code className="text-[10px] font-mono text-success-900 dark:text-success-200 break-words leading-tight">
                      {getTheoremDisplayName(theorem)}
                    </code>
                  </button>
                ))}
              </div>
            )}
          </div>
        </div>
      </div>

      <TheoremModal
        isOpen={selectedTheorem !== null}
        onClose={() => setSelectedTheorem(null)}
        theorem={selectedTheorem || ''}
      />
    </>
  );
}

