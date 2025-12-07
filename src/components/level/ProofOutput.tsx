import React from 'react';
import { ProofState as ProofStateType } from '../../types/proof';
import { AlertCircle, CheckCircle2, Info, Target, List } from 'lucide-react';

interface ProofOutputProps {
  state: ProofStateType | null;
  isExecuting?: boolean;
}

// Format goal in jsCoq style
function formatGoal(goal: any, index: number, total: number): string {
  const goalType = goal.type || '';
  const context = goal.context || [];
  const goalCountText = goal.goalCountText || `Goal ${index + 1}`;
  
  let output = `${goalCountText}\n\n`;
  
  // Add hypotheses/context
  if (context.length > 0) {
    context.forEach((hyp: any) => {
      output += `${hyp.name} : ${hyp.type}\n`;
    });
    output += '\n';
    // Add separator line
    output += '========\n\n';
  }
  
  // Add goal counter
  output += `(${index + 1} / ${total})\n\n`;
  
  // Add goal type
  output += goalType;
  
  return output;
}

export function ProofOutput({ state, isExecuting }: ProofOutputProps) {
  return (
    <div className="bg-white dark:bg-gray-800 rounded-lg border border-gray-200 dark:border-gray-700">
      <div className="bg-gray-50 dark:bg-gray-700 px-4 py-2 border-b border-gray-200 dark:border-gray-600 flex items-center space-x-2">
        <Target size={16} className="text-gray-600 dark:text-gray-300" />
        <h3 className="text-sm font-semibold text-gray-700 dark:text-gray-200">Proof State</h3>
        {isExecuting && (
          <span className="ml-auto text-xs text-primary-600 dark:text-primary-400 animate-pulse">Executing...</span>
        )}
      </div>
      
      <div className="p-4 space-y-4 max-h-96 overflow-y-auto">
        {!state && (
          <div className="text-sm text-gray-500 dark:text-gray-400 italic text-center py-8">
            Start writing your proof to see the current state here
          </div>
        )}

        {state && (
          <>
            {state.isComplete && !state.hasError ? (
              <div className="bg-success-50 dark:bg-success-900/30 border border-success-200 dark:border-success-800 rounded-lg p-4">
                <div className="flex items-center space-x-2 text-success-700 dark:text-success-400">
                  <CheckCircle2 size={20} />
                  <span className="font-semibold">Proof Complete!</span>
                </div>
                <p className="text-sm text-success-600 dark:text-success-300 mt-2">
                  All goals have been proven. Great work!
                </p>
              </div>
            ) : (
              <>
                {state.goals.length > 0 && (
                  <div>
                    <div className="flex items-center space-x-2 mb-2">
                      <Target size={16} className="text-primary-600 dark:text-primary-400" />
                      <h4 className="font-semibold text-gray-900 dark:text-gray-100">
                        Goals ({state.goals.length})
                      </h4>
                    </div>
                    <div className="space-y-4">
                      {state.goals.map((goal, idx) => {
                        // Get hypotheses from goal context or fallback to state-level hypotheses
                        const goalHyps = goal.context && goal.context.length > 0 
                          ? goal.context 
                          : (state.hypotheses || []);
                        
                        return (
                          <div 
                            key={goal.id || idx} 
                            className="bg-gray-50 dark:bg-gray-700/50 border border-gray-200 dark:border-gray-600 rounded p-4"
                          >
                            <pre className="text-sm font-mono text-gray-800 dark:text-gray-200 whitespace-pre-wrap">
                              {formatGoal({ ...goal, context: goalHyps }, idx, state.goals.length)}
                            </pre>
                          </div>
                        );
                      })}
                    </div>
                  </div>
                )}
                
                {/* Show hypotheses separately if they exist but aren't in goals */}
                {state.hypotheses.length > 0 && state.goals.length > 0 && 
                 state.goals.every(g => !g.context || g.context.length === 0) && (
                  <div className="mt-4">
                    <div className="flex items-center space-x-2 mb-2">
                      <List size={16} className="text-gray-600 dark:text-gray-300" />
                      <h4 className="font-semibold text-gray-900 dark:text-gray-100">Hypotheses</h4>
                    </div>
                    <div className="bg-gray-50 dark:bg-gray-700/50 rounded p-3 space-y-1.5">
                      {state.hypotheses.map((hyp, idx) => (
                        <div key={idx} className="text-sm text-gray-700 dark:text-gray-300">
                          <span className="font-semibold text-primary-700 dark:text-primary-400">{hyp.name}</span>
                          <span className="text-gray-400 dark:text-gray-500"> : </span>
                          <span className="font-mono text-gray-800 dark:text-gray-200">{hyp.type}</span>
                        </div>
                      ))}
                    </div>
                  </div>
                )}

                {state.messages.length > 0 && (
                  <div className="mt-4">
                    <div className="flex items-center space-x-2 mb-2">
                      <Info size={16} className="text-gray-600 dark:text-gray-300" />
                      <h4 className="font-semibold text-gray-900 dark:text-gray-100">Messages</h4>
                    </div>
                    <div className="space-y-2">
                      {state.messages.map((msg, idx) => (
                        <div
                          key={idx}
                          className={`flex items-start space-x-2 p-3 rounded ${
                            msg.level === 'error'
                              ? 'bg-error-50 dark:bg-error-900/30 border border-error-200 dark:border-error-800 text-error-700 dark:text-error-300'
                              : msg.level === 'warning'
                              ? 'bg-warning-50 dark:bg-warning-900/30 border border-warning-200 dark:border-warning-800 text-warning-700 dark:text-warning-300'
                              : 'bg-blue-50 dark:bg-blue-900/30 border border-blue-200 dark:border-blue-800 text-blue-700 dark:text-blue-300'
                          }`}
                        >
                          {msg.level === 'error' ? (
                            <AlertCircle size={16} className="flex-shrink-0 mt-0.5" />
                          ) : (
                            <Info size={16} className="flex-shrink-0 mt-0.5" />
                          )}
                          <div className="flex-1">
                            <pre className="text-sm whitespace-pre-wrap font-mono">{msg.text}</pre>
                            {msg.location && (
                              <div className="text-xs mt-1 opacity-75">
                                Line {msg.location.line}, Column {msg.location.column}
                              </div>
                            )}
                          </div>
                        </div>
                      ))}
                    </div>
                  </div>
                )}

                {state.hypotheses.length > 0 && state.goals.length === 0 && (
                  <div>
                    <div className="flex items-center space-x-2 mb-2">
                      <List size={16} className="text-gray-600 dark:text-gray-300" />
                      <h4 className="font-semibold text-gray-900 dark:text-gray-100">Hypotheses</h4>
                    </div>
                    <div className="bg-gray-50 dark:bg-gray-700/50 rounded p-3 space-y-1.5">
                      {state.hypotheses.map((hyp, idx) => (
                        <div key={idx} className="text-sm text-gray-700 dark:text-gray-300">
                          <span className="font-semibold text-primary-700 dark:text-primary-400">{hyp.name}</span>
                          <span className="text-gray-400 dark:text-gray-500"> : </span>
                          <span className="font-mono text-gray-800 dark:text-gray-200">{hyp.type}</span>
                        </div>
                      ))}
                    </div>
                  </div>
                )}

                {state.goals.length === 0 && state.hypotheses.length === 0 && !state.hasError && (
                  <div className="text-sm text-gray-500 dark:text-gray-400 italic">
                    No active goals. The proof may be complete or waiting for input.
                  </div>
                )}
              </>
            )}

            {state.messages.length > 0 && (
              <div>
                <div className="flex items-center space-x-2 mb-2">
                  <Info size={16} className="text-gray-600 dark:text-gray-300" />
                  <h4 className="font-semibold text-gray-900 dark:text-gray-100">Messages</h4>
                </div>
                <div className="space-y-2">
                  {state.messages.map((msg, idx) => (
                    <div
                      key={idx}
                      className={`flex items-start space-x-2 p-3 rounded ${
                        msg.level === 'error'
                          ? 'bg-error-50 dark:bg-error-900/30 border border-error-200 dark:border-error-800 text-error-700 dark:text-error-300'
                          : msg.level === 'warning'
                          ? 'bg-warning-50 dark:bg-warning-900/30 border border-warning-200 dark:border-warning-800 text-warning-700 dark:text-warning-300'
                          : 'bg-blue-50 dark:bg-blue-900/30 border border-blue-200 dark:border-blue-800 text-blue-700 dark:text-blue-300'
                      }`}
                    >
                      {msg.level === 'error' ? (
                        <AlertCircle size={16} className="flex-shrink-0 mt-0.5" />
                      ) : (
                        <Info size={16} className="flex-shrink-0 mt-0.5" />
                      )}
                      <div className="flex-1">
                        <pre className="text-sm whitespace-pre-wrap font-mono">{msg.text}</pre>
                        {msg.location && (
                          <div className="text-xs mt-1 opacity-75">
                            Line {msg.location.line}, Column {msg.location.column}
                          </div>
                        )}
                      </div>
                    </div>
                  ))}
                </div>
              </div>
            )}
          </>
        )}
      </div>
    </div>
  );
}
