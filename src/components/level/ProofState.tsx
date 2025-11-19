import React from 'react';
import { ProofState as ProofStateType } from '../../types/proof';
import { AlertCircle, CheckCircle2, Info } from 'lucide-react';

interface ProofStateProps {
  state: ProofStateType;
}

export function ProofState({ state }: ProofStateProps) {
  if (state.isComplete && !state.hasError) {
    return (
      <div className="bg-success-50 border border-success-200 rounded-lg p-4">
        <div className="flex items-center space-x-2 text-success-700">
          <CheckCircle2 size={20} />
          <span className="font-semibold">Proof Complete!</span>
        </div>
      </div>
    );
  }

  return (
    <div className="bg-white rounded-lg border border-gray-200 p-4 space-y-4">
      {state.goals.length > 0 && (
        <div>
          <h4 className="font-semibold text-gray-900 mb-2">
            Goals ({state.goals.length})
          </h4>
          <div className="space-y-2">
            {state.goals.map((goal, idx) => (
              <div key={goal.id || idx} className="bg-gray-50 rounded p-3">
                <div className="text-sm font-mono text-gray-800">{goal.type}</div>
              </div>
            ))}
          </div>
        </div>
      )}

      {state.hypotheses.length > 0 && (
        <div>
          <h4 className="font-semibold text-gray-900 mb-2">Hypotheses</h4>
          <div className="space-y-1">
            {state.hypotheses.map((hyp, idx) => (
              <div key={idx} className="text-sm text-gray-600">
                <span className="font-semibold">{hyp.name}</span>
                <span className="text-gray-400"> : </span>
                <span className="font-mono">{hyp.type}</span>
              </div>
            ))}
          </div>
        </div>
      )}

      {state.messages.length > 0 && (
        <div>
          <h4 className="font-semibold text-gray-900 mb-2">Messages</h4>
          <div className="space-y-2">
            {state.messages.map((msg, idx) => (
              <div
                key={idx}
                className={`flex items-start space-x-2 p-2 rounded ${
                  msg.level === 'error'
                    ? 'bg-error-50 text-error-700'
                    : msg.level === 'warning'
                    ? 'bg-warning-50 text-warning-700'
                    : 'bg-blue-50 text-blue-700'
                }`}
              >
                {msg.level === 'error' ? (
                  <AlertCircle size={16} className="flex-shrink-0 mt-0.5" />
                ) : (
                  <Info size={16} className="flex-shrink-0 mt-0.5" />
                )}
                <span className="text-sm">{msg.text}</span>
              </div>
            ))}
          </div>
        </div>
      )}
    </div>
  );
}

