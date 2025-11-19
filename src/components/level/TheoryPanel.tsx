import React from 'react';
import ReactMarkdown from 'react-markdown';
import { ChevronDown, ChevronUp } from 'lucide-react';
import { Theory } from '../../types/world';

interface TheoryPanelProps {
  theory?: Theory;
  objective: string;
  show: boolean;
  onToggle: () => void;
}

export function TheoryPanel({ theory, objective, show, onToggle }: TheoryPanelProps) {
  return (
    <div className="bg-white rounded-lg border border-gray-200">
      <button
        onClick={onToggle}
        className="w-full flex items-center justify-between p-4 hover:bg-gray-50 transition-colors"
      >
        <h3 className="font-semibold text-gray-900">Theory & Objective</h3>
        {show ? <ChevronUp size={20} /> : <ChevronDown size={20} />}
      </button>
      
      {show && (
        <div className="p-4 border-t border-gray-200 space-y-4">
          <div>
            <h4 className="font-semibold text-gray-900 mb-2">Objective</h4>
            <p className="text-gray-700">{objective}</p>
          </div>
          
          {theory && (
            <div>
              <h4 className="font-semibold text-gray-900 mb-2">Theory</h4>
              <div className="prose prose-sm max-w-none">
                <ReactMarkdown>{theory.markdown}</ReactMarkdown>
              </div>
              
              {theory.examples && theory.examples.length > 0 && (
                <div className="mt-4 space-y-3">
                  {theory.examples.map((example, idx) => (
                    <div key={idx} className="bg-gray-50 rounded p-3">
                      <h5 className="font-semibold text-sm text-gray-900 mb-2">
                        {example.title}
                      </h5>
                      <pre className="text-xs font-mono text-gray-800 overflow-x-auto">
                        <code>{example.code}</code>
                      </pre>
                    </div>
                  ))}
                </div>
              )}
            </div>
          )}
        </div>
      )}
    </div>
  );
}

