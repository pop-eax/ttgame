import React from 'react';
import ReactMarkdown from 'react-markdown';
import { ChevronDown, ChevronUp } from 'lucide-react';
import { Theory } from '../../types/world';

interface TheoryPanelProps {
  theory?: Theory;
  show: boolean;
  onToggle: () => void;
}

export function TheoryPanel({ theory, show, onToggle }: TheoryPanelProps) {
  return (
    <div className="bg-white dark:bg-gray-800 rounded-lg border border-gray-200 dark:border-gray-700">
      <button
        onClick={onToggle}
        className="w-full flex items-center justify-between p-4 hover:bg-gray-50 dark:hover:bg-gray-700 transition-colors"
      >
        <h3 className="font-semibold text-gray-900 dark:text-gray-100">Theory</h3>
        {show ? <ChevronUp size={20} className="text-gray-600 dark:text-gray-300" /> : <ChevronDown size={20} className="text-gray-600 dark:text-gray-300" />}
      </button>
      
      {show && theory && (
        <div className="p-4 border-t border-gray-200 dark:border-gray-700">
          <div className="prose prose-sm max-w-none dark:prose-invert">
            <ReactMarkdown>{theory.markdown}</ReactMarkdown>
          </div>
          
          {theory.examples && theory.examples.length > 0 && (
            <div className="mt-4 space-y-3">
              {theory.examples.map((example, idx) => (
                <div key={idx} className="bg-gray-50 dark:bg-gray-700/50 rounded p-3">
                  <h5 className="font-semibold text-sm text-gray-900 dark:text-gray-100 mb-2">
                    {example.title}
                  </h5>
                  <pre className="text-xs font-mono text-gray-800 dark:text-gray-200 overflow-x-auto">
                    <code>{example.code}</code>
                  </pre>
                </div>
              ))}
            </div>
          )}
        </div>
      )}
      
      {show && !theory && (
        <div className="p-4 border-t border-gray-200 dark:border-gray-700">
          <p className="text-sm text-gray-500 dark:text-gray-400 italic">No theory content available for this level.</p>
        </div>
      )}
    </div>
  );
}

