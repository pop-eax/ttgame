import React, { useEffect, useRef } from 'react';

interface ProofEditorProps {
  containerId: string;
  initialValue?: string;
  onContentChange?: (value: string) => void;
  onCursorChange?: (line: number, code: string) => void;
  isLoaded?: boolean;
}

export function ProofEditor({ 
  containerId, 
  initialValue = '',
  onContentChange,
  onCursorChange,
  isLoaded = true 
}: ProofEditorProps) {
  const containerRef = useRef<HTMLDivElement | null>(null);

  useEffect(() => {
    // Ensure the container has the correct ID
    if (containerRef.current) {
      containerRef.current.id = containerId;
    }
  }, [containerId]);

  return (
    <div className="bg-white dark:bg-gray-800 rounded-lg border border-gray-200 dark:border-gray-700">
      <div className="bg-gray-50 dark:bg-gray-700 px-4 py-2 border-b border-gray-200 dark:border-gray-600">
        <h3 className="text-sm font-semibold text-gray-700 dark:text-gray-200">Proof Editor</h3>
      </div>
      {/* jsCoq will create its own UI here with editor and goal panel */}
      {/* Don't use overflow-hidden as it might hide jsCoq's goal panel */}
      <div 
        ref={containerRef}
        id={containerId}
        className="w-full"
        style={{ minHeight: '600px' }}
      >
        {!isLoaded && (
          <div className="flex items-center justify-center" style={{ minHeight: '600px' }}>
            <div className="text-gray-500 dark:text-gray-400">Loading jsCoq editor...</div>
          </div>
        )}
      </div>
    </div>
  );
}
