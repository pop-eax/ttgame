import { useState } from 'react';
import { ProofState } from '../types/proof';
import { Level } from '../types/world';

export function useProofExecution() {
  const [isExecuting, setIsExecuting] = useState(false);
  const [proofState, setProofState] = useState<ProofState | null>(null);

  // Note: executeProof and isLoaded should be passed from LevelPage
  // This hook just manages the execution state
  const execute = async (
    code: string, 
    level: Level,
    executeProof?: (code: string) => Promise<ProofState>,
    isLoaded?: boolean
  ): Promise<ProofState> => {
    if (!isLoaded || !executeProof) {
      throw new Error('jsCoq is not loaded yet');
    }

    setIsExecuting(true);
    try {
      const result = await executeProof(code);
      setProofState(result);
      return result;
    } finally {
      setIsExecuting(false);
    }
  };

  return {
    isExecuting,
    proofState,
    execute,
    clearState: () => setProofState(null),
  };
}

