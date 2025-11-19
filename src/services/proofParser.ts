import { Level } from '../types/world';
import { ProofState } from '../types/proof';

/**
 * Parse proof code up to a specific line and return the current proof state
 */
export function parseProofToLine(code: string, level: Level, lineNumber?: number): ProofState {
  // If lineNumber is provided, only parse up to that line
  const lines = code.split('\n');
  const codeToParse = lineNumber !== undefined 
    ? lines.slice(0, lineNumber).join('\n')
    : code;
  
  const proofLines = codeToParse
    .split('\n')
    .map(l => l.trim())
    .filter(l => l && !l.startsWith('(*'));
  
  const hypotheses: Array<{ name: string; type: string }> = [];
  let currentGoal = level.objective;
  const messages: Array<{ level: 'info' | 'warning' | 'error'; text: string }> = [];
  
  // Try to extract goal from theorem statement if objective is not specific
  for (const line of proofLines) {
    const theoremMatch = line.match(/theorem\s+\w+\s*:\s*(.+?)\./i);
    if (theoremMatch) {
      currentGoal = theoremMatch[1].trim();
      break;
    }
  }
  
  // Track if we're inside a Proof block
  let inProof = false;
  let hasQed = false;
  
  for (let i = 0; i < proofLines.length; i++) {
    const line = proofLines[i];
    const lowerLine = line.toLowerCase();
    
    // Check if we've entered Proof block
    if (lowerLine.includes('proof')) {
      inProof = true;
      continue;
    }
    
    // Check for Qed
    if (lowerLine.includes('qed')) {
      hasQed = true;
      if (!currentGoal) {
        return {
          goals: [],
          hypotheses,
          messages: [],
          isComplete: true,
          hasError: false,
        };
      }
    }
    
    if (!inProof) continue;
    
    // Check for intro/intros
    if (lowerLine.startsWith('intro') || lowerLine.startsWith('intros')) {
      const match = line.match(/intro(?:s)?\s+(\w+)/i);
      if (match) {
        const varName = match[1];
        // Try to infer type from current goal
        if (currentGoal.includes('->')) {
          const parts = currentGoal.split('->');
          if (parts.length > 1) {
            hypotheses.push({
              name: varName,
              type: parts[0].trim(),
            });
            currentGoal = parts.slice(1).join('->').trim();
            messages.push({
              level: 'info',
              text: `Introduced hypothesis ${varName} : ${parts[0].trim()}`,
            });
          }
        } else if (currentGoal.includes('forall')) {
          // Parse forall quantifier
          const forallMatch = currentGoal.match(/forall\s+(\w+)\s*:\s*([^,]+)/i);
          if (forallMatch) {
            hypotheses.push({
              name: varName,
              type: forallMatch[2].trim(),
            });
            currentGoal = currentGoal.replace(/forall\s+\w+\s*:\s*[^,]+,\s*/i, '').trim();
            messages.push({
              level: 'info',
              text: `Introduced variable ${varName} : ${forallMatch[2].trim()}`,
            });
          }
        } else {
          hypotheses.push({
            name: varName,
            type: 'Prop',
          });
          messages.push({
            level: 'info',
            text: `Introduced hypothesis ${varName}`,
          });
        }
      }
    }
    
    // Check for split (product types)
    if (lowerLine.includes('split') && !lowerLine.includes('split.')) {
      // Check if line ends with split
      if (lowerLine.trim().endsWith('split') || lowerLine.trim().endsWith('split.')) {
        if (currentGoal.includes('*')) {
          const parts = currentGoal.split('*');
          if (parts.length === 2) {
            messages.push({
              level: 'info',
              text: `Split goal into two subgoals. Current goal: ${parts[0].trim()}`,
            });
            currentGoal = parts[0].trim();
          }
        } else if (currentGoal.includes('/\\')) {
          const parts = currentGoal.split('/\\');
          if (parts.length === 2) {
            messages.push({
              level: 'info',
              text: `Split conjunction. Current goal: ${parts[0].trim()}`,
            });
            currentGoal = parts[0].trim();
          }
        }
      }
    }
    
    // Also check for standalone split.
    if (lowerLine.trim() === 'split.' || lowerLine.trim() === 'split') {
      if (currentGoal.includes('*')) {
        const parts = currentGoal.split('*');
        if (parts.length === 2) {
          messages.push({
            level: 'info',
            text: `Split goal into two subgoals.`,
          });
          // Show first subgoal
          currentGoal = parts[0].trim();
        }
      } else if (currentGoal.includes('/\\')) {
        const parts = currentGoal.split('/\\');
        if (parts.length === 2) {
          messages.push({
            level: 'info',
            text: `Split conjunction.`,
          });
          currentGoal = parts[0].trim();
        }
      }
    }
    
    // Check for exact
    if (lowerLine.includes('exact')) {
      const match = line.match(/exact\s+(.+?)\./i);
      if (match) {
        const term = match[1].trim();
        // Check if it matches a hypothesis
        const matchingHyp = hypotheses.find(h => h.name === term);
        if (matchingHyp) {
          messages.push({
            level: 'info',
            text: `Using hypothesis ${term} to solve the goal`,
          });
          currentGoal = '';
        } else {
          messages.push({
            level: 'info',
            text: `Providing term ${term} directly`,
          });
          // If we have Qed after this, assume it's complete
          if (hasQed) {
            currentGoal = '';
          }
        }
      }
    }
    
    // Check for destruct
    if (lowerLine.includes('destruct')) {
      const match = line.match(/destruct\s+(\w+)/i);
      if (match) {
        const varName = match[1];
        messages.push({
          level: 'info',
          text: `Destructing ${varName} into cases`,
        });
      }
    }
  }
  
  // If we have Qed and no goal, it's complete
  const isComplete = hasQed && !currentGoal;
  
  return {
    goals: currentGoal ? [{ 
      id: '1', 
      type: currentGoal, 
      context: hypotheses 
    }] : [],
    hypotheses,
    messages: messages.length > 0 ? messages : (currentGoal && !isComplete ? [{
      level: 'info',
      text: 'Continue building your proof. The goal above shows what remains to be proven.',
    }] : []),
    isComplete,
    hasError: false,
  };
}

