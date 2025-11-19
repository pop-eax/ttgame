import { Level } from '../types/world';
import { ProofState } from '../types/proof';

// Mock proof validator - will be replaced with real jsCoq integration
export async function validateProof(code: string, level: Level): Promise<ProofState> {
  // For MVP: Simple string comparison with solution
  // In production, this will use jsCoq to actually verify the proof
  
  // Normalize code: remove comments, extra whitespace
  const normalize = (str: string) => {
    return str
      .replace(/\(\*[\s\S]*?\*\)/g, '') // Remove comments
      .replace(/\s+/g, ' ')
      .trim()
      .toLowerCase();
  };
  
  const normalizedCode = normalize(code);
  const normalizedSolution = normalize(level.solution);
  
  // Check if code contains the solution (allowing for extra code)
  const solutions = [
    normalizedSolution,
    ...(level.alternativeSolutions || []).map(s => normalize(s))
  ];
  
  // Check if any solution is contained in the code
  const matches = solutions.some(sol => {
    // Remove all whitespace for comparison
    const codeNoSpace = normalizedCode.replace(/\s/g, '');
    const solNoSpace = sol.replace(/\s/g, '');
    return codeNoSpace.includes(solNoSpace) || solNoSpace.includes(codeNoSpace);
  });
  
  if (matches) {
    return {
      goals: [],
      hypotheses: [],
      messages: [],
      isComplete: true,
      hasError: false,
    };
  }
  
  // Check for common mistakes
  if (level.commonMistakes) {
    for (const mistake of level.commonMistakes) {
      if (code.toLowerCase().includes(mistake.pattern.toLowerCase())) {
        return {
          goals: [],
          hypotheses: [],
          messages: [{
            level: 'error',
            text: mistake.explanation,
          }],
          isComplete: false,
          hasError: true,
        };
      }
    }
  }
  
  // Try to parse the proof and show intermediate state
  const proofLines = code.split('\n').map(l => l.trim()).filter(l => l && !l.startsWith('(*'));
  const hypotheses: Array<{ name: string; type: string }> = [];
  let currentGoal = level.objective;
  
  // Simple parsing to extract hypotheses and track goal changes
  for (const line of proofLines) {
    const lowerLine = line.toLowerCase();
    
    // Check for intro/intros
    if (lowerLine.startsWith('intro') || lowerLine.startsWith('intros')) {
      const match = line.match(/intro(?:s)?\s+(\w+)/i);
      if (match) {
        const varName = match[1];
        // Try to infer type from context
        if (currentGoal.includes('->')) {
          const parts = currentGoal.split('->');
          if (parts.length > 1) {
            hypotheses.push({
              name: varName,
              type: parts[0].trim(),
            });
            currentGoal = parts.slice(1).join('->').trim();
          }
        } else {
          hypotheses.push({
            name: varName,
            type: 'Prop',
          });
        }
      }
    }
    
    // Check for split (product types)
    if (lowerLine.includes('split')) {
      // Split creates two goals - show the first one
      if (currentGoal.includes('*')) {
        const parts = currentGoal.split('*');
        if (parts.length === 2) {
          currentGoal = parts[0].trim();
        }
      }
    }
    
    // Check for exact
    if (lowerLine.includes('exact')) {
      const match = line.match(/exact\s+(.+?)\./i);
      if (match) {
        const term = match[1].trim();
        // If exact matches a hypothesis, goal might be solved
        if (hypotheses.some(h => h.name === term)) {
          currentGoal = '';
        }
      }
    }
  }
  
  // If we have Qed and no goal, it's complete
  const hasQed = proofLines.some(l => l.toLowerCase().includes('qed'));
  const isComplete = hasQed && !currentGoal;
  
  return {
    goals: currentGoal ? [{ 
      id: '1', 
      type: currentGoal, 
      context: hypotheses 
    }] : [],
    hypotheses,
    messages: currentGoal && !isComplete ? [{
      level: 'info',
      text: 'Continue building your proof. The goal above shows what remains to be proven.',
    }] : [],
    isComplete,
    hasError: false,
  };
}

