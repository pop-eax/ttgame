import { useState, useEffect, useRef } from 'react';
import { useParams, useNavigate } from 'react-router-dom';
import { Level, World } from '../types/world';
import { ProofEditor } from '../components/level/ProofEditor';
import { ProofOutput } from '../components/level/ProofOutput';
import { TheoryPanel } from '../components/level/TheoryPanel';
import { HintsPanel } from '../components/level/HintsPanel';
import { TacticsAndTheoremsPanel } from '../components/level/TacticsAndTheoremsPanel';
import { SuccessModal } from '../components/level/SuccessModal';
import { Button } from '../components/common/Button';
import { useGame } from '../context/GameContext';
import { useTheme } from '../context/ThemeContext';
import { useProofExecution } from '../hooks/useProofExecution';
import { useJsCoq } from '../hooks/useJsCoq';
import { useJsCoqState } from '../hooks/useJsCoqState';
import toast from 'react-hot-toast';

const COQ_EDITOR_ID = 'coq-editor';

export function LevelPage() {
  const { worldId, levelId } = useParams<{ worldId: string; levelId: string }>();
  const navigate = useNavigate();
  const { completeLevel, saveProof, loadWorldData, gameData } = useGame();
  const { theme } = useTheme();
  const { execute: executeProof, proofState, isExecuting, clearState } = useProofExecution();
  const { executeProof: jsCoqExecuteProof, isLoaded: jsCoqLoaded, setEditorValue, getEditorValue, setInitialCode, coqManager } = useJsCoq(COQ_EDITOR_ID, theme);
  const { goalState, reset: resetJsCoqState } = useJsCoqState(coqManager, jsCoqLoaded);
  
  const [level, setLevel] = useState<Level | null>(null);
  const [world, setWorld] = useState<World | null>(null);
  const [hintsUsed, setHintsUsed] = useState(0);
  const [attempts, setAttempts] = useState(0);
  const [startTime] = useState(Date.now());
  const [showSuccess, setShowSuccess] = useState(false);
  const [showTheory, setShowTheory] = useState(true);
  const [isLevelComplete, setIsLevelComplete] = useState(false);
  const initializedLevelRef = useRef<string | null>(null);
  const goalStateRef = useRef<any>(null);

  useEffect(() => {
    async function fetchLevel() {
      if (!worldId || !levelId) return;
      
      try {
        const loadedWorld = await loadWorldData(worldId);
        if (!loadedWorld) {
          toast.error('World not found');
          navigate('/worlds');
          return;
        }
        
        setWorld(loadedWorld);
        
        const loadedLevel = loadedWorld.levels.find(l => l.id === levelId);
        if (loadedLevel) {
          setLevel(loadedLevel);
          
          // Check if level is already completed
          const isCompleted = gameData?.progress.completedLevels.includes(levelId) || false;
          setIsLevelComplete(isCompleted);
          
          // Set initial code in jsCoq editor when it's loaded
          // Will be handled by the useEffect that checks for saved proofs
        } else {
          toast.error('Level not found');
          navigate(`/worlds/${worldId}`);
        }
      } catch (error) {
        console.error('Failed to load level:', error);
        toast.error('Failed to load level');
        navigate('/worlds');
      }
    }
    
    fetchLevel();
  }, [worldId, levelId, loadWorldData, navigate]);

  // Update editor when jsCoq loads or level changes
  // Only initialize once per level to prevent resetting user's edits
  useEffect(() => {
    if (!level || !jsCoqLoaded || !setInitialCode || !coqManager) return;
    
    // Check if we've already initialized this level
    if (initializedLevelRef.current === level.id) {
      return;
    }
    
    // Mark this level as initialized
    initializedLevelRef.current = level.id;
    
    // Reset jsCoq state for new level
    resetJsCoqState();
    
    // Check if there's a saved proof for this completed level
    let codeToLoad = level.startingCode;
    if (gameData) {
      const savedProof = gameData.proofs[level.id];
      const isCompleted = gameData.progress.completedLevels.includes(level.id);
      
      // If level is completed and we have saved code, use that instead
      if (isCompleted && savedProof && savedProof.code) {
        codeToLoad = savedProof.code;
      }
    }
    
    // Set initial code - will be set when editor is available
    setInitialCode(codeToLoad);
  }, [level?.id, jsCoqLoaded, setInitialCode, setEditorValue, coqManager, resetJsCoqState, gameData]);

  const handleRunProof = async () => {
    if (!level) return;

    // If already complete, go to next level
    if (isLevelComplete) {
      handleNextLevel();
      return;
    }

    setAttempts(prev => prev + 1);
    clearState();

    try {
      const code = getEditorValue ? getEditorValue() : '';
      const result = await executeProof(code, level, jsCoqExecuteProof, jsCoqLoaded);

      // Also check goalState as a fallback - it's updated in real-time
      // Use ref to get the latest value (avoid stale closure)
      const currentGoalState = goalStateRef.current || goalState;
      const hasNoGoalsInState = !currentGoalState || 
                                 !currentGoalState.goals || 
                                 currentGoalState.goals.length === 0;
      
      console.log('🔍 Proof execution result:', {
        isComplete: result.isComplete,
        hasError: result.hasError,
        goalsCount: result.goals?.length || 0,
        goalStateGoalsCount: currentGoalState?.goals?.length || 0,
        hasNoGoalsInState,
        result
      });

      // Check if proof is complete: either result says so OR goalState has no goals
      const proofIsComplete = (result.isComplete && !result.hasError) || 
                              (hasNoGoalsInState && !result.hasError && result.goals?.length === 0);

      if (proofIsComplete) {
        const timeSpent = Math.floor((Date.now() - startTime) / 1000);
        const code = getEditorValue ? getEditorValue() : '';
        
        console.log('💾 Saving proof:', {
          levelId: level.id,
          codeLength: code.length,
          codePreview: code.substring(0, 100),
          timeSpent,
          hintsUsed,
          attempts
        });
        
        if (!code) {
          console.warn('⚠️ Warning: No code retrieved from editor!');
        }
        
        saveProof(level.id, {
          code,
          completedAt: new Date().toISOString(),
          timeSpent,
          hintsUsed,
          attempts,
          correct: true,
        });
        
        console.log('✅ Proof saved, checking localStorage...');
        // Verify it was saved
        setTimeout(() => {
          const savedData = localStorage.getItem('rocq_game_data');
          if (savedData) {
            const parsed = JSON.parse(savedData);
            const savedProof = parsed.proofs?.[level.id];
            console.log('📦 Saved proof in localStorage:', {
              hasProof: !!savedProof,
              codeLength: savedProof?.code?.length || 0,
              codePreview: savedProof?.code?.substring(0, 100) || 'N/A'
            });
          } else {
            console.error('❌ No data found in localStorage!');
          }
        }, 100);

        completeLevel(level.id);
        setIsLevelComplete(true);
        setShowSuccess(true);
        toast.success('Proof complete!');
        console.log('✅ Level marked as complete');
      } else if (result.hasError) {
        toast.error('Proof has errors - check the messages below');
      } else {
        // Not complete yet - show current state
        console.log('⚠️ Proof not complete:', {
          goals: result.goals?.length || 0,
          goalStateGoals: currentGoalState?.goals?.length || 0,
          isComplete: result.isComplete,
          hasError: result.hasError
        });
        toast.error(`Proof not complete. ${result.goals?.length || 0} goal(s) remaining.`);
      }
    } catch (error: any) {
      console.error('❌ Proof execution error:', error);
      toast.error(error.message || 'Failed to execute proof');
    }
  };

  const handleHintRequest = (hintNumber: number) => {
    setHintsUsed(Math.max(hintsUsed, hintNumber));
  };

  const handleNextLevel = () => {
    
    if (!world || !level) {
      console.warn('⚠️ Cannot navigate: missing world or level', { world: !!world, level: !!level });
      return;
    }
    
    const currentIndex = world.levels.findIndex((l: Level) => l.id === level.id);
    
    if (currentIndex >= 0 && currentIndex < world.levels.length - 1) {
      const nextLevel = world.levels[currentIndex + 1];
      navigate(`/worlds/${worldId}/levels/${nextLevel.id}`);
    } else {
      navigate(`/worlds/${worldId}`);
    }
  };

  if (!level) {
    return (
      <div className="flex items-center justify-center min-h-screen">
        <div className="text-gray-900 dark:text-gray-100">Loading...</div>
      </div>
    );
  }

  return (
    <div className="min-h-screen bg-gray-50 dark:bg-gray-900">
      <div className="bg-white dark:bg-gray-800 border-b dark:border-gray-700">
        <div className="mx-auto px-4 py-4">
          <div className="flex items-center justify-between mb-4">
            <Button onClick={() => navigate(`/worlds/${worldId}`)} variant="secondary">
              ← Back to World
            </Button>
            <div className="space-y-2">
            <div className="flex items-center justify-center space-x-3">
              <h1 className="text-2xl font-bold dark:text-gray-100">{level.name}</h1>
              <span className="text-gray-600 dark:text-gray-400">{'★'.repeat(level.difficulty)}{'☆'.repeat(5 - level.difficulty)}</span>
            </div>
            <p className="text-center text-gray-700 dark:text-gray-300 max-w-3xl mx-auto">{level.objective}</p>
          </div>
            <Button 
              onClick={handleRunProof} 
              disabled={isExecuting && !isLevelComplete}
            >
              {isExecuting && !isLevelComplete ? 'Running...' : isLevelComplete ? 'Next Level →' : 'Check Proof'}
            </Button>
          </div>
          
        </div>
      </div>

      <div className=" mx-auto px-4 py-6">
        <div className="grid grid-cols-1 lg:grid-cols-12 gap-6">
          {/* Left Column: Theory & Hints */}
          <div className="lg:col-span-3 space-y-6">
            <TheoryPanel 
              theory={level.theory}
              show={showTheory}
              onToggle={() => setShowTheory(!showTheory)}
            />
            <HintsPanel
              hints={level.hints}
              onHintRequest={handleHintRequest}
            />
          </div>

          {/* Middle Column: Proof Output & Editor - Takes most of the space */}
          <div className="lg:col-span-6 space-y-6">
            <ProofOutput
              state={goalState || proofState}
              isExecuting={isExecuting}
            />
            
            <ProofEditor
              containerId={COQ_EDITOR_ID}
              isLoaded={jsCoqLoaded}
            />
          </div>

          {/* Right Column: Tactics & Theorems */}
          <div className="lg:col-span-3">
            <TacticsAndTheoremsPanel
              unlockedTactics={gameData?.unlockedTactics || []}
              availableTheorems={world?.availableTheorems || []}
            />
          </div>
        </div>
      </div>

      {showSuccess && (
        <SuccessModal
          level={level}
          hintsUsed={hintsUsed}
          timeSpent={Math.floor((Date.now() - startTime) / 1000)}
          onNext={() => {
            navigate(`/worlds/${worldId}`);
          }}
        />
      )}
    </div>
  );
}

