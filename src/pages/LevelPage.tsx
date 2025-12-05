import { useState, useEffect, useRef, startTransition } from 'react';
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
import { useProofExecution } from '../hooks/useProofExecution';
import { useJsCoq, parseJsCoqState } from '../hooks/useJsCoq';
import toast from 'react-hot-toast';

const COQ_EDITOR_ID = 'coq-editor';

// Filter query panel messages to only show meaningful results (Check/Compute outputs)
function filterQueryMessages(text: string): string | null {
  if (!text || text.trim().length === 0) return null;
  
  // Split by lines and filter out noise
  const lines = text.split('\n').filter(line => {
    const trimmed = line.trim();
    if (!trimmed) return false;
    
    // Filter out library loading messages
    if (trimmed.includes('["Put",') || 
        trimmed.includes('["Init",') ||
        trimmed.includes('["NewDoc",') ||
        trimmed.includes('["Add",') ||
        trimmed.includes('["Query",') ||
        trimmed.includes('["Cancel",') ||
        trimmed.includes(' loaded.') ||
        trimmed.includes('["Exec",') && trimmed.length < 20) { // Short Exec lines are just command markers
      return false;
    }
    
    // Keep lines that look like results (contain ":" or "=" which are common in Check/Compute outputs)
    // Or lines that are actual command results
    if (trimmed.includes(':') || trimmed.includes('=') || trimmed.match(/^\s*[a-zA-Z_][a-zA-Z0-9_]*\s*:/)) {
      return true;
    }
    
    // Filter out JSON-like structures that are just metadata
    if (trimmed.startsWith('[') && trimmed.includes('"')) {
      return false;
    }
    
    return false;
  });
  
  // Also try to extract just the result parts (after "Exec" commands)
  const execMatches = text.match(/\["Exec",\d+\]([^\[]+)/g);
  if (execMatches && execMatches.length > 0) {
    const results = execMatches.map(match => {
      // Extract the part after ["Exec",N]
      const result = match.replace(/\["Exec",\d+\]/, '').trim();
      return result;
    }).filter(r => r.length > 0 && !r.includes('["Put",') && !r.includes('["Init",'));
    
    if (results.length > 0) {
      return results.join('\n');
    }
  }
  
  // If we have filtered lines, return them
  if (lines.length > 0) {
    return lines.join('\n');
  }
  
  return null;
}

export function LevelPage() {
  const { worldId, levelId } = useParams<{ worldId: string; levelId: string }>();
  const navigate = useNavigate();
  const { completeLevel, saveProof, loadWorldData, gameData } = useGame();
  const { execute: executeProof, proofState, isExecuting, clearState } = useProofExecution();
  const { executeProof: jsCoqExecuteProof, isLoaded: jsCoqLoaded, setEditorValue, getEditorValue, setInitialCode, coqManager } = useJsCoq(COQ_EDITOR_ID);
  
  const [level, setLevel] = useState<Level | null>(null);
  const [world, setWorld] = useState<World | null>(null); // Store world to find next level
  const [hintsUsed, setHintsUsed] = useState(0);
  const [attempts, setAttempts] = useState(0);
  const [startTime] = useState(Date.now());
  const [showSuccess, setShowSuccess] = useState(false);
  const [showTheory, setShowTheory] = useState(true);
  const [goalState, setGoalState] = useState<any>(null); // Track goals from jsCoq
  const [isLevelComplete, setIsLevelComplete] = useState(false); // Track if level is complete
  const initializedLevelRef = useRef<string | null>(null); // Track which level we've initialized
  const goalUpdateTimeoutRef = useRef<number | null>(null); // Debounce goal updates
  const isProcessingGoalsRef = useRef(false); // Prevent concurrent goal processing
  const originalUpdateGoalsRef = useRef<((goals: any) => void) | null>(null); // Store original function
  const originalCoqGoalInfoRef = useRef<((sid: number, rawGoals: any) => any) | null>(null); // Store original function
  const messageCheckIntervalRef = useRef<number | null>(null); // Store message check interval
  const goalStateRef = useRef<any>(null); // Store current goal state for interval access

  useEffect(() => {
    async function fetchLevel() {
      if (!worldId || !levelId) return;
      
      try {
        // Load the world first
        const loadedWorld = await loadWorldData(worldId);
        if (!loadedWorld) {
          toast.error('World not found');
          navigate('/worlds');
          return;
        }
        
        setWorld(loadedWorld);
        
        // Now get the level from the loaded world
        const loadedLevel = loadedWorld.levels.find(l => l.id === levelId);
        if (loadedLevel) {
          setLevel(loadedLevel);
          setIsLevelComplete(false); // Reset completion state when level changes
          // Set initial code in jsCoq editor when it's loaded
          if (jsCoqLoaded && setEditorValue) {
            setEditorValue(loadedLevel.startingCode);
          }
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
    
    // Use setInitialCode which will set it immediately if editor is ready,
    // or queue it for when the editor becomes ready
    setInitialCode(level.startingCode);
    
    // Also try setting it directly as a fallback
    let retryCount = 0;
    const maxRetries = 20;
    
    const initEditor = () => {
      const editor = coqManager?.provider?.editor;
      if (editor && typeof editor.setValue === 'function') {
        const currentValue = editor.getValue ? editor.getValue() : '';
        // Check if value is already set (don't reset if user has edited)
        if (currentValue && currentValue.trim() && currentValue !== level.startingCode) {
          // User has edited the code, don't reset it
          return;
        }
        
        if (currentValue === level.startingCode || currentValue.includes(level.startingCode.split('\n')[0])) {
          return;
        }
        
        // Try to set it
        const success = setEditorValue(level.startingCode);
        if (success) {
          const newValue = editor.getValue ? editor.getValue() : '';
          if (newValue === level.startingCode || newValue.includes(level.startingCode.split('\n')[0])) {
            return;
          }
        }
      }
      
      if (retryCount < maxRetries) {
        retryCount++;
        setTimeout(initEditor, 300);
      }
    };
    
    // Start trying after a delay
    setTimeout(initEditor, 500);
  }, [level?.id, jsCoqLoaded, setInitialCode, setEditorValue, coqManager]);

  // Hook into jsCoq's goal updates (when user steps through proof with Alt+Down)
  useEffect(() => {
    if (!coqManager || !jsCoqLoaded) return;

    try {
      // Only hook once - check if already hooked
      if (originalCoqGoalInfoRef.current || originalUpdateGoalsRef.current) {
        return; // Already hooked
      }
      
      // Hook into coqGoalInfo to capture raw goals before DOM conversion
      if ((coqManager as any).coqGoalInfo) {
        originalCoqGoalInfoRef.current = (coqManager as any).coqGoalInfo.bind(coqManager);
        (coqManager as any).coqGoalInfo = function(sid: number, rawGoals: any) {
          // Store raw goals before converting to DOM
          if (coqManager.doc) {
            if (!coqManager.doc.goals_raw) {
              coqManager.doc.goals_raw = {};
            }
            coqManager.doc.goals_raw[sid] = rawGoals;
          }
          // Call original function to convert to DOM and update UI
          if (originalCoqGoalInfoRef.current) {
            return originalCoqGoalInfoRef.current(sid, rawGoals);
          }
        };
      }
      
      
      // Hook into updateGoals to display goals when jsCoq updates them
      const originalUpdateGoals = (coqManager as any).updateGoals;
      if (originalUpdateGoals && typeof originalUpdateGoals === 'function') {
        originalUpdateGoalsRef.current = originalUpdateGoals.bind(coqManager);
        (coqManager as any).updateGoals = function(goals: any) {
          // Call original function first - don't block it
          if (originalUpdateGoalsRef.current) {
            originalUpdateGoalsRef.current(goals);
          }
          
          // Clear any pending updates
          if (goalUpdateTimeoutRef.current !== null) {
            clearTimeout(goalUpdateTimeoutRef.current);
            goalUpdateTimeoutRef.current = null;
          }
          
          // Debounce goal state updates to avoid stalling
          // Make parsing fully async and non-blocking
          goalUpdateTimeoutRef.current = window.setTimeout(() => {
            // Prevent concurrent processing
            if (isProcessingGoalsRef.current) return;
            
            // Capture data synchronously (fast)
            let goalData: any = undefined;
            let messagesData: any[] = [];
            try {
              const doc = coqManager.doc;
              if (doc) {
                const lastAdded = coqManager.lastAdded?.();
                if (lastAdded && lastAdded.coq_sid) {
                  const sid = lastAdded.coq_sid;
                  goalData = doc.goals_raw?.[sid] || doc.goals?.[sid];
                  
                  // Read from jsCoq's query panel where it displays Check/Compute results
                  // Try multiple selectors to find the query panel
                  const querySelectors = [
                    '#query-panel',
                    '.query-panel',
                    '[id*="query"]',
                    '.jscoq-query',
                    '.coq-query'
                  ];
                  
                  for (const selector of querySelectors) {
                    const queryPanelEl = document.querySelector(selector) as HTMLElement;
                    if (queryPanelEl) {
                      const queryText = queryPanelEl.textContent?.trim() || queryPanelEl.innerText?.trim() || '';
                      if (queryText && queryText.length > 0) {
                        // Filter to only show meaningful results (Check/Compute outputs)
                        const filteredText = filterQueryMessages(queryText);
                        if (filteredText) {
                          messagesData.push({
                            text: filteredText,
                            level: 'info'
                          });
                        }
                        break; // Found it, stop looking
                      }
                    }
                  }
                  
                  // Also check layout.query if available
                  if (coqManager.layout && coqManager.layout.query) {
                    const queryPanel = coqManager.layout.query;
                    if (queryPanel.content) {
                      const content = queryPanel.content as HTMLElement;
                      const queryText = content.textContent?.trim() || content.innerText?.trim() || '';
                      if (queryText && queryText.length > 0) {
                        const filteredText = filterQueryMessages(queryText);
                        if (filteredText) {
                          // Check if we already have this text
                          const alreadyExists = messagesData.some((m: any) => m.text === filteredText);
                          if (!alreadyExists) {
                            messagesData.push({
                              text: filteredText,
                              level: 'info'
                            });
                          }
                        }
                      }
                    }
                  }
                }
              }
            } catch (error) {
              // Silently fail
              return;
            }
            
            // Always process if we have messages, even without goals
            if (goalData === undefined && messagesData.length === 0) return;
            
            // Mark as processing
            isProcessingGoalsRef.current = true;
            
            // Parse in next tick to avoid blocking UI
            // Use requestIdleCallback if available for better performance
            const parseAndUpdate = () => {
              try {
                const state = parseJsCoqState(goalData, coqManager, messagesData);
                // Use startTransition to mark this as low-priority update
                // This allows React to interrupt if user interactions occur
                startTransition(() => {
                  setGoalState(state);
                });
              } catch (error) {
                // Silently fail
              } finally {
                isProcessingGoalsRef.current = false;
              }
            };
            
            // Schedule parsing when browser is idle
            if (typeof (window as any).requestIdleCallback === 'function') {
              (window as any).requestIdleCallback(parseAndUpdate, { timeout: 50 });
            } else {
              // Fallback: use setTimeout with 0 delay to yield to browser
              setTimeout(parseAndUpdate, 0);
            }
          }, 100); // Debounce to batch rapid updates
        };
      }
      
      // Also set up a simple interval to check for messages in the query panel
      // This ensures we catch messages even if updateGoals isn't called
      messageCheckIntervalRef.current = window.setInterval(() => {
        try {
          const querySelectors = [
            '#query-panel',
            '.query-panel',
            '[id*="query"]',
            '.jscoq-query',
            '.coq-query'
          ];
          
          let foundText = '';
          for (const selector of querySelectors) {
            const queryPanelEl = document.querySelector(selector) as HTMLElement;
            if (queryPanelEl) {
              const queryText = queryPanelEl.textContent?.trim() || queryPanelEl.innerText?.trim() || '';
              if (queryText && queryText.length > 0) {
                foundText = queryText;
                break;
              }
            }
          }
          
          // Also check layout.query
          if (!foundText && coqManager.layout && coqManager.layout.query) {
            const queryPanel = coqManager.layout.query;
            if (queryPanel.content) {
              const content = queryPanel.content as HTMLElement;
              foundText = content.textContent?.trim() || content.innerText?.trim() || '';
            }
          }
          
          if (foundText) {
            // Filter to only show meaningful results
            const filteredText = filterQueryMessages(foundText);
            if (filteredText) {
              // Check if we need to update
              const currentState = goalStateRef.current;
              const hasMessage = currentState?.messages?.some((m: any) => m.text === filteredText);
              
              if (!hasMessage) {
                // Create a simple state with just the message
                const state = parseJsCoqState(undefined, coqManager, [{
                  text: filteredText,
                  level: 'info'
                }]);
                startTransition(() => {
                  setGoalState(state);
                });
              }
            }
          } else {
            // Debug: log what we're finding
            // console.log('Query panel check:', {
            //   selectors: querySelectors,
            //   layoutQuery: coqManager.layout?.query,
            //   foundElements: querySelectors.map(s => document.querySelector(s))
            // });
          }
        } catch (error) {
          // Silently fail
        }
      }, 500); // Check every 500ms
      
      return () => {
        if (messageCheckIntervalRef.current !== null) {
          clearInterval(messageCheckIntervalRef.current);
          messageCheckIntervalRef.current = null;
        }
        // Clear any pending timeouts
        if (goalUpdateTimeoutRef.current !== null) {
          clearTimeout(goalUpdateTimeoutRef.current);
          goalUpdateTimeoutRef.current = null;
        }
        // Restore original on cleanup
        if (originalUpdateGoalsRef.current && (coqManager as any).updateGoals) {
          (coqManager as any).updateGoals = originalUpdateGoalsRef.current;
          originalUpdateGoalsRef.current = null;
        }
        if (originalCoqGoalInfoRef.current && (coqManager as any).coqGoalInfo) {
          (coqManager as any).coqGoalInfo = originalCoqGoalInfoRef.current;
          originalCoqGoalInfoRef.current = null;
        }
      };
    } catch (error) {
      // Silently fail
    }
  }, [coqManager, jsCoqLoaded]);
  
  // Update ref when goalState changes
  useEffect(() => {
    goalStateRef.current = goalState;
  }, [goalState]);

  // Debug: log when isLevelComplete changes
  useEffect(() => {
    console.log('🔄 isLevelComplete changed:', isLevelComplete);
  }, [isLevelComplete]);

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
        
        saveProof(level.id, {
          code,
          completedAt: new Date().toISOString(),
          timeSpent,
          hintsUsed,
          attempts,
          correct: true,
        });

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
    console.log('🚀 handleNextLevel called', { world, level, worldId });
    
    if (!world || !level) {
      console.warn('⚠️ Cannot navigate: missing world or level', { world: !!world, level: !!level });
      return;
    }
    
    // Find current level index
    const currentIndex = world.levels.findIndex((l: Level) => l.id === level.id);
    console.log('📍 Current level index:', currentIndex, 'Total levels:', world.levels.length);
    
    // Find next level
    if (currentIndex >= 0 && currentIndex < world.levels.length - 1) {
      const nextLevel = world.levels[currentIndex + 1];
      console.log('➡️ Navigating to next level:', nextLevel.id);
      navigate(`/worlds/${worldId}/levels/${nextLevel.id}`);
    } else {
      // No next level, go back to world
      console.log('🏠 No next level, going back to world');
      navigate(`/worlds/${worldId}`);
    }
  };

  if (!level) {
    return (
      <div className="flex items-center justify-center min-h-screen">
        <div>Loading...</div>
      </div>
    );
  }

  return (
    <div className="min-h-screen bg-gray-50">
      <div className="bg-white border-b">
        <div className="mx-auto px-4 py-4">
          <div className="flex items-center justify-between mb-4">
            <Button onClick={() => navigate(`/worlds/${worldId}`)} variant="secondary">
              ← Back to World
            </Button>
            <div className="space-y-2">
            <div className="flex items-center justify-center space-x-3">
              <h1 className="text-2xl font-bold">{level.name}</h1>
              <span className="text-gray-600">{'★'.repeat(level.difficulty)}{'☆'.repeat(5 - level.difficulty)}</span>
            </div>
            <p className="text-center text-gray-700 max-w-3xl mx-auto">{level.objective}</p>
          </div>
            <Button 
              onClick={handleRunProof} 
              disabled={isExecuting && !isLevelComplete}
            >
              {isExecuting && !isLevelComplete ? 'Running...' : isLevelComplete ? 'Next Level →' : 'Run Proof'}
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
              initialValue={level.startingCode}
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

