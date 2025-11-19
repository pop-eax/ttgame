import { useState, useEffect, useRef } from 'react';
import { ProofState } from '../types/proof';
import { JsCoq } from 'jscoq';
import type { CoqManager } from 'jscoq';

export function useJsCoq(containerId: string) {
  const [isLoaded, setIsLoaded] = useState(false);
  const [isInitializing, setIsInitializing] = useState(false);
  const coqManagerRef = useRef<CoqManager | null>(null);
  const initRef = useRef(false); // Prevent double initialization in Strict Mode
  const pendingInitialCodeRef = useRef<string | null>(null);
  const isSettingValueRef = useRef(false); // Flag to prevent cursor events during programmatic value setting
  
  // Function to set initial code (can be called from outside)
  const setInitialCode = (code: string) => {
    pendingInitialCodeRef.current = code;
    // If jsCoq is already loaded, set it immediately
      // Try multiple paths to find the editor
      // jsCoq uses CmCoqProvider which has a 'cm' property (CodeMirror instance)
      const provider = coqManagerRef.current?.provider;
      const editor = provider?.editor || 
                   (provider as any)?.cm ||  // CodeMirror instance
                   (coqManagerRef.current as any)?.editor ||
                   (provider as any)?.cm?.editor;
      
      // Also try to find CodeMirror in the DOM
      let domEditor = null;
      if (!editor && containerId) {
        const container = document.getElementById(containerId);
        if (container) {
          // CodeMirror creates a textarea or div with class 'CodeMirror'
          const cmElement = container.querySelector('.CodeMirror') as any;
          if (cmElement && cmElement.CodeMirror) {
            domEditor = cmElement.CodeMirror;
          } else if (cmElement && (cmElement as any).cm) {
            domEditor = (cmElement as any).cm;
          }
        }
      }
      
      const finalEditor = editor || domEditor;
    
    if (finalEditor && coqManagerRef.current) {
      const setValueFn = finalEditor.setValue || (finalEditor as any).setValue;
      if (typeof setValueFn === 'function') {
        // Set flag to prevent cursor events during programmatic update
        isSettingValueRef.current = true;
        setValueFn.call(finalEditor, code);
        if ((finalEditor as any).trigger) {
          (finalEditor as any).trigger('change', 'setValue', [code]);
        }
        if (coqManagerRef.current.work) {
          coqManagerRef.current.work();
        }
        // Store editor reference if not already stored
        if (provider && !provider.editor && finalEditor) {
          provider.editor = finalEditor;
        }
        pendingInitialCodeRef.current = null;
        // Clear flag after a short delay to allow events to settle
        setTimeout(() => {
          isSettingValueRef.current = false;
        }, 500);
      }
    }
  };

  useEffect(() => {
    if (!containerId || initRef.current) {
      // Silently return if containerId is undefined (React Strict Mode double render)
      return;
    }
    initRef.current = true;
    loadJsCoq();
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [containerId]);

  const loadJsCoq = async () => {
    if (coqManagerRef.current) {
      setIsLoaded(true);
      return;
    }

    if (!containerId) {
      console.error('useJsCoq: containerId is undefined');
      return;
    }

    // Wait for container to be in DOM with retries
    let container = document.getElementById(containerId);
    let retries = 0;
    const maxRetries = 50; // 5 seconds max
    
    while (!container && retries < maxRetries) {
      await new Promise(resolve => setTimeout(resolve, 100));
      container = document.getElementById(containerId);
      retries++;
    }

    if (!container) {
      console.error(`Container ${containerId} not found after ${maxRetries} retries`);
      setIsInitializing(false);
      setIsLoaded(false);
      return;
    }

    // Wait a bit more to ensure container is fully rendered
    await new Promise(resolve => setTimeout(resolve, 100));

    setIsInitializing(true);

    // Create wrapper element for jsCoq if it doesn't exist
    const wrapperId = containerId + '-wrapper';
    const basePath = new URL('/jscoq/', window.location.origin).href;

    try {
      let wrapper = document.getElementById(wrapperId);
      if (!wrapper) {
        wrapper = document.createElement('div');
        wrapper.id = wrapperId;
        wrapper.className = 'coq-wrapper';
        container.appendChild(wrapper);
      }
      
      
      // Initialize jsCoq with configuration
      // show: true makes jsCoq's UI visible (goal panel, etc.)
      const coqManager = await JsCoq.start([containerId], {
        wrapper_id: wrapperId,
        init_pkgs: ['init'],
        all_pkgs: ['init'],
        theme: 'light',
        base_path: basePath,
        pkg_path: basePath + 'coq-pkgs/',
        backend: 'js', // Use JS backend
        show: true, // Show jsCoq's default UI (goal panel, etc.)
        focus: true,
        prelude: true,
        implicit_libs: false, // Don't auto-load libraries
      });
      
      // Ensure the layout is visible
      if (coqManager.layout && coqManager.layout.show) {
        coqManager.layout.show();
      }

      coqManagerRef.current = coqManager;
      
      // Ensure the layout is visible - jsCoq's UI should be shown
      if (coqManager.layout) {
        if (coqManager.layout.show) {
          coqManager.layout.show();
        }
      }
      
      // Wait for the editor to be fully initialized - retry multiple times
      for (let i = 0; i < 10; i++) {
        await new Promise(resolve => setTimeout(resolve, 200));
        // Check multiple possible paths to the editor
        // jsCoq uses CmCoqProvider which has a 'cm' property (CodeMirror instance)
        const provider = coqManager.provider;
        const editor = provider?.editor || 
                      (provider as any)?.cm ||  // CodeMirror instance
                      (coqManager as any).editor ||
                      (provider as any)?.cm?.editor;
        
        // Also try to find CodeMirror in the DOM
        let domEditor = null;
        if (!editor) {
          const container = document.getElementById(containerId);
          if (container) {
            // CodeMirror creates a textarea or div with class 'CodeMirror'
            const cmElement = container.querySelector('.CodeMirror') as any;
            if (cmElement && cmElement.CodeMirror) {
              domEditor = cmElement.CodeMirror;
            } else if (cmElement && (cmElement as any).cm) {
              domEditor = (cmElement as any).cm;
            }
          }
        }
        
        const finalEditor = editor || domEditor;
        if (finalEditor && (typeof finalEditor.setValue === 'function' || typeof (finalEditor as any).setValue === 'function')) {
          // Store the editor reference if it's not at the expected path
          if (provider && !provider.editor && finalEditor) {
            provider.editor = finalEditor;
          }
          break;
        }
      }
      
      // Try to set pending initial code if any
      if (pendingInitialCodeRef.current) {
        if (coqManager.provider && coqManager.provider.editor) {
          const editor = coqManager.provider.editor;
          if (typeof editor.setValue === 'function') {
            editor.setValue(pendingInitialCodeRef.current);
            // Trigger events to ensure jsCoq processes it
            if ((editor as any).trigger) {
              (editor as any).trigger('change', 'setValue', [pendingInitialCodeRef.current]);
            }
            if (coqManager.work) {
              coqManager.work();
            }
            pendingInitialCodeRef.current = null;
          }
        }
      }
      
      setIsLoaded(true);
      setIsInitializing(false);
      
      // Set up a periodic check to set pending code when editor becomes ready
      if (pendingInitialCodeRef.current) {
        const checkInterval = setInterval(() => {
          if (coqManagerRef.current?.provider?.editor && pendingInitialCodeRef.current) {
            const editor = coqManagerRef.current.provider.editor;
            if (typeof editor.setValue === 'function') {
              const code = pendingInitialCodeRef.current;
              editor.setValue(code);
              if ((editor as any).trigger) {
                (editor as any).trigger('change', 'setValue', [code]);
              }
              if (coqManagerRef.current.work) {
                coqManagerRef.current.work();
              }
              pendingInitialCodeRef.current = null;
              clearInterval(checkInterval);
            }
          }
        }, 500);
        
        // Clear interval after 10 seconds
        setTimeout(() => {
          clearInterval(checkInterval);
        }, 10000);
      }
    } catch (error: any) {
      console.error('Failed to initialize jsCoq:', error);
      console.error('Error details:', {
        message: error?.message,
        stack: error?.stack,
        basePath,
        containerId,
        wrapperId
      });
      setIsInitializing(false);
      setIsLoaded(false);
    }
  };

  const executeToCursor = async (_code: string, _cursorLine: number): Promise<ProofState> => {
    // Don't execute if we're currently setting a value programmatically
    if (isSettingValueRef.current) {
      return {
        goals: [],
        hypotheses: [],
        messages: [],
        isComplete: false,
        hasError: false,
      };
    }
    
    if (!isLoaded || !coqManagerRef.current) {
      return {
        goals: [],
        hypotheses: [],
        messages: [],
        isComplete: false,
        hasError: false,
      };
    }

    try {
      const coqManager = coqManagerRef.current;
      const provider = coqManager.provider;
      
      if (!provider || !provider.editor) {
        return {
          goals: [],
          hypotheses: [],
          messages: [],
          isComplete: false,
          hasError: false,
        };
      }
      
      // Get goals from the last processed sentence
      // jsCoq updates goals automatically when you use Alt+Down, so we just need to read them
      const doc = coqManager.doc;
      if (doc) {
        // Get last processed sentence
        let lastAdded: any = null;
        if (coqManager.lastAdded && typeof coqManager.lastAdded === 'function') {
          lastAdded = coqManager.lastAdded();
        } else if (doc.sentences && doc.sentences.length > 0) {
          const processed = doc.sentences.filter((s: any) => s.coq_sid && s.phase === 'PROCESSED');
          lastAdded = processed[processed.length - 1];
        }
        
        if (lastAdded && lastAdded.coq_sid) {
          const sid = lastAdded.coq_sid;
          let goals = doc.goals?.[sid];
          
          // Request goals if not available
          if (goals === undefined && coqManager.coq && typeof coqManager.coq.goals === 'function') {
            coqManager.coq.goals(sid);
            // Wait a bit for goals to be fetched
            await new Promise(resolve => setTimeout(resolve, 300));
            goals = doc.goals?.[sid];
          }
          
          if (goals !== undefined) {
            const state = parseJsCoqState(goals, coqManager);
            return state;
          }
        }
      }
      
      return {
        goals: [],
        hypotheses: [],
        messages: [],
        isComplete: false,
        hasError: false,
      };
    } catch (error: any) {
      return {
        goals: [],
        hypotheses: [],
        messages: [{
          level: 'error',
          text: error.message || 'Proof execution failed',
        }],
        isComplete: false,
        hasError: true,
      };
    }
  };

  const executeProof = async (code: string): Promise<ProofState> => {
    // Don't execute if we're currently setting a value programmatically
    if (isSettingValueRef.current) {
      return {
        goals: [],
        hypotheses: [],
        messages: [],
        isComplete: false,
        hasError: false,
      };
    }
    
    if (!isLoaded || !coqManagerRef.current) {
      return {
        goals: [],
        hypotheses: [],
        messages: [],
        isComplete: false,
        hasError: false,
      };
    }

    try {
      const coqManager = coqManagerRef.current;
      const provider = coqManager.provider;
      
      if (!provider || !provider.editor) {
        return {
          goals: [],
          hypotheses: [],
          messages: [],
          isComplete: false,
          hasError: false,
        };
      }
      
      // Process all sentences to completion
      const doc = coqManager.doc;
      if (!doc) {
        return {
          goals: [],
          hypotheses: [],
          messages: [],
          isComplete: false,
          hasError: false,
        };
      }
      
      // Get all sentences
      const sentences = doc.sentences || [];
      if (sentences.length === 0) {
        return {
          goals: [],
          hypotheses: [],
          messages: [],
          isComplete: true, // No sentences means nothing to prove
          hasError: false,
        };
      }
      
      // Process all sentences by calling goNext() until all are processed
      let maxIterations = sentences.length * 2; // Safety limit
      let iterations = 0;
      
      while (iterations < maxIterations) {
        // Check if all sentences are processed
        const allProcessed = sentences.every((s: any) => 
          s.phase === 'PROCESSED' || s.phase === 'ERROR' || s.phase === 'FAILED'
        );
        
        if (allProcessed) {
          break;
        }
        
        // Process next sentence
        if (coqManager.goNext && typeof coqManager.goNext === 'function') {
          coqManager.goNext(true); // true = forward
        } else if (coqManager.goCursor && typeof coqManager.goCursor === 'function') {
          // Move cursor to end and process
          const editor = provider.editor;
          if (editor && editor.setCursor) {
            const lineCount = editor.lineCount();
            editor.setCursor({ line: lineCount - 1, ch: 999 });
          }
          coqManager.goCursor();
        }
        
        // Wait a bit for processing
        await new Promise(resolve => setTimeout(resolve, 100));
        iterations++;
      }
      
      // Wait a bit more for final processing
      await new Promise(resolve => setTimeout(resolve, 300));
      
      // Check for errors in any sentence
      const hasError = sentences.some((s: any) => 
        s.phase === 'ERROR' || s.phase === 'FAILED'
      );
      
      if (hasError) {
        // Collect error messages
        const errorMessages: any[] = [];
        sentences.forEach((s: any) => {
          if (s.phase === 'ERROR' || s.phase === 'FAILED') {
            if (s.feedback && Array.isArray(s.feedback)) {
              s.feedback.forEach((fb: any) => {
                if (fb && (fb.msg || fb.message)) {
                  errorMessages.push({
                    level: 'error' as const,
                    text: fb.msg || fb.message || 'Proof error',
                  });
                }
              });
            }
          }
        });
        
        // Still check goals even if there are errors
        const lastProcessed = sentences
          .filter((s: any) => s.coq_sid && (s.phase === 'PROCESSED' || s.phase === 'ERROR'))
          .pop();
        
        if (lastProcessed && lastProcessed.coq_sid) {
          const sid = lastProcessed.coq_sid;
          let goals = doc.goals?.[sid] || doc.goals_raw?.[sid];
          
          if (goals === undefined && coqManager.coq && typeof coqManager.coq.goals === 'function') {
            coqManager.coq.goals(sid);
            await new Promise(resolve => setTimeout(resolve, 300));
            goals = doc.goals?.[sid] || doc.goals_raw?.[sid];
          }
          
          const state = parseJsCoqState(goals, coqManager, errorMessages);
          return {
            ...state,
            hasError: true,
          };
        }
        
        return {
          goals: [],
          hypotheses: [],
          messages: errorMessages.length > 0 ? errorMessages : [{
            level: 'error' as const,
            text: 'Proof execution failed',
          }],
          isComplete: false,
          hasError: true,
        };
      }
      
      // Get goals from the last processed sentence
      const lastProcessed = sentences
        .filter((s: any) => s.coq_sid && s.phase === 'PROCESSED')
        .pop();
      
      if (lastProcessed && lastProcessed.coq_sid) {
        const sid = lastProcessed.coq_sid;
        let goals = doc.goals?.[sid] || doc.goals_raw?.[sid];
        
        // Request goals if not available
        if (goals === undefined && coqManager.coq && typeof coqManager.coq.goals === 'function') {
          coqManager.coq.goals(sid);
          await new Promise(resolve => setTimeout(resolve, 300));
          goals = doc.goals?.[sid] || doc.goals_raw?.[sid];
        }
        
        if (goals !== undefined) {
          const state = parseJsCoqState(goals, coqManager);
          return state;
        }
      }
      
      // If no processed sentences, check if we can get goals from lastAdded
      if (coqManager.lastAdded && typeof coqManager.lastAdded === 'function') {
        const lastAdded = coqManager.lastAdded();
        if (lastAdded && lastAdded.coq_sid) {
          const sid = lastAdded.coq_sid;
          let goals = doc.goals?.[sid] || doc.goals_raw?.[sid];
          
          if (goals === undefined && coqManager.coq && typeof coqManager.coq.goals === 'function') {
            coqManager.coq.goals(sid);
            await new Promise(resolve => setTimeout(resolve, 300));
            goals = doc.goals?.[sid] || doc.goals_raw?.[sid];
          }
          
          if (goals !== undefined) {
            const state = parseJsCoqState(goals, coqManager);
            return state;
          }
        }
      }
      
      // No goals found - assume complete if all sentences processed
      const allProcessed = sentences.every((s: any) => 
        s.phase === 'PROCESSED' || s.phase === 'ERROR' || s.phase === 'FAILED'
      );
      
      return {
        goals: [],
        hypotheses: [],
        messages: [],
        isComplete: allProcessed && !hasError,
        hasError: hasError,
      };
    } catch (error: any) {
      return {
        goals: [],
        hypotheses: [],
        messages: [{
          level: 'error',
          text: error.message || 'Proof execution failed',
        }],
        isComplete: false,
        hasError: true,
      };
    }
  };

  const getEditorValue = (): string => {
    if (!coqManagerRef.current?.provider?.editor) {
      return '';
    }
    return coqManagerRef.current.provider.editor.getValue() || '';
  };

  const setEditorValue = (value: string) => {
    if (!coqManagerRef.current?.provider?.editor) {
      console.warn('setEditorValue: editor not available');
      return false;
    }
    
    const editor = coqManagerRef.current.provider.editor;
    const provider = coqManagerRef.current.provider;
    
    // Set flag to prevent cursor events during programmatic update
    isSettingValueRef.current = true;
    
    // Set the value using the editor's setValue method
    if (typeof editor.setValue === 'function') {
      editor.setValue(value);
    } else {
      isSettingValueRef.current = false;
      return false;
    }
    
    // Trigger change event so jsCoq parses the content
    if ((editor as any).trigger && typeof (editor as any).trigger === 'function') {
      (editor as any).trigger('change', 'setValue', [value]);
    }
    
    // Also trigger input event
    if ((editor as any).trigger && typeof (editor as any).trigger === 'function') {
      (editor as any).trigger('input', 'setValue', [value]);
    }
    
    // Use provider's API to update content
    if (provider.updateContent && typeof provider.updateContent === 'function') {
      provider.updateContent();
    }
    
    // Process the document
    if (coqManagerRef.current.work && typeof coqManagerRef.current.work === 'function') {
      coqManagerRef.current.work();
    }
    
    // Also try to refresh/parse the document
    if (provider.parseContent && typeof provider.parseContent === 'function') {
      provider.parseContent();
    }
    
    // Clear flag after a delay to allow events to settle
    setTimeout(() => {
      isSettingValueRef.current = false;
    }, 500);
    
    return true;
  };

  return {
    isLoaded,
    isInitializing,
    executeProof,
    executeToCursor,
    getEditorValue,
    setEditorValue,
    setInitialCode,
    coqManager: coqManagerRef.current,
  };
}

// Helper function to extract string from jsCoq's pretty-printing format
// Format: ["Pp_tag", "constr.variable", ["Pp_string", "nat"]]
// Or: ["Pp_string", "nat"]
function extractStringFromPp(pp: any): string {
  if (typeof pp === 'string') {
    return pp;
  }
  if (!pp) {
    return '';
  }
  if (Array.isArray(pp)) {
    // Check if it's a Pp_string directly
    if (pp[0] === 'Pp_string' && pp.length >= 2) {
      return pp[1];
    }
    // Recursively extract strings from nested structure
    const parts: string[] = [];
    for (let i = 0; i < pp.length; i++) {
      const part = extractStringFromPp(pp[i]);
      if (part) {
        parts.push(part);
      }
    }
    // Join parts, but skip tags and other metadata
    return parts.filter(p => p && !p.startsWith('Pp_') && !p.includes('.')).join(' ');
  }
  return pp?.toString() || '';
}

export function parseJsCoqState(goals: any, coqManager: any, messagesData?: any[]): ProofState {
  try {
    
    const hypotheses: Array<{ name: string; type: string }> = [];
    const messages: Array<{ level: 'info' | 'warning' | 'error'; text: string }> = [];
    
    // Handle different goal formats
    let goalsArray: any[] = [];
    
    // Check if it's the raw goal structure from jsCoq
    // Structure: { goals: [], stack: [[...]], shelf: [], given_up: [] }
    if (goals && typeof goals === 'object' && !goals.nodeType && goals.stack !== undefined) {
      // This is the raw goal structure from jsCoq
      
      // Extract goals from the stack
      // stack structure: [[fg_goals, bg_goals], ...] where each level has foreground and background goals
      if (Array.isArray(goals.stack)) {
        // Iterate through each stack level
        goals.stack.forEach((stackLevel: any) => {
          if (Array.isArray(stackLevel)) {
            // Each stack level is [fg_goals, bg_goals]
            stackLevel.forEach((goalGroup: any) => {
              if (Array.isArray(goalGroup)) {
                // It's an array of goals (fg_goals or bg_goals)
                goalGroup.forEach((goal: any) => {
                  if (goal && typeof goal === 'object' && !Array.isArray(goal)) {
                    // It's a goal object, add it
                    goalsArray.push(goal);
                  }
                });
              } else if (goalGroup && typeof goalGroup === 'object' && !Array.isArray(goalGroup)) {
                // It's a single goal object
                goalsArray.push(goalGroup);
              }
            });
          } else if (stackLevel && typeof stackLevel === 'object' && !Array.isArray(stackLevel)) {
            // It's a single goal object at the stack level
            goalsArray.push(stackLevel);
          }
        });
      }
      
      // Also check goals array directly
      if (Array.isArray(goals.goals) && goals.goals.length > 0) {
        goals.goals.forEach((goal: any) => {
          if (goal && typeof goal === 'object') {
            goalsArray.push(goal);
          }
        });
      }
      
    } else if (goals && typeof goals === 'object' && goals.length !== undefined) {
      // It's an array-like object (could be DOM elements)
      goalsArray = Array.from(goals);
    } else if (Array.isArray(goals)) {
      goalsArray = goals;
    } else if (goals && typeof goals === 'object') {
      // Check if it's a single DOM element
      if (goals.nodeType !== undefined) {
        goalsArray = [goals];
      } else if (goals.fg_goals) {
        goalsArray = Array.isArray(goals.fg_goals) ? goals.fg_goals : [goals.fg_goals];
      } else if (goals.bg_goals) {
        goalsArray = Array.isArray(goals.bg_goals) ? goals.bg_goals : [goals.bg_goals];
      } else {
        goalsArray = [goals];
      }
    }
    
    // Parse goals - they might be DOM elements from goals2DOM or raw goal objects
    const parsedGoals = goalsArray.map((goal: any, idx: number) => {
      // Extract hypotheses from goal context
      const goalHyps: Array<{ name: string; type: string }> = [];
      
      let goalType = '';
      let goalCountText = ''; // Store "X goal" or "X goals" text
      
      // Check if it's a raw goal object (not DOM)
      if (goal && typeof goal === 'object' && !goal.nodeType) {
        // console.log('🔍 Parsing raw goal object:', goal);
        
        // Raw goal structure from jsCoq:
        // Each goal has: hyp (array of hypotheses), ty (goal type in structured format)
        // ty is in jsCoq's pretty-printing format: ["Pp_tag", "constr.variable", ["Pp_string", "nat"]]
        // hyp is an array of hypothesis objects
        
        // Extract hypotheses from raw goal structure
        // Check both 'hyp' and 'hyps' for compatibility
        const hypsArray = goal.hyp || goal.hyps;
        if (hypsArray && Array.isArray(hypsArray)) {
          hypsArray.forEach((hyp: any) => {
            if (hyp) {
              let hypName = '';
              let hypType = '';
              
              // Handle different hypothesis formats from jsCoq
              if (Array.isArray(hyp) && hyp.length >= 2) {
                // Format: [name, type] where type might be structured
                hypName = hyp[0]?.toString() || '';
                // Type might be structured (Pp format) or a string
                if (Array.isArray(hyp[1])) {
                  // Use pretty printer to format structured type
                  if (coqManager && coqManager.pprint && typeof coqManager.pprint.pp2String === 'function') {
                    hypType = coqManager.pprint.pp2String(hyp[1]);
                  } else {
                    hypType = JSON.stringify(hyp[1]);
                  }
                } else {
                  hypType = hyp[1]?.toString() || '';
                }
              } else if (hyp.id !== undefined && hyp.type !== undefined) {
                hypName = hyp.id.toString();
                if (Array.isArray(hyp.type)) {
                  if (coqManager && coqManager.pprint && typeof coqManager.pprint.pp2String === 'function') {
                    hypType = coqManager.pprint.pp2String(hyp.type);
                  } else {
                    hypType = JSON.stringify(hyp.type);
                  }
                } else {
                  hypType = hyp.type.toString();
                }
              } else if (hyp.name !== undefined && hyp.ty !== undefined) {
                hypName = hyp.name.toString();
                if (Array.isArray(hyp.ty)) {
                  if (coqManager && coqManager.pprint && typeof coqManager.pprint.pp2String === 'function') {
                    hypType = coqManager.pprint.pp2String(hyp.ty);
                  } else {
                    hypType = JSON.stringify(hyp.ty);
                  }
                } else {
                  hypType = hyp.ty.toString();
                }
              }
              
              if (hypName && hypType) {
                goalHyps.push({ name: hypName, type: hypType });
                if (!hypotheses.find(h => h.name === hypName)) {
                  hypotheses.push({ name: hypName, type: hypType });
                }
              }
            }
          });
        }
        
        // Extract goal type from raw goal structure
        // jsCoq uses 'ty' (structured format) or 'ccl' for goal type
        if (goal.ty !== undefined) {
          // ty is in structured format, use jsCoq's pretty printer
          if (coqManager && coqManager.pprint && typeof coqManager.pprint.pp2String === 'function') {
            goalType = coqManager.pprint.pp2String(goal.ty);
          } else {
            // Fallback: try to extract string from structure
            goalType = extractStringFromPp(goal.ty);
          }
        } else if (goal.ccl !== undefined) {
          if (coqManager && coqManager.pprint && typeof coqManager.pprint.pp2String === 'function') {
            goalType = coqManager.pprint.pp2String(goal.ccl);
          } else {
            goalType = extractStringFromPp(goal.ccl);
          }
        } else if (goal.type !== undefined) {
          if (Array.isArray(goal.type)) {
            if (coqManager && coqManager.pprint && typeof coqManager.pprint.pp2String === 'function') {
              goalType = coqManager.pprint.pp2String(goal.type);
            } else {
              goalType = extractStringFromPp(goal.type);
            }
          } else {
            goalType = goal.type.toString();
          }
        }
        
        // console.log('🔍 Parsed raw goal:', { goalType, goalHyps: goalHyps.length, goal });
      } else if (goal && goal.nodeType !== undefined) {
        // If goal is a DOM element, extract text content
        // It's a DOM element - extract the formatted text
        // jsCoq formats goals in a specific structure in the DOM
        const goalDiv = goal.querySelector ? goal : (goal.parentElement || goal);
        
        // Get all text content from the goal div
        const fullText = goalDiv.textContent || goalDiv.innerText || goal.textContent || goal.innerText || '';
        
        // Debug: log the raw text to understand the format
        // console.log('🔍 Raw goal text:', JSON.stringify(fullText));
        
        // Parse jsCoq's goal format:
        // Format is usually: "hyp1 : type1\nhyp2 : type2\n========\ngoal_type"
        // Or sometimes: "hyp1 : type1\nhyp2 : type2\n\n========\n\ngoal_type"
        const lines = fullText.split('\n').map((l: string) => l.trim()).filter((l: string) => l.length > 0);
        
        // console.log('🔍 Parsed lines:', lines);
        
        // Find the separator line (usually "========" or similar)
        let separatorIndex = -1;
        for (let i = 0; i < lines.length; i++) {
          if (lines[i].match(/^=+$/)) {
            separatorIndex = i;
            break;
          }
        }
        
        if (separatorIndex > 0) {
          // Extract hypotheses (everything before the separator)
          for (let i = 0; i < separatorIndex; i++) {
            const line = lines[i];
            // Check for goal count text first
            const goalPrefixMatch = line.match(/^(\d+\s+goals?)$/i);
            if (goalPrefixMatch) {
              goalCountText = goalPrefixMatch[1].trim();
              continue;
            }
            // Then check for hypothesis pattern
            const match = line.match(/^(\w+)\s*:\s*(.+)$/);
            if (match) {
              const [, name, type] = match;
              goalHyps.push({ name, type });
              if (!hypotheses.find(h => h.name === name)) {
                hypotheses.push({ name, type });
              }
            }
          }
          
          // Extract goal type (everything after the separator)
          goalType = lines.slice(separatorIndex + 1).join(' ').trim();
        } else {
          // No separator found, try to parse differently
          // First, try to find structured DOM elements
          const hypElements = goalDiv.querySelectorAll ? goalDiv.querySelectorAll('.hyp, .hypothesis, [data-hyp], .goal-hyp, .goal-hyps .hyp, .coq-goal-hyp') : [];
          hypElements.forEach((hypEl: any) => {
            const hypText = hypEl.textContent || hypEl.innerText || '';
            const match = hypText.match(/^(\w+)\s*:\s*(.+)$/);
            if (match) {
              const [, name, type] = match;
              goalHyps.push({ name, type });
              if (!hypotheses.find(h => h.name === name)) {
                hypotheses.push({ name, type });
              }
            }
          });
          
          // Try to find goal type in structured elements
          const goalTypeEl = goalDiv.querySelector ? goalDiv.querySelector('.goal-type, .goal-ccl, .goal-conclusion, .coq-goal-ccl') : null;
          if (goalTypeEl) {
            goalType = goalTypeEl.textContent || goalTypeEl.innerText || '';
          } else {
            // Fallback: parse from text lines
            // The format might be: "X goal<goal_type>" or "X goals<goal_type>"
            // Or: "hyp1 : type1\nhyp2 : type2\ngoal_type"
            
            // First, try to extract hypotheses
            for (const line of lines) {
              const hypMatch = line.match(/^(\w+)\s*:\s*(.+)$/);
              if (hypMatch) {
                const [, name, type] = hypMatch;
                goalHyps.push({ name, type });
                if (!hypotheses.find(h => h.name === name)) {
                  hypotheses.push({ name, type });
                }
              }
            }
            
            // Then find goal type
            for (const line of lines) {
              // Skip hypothesis lines and separators
              if (line.match(/^\w+\s*:/) || line.match(/^=+$/)) {
                continue;
              }
              
              // Check if line starts with "X goal" or "X goals" pattern
              // Format: "1 goalnat * nat" or "2 goalsnat2nat"
              // The text might be concatenated without spaces
              const goalPrefixMatch = line.match(/^(\d+\s+goals?)(.+)$/i);
              if (goalPrefixMatch) {
                // Extract the "X goal" or "X goals" text and the goal type
                goalCountText = goalPrefixMatch[1].trim();
                let extractedType = goalPrefixMatch[2].trim();
                
                // Handle concatenated types like "nat2nat" -> "nat * nat"
                // Or "natnat" -> "nat * nat"
                // Try to split on common patterns
                if (extractedType.match(/^(\w+)(\d+)(\w+)$/)) {
                  // Pattern like "nat2nat" - split into "nat * nat"
                  extractedType = extractedType.replace(/(\w+)(\d+)(\w+)/g, '$1 * $3');
                } else if (extractedType.match(/^(\w+)(\w+)$/)) {
                  // Pattern like "natnat" - split into "nat * nat"
                  extractedType = extractedType.replace(/(\w+)(\w+)/g, '$1 * $2');
                }
                
                goalType = extractedType;
                break;
              } else if (!line.match(/^\d+\s+goals?$/i) && 
                         !line.match(/^Goal\s+\d+$/i) &&
                         !line.match(/^\(\d+\s*\/\s*\d+\)$/)) {
                // This might be the goal type (no prefix)
                if (!goalType) {
                  goalType = line;
                } else {
                  goalType += ' ' + line;
                }
              }
            }
            
            // Clean up goal type - remove any remaining artifacts
            goalType = goalType.trim();
          }
        }
        
        // console.log('🔍 Parsed goal:', { goalType, goalHyps: goalHyps.length });
      } else {
        // It's a plain object - extract from properties
        let hyps: any[] = [];
        if (goal && goal.hyps) {
          hyps = Array.isArray(goal.hyps) ? goal.hyps : [goal.hyps];
        } else if (goal && goal.fg_hyps) {
          hyps = Array.isArray(goal.fg_hyps) ? goal.fg_hyps : [goal.fg_hyps];
        }
        
        hyps.forEach((hyp: any) => {
          if (hyp) {
            let hypName = '';
            let hypType = '';
            
            if (Array.isArray(hyp) && hyp.length >= 2) {
              hypName = hyp[0]?.toString() || '';
              hypType = hyp[1]?.toString() || '';
            } else if (hyp.name && hyp.ty) {
              hypName = hyp.name.toString();
              hypType = hyp.ty.toString();
            }
            
            if (hypName && hypType) {
              goalHyps.push({ name: hypName, type: hypType });
              if (!hypotheses.find(h => h.name === hypName)) {
                hypotheses.push({ name: hypName, type: hypType });
              }
            }
          }
        });
        
        // Get goal type
        if (goal && goal.ty) {
          goalType = goal.ty.toString();
        } else if (goal && goal.ccl) {
          goalType = goal.ccl.toString();
        } else if (goal && goal.type) {
          goalType = goal.type.toString();
        }
      }
      
      return {
        id: `goal-${idx + 1}`,
        type: goalType,
        context: goalHyps,
        rawGoal: goal,
        goalCountText: goalCountText, // Store "X goal" or "X goals" text
      };
    });
    
    // Helper function to extract text from jsCoq's pretty-printing format
    const extractMessageText = (content: any): string => {
      if (typeof content === 'string') {
        return content;
      }
      if (Array.isArray(content)) {
        return content.map((c: any) => {
          if (typeof c === 'string') return c;
          if (Array.isArray(c)) {
            // Handle nested arrays (pretty-printing format)
            if (c[0] === 'Pp_string' && c.length >= 2) {
              return c[1];
            }
            return extractMessageText(c);
          }
          if (c && typeof c === 'object') {
            if (c[0] === 'Pp_string' && c.length >= 2) {
              return c[1];
            }
            // Try to extract from object
            if (c.text) return c.text;
            if (c.msg) return c.msg;
            if (c.str) return c.str;
            // Try to use pprint if available
            if (coqManager && coqManager.pprint && coqManager.pprint.pp2String) {
              try {
                return coqManager.pprint.pp2String(c);
              } catch (e) {
                // Fall through
              }
            }
            return extractStringFromPp(c);
          }
          return String(c);
        }).filter((s: string) => s && s.trim()).join(' ');
      }
      if (content && typeof content === 'object') {
        if (content[0] === 'Pp_string' && content.length >= 2) {
          return content[1];
        }
        if (content.text) return content.text;
        if (content.msg) return content.msg;
        if (content.str) return content.str;
        // Try pprint
        if (coqManager && coqManager.pprint && coqManager.pprint.pp2String) {
          try {
            return coqManager.pprint.pp2String(content);
          } catch (e) {
            // Fall through
          }
        }
        return extractStringFromPp(content);
      }
      return String(content);
    };
    
    // Get messages from messagesData parameter
    if (messagesData && Array.isArray(messagesData)) {
      messagesData.forEach((msg: any) => {
        if (msg) {
          let messageText = '';
          let messageLevel: 'info' | 'warning' | 'error' = msg.level || 'info';
          
          // Simple: if it has a text property, use it
          if (msg.text) {
            messageText = msg.text;
          } else if (typeof msg === 'string') {
            messageText = msg;
          } else {
            // Fallback: try to extract text
            messageText = String(msg);
          }
          
          if (messageText && messageText.trim()) {
            messages.push({
              level: messageLevel,
              text: messageText.trim(),
            });
          }
        }
      });
    }
    
    // Also get messages from coqManager if available (fallback)
    if (coqManager && coqManager.messages && (!messagesData || messagesData.length === 0)) {
      coqManager.messages.forEach((msg: any) => {
        if (msg) {
          messages.push({
            level: msg.level || 'info',
            text: msg.text || msg.msg || msg.toString(),
          });
        }
      });
    }
    
    const isComplete = parsedGoals.length === 0;
    
    // Generate goal count text (e.g., "1 goal" or "2 goals")
    const goalCount = parsedGoals.length;
    const goalCountText = goalCount === 1 ? '1 goal' : `${goalCount} goals`;
    
    // Add goal count text to each goal if not already set
    parsedGoals.forEach((goal) => {
      if (!goal.goalCountText) {
        goal.goalCountText = goalCountText;
      }
    });
    
    console.log('🔍 Final parsed state:', { 
      goalsCount: parsedGoals.length, 
      isComplete,
      goalCountText,
      parsedGoals: parsedGoals.map(g => ({ type: g.type, hyps: g.context.length }))
    });
    
    return {
      goals: parsedGoals,
      hypotheses,
      messages,
      isComplete,
      hasError: false,
      rawState: { goals: goalsArray },
    };
  } catch (error) {
    console.error('Error parsing jsCoq state:', error);
    return {
      goals: [],
      hypotheses: [],
      messages: [{
        level: 'error',
        text: 'Failed to parse proof state',
      }],
      isComplete: false,
      hasError: true,
    };
  }
}
