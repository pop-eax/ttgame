import { useState, useEffect, useRef } from 'react';
import { ProofState } from '../types/proof';
import { JsCoq } from 'jscoq';
import type { CoqManager } from 'jscoq';

export function useJsCoq(containerId: string, theme: 'light' | 'dark' = 'light') {
  const [isLoaded, setIsLoaded] = useState(false);
  const [isInitializing, setIsInitializing] = useState(false);
  const coqManagerRef = useRef<CoqManager | null>(null);
  const initRef = useRef(false);
  const initialCodeRef = useRef<string | null>(null);
  const themeRef = useRef<'light' | 'dark'>(theme);

  // Update theme when it changes
  useEffect(() => {
    themeRef.current = theme;
    const coqManager = coqManagerRef.current;
    if (coqManager?.provider && isLoaded) {
      // Map theme: 'light' -> 'default', 'dark' -> 'blackboard' for CodeMirror
      const editorTheme = theme === 'dark' ? 'blackboard' : 'default';
      coqManager.provider.configure({ theme: editorTheme });
    }
  }, [theme, isLoaded]);

  useEffect(() => {
    if (!containerId || initRef.current) return;
    initRef.current = true;
    loadJsCoq();
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

    // Wait for container to be in DOM
    let container = document.getElementById(containerId);
    let retries = 0;
    while (!container && retries < 50) {
      await new Promise(resolve => setTimeout(resolve, 100));
      container = document.getElementById(containerId);
      retries++;
    }

    if (!container) {
      console.error(`Container ${containerId} not found`);
      setIsInitializing(false);
      setIsLoaded(false);
      return;
    }

    setIsInitializing(true);

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

      // Map theme: 'light' -> 'light', 'dark' -> 'dark' (jsCoq uses these directly)
      const coqManager = await JsCoq.start([containerId], {
        wrapper_id: wrapperId,
        init_pkgs: ['init'],
        all_pkgs: ['init'],
        theme: themeRef.current,
        base_path: basePath,
        pkg_path: basePath + 'coq-pkgs/',
        backend: 'wa',
        show: true,
        focus: true,
        prelude: true,
        implicit_libs: false,
      });

      coqManagerRef.current = coqManager;
      
      // If we have initial code queued, set it now using provider.load()
      if (initialCodeRef.current && coqManager.provider) {
        coqManager.provider.load(initialCodeRef.current);
        initialCodeRef.current = null;
      }
      
      setIsLoaded(true);
      setIsInitializing(false);
    } catch (error: any) {
      console.error('Failed to initialize jsCoq:', error);
      setIsInitializing(false);
      setIsLoaded(false);
    }
  };

  const getGoalsAndMessages = async (): Promise<ProofState> => {
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

      const sentences = doc.sentences || [];
      const allProcessed = sentences.every((s: any) => 
        s.phase === 'PROCESSED' || s.phase === 'ERROR' || s.phase === 'FAILED'
      );

      // Get last processed sentence
      const lastProcessed = sentences
        .filter((s: any) => s.coq_sid && (s.phase === 'PROCESSED' || s.phase === 'ERROR'))
        .pop();

      let goals: any = null;
      if (lastProcessed?.coq_sid) {
        const sid = lastProcessed.coq_sid;
        goals = doc.goals?.[sid] || doc.goals_raw?.[sid];
        
        if (goals === undefined && coqManager.coq?.goals) {
          coqManager.coq.goals(sid);
          await new Promise(resolve => setTimeout(resolve, 300));
          goals = doc.goals?.[sid] || doc.goals_raw?.[sid];
        }
      }

      // Collect messages from doc.messages (Check/Compute outputs)
      const messages: Array<{ level: 'info' | 'warning' | 'error'; text: string }> = [];
      
      if (doc.messages && Array.isArray(doc.messages)) {
        doc.messages.forEach((msg: any) => {
          if (msg) {
            let messageText = '';
            let messageLevel: 'info' | 'warning' | 'error' = 'info';
            
            if (msg.msg) {
              messageText = ppToString(msg.msg, coqManager);
            } else if (msg.text) {
              messageText = typeof msg.text === 'string' ? msg.text : ppToString(msg.text, coqManager);
            } else if (typeof msg === 'string') {
              messageText = msg;
            } else if (msg.content) {
              messageText = ppToString(msg.content, coqManager);
            }
            
            if (msg.level) {
              messageLevel = msg.level;
            } else if (msg.feedback_id) {
              const fid = msg.feedback_id;
              if (Array.isArray(fid) && fid.length > 0) {
                const fidStr = fid[0]?.toString() || '';
                if (fidStr.includes('error') || fidStr.includes('Error')) messageLevel = 'error';
                else if (fidStr.includes('warning') || fidStr.includes('Warning')) messageLevel = 'warning';
              }
            }
            
            if (messageText && messageText.trim()) {
              messages.push({ level: messageLevel, text: messageText.trim() });
            }
          }
        });
      }

      // Collect error messages from sentences
      sentences.forEach((s: any) => {
        if ((s.phase === 'ERROR' || s.phase === 'FAILED') && s.feedback) {
          s.feedback.forEach((fb: any) => {
            if (fb?.msg) {
              const text = ppToString(fb.msg, coqManager);
              if (text?.trim() && !messages.some(m => m.text === text.trim())) {
                messages.push({ level: 'error', text: text.trim() });
              }
            }
          });
        }
      });

      const hasError = sentences.some((s: any) => s.phase === 'ERROR' || s.phase === 'FAILED');
      const parsedState = parseJsCoqState(goals, coqManager, messages);

      return {
        ...parsedState,
        isComplete: allProcessed && !hasError,
        hasError,
      };
    } catch (error: any) {
      return {
        goals: [],
        hypotheses: [],
        messages: [{
          level: 'error',
          text: error.message || 'Failed to get goals and messages',
        }],
        isComplete: false,
        hasError: true,
      };
    }
  };

  const executeProof = async (_code: string): Promise<ProofState> => {
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

      const sentences = doc.sentences || [];
      
      // Process all sentences
      let maxIterations = sentences.length * 2;
      let iterations = 0;
      
      while (iterations < maxIterations) {
        const allProcessed = sentences.every((s: any) => 
          s.phase === 'PROCESSED' || s.phase === 'ERROR' || s.phase === 'FAILED'
        );
        
        if (allProcessed) break;
        
        if (coqManager.goNext) {
          coqManager.goNext(true);
        }
        
        await new Promise(resolve => setTimeout(resolve, 100));
        iterations++;
      }
      
      await new Promise(resolve => setTimeout(resolve, 300));
      
      return await getGoalsAndMessages();
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
    const coqManager = coqManagerRef.current;
    if (!coqManager?.provider) return '';
    
    // Get from current focus or first snippet
    const provider = coqManager.provider.currentFocus || coqManager.provider.snippets[0];
    if (provider) {
      return provider.getText();
    }
    return '';
  };

  const setEditorValue = (value: string): boolean => {
    const coqManager = coqManagerRef.current;
    if (!coqManager?.provider) return false;
    
    try {
      // Use provider.load() to set the content
      coqManager.provider.load(value);
      if (coqManager.work) {
        coqManager.work();
      }
      return true;
    } catch (error) {
      console.error('Error setting editor value:', error);
      return false;
    }
  };

  const setInitialCode = (code: string) => {
    initialCodeRef.current = code;
    const coqManager = coqManagerRef.current;
    if (!coqManager?.provider) return;
    
    // Use provider.load() method to set the code
    coqManager.provider.load(code);
    initialCodeRef.current = null;
  };

  return {
    isLoaded,
    isInitializing,
    executeProof,
    getEditorValue,
    setEditorValue,
    setInitialCode,
    coqManager: coqManagerRef.current,
  };
}

export function ppToString(pp: any, coqManager?: any): string {
  if (!pp) return '';
  if (typeof pp === 'string') return pp;
  
  if (coqManager?.pprint?.pp2DOM) {
    try {
      const $ = (window as any).$ || (globalThis as any).$;
      if ($) {
        const dom = coqManager.pprint.pp2DOM(pp);
        const text = dom.text() || dom.textContent || '';
        if (text.trim()) return text;
      }
    } catch (e) {
      // Fall through
    }
  }
  
  return extractStringFromPp(pp);
}

function extractStringFromPp(pp: any): string {
  if (typeof pp === 'string') return pp;
  if (!pp) return '';
  
  if (Array.isArray(pp)) {
    const tag = pp[0];
    
    if (tag === 'Pp_string' && pp.length >= 2) return pp[1];
    if (tag === 'Pp_glue' && pp.length >= 2 && Array.isArray(pp[1])) {
      return pp[1].map((elem: any) => extractStringFromPp(elem)).join('');
    }
    if (tag === 'Pp_box' && pp.length >= 3) return extractStringFromPp(pp[2]);
    if (tag === 'Pp_tag' && pp.length >= 3) return extractStringFromPp(pp[2]);
    if (tag === 'Pp_print_break' && pp.length >= 2) {
      return ' '.repeat(Math.max(0, pp[1] || 0));
    }
    if (tag === 'Pp_force_newline') return ' ';
    if (tag === 'Pp_empty') return '';
    
    const parts: string[] = [];
    for (let i = 0; i < pp.length; i++) {
      const part = extractStringFromPp(pp[i]);
      if (part) parts.push(part);
    }
    return parts.filter(p => p && typeof p === 'string' && !p.startsWith('Pp_')).join('');
  }
  
  return pp?.toString() || '';
}

function idToString(id: any, coqManager?: any): string {
  if (typeof id === 'string') return id;
  
  if (coqManager?.pprint) {
    const FormatPrettyPrint = (coqManager.pprint.constructor as any);
    if (FormatPrettyPrint?._idToString) {
      try {
        return FormatPrettyPrint._idToString(id);
      } catch (e) {
        // Fall through
      }
    }
  }
  
  if (Array.isArray(id)) {
    if (id.length >= 2 && typeof id[1] === 'string') return id[1];
    if (id.length >= 1) return id[0]?.toString() || '';
  }
  
  if (id && typeof id === 'object') {
    if (id.id) return id.id.toString();
    if (id.name) return id.name.toString();
    if (id.toString) return id.toString();
  }
  
  return id?.toString() || '';
}

export function parseJsCoqState(goals: any, coqManager: any, messagesData?: any[]): ProofState {
  try {
    const hypotheses: Array<{ name: string; type: string }> = [];
    const messages: Array<{ level: 'info' | 'warning' | 'error'; text: string }> = [];
    
    let goalsArray: any[] = [];
    
    // Extract goals from raw structure
    if (goals && typeof goals === 'object' && !goals.nodeType && goals.stack !== undefined) {
      if (Array.isArray(goals.stack)) {
        goals.stack.forEach((stackLevel: any) => {
          if (Array.isArray(stackLevel)) {
            stackLevel.forEach((goalGroup: any) => {
              if (Array.isArray(goalGroup)) {
                goalGroup.forEach((goal: any) => {
                  if (goal && typeof goal === 'object' && !Array.isArray(goal)) {
                    goalsArray.push(goal);
                  }
                });
              } else if (goalGroup && typeof goalGroup === 'object' && !Array.isArray(goalGroup)) {
                goalsArray.push(goalGroup);
              }
            });
          } else if (stackLevel && typeof stackLevel === 'object' && !Array.isArray(stackLevel)) {
            goalsArray.push(stackLevel);
          }
        });
      }
      
      if (Array.isArray(goals.goals) && goals.goals.length > 0) {
        goals.goals.forEach((goal: any) => {
          if (goal && typeof goal === 'object') goalsArray.push(goal);
        });
      }
    } else if (Array.isArray(goals)) {
      goalsArray = goals;
    } else if (goals && typeof goals === 'object') {
      if (goals.fg_goals) {
        goalsArray = Array.isArray(goals.fg_goals) ? goals.fg_goals : [goals.fg_goals];
      } else {
        goalsArray = [goals];
      }
    }
    
    // Parse goals
    const parsedGoals = goalsArray.map((goal: any, idx: number) => {
      const goalHyps: Array<{ name: string; type: string }> = [];
      let goalType = '';
      
      if (goal && typeof goal === 'object' && !goal.nodeType) {
        // Raw goal structure
        const hypsArray = goal.hyp;
        
        if (hypsArray && Array.isArray(hypsArray)) {
          [...hypsArray].reverse().forEach((hyp: any) => {
            if (hyp && Array.isArray(hyp) && hyp.length >= 3) {
              const h_names = hyp[0];
              const h_def = hyp[1];
              const h_type = hyp[2];
              
              const hypType = Array.isArray(h_type) ? ppToString(h_type, coqManager) : (h_type?.toString() || '');
              
              if (Array.isArray(h_names) && h_names.length > 0 && hypType) {
                h_names.forEach((nameId: any) => {
                  const hypName = idToString(nameId, coqManager);
                  
                  if (hypName && hypType) {
                    let fullType = hypType;
                    if (h_def) {
                      const defStr = Array.isArray(h_def) ? ppToString(h_def, coqManager) : h_def.toString();
                      if (defStr) {
                        fullType = `${hypName} := ${defStr} : ${hypType}`;
                      }
                    }
                    
                    goalHyps.push({ name: hypName, type: fullType });
                    if (!hypotheses.find(h => h.name === hypName)) {
                      hypotheses.push({ name: hypName, type: fullType });
                    }
                  }
                });
              }
            }
          });
        }
        
        if (goal.ty !== undefined) {
          goalType = ppToString(goal.ty, coqManager);
        } else if (goal.ccl !== undefined) {
          goalType = ppToString(goal.ccl, coqManager);
        } else if (goal.type !== undefined) {
          goalType = Array.isArray(goal.type) ? ppToString(goal.type, coqManager) : goal.type.toString();
        }
      }
      
      return {
        id: `goal-${idx + 1}`,
        type: goalType,
        context: goalHyps,
        rawGoal: goal,
        goalCountText: undefined as string | undefined,
      };
    });
    
    // Add messages
    if (messagesData && Array.isArray(messagesData)) {
      messagesData.forEach((msg: any) => {
        if (msg?.text && msg.text.trim()) {
          messages.push({
            level: msg.level || 'info',
            text: msg.text.trim(),
          });
        }
      });
    }
    
    const goalCount = parsedGoals.length;
    const goalCountText = goalCount === 1 ? '1 goal' : `${goalCount} goals`;
    
    parsedGoals.forEach((goal) => {
      if (!goal.goalCountText) {
        goal.goalCountText = goalCountText;
      }
    });
    
    return {
      goals: parsedGoals,
      hypotheses,
      messages,
      isComplete: parsedGoals.length === 0,
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
