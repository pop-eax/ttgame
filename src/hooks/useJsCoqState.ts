import { useState, useEffect, useRef, useCallback } from 'react';
import { ProofState } from '../types/proof';
import { parseJsCoqState, ppToString } from './useJsCoq';
import type { CoqManager } from 'jscoq';

// Filter query panel messages to only show meaningful results (Check/Compute outputs)
function filterQueryMessages(text: string): string | null {
  if (!text || text.trim().length === 0) return null;
  
  const lines = text.split('\n').filter(line => {
    const trimmed = line.trim();
    if (!trimmed) return false;
    
    if (trimmed.includes('["Put",') || 
        trimmed.includes('["Init",') ||
        trimmed.includes('["NewDoc",') ||
        trimmed.includes('["Add",') ||
        trimmed.includes('["Query",') ||
        trimmed.includes('["Cancel",') ||
        trimmed.includes(' loaded.') ||
        trimmed.includes('["Exec",') && trimmed.length < 20) {
      return false;
    }
    
    if (trimmed.includes(':') || trimmed.includes('=') || trimmed.match(/^\s*[a-zA-Z_][a-zA-Z0-9_]*\s*:/)) {
      return true;
    }
    
    if (trimmed.startsWith('[') && trimmed.includes('"')) {
      return false;
    }
    
    return false;
  });
  
  const execMatches = text.match(/\["Exec",\d+\]([^\[]+)/g);
  if (execMatches && execMatches.length > 0) {
    const results = execMatches.map(match => {
      const result = match.replace(/\["Exec",\d+\]/, '').trim();
      return result;
    }).filter(r => r.length > 0 && !r.includes('["Put",') && !r.includes('["Init",'));
    
    if (results.length > 0) {
      return results.join('\n');
    }
  }
  
  if (lines.length > 0) {
    return lines.join('\n');
  }
  
  return null;
}

function readMessagesFromDoc(doc: any, coqManager: CoqManager, processedMessages: Set<string>): Array<{ level: 'info' | 'warning' | 'error'; text: string }> {
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
          const trimmedText = messageText.trim();
          if (!processedMessages.has(trimmedText)) {
            messages.push({ level: messageLevel, text: trimmedText });
            processedMessages.add(trimmedText);
          }
        }
      }
    });
  }
  
  return messages;
}

function readMessagesFromQueryPanel(
  coqManager: CoqManager, 
  previousQueryTextLength: { current: number },
  processedMessages: Set<string>
): Array<{ level: 'info' | 'warning' | 'error'; text: string }> {
  const messages: Array<{ level: 'info' | 'warning' | 'error'; text: string }> = [];
  
  const querySelectors = [
    '#query-panel',
    '.query-panel',
    '[id*="query"]',
    '.jscoq-query',
    '.coq-query'
  ];
  
  let queryPanelEl: HTMLElement | null = null;
  for (const selector of querySelectors) {
    const el = document.querySelector(selector) as HTMLElement;
    if (el) {
      queryPanelEl = el;
      break;
    }
  }
  
  if (!queryPanelEl && coqManager.layout && coqManager.layout.query) {
    const queryPanel = coqManager.layout.query;
    if (queryPanel.content) {
      queryPanelEl = queryPanel.content as HTMLElement;
    }
  }
  
  if (queryPanelEl) {
    const fullQueryText = queryPanelEl.textContent?.trim() || queryPanelEl.innerText?.trim() || '';
    if (fullQueryText.length > previousQueryTextLength.current) {
      const newText = fullQueryText.substring(previousQueryTextLength.current);
      const filteredText = filterQueryMessages(newText);
      if (filteredText && !processedMessages.has(filteredText)) {
        messages.push({ text: filteredText, level: 'info' });
        processedMessages.add(filteredText);
      }
      previousQueryTextLength.current = fullQueryText.length;
    }
  }
  
  return messages;
}

export function useJsCoqState(coqManager: CoqManager | null, isLoaded: boolean) {
  const [goalState, setGoalState] = useState<ProofState | null>(null);
  const goalStateRef = useRef<ProofState | null>(null);
  const previousQueryTextLengthRef = useRef<number>(0);
  const processedMessagesRef = useRef<Set<string>>(new Set());
  const allMessagesRef = useRef<Array<{ level: 'info' | 'warning' | 'error'; text: string }>>([]);
  const displayedMessagesCountRef = useRef<number>(0);
  const goalUpdateTimeoutRef = useRef<number | null>(null);
  const isProcessingGoalsRef = useRef(false);
  const originalUpdateGoalsRef = useRef<((goals: any) => void) | null>(null);
  const originalCoqGoalInfoRef = useRef<((sid: number, rawGoals: any) => any) | null>(null);
  const messageCheckIntervalRef = useRef<number | null>(null);

  // Update ref when goalState changes
  useEffect(() => {
    goalStateRef.current = goalState;
  }, [goalState]);

  const readGoalsAndMessages = useCallback((): { goals: any; messages: Array<{ level: 'info' | 'warning' | 'error'; text: string }> } => {
    if (!coqManager) {
      return { goals: null, messages: [] };
    }

    const doc = coqManager.doc;
    if (!doc) {
      return { goals: null, messages: [] };
    }

    let goalData: any = null;
    const messagesData: Array<{ level: 'info' | 'warning' | 'error'; text: string }> = [];

    const lastAdded = coqManager.lastAdded?.();
    if (lastAdded && lastAdded.coq_sid) {
      const sid = lastAdded.coq_sid;
      goalData = doc.goals_raw?.[sid] || doc.goals?.[sid];
    }

    // Read messages from doc.messages
    const docMessages = readMessagesFromDoc(doc, coqManager, processedMessagesRef.current);
    messagesData.push(...docMessages);

    // Read messages from query panel
    const queryMessages = readMessagesFromQueryPanel(coqManager, previousQueryTextLengthRef, processedMessagesRef.current);
    messagesData.push(...queryMessages);

    return { goals: goalData, messages: messagesData };
  }, [coqManager]);

  const updateState = useCallback((goalData: any, newMessages: Array<{ level: 'info' | 'warning' | 'error'; text: string }>) => {
    // Add new messages to our single source of truth
    newMessages.forEach(newMsg => {
      if (!allMessagesRef.current.some(m => m.text === newMsg.text)) {
        allMessagesRef.current.push(newMsg);
      }
    });

    // Only show messages that are NEW (beyond what we've already displayed)
    const currentMessagesCount = allMessagesRef.current.length;
    const newMessagesCount = currentMessagesCount - displayedMessagesCountRef.current;

    let messagesToDisplay: Array<{ level: 'info' | 'warning' | 'error'; text: string }> = [];

    if (newMessagesCount > 0) {
      messagesToDisplay = allMessagesRef.current.slice(displayedMessagesCountRef.current);
      displayedMessagesCountRef.current = currentMessagesCount;
    } else if (goalData !== undefined) {
      // No new messages, but we have goal updates - clear messages (user has read them)
      messagesToDisplay = [];
    }

    // Only update state if we have goals or new messages
    if (goalData !== undefined || messagesToDisplay.length > 0) {
      const state = parseJsCoqState(goalData, coqManager, messagesToDisplay);
      setGoalState(state);
      return true;
    }

    return false;
  }, [coqManager]);

  // Hook into jsCoq's goal updates
  useEffect(() => {
    if (!coqManager || !isLoaded) return;

    try {
      if (originalCoqGoalInfoRef.current || originalUpdateGoalsRef.current) {
        return;
      }

      // Hook into coqGoalInfo to capture raw goals
      if ((coqManager as any).coqGoalInfo) {
        originalCoqGoalInfoRef.current = (coqManager as any).coqGoalInfo.bind(coqManager);
        (coqManager as any).coqGoalInfo = function(sid: number, rawGoals: any) {
          if (coqManager.doc) {
            if (!coqManager.doc.goals_raw) {
              coqManager.doc.goals_raw = {};
            }
            coqManager.doc.goals_raw[sid] = rawGoals;
          }
          if (originalCoqGoalInfoRef.current) {
            return originalCoqGoalInfoRef.current(sid, rawGoals);
          }
        };
      }

      // Hook into updateGoals
      const originalUpdateGoals = (coqManager as any).updateGoals;
      if (originalUpdateGoals && typeof originalUpdateGoals === 'function') {
        originalUpdateGoalsRef.current = originalUpdateGoals.bind(coqManager);
        (coqManager as any).updateGoals = function(goals: any) {
          if (originalUpdateGoalsRef.current) {
            originalUpdateGoalsRef.current(goals);
          }

          if (goalUpdateTimeoutRef.current !== null) {
            clearTimeout(goalUpdateTimeoutRef.current);
            goalUpdateTimeoutRef.current = null;
          }

          goalUpdateTimeoutRef.current = window.setTimeout(() => {
            if (isProcessingGoalsRef.current) return;

            isProcessingGoalsRef.current = true;

            const parseAndUpdate = () => {
              try {
                const { goals: goalData, messages: messagesData } = readGoalsAndMessages();
                if (goalData === undefined && messagesData.length === 0) {
                  isProcessingGoalsRef.current = false;
                  return;
                }

                updateState(goalData, messagesData);
              } catch (error) {
                // Silently fail
              } finally {
                isProcessingGoalsRef.current = false;
              }
            };

            if (typeof (window as any).requestIdleCallback === 'function') {
              (window as any).requestIdleCallback(parseAndUpdate, { timeout: 50 });
            } else {
              setTimeout(parseAndUpdate, 0);
            }
          }, 100);
        };
      }

      // Set up interval to check for messages
      messageCheckIntervalRef.current = window.setInterval(() => {
        try {
          const { messages: messagesData } = readGoalsAndMessages();
          if (messagesData.length > 0) {
            updateState(undefined, messagesData);
          }
        } catch (error) {
          // Silently fail
        }
      }, 500);

      return () => {
        if (messageCheckIntervalRef.current !== null) {
          clearInterval(messageCheckIntervalRef.current);
          messageCheckIntervalRef.current = null;
        }
        if (goalUpdateTimeoutRef.current !== null) {
          clearTimeout(goalUpdateTimeoutRef.current);
          goalUpdateTimeoutRef.current = null;
        }
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
  }, [coqManager, isLoaded, readGoalsAndMessages, updateState]);

  const reset = useCallback(() => {
    previousQueryTextLengthRef.current = 0;
    processedMessagesRef.current = new Set();
    allMessagesRef.current = [];
    displayedMessagesCountRef.current = 0;
  }, []);

  return {
    goalState,
    reset,
  };
}

