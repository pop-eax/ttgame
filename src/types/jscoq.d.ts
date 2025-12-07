// Type definitions for jsCoq library based on actual source code
// Generated from: node_modules/jscoq/frontend/classic/js/

declare module 'jscoq' {
  import type CodeMirror from 'codemirror';

  export interface JsCoqInstance {
    backend: string;
    base_path: string;
    start(...args: any[]): Promise<CoqManager>;
    globalConfig(v?: any): any;
    _getopts(method: string, ...args: any[]): { jscoq_ids: string[], jscoq_opts: any };
  }

  export interface CmCoqProvider {
    idx: number;
    filename?: string;
    dirty: boolean;
    editor: CodeMirror.Editor;
    lineCount: number;
    getText(): string;
    load(text: string, filename?: string, dirty?: boolean): void;
    openFile(file: File): Promise<string>;
    openLocal(filename: string): void;
    focus(): void;
    getNext(prev: any, until?: any): any;
    getAtPoint(): any;
    getCursor(): any;
    mark(stm: any, mark_type: string, loc_focus?: any): void;
    highlight(stm: any, flag: boolean): void;
    retract(): void;
    cursorToStart(stm: any): void;
    cursorToEnd(stm: any): void;
    configure(options: any): void;
  }

  export interface ProviderContainer {
    options: any;
    snippets: CmCoqProvider[];
    currentFocus: CmCoqProvider;
    wait_for: any;
    onChange?: (cm: any, change: any) => void;
    onInvalidate?: (evt: any) => void;
    onMouseEnter?: (stm: any, evt: any) => void;
    onMouseLeave?: (stm: any, evt: any) => void;
    onTipHover?: (entries: any, zoom: any) => void;
    onTipOut?: (evt: any) => void;
    onResize?: (evt: any) => void;
    onAction?: (evt: any) => void;
    load(text: string, filename?: string, dirty?: boolean): void;
    openFile(file: File): void;
    openLocal(filename: string): void;
    focus(): void;
    getNext(prev: any, until?: any): any;
    getAtPoint(): any;
    getCursor(): any;
    mark(stm: any, mark: string, loc_focus?: any): void;
    highlight(stm: any, flag: boolean): void;
    retract(): void;
    cursorToStart(stm: any): void;
    cursorToEnd(stm: any): void;
    configure(options: any): void;
    renumber(startIndex: number): Promise<void>;
    yield(): Promise<void>;
    findElements(elementRefs: any): HTMLElement[];
  }

  export interface CoqWorker {
    goals(sid: number): void;
    cancel(sid: number): void;
    [key: string]: any;
  }

  export interface ManagerSentence {
    text: string;
    coq_sid: number;
    flags: object;
    sp: CmCoqProvider;
    phase: any;
  }

  export interface CoqDocument {
    fresh_id: number;
    sentences: ManagerSentence[];
    stm_id: ManagerSentence[];
    goals: any[];
    goals_raw?: Record<number, any>;
    messages?: any[];
  }

  export interface CoqManager {
    options: any;
    provider: ProviderContainer;
    doc: CoqDocument;
    coq: CoqWorker | null;
    layout: any;
    pprint: any;
    packages: any;
    contextual_info: any;
    company_coq?: any;
    completion?: any;
    markup?: any;
    observe?: any;
    error: any[];
    navEnabled: boolean;
    when_ready: any;
    
    // Methods
    launch(): Promise<void>;
    work(): void;
    goNext(forward: boolean): void;
    goCursor(): void;
    lastAdded(): ManagerSentence | null;
    updateGoals(goals: any): void;
    coqGoalInfo?(sid: number, rawGoals: any): any;
    [key: string]: any;
  }

  export const JsCoq: JsCoqInstance;
  export { CoqManager };
}

