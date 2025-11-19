declare module 'jscoq' {
  export interface JsCoqInstance {
    start(...args: any[]): Promise<CoqManager>;
    base_path: string;
    [key: string]: any;
  }
  
  export interface CoqManager {
    execute(code: string): Promise<any>;
    goals: any[];
    messages: any[];
    work(): void;
    goCursor(): void;
    goNext(forward: boolean): void;
    lastAdded(): any;
    coq?: {
      goals(sid: number): void;
      [key: string]: any;
    };
    doc: {
      goals: any[];
      sentences: any[];
      [key: string]: any;
    };
    provider: {
      mark(stm: any, status: string): void;
      getAtPoint(): any;
      getCursor(): any;
      editor?: {
        setValue(value: string): void;
        setCursor(pos: any): void;
        posFromIndex(index: number): any;
        getValue(): string;
      };
      [key: string]: any;
    };
    [key: string]: any;
  }
  
  export const JsCoq: JsCoqInstance;
  export { CoqManager };
}
