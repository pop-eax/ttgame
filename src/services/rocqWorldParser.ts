/**
 * Parser for Rocq-based world configuration files
 * 
 * Format:
 * - World metadata in comments: (*@WORLD: { ... }*)
 * - Level markers: (*@LEVEL: levelId*)
 * - Level metadata: (*@LEVEL_META: { ... }*)
 * - Theory sections: (*@THEORY: ... *)
 * - Examples: (*@EXAMPLE: title ... *)
 * - Starting code: (*@START: ... *)
 * - Solution: (*@SOLUTION: ... *)
 * - Hints: (*@HINT: ... *)
 */

export interface RocqWorldMetadata {
  id: string;
  name: string;
  description: string;
  order: number;
  icon?: string;
  color?: string;
  estimatedHours?: number;
  tags?: string[];
  availableTheorems?: string[];
}

export interface RocqLevelMetadata {
  id: string;
  name: string;
  description: string;
  difficulty: 1 | 2 | 3 | 4 | 5;
  estimatedTime?: number;
  objective: string;
  hints: [string, string, string];
  unlockedTactics?: string[];
  rewards?: {
    xp?: number;
    achievements?: string[];
  };
}

export interface ParsedRocqWorld {
  metadata: RocqWorldMetadata;
  levels: ParsedRocqLevel[];
}

export interface ParsedRocqLevel {
  metadata: RocqLevelMetadata;
  theory?: {
    markdown: string;
    examples?: Array<{ title: string; code: string }>;
  };
  startingCode: string;
  solution: string;
  code?: string; // Full code context for the level
}

/**
 * Parse a Rocq file into a world structure
 */
export function parseRocqWorld(content: string): ParsedRocqWorld | null {
  try {
    // Extract world metadata
    const worldMetaMatch = content.match(/\(\*@WORLD:\s*(\{[\s\S]*?\})\s*\*\)/);
    if (!worldMetaMatch) {
      throw new Error('World metadata not found');
    }
    const worldMetadata: RocqWorldMetadata = JSON.parse(worldMetaMatch[1]);

    // Split content by level markers
    const levelRegex = /\(\*@LEVEL:\s*([^\s*]+)\s*\*\)/g;
    const levels: ParsedRocqLevel[] = [];
    let lastIndex = 0;
    let match;

    while ((match = levelRegex.exec(content)) !== null) {
      const levelId = match[1];
      const levelStart = match.index;
      
      // Find the next level or end of file
      levelRegex.lastIndex = match.index + match[0].length;
      const nextMatch = levelRegex.exec(content);
      const levelEnd = nextMatch ? nextMatch.index : content.length;
      levelRegex.lastIndex = match.index + match[0].length; // Reset for next iteration
      
      const levelContent = content.substring(levelStart, levelEnd);
      const parsedLevel = parseLevel(levelId, levelContent);
      if (parsedLevel) {
        levels.push(parsedLevel);
      }
    }

    return {
      metadata: worldMetadata,
      levels,
    };
  } catch (error) {
    console.error('Error parsing Rocq world:', error);
    return null;
  }
}

function parseLevel(levelId: string, content: string): ParsedRocqLevel | null {
  try {
    // Extract level metadata
    const metaMatch = content.match(/\(\*@LEVEL_META:\s*(\{[\s\S]*?\})\s*\*\)/);
    if (!metaMatch) {
      throw new Error(`Level metadata not found for level ${levelId}`);
    }
    const metadata: RocqLevelMetadata = JSON.parse(metaMatch[1]);
    
    if (metadata.id !== levelId) {
      metadata.id = levelId; // Ensure consistency
    }

    // Extract theory
    let theory: ParsedRocqLevel['theory'] | undefined;
    const theoryMatch = content.match(/\(\*@THEORY:\s*([\s\S]*?)\s*\*\)/);
    if (theoryMatch) {
      const theoryContent = theoryMatch[1].trim();
      const examples: Array<{ title: string; code: string }> = [];
      
      // Extract examples
      const exampleRegex = /\(\*@EXAMPLE:\s*([^\n*]+)\s*([\s\S]*?)\s*\*\)/g;
      let exampleMatch;
      while ((exampleMatch = exampleRegex.exec(theoryContent)) !== null) {
        examples.push({
          title: exampleMatch[1].trim(),
          code: exampleMatch[2].trim(),
        });
      }
      
      // Remove examples from theory markdown
      const theoryMarkdown = theoryContent.replace(/\(\*@EXAMPLE:[\s\S]*?\*\)/g, '').trim();
      
      theory = {
        markdown: theoryMarkdown,
        examples: examples.length > 0 ? examples : undefined,
      };
    }

    // Extract starting code
    const startMatch = content.match(/\(\*@START:\s*([\s\S]*?)\s*\*\)/);
    if (!startMatch) {
      throw new Error(`Starting code not found for level ${levelId}`);
    }
    const startingCode = startMatch[1].trim();

    // Extract solution
    const solutionMatch = content.match(/\(\*@SOLUTION:\s*([\s\S]*?)\s*\*\)/);
    if (!solutionMatch) {
      throw new Error(`Solution not found for level ${levelId}`);
    }
    const solution = solutionMatch[1].trim();

    // Extract code context (everything between START and SOLUTION, or after SOLUTION)
    const codeStart = startMatch.index! + startMatch[0].length;
    const codeEnd = solutionMatch.index!;
    const code = content.substring(codeStart, codeEnd).trim();

    return {
      metadata,
      theory,
      startingCode,
      solution,
      code: code || undefined,
    };
  } catch (error) {
    console.error(`Error parsing level ${levelId}:`, error);
    return null;
  }
}

/**
 * Convert parsed Rocq world to JSON world format
 */
export function rocqToJsonWorld(parsed: ParsedRocqWorld): any {
  return {
    id: parsed.metadata.id,
    name: parsed.metadata.name,
    description: parsed.metadata.description,
    order: parsed.metadata.order,
    icon: parsed.metadata.icon,
    color: parsed.metadata.color,
    estimatedHours: parsed.metadata.estimatedHours,
    tags: parsed.metadata.tags,
    availableTheorems: parsed.metadata.availableTheorems,
    levels: parsed.levels.map(level => ({
      id: level.metadata.id,
      name: level.metadata.name,
      description: level.metadata.description,
      difficulty: level.metadata.difficulty,
      estimatedTime: level.metadata.estimatedTime,
      objective: level.metadata.objective,
      theory: level.theory,
      startingCode: level.startingCode,
      solution: level.solution,
      hints: level.metadata.hints,
      unlockedTactics: level.metadata.unlockedTactics,
      rewards: level.metadata.rewards,
    })),
  };
}

/**
 * Load and parse a Rocq world file
 */
export async function loadRocqWorld(filename: string): Promise<ParsedRocqWorld | null> {
  try {
    const response = await fetch(`/worlds/${filename}`);
    if (!response.ok) {
      throw new Error(`Failed to load Rocq world: ${response.statusText}`);
    }
    const content = await response.text();
    return parseRocqWorld(content);
  } catch (error) {
    console.error(`Error loading Rocq world ${filename}:`, error);
    return null;
  }
}

