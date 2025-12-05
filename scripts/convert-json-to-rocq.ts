#!/usr/bin/env ts-node
/**
 * Convert JSON world files to Rocq format
 * 
 * Usage: npx ts-node scripts/convert-json-to-rocq.ts <input.json> [output.v]
 */

import * as fs from 'fs';
import * as path from 'path';

interface World {
  id: string;
  name: string;
  description: string;
  order: number;
  icon?: string;
  color?: string;
  estimatedHours?: number;
  tags?: string[];
  availableTheorems?: string[];
  levels: Level[];
}

interface Level {
  id: string;
  name: string;
  description: string;
  difficulty: number;
  estimatedTime?: number;
  objective: string;
  theory?: {
    markdown: string;
    examples?: Array<{ title: string; code: string }>;
  };
  startingCode: string;
  solution: string;
  hints: string[];
  unlockedTactics?: string[];
  rewards?: {
    xp?: number;
    achievements?: string[];
  };
}

function escapeJsonForComment(json: any): string {
  return JSON.stringify(json, null, 2).replace(/\*\//g, '* /');
}

function convertWorldToRocq(world: World): string {
  const lines: string[] = [];
  
  // World metadata
  const worldMeta = {
    id: world.id,
    name: world.name,
    description: world.description,
    order: world.order,
    ...(world.icon && { icon: world.icon }),
    ...(world.color && { color: world.color }),
    ...(world.estimatedHours && { estimatedHours: world.estimatedHours }),
    ...(world.tags && world.tags.length > 0 && { tags: world.tags }),
    ...(world.availableTheorems && world.availableTheorems.length > 0 && { availableTheorems: world.availableTheorems }),
  };
  
  lines.push(`(*@WORLD: ${escapeJsonForComment(worldMeta)}*)`);
  lines.push('');
  
  // Convert each level
  for (const level of world.levels) {
    lines.push('(*===========================================*)');
    lines.push(`(*@LEVEL: ${level.id}*)`);
    
    // Level metadata
    const levelMeta = {
      id: level.id,
      name: level.name,
      description: level.description,
      difficulty: level.difficulty,
      ...(level.estimatedTime && { estimatedTime: level.estimatedTime }),
      objective: level.objective,
      hints: level.hints.length === 3 ? level.hints : [
        ...level.hints,
        ...Array(3 - level.hints.length).fill('Complete the exercise'),
      ].slice(0, 3) as [string, string, string],
      ...(level.unlockedTactics && level.unlockedTactics.length > 0 && { unlockedTactics: level.unlockedTactics }),
      ...(level.rewards && { rewards: level.rewards }),
    };
    
    lines.push(`(*@LEVEL_META: ${escapeJsonForComment(levelMeta)}*)`);
    lines.push('');
    
    // Theory section
    if (level.theory) {
      lines.push('(*@THEORY:');
      lines.push(level.theory.markdown);
      
      if (level.theory.examples && level.theory.examples.length > 0) {
        lines.push('');
        for (const example of level.theory.examples) {
          lines.push(`(*@EXAMPLE: ${example.title}`);
          lines.push(example.code);
          lines.push('*)');
          lines.push('');
        }
      }
      
      lines.push('*)');
      lines.push('');
    }
    
    // Starting code
    lines.push('(*@START:');
    lines.push(level.startingCode);
    lines.push('*)');
    lines.push('');
    
    // Solution
    lines.push('(*@SOLUTION:');
    lines.push(level.solution);
    lines.push('*)');
    lines.push('');
  }
  
  return lines.join('\n');
}

function main() {
  const args = process.argv.slice(2);
  
  if (args.length === 0) {
    console.error('Usage: npx ts-node scripts/convert-json-to-rocq.ts <input.json> [output.v]');
    process.exit(1);
  }
  
  const inputFile = args[0];
  const outputFile = args[1] || inputFile.replace(/\.json$/, '.v');
  
  if (!fs.existsSync(inputFile)) {
    console.error(`Error: File not found: ${inputFile}`);
    process.exit(1);
  }
  
  try {
    const jsonContent = fs.readFileSync(inputFile, 'utf-8');
    const world: World = JSON.parse(jsonContent);
    
    const rocqContent = convertWorldToRocq(world);
    
    fs.writeFileSync(outputFile, rocqContent, 'utf-8');
    
    console.log(`✓ Converted ${inputFile} to ${outputFile}`);
    console.log(`  World: ${world.name}`);
    console.log(`  Levels: ${world.levels.length}`);
  } catch (error) {
    console.error('Error converting file:', error);
    process.exit(1);
  }
}

if (require.main === module) {
  main();
}

