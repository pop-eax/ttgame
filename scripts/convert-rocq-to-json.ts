#!/usr/bin/env npx tsx
/**
 * Convert Rocq .v world files to JSON format
 * 
 * Usage: npx tsx scripts/convert-rocq-to-json.ts <input.v> [output.json]
 */

import * as fs from 'fs';
import * as path from 'path';
import { parseRocqWorld, rocqToJsonWorld } from './rocqWorldParser';

function main() {
  const args = process.argv.slice(2);
  
  if (args.length === 0) {
    console.error('Usage: npx tsx scripts/convert-rocq-to-json.ts <input.v> [output.json]');
    process.exit(1);
  }
  
  const inputFile = args[0];
  const outputFile = args[1] || inputFile.replace(/\.v$/, '.json');
  
  if (!fs.existsSync(inputFile)) {
    console.error(`Error: File not found: ${inputFile}`);
    process.exit(1);
  }
  
  if (!inputFile.endsWith('.v')) {
    console.error(`Error: Input file must be a .v file: ${inputFile}`);
    process.exit(1);
  }
  
  try {
    const content = fs.readFileSync(inputFile, 'utf-8');
    const parsed = parseRocqWorld(content);
    
    if (!parsed) {
      throw new Error('Failed to parse Rocq world file');
    }
    
    const jsonWorld = rocqToJsonWorld(parsed);
    const jsonContent = JSON.stringify(jsonWorld, null, 2);
    
    fs.writeFileSync(outputFile, jsonContent, 'utf-8');
    
    console.log(`✓ Converted ${inputFile} to ${outputFile}`);
    console.log(`  World: ${jsonWorld.name}`);
    console.log(`  Levels: ${jsonWorld.levels.length}`);
  } catch (error) {
    console.error('Error converting file:', error);
    process.exit(1);
  }
}

main();

