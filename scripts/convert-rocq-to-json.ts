#!/usr/bin/env npx tsx
/**
 * Convert Rocq .v world files to JSON format
 * 
 * Usage: 
 *   npx tsx scripts/convert-rocq-to-json.ts <input.v> [output.json]
 *   npx tsx scripts/convert-rocq-to-json.ts <directory> [output.json]
 */

import * as fs from 'fs';
import * as path from 'path';
import { parseRocqWorld, rocqToJsonWorld, ParsedRocqWorld } from './rocqWorldParser';

function convertDirectory(dirPath: string): ParsedRocqWorld | null {
  const files = fs.readdirSync(dirPath)
    .filter(f => f.endsWith('.v'))
    .sort()
    .map(f => path.join(dirPath, f));
  
  if (files.length === 0) {
    throw new Error(`No .v files found in directory: ${dirPath}`);
  }
  
  // Merge all file contents into one string
  const fileContents: string[] = [];
  
  for (const file of files) {
    const content = fs.readFileSync(file, 'utf-8');
    fileContents.push(content);
  }
  
  // Join all contents with newlines
  const mergedContent = fileContents.join('\n\n');
  
  // Parse the merged content as a single world
  const parsed = parseRocqWorld(mergedContent);
  
  if (!parsed) {
    throw new Error('Failed to parse merged world files');
  }
  
  return parsed;
}

function main() {
  const args = process.argv.slice(2);
  
  if (args.length === 0) {
    console.error('Usage: npx tsx scripts/convert-rocq-to-json.ts <input.v|directory> [output.json]');
    process.exit(1);
  }
  
  const inputPath = args[0];
  let outputFile = args[1];
  
  if (!fs.existsSync(inputPath)) {
    console.error(`Error: Path not found: ${inputPath}`);
    process.exit(1);
  }
  
  const stats = fs.statSync(inputPath);
  let parsed: ParsedRocqWorld | null = null;
  
  try {
    if (stats.isDirectory()) {
      // Handle directory
      parsed = convertDirectory(inputPath);
      
      if (!outputFile) {
        const dirName = path.basename(inputPath);
        outputFile = path.join(inputPath, '..', `${dirName}.json`);
      }
    } else if (stats.isFile()) {
      // Handle single file
      if (!inputPath.endsWith('.v')) {
        console.error(`Error: Input file must be a .v file: ${inputPath}`);
        process.exit(1);
      }
      
      const content = fs.readFileSync(inputPath, 'utf-8');
      parsed = parseRocqWorld(content);
      
      if (!outputFile) {
        outputFile = inputPath.replace(/\.v$/, '.json');
      }
    } else {
      console.error(`Error: Input must be a file or directory: ${inputPath}`);
      process.exit(1);
    }
    
    if (!parsed) {
      throw new Error('Failed to parse Rocq world file(s)');
    }
    
    const jsonWorld = rocqToJsonWorld(parsed);
    const jsonContent = JSON.stringify(jsonWorld, null, 2);
    
    fs.writeFileSync(outputFile, jsonContent, 'utf-8');
    
    console.log(`✓ Converted ${stats.isDirectory() ? 'directory' : 'file'} to ${outputFile}`);
    console.log(`  World: ${jsonWorld.name}`);
    console.log(`  Levels: ${jsonWorld.levels.length}`);
  } catch (error) {
    console.error('Error converting:', error);
    process.exit(1);
  }
}

main();

