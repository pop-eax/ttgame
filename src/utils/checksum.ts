import { ExportData } from '../types/export';

export function generateChecksum(data: ExportData): string {
  // Create a stable string representation (excluding checksum field)
  const { checksum, ...dataToHash } = data;
  const jsonString = JSON.stringify(dataToHash, Object.keys(dataToHash).sort());
  
  // Simple hash for demo - use proper SHA-256 in production
  return hashString(jsonString);
}

export function verifyChecksum(data: ExportData): boolean {
  const providedChecksum = data.checksum;
  const calculatedChecksum = generateChecksum(data);
  return providedChecksum === calculatedChecksum;
}

// Synchronous hash function
function hashString(str: string): string {
  let hash = 0;
  for (let i = 0; i < str.length; i++) {
    const char = str.charCodeAt(i);
    hash = ((hash << 5) - hash) + char;
    hash = hash & hash;
  }
  return hash.toString(16);
}

