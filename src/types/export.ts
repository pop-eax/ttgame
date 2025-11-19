import { ProofRecord } from './game';

export interface ExportData {
  exportVersion: string;
  exportedAt: string;
  studentInfo?: {
    name?: string;
    id?: string;
  };
  assignment?: {
    worldId: string;
    requiredLevels: string[];
  };
  proofs: Record<string, ProofRecord>;
  checksum: string;
}

