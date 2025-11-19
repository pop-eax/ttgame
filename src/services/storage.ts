import { GameData, ExportData } from '../types/game';
import { generateChecksum, verifyChecksum } from '../utils/checksum';
import { validateGameData } from '../utils/validators';

const STORAGE_KEY = 'rocq_game_data';
const CURRENT_VERSION = '1.0';

export class GameStorage {
  static save(data: GameData): void {
    try {
      const json = JSON.stringify(data);
      localStorage.setItem(STORAGE_KEY, json);
    } catch (error) {
      console.error('Failed to save game data:', error);
      throw new Error('Storage quota exceeded or localStorage unavailable');
    }
  }

  static load(): GameData | null {
    try {
      const json = localStorage.getItem(STORAGE_KEY);
      if (!json) return null;
      
      const data = JSON.parse(json) as GameData;
      
      if (!validateGameData(data)) {
        console.warn('Invalid game data structure, creating new');
        return null;
      }
      
      // Migrate if necessary
      if (data.version !== CURRENT_VERSION) {
        return this.migrate(data);
      }
      
      return data;
    } catch (error) {
      console.error('Failed to load game data:', error);
      return null;
    }
  }

  static exportJSON(options?: {
    studentName?: string;
    studentId?: string;
    worldId?: string;
    requiredLevels?: string[];
  }): string {
    const data = this.load();
    if (!data) throw new Error('No data to export');

    const exportData: ExportData = {
      exportVersion: CURRENT_VERSION,
      exportedAt: new Date().toISOString(),
      studentInfo: options?.studentName || options?.studentId ? {
        name: options.studentName,
        id: options.studentId,
      } : undefined,
      assignment: options?.worldId ? {
        worldId: options.worldId,
        requiredLevels: options.requiredLevels || [],
      } : undefined,
      proofs: data.proofs,
      checksum: '', // Will be calculated
    };

    // Calculate checksum
    exportData.checksum = generateChecksum(exportData);

    return JSON.stringify(exportData, null, 2);
  }

  static importJSON(json: string): boolean {
    try {
      const exportData = JSON.parse(json) as ExportData;
      
      // Verify checksum
      if (!verifyChecksum(exportData)) {
        throw new Error('Invalid checksum - data may be corrupted or tampered');
      }

      const currentData = this.load() || this.createEmpty();
      
      // Merge proofs
      currentData.proofs = {
        ...currentData.proofs,
        ...exportData.proofs,
      };

      // Update completed levels
      const completedLevels = Object.keys(exportData.proofs).filter(
        levelId => exportData.proofs[levelId].correct
      );
      currentData.progress.completedLevels = [
        ...new Set([...currentData.progress.completedLevels, ...completedLevels])
      ];

      this.save(currentData);
      return true;
    } catch (error) {
      console.error('Failed to import data:', error);
      return false;
    }
  }

  static clear(): void {
    localStorage.removeItem(STORAGE_KEY);
  }

  static createEmpty(): GameData {
    return {
      version: CURRENT_VERSION,
      user: {
        id: crypto.randomUUID(),
        createdAt: new Date().toISOString(),
        lastActive: new Date().toISOString(),
      },
      progress: {
        completedLevels: [],
        currentWorld: 'world0',
        currentLevel: '0.1',
        xp: 0,
        level: 1,
      },
      proofs: {},
      unlockedTactics: [],
      achievements: {},
      settings: {
        theme: 'light',
        fontSize: 14,
        autoSave: true,
      },
    };
  }

  private static migrate(data: GameData): GameData {
    // Handle version migrations here
    return { ...data, version: CURRENT_VERSION };
  }
}

