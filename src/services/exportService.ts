import { GameStorage } from './storage';

export function downloadExport(options?: {
  studentName?: string;
  studentId?: string;
  worldId?: string;
  requiredLevels?: string[];
}): void {
  try {
    const json = GameStorage.exportJSON(options);
    const blob = new Blob([json], { type: 'application/json' });
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.href = url;
    a.download = `rocq_progress_${new Date().toISOString().split('T')[0]}.json`;
    document.body.appendChild(a);
    a.click();
    document.body.removeChild(a);
    URL.revokeObjectURL(url);
  } catch (error) {
    console.error('Failed to export:', error);
    throw error;
  }
}

export function importFromFile(file: File): Promise<boolean> {
  return new Promise((resolve, reject) => {
    const reader = new FileReader();
    reader.onload = (e) => {
      try {
        const json = e.target?.result as string;
        const success = GameStorage.importJSON(json);
        resolve(success);
      } catch (error) {
        reject(error);
      }
    };
    reader.onerror = () => reject(new Error('Failed to read file'));
    reader.readAsText(file);
  });
}

