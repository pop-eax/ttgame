import { useState } from 'react';
import { Link } from 'react-router-dom';
import { User, Download, Upload, HelpCircle, Moon, Sun } from 'lucide-react';
import { useGame } from '../../context/GameContext';
import { useTheme } from '../../context/ThemeContext';
import { downloadExport, importFromFile } from '../../services/exportService';
import { Modal } from '../common/Modal';
import toast from 'react-hot-toast';

export function Header() {
  const { gameData } = useGame();
  const { theme, toggleTheme } = useTheme();
  const [showUserMenu, setShowUserMenu] = useState(false);
  const [showImportModal, setShowImportModal] = useState(false);

  const handleExport = () => {
    try {
      downloadExport();
      toast.success('Progress exported successfully!');
    } catch (error) {
      toast.error('Failed to export progress');
    }
  };

  const handleImport = async (file: File) => {
    try {
      const success = await importFromFile(file);
      if (success) {
        toast.success('Progress imported successfully!');
        setShowImportModal(false);
        window.location.reload();
      } else {
        toast.error('Failed to import progress');
      }
    } catch (error) {
      toast.error('Failed to import progress');
    }
  };

  return (
    <header className="bg-white border-gray-200 sticky top-0 z-40">
      <div className="max-w-7xl mx-auto px-4 py-3 flex items-center justify-between">
        <Link to="/" className="flex items-center space-x-2">
          <span className="text-2xl font-bold text-primary-600 dark:text-primary-400">Rocq Type Theory Game</span>
        </Link>

        <nav className="flex items-center space-x-4">
          <button
            onClick={toggleTheme}
            className="p-2 rounded-lg text-gray-600 hover:text-gray-900 hover:bg-gray-100 dark:hover:bg-gray-800 dark:text-gray-300"
            aria-label="Toggle theme"
          >
            {theme === 'dark' ? <Sun size={20} /> : <Moon size={20} />}
          </button>
          
          <Link to="/help" className="text-gray-600 hover:text-gray-900 dark:text-gray-300 dark:hover:text-gray-100">
            <HelpCircle size={20} />
          </Link>
          
          <div className="relative">
            <button
              onClick={() => setShowUserMenu(!showUserMenu)}
              className="flex items-center space-x-2 text-gray-600 dark:text-gray-300 hover:text-gray-900 dark:hover:text-gray-100"
            >
              <User size={20} />
              {gameData && (
                <span className="text-sm">
                  Level {gameData.progress.level} | {gameData.progress.xp} XP
                </span>
              )}
            </button>

            {showUserMenu && (
              <div className="absolute right-0 mt-2 w-48 bg-white dark:bg-gray-800 rounded-lg shadow-lg border border-gray-200 dark:border-gray-700 py-1">
                <button
                  onClick={handleExport}
                  className="w-full text-left px-4 py-2 text-sm text-gray-700 dark:text-gray-300 hover:bg-gray-100 dark:hover:bg-gray-700 flex items-center space-x-2"
                >
                  <Download size={16} />
                  <span>Export Progress</span>
                </button>
                <button
                  onClick={() => {
                    setShowImportModal(true);
                    setShowUserMenu(false);
                  }}
                  className="w-full text-left px-4 py-2 text-sm text-gray-700 dark:text-gray-300 hover:bg-gray-100 dark:hover:bg-gray-700 flex items-center space-x-2"
                >
                  <Upload size={16} />
                  <span>Import Progress</span>
                </button>
                <Link
                  to="/progress"
                  className="block px-4 py-2 text-sm text-gray-700 dark:text-gray-300 hover:bg-gray-100 dark:hover:bg-gray-700"
                  onClick={() => setShowUserMenu(false)}
                >
                  View Progress
                </Link>
              </div>
            )}
          </div>
        </nav>
      </div>

      <Modal isOpen={showImportModal} onClose={() => setShowImportModal(false)} title="Import Progress">
        <div className="space-y-4">
          <p className="text-gray-600 dark:text-gray-300">Select a JSON file to import your progress.</p>
          <input
            type="file"
            accept=".json"
            onChange={(e) => {
              const file = e.target.files?.[0];
              if (file) {
                handleImport(file);
              }
            }}
            className="block w-full text-sm text-gray-500 dark:text-gray-400 file:mr-4 file:py-2 file:px-4 file:rounded-lg file:border-0 file:text-sm file:font-semibold file:bg-primary-50 dark:file:bg-primary-900 file:text-primary-700 dark:file:text-primary-300 hover:file:bg-primary-100 dark:hover:file:bg-primary-800"
          />
        </div>
      </Modal>
    </header>
  );
}

