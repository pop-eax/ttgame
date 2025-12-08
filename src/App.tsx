import React from 'react';
import { BrowserRouter, Routes, Route } from 'react-router-dom';
import { Toaster } from 'react-hot-toast';
import { GameProvider } from './context/GameContext';
import { ThemeProvider } from './context/ThemeContext';
import { Layout } from './components/layout/Layout';
import { HomePage } from './pages/HomePage';
import { WorldMapPage } from './pages/WorldMapPage';
import { WorldDetailPage } from './pages/WorldDetailPage';
import { LevelPage } from './pages/LevelPage';
import { ProgressPage } from './pages/ProgressPage';
import { HelpPage } from './pages/HelpPage';
import './styles/globals.css';

function App() {
  return (
    <div className="app-root">
    <ThemeProvider>
      <GameProvider>
        <BrowserRouter>
          <Layout>
            <Routes>
              <Route path="/" element={<HomePage />} />
              <Route path="/worlds" element={<WorldMapPage />} />
              <Route path="/worlds/:worldId" element={<WorldDetailPage />} />
              <Route path="/worlds/:worldId/levels/:levelId" element={<LevelPage />} />
              <Route path="/progress" element={<ProgressPage />} />
              <Route path="/help" element={<HelpPage />} />
            </Routes>
          </Layout>
          <Toaster position="top-right" />
        </BrowserRouter>
      </GameProvider>
    </ThemeProvider>
    </div>
  );
}

export default App;

