import React from 'react';
import { useLocation } from 'react-router-dom';
import { Header } from './Header';
import { Footer } from './Footer';

export function Layout({ children }: { children: React.ReactNode }) {
  const location = useLocation();
  const isLevelPage = location.pathname.includes('/levels/');
  
  return (
    <div className="min-h-screen flex flex-col bg-gray-50 dark:bg-gray-900">
      {!isLevelPage && <Header />}
      <main className="flex-1">
        {children}
      </main>
      {!isLevelPage && <Footer />}
    </div>
  );
}

