import React from 'react';
import { Link } from 'react-router-dom';
import { Button } from '../components/common/Button';

export function HelpPage() {
  return (
    <div className="max-w-4xl mx-auto px-4 py-8">
      <h1 className="text-3xl font-bold text-gray-900 dark:text-gray-100 mb-6">Help & Tutorial</h1>
      
      <div className="space-y-6">
        <section>
          <h2 className="text-2xl font-semibold mb-3 dark:text-gray-100">Getting Started</h2>
          <p className="text-gray-600 dark:text-gray-300 mb-4">
            Welcome to Rocq Type Theory Game! This interactive platform teaches you type theory
            through hands-on proof writing.
          </p>
          <p className="text-gray-600 dark:text-gray-300">
            Start with World 0 (Tutorial) to learn the basics of Rocq syntax and proof structure.
            Each level introduces new concepts and tactics that you'll use in future challenges.
          </p>
        </section>

        <section>
          <h2 className="text-2xl font-semibold mb-3 dark:text-gray-100">How to Play</h2>
          <ol className="list-decimal list-inside space-y-2 text-gray-600 dark:text-gray-300">
            <li>Select a world from the world map</li>
            <li>Choose a level to start</li>
            <li>Read the objective and theory sections</li>
            <li>Write your proof in the editor</li>
            <li>Click "Run Proof" to check your solution</li>
            <li>Use hints if you get stuck</li>
            <li>Complete levels to unlock new worlds and tactics</li>
          </ol>
        </section>

        <section>
          <h2 className="text-2xl font-semibold mb-3 dark:text-gray-100">Export & Import</h2>
          <p className="text-gray-600 dark:text-gray-300 mb-4">
            You can export your progress as a JSON file to submit assignments or backup your work.
            Import functionality allows you to restore progress or load custom worlds.
          </p>
        </section>

        <div className="pt-6">
          <Link to="/">
            <Button>Back to Home</Button>
          </Link>
        </div>
      </div>
    </div>
  );
}

