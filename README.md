# Rocq Type Theory Game

An interactive, gamified learning platform for type theory using Rocq (formerly Coq).

## Features

- 🎮 Interactive proof writing with immediate feedback
- 📚 Progressive world-based learning system
- 🏆 Achievement and XP system
- 💾 LocalStorage-based progress tracking
- 📤 Export/Import functionality for assignments
- 🎯 Hint system with progressive difficulty
- 📖 Theory sections with examples

## Getting Started

### Prerequisites

- Node.js 18+ and npm

### Installation

```bash
npm install
```

### Development

```bash
npm run dev
```

The app will be available at `http://localhost:3000`

### Build

```bash
npm run build
```

### Preview Production Build

```bash
npm run preview
```

## Project Structure

```
src/
├── components/     # React components
├── context/        # React context providers
├── hooks/          # Custom React hooks
├── pages/          # Page components
├── services/       # Business logic services
├── types/          # TypeScript type definitions
└── utils/          # Utility functions
```

## World System

Worlds are defined as JSON files in `public/worlds/`. Each world contains multiple levels with:
- Theory sections
- Starting code templates
- Solutions
- Hints
- Rewards

## License

MIT

