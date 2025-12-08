import { defineConfig } from 'vite';
import react from '@vitejs/plugin-react';
import path from 'path';
import { readFileSync, existsSync } from 'fs';

// Plugin to fix jsCoq .js imports resolving to .ts files
const jscoqResolvePlugin = () => ({
  name: 'jscoq-resolve',
  resolveId(id, importer) {
    if (importer && importer.includes('jscoq/frontend/classic/js') && id.startsWith('./') && id.endsWith('.js')) {
      // Try to resolve .ts version
      const tsId = id.replace(/\.js$/, '.ts');
      const importerDir = path.dirname(importer);
      const tsPath = path.resolve(importerDir, tsId);
      if (existsSync(tsPath)) {
        return tsPath;
      }
    }
    return null;
  },
});

export default defineConfig({
  plugins: [react(), jscoqResolvePlugin()],
  resolve: {
    alias: {
      '@': path.resolve(__dirname, './src'),
    },
    extensions: ['.mjs', '.js', '.mts', '.ts', '.jsx', '.tsx', '.json'],
    // Fix jsCoq module resolution - allow .ts files to be resolved when .js is imported
    dedupe: ['jscoq'],
  },
  optimizeDeps: {
    include: ['jscoq', 'bootstrap'],
    exclude: ['jscoq/frontend'],
    esbuildOptions: {
      resolveExtensions: ['.mjs', '.js', '.mts', '.ts', '.jsx', '.tsx', '.json'],
    },
  },
  build: {
    outDir: 'dist',
    sourcemap: true,
    rollupOptions: {
      output: {
        manualChunks: {
          'react-vendor': ['react', 'react-dom', 'react-router-dom'],
          'ui-vendor': ['framer-motion', 'lucide-react', 'react-hot-toast'],
          'editor': ['@monaco-editor/react'],
        },
      },
    },
    commonjsOptions: {
      include: [/node_modules/],
      transformMixedEsModules: true,
    },
  },
  base: './',
  server: {
    port: 3000,
    open: true,
    fs: {
      allow: ['..'],
    },
  },
});
