import { defineConfig } from 'vite';
import react from '@vitejs/plugin-react';
import path from 'path';
import { readFileSync, existsSync, statSync } from 'fs';
import { fileURLToPath } from 'url';

const __dirname = path.dirname(fileURLToPath(import.meta.url));

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

// Plugin to serve node_modules/jscoq at /jscoq path
const jscoqServePlugin = () => ({
  name: 'jscoq-serve',
  configureServer(server) {
    server.middlewares.use('/jscoq', (req, res, next) => {
      // req.url already includes /jscoq, so we need to remove it
      // e.g., /jscoq/dist/wacoq_worker.js -> dist/wacoq_worker.js
      let relativePath = req.url || '';
      if (relativePath.startsWith('/jscoq')) {
        relativePath = relativePath.slice('/jscoq'.length);
      }
      // Remove leading slash if present
      const cleanPath = relativePath.startsWith('/') ? relativePath.slice(1) : relativePath;
      const jscoqPath = path.resolve(__dirname, 'node_modules/jscoq', cleanPath);
      
      try {
        if (existsSync(jscoqPath)) {
          const stats = statSync(jscoqPath);
          if (stats.isFile()) {
            res.setHeader('Content-Type', getContentType(jscoqPath));
            res.end(readFileSync(jscoqPath));
            return;
          } else if (stats.isDirectory()) {
            // If it's a directory, try index files
            const indexFiles = ['index.html', 'index.js'];
            for (const indexFile of indexFiles) {
              const indexPath = path.join(jscoqPath, indexFile);
              if (existsSync(indexPath)) {
                res.setHeader('Content-Type', getContentType(indexPath));
                res.end(readFileSync(indexPath));
                return;
              }
            }
          }
        }
      } catch (error) {
        // File doesn't exist or can't be read
        console.warn(`Failed to serve jsCoq file: ${jscoqPath}`, error);
      }
      next();
    });
  },
  async closeBundle() {
    // Copy jsCoq to dist during build
    const jscoqSrc = path.resolve(__dirname, 'node_modules/jscoq');
    const jscoqDest = path.resolve(__dirname, 'dist/jscoq');
    if (existsSync(jscoqSrc)) {
      try {
        // Use fs-extra if available, otherwise use cp command
        const fsExtra = await import('fs-extra').catch(() => null);
        if (fsExtra && fsExtra.default && fsExtra.default.copySync) {
          fsExtra.default.copySync(jscoqSrc, jscoqDest, { overwrite: true });
          console.log('✓ Copied jsCoq from node_modules to dist/jscoq');
        } else {
          // Fallback: use cp command via exec
          const { execSync } = await import('child_process');
          execSync(`cp -r "${jscoqSrc}" "${jscoqDest}"`, { stdio: 'inherit' });
          console.log('✓ Copied jsCoq from node_modules to dist/jscoq (using cp)');
        }
      } catch (error) {
        console.warn('Failed to copy jsCoq:', error);
      }
    }
  },
});

function getContentType(filePath: string): string {
  const ext = path.extname(filePath);
  const types: Record<string, string> = {
    '.js': 'application/javascript',
    '.ts': 'application/typescript',
    '.wasm': 'application/wasm',
    '.json': 'application/json',
    '.css': 'text/css',
    '.html': 'text/html',
    '.png': 'image/png',
    '.jpg': 'image/jpeg',
    '.svg': 'image/svg+xml',
  };
  return types[ext] || 'application/octet-stream';
}

export default defineConfig({
  plugins: [react(), jscoqResolvePlugin(), jscoqServePlugin()],
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

