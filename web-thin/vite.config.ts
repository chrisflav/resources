/// <reference types="vitest" />
import { fileURLToPath } from 'node:url'
import { defineConfig } from 'vite'
import react from '@vitejs/plugin-react'

// The thin client talks only to a sequencer. In dev Vite proxies /seq to a
// locally running one, so the client code never needs to know which of the two
// is serving it.
// libsodium's ESM build points at a sibling file that ships in a different
// package, so it resolves to nothing; the CommonJS entry of the same package is
// the one that works in both Vite and Vitest.
const sodium = fileURLToPath(
  new URL('node_modules/libsodium-wrappers-sumo/dist/modules-sumo/libsodium-wrappers.js', import.meta.url),
)

export default defineConfig({
  plugins: [react()],
  resolve: { alias: { 'libsodium-wrappers-sumo': sodium } },
  server: {
    proxy: { '/seq': { target: 'http://127.0.0.1:8088', changeOrigin: true } },
  },
  build: { outDir: 'dist', emptyOutDir: true },
  test: { globals: true, environment: 'node', include: ['src/**/*.test.ts'] },
})
