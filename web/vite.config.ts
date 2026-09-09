import { defineConfig } from 'vite'
import react from '@vitejs/plugin-react'

// In dev the Vite server proxies /api to the Lean server, so the client code
// never needs to know which of the two is serving it.
export default defineConfig({
  plugins: [react()],
  server: {
    proxy: { '/api': { target: 'http://127.0.0.1:8087', changeOrigin: true } },
  },
  build: { outDir: 'dist', emptyOutDir: true },
})
