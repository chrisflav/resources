import { StrictMode } from 'react'
import { createRoot } from 'react-dom/client'
import App from './App'
import './styles.css'

// One component for both routes. `/join/#…` and `/` are two moments in the same
// session rather than two applications: accepting an invite leaves you looking
// at the realm you were invited to, with the identity it just made.
createRoot(document.getElementById('root')!).render(
  <StrictMode>
    <App />
  </StrictMode>,
)
