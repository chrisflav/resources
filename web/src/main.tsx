import { StrictMode } from 'react'
import { createRoot } from 'react-dom/client'
import App from './App'
import Guest from './views/Guest'
import './styles.css'

// `/s/#<secret>` is a share link. It gets its own root component rather than a
// mode of the main one, mirroring the server, where a guest token is dispatched
// to a route table of its own.
const shared = window.location.pathname.replace(/\/+$/, '') === '/s'

createRoot(document.getElementById('root')!).render(
  <StrictMode>{shared ? <Guest /> : <App />}</StrictMode>,
)
