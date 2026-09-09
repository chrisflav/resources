import { useState } from 'react'
import { api } from './api'
import { useAsync } from './hooks'
import Ledger from './views/Ledger'
import Inbox from './views/Inbox'
import Accounts from './views/Accounts'
import Sharing from './views/Sharing'
import Contacts from './views/Contacts'
import Rules from './views/Rules'
import Settings from './views/Settings'

const TABS = ['Ledger', 'Inbox', 'Accounts', 'Sharing', 'Contacts', 'Rules', 'Settings'] as const
type Tab = (typeof TABS)[number]

/** The tab lives in the hash, so a view is a link you can send to yourself. */
function tabFromHash(): Tab {
  const raw = decodeURIComponent(window.location.hash.replace(/^#/, '')).split('?')[0]
  const found = TABS.find((t) => t.toLowerCase() === raw.toLowerCase())
  return found ?? 'Ledger'
}

export default function App() {
  const [tab, setTab] = useState<Tab>(tabFromHash)
  // Transactions handed from the Ledger to the Sharing tab, so "share these"
  // is one click rather than retyping a filter.
  const [toBill, setToBill] = useState<string[]>([])
  const health = useAsync(() => api.health(), [])
  const trial = useAsync(() => api.trial(), [tab])

  const go = (t: Tab) => {
    setTab(t)
    window.location.hash = t.toLowerCase()
  }

  const unbalanced = (trial.data ?? []).filter((b) => b.minor !== 0)

  return (
    <div className="shell">
      <header className="top">
        <div className="wordmark">
          resources<span>.</span>
        </div>
        <nav className="tabs">
          {TABS.map((t) => (
            <button key={t} aria-current={t === tab} onClick={() => go(t)}>
              {t}
            </button>
          ))}
        </nav>
      </header>

      <div className="statusline">
        {health.error ? (
          <span style={{ color: 'var(--danger)' }}>api: {health.error}</span>
        ) : health.data ? (
          <>
            <span>schema {health.data.schema}</span>
            <span>
              actor {health.data.actor} · {health.data.scopes}
            </span>
          </>
        ) : (
          <span>connecting…</span>
        )}
        {unbalanced.length > 0 ? (
          <span style={{ color: 'var(--danger)' }}>
            trial balance is not zero:{' '}
            {unbalanced.map((b) => `${b.text} ${b.commodity}`).join(', ')}
          </span>
        ) : trial.data ? (
          <span>trial balance zero</span>
        ) : null}
      </div>

      <main>
        {tab === 'Ledger' && (
          <Ledger
            onBill={(ids) => {
              setToBill(ids)
              go('Sharing')
            }}
          />
        )}
        {tab === 'Inbox' && <Inbox />}
        {tab === 'Accounts' && <Accounts />}
        {tab === 'Sharing' && <Sharing initialPicked={toBill} onConsumed={() => setToBill([])} />}
        {tab === 'Contacts' && <Contacts />}
        {tab === 'Rules' && <Rules />}
        {tab === 'Settings' && <Settings onChanged={() => health.reload()} />}
      </main>
    </div>
  )
}
