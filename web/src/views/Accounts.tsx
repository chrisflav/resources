import { useState } from 'react'
import { api, formatMinor } from '../api'
import { useAsync } from '../hooks'
import type { Account, Balance } from '../types'

const KINDS = ['asset', 'liability', 'equity', 'income', 'expense'] as const

/** Mirrors the server's guess, so the form can show what it is about to do. */
function guessKind(name: string): string {
  switch (name.split('.')[0]) {
    case 'Assets':
      return 'asset'
    case 'Liabilities':
      return 'liability'
    case 'Equity':
    case 'Budget':
      return 'equity'
    case 'Income':
      return 'income'
    default:
      return 'expense'
  }
}

/** Rolls per-account balances up the dotted hierarchy. */
function rollUp(balances: Balance[]): Map<string, number> {
  const totals = new Map<string, number>()
  for (const b of balances) {
    const parts = b.account.split('.')
    for (let i = 1; i <= parts.length; i++) {
      const prefix = parts.slice(0, i).join('.')
      totals.set(prefix, (totals.get(prefix) ?? 0) + b.minor)
    }
  }
  return totals
}

/** Editing an existing account, or creating a new one when `editing` is null. */
function AccountForm({
  editing,
  onDone,
}: {
  editing: Account | null
  onDone: () => void
}) {
  const [name, setName] = useState(editing?.name ?? '')
  const [kind, setKind] = useState(editing?.kind ?? '')
  const [owner, setOwner] = useState(editing && !editing.mine ? editing.ownerName : '')
  const [iban, setIban] = useState(editing?.iban ?? '')
  const [note, setNote] = useState(editing?.note ?? '')
  const [busy, setBusy] = useState(false)
  const [error, setError] = useState<string | null>(null)

  const save = async () => {
    if (!name) return
    setBusy(true)
    setError(null)
    try {
      await api.createAccount({
        name,
        kind: kind || undefined,
        owner: owner.trim() || undefined,
        iban: iban || undefined,
        note: note || undefined,
      })
      onDone()
    } catch (e) {
      setError(e instanceof Error ? e.message : String(e))
    } finally {
      setBusy(false)
    }
  }

  const remove = async () => {
    if (!editing) return
    setBusy(true)
    setError(null)
    try {
      await api.deleteAccount(editing.id)
      onDone()
    } catch (e) {
      setError(e instanceof Error ? e.message : String(e))
    } finally {
      setBusy(false)
    }
  }

  return (
    <div className="card">
      <div className="card-head">{editing ? `edit ${editing.name}` : 'new account'}</div>
      <div className="card-body">
        {error && <div className="error">{error}</div>}
        {editing ? (
          <div className="mono muted">{editing.name}</div>
        ) : (
          <label className="field">
            Dotted name
            <input
              type="text"
              placeholder="Assets.Bank.DKB.Giro"
              value={name}
              onChange={(e) => setName(e.target.value)}
            />
          </label>
        )}
        <label className="field">
          Kind
          <select value={kind} onChange={(e) => setKind(e.target.value)}>
            {!editing && <option value="">from the name{name ? ` — ${guessKind(name)}` : ''}</option>}
            {KINDS.map((k) => (
              <option key={k} value={k}>
                {k}
              </option>
            ))}
          </select>
        </label>
        <label className="field">
          Owner
          <input
            type="text"
            placeholder="you"
            value={owner}
            onChange={(e) => setOwner(e.target.value)}
          />
        </label>
        <label className="field">
          IBAN
          <input type="text" value={iban} onChange={(e) => setIban(e.target.value)} />
        </label>
        <label className="field">
          Note
          <input type="text" value={note} onChange={(e) => setNote(e.target.value)} />
        </label>
        <div className="muted">
          {editing ? (
            <>
              A bank account must be <strong>asset</strong> — or <strong>liability</strong> for a
              credit card — to be offered as an import target. Renaming is not supported here;
              create the new name and move the postings.
            </>
          ) : (
            <>
              Left on "from the name", the kind comes from the first path component: Assets,
              Liabilities, Equity, Budget, Income — anything else becomes an expense. Naming an
              owner makes it somebody else's: an ordinary account in every other respect, and kept
              out of your net worth by the owner rather than by its kind.
            </>
          )}
        </div>
        <div className="row">
          <button className="btn" disabled={busy || !name} onClick={() => void save()}>
            {editing ? 'Save' : 'Create'}
          </button>
          {editing && (
            <>
              <button className="btn quiet" onClick={onDone}>
                Cancel
              </button>
              <button
                className="btn quiet"
                style={{ marginLeft: 'auto' }}
                disabled={busy}
                onClick={() => void remove()}
              >
                Delete
              </button>
            </>
          )}
        </div>
      </div>
    </div>
  )
}

export default function Accounts() {
  const [asOf, setAsOf] = useState('')
  const [editing, setEditing] = useState<string | null>(null)
  const accounts = useAsync(() => api.accounts(), [])
  const balances = useAsync(() => api.balances(asOf || undefined), [asOf])
  const monthly = useAsync(() => api.monthly('Expenses', 'EUR'), [])
  const worth = useAsync(() => api.worth(), [])

  const rows = balances.data ?? []
  const totals = rollUp(rows)
  const names = [...new Set([...rows.map((b) => b.account), ...(accounts.data ?? []).map((a) => a.name)])].sort()
  const roots = [...new Set(names.map((n) => n.split('.')[0]))].sort()

  const months = monthly.data ?? []
  const peak = months.reduce((m, x) => Math.max(m, Math.abs(x.minor)), 1)

  return (
    <>
      <div className="grid-2">
        {worth.data && (
          <div className="stat">
            <div className="k">what you are worth</div>
            <div className="v">{worth.data.text}</div>
            <div className="muted" style={{ fontSize: 12 }}>
              your own money, plus what passes between you and everybody else
            </div>
          </div>
        )}
        {roots.map((r) => (
          <div className="stat" key={r}>
            <div className="k">{r}</div>
            <div className="v">{formatMinor(totals.get(r) ?? 0)}</div>
          </div>
        ))}
      </div>

      <div className="split">
        <div className="card">
          <div className="card-head">
            <div className="spread">
              <span>balances</span>
              <input
                type="date"
                value={asOf}
                onChange={(e) => setAsOf(e.target.value)}
                aria-label="as of"
              />
            </div>
          </div>
          <div className="card-body">
            {names.map((n) => {
              const depth = n.split('.').length - 1
              const total = totals.get(n)
              const isLeaf = !names.some((m) => m.startsWith(n + '.'))
              const real = (accounts.data ?? []).find((a) => a.name === n)
              return (
                <div
                  className={`tree-row${real ? ' selectable' : ''}${
                    editing === n ? ' picked' : ''
                  }`}
                  key={n}
                  style={{ paddingLeft: depth * 16 }}
                  onClick={real ? () => setEditing(n) : undefined}
                  role={real ? 'button' : undefined}
                  tabIndex={real ? 0 : undefined}
                  onKeyDown={
                    real
                      ? (e) => {
                          if (e.key === 'Enter' || e.key === ' ') {
                            e.preventDefault()
                            setEditing(n)
                          }
                        }
                      : undefined
                  }
                >
                  <span style={{ fontWeight: depth === 0 ? 600 : 400 }}>
                    {n.split('.').slice(-1)[0]}
                    {!isLeaf && <span className="muted"> ·</span>}
                  </span>
                  <span style={{ display: 'flex', gap: 10, alignItems: 'baseline' }}>
                    {real && !real.mine && <span className="pill warn">{real.ownerName}</span>}
                    {real && <span className="pill">{real.kind}</span>}
                    <span className={total !== undefined && total < 0 ? 'neg' : undefined}>
                      {total === undefined ? '' : formatMinor(total)}
                    </span>
                  </span>
                </div>
              )
            })}
            {names.length === 0 && <div className="empty">No accounts yet.</div>}
          </div>
        </div>

        <div style={{ display: 'flex', flexDirection: 'column', gap: 18 }}>
          <AccountForm
            key={editing ?? 'new'}
            editing={(accounts.data ?? []).find((a) => a.name === editing) ?? null}
            onDone={() => {
              setEditing(null)
              accounts.reload()
              balances.reload()
            }}
          />
          {editing === null && (
            <div className="muted">Select an account on the left to change its kind or IBAN.</div>
          )}

          <div className="card">
            <div className="card-head">expenses by month</div>
            <div className="card-body">
              {months.length === 0 && <div className="muted">no data yet</div>}
              {months.map((m) => (
                <div key={m.month} style={{ display: 'flex', gap: 10, alignItems: 'center' }}>
                  <span className="mono" style={{ width: 62 }}>
                    {m.month}
                  </span>
                  <div
                    className="bar"
                    style={{ width: `${(Math.abs(m.minor) / peak) * 100}%` }}
                    aria-hidden
                  />
                  <span className="mono muted" style={{ marginLeft: 'auto' }}>
                    {formatMinor(m.minor)}
                  </span>
                </div>
              ))}
            </div>
          </div>
        </div>
      </div>
    </>
  )
}
