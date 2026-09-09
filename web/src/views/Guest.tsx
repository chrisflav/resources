import { useEffect, useState } from 'react'
import { api, useSessionToken, type GuestView } from '../api'
import { useAsync } from '../hooks'

/**
 * What somebody holding a share link sees.
 *
 * A separate page rather than a mode of the main one, mirroring the server: the
 * guest routes are their own table there, and this is their own screen here.
 * Nothing on it can address anything outside the budget the link names, because
 * there is nothing else to ask for.
 *
 * The secret lives in the page fragment, which never reaches a server log or a
 * Referer header, and is held for this page only — never written to storage,
 * where it would outlive the visit and displace the token of whoever else uses
 * this browser.
 */
export default function Guest() {
  const [ready, setReady] = useState(false)

  useEffect(() => {
    const secret = decodeURIComponent(window.location.hash.replace(/^#/, '')).trim()
    if (secret) useSessionToken(secret)
    setReady(true)
  }, [])

  const view = useAsync(() => (ready ? api.guest() : Promise.resolve(null)), [ready])

  const [amount, setAmount] = useState('')
  const [what, setWhat] = useState('')
  const [date, setDate] = useState('')
  const [busy, setBusy] = useState(false)
  const [error, setError] = useState<string | null>(null)

  const guard = async (act: () => Promise<void>) => {
    setBusy(true)
    setError(null)
    try {
      await act()
    } catch (e) {
      setError(e instanceof Error ? e.message : String(e))
    } finally {
      setBusy(false)
    }
  }

  const add = () =>
    guard(async () => {
      await api.addGuestExpense({
        amount,
        narration: what,
        payee: what,
        ...(date ? { date } : {}),
      })
      setAmount('')
      setWhat('')
      setDate('')
      view.reload()
    })

  const drop = (id: string) =>
    guard(async () => {
      await api.dropGuestExpense(id)
      view.reload()
    })

  const g: GuestView | null = view.data

  if (view.error) {
    return (
      <div className="shell">
        <main>
          <div className="error">{view.error}</div>
          <div className="muted">
            This link may have been revoked, or the address may be missing the part after the #.
          </div>
        </main>
      </div>
    )
  }

  if (!g) {
    return (
      <div className="shell">
        <main>
          <div className="muted">Loading…</div>
        </main>
      </div>
    )
  }

  const yours = g.claims.filter((c) => c.state === 'pending')

  return (
    <div className="shell">
      <header className="top">
        <div className="wordmark">
          {g.budget}
          <span>.</span>
        </div>
        <nav className="tabs">
          <button aria-current>you are {g.you}</button>
        </nav>
      </header>

      <div className="statusline">
        <span>{g.costs.length} cost(s)</span>
        <span>{g.total.text} spent between you</span>
        {g.undivided.minor !== 0 && (
          <span>{g.undivided.text} added since it was last divided up</span>
        )}
        {g.closed && <span>closed</span>}
      </div>

      <main style={{ display: 'flex', flexDirection: 'column', gap: 18 }}>
        {error && <div className="error">{error}</div>}
        {g.note && <div className="muted">{g.note}</div>}

        <div className="grid-2">
          {g.standings.map((s) => (
            <div className="stat" key={s.owner}>
              <div className="k">{s.name}</div>
              <div className="v">{s.amount.text}</div>
              <div className="muted" style={{ fontSize: 12 }}>
                {s.amount.minor === 0
                  ? 'square'
                  : s.owes
                    ? 'has spent less than their share'
                    : 'has spent more than their share'}
              </div>
            </div>
          ))}
        </div>

        {yours.length > 0 && (
          <div className="card">
            <div className="card-head">still to settle</div>
            <div className="table-wrap">
              <table>
                <thead>
                  <tr>
                    <th>from</th>
                    <th>to</th>
                    <th className="num">amount</th>
                    <th>by</th>
                  </tr>
                </thead>
                <tbody>
                  {yours.map((c) => (
                    <tr key={c.id}>
                      <td>{c.from}</td>
                      <td>{c.to}</td>
                      <td className="num">
                        <strong>{c.amount.text}</strong>
                      </td>
                      <td className="mono muted">{c.due}</td>
                    </tr>
                  ))}
                </tbody>
              </table>
            </div>
            <div className="card-body">
              <div className="muted">
                These are the payments that would leave everybody square. Nothing here has happened
                yet.
              </div>
              {g.undivided.minor !== 0 && (
                <div className="muted">
                  <strong>{g.undivided.text}</strong> of what has been added is not divided up yet,
                  so these figures are from before it. They are worked out again once it is —
                  nothing can be settled while part of the total belongs to nobody in particular.
                </div>
              )}
            </div>
          </div>
        )}

        {!g.closed && (
          <div className="card">
            <div className="card-head">add something you paid for</div>
            <div className="card-body">
              <div className="row">
                <label className="field" style={{ flex: '1 1 200px' }}>
                  What
                  <input
                    type="text"
                    placeholder="the taxi"
                    value={what}
                    onChange={(e) => setWhat(e.target.value)}
                  />
                </label>
                <label className="field" style={{ flex: '0 1 120px' }}>
                  How much
                  <input
                    type="text"
                    inputMode="decimal"
                    placeholder="42.50"
                    value={amount}
                    onChange={(e) => setAmount(e.target.value)}
                  />
                </label>
                <label className="field">
                  When
                  <input type="date" value={date} onChange={(e) => setDate(e.target.value)} />
                </label>
              </div>
              <div className="row">
                <button className="btn" disabled={busy || !amount.trim()} onClick={() => void add()}>
                  Add it
                </button>
              </div>
              <div className="muted">
                What you paid goes in beside everyone else's, and is set against your own share when
                the costs are divided up. You do not have to be paid back separately — but the
                figures above only move once somebody divides it up.
              </div>
            </div>
          </div>
        )}

        <div className="card">
          <div className="card-head">everything shared so far</div>
          <div className="table-wrap">
            <table>
              <thead>
                <tr>
                  <th>date</th>
                  <th>what</th>
                  <th>paid by</th>
                  <th className="num">amount</th>
                  <th />
                </tr>
              </thead>
              <tbody>
                {g.costs.map((c) => (
                  <tr key={c.id}>
                    <td className="mono">{c.date}</td>
                    <td>{c.what}</td>
                    <td>{c.mine ? <strong>you</strong> : c.paidBy}</td>
                    <td className="num">{c.amount.text}</td>
                    <td>
                      {c.mine && !g.closed && (
                        <button
                          className="btn quiet"
                          style={{ padding: '2px 9px' }}
                          disabled={busy}
                          onClick={() => void drop(c.id)}
                          aria-label={`remove ${c.what}`}
                        >
                          ×
                        </button>
                      )}
                    </td>
                  </tr>
                ))}
              </tbody>
            </table>
            {g.costs.length === 0 && <div className="empty">Nothing yet.</div>}
          </div>
        </div>
      </main>
    </div>
  )
}
