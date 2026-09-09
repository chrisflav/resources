import { useState } from 'react'
import { api } from '../api'
import { useAsync } from '../hooks'
import { SortTh, nextSort, type Sort } from '../components'
import type { StagedEntry } from '../types'

type SortKey = 'date' | 'payee' | 'purpose' | 'amount' | 'state' | 'account'

/** Amounts compare numerically on exact minor units; ISO dates compare as text. */
function compare(a: StagedEntry, b: StagedEntry, key: SortKey): number {
  switch (key) {
    case 'date':
      return a.date.localeCompare(b.date)
    case 'payee':
      return (a.payee ?? '').localeCompare(b.payee ?? '')
    case 'purpose':
      return (a.purpose ?? '').localeCompare(b.purpose ?? '')
    case 'amount':
      return a.amount.minor - b.amount.minor
    case 'state':
      return a.state.localeCompare(b.state)
    case 'account':
      return (a.suggestedAccount ?? '').localeCompare(b.suggestedAccount ?? '')
  }
}

/**
 * The screen you actually live in. Imports land here as staged rows; nothing
 * reaches the ledger until it is promoted, so re-importing an overlapping date
 * range is harmless.
 */
export default function Inbox() {
  const accounts = useAsync(() => api.accounts(), [])
  const batches = useAsync(() => api.batches(), [])
  const [batch, setBatch] = useState<string | null>(null)
  const [account, setAccount] = useState('')
  const [profile, setProfile] = useState('auto')
  const [busy, setBusy] = useState(false)
  const [error, setError] = useState<string | null>(null)
  const [notice, setNotice] = useState<string | null>(null)
  const [picked, setPicked] = useState<Set<string>>(new Set())

  const current = batch ?? batches.data?.[0]?.id ?? null
  const staged = useAsync<StagedEntry[]>(
    () => (current ? api.staged(current) : Promise.resolve([])),
    [current],
  )
  const proposals = useAsync(
    () => (current ? api.proposals(current) : Promise.resolve([])),
    [current],
  )
  // Receipts that have been photographed but not yet placed.
  const receipts = useAsync(() => api.receipts(), [])
  const receiptMatches = useAsync(() => api.receiptProposals(), [])
  const [scanning, setScanning] = useState(false)

  const scanAll = async () => {
    setScanning(true)
    setError(null)
    try {
      for (const rec of receipts.data ?? []) await api.scanReceipt(rec.sha256)
      receipts.reload()
      receiptMatches.reload()
    } catch (e) {
      setError(e instanceof Error ? e.message : String(e))
    } finally {
      setScanning(false)
    }
  }

  const attachMatches = async () => {
    setScanning(true)
    try {
      for (const m of receiptMatches.data ?? []) await api.attach(m.txn.id, m.sha256)
      receipts.reload()
      receiptMatches.reload()
    } catch (e) {
      setError(e instanceof Error ? e.message : String(e))
    } finally {
      setScanning(false)
    }
  }

  const uploadReceipt = async (file: File) => {
    setScanning(true)
    setError(null)
    try {
      const att = await api.putAttachment(file)
      await api.scanReceipt(att.sha256)
      receipts.reload()
      receiptMatches.reload()
    } catch (e) {
      setError(e instanceof Error ? e.message : String(e))
    } finally {
      setScanning(false)
    }
  }

  const [sort, setSort] = useState<Sort<SortKey>>({ key: 'date', dir: 'asc' })

  const unsorted = staged.data ?? []
  const rows = [...unsorted].sort((a, b) => {
    const c = compare(a, b, sort.key)
    return sort.dir === 'asc' ? c : -c
  })
  const isNew = (e: StagedEntry) => e.state === 'new'

  const sortBy = (key: SortKey) => setSort((s) => nextSort(s, key))

  // Every account is offered, not only the ones whose kind says "bank": an
  // account created before its kind was set right should still be importable.
  const all = accounts.data ?? []
  const isBalanceSheet = (kind: string) => kind === 'asset' || kind === 'liability'
  const balanceSheet = all.filter((a) => isBalanceSheet(a.kind))
  const other = all.filter((a) => !isBalanceSheet(a.kind))
  const chosen = all.find((a) => a.name === account)
  const oddKind = chosen && !isBalanceSheet(chosen.kind)

  const upload = async (file: File) => {
    if (!account) {
      setError('Choose the bank account this file belongs to first.')
      return
    }
    setBusy(true)
    setError(null)
    setNotice(null)
    try {
      const res = await api.upload(file, account, profile)
      setBatch(res.batch.id)
      batches.reload()
      const dup = res.batch.duplicates
      setNotice(
        `${res.profile}: ${res.staged.length} new row(s)` +
          (dup > 0 ? `, ${dup} already known and skipped` : '') +
          (res.problems.length ? ` — ${res.problems.length} line(s) could not be read` : ''),
      )
    } catch (e) {
      setError(e instanceof Error ? e.message : String(e))
    } finally {
      setBusy(false)
    }
  }

  const promote = async (ids?: string[], merge?: 'auto' | 'true') => {
    if (!current) return
    setBusy(true)
    setError(null)
    try {
      const res = await api.promote(current, ids, merge)
      setNotice(
        `promoted ${res.created.length} transaction(s)` +
          (res.merged ? `, ${res.merged} combined from several rows` : '') +
          (res.settledInvoices.length
            ? `; settled invoice(s) ${res.settledInvoices.join(', ')}`
            : ''),
      )
      setPicked(new Set())
      staged.reload()
      proposals.reload()
      batches.reload()
    } catch (e) {
      setError(e instanceof Error ? e.message : String(e))
    } finally {
      setBusy(false)
    }
  }

  const ignore = async () => {
    if (picked.size === 0) return
    setBusy(true)
    try {
      await api.ignoreStaged([...picked])
      setPicked(new Set())
      staged.reload()
    } catch (e) {
      setError(e instanceof Error ? e.message : String(e))
    } finally {
      setBusy(false)
    }
  }

  /** Routes one staged row to an account before it is promoted. */
  const route = async (id: string, target: string) => {
    try {
      await api.suggest(id, target)
      staged.reload()
    } catch (e) {
      setError(e instanceof Error ? e.message : String(e))
    }
  }

  const toggle = (id: string) => {
    const next = new Set(picked)
    if (next.has(id)) next.delete(id)
    else next.add(id)
    setPicked(next)
  }

  return (
    <>
      <div className="card">
        <div className="card-head">import a bank export</div>
        <div className="card-body">
          <div className="row">
            <label className="field">
              Bank account
              <select value={account} onChange={(e) => setAccount(e.target.value)}>
                <option value="">choose…</option>
                {balanceSheet.length > 0 && (
                  <optgroup label="Asset and liability accounts">
                    {balanceSheet.map((a) => (
                      <option key={a.id} value={a.name}>
                        {a.name}
                      </option>
                    ))}
                  </optgroup>
                )}
                {other.length > 0 && (
                  <optgroup label="Other accounts">
                    {other.map((a) => (
                      <option key={a.id} value={a.name}>
                        {a.name} ({a.kind})
                      </option>
                    ))}
                  </optgroup>
                )}
              </select>
            </label>
            <label className="field">
              Profile
              <select value={profile} onChange={(e) => setProfile(e.target.value)}>
                <option value="auto">detect automatically</option>
                <option value="dkb">dkb</option>
                <option value="sparkasse">sparkasse</option>
                <option value="ing">ing</option>
                <option value="n26">n26</option>
                <option value="revolut">revolut</option>
                <option value="wise">wise</option>
                <option value="paypal">paypal</option>
                <option value="camt-csv">camt-csv</option>
                <option value="generic">generic</option>
              </select>
            </label>
            <label className="field">
              File
              <input
                type="file"
                accept=".csv,text/csv,text/plain"
                disabled={busy}
                onChange={(e) => {
                  const f = e.target.files?.[0]
                  if (f) void upload(f)
                }}
              />
            </label>
          </div>
          {oddKind && (
            <div className="muted">
              {chosen.name} is an <strong>{chosen.kind}</strong> account. Bank accounts are usually
              assets — set its kind on the Accounts tab if that is wrong.
            </div>
          )}
          {all.length === 0 && !accounts.loading && (
            <div className="muted">No accounts yet — create one on the Accounts tab first.</div>
          )}
          {error && <div className="error">{error}</div>}
          {notice && <div className="muted">{notice}</div>}
        </div>
      </div>

      <div className="card">
        <div className="card-head">
          <div className="spread">
            <span>receipts waiting to be placed</span>
            <div className="row">
              <label className="btn quiet" style={{ cursor: 'pointer' }}>
                Add a photo
                <input
                  type="file"
                  style={{ display: 'none' }}
                  accept="image/*,.pdf,.txt"
                  disabled={scanning}
                  onChange={(e) => {
                    const f = e.target.files?.[0]
                    if (f) void uploadReceipt(f)
                  }}
                />
              </label>
              <button
                className="btn quiet"
                disabled={scanning || (receipts.data ?? []).length === 0}
                onClick={() => void scanAll()}
              >
                Read them
              </button>
              <button
                className="btn"
                disabled={scanning || (receiptMatches.data ?? []).length === 0}
                onClick={() => void attachMatches()}
              >
                Attach {(receiptMatches.data ?? []).length || ''} match(es)
              </button>
            </div>
          </div>
        </div>
        <div className="table-wrap">
          <table>
            <thead>
              <tr>
                <th>file</th>
                <th>merchant</th>
                <th>date</th>
                <th className="num">total</th>
                <th>goes with</th>
              </tr>
            </thead>
            <tbody>
              {(receipts.data ?? []).map((rec) => {
                const m = (receiptMatches.data ?? []).find((x) => x.sha256 === rec.sha256)
                return (
                  <tr key={rec.sha256}>
                    <td className="mono">
                      <a href={api.attachmentUrl(rec.sha256)} target="_blank" rel="noreferrer">
                        {rec.origName ?? rec.sha256.slice(0, 12)}
                      </a>
                    </td>
                    <td>{rec.merchant ?? <span className="muted">not read yet</span>}</td>
                    <td className="mono">{rec.date ?? ''}</td>
                    <td className="num">{rec.total?.text ?? ''}</td>
                    <td>
                      {m ? (
                        <>
                          <span className={m.confidence === 'high' ? 'pill good' : 'pill warn'}>
                            {m.confidence}
                          </span>{' '}
                          {m.txn.payee ?? m.txn.date}
                        </>
                      ) : rec.total ? (
                        <span className="muted">nothing matches — it may be cash</span>
                      ) : (
                        ''
                      )}
                    </td>
                  </tr>
                )
              })}
            </tbody>
          </table>
          {(receipts.data ?? []).length === 0 && (
            <div className="empty">
              Every receipt is attached to something. Add a photo now and place it later.
            </div>
          )}
        </div>
      </div>

      {(proposals.data ?? []).length > 0 && (
        <div className="card">
          <div className="card-head">
            <div className="spread">
              <span>
                {(proposals.data ?? []).length} row pair(s) look like one event
              </span>
              <button
                className="btn"
                disabled={busy}
                onClick={() => void promote(undefined, 'auto')}
              >
                Promote all, combining these
              </button>
            </div>
          </div>
          <div className="table-wrap" style={{ maxHeight: '32vh', overflowY: 'auto' }}>
            <table>
              <thead>
                <tr>
                  <th>date</th>
                  <th>main row</th>
                  <th className="num">amount</th>
                  <th className="num">with</th>
                  <th>why</th>
                </tr>
              </thead>
              <tbody>
                {(proposals.data ?? []).map((p, i) => (
                  <tr key={i}>
                    <td className="mono">{p.parent.date}</td>
                    <td>{p.parent.payee ?? p.parent.purpose ?? ''}</td>
                    <td className="num neg">{p.parent.amount.text}</td>
                    <td className="num neg">{p.child.amount.text}</td>
                    <td className="muted wrap">
                      <span className={p.confidence === 'high' ? 'pill good' : 'pill warn'}>
                        {p.confidence}
                      </span>{' '}
                      {p.reason}
                    </td>
                  </tr>
                ))}
              </tbody>
            </table>
          </div>
        </div>
      )}

      <div className="row">
        <label className="field">
          Batch
          <select value={current ?? ''} onChange={(e) => setBatch(e.target.value)}>
            {(batches.data ?? []).map((b) => (
              <option key={b.id} value={b.id}>
                {b.at} · {b.profile} · {b.filename ?? b.id} ({b.total} rows, {b.duplicates} dup)
              </option>
            ))}
          </select>
        </label>
        <div style={{ marginLeft: 'auto' }} className="row">
          <button
            className="btn quiet"
            disabled={busy || picked.size === 0}
            onClick={() => void ignore()}
          >
            Ignore {picked.size || ''}
          </button>
          <button
            className="btn ghost"
            disabled={busy || picked.size === 0}
            onClick={() => void promote([...picked])}
          >
            Promote selected
          </button>
          <button
            className="btn ghost"
            disabled={busy || picked.size < 2}
            onClick={() => void promote([...picked], 'true')}
            title="Promote the selected rows as a single transaction"
          >
            Promote as one
          </button>
          <button
            className="btn"
            disabled={busy || !rows.some(isNew)}
            onClick={() => void promote()}
          >
            Promote all new
          </button>
        </div>
      </div>

      <div className="card">
        <datalist id="inbox-accounts">
          {all.map((a) => (
            <option key={a.id} value={a.name} />
          ))}
        </datalist>
        <div className="card-head">
          {rows.filter(isNew).length} awaiting review · {rows.length} in this batch
        </div>
        <div className="table-wrap">
          <table>
            <thead>
              <tr>
                <th />
                <SortTh label="date" column="date" sort={sort} onSort={sortBy} />
                <SortTh label="payee" column="payee" sort={sort} onSort={sortBy} />
                <SortTh label="purpose" column="purpose" sort={sort} onSort={sortBy} />
                <SortTh label="amount" column="amount" sort={sort} onSort={sortBy} numeric />
                <SortTh label="state" column="state" sort={sort} onSort={sortBy} />
                <SortTh label="goes to" column="account" sort={sort} onSort={sortBy} />
              </tr>
            </thead>
            <tbody>
              {rows.map((e) => (
                <tr key={e.id} className={picked.has(e.id) ? 'selected' : undefined}>
                  <td>
                    <input
                      type="checkbox"
                      checked={picked.has(e.id)}
                      disabled={!isNew(e)}
                      onChange={() => toggle(e.id)}
                      aria-label={`select ${e.id}`}
                    />
                  </td>
                  <td className="mono">{e.date}</td>
                  <td>{e.payee ?? ''}</td>
                  <td className="wrap muted">{e.purpose ?? ''}</td>
                  <td className={`num${e.amount.minor < 0 ? ' neg' : ''}`}>
                    {e.amount.text} {e.amount.commodity}
                  </td>
                  <td>
                    <span
                      className={
                        e.state === 'new'
                          ? 'pill warn'
                          : e.state === 'promoted'
                            ? 'pill good'
                            : 'pill'
                      }
                    >
                      {e.state}
                    </span>
                  </td>
                  <td>
                    {isNew(e) ? (
                      <input
                        type="text"
                        list="inbox-accounts"
                        style={{ minWidth: 210 }}
                        defaultValue={e.suggestedAccount ?? ''}
                        placeholder="(rules decide)"
                        aria-label={`account for ${e.payee ?? e.id}`}
                        onBlur={(ev) => {
                          const v = ev.target.value.trim()
                          if (v && v !== (e.suggestedAccount ?? '')) void route(e.id, v)
                        }}
                        onKeyDown={(ev) => {
                          if (ev.key === 'Enter') ev.currentTarget.blur()
                        }}
                      />
                    ) : (
                      <span className="muted">{e.suggestedAccount ?? ''}</span>
                    )}
                  </td>
                </tr>
              ))}
            </tbody>
          </table>
          {rows.length === 0 && <div className="empty">No staged rows. Import a file above.</div>}
        </div>
      </div>
    </>
  )
}
