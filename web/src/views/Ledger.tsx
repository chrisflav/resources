import { useState } from 'react'
import { api } from '../api'
import { SortTh, nextSort, type Sort } from '../components'
import { useAsync, useDebounced } from '../hooks'
import type { Revision } from '../types'

type LedgerSortKey = 'date' | 'payee' | 'narration' | 'amount'

type Draft = { date: string; payee: string; narration: string; labels: string; accounts: string[] }

function Detail({ id, onChanged }: { id: string; onChanged: () => void }) {
  const txn = useAsync(() => api.transaction(id), [id])
  const revisions = useAsync<Revision[]>(() => api.revisions(id), [id])
  const accounts = useAsync(() => api.accounts(), [])
  const labels = useAsync(() => api.labels(), [])
  const [busy, setBusy] = useState(false)
  const [error, setError] = useState<string | null>(null)
  const [draft, setDraft] = useState<Draft | null>(null)

  const t = txn.data
  if (!t)
    return (
      <div className="card">
        <div className="empty">{txn.error ?? 'loading…'}</div>
      </div>
    )

  const startEdit = () =>
    setDraft({
      date: t.date,
      payee: t.payee ?? '',
      narration: t.narration,
      labels: t.labels.join(', '),
      accounts: t.postings.map((p) => p.account),
    })

  const save = async () => {
    if (!draft) return
    setBusy(true)
    setError(null)
    try {
      // Only the fields shown are sent; the server merges, so amounts and
      // provenance are untouched and the transaction cannot fall out of balance.
      await api.updateTransaction(t.id, {
        date: draft.date,
        payee: draft.payee || null,
        narration: draft.narration,
        labels: draft.labels
          .split(',')
          .map((l) => l.trim())
          .filter(Boolean),
        postings: t.postings.map((p, i) => ({
          account: draft.accounts[i] || p.account,
          minor: p.amount.minor,
          commodity: p.amount.commodity,
          note: p.note,
        })),
      })
      setDraft(null)
      txn.reload()
      revisions.reload()
      onChanged()
    } catch (e) {
      setError(e instanceof Error ? e.message : String(e))
    } finally {
      setBusy(false)
    }
  }

  const upload = async (file: File) => {
    setBusy(true)
    setError(null)
    try {
      const att = await api.putAttachment(file)
      await api.attach(t.id, att.sha256)
      txn.reload()
      onChanged()
    } catch (e) {
      setError(e instanceof Error ? e.message : String(e))
    } finally {
      setBusy(false)
    }
  }

  const unmerge = async () => {
    setBusy(true)
    setError(null)
    try {
      await api.unmergeTransaction(t.id)
      onChanged()
    } catch (e) {
      setError(e instanceof Error ? e.message : String(e))
    } finally {
      setBusy(false)
    }
  }

  const remove = async () => {
    setBusy(true)
    try {
      await api.deleteTransaction(t.id)
      onChanged()
    } catch (e) {
      setError(e instanceof Error ? e.message : String(e))
    } finally {
      setBusy(false)
    }
  }

  return (
    <div className="card">
      <div className="card-head">transaction</div>
      <div className="card-body">
        {error && <div className="error">{error}</div>}
        <datalist id="account-names">
          {(accounts.data ?? []).map((a) => (
            <option key={a.id} value={a.name} />
          ))}
        </datalist>
        <datalist id="label-names">
          {(labels.data ?? []).map((l) => (
            <option key={l.id} value={l.name} />
          ))}
        </datalist>

        <div className="spread">
          <div>
            <div style={{ fontSize: 16, fontWeight: 600 }}>{t.payee ?? '(no payee)'}</div>
            <div className="muted">{t.narration}</div>
          </div>
          <span className={t.balanced ? 'pill good' : 'pill bad'}>
            {t.balanced ? 'balanced' : 'UNBALANCED'}
          </span>
        </div>
        <div className="mono muted">
          {t.date} · {t.source}
        </div>

        {draft ? (
          <>
            <div className="row">
              <label className="field">
                Date
                <input
                  type="date"
                  value={draft.date}
                  onChange={(e) => setDraft({ ...draft, date: e.target.value })}
                />
              </label>
              <label className="field" style={{ flex: '1 1 160px' }}>
                Payee
                <input
                  type="text"
                  value={draft.payee}
                  onChange={(e) => setDraft({ ...draft, payee: e.target.value })}
                />
              </label>
            </div>
            <label className="field">
              Narration
              <input
                type="text"
                value={draft.narration}
                onChange={(e) => setDraft({ ...draft, narration: e.target.value })}
              />
            </label>
            <label className="field">
              Labels, comma separated
              <input
                type="text"
                list="label-names"
                value={draft.labels}
                onChange={(e) => setDraft({ ...draft, labels: e.target.value })}
              />
            </label>
          </>
        ) : null}

        <div className="table-wrap">
          <table>
            <thead>
              <tr>
                <th>account</th>
                <th className="num">amount</th>
                <th>party</th>
              </tr>
            </thead>
            <tbody>
              {t.postings.map((p, i) => (
                <tr key={i}>
                  <td>
                    {draft ? (
                      <input
                        type="text"
                        list="account-names"
                        style={{ width: '100%', minWidth: 220 }}
                        value={draft.accounts[i] ?? p.account}
                        aria-label={`account for posting ${i + 1}`}
                        onChange={(e) =>
                          setDraft({
                            ...draft,
                            accounts: draft.accounts.map((a, j) => (i === j ? e.target.value : a)),
                          })
                        }
                      />
                    ) : (
                      p.account
                    )}
                  </td>
                  <td className={`num${p.amount.minor < 0 ? ' neg' : ''}`}>
                    {p.amount.text} {p.amount.commodity}
                  </td>
                  <td className="muted">{p.party ?? ''}</td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
        {draft && (
          <div className="muted">
            Amounts are fixed here on purpose — moving a posting to another account keeps the
            transaction balanced by construction. An account you name that does not exist yet is
            created.
          </div>
        )}

        {!draft && t.labels.length > 0 && (
          <div className="row">
            {t.labels.map((l) => (
              <span key={l} className="pill">
                {l}
              </span>
            ))}
          </div>
        )}

        <div>
          <div className="card-head" style={{ padding: '0 0 6px', border: 'none' }}>
            receipts
          </div>
          {t.attachments.length === 0 && <div className="muted">none attached</div>}
          {t.attachments.map((sha) => (
            <div key={sha} className="mono">
              <a href={api.attachmentUrl(sha)} target="_blank" rel="noreferrer">
                {sha.slice(0, 16)}…
              </a>
            </div>
          ))}
          <div style={{ marginTop: 8 }}>
            <input
              type="file"
              disabled={busy}
              onChange={(e) => {
                const f = e.target.files?.[0]
                if (f) void upload(f)
              }}
            />
          </div>
        </div>

        <div>
          <div className="card-head" style={{ padding: '0 0 6px', border: 'none' }}>
            history
          </div>
          <table>
            <tbody>
              {(revisions.data ?? []).map((r) => (
                <tr key={r.seq}>
                  <td className="mono">{r.at}</td>
                  <td>{r.kind}</td>
                  <td className="muted mono">{r.actor}</td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>

        {t.origins.length > 1 && !draft && (
          <div className="muted">
            Built from {t.origins.length} separate bank lines.{' '}
            <button
              className="btn quiet"
              disabled={busy}
              onClick={() => void unmerge()}
              style={{ padding: '2px 8px' }}
            >
              Unmerge
            </button>
          </div>
        )}

        <div className="row">
          {draft ? (
            <>
              <button className="btn" disabled={busy} onClick={() => void save()}>
                Save
              </button>
              <button className="btn quiet" disabled={busy} onClick={() => setDraft(null)}>
                Cancel
              </button>
            </>
          ) : (
            <button className="btn ghost" onClick={startEdit}>
              Edit
            </button>
          )}
          <button
            className="btn quiet"
            style={{ marginLeft: 'auto' }}
            disabled={busy}
            onClick={() => void remove()}
          >
            Delete
          </button>
        </div>
      </div>
    </div>
  )
}

export default function Ledger({ onBill }: { onBill: (ids: string[]) => void }) {
  const [filterText, setFilterText] = useState('')
  // Sorting is server-side: the list is paginated, so reordering only the
  // fetched page would be a lie about what "largest" means.
  const [sort, setSort] = useState<Sort<LedgerSortKey>>({ key: 'date', dir: 'desc' })
  const [selected, setSelected] = useState<string | null>(null)
  const [picked, setPicked] = useState<Set<string>>(new Set())
  const [merging, setMerging] = useState(false)
  const [mergeError, setMergeError] = useState<string | null>(null)
  const [sharing, setSharing] = useState(false)
  const [shareWith, setShareWith] = useState('')
  const [keepShare, setKeepShare] = useState(true)
  const [moveTo, setMoveTo] = useState('')
  const [asPot, setAsPot] = useState(false)
  const groups = useAsync(() => api.groups(), [])
  const accounts = useAsync(() => api.accounts(), [])

  const togglePick = (id: string) => {
    const next = new Set(picked)
    if (next.has(id)) next.delete(id)
    else next.add(id)
    setPicked(next)
  }
  const filter = useDebounced(filterText)
  const sortParam = (sort.dir === 'desc' ? '-' : '') + sort.key
  const page = useAsync(
    () => api.transactions({ filter, sort: sortParam, limit: '200' }),
    [filter, sortParam],
  )
  const sortBy = (key: LedgerSortKey) =>
    setSort((s) =>
      // Dates and amounts are far more useful largest-first, so they open that way.
      s.key === key
        ? nextSort(s, key)
        : { key, dir: key === 'date' || key === 'amount' ? 'desc' : 'asc' },
    )

  const rows = page.data?.items ?? []

  return (
    <div className="split">
      <div style={{ display: 'flex', flexDirection: 'column', gap: 12 }}>
        <div className="row">
          <input
            className="grow mono"
            type="text"
            placeholder="account:Assets.Bank date>=2026-01-01 -label:private"
            value={filterText}
            onChange={(e) => setFilterText(e.target.value)}
            aria-label="Filter"
          />
        </div>

        {page.error && <div className="error">{page.error}</div>}
        {mergeError && <div className="error">{mergeError}</div>}
        {picked.size >= 1 && (
          <div className="row">
            <span className="muted">move {picked.size} into</span>
            <input
              type="text"
              list="all-accounts"
              style={{ flex: '1 1 220px' }}
              placeholder="Expenses.Trips.HutWeekend — a new name is created"
              value={moveTo}
              onChange={(e) => setMoveTo(e.target.value)}
              aria-label="account to move into"
            />
            <datalist id="all-accounts">
              {(accounts.data ?? []).map((a) => (
                <option key={a.id} value={a.name} />
              ))}
            </datalist>
            <button
              className="btn"
              disabled={sharing || !moveTo}
              onClick={async () => {
                setSharing(true)
                setMergeError(null)
                try {
                  await api.moveMany([...picked], moveTo, asPot)
                  setMoveTo('')
                  page.reload()
                  accounts.reload()
                } catch (e) {
                  setMergeError(e instanceof Error ? e.message : String(e))
                } finally {
                  setSharing(false)
                }
              }}
            >
              Move
            </button>
            <label
              className="row"
              style={{ gap: 5 }}
              title="Move the funding side, so the account becomes a pot the costs were drawn against and paying into it clears it"
            >
              <input type="checkbox" checked={asPot} onChange={(e) => setAsPot(e.target.checked)} />
              <span className="muted">as a pot</span>
            </label>
            <button className="btn ghost" onClick={() => onBill([...picked])}>
              Share these →
            </button>
          </div>
        )}
        {picked.size >= 2 && (
          <div className="row">
            <span className="muted">{picked.size} selected</span>
            <button
              className="btn"
              disabled={merging}
              onClick={async () => {
                setMerging(true)
                setMergeError(null)
                try {
                  const merged = await api.mergeTransactions([...picked])
                  setPicked(new Set())
                  setSelected(merged.id)
                  page.reload()
                } catch (e) {
                  setMergeError(e instanceof Error ? e.message : String(e))
                } finally {
                  setMerging(false)
                }
              }}
            >
              Combine into one transaction
            </button>
            <button className="btn quiet" onClick={() => setPicked(new Set())}>
              Clear
            </button>
          </div>
        )}
        {picked.size >= 1 && (
          <div className="row">
            <span className="muted">share the cost of {picked.size} with</span>
            <input
              type="text"
              list="group-names"
              style={{ flex: '1 1 200px' }}
              placeholder="anna,ben  or a saved group"
              value={shareWith}
              onChange={(e) => setShareWith(e.target.value)}
              aria-label="who to share with"
            />
            <datalist id="group-names">
              {(groups.data ?? []).map((g) => (
                <option key={g.name} value={g.name}>
                  {g.members.join(', ')}
                </option>
              ))}
            </datalist>
            <label className="row" style={{ gap: 5 }}>
              <input
                type="checkbox"
                checked={keepShare}
                onChange={(e) => setKeepShare(e.target.checked)}
              />
              <span className="muted">I keep a share</span>
            </label>
            <button
              className="btn"
              disabled={sharing || !shareWith}
              onClick={async () => {
                setSharing(true)
                setMergeError(null)
                try {
                  // A saved group by name, or names typed straight in.
                  const known = (groups.data ?? []).find((g) => g.name === shareWith.trim())
                  await api.splitMany({
                    ids: [...picked],
                    keepShare,
                    ...(known
                      ? { group: known.name }
                      : {
                          among: shareWith
                            .split(',')
                            .map((x) => x.trim())
                            .filter(Boolean),
                        }),
                  })
                  setPicked(new Set())
                  setShareWith('')
                  page.reload()
                } catch (e) {
                  setMergeError(e instanceof Error ? e.message : String(e))
                } finally {
                  setSharing(false)
                }
              }}
            >
              Split
            </button>
          </div>
        )}

        <div className="card">
          <div className="card-head">
            {page.data ? `${rows.length} of ${page.data.total} transactions` : 'loading…'}
          </div>
          <div className="table-wrap" style={{ maxHeight: '68vh', overflowY: 'auto' }}>
            <table>
              <thead>
                <tr>
                  <th />
                  <SortTh label="date" column="date" sort={sort} onSort={sortBy} />
                  <SortTh label="payee" column="payee" sort={sort} onSort={sortBy} />
                  <SortTh label="narration" column="narration" sort={sort} onSort={sortBy} />
                  <SortTh label="amount" column="amount" sort={sort} onSort={sortBy} numeric />
                  {/* Account and labels are per-posting, so there is no single
                      value to order the whole result set by; they stay plain
                      rather than pretending to sort. */}
                  <th>account</th>
                  <th>labels</th>
                </tr>
              </thead>
              <tbody>
                {rows.map((t) => {
                  const h = t.headline
                  const counter = t.postings.find((p) => p.account !== h?.account)
                  return (
                    <tr
                      key={t.id}
                      className={`clickable${selected === t.id ? ' selected' : ''}`}
                      onClick={() => setSelected(t.id)}
                    >
                      <td onClick={(e) => e.stopPropagation()}>
                        <input
                          type="checkbox"
                          checked={picked.has(t.id)}
                          onChange={() => togglePick(t.id)}
                          aria-label={`select ${t.payee ?? t.id}`}
                        />
                      </td>
                      <td className="mono">{t.date}</td>
                      <td>{t.payee ?? ''}</td>
                      <td className="wrap muted">{t.narration}</td>
                      <td className={`num${(h?.amount.minor ?? 0) < 0 ? ' neg' : ''}`}>
                        {h ? `${h.amount.text} ${h.amount.commodity}` : ''}
                      </td>
                      <td className="muted">
                        {counter?.account ?? h?.account ?? ''}
                        {t.origins.length > 1 && (
                          <span className="pill" style={{ marginLeft: 6 }}>
                            {t.origins.length} lines
                          </span>
                        )}
                      </td>
                      <td>
                        {t.labels.map((l) => (
                          <span key={l} className="pill" style={{ marginRight: 4 }}>
                            {l}
                          </span>
                        ))}
                      </td>
                    </tr>
                  )
                })}
              </tbody>
            </table>
            {rows.length === 0 && !page.loading && <div className="empty">nothing matches</div>}
          </div>
        </div>
      </div>

      {selected ? (
        <Detail
          id={selected}
          onChanged={() => {
            setSelected(null)
            page.reload()
          }}
        />
      ) : (
        <div className="card">
          <div className="card-head">detail</div>
          <div className="empty">Select a transaction.</div>
        </div>
      )}
    </div>
  )
}
