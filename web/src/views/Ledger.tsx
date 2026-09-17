import { useState } from 'react'
import { api } from '../api'
import { SortTh, nextSort, type Sort } from '../components'
import { useAsync, useDebounced } from '../hooks'
import type { Amount, LineItem, Revision, Transaction } from '../types'

type LedgerSortKey = 'date' | 'payee' | 'narration' | 'amount'

type Draft = { date: string; payee: string; narration: string; labels: string; accounts: string[] }

/** Money as text, for a running total the server has not rendered. */
function render(minor: number, like: Amount): string {
  const scale = 10 ** like.exponent
  const sign = minor < 0 ? '-' : ''
  const whole = Math.floor(Math.abs(minor) / scale)
  const frac = String(Math.abs(minor) % scale).padStart(like.exponent, '0')
  return like.exponent === 0 ? `${sign}${whole}` : `${sign}${whole}.${frac}`
}

/**
 * The lines printed on a receipt, and the grouping that turns them into
 * transactions of their own.
 *
 * The lines hardly ever add up to what was paid -- a service charge or a fold
 * in the scanned paper is enough -- so the remainder is shown as it is built up
 * and stays behind as its own transaction rather than being an error.
 */
function Divide({ txn, onDivided }: { txn: Transaction; onDivided: () => void }) {
  const sha = txn.attachments[0] ?? null
  const receipt = useAsync(
    () =>
      sha
        ? api.receipt(sha)
        : Promise.resolve({ sha256: '', total: null, headroom: null, items: [] as LineItem[] }),
    [sha],
  )
  const accounts = useAsync(() => api.accounts(), [])
  const [picked, setPicked] = useState<Map<number, number>>(new Map())
  const [into, setInto] = useState('')
  const [groups, setGroups] = useState<{ items: { line: number; qty?: number }[]; into: string }[]>(
    [],
  )
  const [busy, setBusy] = useState(false)
  const [error, setError] = useState<string | null>(null)
  const [adding, setAdding] = useState({ description: '', qty: '', amount: '' })

  if (!sha) return null
  const lines = receipt.data?.items ?? []
  const headroom = receipt.data?.headroom ?? null
  const stated = receipt.data?.total ?? null

  // Editing renumbers the lines, so any grouping built on the old numbers has
  // to go rather than quietly point at something else.
  const afterEdit = () => {
    setGroups([])
    setPicked(new Map())
    receipt.reload()
  }

  const addLine = async () => {
    if (!adding.description.trim() || !adding.amount.trim()) return
    setBusy(true)
    setError(null)
    try {
      const qty = Number.parseInt(adding.qty, 10)
      await api.addReceiptItem(sha, {
        description: adding.description.trim(),
        ...(Number.isFinite(qty) ? { qty } : {}),
        total: adding.amount.trim(),
      })
      setAdding({ description: '', qty: '', amount: '' })
      afterEdit()
    } catch (e) {
      setError(e instanceof Error ? e.message : String(e))
    } finally {
      setBusy(false)
    }
  }

  const removeLine = async (n: number) => {
    setBusy(true)
    setError(null)
    try {
      await api.removeReceiptItem(sha, n)
      afterEdit()
    } catch (e) {
      setError(e instanceof Error ? e.message : String(e))
    } finally {
      setBusy(false)
    }
  }
  const head = txn.headline?.amount
  const paid = head ? Math.abs(head.minor) : 0
  // Lines are numbered from one, the way `receipt items` shows them. A line can
  // cover several units, and each is claimable on its own.
  const unitsOf = (n: number) => Math.max(1, Math.abs(lines[n - 1]?.qty ?? 1))
  const claimedOn = (n: number) =>
    groups.reduce(
      (acc, g) =>
        acc +
        g.items.filter((it) => it.line === n).reduce((k, it) => k + (it.qty ?? unitsOf(n)), 0),
      0,
    )
  const freeOn = (n: number) => unitsOf(n) - claimedOn(n)

  // The same allocation the server uses, so the figures on screen match what
  // dividing will actually book: the odd minor unit lands on the last unit.
  // Lean divides Int by flooring, not truncating, which only shows on a
  // negative line covering several units. Math.trunc would be off by a minor
  // unit there, and the screen would disagree with what gets booked.
  const cut = (total: number, n: number, i: number) => Math.floor((total * i) / n)
  const shareValue = (line: number, from: number, count: number) => {
    const total = lines[line - 1]?.amount.minor ?? 0
    const units = unitsOf(line)
    return cut(total, units, from + count) - cut(total, units, from)
  }
  const groupValue = (g: { items: { line: number; qty?: number }[] }, upto: number) => {
    // Earlier groups take the earlier units, so a group's value depends on what
    // was claimed before it.
    let used = new Map<number, number>()
    for (let i = 0; i < upto; i++)
      for (const it of groups[i].items)
        used.set(it.line, (used.get(it.line) ?? 0) + (it.qty ?? unitsOf(it.line)))
    let sum = 0
    for (const it of g.items) {
      const from = used.get(it.line) ?? 0
      const count = it.qty ?? unitsOf(it.line)
      sum += shareValue(it.line, from, count)
      used.set(it.line, from + count)
    }
    return sum
  }
  const spokenFor = groups.reduce((acc, g, i) => acc + groupValue(g, i), 0)
  const remainder = paid - spokenFor
  const pickedValue = [...picked.entries()].reduce(
    (acc, [n, k]) => acc + shareValue(n, claimedOn(n), k),
    0,
  )

  const addGroup = () => {
    if (picked.size === 0 || !into.trim()) return
    const items = [...picked.entries()]
      .sort((a, b) => a[0] - b[0])
      .map(([line, qty]) => (qty === unitsOf(line) ? { line } : { line, qty }))
    setGroups([...groups, { items, into: into.trim() }])
    setPicked(new Map())
    setInto('')
  }

  const divide = async () => {
    setBusy(true)
    setError(null)
    try {
      await api.divideTransaction(txn.id, groups)
      setGroups([])
      onDivided()
    } catch (e) {
      setError(e instanceof Error ? e.message : String(e))
    } finally {
      setBusy(false)
    }
  }

  /** Sets how many of line `n` the group being built takes; 0 drops it. */
  const take = (n: number, count: number) => {
    const next = new Map(picked)
    const capped = Math.max(0, Math.min(count, freeOn(n)))
    if (capped === 0) next.delete(n)
    else next.set(n, capped)
    setPicked(next)
  }

  return (
    <div>
      <div className="card-head" style={{ padding: '0 0 6px', border: 'none' }}>
        what this paid for
      </div>
      {lines.length === 0 ? (
        <div className="muted">
          {receipt.loading
            ? 'loading…'
            : 'No lines were read off this receipt. Add them by hand below, or read it again.'}
        </div>
      ) : (
        <>
          <table>
            <thead>
              <tr>
                <th />
                <th className="num">qty</th>
                <th>line</th>
                <th className="num">amount</th>
                <th />
              </tr>
            </thead>
            <tbody>
              {lines.map((it, i) => {
                const n = i + 1
                const units = unitsOf(n)
                const free = freeOn(n)
                const mine = picked.get(n) ?? 0
                return (
                  <tr key={n} className={mine > 0 ? 'selected' : undefined}>
                    <td>
                      {units > 1 ? (
                        <input
                          type="number"
                          min={0}
                          max={free}
                          style={{ width: 54 }}
                          value={mine || ''}
                          placeholder="0"
                          disabled={busy || free === 0}
                          onChange={(e) => take(n, Number.parseInt(e.target.value, 10) || 0)}
                          aria-label={`how many of line ${n}`}
                        />
                      ) : (
                        <input
                          type="checkbox"
                          checked={mine > 0}
                          disabled={busy || free === 0}
                          onChange={() => take(n, mine > 0 ? 0 : 1)}
                          aria-label={`select line ${n}`}
                        />
                      )}
                    </td>
                    <td className="num muted">
                      {units > 1 && free < units ? `${free} of ${units} left` : it.qty}
                    </td>
                    <td className={free === 0 ? 'muted' : undefined}>
                      {it.description}
                      {units > 1 && (
                        <>
                          {' '}
                          <button
                            className="btn quiet"
                            style={{ padding: '0 6px' }}
                            disabled={busy || free === 0}
                            onClick={() => take(n, free)}
                            title="Take all that is left of this line"
                          >
                            all {free}
                          </button>
                        </>
                      )}
                    </td>
                    <td className={`num${it.amount.minor < 0 ? ' neg' : ''}`}>{it.amount.text}</td>
                    <td>
                      <button
                        className="btn quiet"
                        style={{ padding: '2px 8px' }}
                        disabled={busy}
                        title="Remove this line from the receipt"
                        onClick={() => void removeLine(n)}
                      >
                        Remove
                      </button>
                    </td>
                  </tr>
                )
              })}
            </tbody>
          </table>
        </>
      )}

      <div className="row" style={{ marginTop: 8 }}>
        <input
          type="text"
          style={{ minWidth: 200 }}
          value={adding.description}
          placeholder="a line the scan missed"
          aria-label="new line description"
          onChange={(e) => setAdding({ ...adding, description: e.target.value })}
        />
        <input
          type="text"
          style={{ width: 60 }}
          value={adding.qty}
          placeholder="qty"
          aria-label="new line quantity"
          onChange={(e) => setAdding({ ...adding, qty: e.target.value })}
        />
        <input
          type="text"
          style={{ width: 90 }}
          value={adding.amount}
          placeholder="amount"
          aria-label="new line amount"
          onChange={(e) => setAdding({ ...adding, amount: e.target.value })}
          onKeyDown={(e) => {
            if (e.key === 'Enter') void addLine()
          }}
        />
        <button
          className="btn quiet"
          disabled={busy || !adding.description.trim() || !adding.amount.trim()}
          onClick={() => void addLine()}
        >
          Add line
        </button>
        {headroom && stated && (
          <span className={`muted${headroom.minor < 0 ? ' neg' : ''}`} style={{ marginLeft: 'auto' }}>
            {headroom.text} of {stated.text} is not on any line
          </span>
        )}
      </div>

      {lines.length > 0 && (
        <>
          <datalist id="divide-accounts">
            {(accounts.data ?? []).map((a) => (
              <option key={a.id} value={a.name} />
            ))}
          </datalist>
          <div className="row" style={{ marginTop: 8 }}>
            <input
              type="text"
              list="divide-accounts"
              style={{ minWidth: 240 }}
              value={into}
              placeholder="book these lines to…"
              aria-label="account for this group"
              onChange={(e) => setInto(e.target.value)}
            />
            <button
              className="btn quiet"
              disabled={busy || picked.size === 0 || !into.trim()}
              onClick={addGroup}
            >
              Group{head && pickedValue ? ` ${render(pickedValue, head)}` : ''}
            </button>
          </div>

          {groups.length > 0 && head && (
            <div style={{ marginTop: 8 }}>
              <table>
                <tbody>
                  {groups.map((g, i) => (
                    <tr key={i}>
                      <td className="muted">
                        {g.items
                          .map((it) => {
                            const d = lines[it.line - 1]?.description ?? `line ${it.line}`
                            return it.qty === undefined ? d : `${it.qty} × ${d}`
                          })
                          .join(', ')}
                      </td>
                      <td className="mono">{g.into}</td>
                      <td className="num">{render(groupValue(g, i), head)}</td>
                      <td>
                        <button
                          className="btn quiet"
                          style={{ padding: '2px 8px' }}
                          disabled={busy}
                          onClick={() => setGroups(groups.filter((_, j) => j !== i))}
                        >
                          Undo
                        </button>
                      </td>
                    </tr>
                  ))}
                  <tr>
                    <td className="muted">stays behind as a remainder</td>
                    <td className="mono muted">
                      {txn.postings.find((p) => p.amount.minor > 0)?.account ?? ''}
                    </td>
                    <td className={`num${remainder < 0 ? ' neg' : ''}`}>
                      {render(remainder, head)}
                    </td>
                    <td />
                  </tr>
                </tbody>
              </table>
            </div>
          )}

          {remainder < 0 && (
            <div className="error">
              Those lines come to more than the {head?.text} this payment moved.
            </div>
          )}
          {error && <div className="error">{error}</div>}
          <div className="row" style={{ marginTop: 8 }}>
            <button
              className="btn"
              disabled={busy || groups.length === 0 || remainder < 0}
              onClick={() => void divide()}
              title="Each group becomes its own transaction; the rest stays behind"
            >
              Divide into {groups.length + (remainder !== 0 ? 1 : 0)} transaction(s)
            </button>
          </div>
        </>
      )}
    </div>
  )
}

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

        {!draft && (
          <Divide
            txn={t}
            onDivided={() => {
              // The transaction it was divided from is gone, so there is nothing
              // left to show here.
              onChanged()
            }}
          />
        )}

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
