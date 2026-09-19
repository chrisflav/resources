import { useState } from 'react'
import { api } from '../api'
import { useAsync, useDebounced } from '../hooks'
import type { Budget, Invoice, Realm } from '../types'

function Detail({ invoice, onChanged }: { invoice: Invoice; onChanged: () => void }) {
  const [busy, setBusy] = useState(false)
  const setStatus = async (status: string) => {
    setBusy(true)
    try {
      await api.setInvoiceStatus(invoice.id, status)
      onChanged()
    } finally {
      setBusy(false)
    }
  }

  const [error, setError] = useState<string | null>(null)

  // A draft has been shown to nobody, so it can go and take its number with it.
  const remove = async () => {
    setBusy(true)
    setError(null)
    try {
      await api.deleteInvoice(invoice.id)
      onChanged()
    } catch (e) {
      setError(e instanceof Error ? e.message : String(e))
    } finally {
      setBusy(false)
    }
  }

  return (
    <div className="card">
      <div className="card-head">invoice {invoice.number}</div>
      <div className="card-body">
        <div className="spread">
          <div>
            <div style={{ fontSize: 17, fontWeight: 600 }}>{invoice.totalText}</div>
            <div className="muted">to {invoice.payerName}</div>
          </div>
          <span
            className={
              invoice.status === 'paid'
                ? 'pill good'
                : invoice.status === 'sent'
                  ? 'pill warn'
                  : 'pill'
            }
          >
            {invoice.status}
          </span>
        </div>
        <div className="mono muted">
          issued {invoice.issued} · due {invoice.due}
          <br />
          reference {invoice.reference}
          <br />
          payable to {invoice.payment}
        </div>

        <div className="qr">
          <img
            src={api.invoiceQrUrl(invoice.id)}
            alt={`Payment QR for invoice ${invoice.number}`}
          />
        </div>
        <div className="muted" style={{ textAlign: 'center' }}>
          Scanning this fills in the transfer, reference included — which is how the invoice settles
          itself when the payment lands in the next bank import.
        </div>

        <div className="table-wrap">
          <table>
            <thead>
              <tr>
                <th>description</th>
                <th className="num">qty</th>
                <th className="num">net</th>
              </tr>
            </thead>
            <tbody>
              {invoice.lines.map((l, i) => (
                <tr key={i}>
                  <td>{l.description}</td>
                  <td className="num">{l.quantity}</td>
                  <td className="num">{(l.net / 100).toFixed(2)}</td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>

        {error && <div className="error">{error}</div>}
        <div className="muted">
          This is a document about a share that was already decided, so nothing here moves money.
          The allocation recorded who bears what; when {invoice.payerName} transfers their share it
          arrives in the next bank import, and the reference above closes this invoice.
        </div>

        <div className="row">
          <a
            className="btn ghost"
            href={api.invoicePdfUrl(invoice.id)}
            target="_blank"
            rel="noreferrer"
          >
            PDF
          </a>
          {invoice.status === 'draft' && (
            <button className="btn" disabled={busy} onClick={() => void setStatus('sent')}>
              Mark sent
            </button>
          )}
          {invoice.status !== 'paid' && (
            <button className="btn quiet" disabled={busy} onClick={() => void setStatus('paid')}>
              Mark paid
            </button>
          )}
          {invoice.status !== 'void' && invoice.status !== 'draft' && (
            <button className="btn quiet" disabled={busy} onClick={() => void setStatus('void')}>
              Void
            </button>
          )}
          {invoice.status === 'draft' && (
            <button className="btn quiet" disabled={busy} onClick={() => void remove()}>
              Delete
            </button>
          )}
        </div>
      </div>
    </div>
  )
}

/** One row of the allocation editor: a person and where their share lands. */
type Bearer = { name: string; account: string; weight: string }

const ME: Bearer = { name: '', account: '', weight: '1' }

/**
 * Putting a budget in front of the people who were there.
 *
 * The costs move into a realm of the budget's own -- an account stays in the
 * realm it was written in, so they are re-entered through a purse rather than
 * relabelled -- and everybody with a link can then say which of them were
 * theirs. What they say is here: a cost several people take is split equally
 * between them when the budget is divided, and what nobody takes is divided by
 * the shares above, which is what a budget did before anybody could take
 * anything.
 */
function Share({ budget, onChanged }: { budget: Budget; onChanged: () => void }) {
  const [guests, setGuests] = useState('')
  const [invites, setInvites] = useState<{ for: string; link: string }[]>([])
  const [busy, setBusy] = useState(false)
  const [error, setError] = useState<string | null>(null)
  // The costs themselves, so that the person running the budget can take one
  // too, and can take one back off somebody who has gone quiet.
  const detail = useAsync(() => api.budget(budget.shortName), [budget.shortName, budget.taken])
  const costs = detail.data?.items ?? []
  const takenBy = (id: string) => budget.taken.find((t) => t.txn === id)

  const named = () =>
    guests
      .split(',')
      .map((g) => g.trim())
      .filter((g) => g !== '')

  const run = async (what: () => Promise<unknown>) => {
    setBusy(true)
    setError(null)
    try {
      await what()
      onChanged()
      detail.reload()
    } catch (e) {
      setError(e instanceof Error ? e.message : String(e))
    } finally {
      setBusy(false)
    }
  }

  const mine = (txn: string, already: boolean) =>
    run(() =>
      already
        ? api.releaseCost(budget.shortName, txn)
        : api.claimCost(budget.shortName, txn),
    )

  const release = (txn: string, member: string) =>
    run(() => api.releaseCost(budget.shortName, txn, member))

  const share = async () => {
    setBusy(true)
    setError(null)
    try {
      const made = await api.shareBudget(budget.shortName, { with: named() })
      setInvites(made.invites.map((i) => ({ for: i.for, link: i.link })))
      setGuests('')
      onChanged()
    } catch (e) {
      setError(e instanceof Error ? e.message : String(e))
    } finally {
      setBusy(false)
    }
  }

  return (
    <div className="card-body">
      <div className="row">
        <input
          type="text"
          style={{ minWidth: 240 }}
          value={guests}
          placeholder="names to send a link to, comma separated"
          aria-label="who to share this budget with"
          onChange={(e) => setGuests(e.target.value)}
        />
        <button className="btn quiet" disabled={busy || budget.closed} onClick={() => void share()}>
          Share this budget
        </button>
      </div>
      {costs.length > 0 && (
        <div className="table-wrap" style={{ marginTop: 8 }}>
          <table>
            <thead>
              <tr>
                <th>date</th>
                <th>cost</th>
                <th className="num">amount</th>
                <th>taken by</th>
                <th />
              </tr>
            </thead>
            <tbody>
              {costs.map((t) => {
                const taken = takenBy(t.id)
                const who = taken?.who ?? []
                return (
                  <tr key={t.id}>
                    <td className="mono">{t.date}</td>
                    <td>{t.payee ?? t.narration}</td>
                    <td className="num">{t.headline?.amount.text ?? ''}</td>
                    <td className="muted">{who.join(', ')}</td>
                    <td>
                      {!budget.closed && (
                        <>
                          <button
                            className="btn quiet"
                            style={{ padding: '2px 8px', marginRight: 6 }}
                            disabled={busy}
                            onClick={() => void mine(t.id, who.includes('me'))}
                            title="A cost several people take is split equally between them"
                          >
                            {who.includes('me') ? 'not mine' : 'mine'}
                          </button>
                          {(taken?.members ?? []).map((m, i) => (
                            <button
                              key={m}
                              className="btn quiet"
                              style={{ padding: '2px 8px', marginRight: 4 }}
                              disabled={busy}
                              onClick={() => void release(t.id, m)}
                              title={`Take this off ${who[i] ?? m}`}
                            >
                              × {who[i] ?? m}
                            </button>
                          ))}
                        </>
                      )}
                    </td>
                  </tr>
                )
              })}
            </tbody>
          </table>
        </div>
      )}
      {invites.length > 0 && (
        <div className="table-wrap" style={{ marginTop: 8 }}>
          <table>
            <tbody>
              {invites.map((i) => (
                <tr key={i.link}>
                  <td>{i.for}</td>
                  <td className="mono">{i.link}</td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
      )}
      {error && <div className="error">{error}</div>}
    </div>
  )
}

/**
 * Sharing: budgets, where everybody stands, and the documents that say so.
 *
 * These used to be two screens because they looked like two workflows. They are
 * one. A payment several people bear is a loan from whichever account paid it —
 * yours or theirs — into an auxiliary budget; dividing that budget says whose
 * the spending was. Whether you bear a share is the only difference between
 * "someone owes me this" and "we split this", and it is one row in the table
 * below.
 *
 * Two things are kept apart here because they are two facts. Dividing a budget
 * decides whose the spending was, and is true the moment it is decided. Who
 * still has to pay whom is a claim: a transaction that has not happened, which
 * reaches no balance until it does.
 */
export default function Sharing({
  initialPicked = [],
  onConsumed,
}: {
  initialPicked?: string[]
  onConsumed?: () => void
}) {
  const budgets = useAsync(() => api.budgets(), [])
  const invoices = useAsync(() => api.invoices(), [])
  const accounts = useAsync(() => api.accounts(), [])
  const book = useAsync(() => api.contacts(), [])
  const [openOnly, setOpenOnly] = useState(true)
  const people = useAsync(() => api.people(), [])

  const [selected, setSelected] = useState<string | null>(null)
  const [openBudget, setOpenBudget] = useState<string | null>(null)
  const [expanded, setExpanded] = useState<string | null>(null)
  const [busy, setBusy] = useState(false)
  const [error, setError] = useState<string | null>(null)
  const [notice, setNotice] = useState<string | null>(null)

  // 1 · lend
  const [newName, setNewName] = useState('')
  const [pickFilter, setPickFilter] = useState('')
  const [picked, setPicked] = useState<Set<string>>(new Set(initialPicked))
  const debouncedPick = useDebounced(pickFilter)
  const candidates = useAsync(
    () =>
      debouncedPick
        ? api.transactions({ filter: debouncedPick, sort: 'date', limit: '200' })
        : Promise.resolve(null),
    [debouncedPick],
  )

  // 2 · allocate
  const [bearers, setBearers] = useState<Bearer[]>([{ name: '', account: '', weight: '1' }])
  const [through, setThrough] = useState('')
  // Whichever budget is open, the editor starts from what it already says, so
  // changing one person is changing one field rather than retyping everybody.
  const [shownFor, setShownFor] = useState<string | null>(null)

  // …and what somebody else paid for out of their own account
  const [theirName, setTheirName] = useState('')
  const [theirAmount, setTheirAmount] = useState('')
  const [theirWhat, setTheirWhat] = useState('')

  // …and the realm that lets them do it themselves
  const [shareWith, setShareWith] = useState('')
  const [shareRole, setShareRole] = useState('viewer')
  const [linkFor, setLinkFor] = useState<string | null>(null)
  const [newRealm, setNewRealm] = useState('')
  const [openRealm, setOpenRealm] = useState<string | null>(null)
  const realms = useAsync(() => api.realms(), [])
  const members = useAsync(
    () => (openRealm ? api.realmMembers(openRealm) : Promise.resolve(null)),
    [openRealm],
  )
  const sync = useAsync(() => api.syncStatus(), [])

  // 3 · write up
  const [beneficiary, setBeneficiary] = useState('')
  const [iban, setIban] = useState('')
  const [link, setLink] = useState('')
  const [due, setDue] = useState('')

  const list = invoices.data ?? []
  const current = list.find((i) => i.id === selected) ?? null
  const all: Budget[] = budgets.data ?? []
  const budget = all.find((b) => b.name === openBudget) ?? null
  const rows = (people.data ?? []).filter((p) => !openOnly || p.net !== 0 || p.claims.length > 0)
  const outstanding = (b: Budget) => b.claims.filter((c) => c.state === 'pending')

  const guard = async (what: () => Promise<void>) => {
    setBusy(true)
    setError(null)
    setNotice(null)
    try {
      await what()
    } catch (e) {
      setError(e instanceof Error ? e.message : String(e))
    } finally {
      setBusy(false)
    }
  }

  const lend = () =>
    guard(async () => {
      const ids = [...picked]
      if (openBudget && !newName) {
        const r = await api.lendToBudget(openBudget, ids)
        setNotice(`lent ${r.lent} cost(s) into ${r.budget}`)
      } else {
        const r = await api.createBudget(newName, ids)
        setNotice(`${r.name} — lent ${r.lent} cost(s)`)
        setOpenBudget(r.name)
        setNewName('')
      }
      setPicked(new Set())
      setPickFilter('')
      onConsumed?.()
      budgets.reload()
    })

  // Saved once. Everything after this is booked already divided, which is the
  // whole of what the "divide it" step used to be for.
  const saveAmong = () =>
    guard(async () => {
      if (!budget) return
      const among = bearers
        .filter((b) => b.name.trim() || b.account.trim())
        .map((b) => ({
          name: b.name.trim(),
          account: b.account.trim(),
          weight: Number(b.weight) || 1,
        }))
      const r = await api.setBudgetParticipants(budget.shortName, among)
      setNotice(
        r.undivided.minor === 0
          ? 'saved'
          : `saved — ${r.undivided.text} is waiting, and closing the budget divides it`,
      )
      budgets.reload()
      people.reload()
    })

  // Closing is the decision. Until it happens costs just accumulate, which is
  // what the budget account is for.
  const close = () =>
    guard(async () => {
      if (!budget) return
      const r = await api.closeBudget(budget.shortName, {
        ...(through ? { through } : {}),
      })
      setNotice(
        r.division
          ? 'closed and divided; nobody can add to it now'
          : 'closed; there was nothing left to divide',
      )
      budgets.reload()
      people.reload()
    })

  const reopen = () =>
    guard(async () => {
      if (!budget) return
      await api.reopenBudget(budget.shortName)
      setNotice('open again — every division already made still stands')
      budgets.reload()
    })

  const settle = () =>
    guard(async () => {
      if (!budget) return
      const r = await api.settleBudget(budget.shortName, through || undefined)
      setNotice(
        r.claims.length === 0
          ? 'nothing more to ask for'
          : `${r.claims.length} payment(s) would settle it`,
      )
      budgets.reload()
      people.reload()
    })

  const contribute = () =>
    guard(async () => {
      if (!budget) return
      await api.contributeToBudget(budget.shortName, {
        who: theirName.trim(),
        amount: theirAmount.trim(),
        narration: theirWhat.trim(),
        payee: theirWhat.trim(),
      })
      setNotice(`recorded what ${theirName.trim()} paid for`)
      setTheirAmount('')
      setTheirWhat('')
      budgets.reload()
      people.reload()
    })

  const allRealms: Realm[] = realms.data ?? []
  const realmOf = (b: Budget) => allRealms.find((r) => r.budget === b.shortName) ?? null
  const realm = allRealms.find((r) => r.id === openRealm) ?? null

  // Sharing a budget is making the realm it lives in, and inviting somebody to
  // that. A realm is one key and one set of members; the invite is a pending
  // grant on the sequencer, and redeeming it makes them a member with a key of
  // their own rather than a caller with fewer rights.
  const shareBudget = (b: Budget) =>
    guard(async () => {
      const found = realmOf(b)
      if (found) {
        setOpenRealm(found.id)
        return
      }
      const made = await api.createRealm({ name: b.shortName, budget: b.shortName })
      setOpenRealm(made.id)
      setNotice(`${made.name} is a realm now — invite somebody to it below`)
      realms.reload()
      budgets.reload()
    })

  const startRealm = () =>
    guard(async () => {
      const made = await api.createRealm({ name: newRealm.trim(), budget: newRealm.trim() })
      setNewRealm('')
      setOpenRealm(made.id)
      setNotice(`${made.name} is open — lend costs into ${made.budget ?? made.name}`)
      realms.reload()
      budgets.reload()
    })

  const invite = (id: string) =>
    guard(async () => {
      const made = await api.inviteToRealm(id, { for: shareWith.trim(), role: shareRole })
      setLinkFor(made.link)
      setShareWith('')
      members.reload()
    })

  // Said beside the button as well as at the top of the page. A round is run
  // from the bottom of a long two-column view, and a banner above the fold that
  // the reader never scrolls back to is indistinguishable from a button that
  // does nothing — which is exactly how a failing round looked.
  const [syncSaid, setSyncSaid] = useState<{ trouble: boolean; text: string } | null>(null)

  const syncNow = async () => {
    setSyncSaid(null)
    await guard(async () => {
      try {
        const r = await api.syncNow()
        const text =
          r.trouble || `${r.applied} in, ${r.pushed} out; the shared order stands at entry ${r.seq}`
        setSyncSaid({ trouble: r.trouble !== '', text })
        setNotice(text)
      } catch (e) {
        const text = e instanceof Error ? e.message : String(e)
        setSyncSaid({ trouble: true, text })
        throw e
      }
      sync.reload()
      realms.reload()
      budgets.reload()
    })
  }

  const writeUp = () =>
    guard(async () => {
      if (!budget) return
      const created = await api.createInvoice({
        budget: budget.shortName,
        due: due || undefined,
        ...(link ? { paymentLink: link } : { beneficiary, iban }),
      })
      setNotice(`raised ${created.count} invoice(s)`)
      setSelected(created.items[0]?.id ?? null)
      invoices.reload()
    })

  const contacts = book.data?.items ?? []

  if (budget && budget.name !== shownFor) {
    setShownFor(budget.name)
    setBearers(
      budget.among.length === 0
        ? [{ ...ME }]
        : budget.among.map((p) => ({
            name: p.mine ? '' : p.name,
            account: p.account,
            weight: String(p.weight),
          })),
    )
  }

  return (
    <div style={{ display: 'flex', flexDirection: 'column', gap: 18 }}>
      {error && <div className="error">{error}</div>}
      {notice && <div className="muted">{notice}</div>}

      <div className="grid-2">
        {(people.data ?? [])
          .filter((p) => p.net !== 0)
          .map((p) => (
            <div className="stat" key={p.party}>
              <div className="k">{p.net > 0 ? `${p.name} owes you` : `you owe ${p.name}`}</div>
              <div className="v">{p.netText}</div>
              <div className="muted" style={{ fontSize: 12 }}>
                {p.claims.filter((c) => c.state === 'pending').length} payment(s) outstanding
              </div>
            </div>
          ))}
        {all
          .filter((b) => b.outstanding.minor !== 0)
          .map((b) => (
            <div className="stat" key={b.id}>
              <div className="k">{b.shortName} — not yet divided</div>
              <div className="v">{b.outstanding.text}</div>
              <div className="muted" style={{ fontSize: 12 }}>
                paid out, nobody assigned to it
              </div>
            </div>
          ))}
      </div>

      <div className="split">
        <div style={{ display: 'flex', flexDirection: 'column', gap: 18 }}>
          <div className="card">
            <div className="card-head">budgets — money laid out, divided later</div>
            <div className="table-wrap">
              <table>
                <thead>
                  <tr>
                    <th>budget</th>
                    <th className="num">costs</th>
                    <th className="num">undivided</th>
                    <th className="num">allocated</th>
                    <th className="num">to settle</th>
                  </tr>
                </thead>
                <tbody>
                  {all.map((b) => (
                    <tr
                      key={b.id}
                      className={`clickable${openBudget === b.name ? ' selected' : ''}`}
                      onClick={() => setOpenBudget(openBudget === b.name ? null : b.name)}
                    >
                      <td>{b.shortName}</td>
                      <td className="num">{b.costs}</td>
                      <td className={`num${b.outstanding.minor !== 0 ? ' warn' : ''}`}>
                        {b.outstanding.text}
                      </td>
                      <td className="num">{b.allocated.text}</td>
                      <td className="num">{outstanding(b).length}</td>
                    </tr>
                  ))}
                </tbody>
              </table>
              {all.length === 0 && !budgets.loading && (
                <div className="empty">
                  Nothing shared yet. Pick the costs on the right to start a budget.
                </div>
              )}
            </div>
          </div>

          {budget && (
            <div className="card">
              <div className="card-head">
                <div className="spread">
                  <span>{budget.shortName} — who bears what</span>
                  <span className="mono muted">{budget.name}</span>
                </div>
              </div>
              <div className="table-wrap">
                <table>
                  <thead>
                    <tr>
                      <th>person</th>
                      <th className="num">borne, less what they put in</th>
                      <th />
                    </tr>
                  </thead>
                  <tbody>
                    {budget.standings.map((st) => (
                      <tr key={st.owner}>
                        <td>{st.name}</td>
                        <td className={`num${st.owes ? '' : ' neg'}`}>{st.amount.text}</td>
                        <td>
                          {st.amount.minor === 0 ? (
                            <span className="pill good">square</span>
                          ) : st.owes ? (
                            <span className="pill warn">short</span>
                          ) : (
                            <span className="pill">has fronted more</span>
                          )}
                        </td>
                      </tr>
                    ))}
                  </tbody>
                </table>
                {budget.standings.length === 0 && <div className="empty">Not divided yet.</div>}
              </div>

              <Share budget={budget} onChanged={() => budgets.reload()} />

              {budget.claims.length > 0 && (
                <div className="table-wrap">
                  <table>
                    <thead>
                      <tr>
                        <th>from</th>
                        <th>to</th>
                        <th className="num">amount</th>
                        <th>state</th>
                      </tr>
                    </thead>
                    <tbody>
                      {budget.claims.map((c) => (
                        <tr key={c.id}>
                          <td>{c.from}</td>
                          <td>{c.to}</td>
                          <td className="num">{c.amount.text}</td>
                          <td>
                            <span
                              className={
                                c.state === 'settled'
                                  ? 'pill good'
                                  : c.state === 'pending'
                                    ? 'pill warn'
                                    : 'pill'
                              }
                            >
                              {c.state}
                            </span>
                          </td>
                        </tr>
                      ))}
                    </tbody>
                  </table>
                  <div className="card-body">
                    <div className="muted">
                      These payments have not happened. They reach no balance until they do — which
                      is why writing one off leaves whose the spending was exactly where it is.
                    </div>
                  </div>
                </div>
              )}

              <div className="card-body">
                <div className="card-head" style={{ padding: '0 0 6px', border: 'none' }}>
                  what somebody else paid for
                </div>
                <div className="row">
                  <input
                    type="text"
                    list="bearer-names"
                    style={{ flex: '1 1 130px' }}
                    placeholder="who paid"
                    value={theirName}
                    onChange={(e) => setTheirName(e.target.value)}
                    aria-label="who paid"
                  />
                  <input
                    type="text"
                    style={{ flex: '1 1 160px' }}
                    placeholder="what for"
                    value={theirWhat}
                    onChange={(e) => setTheirWhat(e.target.value)}
                    aria-label="what they paid for"
                  />
                  <input
                    type="text"
                    inputMode="decimal"
                    style={{ width: 90 }}
                    placeholder="42.50"
                    value={theirAmount}
                    onChange={(e) => setTheirAmount(e.target.value)}
                    aria-label="how much they paid"
                  />
                  <button
                    className="btn quiet"
                    disabled={busy || !theirName.trim() || !theirAmount.trim()}
                    onClick={() => void contribute()}
                  >
                    Record it
                  </button>
                </div>
                <div className="muted">
                  It goes into the budget out of an account of theirs, exactly as one of yours does,
                  and is set against their own share when everything is divided. None of it is ever
                  counted as your money.
                </div>
              </div>

              <div className="card-body">
                <div className="card-head" style={{ padding: '0 0 6px', border: 'none' }}>
                  let them add their own
                </div>
                <div className="row">
                  <button
                    className="btn quiet"
                    disabled={busy}
                    onClick={() => void shareBudget(budget)}
                  >
                    {realmOf(budget) ? 'Invite somebody' : 'Share this budget'}
                  </button>
                  <span className="muted">
                    {realmOf(budget)
                      ? `in realm ${realmOf(budget)?.name}`
                      : 'this budget is yours alone'}
                  </span>
                </div>
                <div className="muted">
                  Sharing a budget is making the realm it lives in and inviting somebody to that.
                  Whoever redeems the invite becomes a member with a key of their own and a purse
                  in the realm, and can put what they paid for straight into the budget.
                </div>
              </div>

              <div className="card-body">
                <div className="card-head" style={{ padding: '0 0 6px', border: 'none' }}>
                  2 · who shares this
                </div>
                  <datalist id="bearer-names">
                    {contacts.map((c) => (
                      <option key={c.name} value={c.name} />
                    ))}
                  </datalist>
                  <datalist id="bearer-accounts">
                    {(accounts.data ?? []).map((a) => (
                      <option key={a.id} value={a.name} />
                    ))}
                  </datalist>
                  {bearers.map((b, i) => (
                    <div className="row" key={i} style={{ gap: 6, marginTop: 4 }}>
                      <input
                        type="text"
                        list="bearer-names"
                        style={{ flex: '1 1 130px' }}
                        placeholder="who (blank = me)"
                        value={b.name}
                        onChange={(e) =>
                          setBearers(
                            bearers.map((x, j) => (i === j ? { ...x, name: e.target.value } : x)),
                          )
                        }
                        aria-label={`person ${i + 1}`}
                      />
                      <input
                        className="mono"
                        type="text"
                        list="bearer-accounts"
                        style={{ flex: '1 1 190px' }}
                        placeholder={b.name.trim() ? 'their purse (automatic)' : 'which expense?'}
                        value={b.account}
                        onChange={(e) =>
                          setBearers(
                            bearers.map((x, j) =>
                              i === j ? { ...x, account: e.target.value } : x,
                            ),
                          )
                        }
                        aria-label={`account for person ${i + 1}`}
                      />
                      <input
                        type="text"
                        style={{ width: 52 }}
                        value={b.weight}
                        onChange={(e) =>
                          setBearers(
                            bearers.map((x, j) => (i === j ? { ...x, weight: e.target.value } : x)),
                          )
                        }
                        aria-label={`weight for person ${i + 1}`}
                      />
                      <button
                        className="btn quiet"
                        style={{ padding: '2px 9px' }}
                        disabled={bearers.length === 1}
                        onClick={() => setBearers(bearers.filter((_, j) => j !== i))}
                        aria-label={`remove person ${i + 1}`}
                      >
                        ×
                      </button>
                    </div>
                  ))}
                  <div className="row" style={{ marginTop: 6 }}>
                    <button
                      className="btn quiet"
                      onClick={() =>
                        setBearers([...bearers, { name: '', account: '', weight: '1' }])
                      }
                    >
                      Add person
                    </button>
                    <input
                      type="text"
                      list="bearer-names"
                      style={{ flex: '1 1 150px' }}
                      placeholder="settle through… (optional)"
                      value={through}
                      onChange={(e) => setThrough(e.target.value)}
                      aria-label="settle through"
                    />
                    <button
                      className="btn quiet"
                      disabled={busy || !bearers.some((b) => b.name.trim() || b.account.trim())}
                      onClick={() => void saveAmong()}
                    >
                      Save
                    </button>
                    {budget.closed ? (
                      <button className="btn" disabled={busy} onClick={() => void reopen()}>
                        Reopen
                      </button>
                    ) : (
                      <button
                        className="btn"
                        disabled={busy || budget.among.length === 0}
                        onClick={() => void close()}
                      >
                        Close and divide {budget.outstanding.text}
                      </button>
                    )}
                  </div>
                  <div className="muted">
                    Say who shares it once; closing is what divides it. Until you close, costs
                    just accumulate — which is what the budget account is for. Closing also stops
                    anybody adding to it, including everybody else in its realm.
                  </div>
                  <div className="muted">
                    Reopening leaves every division already made exactly as it is. Closing again
                    writes a new one covering only what came in since, because somebody was told
                    what they owed on the strength of the first.
                  </div>
                  <div className="muted">
                    Leave the name blank for your own share, and say which expense account it
                    belongs to — that is what turns money you consumed into a classified expense
                    rather than a claim on somebody. Everyone else's share lands in an account of
                    their own. The weight is for unequal shares; leave it at 1 for an even split.
                  </div>
                  <div className="muted">
                    What everybody has already put in is netted against their share, so the
                    payments asked for are as few as they can be. Naming somebody to settle through
                    routes them all via that one person instead — the same number in the worst
                    case, and a good deal less explaining.
                  </div>
                </div>

              {budget.standings.length > 0 && budget.outstanding.minor === 0 && (
                <div className="card-body">
                  <div className="row">
                    <button className="btn quiet" disabled={busy} onClick={() => void settle()}>
                      Work out who pays whom
                    </button>
                  </div>
                  <div className="muted">
                    Closing does this already. Run it again after writing a claim off or voiding an
                    invoice: it nets off whatever has been asked for and raises only the difference.
                  </div>
                </div>
              )}

              {outstanding(budget).length > 0 && (
                <div className="card-body">
                  <div className="card-head" style={{ padding: '0 0 6px', border: 'none' }}>
                    3 · write the claims up as invoices
                  </div>
                  <div className="row">
                    <label className="field" style={{ flex: '1 1 180px' }}>
                      Beneficiary (SEPA)
                      <input
                        type="text"
                        value={beneficiary}
                        onChange={(e) => setBeneficiary(e.target.value)}
                      />
                    </label>
                    <label className="field" style={{ flex: '1 1 180px' }}>
                      IBAN
                      <input type="text" value={iban} onChange={(e) => setIban(e.target.value)} />
                    </label>
                    <label className="field">
                      Due
                      <input type="date" value={due} onChange={(e) => setDue(e.target.value)} />
                    </label>
                  </div>
                  <label className="field">
                    …or a payment link instead of a SEPA QR
                    <input
                      type="text"
                      placeholder="https://paypal.me/…"
                      value={link}
                      onChange={(e) => setLink(e.target.value)}
                    />
                  </label>
                  <div className="row">
                    <button
                      className="btn"
                      disabled={busy || (!link && !iban)}
                      onClick={() => void writeUp()}
                    >
                      Write up
                    </button>
                  </div>
                  <div className="muted">
                    One invoice per outstanding payment addressed to you, each to one person.
                    Nothing is divided here and no money moves — the division already happened, and
                    this asks for the payment that has not. Your own share gets no invoice: it is
                    not a claim, you bore it when you paid.
                  </div>
                </div>
              )}
            </div>
          )}

          <div className="card">
            <div className="card-head">
              <div className="spread">
                <span>what passes between you and everybody else</span>
                <label className="row" style={{ gap: 6, textTransform: 'none', letterSpacing: 0 }}>
                  <input
                    type="checkbox"
                    checked={openOnly}
                    onChange={(e) => setOpenOnly(e.target.checked)}
                  />
                  only those not yet square
                </label>
              </div>
            </div>
            <div className="table-wrap">
              <table>
                <thead>
                  <tr>
                    <th>person</th>
                    <th className="num">net</th>
                    <th className="num">outstanding</th>
                    <th />
                  </tr>
                </thead>
                <tbody>
                  {rows.map((p) => (
                    <tr
                      key={p.party}
                      className="clickable"
                      onClick={() => setExpanded(expanded === p.party ? null : p.party)}
                    >
                      <td>{p.name}</td>
                      <td className={`num${p.net < 0 ? ' neg' : ''}`}>
                        <strong>{p.netText}</strong>
                      </td>
                      <td className="num">
                        {p.claims.filter((c) => c.state === 'pending').length}
                      </td>
                      <td>
                        {p.net > 0 ? (
                          <span className="pill warn">owed to you</span>
                        ) : p.net < 0 ? (
                          <span className="pill">you owe them</span>
                        ) : (
                          <span className="pill good">square</span>
                        )}
                      </td>
                    </tr>
                  ))}
                </tbody>
              </table>
              {rows.length === 0 && !people.loading && (
                <div className="empty">You are square with everybody.</div>
              )}
            </div>
            <div className="card-body">
              <div className="muted">
                Their own accounts carry the figure, so none of it has ever been counted as yours.
                A positive net is money they owe you; negative is money you owe them.
              </div>
            </div>
          </div>

          {rows
            .filter((p) => p.party === expanded)
            .map((p) => (
              <div className="card" key={p.party}>
                <div className="card-head">{p.name} — their accounts, and what is asked</div>
                <div className="table-wrap">
                  <table>
                    <thead>
                      <tr>
                        <th>account</th>
                        <th className="num">balance</th>
                      </tr>
                    </thead>
                    <tbody>
                      {p.balances.map((b) => (
                        <tr key={b.account}>
                          <td className="mono">{b.account}</td>
                          <td className={`num${b.minor < 0 ? ' neg' : ''}`}>{b.text}</td>
                        </tr>
                      ))}
                    </tbody>
                  </table>
                </div>
                {p.claims.length > 0 && (
                  <div className="table-wrap">
                    <table>
                      <thead>
                        <tr>
                          <th>due</th>
                          <th>from</th>
                          <th>to</th>
                          <th className="num">amount</th>
                          <th>state</th>
                        </tr>
                      </thead>
                      <tbody>
                        {p.claims.map((c) => (
                          <tr key={c.id}>
                            <td className="mono">{c.due}</td>
                            <td>{c.from}</td>
                            <td>{c.to}</td>
                            <td className="num">{c.amount.text}</td>
                            <td>
                              <span className={c.state === 'pending' ? 'pill warn' : 'pill good'}>
                                {c.state}
                              </span>
                            </td>
                          </tr>
                        ))}
                      </tbody>
                    </table>
                    <div className="card-body">
                      <div className="muted">
                        Each of these names one specific thing. A part payment reduces the one it
                        was for, rather than being aged against whatever is oldest.
                      </div>
                    </div>
                  </div>
                )}
              </div>
            ))}

          <div className="card">
            <div className="card-head">invoices</div>
            <div className="table-wrap">
              <table>
                <thead>
                  <tr>
                    <th>number</th>
                    <th>payer</th>
                    <th>due</th>
                    <th className="num">total</th>
                    <th>status</th>
                  </tr>
                </thead>
                <tbody>
                  {list.map((i) => (
                    <tr
                      key={i.id}
                      className={`clickable${selected === i.id ? ' selected' : ''}`}
                      onClick={() => setSelected(i.id)}
                    >
                      <td className="mono">{i.number}</td>
                      <td>{i.payerName}</td>
                      <td className="mono">{i.due}</td>
                      <td className="num">{i.totalText}</td>
                      <td>
                        <span
                          className={
                            i.status === 'paid'
                              ? 'pill good'
                              : i.status === 'sent'
                                ? 'pill warn'
                                : 'pill'
                          }
                        >
                          {i.status}
                        </span>
                      </td>
                    </tr>
                  ))}
                </tbody>
              </table>
              {list.length === 0 && <div className="empty">No invoices yet.</div>}
            </div>
          </div>

          <div className="card">
            <div className="card-head">realms — one key, one set of members</div>
            <div className="table-wrap">
              <table>
                <thead>
                  <tr>
                    <th>realm</th>
                    <th>budget</th>
                    <th className="num">generation</th>
                    <th className="num">members</th>
                    <th>key</th>
                  </tr>
                </thead>
                <tbody>
                  {allRealms.map((r) => (
                    <tr
                      key={r.id}
                      className={`clickable${openRealm === r.id ? ' selected' : ''}`}
                      onClick={() => setOpenRealm(openRealm === r.id ? null : r.id)}
                    >
                      <td>{r.name}</td>
                      <td>{r.budget ?? ''}</td>
                      <td className="num">{r.generation}</td>
                      <td className="num">{r.members.length}</td>
                      <td>
                        {r.hasKey ? (
                          <span className="pill good">held here</span>
                        ) : (
                          <span className="pill">not held here</span>
                        )}
                      </td>
                    </tr>
                  ))}
                </tbody>
              </table>
              {allRealms.length === 0 && !realms.loading && (
                <div className="empty">No realms yet.</div>
              )}
            </div>

            {realm && (
              <>
                <div className="table-wrap">
                  <table>
                    <thead>
                      <tr>
                        <th>member</th>
                        <th>role</th>
                        <th>key</th>
                      </tr>
                    </thead>
                    <tbody>
                      {(members.data?.members ?? realm.members).map((m) => (
                        <tr key={m.id}>
                          <td>
                            {m.name}
                            {m.mine ? ' (you)' : ''}
                          </td>
                          <td>{m.role}</td>
                          <td className="muted">
                            {members.data?.granted == null
                              ? '—'
                              : members.data.granted.includes(m.id)
                                ? 'held'
                                : 'none'}
                          </td>
                        </tr>
                      ))}
                    </tbody>
                  </table>
                </div>
                <div className="card-body">
                  <div className="row">
                    <input
                      type="text"
                      list="bearer-names"
                      style={{ flex: '1 1 160px' }}
                      placeholder="who to invite"
                      value={shareWith}
                      onChange={(e) => setShareWith(e.target.value)}
                      aria-label="who to invite"
                    />
                    <select
                      value={shareRole}
                      onChange={(e) => setShareRole(e.target.value)}
                      aria-label="what they may do"
                    >
                      <option value="viewer">viewer</option>
                      <option value="admin">admin</option>
                    </select>
                    <button
                      className="btn quiet"
                      disabled={busy || !shareWith.trim()}
                      onClick={() => void invite(realm.id)}
                    >
                      Make an invite
                    </button>
                  </div>
                  {linkFor && (
                    <>
                      <input
                        className="mono"
                        type="text"
                        readOnly
                        value={linkFor}
                        aria-label="invite link"
                        onFocus={(e) => e.currentTarget.select()}
                      />
                      <div className="row">
                        <button
                          className="btn quiet"
                          onClick={() => void navigator.clipboard?.writeText(linkFor)}
                        >
                          Copy link
                        </button>
                      </div>
                      <div className="muted">
                        Send it once. The secret is in the fragment after the #, which a browser
                        never sends to a server, and the offer is single-use and expires.
                      </div>
                    </>
                  )}
                </div>
              </>
            )}

            <div className="card-body">
              <div className="row">
                <input
                  type="text"
                  style={{ flex: '1 1 160px' }}
                  placeholder="Sicily2026"
                  value={newRealm}
                  onChange={(e) => setNewRealm(e.target.value)}
                  aria-label="name for a shared budget"
                />
                <button
                  className="btn quiet"
                  disabled={busy || !newRealm.trim()}
                  onClick={() => void startRealm()}
                >
                  Start a shared budget
                </button>
              </div>
              <div className="muted">
                A budget has to be made inside the realm it is shared in: an account cannot move
                between realms afterwards, because that would move money out from under the key it
                was written under.
              </div>
            </div>
          </div>

          <div className="card">
            <div className="card-head">sync — the order everybody shares</div>
            <div className="card-body">
              {sync.data && sync.data.configured ? (
                <>
                  <div className="mono muted">
                    sequencer {sync.data.sequencer}
                    <br />
                    ledger {sync.data.ledger}
                    <br />
                    head entry {sync.data.seq} {sync.data.hash.slice(0, 12)}
                    <br />
                    {sync.data.pending} event{sync.data.pending === 1 ? '' : 's'} waiting to go out
                  </div>
                  <div className="muted">
                    {sync.data.lastRound
                      ? `last round ${sync.data.lastRound.at}: ` +
                        `${sync.data.lastRound.applied} in, ${sync.data.lastRound.pushed} out` +
                        (sync.data.lastRound.trouble ? ` — ${sync.data.lastRound.trouble}` : '')
                      : 'no round has run in this process yet'}
                  </div>
                  <div className="row">
                    <button className="btn quiet" disabled={busy} onClick={() => void syncNow()}>
                      {busy ? 'Syncing…' : 'Sync now'}
                    </button>
                  </div>
                  {syncSaid && (
                    <div className={syncSaid.trouble ? 'error' : 'muted'}>{syncSaid.text}</div>
                  )}
                </>
              ) : (
                <div className="muted">
                  This store syncs with nothing, so a realm is a set of accounts and nobody else
                  can be let into it. `resources sync init --sequencer URL` is what changes that.
                </div>
              )}
            </div>
          </div>
        </div>

        <div style={{ display: 'flex', flexDirection: 'column', gap: 18 }}>
          <div className="card">
            <div className="card-head">
              1 · lend costs into {openBudget ? budget?.shortName : 'a budget'}
            </div>
            <div className="card-body">
              {!openBudget && (
                <label className="field">
                  Call it
                  <input
                    type="text"
                    placeholder="Zinalrothorn2026"
                    value={newName}
                    onChange={(e) => setNewName(e.target.value)}
                  />
                </label>
              )}
              <input
                className="mono"
                type="text"
                placeholder='payee:"Cabane du Trient"'
                value={pickFilter}
                onChange={(e) => setPickFilter(e.target.value)}
                aria-label="find costs to share"
              />
              {candidates.error && <div className="error">{candidates.error}</div>}
              {candidates.data && (
                <div className="table-wrap" style={{ maxHeight: '38vh', overflowY: 'auto' }}>
                  <table>
                    <thead>
                      <tr>
                        <th />
                        <th>date</th>
                        <th>payee</th>
                        <th className="num">amount</th>
                      </tr>
                    </thead>
                    <tbody>
                      {candidates.data.items.map((t) => (
                        <tr
                          key={t.id}
                          className={`clickable${picked.has(t.id) ? ' selected' : ''}`}
                          onClick={() => {
                            const next = new Set(picked)
                            if (next.has(t.id)) next.delete(t.id)
                            else next.add(t.id)
                            setPicked(next)
                          }}
                        >
                          <td>
                            <input
                              type="checkbox"
                              readOnly
                              checked={picked.has(t.id)}
                              aria-label={`share ${t.payee ?? t.id}`}
                            />
                          </td>
                          <td className="mono">{t.date}</td>
                          <td>{t.payee ?? t.narration.slice(0, 30)}</td>
                          <td className="num neg">{t.headline?.amount.text ?? ''}</td>
                        </tr>
                      ))}
                    </tbody>
                  </table>
                  {candidates.data.items.length === 0 && (
                    <div className="empty">nothing matches</div>
                  )}
                </div>
              )}
              <div className="row">
                <button
                  className="btn"
                  disabled={busy || picked.size === 0 || (!openBudget && !newName.trim())}
                  onClick={() => void lend()}
                >
                  Lend {picked.size || ''} cost{picked.size === 1 ? '' : 's'}
                </button>
                {openBudget && (
                  <button className="btn quiet" onClick={() => setOpenBudget(null)}>
                    New budget instead
                  </button>
                )}
              </div>
              <div className="muted">
                Lending redirects each cost into the budget and rewrites the transaction in place —
                it adds no entry, and the bank leg is untouched, so your statement still reconciles.
              </div>
            </div>
          </div>

          {current && <Detail invoice={current} onChanged={() => invoices.reload()} />}
        </div>
      </div>
    </div>
  )
}
