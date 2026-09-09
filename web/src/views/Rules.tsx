import { useState } from 'react'
import { api } from '../api'
import { useAsync } from '../hooks'

/**
 * Rules run when a staged row is promoted. They match with exactly the filter
 * language the ledger search box uses, so anything you can find you can also
 * categorise.
 */
export default function Rules() {
  const rules = useAsync(() => api.rules(), [])
  const [name, setName] = useState('')
  const [filter, setFilter] = useState('')
  const [account, setAccount] = useState('')
  const [labels, setLabels] = useState('')
  const [priority, setPriority] = useState('0')
  const [busy, setBusy] = useState(false)
  const [error, setError] = useState<string | null>(null)

  const add = async () => {
    setBusy(true)
    setError(null)
    try {
      await api.createRule({
        name,
        filter,
        setAccount: account || undefined,
        addLabels: labels ? labels.split(',').map((s) => s.trim()).filter(Boolean) : [],
        priority: Number(priority) || 0,
      })
      setName('')
      setFilter('')
      setAccount('')
      setLabels('')
      rules.reload()
    } catch (e) {
      setError(e instanceof Error ? e.message : String(e))
    } finally {
      setBusy(false)
    }
  }

  const remove = async (id: string) => {
    await api.deleteRule(id)
    rules.reload()
  }

  return (
    <div className="split">
      <div className="card">
        <div className="card-head">rules, highest priority first</div>
        <div className="table-wrap">
          <table>
            <thead>
              <tr>
                <th className="num">pri</th>
                <th>name</th>
                <th>matches</th>
                <th>books into</th>
                <th>labels</th>
                <th />
              </tr>
            </thead>
            <tbody>
              {(rules.data ?? []).map((r) => (
                <tr key={r.id}>
                  <td className="num">{r.priority}</td>
                  <td>{r.name}</td>
                  <td className="mono wrap">{r.filter}</td>
                  <td className="muted">{r.setAccount ?? ''}</td>
                  <td>
                    {r.addLabels.map((l) => (
                      <span key={l} className="pill" style={{ marginRight: 4 }}>
                        {l}
                      </span>
                    ))}
                  </td>
                  <td>
                    <button className="btn quiet" onClick={() => void remove(r.id)}>
                      Delete
                    </button>
                  </td>
                </tr>
              ))}
            </tbody>
          </table>
          {(rules.data ?? []).length === 0 && <div className="empty">No rules yet.</div>}
        </div>
      </div>

      <div className="card">
        <div className="card-head">new rule</div>
        <div className="card-body">
          {error && <div className="error">{error}</div>}
          <label className="field">
            Name
            <input type="text" value={name} onChange={(e) => setName(e.target.value)} />
          </label>
          <label className="field">
            Filter
            <input
              className="mono"
              type="text"
              placeholder='payee:REWE'
              value={filter}
              onChange={(e) => setFilter(e.target.value)}
            />
          </label>
          <label className="field">
            Book counter posting into
            <input
              type="text"
              placeholder="Expenses.Food.Groceries"
              value={account}
              onChange={(e) => setAccount(e.target.value)}
            />
          </label>
          <label className="field">
            Labels, comma separated
            <input type="text" value={labels} onChange={(e) => setLabels(e.target.value)} />
          </label>
          <label className="field">
            Priority
            <input type="number" value={priority} onChange={(e) => setPriority(e.target.value)} />
          </label>
          <div>
            <button className="btn" disabled={busy || !name || !filter} onClick={() => void add()}>
              Create rule
            </button>
          </div>
        </div>
      </div>
    </div>
  )
}
