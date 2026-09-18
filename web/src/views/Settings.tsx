import { useState } from 'react'
import { api, getToken, setToken } from '../api'
import { useAsync } from '../hooks'

/**
 * While no token exists the API is open, which is what makes the tool usable
 * the moment it starts. Minting the first token locks it down.
 */
export default function Settings({ onChanged }: { onChanged: () => void }) {
  const [token, setTokenState] = useState(getToken())
  const [name, setName] = useState('')
  const [scopes, setScopes] = useState('read,write,import')
  const [secret, setSecret] = useState<string | null>(null)
  const [error, setError] = useState<string | null>(null)
  const attachments = useAsync(() => api.attachments(), [])
  const tokens = useAsync(() => api.tokens(), [])
  const sync = useAsync(() => api.syncStatus(), [])

  const save = () => {
    setToken(token)
    onChanged()
  }

  const mint = async () => {
    setError(null)
    try {
      const created = await api.createToken(name, scopes)
      setSecret(created.secret)
      tokens.reload()
    } catch (e) {
      setError(e instanceof Error ? e.message : String(e))
    }
  }

  const revoke = async (id: string) => {
    setError(null)
    try {
      await api.revokeToken(id)
      tokens.reload()
    } catch (e) {
      setError(e instanceof Error ? e.message : String(e))
    }
  }

  return (
    <div className="split">
      <div className="card">
        <div className="card-head">this browser's token</div>
        <div className="card-body">
          <label className="field">
            Bearer token
            <input
              className="mono"
              type="password"
              value={token}
              onChange={(e) => setTokenState(e.target.value)}
              placeholder="rsrc_…"
            />
          </label>
          <div className="muted">
            Stored in this browser only. Leave empty while the server still has no tokens.
          </div>
          <div>
            <button className="btn" onClick={save}>
              Save
            </button>
          </div>
        </div>
      </div>

      <div className="card">
        <div className="card-head">this node's identity and sync</div>
        <div className="card-body">
          {sync.error && <div className="error">{sync.error}</div>}
          <div className="muted">
            The member id is the hex of this node's signing key, and the agreement key is what
            other people wrap a realm key to. Both are public; the secret halves never leave
            identity.json, which is encrypted under a passphrase this page has never seen.
          </div>
          <div className="mono" style={{ wordBreak: 'break-all' }}>
            member {sync.data?.member || 'no identity yet — run `resources identity init`'}
            <br />
            agreement {sync.data?.boxPk || '—'}
          </div>
          {sync.data?.configured ? (
            <>
              <div className="mono muted" style={{ wordBreak: 'break-all' }}>
                sequencer {sync.data.sequencer}
                <br />
                ledger {sync.data.ledger}
                <br />
                head entry {sync.data.seq} {sync.data.hash.slice(0, 12)}
                <br />
                {sync.data.pending} of {sync.data.events} local events waiting to go out
              </div>
              <div className="muted">
                Read-only here on purpose: where a store syncs is `sync.json` beside the database,
                and changing it is `resources sync init`. Syncing itself is on the Sharing tab.
              </div>
            </>
          ) : (
            <div className="muted">
              This store syncs with nothing: every event stays in the local log and no realm can
              be shared. `resources sync init --sequencer URL` is what changes that.
            </div>
          )}
        </div>
      </div>

      <div style={{ display: 'flex', flexDirection: 'column', gap: 18 }}>
        <div className="card">
          <div className="card-head">mint a token</div>
          <div className="card-body">
            {error && <div className="error">{error}</div>}
            <label className="field">
              Name
              <input type="text" value={name} onChange={(e) => setName(e.target.value)} />
            </label>
            <label className="field">
              Scopes
              <input type="text" value={scopes} onChange={(e) => setScopes(e.target.value)} />
            </label>
            <div>
              <button className="btn" disabled={!name} onClick={() => void mint()}>
                Create
              </button>
            </div>
            {secret && (
              <>
                <div className="mono" style={{ wordBreak: 'break-all' }}>
                  {secret}
                </div>
                <div className="muted">
                  This is the only time the secret is shown. Copy it into the box on the left, or
                  into your shell's RESOURCES_TOKEN.
                </div>
              </>
            )}
          </div>
        </div>

        <div className="card">
          <div className="card-head">tokens</div>
          <div className="table-wrap">
            <table>
              <thead>
                <tr>
                  <th>name</th>
                  <th>what it can do</th>
                  <th>last used</th>
                  <th />
                </tr>
              </thead>
              <tbody>
                {(tokens.data ?? []).map((t) => (
                  <tr key={t.id}>
                    <td>{t.name}</td>
                    <td>
                      <span className="mono muted">{t.scopes}</span>
                    </td>
                    <td className="mono muted">{t.lastUsedAt ?? 'never'}</td>
                    <td>
                      <button
                        className="btn quiet"
                        style={{ padding: '2px 9px' }}
                        onClick={() => void revoke(t.id)}
                        aria-label={`revoke ${t.name}`}
                      >
                        Revoke
                      </button>
                    </td>
                  </tr>
                ))}
              </tbody>
            </table>
            {(tokens.data ?? []).length === 0 && !tokens.loading && (
              <div className="empty">
                No tokens yet, so the API is open. Minting the first one locks it down.
              </div>
            )}
          </div>
          <div className="card-body">
            <div className="muted">
              A token is a credential of your own. Letting somebody else in is an invite to a
              realm, on the Sharing tab: it hands them a key rather than a narrower version of
              yours, and what they can read is what that key opens.
            </div>
          </div>
        </div>

        <div className="card">
          <div className="card-head">stored receipts</div>
          <div className="table-wrap">
            <table>
              <tbody>
                {(attachments.data ?? []).map((a) => (
                  <tr key={a.sha256}>
                    <td className="mono">
                      <a href={api.attachmentUrl(a.sha256)} target="_blank" rel="noreferrer">
                        {a.sha256.slice(0, 12)}…
                      </a>
                    </td>
                    <td>{a.origName ?? ''}</td>
                    <td className="num">{a.bytes}</td>
                  </tr>
                ))}
              </tbody>
            </table>
            {(attachments.data ?? []).length === 0 && <div className="empty">none yet</div>}
          </div>
        </div>
      </div>
    </div>
  )
}
