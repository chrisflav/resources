import { useState } from 'react'
import { api } from '../api'
import { useAsync, useDebounced } from '../hooks'

/**
 * The people in your address book.
 *
 * Read only, on purpose. A second copy of an address book is a copy that goes
 * stale, and the moment it can be edited here there are two answers to "what is
 * Anna's email". Point the source at where they already live and they stay
 * there.
 */
export default function Contacts() {
  const [search, setSearch] = useState('')
  const needle = useDebounced(search)
  const book = useAsync(() => api.contacts(), [])
  const books = useAsync(() => api.contactBooks(), [])
  const [kind, setKind] = useState('eds')
  const [path, setPath] = useState('')
  const [url, setUrl] = useState('')
  const [user, setUser] = useState('')
  const [pwCommand, setPwCommand] = useState('')
  const [busy, setBusy] = useState(false)
  const [error, setError] = useState<string | null>(null)

  const apply = async () => {
    setBusy(true)
    setError(null)
    try {
      await api.setContactSource({
        kind,
        ...(kind === 'files' ? { path } : {}),
        ...(kind === 'carddav'
          ? { url, user, passwordCommand: pwCommand.split(' ').filter(Boolean) }
          : {}),
      })
      book.reload()
      books.reload()
    } catch (e) {
      setError(e instanceof Error ? e.message : String(e))
    } finally {
      setBusy(false)
    }
  }

  const people = book.data?.items ?? []
  const shown = needle
    ? people.filter(
        (c) =>
          c.name.toLowerCase().includes(needle.toLowerCase()) ||
          (c.email ?? '').toLowerCase().includes(needle.toLowerCase()),
      )
    : people

  return (
    <div className="split">
      <div className="card">
        <div className="card-head">
          <div className="spread">
            <span>
              {people.length} contact(s) — offered wherever a person has to be chosen
            </span>
            <input
              type="text"
              placeholder="search"
              value={search}
              onChange={(e) => setSearch(e.target.value)}
              aria-label="search contacts"
            />
          </div>
        </div>
        <div className="table-wrap">
          <table>
            <thead>
              <tr>
                <th>name</th>
                <th>email</th>
                <th>iban</th>
              </tr>
            </thead>
            <tbody>
              {shown.map((c) => (
                <tr key={c.name}>
                  <td>{c.name}</td>
                  <td className="muted">{c.email ?? ''}</td>
                  <td className="mono muted">{c.iban ?? ''}</td>
                </tr>
              ))}
            </tbody>
          </table>
          {shown.length === 0 && !book.loading && (
            <div className="empty">
              {book.data?.configured
                ? 'Nothing matches.'
                : 'No address book was found — see the panel on the right.'}
            </div>
          )}
        </div>
      </div>

      <div className="card">
        <div className="card-head">where these come from</div>
        <div className="card-body">
          <div className="mono">{book.data?.source ?? '…'}</div>
          {book.error && <div className="error">{book.error}</div>}
          {error && <div className="error">{error}</div>}
          <p className="muted">
            Read from your address book and never copied here, so there is only ever one answer to
            who somebody is. Editing them is your address book's job.
          </p>

          {(books.data ?? []).length > 0 && (
            <>
              <div className="card-head" style={{ padding: '0 0 4px', border: 'none' }}>
                address books on this computer
              </div>
              {(books.data ?? []).map((b) => (
                <div className="tree-row" key={b.name}>
                  <span>{b.name}</span>
                  <span className="mono muted">{b.contacts}</span>
                </div>
              ))}
              <p className="muted">
                These come from the desktop contact store, which already keeps whatever CardDAV
                account it is signed in to up to date — so there is nothing to configure and no
                second copy of your password.
              </p>
            </>
          )}

          <div className="card-head" style={{ padding: '8px 0 4px', border: 'none' }}>
            read from somewhere else
          </div>
          <div className="row">
            <select value={kind} onChange={(e) => setKind(e.target.value)} aria-label="source kind">
              <option value="eds">desktop contact store</option>
              <option value="files">a directory of vCards</option>
              <option value="carddav">a CardDAV collection</option>
            </select>
          </div>
          {kind === 'files' && (
            <label className="field">
              Directory
              <input
                type="text"
                placeholder="/home/you/.contacts/default"
                value={path}
                onChange={(e) => setPath(e.target.value)}
              />
            </label>
          )}
          {kind === 'carddav' && (
            <>
              <label className="field">
                Collection URL
                <input
                  className="mono"
                  type="text"
                  placeholder="https://cloud.example.de/remote.php/dav/addressbooks/users/you/contacts/"
                  value={url}
                  onChange={(e) => setUrl(e.target.value)}
                />
              </label>
              <div className="row">
                <label className="field" style={{ flex: '1 1 120px' }}>
                  User
                  <input type="text" value={user} onChange={(e) => setUser(e.target.value)} />
                </label>
                <label className="field" style={{ flex: '1 1 200px' }}>
                  Command that prints the password
                  <input
                    className="mono"
                    type="text"
                    placeholder="pass show dav"
                    value={pwCommand}
                    onChange={(e) => setPwCommand(e.target.value)}
                  />
                </label>
              </div>
              <div className="muted">
                A command, not the password itself — nothing secret is written to disk here.
              </div>
            </>
          )}
          <div className="row">
            <button className="btn" disabled={busy} onClick={() => void apply()}>
              Use this
            </button>
            <button className="btn quiet" onClick={() => book.reload()}>
              Re-read
            </button>
          </div>
        </div>
      </div>
    </div>
  )
}
