import { useCallback, useEffect, useState } from 'react'

/**
 * The whole data layer. A load function plus a `reload` trigger covers every
 * screen here; anything more would be machinery for its own sake.
 */
export function useAsync<T>(load: () => Promise<T>, deps: unknown[]): {
  data: T | null
  error: string | null
  loading: boolean
  reload: () => void
} {
  const [data, setData] = useState<T | null>(null)
  const [error, setError] = useState<string | null>(null)
  const [loading, setLoading] = useState(true)
  const [nonce, setNonce] = useState(0)

  useEffect(() => {
    let live = true
    setLoading(true)
    load()
      .then((value) => {
        if (!live) return
        setData(value)
        setError(null)
      })
      .catch((e: unknown) => {
        if (!live) return
        setError(e instanceof Error ? e.message : String(e))
      })
      .finally(() => {
        if (live) setLoading(false)
      })
    return () => {
      live = false
    }
    // eslint-disable-next-line react-hooks/exhaustive-deps
  }, [...deps, nonce])

  const reload = useCallback(() => setNonce((n) => n + 1), [])
  return { data, error, loading, reload }
}

/** Debounces a rapidly changing value, for the filter box. */
export function useDebounced<T>(value: T, ms = 250): T {
  const [held, setHeld] = useState(value)
  useEffect(() => {
    const t = setTimeout(() => setHeld(value), ms)
    return () => clearTimeout(t)
  }, [value, ms])
  return held
}
