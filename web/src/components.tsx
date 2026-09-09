/** Shared table furniture, so the Inbox and the Ledger sort the same way. */

export type Dir = 'asc' | 'desc'

export type Sort<K extends string> = { key: K; dir: Dir }

/**
 * A column header that sorts.
 *
 * The `<th>` carries `aria-sort` and the label is a real button, so the column
 * is reachable by keyboard and a screen reader announces the direction.
 */
export function SortTh<K extends string>({
  label,
  column,
  sort,
  onSort,
  numeric,
}: {
  label: string
  column: K
  sort: Sort<K>
  onSort: (key: K) => void
  numeric?: boolean
}) {
  const active = sort.key === column
  return (
    <th
      className={numeric ? 'num sortable' : 'sortable'}
      aria-sort={active ? (sort.dir === 'asc' ? 'ascending' : 'descending') : 'none'}
    >
      <button type="button" onClick={() => onSort(column)}>
        {label}
        <span className="caret" aria-hidden>
          {active ? (sort.dir === 'asc' ? '▲' : '▼') : '↕'}
        </span>
      </button>
    </th>
  )
}

/** Toggles direction when the same column is clicked again, else starts ascending. */
export function nextSort<K extends string>(current: Sort<K>, key: K): Sort<K> {
  return current.key === key
    ? { key, dir: current.dir === 'asc' ? 'desc' : 'asc' }
    : { key, dir: 'asc' }
}
