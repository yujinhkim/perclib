import { summarizeDays, compareHistoryFiles } from "./history.mjs";
// Source counters only: compiled proof status is not inferred from Git history.
export const historyCountFields = [
  'leanFiles', 'leanLines', 'articles', 'articleWords',
  'assertions', 'reservedTags', 'withdrawnTags', 'readingMaps', 'readingMapWords',
];
const cell = value => {
  const text = String(value);
  return /[",\r\n]/.test(text) ? '"' + text.replaceAll('"', '""') + '"' : text;
};
export function historyCsv(history) {
  if (!history.available) return null;
  const header = ['selectedTip', 'shallow', 'referenceCommit', 'referenceRelationship', 'snapshotIndex', 'commit', 'date',
    ...historyCountFields, ...historyCountFields.map(key => key + 'Delta')];
  const rows = history.snapshots.map((row, index, snapshots) => [
    history.tip, history.shallow, history.comparison?.referenceCommit || '',
    history.comparison?.relationship || '', index, row.commit, row.date,
    ...historyCountFields.map(key => row[key] ?? ''),
    ...historyCountFields.map(key => index && Number.isFinite(row[key]) && Number.isFinite(snapshots[index - 1][key]) ? row[key] - snapshots[index - 1][key] : ''),
  ]);
  return [header, ...rows].map(row => row.map(cell).join(',')).join('\r\n') + '\r\n';
}

// Daily deltas use first-parent adjacency, then the later commit's UTC day.
export function dailyHistoryCsv(history) {
  if (!history.available) return null;
  const header = ['selectedTip', 'shallow', 'utcDate', 'recordedSnapshots', 'baselineObserved',
    ...historyCountFields.map(key => key + 'Delta')];
  const rows = summarizeDays(history.snapshots).map(day => [
    history.tip, history.shallow, day.day, day.snapshots, day.baseline,
    ...historyCountFields.map(key => day.changes[key] ?? ''),
  ]);
  return [header, ...rows].map(row => row.map(cell).join(',')).join('\r\n') + '\r\n';
}

export function fileHistoryCsv(history) {
  const inventory = compareHistoryFiles(history);
  if (inventory === null) return null;
  const keys = ['leanLines', 'articleWords', 'readingMapWords', 'assertions', 'reservedTags', 'withdrawnTags'];
  const header = ['selectedTip', 'shallow', 'referenceCommit', 'referenceRelationship',
    'referenceInventoryAvailable', 'path', 'kind', 'state', 'referenceBlob', 'selectedBlob',
    ...keys.flatMap(key => [key + 'Reference', key + 'Selected', key + 'Delta'])];
  const rows = inventory.map(row => [history.tip, history.shallow,
    history.comparison?.available ? history.comparison.referenceCommit : '',
    history.comparison?.available ? history.comparison.relationship : '',
    row.hasReference, row.path, row.kind, row.state, row.referenceBlob ?? '', row.selectedBlob ?? '',
    ...keys.flatMap(key => ['reference', 'selected', 'delta'].map(side => row.counts[key]?.[side] ?? '')),
  ]);
  return [header, ...rows].map(row => row.map(cell).join(',')).join('\r\n') + '\r\n';
}
