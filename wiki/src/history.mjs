import { spawnSync } from "node:child_process";
import { esc, heading } from "./render.mjs";

export function collectHistory(
  cwd,
  ref = process.env.WIKI_HISTORY_REF || "HEAD",
  reference = process.env.WIKI_HISTORY_REFERENCE || "refs/remotes/origin/main",
) {
  const git = (args) => {
    const r = spawnSync("git", args, {
      cwd,
      encoding: "utf8",
      maxBuffer: 64 * 1024 * 1024,
    });
    if (r.error || r.status !== 0)
      throw Error(r.stderr || r.error?.message || "Git history unavailable");
    return r.stdout.trimEnd();
  };
  let tip;
  try {
    cwd = git(["rev-parse", "--show-toplevel"]);
    tip = git(["rev-parse", "--verify", "--end-of-options", `${ref}^{commit}`]);
  } catch {
    return {
      schema: "perclib-history-v1",
      available: false,
      reason: "No readable Git history for the selected revision.",
      snapshots: [],
    };
  }
  const shallow = git(["rev-parse", "--is-shallow-repository"]) === "true";
  const commits = git([
    "log",
    "--first-parent",
    "--reverse",
    "--format=%H%x09%cI",
    tip,
    "--",
    "PercLib",
    "Lrp",
    "wiki/articles",
    "wiki/sources",
    "wiki/tags.json",
  ])
    .split("\n")
    .filter(Boolean);
  if (!commits.some((c) => c.startsWith(tip + "\t")))
    commits.push(git(["show", "-s", "--format=%H%x09%cI", tip]));
  const cache = new Map();
  const snapshot = (commit, date, includeFiles = false) => {
    const tree = git([
      "ls-tree",
      "-r",
      "-z",
      commit,
      "--",
      "PercLib",
      "Lrp",
      "wiki/articles",
      "wiki/sources",
      "wiki/tags.json",
    ])
      .split("\0")
      .filter(Boolean)
      .map((row) => {
        const tab = row.indexOf("\t");
        const meta = row.slice(0, tab), file = row.slice(tab + 1);
        return { blob: meta.split(" ")[2], file };
      })
      .filter(
        (x) =>
          /^(?:PercLib|Lrp)\/[\s\S]*\.lean$/.test(x.file) ||
          /^wiki\/articles\/[^/]+\.md$/.test(x.file) ||
          /^wiki\/sources\/[^/]+\.md$/.test(x.file) ||
          x.file === "wiki/tags.json",
      );
    const row = {
      commit,
      date,
      leanFiles: 0,
      leanLines: 0,
      articles: 0,
      articleWords: 0,
      readingMaps: 0,
      readingMapWords: 0,
      assertions: 0,
      reservedTags: 0,
      withdrawnTags: 0,
    };
    const files = [];
    for (const { blob, file } of tree) {
      if (!cache.has(blob)) cache.set(blob, git(["cat-file", "blob", blob]));
      const text = cache.get(blob);
      const item = { path: file, blob, counts: {} };
      if (/^(?:PercLib|Lrp)\//.test(file)) {
        row.leanFiles++;
        item.kind = "library";
        item.counts.leanLines = text.split("\n").filter((l) => l.trim()).length;
        row.leanLines += item.counts.leanLines;
      } else if (file === "wiki/tags.json") {
        const registry = JSON.parse(text);
        item.kind = "tags";
        row.reservedTags = registry.tags.length;
        row.withdrawnTags = registry.tags.filter(
          (t) => t.state === "withdrawn",
        ).length;
        item.counts = { reservedTags: row.reservedTags, withdrawnTags: row.withdrawnTags };
      } else if (file.startsWith("wiki/sources/")) {
        row.readingMaps++;
        item.kind = "reading-map";
        item.counts.readingMapWords = text.trim().split(/\s+/).filter(Boolean).length;
        row.readingMapWords += item.counts.readingMapWords;
      } else {
        row.articles++;
        item.kind = "article";
        item.counts.articleWords = text.trim().split(/\s+/).filter(Boolean).length;
        item.counts.assertions = [...text.matchAll(/\bid="tag-[A-Z0-9]{4}"/g)].length;
        row.articleWords += item.counts.articleWords;
        row.assertions += item.counts.assertions;
      }
      if (includeFiles) files.push(item);
    }
    if (includeFiles) row.files = files;
    return row;
  };
  const snapshots = commits.map(c => snapshot(...c.split("\t")));
  let comparison = { available: false, reference };
  try {
    const referenceCommit = git(["rev-parse", "--verify", "--end-of-options", `${reference}^{commit}`]);
    const referenceDate = git(["show", "-s", "--format=%cI", referenceCommit]);
    let commonAncestor = null;
    try { commonAncestor = git(["merge-base", tip, referenceCommit]); } catch {
      // Disconnected or shallow history does not establish an ancestry relation.
    }
    const relationship = tip === referenceCommit ? "same"
      : commonAncestor === tip ? "contained"
      : commonAncestor === referenceCommit ? "ahead"
      : commonAncestor ? "diverged" : "unknown";
    const { files, ...counts } = snapshot(referenceCommit, referenceDate, true);
    comparison = { available: true, reference, referenceCommit, commonAncestor,
      relationship, snapshot: counts, files };
  } catch {
    // A missing optional reference must not suppress the selected history.
  }
  return {
    schema: "perclib-history-v1",
    available: true,
    tip,
    shallow,
    comparison,
    selection:
      "First-parent commits changing tracked source paths, plus the selected tip; committed contents only.",
    snapshots,
    files: snapshot(tip, snapshots.at(-1).date, true).files,
  };
}
const fields = {
  leanFiles: "Lean source files",
  leanLines: "Nonblank Lean source lines",
  articles: "Article files",
  articleWords: "Article source words",
  readingMaps: "Reading-map files",
  readingMapWords: "Reading-map source words",
  assertions: "Assertion anchors",
  reservedTags: "Permanently reserved tags",
  withdrawnTags: "Withdrawn tags",
};
const commitURL = (sha) => `https://github.com/tomhutchcroft/lrp/commit/${sha}`;
const compareURL = (before, after) =>
  `https://github.com/tomhutchcroft/lrp/compare/${before}...${after}`;
const signed = (n) => (n > 0 ? "+" + n : String(n));
export function summarizeDays(snapshots) {
  const days = new Map();
  snapshots.forEach((row, index) => {
    const day = new Date(row.date).toISOString().slice(0, 10);
    if (!days.has(day)) days.set(day, {
      day, snapshots: 0, baseline: false,
      changes: Object.fromEntries(Object.keys(fields).map(key => [key, 0])),
    });
    const summary = days.get(day);
    summary.snapshots++;
    if (!index) {
      summary.baseline = true;
      for (const key of Object.keys(fields))
        if (!Number.isFinite(row[key])) summary.changes[key] = null;
    }
    else for (const key of Object.keys(fields))
      summary.changes[key] = Number.isFinite(row[key]) && Number.isFinite(snapshots[index - 1][key])
        && summary.changes[key] !== null
        ? summary.changes[key] + row[key] - snapshots[index - 1][key] : null;
  });
  return [...days.values()].sort((a, b) => a.day.localeCompare(b.day));
}

function dailyTable(rows, keys) {
  return `<section class="article-section"><h2>Daily changes (UTC)</h2><p>Net changes between adjacent recorded snapshots, grouped by the later snapshot’s UTC commit date. The first observed snapshot supplies a baseline, not an inferred addition. <a href="/metrics/history-daily.csv" download="perclib-history-daily.csv">Download daily CSV</a> for both library and wiki counters. Zero on a baseline-only day means no observed transition; blank CSV cells mean unavailable counters. Dates with no recorded snapshots are omitted; the first and last dates may cover only part of a day.</p><div class="history-table"><table><caption>Daily net source-count changes</caption><thead><tr><th scope="col">UTC date</th><th scope="col">Recorded snapshots</th>${keys.map(key => `<th scope="col">Change in ${fields[key].toLowerCase()}</th>`).join("")}</tr></thead><tbody>${summarizeDays(rows).map(day => `<tr><th scope="row">${day.day}${day.baseline ? " (baseline observed)" : ""}</th><td>${day.snapshots}</td>${keys.map(key => `<td>${signed(day.changes[key])}</td>`).join("")}</tr>`).join("")}</tbody></table></div><p>Commit timestamps can be out of order: changes are computed in first-parent order before grouping by date. These are net changes in source counts, not gross additions/deletions, hours worked, or newly verified results. A rewrite can leave a count unchanged.</p></section>`;
}
function referenceComparison(history, keys) {
  const comparison = history.comparison;
  if (!comparison?.available)
    return `<section class="article-section"><h2>Recorded reference comparison</h2><p>No readable comparison revision was supplied with this build. The selected history alone does not establish which changes have merged.</p></section>`;
  const descriptions = {
    same: "The selected tip is the recorded reference revision.",
    contained: "The selected tip is contained in the recorded reference history.",
    ahead: "The selected tip includes changes beyond the recorded reference revision.",
    diverged: "The selected tip and recorded reference have diverged: each has changes absent from the other.",
    unknown: "Their ancestry relationship could not be established from the available history.",
  };
  const selected = history.snapshots.at(-1), baseline = comparison.snapshot;
  return `<section class="article-section"><h2>Recorded reference comparison</h2><p>${descriptions[comparison.relationship]} Reference <code>${esc(comparison.reference)}</code>: <a href="${commitURL(comparison.referenceCommit)}"><code>${comparison.referenceCommit}</code></a>, committed ${esc(baseline.date)}.</p><p>This is the reference available to the build, not a live check of GitHub. Its date is the commit date, not the time the branch was last fetched. Differences below compare complete source trees; they are not additions attributed to this branch, merge totals, or newly verified results.</p><div class="history-table"><table><caption>Selected tip versus recorded reference</caption><thead><tr><th scope="col">Source count</th><th scope="col">Reference</th><th scope="col">Selected tip</th><th scope="col">Difference</th></tr></thead><tbody>${keys.map(key => `<tr><th scope="row">${fields[key]}</th><td>${baseline[key]}</td><td>${selected[key]}</td><td>${signed(selected[key] - baseline[key])}</td></tr>`).join("")}</tbody></table></div></section>`;
}

export function compareHistoryFiles(history) {
  if (!history.available || !Array.isArray(history.files)) return null;
  const reference = history.comparison;
  const hasReference = Boolean(reference?.available && Array.isArray(reference.files));
  const selected = new Map(history.files.map(file => [file.path, file]));
  const baseline = new Map((hasReference ? reference.files : []).map(file => [file.path, file]));
  return [...new Set([...selected.keys(), ...baseline.keys()])].sort().map(path => {
    const after = selected.get(path), before = baseline.get(path);
    const keys = new Set([...Object.keys(after?.counts || {}), ...Object.keys(before?.counts || {})]);
    const counts = Object.fromEntries([...keys].map(key => {
      const a = !after ? 0 : Number.isFinite(after.counts?.[key]) ? after.counts[key] : null;
      const b = !hasReference ? null : !before ? 0 : Number.isFinite(before.counts?.[key]) ? before.counts[key] : null;
      return [key, {selected:a, reference:b, delta:a !== null && b !== null ? a - b : null}];
    }));
    return {path, kind:(after || before).kind, hasReference,
      state: !hasReference ? "Reference unavailable" : !before ? "Added" : !after ? "Removed"
        : before.blob === after.blob ? "Unchanged" : "Modified",
      selectedBlob:after?.blob || null, referenceBlob:before?.blob || null, counts};
  });
}

function fileBreakdown(history, kind) {
  const inventory = compareHistoryFiles(history);
  if (inventory === null) return "";
  const hasReference = Boolean(history.comparison?.available && Array.isArray(history.comparison.files));
  const keys = kind === "library" ? ["leanLines"]
    : ["articleWords", "readingMapWords", "assertions", "reservedTags", "withdrawnTags"];
  const rows = inventory.filter(row => (row.kind === "library") === (kind === "library"));
  const fileLink = (commit, path, label) => `<a href="https://github.com/tomhutchcroft/lrp/blob/${commit}/${path.split("/").map(encodeURIComponent).join("/")}">${esc(label)}</a>`;
  return `<section class="article-section"><h2>File-level source comparison</h2><p>${hasReference
    ? "Each cell shows reference → selected tip (net difference). Added and removed mean absent from one of these two recorded trees; renamed paths appear separately. Modified files can have unchanged counts."
    : "Counts describe the selected tip. No file-level reference inventory is available, so additions, removals and differences are not inferred."} These are source counts, not verified results, authorship or editing churn. <a href="/metrics/history-files.csv" download="perclib-history-files.csv">Download file comparison CSV</a> for both library and wiki files. The JSON also includes both inventories when available. A dash in the table or a blank CSV cell means an unavailable or inapplicable counter.</p>${rows.length ? `<div class="history-table"><table><caption>Counted files and their recorded revisions</caption><thead><tr><th scope="col">Source path</th><th scope="col">State versus reference</th><th scope="col">Revisions</th>${keys.map(key => `<th scope="col">${fields[key]}</th>`).join("")}</tr></thead><tbody>${rows.map(row => {
    const revisions = [row.referenceBlob && fileLink(history.comparison.referenceCommit, row.path, "Reference"), row.selectedBlob && fileLink(history.tip, row.path, "Selected")].filter(Boolean).join(" · ");
    return `<tr><th scope="row"><code>${esc(row.path)}</code></th><td>${row.state}</td><td>${revisions}</td>${keys.map(key => {
      const count = row.counts[key];
      if (!count) return "<td>—</td>";
      const a = count.selected ?? "—", b = count.reference ?? "—";
      return `<td>${hasReference ? `${b} → ${a} (${count.delta === null ? "—" : signed(count.delta)})` : a}</td>`;
    }).join("")}</tr>`;
  }).join("")}</tbody></table></div>` : "<p>No counted files of this kind occur in the available inventories.</p>"}</section>`;
}

export function historyPage(history, kind) {
  let keys =
    kind === "library"
      ? ["leanFiles", "leanLines"]
      : [
          "articles",
          "articleWords",
          "readingMaps",
          "readingMapWords",
          "assertions",
          "reservedTags",
          "withdrawnTags",
        ];
  const title =
    kind === "library" ? "Formalization library growth" : "Wiki growth";
  if (!history.available)
    return (
      heading(title) +
      "<p>Git history is unavailable in this build. No growth series has been inferred from the current files.</p>"
    );
  keys = keys.filter(key => history.snapshots.every(row => Number.isFinite(row[key])));
  const rows = history.snapshots,
    first = rows[0],
    last = rows.at(-1);
  const chart = (key) => {
    const max = Math.max(1, ...rows.map((r) => r[key]));
    const positions = rows.map((r, i) => ({
      x: 40 + (rows.length === 1 ? 0 : i / (rows.length - 1)) * 640,
      y: 180 - (r[key] / max) * 150,
    }));
    const points = positions.map(({ x, y }) => `${x},${y}`).join(" ");
    const markers = rows.map((r, i) => {
      const label = `${r.date}: ${fields[key]} ${r[key]}; revision ${r.commit}`;
      const { x, y } = positions[i];
      return `<a class="history-point" href="${commitURL(r.commit)}" tabindex="0" aria-label="${esc(label)}"><title>${esc(label)}</title><circle cx="${x}" cy="${y}" r="4"/></a>`;
    }).join("");
    return `<section class="article-section"><h2>${fields[key]}</h2><p>${last[key].toLocaleString("en-US")} at the selected tip; ${signed(last[key] - first[key])} across the available range.</p><svg class="history-chart" viewBox="0 0 720 220" role="group" aria-label="${fields[key]}: ${first[key]} to ${last[key]}; exact values in the table below"><title>${fields[key]} by recorded commit</title><path d="M40 25V180H690" fill="none" stroke="currentColor"/><polyline points="${points}" fill="none" stroke="#20745e" stroke-width="3"/>${markers}<text x="5" y="30">${max}</text><text x="15" y="185">0</text><text x="40" y="210">${esc(first.date.slice(0, 10))}</text><text x="590" y="210">${esc(last.date.slice(0, 10))}</text></svg></section>`;
  };
  return (
    heading(title, "Reproducible counts from committed source snapshots.") +
    `<p>Selected tip: <a href="https://github.com/tomhutchcroft/lrp/commit/${history.tip}"><code>${history.tip}</code></a>. ${rows.length} recorded snapshots. ${history.shallow ? "This checkout is shallow: earlier history is missing." : "This checkout is not shallow."}</p><p>These are source counts, not counts of verified theorems or reviewed exposition. The selected tip may belong to an unmerged branch. Uncommitted edits are excluded.</p><p>Charts place snapshots in first-parent commit order, at equal spacing; dates label the range. They do not depict an elapsed-time rate. Deletions and withdrawals remain visible, so series need not increase. Each chart point is labelled with its date and value; activate it to open the exact source revision. The table provides the same revision links and comparisons.</p>` +
    (kind === "wiki" && !keys.includes("readingMaps") ? "<p>Reading-map counts are unavailable in this saved history.</p>" : "") +
    referenceComparison(history, keys.filter(key => !history.comparison?.available || Number.isFinite(history.comparison.snapshot[key]))) +
    fileBreakdown(history, kind) +
    keys.map(chart).join("") +
    dailyTable(rows, keys) +
    `<section class="article-section"><h2>Snapshot details</h2><p><a href="/metrics/history.json">Download the full JSON series</a> or <a href="/metrics/history.csv" download="perclib-history.csv">CSV series</a>. Both contain all library and wiki counters. CSV also includes adjacent-snapshot deltas, with blank deltas for the first baseline; selectedTip and shallow identify its revision and history limits; referenceCommit and referenceRelationship record the comparison context when available. These are net source changes, not gross churn or proof counts. Parenthesized changes compare adjacent recorded snapshots; the first snapshot has no inferred earlier baseline. Comparison links show the complete repository difference between adjacent recorded snapshots, including changes outside the counted paths. They do not measure editing churn or proof completion.</p><div class="history-table"><table><caption>${title}: exact counts</caption><thead><tr><th scope="col">Commit time</th><th scope="col">Revision</th><th scope="col">Source changes</th>${keys.map((k) => `<th scope="col">${fields[k]}</th>`).join("")}</tr></thead><tbody>${rows.map((r, i) => `<tr><td>${esc(r.date)}</td><td><a href="https://github.com/tomhutchcroft/lrp/commit/${r.commit}">${r.commit.slice(0, 8)}</a></td><td>${i ? `<a href="${compareURL(rows[i - 1].commit, r.commit)}" aria-label="Compare ${rows[i - 1].commit.slice(0, 8)} to ${r.commit.slice(0, 8)}">Compare with previous snapshot</a>` : "Baseline — no earlier snapshot"}</td>${keys.map((k) => `<td>${r[k]}${i ? ` (${signed(r[k] - rows[i - 1][k])})` : ""}</td>`).join("")}</tr>`).join("")}</tbody></table></div></section><section class="article-section"><h2>How these counts are made</h2><p>${esc(history.selection)}</p><p>Lean files are tracked .lean files under PercLib/ and its earlier name Lrp/. Both historical paths are counted, so moving the same files between them does not create apparent growth. Nonblank lines include comments, definitions, statements and proofs; neither a theorem census nor kernel verification is inferred. Wiki articles are direct .md children of wiki/articles/. Reading maps are direct .md children of wiki/sources/ and are counted separately from articles. Article and reading-map source words are whitespace-separated tokens including metadata and markup. Reading-map counts measure inventory text, not completed source coverage. Assertion anchors are occurrences of the canonical tag anchor in article files. Tag reservations include withdrawn identities; withdrawals are reported separately. Earlier prototype pages are not silently counted as canonical articles.</p><p>Historical proof status and correspondence-review counts require the compiled manifest and review records for each historical revision. Git source counts cannot supply that series. The current evidence snapshot, when supplied, is reported separately on <a href="/metrics/">Project metrics</a>.</p></section>`
  );
}
