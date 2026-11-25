import test from "node:test";
import assert from "node:assert/strict";
import fs from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { execFileSync } from "node:child_process";
import { collectHistory, historyPage, summarizeDays } from "../src/history.mjs";

test("daily summaries use UTC dates and parent-order deltas without inventing a baseline", () => {
  const row = (date, leanLines, articles) => ({date, leanLines, articles,
    leanFiles: 1, articleWords: 100, assertions: 2, reservedTags: 3, withdrawnTags: 1});
  const rows = [
    row("2026-11-14T23:30:00-02:00", 10, 2),
    row("2026-11-16T00:30:00+02:00", 14, 3),
    row("2026-11-14T23:00:00Z", 11, 2),
  ];
  const days = summarizeDays(rows);
  assert.deepEqual(days.map(d => [d.day, d.snapshots, d.baseline]), [
    ["2026-11-14", 1, false], ["2026-11-15", 2, true],
  ]);
  assert.deepEqual(days.map(d => d.changes.leanLines), [-3, 4]);
  assert.deepEqual(days.map(d => d.changes.articles), [-1, 1]);
  assert.equal(days.reduce((total, d) => total + d.changes.leanLines, 0), 1);
  assert.ok(days.every(d => d.changes.reservedTags === 0));
  assert.deepEqual(summarizeDays([]), []);
  assert.equal(summarizeDays(rows.slice(0, 1))[0].changes.leanLines, 0);
  const history = {available: true, tip: "abc", snapshots: rows.map((r, i) =>
    ({...r, commit: String(i)})), selection: "Fixture"};
  for (const kind of ["wiki", "library"]) {
    const page = historyPage(history, kind);
    assert.match(page, /Daily changes \(UTC\)/);
    assert.match(page, /baseline observed/);
    assert.match(page, /not gross additions\/deletions/);
  }
});
test("real history records additions, deletions and withdrawals, and excludes dirty files", async () => {
  const root = await fs.mkdtemp(path.join(os.tmpdir(), "wiki-history-"));
  const git = (...args) =>
    execFileSync("git", args, {
      cwd: root,
      encoding: "utf8",
      stdio: ["ignore", "pipe", "pipe"],
    }).trim();
  try {
    git("init");
    git("config", "user.name", "Fixture");
    git("config", "user.email", "fixture@example.invalid");
    await fs.mkdir(path.join(root, "Lrp"));
    await fs.mkdir(path.join(root, "wiki/articles"), { recursive: true });
    await fs.writeFile(
      path.join(root, "Lrp/Basic.lean"),
      "-- comment\ndef x := 1\n\n",
    );
    await fs.writeFile(
      path.join(root, "wiki/articles/a.md"),
      '<a id="tag-AAAA"></a>\nA statement\n',
    );
    await fs.writeFile(
      path.join(root, "wiki/tags.json"),
      JSON.stringify({ tags: [{ tag: "AAAA", state: "allocated" }] }),
    );
    git("add", ".");
    git("commit", "-m", "First");
    const first = git("rev-parse", "HEAD");
    git("mv", "Lrp", "PercLib");
    git("commit", "-m", "Rename namespace");
    const renamed = collectHistory(root);
    assert.equal(renamed.snapshots.length, 2);
    assert.deepEqual(renamed.snapshots.map(r => r.leanFiles), [1, 1]);
    assert.deepEqual(renamed.snapshots.map(r => r.leanLines), [2, 2]);
    await fs.writeFile(
      path.join(root, "PercLib/Extra.lean"),
      "theorem extra : True := trivial\n",
    );
    await fs.writeFile(
      path.join(root, "wiki/articles/b.md"),
      '<a id="tag-BBBB"></a>\nAnother statement\n',
    );
    await fs.writeFile(
      path.join(root, "wiki/tags.json"),
      JSON.stringify({
        tags: [
          { tag: "AAAA", state: "allocated" },
          { tag: "BBBB", state: "allocated" },
        ],
      }),
    );
    git("add", ".");
    git("commit", "-m", "Add");
    await fs.rm(path.join(root, "PercLib/Extra.lean"));
    await fs.rm(path.join(root, "wiki/articles/b.md"));
    await fs.writeFile(
      path.join(root, "wiki/tags.json"),
      JSON.stringify({
        tags: [
          { tag: "AAAA", state: "allocated" },
          { tag: "BBBB", state: "withdrawn" },
        ],
      }),
    );
    git("add", ".");
    git("commit", "-m", "Withdraw");
    await fs.writeFile(path.join(root, "PercLib/Dirty.lean"), "def dirty := 0");
    const h = collectHistory(root);
    assert.deepEqual(collectHistory(path.join(root, "wiki")), h);
    assert.equal(h.shallow, false);
    assert.equal(h.snapshots.length, 4);
    assert.deepEqual(
      h.snapshots.map((r) => r.leanFiles),
      [1, 1, 2, 1],
    );
    assert.deepEqual(
      h.snapshots.map((r) => r.leanLines),
      [2, 2, 3, 2],
    );
    assert.deepEqual(
      h.snapshots.map((r) => r.assertions),
      [1, 1, 2, 1],
    );
    assert.deepEqual(
      h.snapshots.map((r) => r.reservedTags),
      [1, 1, 2, 2],
    );
    assert.deepEqual(
      h.snapshots.map((r) => r.withdrawnTags),
      [0, 0, 0, 1],
    );
    assert.equal(collectHistory(root, first).snapshots.length, 1);
    const page = historyPage(h, "wiki");
    assert.match(page, /\(-1\)/);
    assert.match(page, /not counts of verified theorems/);
    assert.match(page, /earlier baseline/);
    const shallow = path.join(root, "shallow");
    git("clone", "--depth=1", "file://" + root, shallow);
    assert.equal(collectHistory(shallow).shallow, true);
    assert.equal(collectHistory(shallow).snapshots.length, 1);
  } finally {
    await fs.rm(root, { recursive: true, force: true });
  }
});
test("missing Git history produces an explicit unavailable state", async () => {
  const root = await fs.mkdtemp(path.join(os.tmpdir(), "wiki-no-history-"));
  try {
    const h = collectHistory(root);
    assert.deepEqual(collectHistory(path.join(root, "wiki")), h);
    assert.equal(h.available, false);
    assert.match(
      historyPage(h, "library"),
      /No growth series has been inferred/,
    );
  } finally {
    await fs.rm(root, { recursive: true, force: true });
  }
});

test("growth inspection links preserve snapshot order and single-snapshot baselines", () => {
  const row = (commit, date, leanLines) => ({
    commit, date, leanLines, leanFiles: 1,
    articles: 0, articleWords: 0, assertions: 0, reservedTags: 0, withdrawnTags: 0,
  });
  const a = "a".repeat(40), b = "b".repeat(40);
  const history = {
    available: true, tip: b, shallow: true, selection: "Fixture",
    // Commit timestamps need not increase along the first-parent chain.
    snapshots: [row(a, "2026-11-15T12:00:00Z", 8), row(b, "2026-11-14T12:00:00Z", 3)],
  };
  const page = historyPage(history, "library");
  assert.match(page, new RegExp(`/compare/${a}\\.\\.\\.${b}`));
  assert.doesNotMatch(page, new RegExp(`/compare/${b}\\.\\.\\.${a}`));
  assert.equal((page.match(/class="history-point"/g) || []).length, 4);
  assert.match(page, /2026-11-14T12:00:00Z: Nonblank Lean source lines 3; revision b{40}/);
  assert.match(page, /3 \(-5\)/);
  assert.match(page, /checkout is shallow/);
  assert.match(page, /including changes outside the counted paths/);
  const single = historyPage({ ...history, tip: a, snapshots: [history.snapshots[0]] }, "wiki");
  assert.doesNotMatch(single, /\/compare\/|NaN|Infinity/);
  assert.equal((single.match(/class="history-point"/g) || []).length, 5);
  assert.match(single, /Baseline — no earlier snapshot/);
  assert.match(single, /cx="40" cy="180"/);
});

test("reference comparison distinguishes contained, ahead, divergent and disconnected histories", async () => {
  const root = await fs.mkdtemp(path.join(os.tmpdir(), "wiki-reference-"));
  const git = (...args) => execFileSync("git", args, {
    cwd: root, encoding: "utf8", stdio: ["ignore", "pipe", "pipe"],
  }).trim();
  try {
    git("init");
    git("config", "user.name", "Fixture");
    git("config", "user.email", "fixture@example.invalid");
    await fs.mkdir(path.join(root, "PercLib"));
    await fs.writeFile(path.join(root, "PercLib/Basic.lean"), "-- baseline\n");
    git("add", "."); git("commit", "-m", "Baseline");
    const base = git("rev-parse", "HEAD");
    git("update-ref", "refs/remotes/origin/main", base);
    assert.equal(collectHistory(root).comparison.relationship, "same");
    await fs.writeFile(path.join(root, "PercLib/Feature.lean"), "-- feature\n");
    git("add", "."); git("commit", "-m", "Feature");
    const feature = git("rev-parse", "HEAD");
    const ahead = collectHistory(root);
    assert.equal(ahead.comparison.referenceCommit, base);
    assert.equal(ahead.comparison.commonAncestor, base);
    assert.equal(ahead.comparison.relationship, "ahead");
    assert.equal(ahead.comparison.snapshot.leanFiles, 1);
    assert.match(historyPage(ahead, "library"), /includes changes beyond/);
    assert.match(historyPage(ahead, "library"), /<td>1<\/td><td>2<\/td><td>\+1<\/td>/);
    assert.equal(collectHistory(root, base, feature).comparison.relationship, "contained");
    git("checkout", "--detach", base);
    await fs.writeFile(path.join(root, "PercLib/Other.lean"), "-- other\n-- second\n-- third\n");
    git("add", "."); git("commit", "-m", "Reference changes independently");
    const reference = git("rev-parse", "HEAD");
    git("update-ref", "refs/remotes/origin/main", reference);
    const divergent = collectHistory(root, feature);
    assert.equal(divergent.comparison.relationship, "diverged");
    assert.equal(divergent.comparison.commonAncestor, base);
    assert.equal(divergent.comparison.snapshot.leanLines, 4);
    assert.equal(divergent.snapshots.at(-1).leanLines, 2);
    assert.match(historyPage(divergent, "library"), /<td>4<\/td><td>2<\/td><td>-2<\/td>/);
    assert.match(historyPage(divergent, "wiki"), /each has changes absent from the other/);
    const absent = collectHistory(root, feature, "refs/remotes/missing/main");
    assert.equal(absent.available, true);
    assert.equal(absent.comparison.available, false);
    assert.match(historyPage(absent, "wiki"), /does not establish which changes have merged/);
    git("checkout", "--orphan", "unrelated"); git("rm", "-rf", ".");
    await fs.writeFile(path.join(root, "README"), "Unrelated tree");
    git("add", "."); git("commit", "-m", "Unrelated root");
    const unknown = collectHistory(root);
    assert.equal(unknown.comparison.relationship, "unknown");
    assert.equal(unknown.comparison.commonAncestor, null);
    assert.equal(unknown.comparison.snapshot.leanLines, 4);
    assert.match(historyPage(unknown, "library"), /could not be established/);
  } finally { await fs.rm(root, { recursive: true, force: true }); }
});

test("file inventories reconcile aggregate counts and distinguish removals, zero-count additions and same-count edits", async () => {
  const root = await fs.mkdtemp(path.join(os.tmpdir(), "wiki-file-history-"));
  const git = (...args) => execFileSync("git", args, {
    cwd: root, encoding: "utf8", stdio: ["ignore", "pipe", "pipe"],
  }).trim();
  try {
    git("init"); git("config", "user.name", "Fixture");
    git("config", "user.email", "fixture@example.invalid");
    await fs.mkdir(path.join(root, "PercLib"));
    await fs.mkdir(path.join(root, "wiki/articles"), {recursive: true});
    await fs.writeFile(path.join(root, "PercLib/Keep.lean"), "-- before\n");
    await fs.writeFile(path.join(root, "PercLib/Remove.lean"), "-- removed\n");
    await fs.writeFile(path.join(root, "wiki/articles/a.md"), '<a id="tag-AAAA"></a> A statement\n');
    await fs.writeFile(path.join(root, "wiki/tags.json"), JSON.stringify({tags: [{tag: "AAAA", state: "allocated"}]}));
    git("add", "."); git("commit", "-m", "Reference");
    const reference = git("rev-parse", "HEAD");
    git("update-ref", "refs/remotes/origin/main", reference);
    await fs.writeFile(path.join(root, "PercLib/Keep.lean"), "-- after\n");
    await fs.rm(path.join(root, "PercLib/Remove.lean"));
    await fs.writeFile(path.join(root, "PercLib/New # &.lean"), "-- new\n-- second line\n");
    await fs.writeFile(path.join(root, "PercLib/Empty.lean"), "");
    await fs.writeFile(path.join(root, "PercLib/Λ\tname.lean"), "-- Unicode and tab in path\n");
    await fs.writeFile(path.join(root, "wiki/articles/b.md"), '<a id="tag-BBBB"></a> Second\n');
    await fs.writeFile(path.join(root, "wiki/tags.json"), JSON.stringify({tags: [
      {tag: "AAAA", state: "allocated"}, {tag: "BBBB", state: "allocated"}, {tag: "CCCC", state: "withdrawn"},
    ]}));
    git("add", "."); git("commit", "-m", "Selected");
    const h = collectHistory(root), tip = h.tip;
    for (const [files, counts] of [[h.files, h.snapshots.at(-1)], [h.comparison.files, h.comparison.snapshot]]) {
      for (const key of ["leanLines", "articleWords", "assertions", "reservedTags", "withdrawnTags"])
        assert.equal(files.reduce((sum, file) => sum + (file.counts[key] || 0), 0), counts[key]);
      assert.equal(files.filter(f => f.kind === "library").length, counts.leanFiles);
      assert.equal(files.filter(f => f.kind === "article").length, counts.articles);
      assert.ok(files.every(f => /^[0-9a-f]{40,64}$/.test(f.blob)));
    }
    assert.ok(h.snapshots.every(row => row.files === undefined));
    assert.equal(h.comparison.snapshot.files, undefined);
    const library = historyPage(h, "library"), wiki = historyPage(h, "wiki");
    assert.match(library, /Keep\.lean<\/code><\/th><td>Modified/);
    assert.match(library, /Remove\.lean<\/code><\/th><td>Removed/);
    assert.match(library, /Empty\.lean<\/code><\/th><td>Added/);
    assert.match(library, /0 → 0 \(0\)/);
    assert.match(library, /1 → 1 \(0\)/);
    assert.match(library, /1 → 0 \(-1\)/);
    assert.ok(library.includes(`/blob/${reference}/PercLib/Remove.lean`));
    assert.ok(library.includes(`/blob/${tip}/PercLib/New%20%23%20%26.lean`));
    assert.match(library, /New # &amp;\.lean/);
    assert.ok(h.files.some(f => f.path === "PercLib/Λ\tname.lean" && f.counts.leanLines === 1));
    assert.ok(library.includes(`/blob/${tip}/PercLib/%CE%9B%09name.lean`));
    assert.match(wiki, /a\.md<\/code><\/th><td>Unchanged/);
    assert.match(wiki, /tags\.json<\/code><\/th><td>Modified/);
    assert.match(wiki, /1 → 3 \(\+2\)/);
    const missing = historyPage(collectHistory(root, "HEAD", "missing-ref"), "library");
    assert.match(missing, /Reference unavailable/);
    assert.doesNotMatch(missing, /<td>Added<\/td>|<td>Removed<\/td>/);
    const legacy = {...h, files: undefined};
    assert.doesNotMatch(historyPage(legacy, "library"), /File-level source comparison/);
  } finally { await fs.rm(root, {recursive: true, force: true}); }
});

test("reading-map-only commits have separate historical counts and reference inventories", async () => {
  const root = await fs.mkdtemp(path.join(os.tmpdir(), "wiki-map-history-"));
  const git = (...args) => execFileSync("git", args, {cwd: root, encoding: "utf8", stdio: ["ignore", "pipe", "pipe"]}).trim();
  const write = (file, text) => fs.writeFile(path.join(root, file), text);
  try {
    git("init"); git("config", "user.name", "Fixture"); git("config", "user.email", "fixture@example.invalid");
    await fs.mkdir(path.join(root, "wiki/sources/nested"), {recursive: true});
    await fs.mkdir(path.join(root, "wiki/articles"));
    await write("wiki/articles/a.md", "Article text");
    git("add", "."); git("commit", "-m", "Baseline");
    const first = git("rev-parse", "HEAD");
    await write("wiki/sources/map.md", "One two three");
    await write("wiki/sources/nested/excluded.md", "Not a reading map");
    await write("wiki/sources/excluded.txt", "Not Markdown");
    git("add", "."); git("commit", "-m", "Map only");
    const added = git("rev-parse", "HEAD");
    await write("wiki/sources/map.md", "One two three four five");
    git("add", "."); git("commit", "-m", "Expand map");
    await fs.rm(path.join(root, "wiki/sources/map.md"));
    git("add", "."); git("commit", "-m", "Remove map");
    await write("wiki/sources/dirty.md", "Uncommitted map");
    const h = collectHistory(root, "HEAD", added);
    assert.deepEqual(h.snapshots.map(r => r.readingMaps), [0, 1, 1, 0]);
    assert.deepEqual(h.snapshots.map(r => r.readingMapWords), [0, 3, 5, 0]);
    assert.ok(h.snapshots.every(r => r.articles === 1 && r.articleWords === 2 && r.assertions === 0));
    assert.equal(collectHistory(root, first).snapshots[0].readingMaps, 0);
    assert.equal(h.comparison.snapshot.readingMapWords, 3);
    assert.equal(h.comparison.files.find(f => f.kind === "reading-map").path, "wiki/sources/map.md");
    assert.equal(summarizeDays(h.snapshots).reduce((n, d) => n + d.changes.readingMapWords, 0), 0);
    const page = historyPage(h, "wiki");
    assert.match(page, /Reading-map source words/);
    assert.match(page, /Removed/);
    assert.match(page, /3 → 0 \(-3\)/);
    assert.doesNotMatch(page, /NaN|undefined|dirty.md|excluded.md/);
    const old = {...h, comparison: undefined, snapshots: h.snapshots.map(({readingMaps, readingMapWords, ...r}) => r)};
    assert.match(historyPage(old, "wiki"), /Reading-map counts are unavailable/);
    assert.doesNotMatch(historyPage(old, "wiki"), /NaN|undefined/);
  } finally { await fs.rm(root, {recursive: true, force: true}); }
});
