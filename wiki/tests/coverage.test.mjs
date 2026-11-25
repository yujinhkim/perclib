import test from "node:test";
import assert from "node:assert/strict";
import fs from "node:fs/promises";
import { coveragePage, coverageTables, readingMapPage } from "../src/coverage.mjs";
import { readArticles } from "../scripts/articles.mjs";
import { validateLinks } from "../src/build.mjs";

test("coverage renders the canonical inventory and preserves every row", async () => {
  const markdown = await fs.readFile(new URL("../COVERAGE.md", import.meta.url), "utf8");
  const articles = new Set((await readArticles()).map(article => article.id));
  const tables = coverageTables(markdown);
  const mapFiles = (await fs.readdir(new URL("../sources/", import.meta.url))).filter(file => file.endsWith(".md"));
  const maps = new Map(mapFiles.map(file => [file.slice(0, -3), {title: file.slice(0, -3)}]));
  const page = coveragePage(markdown, articles, maps);
  assert.equal(tables.find(t => t.headers[0] === "Chapter").rows.length, 56);
  assert.equal(tables.find(t => t.headers[0] === "Source ID").rows.length, 45);
  assert.equal([...page.matchAll(/<tr>/g)].length,
    tables.reduce((sum, table) => sum + table.rows.length + 1, 0));
  assert.match(page, /not a completeness or formal-proof certificate/);
  assert.match(page, /href="\/articles\/branching-processes\/"/);
  assert.match(page, /not a count of completed items/);
});

const fixture = cell => `| Chapter | Section | Source |
|---|---|---|
| 1 | ${cell} | [Source](https://example.org/source) |

| Source ID | Title |
|---|---|
| S001 | Statement |

| Text | Remaining work |
|---|---|
| Book | Read it |
`;
test("coverage escapes text and rejects unsafe or stale links", () => {
  assert.match(coveragePage(fixture('<script>alert(1)</script>'), new Set()), /&lt;script&gt;/);
  assert.throws(() => coveragePage(fixture('[bad](javascript:alert)'), new Set()), /Unsupported coverage URL/);
  assert.throws(() => coveragePage(fixture('[missing](articles/missing.md)'), new Set()), /Unknown coverage article/);
  assert.throws(() => coveragePage(fixture('Extra | cell'), new Set()), /table width/);
  assert.throws(() => coveragePage('', new Set()), /Expected one coverage table/);
});

test("coverage preserves article fragments and validates reading-map destinations", () => {
  const articles = new Set(["connectivity"]);
  const maps = new Map([["paper-2103.17013v1", {title: "Paper <v1>"}]]);
  const page = coveragePage(fixture('[Paths](articles/connectivity.md#section-paths) and [Map](sources/paper-2103.17013v1.md)'), articles, maps);
  assert.match(page, /href="\/articles\/connectivity\/#section-paths"/);
  assert.match(page, /href="\/coverage\/sources\/paper-2103.17013v1\/"/);
  assert.match(page, /Paper &lt;v1&gt;/);
  assert.throws(() => coveragePage(fixture('[Map](sources/missing.md)'), articles, maps), /Unknown coverage inventory/);
  for (const target of ['sources/../outside.md', 'articles/connectivity.md#bad"', 'file:///tmp/local'])
    assert.throws(() => coveragePage(fixture(`[Bad](${target})`), articles, maps), /Unsupported coverage URL/);
});

test("reading maps preserve paragraphs and tables while escaping source markup", () => {
  const markdown = '# Paper\n\nFirst line\nsecond line. <script>bad</script>\n\n## Scope\n\n| Locator | Reading |\n|---|---|\n| A | [Paths](articles/connectivity.md#section-paths) |\n\nRemaining work.';
  const page = readingMapPage({title: 'Paper', markdown}, new Set(['connectivity']));
  assert.match(page, /First line second line\. &lt;script&gt;bad&lt;\/script&gt;/);
  assert.match(page, /<h2>Scope<\/h2>/);
  assert.match(page, /<th scope="row">A<\/th>/);
  assert.match(page, /Remaining work/);
  assert.match(page, /href="\/articles\/connectivity\/#section-paths"/);
  assert.throws(() => readingMapPage({title:'Bad',markdown:'# Bad\n\n[bad](javascript:alert)'}, new Set()), /Unsupported coverage URL/);
  assert.throws(() => readingMapPage({title:'Bad',markdown:'Missing title'}, new Set()), /standalone title/);
});

test("reading maps resolve case-preserving source names and known sibling resources", () => {
  const articles = new Set(["connectivity"]);
  const inventories = new Map([["long-range-I-2508.18807v1", {title: "Critical LRP I"}]]);
  const markdown = '# Paper\n\n[Paths](../articles/connectivity.md#section-paths)\n\n| Locator | Reading |\n|---|---|\n| I | [Correction](../errata/paper.json#correction) |\n\n[Related map](sources/long-range-I-2508.18807v1.md)';
  const page = readingMapPage({title: "Paper", markdown}, articles, inventories);
  const files = new Map([
    ["coverage/sources/paper/index.html", page],
    ["coverage/index.html", ""],
    ["articles/connectivity/index.html", '<div id="section-paths"></div>'],
    ["errata/paper/index.html", '<div id="correction"></div>'],
    ["coverage/sources/long-range-I-2508.18807v1/index.html", ""],
  ]);
  assert.doesNotThrow(() => validateLinks(files));
  files.delete("errata/paper/index.html");
  assert.throws(() => validateLinks(files), /missing destination/);
  files.set("errata/paper/index.html", "");
  assert.throws(() => validateLinks(files), /missing anchor/);
  assert.throws(() => coveragePage(fixture('[Map](sources/long-range-i-2508.18807v1.md)'), articles, inventories), /Unknown coverage inventory/);
  assert.throws(() => coveragePage(fixture('[Paths](../articles/connectivity.md)'), articles, inventories), /Unsupported coverage URL/);
  for (const target of ['../../articles/connectivity.md', '../articles/../outside.md', '../errata/../outside.json', '../errata/paper.json#bad"'])
    assert.throws(() => readingMapPage({title: "Bad", markdown: `# Bad\n\n[Bad](${target})`}, articles, inventories), /Unsupported coverage URL/);
});
