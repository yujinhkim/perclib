import test from "node:test";
import assert from "node:assert/strict";
import fs from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { build, validateLinks } from "../src/build.mjs";
import { renderMath, legacyUrl } from "../src/render.mjs";
import {
  readArticles,
  readRegistry,
  assertionsIn,
} from "../scripts/articles.mjs";

test("static output contains all articles, pre-rendered math, citation destinations and tombstones", async () => {
  const dir = await fs.mkdtemp(path.join(os.tmpdir(), "wiki-static-"));
  try {
    const readingMapsPath = await fs.mkdtemp(path.join(dir, "maps-"));
    await fs.cp(new URL("../sources/", import.meta.url), readingMapsPath, {recursive: true});
    await fs.writeFile(path.join(readingMapsPath, "paper-I-2103.17013v1.md"), '# Fixture reading map\n\n[Paths](../articles/connectivity.md#section-paths)\n\n| Locator | Scope |\n|---|---|\n| 1 | Unfinished |\n');
    const files = await build(path.join(dir, "output"), {readingMapsPath}),
      articles = await readArticles();
    assert.match(files.get("frontier/index.html"), /proof frontier is unavailable/);
    assert.match(files.get("index.html"), /href="\/frontier\/"/);
    const assertions = assertionsIn(articles),
      registry = await readRegistry();
    for (const p of articles) {
      const html = files.get(`articles/${p.id}/index.html`);
      assert.ok(html.includes('<h1 class="page-title">'));
      if (
        [...p.context, ...p.sections.map((s) => s.html)].some((s) =>
          s.includes("$"),
        )
      )
        assert.ok(html.includes('class="katex"'), p.id);
      assert.ok(
        !html.includes("auto-render") && !html.includes("katex.min.js"),
      );
      assert.ok(!/href=["']#\//.test(html));
      for (const s of p.sections)
        assert.ok(html.includes(`id="section-${s.id}"`));
    }
    for (const a of assertions) {
      const html = files.get(`articles/${a.article}/index.html`);
      assert.equal(html.split(`id="tag-${a.tag}"`).length - 1, 1);
      const redirect = files.get(`tag/${a.tag}/index.html`);
      assert.ok(redirect.includes(`url=/articles/${a.article}/#tag-${a.tag}`));
      assert.ok(
        redirect.includes(`href="/articles/${a.article}/#tag-${a.tag}"`),
      );
    }
    for (const t of registry.tags.filter((t) => t.state === "withdrawn")) {
      const html = files.get(`tag/${t.tag}/index.html`);
      assert.ok(html.includes("withdrawn"));
      assert.ok(!html.includes('http-equiv="refresh"'));
    }
    const index = JSON.parse(files.get("search-index.json"));
    assert.match(files.get("coverage/index.html"), /href="\/coverage\/sources\/paper-I-2103.17013v1\/"/);
    assert.match(files.get("coverage/sources/paper-I-2103.17013v1/index.html"), /href="\/articles\/connectivity\/#section-paths"/);
    assert.ok(index.some(row => row.url === '/coverage/sources/paper-I-2103.17013v1/' && row.text.includes('Unfinished')));
    for (const a of assertions)
      assert.ok(index.some((row) => row.url === `/tag/${a.tag}/`));
    // Validate the actual site graph, then prove a broken citation fails it.
    files.set(
      "bad/index.html",
      '<a href="/articles/connectivity/#absent">bad</a>',
    );
    assert.throws(() => validateLinks(files), /missing anchor/);
    files.set("bad/index.html", '<a href="/absent/">bad</a>');
    assert.throws(() => validateLinks(files), /missing destination/);
  } finally {
    await fs.rm(dir, { recursive: true, force: true });
  }
});
test("math compilation fails invalid input rather than publishing raw or erroneous mathematics", () => {
  assert.throws(() => renderMath("$\\definitelynotacommand$"));
  const html = renderMath("<p>$a&lt;b$</p><div>$$x^2$$</div>");
  assert.ok(html.includes("katex-display"));
  assert.ok(html.includes("annotation"));
});
test("legacy section citations preserve destination and reject nonexistent sections", () => {
  const articles = new Map([["example", { sections: [{ id: "proof" }] }]]);
  const baseline = { articles: { example: { prototypeId: "PC-000001" } } };
  assert.equal(
    legacyUrl("#/id/PC-000001?section=proof", articles, baseline),
    "/articles/example/#section-proof",
  );
  assert.throws(
    () => legacyUrl("#/example?section=missing", articles, baseline),
    /Missing section/,
  );
});
