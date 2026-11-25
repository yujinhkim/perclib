import fs from "node:fs/promises";
import path from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
import { createRequire } from "node:module";
import { checkArticles, checkHistory } from "../scripts/check-articles.mjs";
import { validateOccurrences, concordancePanel } from "./concordance.mjs";
import { collectHistory, historyPage } from "./history.mjs";
import { coveragePage, readingMapPage } from "./coverage.mjs";
import { historyCsv, dailyHistoryCsv, fileHistoryCsv } from "./history-csv.mjs";
import { validateProofUses, frontierPage } from "./frontier.mjs";
import { loadEvidence, evidencePanel, statusFor } from "./manifest.mjs";
import { readRegistry } from "../scripts/articles.mjs";
import { loadRecords } from "./records.mjs";
import { loadErrata, errataPage, articleErrata, errataNotice } from "./errata.mjs";
import {
  esc,
  decode,
  plain,
  articleUrl,
  transform,
  heading,
  item,
  railBlock,
  document,
} from "./render.mjs";
const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
export function validateLinks(files) {
  for (const [file, html] of files) {
    if (!file.endsWith(".html")) continue;
    for (const m of html.matchAll(/(?:href|src)="([^"]+)"/g)) {
      const href = decode(m[1]);
      if (/^(https?:|mailto:|data:)/.test(href)) continue;
      const url = new URL(href, `https://wiki.invalid/${file}`);
      let target = decodeURIComponent(url.pathname).slice(1);
      if (!target || target.endsWith("/")) target += "index.html";
      if (!files.has(target))
        throw Error(`${file}: missing destination ${href}`);
      if (
        url.hash &&
        target.endsWith(".html") &&
        !files
          .get(target)
          .includes(`id="${decodeURIComponent(url.hash.slice(1))}"`)
      )
        throw Error(`${file}: missing anchor ${href}`);
    }
  }
}
export async function build(
  output = path.join(root, "dist"),
  evidenceOptions = {},
) {
  const { articles, assertions, baseline } = await checkArticles();
  await checkHistory();
  const registry = await readRegistry();
  const evidence = await loadEvidence(assertions, {
    reviewsPath: path.join(root, "reviews/correspondence.json"),
    ...evidenceOptions,
  });
  const records = await loadRecords(root, articles, assertions);
  const proofUses = validateProofUses(
    evidenceOptions.proofUsesPath
      ? JSON.parse(await fs.readFile(evidenceOptions.proofUsesPath, "utf8"))
      : records.proofUses,
    assertions,
  );
  const evidenceCounts = evidence.entries
    ? [...evidence.entries.values()].reduce(
        (counts, entry) => {
          const result = statusFor(entry, evidence.reviews);
          const status =
            result.status ?? "Compiled statement; correspondence pending";
          counts.status[status] = (counts.status[status] ?? 0) + 1;
          if (entry.proof_status !== "unformalised")
            counts.review[result.reviewState] =
              (counts.review[result.reviewState] ?? 0) + 1;
          return counts;
        },
        { status: {}, review: {} },
      )
    : null;
  const evidenceSummary = evidenceCounts
    ? "<h2>Compiled evidence snapshot</h2><p>This is one supplied snapshot, not a historical series. Proof status and prose correspondence are separate counts.</p>" +
      Object.entries(evidenceCounts)
        .map(
          ([axis, counts]) =>
            "<h3>" +
            (axis === "status"
              ? "Assertion status"
              : "Correspondence of compiled statements") +
            "</h3><ul>" +
            Object.entries(counts)
              .map(
                ([label, count]) =>
                  "<li>" + esc(label) + ": " + count + "</li>",
              )
              .join("") +
            "</ul>",
        )
        .join("")
    : "";
  const history = collectHistory(root, evidenceOptions.historyRef);
  const pages = new Map(articles.map((p) => [p.id, p]));
  const read = async (file) =>
    JSON.parse(await fs.readFile(path.join(root, "src/content", file), "utf8"));
  const { collections, sources } = records;
  const errata = await loadErrata(root, sources, assertions);
  const occurrences = validateOccurrences(
    evidenceOptions.occurrencesPath
      ? JSON.parse(await fs.readFile(evidenceOptions.occurrencesPath, "utf8"))
      : records.occursIn,
    sources,
    assertions,
  );
  const concordance = (rows) =>
    concordancePanel(rows, sources, assertions, evidence);
  const reuse = await read("reuse-audit.json");
  const files = new Map();
  const format = (html) => transform(html, pages, baseline);
  const add = (
    route,
    title,
    body,
    rail = "",
    description = "",
    extraHead = "",
  ) => {
    const file = route ? `${route}/index.html` : "index.html";
    if (files.has(file)) throw Error(`Duplicate route: ${route}`);
    files.set(
      file,
      document(title, format(body), {
        collections,
        rail: format(rail),
        description,
        extraHead,
      }),
    );
  };
  const links = (ids) =>
    ids
      .map((id) => {
        if (!pages.has(id)) throw Error(`Missing article ${id}`);
        return `<a class="rail-link" href="${articleUrl(id)}">${esc(pages.get(id).title)}</a>`;
      })
      .join("");
  const occurrence = (o) => {
    if (!pages.has(o.pageId))
      throw Error(`Missing occurrence article ${o.pageId}`);
    if (
      o.sectionId &&
      !pages.get(o.pageId).sections.some((s) => s.id === o.sectionId)
    )
      throw Error(`Missing occurrence section ${o.sectionId}`);
    return `<div class="article-section"><h3><a href="${articleUrl(o.pageId)}${o.sectionId ? "#section-" + o.sectionId : ""}">${esc(o.label)}</a></h3><p>${esc(o.locator)}</p><p>${esc(o.relationship)} · ${esc(o.status)}</p><p>${esc(o.note)}</p></div>`;
  };
  for (const p of articles) {
    const own = assertions.filter((a) => a.article === p.id);
    const incoming = articles
      .filter(
        (q) =>
          q.id !== p.id &&
          q.sections.some((s) => s.html.includes(`href="#/${p.id}`)),
      )
      .map((q) => q.id);
    const body =
      heading(p.title, p.subtitle || p.summary, p.kind) +
      articleErrata(p.id, errata, assertions) +
      `<div class="running-context"><h2>Running context</h2><ul>${p.context.map((c) => `<li>${c}</li>`).join("")}</ul></div>` +
      p.sections
        .map(
          (s) =>
            `<section class="article-section" id="section-${s.id}"><h2>${esc(s.title)}</h2>${s.html}</section>`,
        )
        .join("") +
      `<section class="article-section" id="connections"><h2>Connections</h2><p>These are editorial reading links, not dependencies extracted from Lean.</p><h3>Prerequisites</h3>${links(p.prototypeUses)}<h3>Related articles</h3>${links(p.related)}<h3>What links here</h3>${links(incoming)}</section>` +
      `<section class="article-section" id="sources"><h2>Sources</h2><ul>${p.sourceIds
        .map((id) => {
          const source = sources.find((s) => s.id === id);
          if (!source) throw Error(`Missing source ${id}`);
          return `<li><a href="/sources/${id}/">${esc(source.shortName)}</a></li>`;
        })
        .join(
          "",
        )}</ul>${sources.flatMap((s) => s.occurrences.filter((o) => o.pageId === p.id).map((o) => `<h3><a href="/sources/${s.id}/">${esc(s.shortName)}</a></h3>${occurrence(o)}`)).join("")}</section>` +
      `<section class="article-section" id="citations"><h2>Assertion citations</h2><div class="tag-citations">${own.map((a) => `<a href="/tag/${a.tag}/">${a.tag} · ${esc(a.title)}</a>`).join("")}</div></section>` +
      evidencePanel(own, evidence) +
      concordance(occurrences.filter((o) => own.some((a) => a.tag === o.tag)));
    const rail =
      railBlock(
        "On this page",
        p.sections
          .map((s) => `<a href="#section-${s.id}">${esc(s.title)}</a>`)
          .join("") +
          '<a href="#connections">Connections</a><a href="#sources">Sources</a>',
      ) +
      railBlock(
        "Cite an assertion",
        `<div class="tag-citations">${own.map((a) => `<a href="/tag/${a.tag}/" title="${esc(a.title)}">${a.tag}</a>`).join("")}</div>`,
      ) +
      railBlock("Related reading", links(p.related));
    add(`articles/${p.id}`, p.title, body, rail, p.summary);
    add(
      p.id,
      p.title,
      `<p>This article is at <a href="${articleUrl(p.id)}">${esc(p.title)}</a>.</p>`,
      "",
      "",
      `<meta http-equiv="refresh" content="0;url=${articleUrl(p.id)}">`,
    );
  }
  add(
    "articles",
    "Article index",
    heading("Article index", "Browse the mathematical reference.") +
      articles.map(item).join(""),
  );
  add(
    "",
    "Library overview",
    heading(
      "A connected theory of percolation.",
      "A mathematical encyclopedia of models, results, and proofs.",
      "The mathematical library",
    ) +
      `<div class="collection-grid">${collections
        .map(
          (c) =>
            `<section class="collection"><h2 class="collection-heading"><a href="/collections/${c.id}/">${esc(c.title)}</a><small>${c.pages.length} pages</small></h2><p>${esc(c.description)}</p>${c.pages
              .slice(0, 3)
              .map((id) => item(pages.get(id)))
              .join("")}</section>`,
        )
        .join(
          "",
        )}</div><section class="featured-theorem"><p class="eyebrow">One complete argument to explore</p><h2><a href="${articleUrl("subcritical-bound")}">From a row-sum bound to finite clusters</a></h2><p>Count simple paths, sum walk weights, and bound susceptibility.</p></section>`,
  );
  add(
    "subjects",
    "Subject index",
    heading("Subjects") +
      collections
        .map(
          (c) =>
            `<section class="article-section"><h2><a href="/collections/${c.id}/">${esc(c.title)}</a></h2><p>${esc(c.description)}</p></section>`,
        )
        .join(""),
  );
  for (const c of collections)
    add(
      `collections/${c.id}`,
      c.title,
      heading(c.title, c.description) +
        c.pages
          .map((id) => {
            if (!pages.has(id)) throw Error(`Missing article ${id}`);
            return item(pages.get(id));
          })
          .join(""),
    );
  add(
    "sources",
    "Source concordance",
    heading(
      "Source concordance",
      "Bibliographic records and recorded article correspondences.",
    ) +
      `<p><a href="/errata/">Source errata and provisional corrections</a></p>` +
      '<p><a href="/coverage/">Source coverage worklist</a> — all inventoried sections and named statements, including gaps.</p>' +
      concordance(occurrences) +
      sources
        .map(
          (s) =>
            `<section class="article-section"><h2><a href="/sources/${s.id}/">${esc(s.title)}</a></h2><p>${esc(s.author)} · ${esc(s.year)}</p><p>${esc(s.description)}</p></section>`,
        )
        .join(""),
  );
  const inventories = new Map();
  const inventoryRoot = evidenceOptions.readingMapsPath ?? path.join(root, "sources");
  let inventoryFiles;
  try { inventoryFiles = await fs.readdir(inventoryRoot, { withFileTypes: true }); }
  catch (error) { if (error.code !== "ENOENT") throw error; inventoryFiles = []; }
  for (const file of inventoryFiles.sort((a, b) => a.name.localeCompare(b.name))) {
    if (!file.name.endsWith(".md")) continue;
    if (!file.isFile() || !/^[A-Za-z0-9]+(?:[.-][A-Za-z0-9]+)*\.md$/.test(file.name))
      throw Error(`Invalid reading map file: ${file.name}`);
    const markdown = (await fs.readFile(path.join(inventoryRoot, file.name), "utf8")).replace(/\r\n/g, "\n");
    const title = /^# ([^\n]+)\n/.exec(markdown)?.[1];
    if (!title) throw Error(`Reading map needs a title: ${file.name}`);
    inventories.set(file.name.slice(0, -3), { title, markdown });
  }
  add("coverage", "Source coverage worklist",
    coveragePage(await fs.readFile(evidenceOptions.coveragePath ?? path.join(root, "COVERAGE.md"), "utf8"), pages, inventories));
  for (const [id, record] of inventories)
    add(`coverage/sources/${id}`, record.title, readingMapPage(record, pages, inventories));
  for (const s of sources)
    add(
      `sources/${s.id}`,
      s.shortName,
      heading(s.title, s.description) +
        (errata.some((e) => e.source === s.id) ? `<p><a href="/errata/${s.id}/">Source errata and provisional corrections</a></p>` : "") +
        concordance(occurrences.filter((o) => o.source === s.id)) +
        `<p>${esc(s.author)} · ${esc(s.year)} · ${esc(s.edition)}</p><p><a href="${esc(s.url)}">Source</a></p><p>${esc(s.coverageNote)}</p>` +
        s.occurrences.map(occurrence).join(""),
    );
  add("errata", "Source errata", heading("Source errata", errataNotice) +
    errata.map((data) => {
      const source = sources.find((s) => s.id === data.source);
      return `<section class="article-section"><h2><a href="/errata/${source.id}/">${esc(source.shortName)}</a></h2><p>${data.entries.length} recorded entries · ${esc(source.edition)}</p><ul>${data.entries.map((entry) => `<li><a href="/errata/${source.id}/#${entry.id}">${esc(entry.title)}</a> — ${entry.status}</li>`).join("")}</ul></section>`;
    }).join(""));
  for (const data of errata) {
    const source = sources.find((s) => s.id === data.source);
    add(`errata/${source.id}`, `${source.shortName}: errata`, errataPage(data, source, assertions, evidence));
  }
  // Preserve every field of the dated provenance records without implying current status.
  const record = (value) => {
    if (value === null) return "Not recorded";
    if (Array.isArray(value))
      return `<ul>${value.map((v) => `<li>${record(v)}</li>`).join("")}</ul>`;
    if (typeof value === "object")
      return `<dl class="record">${Object.entries(value)
        .map(([k, v]) => `<dt>${esc(k)}</dt><dd>${record(v)}</dd>`)
        .join("")}</dl>`;
    if (typeof value === "string" && /^https:\/\//.test(value))
      return `<a href="${esc(value)}">${esc(value)}</a>`;
    return esc(value);
  };
  add(
    "provenance",
    "Lean & provenance",
    heading("Reused foundations and provenance") +
      "<p>These records describe their cited revisions, not the current state of the repository or the formal status of an article.</p>" +
      record(reuse),
  );
  add(
    "frontier",
    "Proof frontier",
    frontierPage(assertions, evidence, proofUses),
  );
  files.set("metrics/history.json", JSON.stringify(history, null, 2) + "\n");
  const csv = historyCsv(history);
  if (csv !== null) files.set("metrics/history.csv", csv);
  const dailyCsv = dailyHistoryCsv(history);
  if (dailyCsv !== null) files.set("metrics/history-daily.csv", dailyCsv);
  const fileCsv = fileHistoryCsv(history);
  if (fileCsv !== null) files.set("metrics/history-files.csv", fileCsv);
  add(
    "metrics/library",
    "Formalization library growth",
    historyPage(history, "library"),
  );
  add("metrics/wiki", "Wiki growth", historyPage(history, "wiki"));
  add(
    "metrics",
    "Project metrics",
    heading("Project metrics") +
      evidenceSummary +
      '<p><a href="/metrics/library/">Formalization library growth</a> · <a href="/metrics/wiki/">Wiki growth</a></p><p>Growth pages show source history. Verified status comes only from the separately supplied compiled evidence.</p>' +
      `<p>This site contains ${articles.length} articles and ${assertions.length} active assertion tags. These counts describe this site build, not the number of Lean proofs.</p>` +
      (evidence.provenance
        ? `<p>Formal evidence comes from <a href="${evidence.provenance.runUrl}">this successful CI run</a>, compiled commit <code>${evidence.provenance.commit}</code>.</p>`
        : "<p>No compiled manifest is supplied.</p>"),
  );
  add(
    "about",
    "About the library",
    heading("About the library") +
      '<section class="article-section"><p>A mathematical reference with permanent assertion citations. Article text, hypotheses, and source references are preserved from the initial exposition. A citation identifies an assertion; it does not certify a Lean proof.</p><p>All articles and mathematics are rendered before publication. Search runs in your browser over a static index. The wiki build does not run Lean.</p></section>',
  );
  add(
    "search",
    "Search",
    heading("Search the library") +
      '<form id="search-form" action="/search/" class="catalog-filter"><label class="catalog-query"><span>Title, concept, source, or tag</span><input type="search" name="q" autocomplete="off"></label><button class="button button-primary">Search</button></form><p id="search-status" role="status">Type to search. JavaScript is needed for filtering; the full article index is below.</p><div id="search-results">' +
      articles.map(item).join("") +
      "</div>",
  );
  const index = articles.map((p) => ({
    title: p.title,
    summary: p.summary,
    url: articleUrl(p.id),
    text: [
      p.title,
      p.summary,
      ...p.aliases,
      ...p.context,
      ...p.sections.map((s) => s.title + " " + plain(s.html)),
      ...assertions
        .filter((a) => a.article === p.id)
        .map((a) => a.tag + " " + a.title),
    ].join(" "),
  }));
  index.push(
    ...[...inventories].map(([id, record]) => ({
      title: record.title,
      summary: "Version-specific source reading map; coverage remains to be checked.",
      url: `/coverage/sources/${id}/`,
      text: record.markdown,
    })),
    ...assertions.map((a) => ({
      title: `${a.tag} · ${a.title}`,
      summary: pages.get(a.article).title,
      url: `/tag/${a.tag}/`,
      text: `${a.tag} ${a.title}`,
    })),
    ...sources.map((s) => ({
      title: s.title,
      summary: s.description,
      url: `/sources/${s.id}/`,
      text: [
        s.title,
        s.author,
        s.shortName,
        ...s.occurrences.map((o) => o.label + " " + o.locator),
      ].join(" "),
    })),
  );
  index.push(...errata.flatMap((data) => data.entries.map((entry) => ({
    title: `${entry.title} (${entry.status})`, summary: entry.status === "withdrawn" ? entry.withdrawalReason : entry.problem,
    url: `/errata/${data.source}/#${entry.id}`,
    text: [entry.title, entry.status, entry.locator, ...(entry.status === "withdrawn" ? [entry.withdrawalReason] : [entry.claim, entry.problem, entry.correction, entry.leanImpact]), ...entry.tags].join(" "),
  }))));
  files.set("search-index.json", JSON.stringify(index) + "\n");
  for (const entry of registry.tags) {
    const a = assertions.find((a) => a.tag === entry.tag),
      target = a ? `${articleUrl(a.article)}#${a.anchor}` : null;
    add(
      `tag/${entry.tag}`,
      `Assertion ${entry.tag}`,
      heading(`Assertion ${entry.tag}`) +
        (target
          ? `<p><a href="${target}">${esc(a.title)}</a></p>`
          : `<p>This identity is ${entry.state === "withdrawn" ? "withdrawn" : "reserved but not yet attached to an assertion"}. It will never be reused.</p>`),
      "",
      "",
      target
        ? `<link rel="canonical" href="${target}"><meta http-equiv="refresh" content="0;url=${target}">`
        : "",
    );
  }
  for (const name of await fs.readdir(path.join(root, "src/assets")))
    files.set(
      `assets/${name}`,
      await fs.readFile(path.join(root, "src/assets", name), "utf8"),
    );
  let katexRoot;
  try {
    katexRoot = path.dirname(
      createRequire(import.meta.url).resolve("katex/package.json"),
    );
  } catch {
    katexRoot = path.dirname(
      createRequire(
        new URL("../prototype/package.json", import.meta.url),
      ).resolve("katex/package.json"),
    );
  }
  files.set(
    "assets/katex/katex.min.css",
    await fs.readFile(path.join(katexRoot, "dist/katex.min.css"), "utf8"),
  );
  validateLinks(files);
  // Replace only generated output, after input and link validation succeed.
  await fs.rm(output, { recursive: true, force: true });
  for (const [file, content] of files) {
    await fs.mkdir(path.dirname(path.join(output, file)), { recursive: true });
    await fs.writeFile(path.join(output, file), content);
  }
  await fs.cp(
    path.join(katexRoot, "dist/fonts"),
    path.join(output, "assets/katex/fonts"),
    { recursive: true },
  );
  await fs.copyFile(
    path.join(katexRoot, "LICENSE"),
    path.join(output, "assets/katex/LICENSE"),
  );
  console.log(
    `Built ${articles.length} static articles, ${assertions.length} assertion redirects, ${registry.tags.filter((t) => t.state === "withdrawn").length} tombstones; all local links and mathematics validated.`,
  );
  return files;
}
if (process.argv[1] && import.meta.url === pathToFileURL(process.argv[1]).href)
  await build();
