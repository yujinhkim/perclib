import { esc, heading } from "./render.mjs";

// COVERAGE.md remains the inventory. Read only its deliberately simple tables;
// do not treat arbitrary Markdown or HTML as executable page content.
export function coverageTables(markdown) {
  const tables = [];
  for (const block of markdown.split(/\n\s*\n/)) {
    const lines = block.trim().split("\n");
    if (!lines[0].startsWith("|")) continue;
    const cells = line => {
      if (!line.startsWith("|") || !line.endsWith("|"))
        throw Error("Malformed coverage table row");
      return line.slice(1, -1).split("|").map(cell => cell.trim());
    };
    const headers = cells(lines[0]);
    if (!lines[1] || cells(lines[1]).length !== headers.length ||
        !cells(lines[1]).every(cell => /^:?-+:?$/.test(cell)))
      throw Error("Malformed coverage table separator");
    const rows = lines.slice(2).map(cells);
    if (rows.some(row => row.length !== headers.length))
      throw Error("Malformed coverage table width");
    tables.push({headers, rows});
  }
  return tables;
}

function inline(text, articles, inventories = new Map(), fromReadingMap = false) {
  let result = "", offset = 0;
  for (const match of text.matchAll(/\[([^\]]+)\]\(([^\s)]+)\)/g)) {
    result += esc(text.slice(offset, match.index));
    let url = match[2];
    // Source maps live one directory below the article and errata sources.
    // Resolve only these two known siblings, never arbitrary parent paths.
    if (fromReadingMap && /^\.\.\/(?:articles|errata)\//.test(url))
      url = url.slice(3);
    const local = /^articles\/([a-z0-9-]+)\.md(#[A-Za-z0-9_-]+)?$/.exec(url);
    const inventory = /^sources\/([A-Za-z0-9]+(?:[.-][A-Za-z0-9]+)*)\.md$/.exec(url);
    const erratum = fromReadingMap && /^errata\/([a-z0-9-]+)\.json(#[A-Za-z0-9_-]+)?$/.exec(url);
    if (local) {
      if (!articles.has(local[1])) throw Error(`Unknown coverage article: ${local[1]}`);
      url = `/articles/${local[1]}/${local[2] ?? ""}`;
    } else if (inventory) {
      if (!inventories.has(inventory[1])) throw Error(`Unknown coverage inventory: ${inventory[1]}`);
      url = `/coverage/sources/${inventory[1]}/`;
    } else if (erratum) {
      // The final site-graph check rejects an absent page or entry anchor.
      url = `/errata/${erratum[1]}/${erratum[2] ?? ""}`;
    } else if (!/^https:\/\//.test(url)) {
      throw Error(`Unsupported coverage URL: ${url}`);
    }
    result += `<a href="${esc(url)}">${esc(match[1])}</a>`;
    offset = match.index + match[0].length;
  }
  return result + esc(text.slice(offset));
}

export function coveragePage(markdown, articles, inventories = new Map()) {
  const tables = coverageTables(markdown);
  const specs = [
    ["Chapter", "Notes: sections", "Every listed section still needs a semantic coverage audit, including unnumbered arguments and heuristics."],
    ["Source ID", "Notes: named statements", "Source IDs are inventory locators, not permanent assertion tags. A missing pointer is a gap in the record; a pointer is not a completeness or formal-proof certificate. Article links open this wiki snapshot; exact-revision links preserve historical source pointers. Neither establishes integration or proof status."],
    ["Text", "Other source texts", "These source inventories remain to be developed on demand. Selected correspondences do not establish complete coverage."],
  ];
  return heading("Source coverage worklist", "What is mapped, and what remains to be checked.") +
    '<p>This page renders the existing repository worklist. Topic pointers indicate relevant exposition; they do not certify that all hypotheses, conclusions, definitions or proof arguments in a passage are covered. No coverage percentage is inferred.</p><p>For statement-level source records and compiled evidence, use <a href="/sources/">Source concordance</a>. Mathematical content, formal status and correspondence review are separate checks.</p>' +
    (inventories.size ? `<section class="article-section"><h2>Version-specific reading maps</h2><ul>${[...inventories].map(([id, record]) => `<li><a href="/coverage/sources/${id}/">${esc(record.title)}</a></li>`).join("")}</ul></section>` : "") +
    specs.map(([key, title, note]) => {
      const matches = tables.filter(table => table.headers[0] === key);
      if (matches.length !== 1) throw Error(`Expected one coverage table: ${key}`);
      const {headers, rows} = matches[0];
      return `<section class="article-section"><h2>${title}</h2><p>${note}</p><p>${rows.length} inventory entries; this is a structural count, not a count of completed items.</p><div class="history-table"><table><caption>${title}</caption><thead><tr>${headers.map(header => `<th scope="col">${esc(header)}</th>`).join("")}</tr></thead><tbody>${rows.map(row => `<tr>${row.map((cell, index) => index === 0 ? `<th scope="row">${inline(cell, articles, inventories)}</th>` : `<td>${inline(cell, articles, inventories)}</td>`).join("")}</tr>`).join("")}</tbody></table></div></section>`;
    }).join("");
}

// Reading maps deliberately support only paragraphs, headings, links and simple
// tables. Raw HTML remains text, as in the canonical coverage worklist.
export function readingMapPage(record, articles, inventories = new Map()) {
  const blocks = record.markdown.trim().split(/\n\s*\n/);
  if (!/^# [^\n]+$/.test(blocks[0])) throw Error("Reading map needs a standalone title");
  return heading(record.title, "Version-specific source reading map") +
    '<p><a href="/coverage/">Back to the coverage worklist</a>. A reading map is not a proof or a formal correspondence certificate.</p>' +
    blocks.slice(1).map(block => {
      if (block.startsWith("|")) {
        const [{ headers, rows }] = coverageTables(block);
        return `<div class="history-table"><table><caption>${esc(record.title)}</caption><thead><tr>${headers.map(h => `<th scope="col">${esc(h)}</th>`).join("")}</tr></thead><tbody>${rows.map(row => `<tr>${row.map((cell, i) => i ? `<td>${inline(cell, articles, inventories, true)}</td>` : `<th scope="row">${inline(cell, articles, inventories, true)}</th>`).join("")}</tr>`).join("")}</tbody></table></div>`;
      }
      const h = /^(#{2,3}) ([^\n]+)$/.exec(block);
      if (h) return `<h${h[1].length}>${esc(h[2])}</h${h[1].length}>`;
      return `<p class="reading-map-prose">${inline(block.replace(/\n/g, " "), articles, inventories, true)}</p>`;
    }).join("");
}
