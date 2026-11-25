import { createRequire } from "node:module";
const require = createRequire(import.meta.url);
// The old CI entry point installs the same pinned dependency under prototype/.
let katex;
try {
  katex = require("katex");
} catch (error) {
  if (error.code !== "MODULE_NOT_FOUND") throw error;
  katex = createRequire(new URL("../prototype/package.json", import.meta.url))(
    "katex",
  );
}
export const esc = (value) =>
  String(value ?? "").replace(
    /[&<>"']/g,
    (c) =>
      ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" })[
        c
      ],
  );
export const decode = (value) =>
  value
    .replace(/&lt;/g, "<")
    .replace(/&gt;/g, ">")
    .replace(/&quot;/g, '"')
    .replace(/&#39;/g, "'")
    .replace(/&amp;/g, "&");
export const plain = (value) =>
  decode(String(value).replace(/<[^>]*>/g, " "))
    .replace(/\s+/g, " ")
    .trim();
export const articleUrl = (id) => `/articles/${id}/`;
export function renderMath(html) {
  // Article bodies use dollar delimiters in text, never in attributes. Keep tags intact.
  return html
    .split(
      /(<pre\b[^>]*>[\s\S]*?<\/pre>|<code\b[^>]*>[\s\S]*?<\/code>|<[^>]*>)/g,
    )
    .map((part) =>
      part.startsWith("<")
        ? part
        : part.replace(
            /\$\$([\s\S]*?)\$\$|\$([^$]+?)\$/g,
            (_, display, inline) =>
              katex.renderToString(decode(display ?? inline), {
                displayMode: display !== undefined,
                throwOnError: true,
                strict: "error",
                trust: false,
              }),
          ),
    )
    .join("");
}
export function legacyUrl(href, articles, baseline) {
  const [route, query = ""] = decode(href).slice(2).split("?");
  const params = new URLSearchParams(query);
  const legacy = route.startsWith("id/")
    ? Object.keys(baseline.articles).find(
        (id) => baseline.articles[id].prototypeId === route.slice(3),
      )
    : null;
  const id = legacy || route;
  if (articles.has(id)) {
    const section = params.get("section");
    if (section && !articles.get(id).sections.some((s) => s.id === section))
      throw Error(`Missing section: ${href}`);
    return (
      articleUrl(id) +
      (section
        ? `#section-${section}`
        : params.get("view") === "connections"
          ? "#connections"
          : params.get("view") === "lean"
            ? "#formal-evidence"
            : "")
    );
  }
  if (!route || route === "library") return "/";
  if (route === "index") return "/articles/";
  return `/${route}/`;
}
export function transform(html, articles, baseline) {
  return renderMath(
    html.replace(
      /href\s*=\s*(["'])(#\/[^"']*)\1/g,
      (_, quote, href) =>
        `href=${quote}${esc(legacyUrl(href, articles, baseline))}${quote}`,
    ),
  );
}
export const heading = (title, summary = "", kind = "") =>
  `<header class="article-header">${kind ? `<p class="eyebrow">${esc(kind)}</p>` : ""}<h1 class="page-title">${esc(title)}</h1>${summary ? `<p class="lede">${esc(summary)}</p>` : ""}</header>`;
export const item = (p) =>
  `<a class="item-row" href="${articleUrl(p.id)}"><span class="item-main"><span class="item-title">${esc(p.title)}</span><span class="item-desc">${esc(p.subtitle || p.summary)}</span></span></a>`;
export const railBlock = (title, body) =>
  `<div class="context-block"><h2 class="context-title">${esc(title)}</h2>${body}</div>`;
export function document(
  title,
  body,
  { collections, rail = "", description = "", extraHead = "" } = {},
) {
  return `<!doctype html><html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1"><meta name="description" content="${esc(description)}"><title>${esc(title)} · Percolation Library</title><link rel="stylesheet" href="/assets/katex/katex.min.css"><link rel="stylesheet" href="/assets/style.css"><link rel="stylesheet" href="/assets/details.css"><link rel="stylesheet" href="/assets/navigation.css"><link rel="stylesheet" href="/assets/static.css"><script defer src="/assets/site.js"></script>${extraHead}</head><body><a class="skip-link" href="#main-content">Skip to content</a><header class="site-header"><button class="icon-button sidebar-toggle" id="menu-toggle" aria-controls="sidebar" aria-expanded="false" aria-label="Open navigation">☰</button><a class="brand" href="/">Percolation Library</a><nav class="top-nav" aria-label="Main navigation"><a href="/articles/">Browse</a><a href="/sources/">Sources</a><a href="/provenance/">Lean & provenance</a></nav><div class="header-tools"><a class="search-trigger" href="/search/">Search the library</a></div></header><div class="site-shell"><aside class="sidebar" id="sidebar" aria-label="Library navigation"><div class="sidebar-inner"><div class="nav-group"><a class="nav-link" href="/">Library overview</a><a class="nav-link" href="/articles/">Article index</a><a class="nav-link" href="/subjects/">Subject index</a><a class="nav-link" href="/search/">Search</a></div><div class="nav-group"><span class="sidebar-label">Subject hubs</span>${collections.map((c) => `<a class="nav-link" href="/collections/${c.id}/">${esc(c.title)}</a>`).join("")}</div><div class="nav-group"><span class="sidebar-label">Sources & evidence</span><a class="nav-link" href="/sources/">Source concordance</a><a class="nav-link" href="/errata/">Source errata</a><a class="nav-link" href="/provenance/">Lean & provenance</a><a class="nav-link" href="/frontier/">Proof frontier</a><a class="nav-link" href="/metrics/">Project metrics</a><a class="nav-link" href="/about/">About</a></div></div></aside><button class="mobile-overlay" id="mobile-overlay" aria-label="Close navigation"></button><main class="main-content" id="main-content" tabindex="-1"><div class="page-grid${rail ? "" : " wide"}"><article class="article"><nav class="breadcrumb" aria-label="Breadcrumb"><a href="/">Library</a><span>›</span><span>${esc(title)}</span></nav>${body}<footer class="footer">Percolation Library · Exposition and formal verification are tracked separately.</footer></article>${rail ? `<aside class="context-rail" aria-label="Page context">${rail}</aside>` : ""}</div></main></div></body></html>`;
}
