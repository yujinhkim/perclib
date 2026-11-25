import fs from "node:fs/promises";
import path from "node:path";
import {esc, heading} from "./render.mjs";
import {statusFor} from "./manifest.mjs";

const slug = /^[a-z0-9]+(?:-[a-z0-9]+)*$/;
const https = (value) => {
  try { const u = new URL(value); return u.protocol === "https:" && !u.username && !u.password; }
  catch { return false; }
};
export function validateErrata(data, sources, assertions) {
  if (data?.schema !== "perclib-source-errata-v1" ||
      !sources.some((s) => s.id === data.source) || !Array.isArray(data.entries))
    throw Error("Errata: unknown source or invalid schema");
  const tags = new Map(assertions.map((a) => [a.tag, a.article]));
  const seen = new Set();
  for (const row of data.entries) {
    if (typeof row.id !== "string" || !slug.test(row.id) || seen.has(row.id) ||
        !["provisional", "confirmed", "withdrawn"].includes(row.status) ||
        !["title", "locator", "claim", "problem", "correction", "leanImpact"].every((k) => typeof row[k] === "string" && row[k].trim()) ||
        Object.keys(row).some((k) => !["id", "title", "status", "locator", "claim", "problem", "correction", "leanImpact", "tags", "issues", "confirmationUrl", "withdrawalReason", "withdrawalUrl"].includes(k)) ||
        !Array.isArray(row.tags) || !row.tags.length || row.tags.some((t) => !tags.has(t)) ||
        new Set(row.tags).size !== row.tags.length ||
        !Array.isArray(row.issues) || !row.issues.length || row.issues.some((u) => !https(u)))
      throw Error("Errata: invalid entry, tag or issue");
    if (row.status === "confirmed" && !https(row.confirmationUrl))
      throw Error("Errata: confirmation requires Tom's recorded confirmation");
    if (row.status === "withdrawn" &&
        (!row.withdrawalReason?.trim() || !https(row.withdrawalUrl)))
      throw Error("Errata: withdrawal requires a reason and record");
    seen.add(row.id);
  }
  return data;
}
export async function loadErrata(root, sources, assertions) {
  const directory = path.join(root, "errata");
  let names;
  try { names = (await fs.readdir(directory)).filter((n) => n.endsWith(".json")).sort(); }
  catch (error) { if (error.code === "ENOENT") return []; throw error; }
  return Promise.all(names.map(async (name) => {
    const data = validateErrata(JSON.parse(await fs.readFile(path.join(directory, name), "utf8")), sources, assertions);
    if (name !== `${data.source}.json`) throw Error("Errata: filename must match source");
    return data;
  }));
}
export const erratumUrl = (source, id) => `/errata/${source}/#${id}`;
export const errataNotice = "Provisional entries are reported source discrepancies awaiting Tom Hutchcroft's confirmation. Their editorial status is separate from formal proof status. An unresolved correction is not a completed theorem.";
export function errataPage(data, source, assertions, evidence) {
  const byTag = new Map(assertions.map((a) => [a.tag, a]));
  const snapshot = evidence.provenance
    ? `<p>Compiled snapshot: <a href="https://github.com/${esc(evidence.provenance.repository)}/commit/${esc(evidence.provenance.commit)}"><code>${esc(evidence.provenance.commit)}</code></a> · <a href="${esc(evidence.provenance.runUrl)}">Successful CI run</a>. Proof status describes the compiled statement; its correspondence to the wiki is reviewed separately.</p>`
    : "<p>No compiled manifest is supplied with this edition. Formal status is unavailable; issue resolutions and prose proofs do not supply compiled evidence.</p>";
  const formal = (tag) => {
    const assertion = byTag.get(tag);
    const entry = evidence.entries?.get(tag);
    const result = entry ? statusFor(entry, evidence.reviews) : null;
    const review = result && entry.proof_status !== "unformalised"
      ? ` Wiki/Lean correspondence review: ${esc(result.reviewState)}.` : "";
    return `<li><a href="/tag/${tag}/">${tag} · ${esc(assertion.title)}</a><p>Formal status: ${esc(result ? (result.status ?? "Compiled statement; correspondence pending") : "unavailable")}.${review} <a href="/articles/${assertion.article}/#${entry ? `formal-${tag}` : "formal-evidence"}">Statement and Lean evidence</a>.</p>` +
      (entry?.proof_status === "proved-modulo"
        ? `<p>Named inputs still to discharge:</p><ul>${entry.inputs.map((input) => `<li><code>${esc(input)}</code></li>`).join("")}</ul>` : "") + "</li>";
  };
  return heading(`${source.shortName}: errata`, errataNotice) +
    `<p><a href="${esc(source.url)}">${esc(source.title)}</a> · ${esc(source.edition)}</p>` +
    snapshot +
    data.entries.map((row) => {
      const start = `<section class="article-section" id="${row.id}"><h2>${esc(row.title)}</h2><p><strong>Editorial status: ${row.status}.</strong></p>`;
      if (row.status === "withdrawn") return start + `<p>This entry has been withdrawn. ${esc(row.withdrawalReason)}</p><p><a href="${esc(row.withdrawalUrl)}">Withdrawal record</a></p></section>`;
      return start +
        `<p><strong>Source locator:</strong> ${esc(row.locator)}</p>` +
        `<h3>Source claim</h3><p>${esc(row.claim)}</p><h3>Reported problem</h3><p>${esc(row.problem)}</p>` +
        `<h3>Correction and remaining scope</h3><p>${esc(row.correction)}</p>` +
        `<h3>Consequences for Lean</h3><p>${esc(row.leanImpact)}</p>` +
        `<ul>${row.tags.map(formal).join("")}</ul>` +
        `<p>${row.issues.map((u, i) => `<a href="${esc(u)}">Issue record${row.issues.length > 1 ? ` ${i + 1}` : ""}</a>`).join(" · ")}` +
        (row.status === "confirmed" ? ` · <a href="${esc(row.confirmationUrl)}">Tom's confirmation</a>` : " · Awaiting Tom's confirmation") +
        "</p></section>";
    }).join("");
}
export function articleErrata(article, errata, assertions) {
  const owned = new Set(assertions.filter((a) => a.article === article).map((a) => a.tag));
  const rows = errata.flatMap((source) => source.entries.filter((row) => row.tags.some((t) => owned.has(t))).map((row) => ({source: source.source, ...row})));
  if (!rows.length) return "";
  return '<section class="running-context"><h2>Source errata</h2><p>These source diagnoses have the editorial status shown below; this does not certify a formal proof.</p><ul>' +
    rows.map((row) => `<li><a href="${erratumUrl(row.source, row.id)}">${esc(row.title)}</a> — ${row.status}${row.status === "provisional" ? "; awaiting Tom's confirmation" : ""}.</li>`).join("") + "</ul></section>";
}
