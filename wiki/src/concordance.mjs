import { esc } from "./render.mjs";
import { statusFor } from "./manifest.mjs";
const relationships = new Map([
  ["source-statement", "Source statement"],
  ["generalization", "Wiki assertion generalizes the source"],
  ["specialization", "Wiki assertion specializes the source"],
  ["definition", "Definition"],
]);
const fields = [
  "source",
  "tag",
  "source_url",
  "edition",
  "locator",
  "relationship",
  "note",
];
export function validateOccurrences(data, sources, assertions) {
  if (
    data?.schema !== "perclib-occurs-in-v1" ||
    !Array.isArray(data.occurrences)
  )
    throw Error("Concordance: invalid schema");
  const catalog = new Map(sources.map((s) => [s.id, s])),
    tags = new Set(assertions.map((a) => a.tag)),
    seen = new Set();
  for (const row of data.occurrences) {
    if (
      !row ||
      Object.keys(row).some((k) => !fields.includes(k)) ||
      fields.some((k) => typeof row[k] !== "string" || !row[k].trim())
    )
      throw Error("Concordance: invalid occurrence fields");
    const source = catalog.get(row.source);
    if (!source || !tags.has(row.tag) || !relationships.has(row.relationship))
      throw Error("Concordance: unknown source, tag or relationship");
    const url = new URL(row.source_url);
    if (
      url.protocol !== "https:" ||
      url.username ||
      url.password ||
      row.source_url !== source.url ||
      row.edition !== source.edition
    )
      throw Error(
        "Concordance: source URL/edition must match the source catalog",
      );
    const key = JSON.stringify([row.source, row.edition, row.tag, row.locator]);
    if (seen.has(key)) throw Error("Concordance: duplicate occurrence");
    seen.add(key);
  }
  return data.occurrences;
}
export function concordancePanel(rows, sources, assertions, evidence) {
  const catalog = new Map(sources.map((s) => [s.id, s])),
    tags = new Map(assertions.map((a) => [a.tag, a]));
  if (!rows.length)
    return '<section class="article-section"><h2>Tagged source occurrences</h2><p>No tagged source occurrences have been recorded for this selection. Editorial reading links are not source-to-assertion correspondences.</p></section>';
  const snapshot = evidence.provenance
    ? `<p>Formal evidence: <a href="${esc(evidence.provenance.runUrl)}">successful CI</a> at compiled commit <code>${esc(evidence.provenance.commit)}</code>.</p>`
    : "<p>No compiled manifest is supplied. Formal status is unavailable.</p>";
  return (
    '<section class="article-section"><h2>Tagged source occurrences</h2><p>These authored records locate source occurrences. A record does not certify source fidelity or a Lean proof; the displayed correspondence review concerns the compiled statement and wiki prose.</p>' +
    snapshot +
    rows
      .map((row) => {
        const entry = evidence.entries?.get(row.tag),
          result = entry ? statusFor(entry, evidence.reviews) : null;
        return `<div class="article-section"><h3><a href="/tag/${row.tag}/">${row.tag} · ${esc(tags.get(row.tag).title)}</a></h3><p><a href="/sources/${esc(row.source)}/">${esc(catalog.get(row.source).shortName)}</a> · <a href="${esc(row.source_url)}">${esc(row.edition)}</a></p><p>${esc(row.locator)}</p><p>${relationships.get(row.relationship)}. ${esc(row.note)}</p><p>Formal status: ${esc(result ? (result.status ?? "Compiled statement; correspondence pending") : "unavailable")}. ${result ? "Wiki/Lean correspondence review: " + esc(result.reviewState) + "." : ""}</p>${entry?.proof_status === "proved-modulo" ? "<p>Named inputs still to discharge:</p><ul>" + entry.inputs.map((input) => "<li><code>" + esc(input) + "</code></li>").join("") + "</ul>" : ""}</div>`;
      })
      .join("") +
    "</section>"
  );
}
