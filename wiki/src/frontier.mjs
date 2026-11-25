import { esc, heading } from "./render.mjs";
import { statusFor } from "./manifest.mjs";

// An absent record means unknown; an explicit empty list means no prerequisites.
export function validateProofUses(data, assertions) {
  if (
    data?.schema !== "perclib-proof-uses-v1" ||
    !Array.isArray(data.assertions)
  )
    throw Error("Frontier: invalid proof-uses schema");
  const tags = new Set(assertions.map((a) => a.tag)),
    records = new Map();
  for (const row of data.assertions) {
    if (
      !tags.has(row.tag) ||
      records.has(row.tag) ||
      !Array.isArray(row.proof_uses) ||
      row.proof_uses.some((t) => !tags.has(t) || t === row.tag) ||
      new Set(row.proof_uses).size !== row.proof_uses.length ||
      typeof row.reason !== "string" ||
      !row.reason.trim()
    )
      throw Error(
        `Frontier: invalid or duplicate prerequisite record ${row.tag}`,
      );
    records.set(row.tag, row);
  }
  return records;
}

export function computeFrontier(assertions, evidence, authored) {
  const result = { ready: [], blocked: [], unknown: [], proved: [] };
  for (const a of [...assertions].sort((a, b) => a.tag.localeCompare(b.tag))) {
    const entry = evidence.entries?.get(a.tag);
    if (!entry) {
      result.unknown.push({ ...a, reason: "No compiled evidence supplied." });
      continue;
    }
    // D-14: authored proof_uses cease to apply once the assertion is proved.
    if (entry.proof_status === "proved") {
      result.proved.push(a);
      continue;
    }
    const record = authored.get(a.tag);
    if (!record) {
      result.unknown.push({
        ...a,
        reason: "Proof prerequisites have not been recorded.",
      });
      continue;
    }
    const statement = entry.dependencies?.statement ?? [],
      extracted = entry.dependencies?.proof ?? [];
    const prerequisites = [
      ...new Set([...statement, ...extracted, ...record.proof_uses]),
    ].sort();
    const blockedBy = prerequisites.filter(
      (t) => evidence.entries.get(t)?.proof_status !== "proved",
    );
    const row = {
      ...a,
      prerequisites,
      blockedBy,
      statement,
      extracted,
      authored: record.proof_uses,
      reason: record.reason,
      inputs: entry.inputs ?? [],
      ...statusFor(entry, evidence.reviews),
    };
    result[blockedBy.length ? "blocked" : "ready"].push(row);
  }
  return result;
}

export function frontierPage(assertions, evidence, authored) {
  const f = computeFrontier(assertions, evidence, authored);
  const tags = (ts) =>
    ts.length
      ? ts.map((t) => `<a href="/tag/${t}/">${t}</a>`).join(", ")
      : "None";
  const list = (rows) =>
    rows.length
      ? "<ul>" +
        rows
          .map(
            (r) =>
              `<li><p><a href="/tag/${r.tag}/">${r.tag} · ${esc(r.title)}</a></p>${r.prerequisites ? `<p>Statement prerequisites: ${tags(r.statement)}. Extracted proof prerequisites: ${tags(r.extracted)}. Authored proof prerequisites: ${tags(r.authored)}.</p><p>${esc(r.reason)}</p>${r.blockedBy.length ? `<p>Not yet proved: ${tags(r.blockedBy)}.</p>` : ""}<p>Status: ${esc(r.status ?? "Compiled statement; correspondence pending")}. Correspondence review: ${esc(r.reviewState)}.</p>${r.inputs.length ? `<p>Named inputs still to discharge: ${r.inputs.map(esc).join(", ")}.</p>` : ""}` : `<p>${esc(r.reason)}</p>`}</li>`,
          )
          .join("") +
        "</ul>"
      : "<p>None in this snapshot.</p>";
  return (
    heading(
      "Proof frontier",
      "Unproved assertions whose recorded prerequisites are all proved.",
    ) +
    (evidence.provenance
      ? `<p>Computed from <a href="${esc(evidence.provenance.runUrl)}">successful CI</a> at compiled commit <code>${esc(evidence.provenance.commit)}</code>.</p>`
      : "<p>No compiled manifest is supplied. The proof frontier is unavailable.</p>") +
    "<p>Readiness concerns prerequisites, not assignment or mathematical correspondence. Check the displayed correspondence review before starting proof work. Missing prerequisite records are kept separate from an explicitly empty list.</p>" +
    `<section class="article-section" id="ready"><h2>Ready by prerequisites (${f.ready.length})</h2>${list(f.ready)}</section>` +
    `<section class="article-section" id="blocked"><h2>Waiting for proofs (${f.blocked.length})</h2>${list(f.blocked)}</section>` +
    `<section class="article-section" id="unknown"><h2>Insufficient evidence (${f.unknown.length})</h2>${list(f.unknown)}</section>` +
    `<p>${f.proved.length} proved assertions are omitted from the frontier. Authored prerequisite records for those assertions are ignored.</p>`
  );
}
