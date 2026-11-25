import fs from "node:fs/promises";
import { createHash } from "node:crypto";
import { esc } from "./render.mjs";
const allowedAxioms = new Set(["propext", "Classical.choice", "Quot.sound"]);
const sha = /^[a-f0-9]{40}$/;
const hash = /^[a-f0-9]{64}$/;
const fail = (message) => {
  throw Error(`Manifest: ${message}`);
};
const nonempty = (value) =>
  typeof value === "string" && value.trim().length > 0;
const stringList = (value) =>
  Array.isArray(value) &&
  value.every(nonempty) &&
  new Set(value).size === value.length;
const fingerprint = (value) =>
  value && value.schema === "perclib-statement-v1" && hash.test(value.sha256);
const sameFingerprint = (a, b) =>
  a.schema === b.schema && a.sha256 === b.sha256;

export function validateManifest(manifest, assertions) {
  if (
    manifest?.schema !== "perclib-manifest-v1" ||
    !sha.test(manifest.commit) ||
    !Array.isArray(manifest.assertions)
  )
    fail("unsupported schema or invalid commit/assertions");
  const local = new Map(assertions.map((a) => [a.tag, a]));
  const entries = new Map();
  for (const entry of manifest.assertions) {
    if (!local.has(entry.tag) || entries.has(entry.tag))
      fail(`unknown or duplicate tag ${entry.tag}`);
    if (!Array.isArray(entry.declarations))
      fail(`missing declarations for ${entry.tag}`);
    if (
      !["unformalised", "statement-only", "proved-modulo", "proved"].includes(
        entry.proof_status,
      )
    )
      fail(`unsupported proof status for ${entry.tag}`);
    if (entry.proof_status === "unformalised") {
      if (entry.declarations.length || entry.statement || entry.fingerprint)
        fail(`unformalised entry carries compiled data: ${entry.tag}`);
    } else {
      if (
        !entry.declarations.length ||
        !nonempty(entry.statement) ||
        !fingerprint(entry.fingerprint)
      )
        fail(`incomplete compiled statement for ${entry.tag}`);
      if (
        !stringList(entry.axioms) ||
        entry.axioms.some((a) => !allowedAxioms.has(a))
      )
        fail(`invalid axioms for ${entry.tag}`);
      if (!stringList(entry.inputs))
        fail(`invalid input debts for ${entry.tag}`);
      if (entry.proof_status === "proved" && entry.inputs.length)
        fail(`proved entry has input debts: ${entry.tag}`);
      if (entry.proof_status === "proved-modulo" && !entry.inputs.length)
        fail(`proved-modulo entry has no debts: ${entry.tag}`);
      for (const d of entry.declarations) {
        if (
          !nonempty(d.name) ||
          !nonempty(d.type) ||
          ![
            "definition",
            "theorem",
            "opaque",
            "inductive",
            "constructor",
            "recursor",
            "quotient",
          ].includes(d.kind) ||
          typeof d.file !== "string" ||
          !/^PercLib\/(?:[A-Za-z0-9_-]+\/)*[A-Za-z0-9_-]+\.lean$/.test(
            d.file,
          ) ||
          !(d.line === null || (Number.isSafeInteger(d.line) && d.line > 0))
        )
          fail(`invalid declaration/source location for ${entry.tag}`);
      }
      for (const axis of ["statement", "proof"]) {
        if (
          !stringList(entry.dependencies?.[axis]) ||
          entry.dependencies[axis].some((t) => !local.has(t) || t === entry.tag)
        )
          fail(`invalid ${axis} dependencies for ${entry.tag}`);
      }
    }
    entries.set(entry.tag, entry);
  }
  if (entries.size !== local.size)
    fail("artifact does not cover the current assertion catalog");
  return entries;
}

export function validateReviews(reviews, assertions) {
  if (
    reviews?.schema !== "perclib-reviews-v1" ||
    !Array.isArray(reviews.reviews)
  )
    fail("invalid review record schema");
  const tags = new Set(assertions.map((a) => a.tag)),
    seen = new Set();
  for (const r of reviews.reviews) {
    if (
      !tags.has(r.tag) ||
      !fingerprint(r.fingerprint) ||
      !nonempty(r.reviewer) ||
      !/^\d{4}-\d{2}-\d{2}$/.test(r.date) ||
      new Date(r.date).toISOString().slice(0, 10) !== r.date
    )
      fail("invalid correspondence review");
    const key = [
      r.tag,
      r.fingerprint.schema,
      r.fingerprint.sha256,
      r.reviewer,
      r.date,
    ].join(":");
    if (seen.has(key)) fail("duplicate correspondence review");
    seen.add(key);
    if (
      !/^https:\/\/github\.com\/[^/]+\/[^/]+\/(?:issues|pull)\/\d+(?:#[^\s]*)?$/.test(
        r.url,
      )
    )
      fail("review needs a GitHub discussion/review URL");
  }
  return reviews.reviews;
}

export function validateEvidence(receipt, manifest, bytes) {
  if (
    receipt?.schema !== "perclib-artifact-receipt-v1" ||
    receipt.manifest_sha256 !== createHash("sha256").update(bytes).digest("hex")
  )
    fail("artifact receipt does not match manifest bytes");
  if (!/^tomhutchcroft\/(?:lrp|perclib)$/.test(receipt.repository))
    fail("unexpected evidence repository");
  const { run, artifact } = receipt;
  const runUrl = `https://github.com/${receipt.repository}/actions/runs/${run?.id}`;
  if (
    !Number.isSafeInteger(run?.id) ||
    run.status !== "completed" ||
    run.conclusion !== "success" ||
    run.html_url !== runUrl ||
    manifest.ci_run !== runUrl ||
    !sha.test(run.head_sha)
  )
    fail("artifact is not from a successful matching CI run");
  if (
    !Number.isSafeInteger(artifact?.id) ||
    artifact.workflow_run?.id !== run.id ||
    artifact.workflow_run?.head_sha !== run.head_sha ||
    artifact.expired !== false
  )
    fail("artifact/run association mismatch");
  if (
    !/^sha256:[a-f0-9]{64}$/.test(artifact.digest) ||
    receipt.archive_sha256 !== artifact.digest.slice(7)
  )
    fail("archive digest mismatch");
  return {
    repository: receipt.repository,
    runUrl,
    commit: manifest.commit,
    artifactId: artifact.id,
  };
}

export function statusFor(entry, reviews) {
  const history = reviews.filter((r) => r.tag === entry.tag);
  const matching = entry.fingerprint
    ? history.filter((r) => sameFingerprint(r.fingerprint, entry.fingerprint))
    : [];
  const reviewState = matching.length
    ? "current"
    : history.length
      ? "stale"
      : "missing";
  // "stated" specifically requires a matching correspondence review (D-4).
  const status =
    entry.proof_status === "statement-only"
      ? matching.length
        ? "stated"
        : null
      : entry.proof_status;
  return { status, reviewState, reviews: matching.length ? matching : history };
}

export async function loadEvidence(
  assertions,
  {
    manifestPath = process.env.WIKI_MANIFEST,
    receiptPath = process.env.WIKI_MANIFEST_RECEIPT,
    reviewsPath,
    docgenBase = process.env.WIKI_DOCGEN_BASE,
    docgenCommit = process.env.WIKI_DOCGEN_COMMIT,
  } = {},
) {
  const reviews = validateReviews(
    JSON.parse(await fs.readFile(reviewsPath, "utf8")),
    assertions,
  );
  if (!manifestPath) {
    if (receiptPath) fail("receipt supplied without manifest");
    return { entries: null, reviews, provenance: null, docgenBase: null };
  }
  if (!receiptPath) fail("manifest requires a successful artifact receipt");
  const bytes = await fs.readFile(manifestPath);
  const manifest = JSON.parse(bytes);
  const entries = validateManifest(manifest, assertions);
  const provenance = validateEvidence(
    JSON.parse(await fs.readFile(receiptPath, "utf8")),
    manifest,
    bytes,
  );
  if (docgenBase) {
    const url = new URL(docgenBase);
    if (
      url.protocol !== "https:" ||
      url.username ||
      url.password ||
      url.search ||
      url.hash ||
      docgenCommit !== manifest.commit
    )
      fail("doc-gen4 base requires HTTPS and the exact manifest commit");
    docgenBase = url.href.endsWith("/") ? url.href : url.href + "/";
  }
  return { entries, reviews, provenance, docgenBase };
}

export function evidencePanel(assertions, evidence) {
  if (!evidence.entries)
    return '<section class="article-section" id="formal-evidence"><h2>Formal evidence</h2><p>No compiled manifest is supplied with this edition. Formal status is unavailable.</p></section>';
  const { repository, commit, runUrl } = evidence.provenance;
  const links = (tags) =>
    tags.length
      ? "<ul>" +
        tags.map((t) => `<li><a href="/tag/${t}/">${t}</a></li>`).join("") +
        "</ul>"
      : "<p>No tagged dependencies recorded on this axis.</p>";
  return `<section class="article-section" id="formal-evidence"><h2>Formal evidence</h2><p>Compiled snapshot <a href="https://github.com/${repository}/commit/${commit}"><code>${commit}</code></a> · <a href="${runUrl}">Successful CI run</a>. A proof status describes the Lean statement; correspondence to the prose is reviewed separately.</p>${assertions
    .map((a) => {
      const e = evidence.entries.get(a.tag),
        result = statusFor(e, evidence.reviews);
      const reviewText =
        result.reviewState === "current"
          ? "Correspondence reviewed"
          : result.reviewState === "stale"
            ? "Correspondence review stale"
            : "Correspondence not reviewed";
      return `<details class="formal-assertion" id="formal-${a.tag}"><summary><a href="#${a.anchor}">${a.tag}</a> · ${esc(a.title)} <span class="status">${result.status ?? "Compiled statement; correspondence pending"}</span></summary><p>${reviewText}</p>${result.reviews.map((r) => `<p><a href="${esc(r.url)}">${esc(r.reviewer)} · ${esc(r.date)}</a>${result.reviewState === "stale" ? " — fingerprint no longer matches" : ""}</p>`).join("")}${
        e.proof_status === "unformalised"
          ? "<p>No Lean declaration is attached to this tag in the supplied artifact.</p>"
          : `<h3>Compiled statement</h3><pre class="lean-statement"><code>${esc(e.statement)}</code></pre><p>Fingerprint: <code>${esc(e.fingerprint.schema)}:${e.fingerprint.sha256}</code></p><ul>${e.declarations
              .map((d) => {
                const source =
                  `https://github.com/${repository}/blob/${commit}/${d.file}` +
                  (d.line === null ? "" : `#L${d.line}`);
                const api = evidence.docgenBase
                  ? new URL(
                      d.file.replace(/\.lean$/, ".html"),
                      evidence.docgenBase,
                    ).href +
                    "#" +
                    encodeURIComponent(d.name)
                  : null;
                return `<li><code>${esc(d.name)}</code> · <a href="${source}">Lean source${d.line === null ? " (line unavailable)" : ":" + d.line}</a>${api ? ` · <a href="${esc(api)}">API documentation</a>` : ""}</li>`;
              })
              .join(
                "",
              )}</ul>${evidence.docgenBase ? "" : "<p>API documentation for this compiled revision has not been supplied.</p>"}${e.inputs.length ? `<h3>Named literature inputs</h3><ul>${e.inputs.map((i) => `<li><code>${esc(i)}</code></li>`).join("")}</ul>` : ""}<p>Axioms: ${e.axioms.length ? e.axioms.map(esc).join(", ") : "none"}.</p><h3>Statement dependencies</h3>${links(e.dependencies.statement)}<h3>Proof dependencies</h3>${links(e.dependencies.proof)}`
      }</details>`;
    })
    .join("")}</section>`;
}
