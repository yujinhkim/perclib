import test from "node:test";
import assert from "node:assert/strict";
import fs from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { createHash } from "node:crypto";
import { assertionsIn, readArticles } from "../scripts/articles.mjs";
import {
  validateManifest,
  validateReviews,
  validateEvidence,
  statusFor,
  loadEvidence,
  evidencePanel,
} from "../src/manifest.mjs";
import { build } from "../src/build.mjs";
import { renderMath } from "../src/render.mjs";
const assertions = assertionsIn(await readArticles());
const sha = "a".repeat(40),
  checksum = "b".repeat(64),
  runUrl = "https://github.com/tomhutchcroft/lrp/actions/runs/123";
function fixture() {
  const manifest = {
    schema: "perclib-manifest-v1",
    commit: sha,
    ci_run: runUrl,
    assertions: assertions.map((a) => ({
      ...a,
      declarations: [],
      proof_status: "unformalised",
    })),
  };
  const entry = manifest.assertions.find((a) => a.tag === "53Z9");
  Object.assign(entry, {
    proof_status: "proved",
    declarations: [
      {
        name: "Fixture.example",
        kind: "theorem",
        type: "True",
        file: "PercLib/Fixture.lean",
        line: 7,
      },
    ],
    statement: "True -- synthetic fixture, not a mathematical correspondence",
    axioms: [],
    inputs: [],
    fingerprint: { schema: "perclib-statement-v1", sha256: checksum },
    dependencies: { statement: ["YFF7"], proof: ["5C44"] },
  });
  const bytes = Buffer.from(JSON.stringify(manifest));
  const receipt = {
    schema: "perclib-artifact-receipt-v1",
    repository: "tomhutchcroft/lrp",
    manifest_sha256: createHash("sha256").update(bytes).digest("hex"),
    archive_sha256: checksum,
    artifact: {
      id: 123,
      expired: false,
      digest: "sha256:" + checksum,
      workflow_run: { id: 123, head_sha: "c".repeat(40) },
    },
    run: {
      id: 123,
      head_sha: "c".repeat(40),
      status: "completed",
      conclusion: "success",
      html_url: runUrl,
    },
  };
  const review = {
    tag: "53Z9",
    fingerprint: { ...entry.fingerprint },
    reviewer: "Fixture reviewer (not a real review)",
    date: "2026-11-14",
    url: "https://github.com/tomhutchcroft/lrp/pull/1#fixture",
  };
  return { manifest, entry, bytes, receipt, review };
}
test("status and fingerprint join distinguish reviewed statements, proofs, debts and stale reviews", () => {
  const { entry, review } = fixture();
  assert.equal(statusFor(entry, []).status, "proved");
  entry.proof_status = "statement-only";
  assert.equal(statusFor(entry, []).status, null);
  assert.equal(statusFor(entry, [review]).status, "stated");
  entry.fingerprint = { ...entry.fingerprint, sha256: "c".repeat(64) };
  assert.deepEqual(statusFor(entry, [review]), {
    status: null,
    reviewState: "stale",
    reviews: [review],
  });
  entry.proof_status = "proved-modulo";
  entry.inputs = ["Fixture.LiteratureInput"];
  assert.equal(statusFor(entry, [review]).status, "proved-modulo");
});
test("schema, catalog coverage, dependencies and axiom constraints fail closed", () => {
  const mutate = (fn) => {
    const { manifest, entry } = fixture();
    fn(manifest, entry);
    assert.throws(() => validateManifest(manifest, assertions));
  };
  validateManifest(fixture().manifest, assertions);
  mutate((m) => m.assertions.pop());
  mutate((m) => m.assertions.push(m.assertions[0]));
  mutate((m, e) => (e.tag = "ZZZZ"));
  mutate((m, e) => (e.axioms = ["sorryAx"]));
  mutate((m, e) => (e.inputs = ["Fixture.Input"]));
  mutate((m, e) => (e.proof_status = "proved-modulo"));
  mutate((m, e) => (e.dependencies.proof = ["ZZZZ"]));
  mutate((m, e) => (e.declarations[0].file = "../secrets"));
  mutate((m, e) => (e.declarations[0].line = 0));
  mutate((m, e) => (e.proof_status = "unformalised"));
  mutate((m) => (m.schema = "unknown"));
});
test("evidence binds exact manifest bytes, artifact digest and successful run, allowing PR merge checkout", () => {
  const { manifest, bytes, receipt } = fixture();
  assert.equal(validateEvidence(receipt, manifest, bytes).commit, sha);
  assert.notEqual(manifest.commit, receipt.run.head_sha);
  assert.throws(
    () => validateEvidence(receipt, manifest, Buffer.from("{}")),
    /bytes/,
  );
  for (const mutate of [
    (r) => (r.run.conclusion = "failure"),
    (r) => (r.run.status = "in_progress"),
    (r) => (r.artifact.workflow_run.id = 999),
    (r) => (r.artifact.workflow_run.head_sha = "d".repeat(40)),
    (r) => (r.archive_sha256 = "d".repeat(64)),
  ]) {
    const r = structuredClone(receipt);
    mutate(r);
    assert.throws(() => validateEvidence(r, manifest, bytes));
  }
});
test("review records reject invalid dates, duplicate records and unknown tags", () => {
  const { review } = fixture();
  validateReviews(
    { schema: "perclib-reviews-v1", reviews: [review] },
    assertions,
  );
  for (const bad of [
    { ...review, date: "2026-02-30" },
    { ...review, tag: "ZZZZ" },
    { ...review, url: "javascript:alert(1)" },
  ])
    assert.throws(() =>
      validateReviews(
        { schema: "perclib-reviews-v1", reviews: [bad] },
        assertions,
      ),
    );
  assert.throws(() =>
    validateReviews(
      { schema: "perclib-reviews-v1", reviews: [review, review] },
      assertions,
    ),
  );
});
test("rendering preserves literal Lean text, separates dependency axes and never invents a source line", () => {
  const { manifest, entry, review } = fixture();
  entry.statement = "<script>alert(1)</script> -- $not_math$";
  entry.declarations[0].line = null;
  const panel = evidencePanel([assertions.find((a) => a.tag === "53Z9")], {
    entries: validateManifest(manifest, assertions),
    reviews: [review],
    provenance: { repository: "tomhutchcroft/lrp", commit: sha, runUrl },
    docgenBase: "https://example.org/api/",
  });
  assert.ok(panel.includes("Statement dependencies"));
  assert.ok(panel.includes("Proof dependencies"));
  assert.ok(panel.includes("/tag/YFF7/"));
  assert.ok(panel.includes("/tag/5C44/"));
  assert.ok(panel.includes("&lt;script&gt;"));
  assert.ok(!panel.includes("<script>"));
  assert.ok(!panel.includes("#Lnull"));
  assert.ok(panel.includes("Fixture.html#Fixture.example"));
  assert.ok(renderMath(panel).includes("$not_math$"));
});
test("artifact/review integration builds a real static page and marks changed-definition review stale", async () => {
  const temp = await fs.mkdtemp(path.join(os.tmpdir(), "wiki-evidence-"));
  const { manifest, bytes, receipt, review } = fixture();
  try {
    const manifestPath = path.join(temp, "manifest.json"),
      receiptPath = path.join(temp, "receipt.json"),
      reviewsPath = path.join(temp, "reviews.json");
    await fs.writeFile(manifestPath, bytes);
    await fs.writeFile(receiptPath, JSON.stringify(receipt));
    review.fingerprint.sha256 = "e".repeat(64);
    await fs.writeFile(
      reviewsPath,
      JSON.stringify({ schema: "perclib-reviews-v1", reviews: [review] }),
    );
    const source = JSON.parse(
      await fs.readFile(
        new URL("../src/content/catalog.json", import.meta.url),
        "utf8",
      ),
    ).sources.find((s) => s.id === "notes");
    const occurrencesPath = path.join(temp, "occurs-in.json");
    await fs.writeFile(
      occurrencesPath,
      JSON.stringify({
        schema: "perclib-occurs-in-v1",
        occurrences: [
          {
            source: source.id,
            tag: "53Z9",
            source_url: source.url,
            edition: source.edition,
            locator: "SYNTHETIC SOURCE LOCATOR",
            relationship: "generalization",
            note: "TEST ONLY: not a source fidelity claim.",
          },
        ],
      }),
    );
    const options = {
      occurrencesPath,
      manifestPath,
      receiptPath,
      reviewsPath,
      docgenBase: "https://example.org/api/",
      docgenCommit: manifest.commit,
    };
    const files = await build(path.join(temp, "dist"), options);
    for (const route of [
      "sources/index.html",
      "sources/notes/index.html",
      "articles/subcritical-bound/index.html",
    ]) {
      const page = files.get(route);
      assert.ok(page.includes("SYNTHETIC SOURCE LOCATOR"));
      assert.ok(page.includes("Wiki/Lean correspondence review: stale"));
    }
    assert.ok(
      !files
        .get("sources/grimmett/index.html")
        .includes("SYNTHETIC SOURCE LOCATOR"),
    );
    const errata = files.get("errata/notes/index.html");
    assert.ok(errata.includes("Consequences for Lean"));
    assert.ok(errata.includes("Formal status: unformalised"));
    assert.ok(errata.includes("Editorial status: provisional"));
    assert.ok(errata.includes(runUrl));
    assert.ok(errata.includes(sha));
    assert.ok(errata.includes('/articles/ghost-fields/#formal-8B62'));
    const html = files.get("articles/subcritical-bound/index.html");
    assert.ok(html.includes("Correspondence review stale"));
    assert.ok(html.includes("synthetic fixture"));
    assert.ok(html.includes(runUrl));
    assert.ok(html.includes(sha));
    assert.ok(html.includes("Fixture.html#Fixture.example"));
    assert.ok(!html.includes("Correspondence reviewed</p>"));
    await assert.rejects(
      loadEvidence(assertions, { ...options, docgenCommit: "f".repeat(40) }),
      /exact manifest commit/,
    );
    await assert.rejects(
      loadEvidence(assertions, { ...options, receiptPath: "" }),
      /requires/,
    );
    const absent = await loadEvidence(assertions, {
      manifestPath: "",
      receiptPath: "",
      reviewsPath,
    });
    assert.ok(
      evidencePanel(assertions, absent).includes("status is unavailable"),
    );
  } finally {
    await fs.rm(temp, { recursive: true, force: true });
  }
});
