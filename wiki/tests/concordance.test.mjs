import test from "node:test";
import assert from "node:assert/strict";
import { validateOccurrences, concordancePanel } from "../src/concordance.mjs";
const sources = [
    {
      id: "notes",
      shortName: "Notes",
      url: "https://example.org/v1",
      edition: "Version 1",
    },
  ],
  assertions = [{ tag: "AAAA", title: "A < B" }];
const occurrence = {
  source: "notes",
  tag: "AAAA",
  source_url: sources[0].url,
  edition: "Version 1",
  locator: "Theorem 2, page 3",
  relationship: "generalization",
  note: "Adds the zero-row case; <script> is literal text.",
};
const validate = (rows) =>
  validateOccurrences(
    { schema: "perclib-occurs-in-v1", occurrences: rows },
    sources,
    assertions,
  );
test("source occurrence records reject invented status, stale editions and unknown identities", () => {
  assert.equal(validate([occurrence]).length, 1);
  for (const patch of [
    { status: "proved" },
    { tag: "BBBB" },
    { source: "other" },
    { source_url: "javascript:alert(1)" },
    { edition: "Version 2" },
    { relationship: "equivalent" },
    { locator: "" },
  ])
    assert.throws(() => validate([{ ...occurrence, ...patch }]));
  assert.throws(() => validate([occurrence, occurrence]));
  assert.equal(
    validate([occurrence, { ...occurrence, locator: "Corollary 3" }]).length,
    2,
  );
});
test("rendering distinguishes source records from formal evidence and escapes source text", () => {
  const html = concordancePanel(validate([occurrence]), sources, assertions, {
    entries: null,
  });
  assert.match(html, /Formal status: unavailable/);
  assert.match(html, /generalizes the source/);
  assert.match(html, /&lt;script&gt;/);
  assert.ok(!html.includes("<script>"));
  assert.match(html, /href="\/tag\/AAAA\/"/);
  assert.match(
    concordancePanel([], sources, assertions, { entries: null }),
    /No tagged source occurrences/,
  );
});
test("source records do not confer stated status or refresh a changed fingerprint", () => {
  const entry = {
    tag: "AAAA",
    proof_status: "statement-only",
    fingerprint: { schema: "perclib-statement-v1", sha256: "a".repeat(64) },
  };
  const evidence = {
    entries: new Map([["AAAA", entry]]),
    reviews: [
      {
        tag: "AAAA",
        fingerprint: { schema: "perclib-statement-v1", sha256: "b".repeat(64) },
      },
    ],
    provenance: {
      runUrl: "https://github.com/tomhutchcroft/lrp/actions/runs/1",
      commit: "c".repeat(40),
    },
  };
  let html = concordancePanel(
    validate([occurrence]),
    sources,
    assertions,
    evidence,
  );
  assert.match(html, /correspondence pending/);
  assert.match(html, /review: stale/);
  evidence.reviews[0].fingerprint = entry.fingerprint;
  html = concordancePanel(
    validate([occurrence]),
    sources,
    assertions,
    evidence,
  );
  assert.match(html, /Formal status: stated/);
  assert.match(html, /review: current/);
});

test("conditional source occurrences name every outstanding input", () => {
  const evidence = {
    entries: new Map([
      [
        "AAAA",
        {
          tag: "AAAA",
          proof_status: "proved-modulo",
          inputs: ["Fixture.FirstInput", "Fixture.SecondInput<script>"],
          fingerprint: {
            schema: "perclib-statement-v1",
            sha256: "a".repeat(64),
          },
        },
      ],
    ]),
    reviews: [],
    provenance: {
      runUrl: "https://github.com/tomhutchcroft/lrp/actions/runs/1",
      commit: "c".repeat(40),
    },
  };
  const html = concordancePanel(
    validate([occurrence]),
    sources,
    assertions,
    evidence,
  );
  assert.match(html, /Formal status: proved-modulo/);
  assert.match(html, /Named inputs still to discharge/);
  assert.match(html, /Fixture.FirstInput/);
  assert.match(html, /Fixture.SecondInput&lt;script&gt;/);
  assert.ok(!html.includes("<script>"));
});
