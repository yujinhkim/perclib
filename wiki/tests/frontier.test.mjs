import test from "node:test";
import assert from "node:assert/strict";
import {
  validateProofUses,
  computeFrontier,
  frontierPage,
} from "../src/frontier.mjs";
const assertions = ["AAAA", "BBBB", "CCCC", "DDDD"].map((tag) => ({
  tag,
  title: tag,
}));
const data = (rows) => ({
  schema: "perclib-proof-uses-v1",
  assertions: rows.map(([tag, proof_uses]) => ({
    tag,
    proof_uses,
    reason: "Test prerequisite argument",
  })),
});
const evidence = () => ({
  entries: new Map(
    assertions.map((a) => [
      a.tag,
      { tag: a.tag, proof_status: "unformalised" },
    ]),
  ),
  reviews: [],
});
const proof = (e, t) =>
  e.entries.set(t, {
    tag: t,
    proof_status: "proved",
    fingerprint: { schema: "perclib-statement-v1", sha256: "a".repeat(64) },
  });
test("unknown evidence and missing records never masquerade as ready leaves", () => {
  const authored = validateProofUses(data([["AAAA", []]]), assertions);
  assert.equal(
    computeFrontier(assertions, { reviews: [] }, authored).unknown.length,
    4,
  );
  const f = computeFrontier(assertions, evidence(), authored);
  assert.deepEqual(
    f.ready.map((a) => a.tag),
    ["AAAA"],
  );
  assert.equal(f.unknown.length, 3);
});
test("frontier combines both extracted axes and authored prerequisites; modulo is not proved", () => {
  const e = evidence();
  proof(e, "BBBB");
  proof(e, "CCCC");
  e.entries.set("AAAA", {
    tag: "AAAA",
    proof_status: "proved-modulo",
    inputs: ["Input.remaining"],
    dependencies: { statement: ["BBBB"], proof: ["CCCC"] },
    fingerprint: { schema: "perclib-statement-v1", sha256: "a".repeat(64) },
  });
  const authored = validateProofUses(
    data([
      ["AAAA", ["DDDD"]],
      ["DDDD", ["AAAA"]],
    ]),
    assertions,
  );
  let f = computeFrontier(assertions, e, authored);
  assert.equal(f.ready.length, 0);
  assert.deepEqual(f.blocked[0].blockedBy, ["DDDD"]);
  assert.deepEqual(f.blocked[1].blockedBy, ["AAAA"]);
  proof(e, "DDDD");
  f = computeFrontier(assertions, e, authored);
  assert.deepEqual(f.ready[0].prerequisites, ["BBBB", "CCCC", "DDDD"]);
  assert.deepEqual(f.ready[0].inputs, ["Input.remaining"]);
  proof(e, "AAAA");
  f = computeFrontier(assertions, e, authored);
  assert.equal(f.ready.length, 0);
  assert.equal(f.proved.length, 4);
});
test("records reject unknown, duplicate and self prerequisites", () => {
  for (const rows of [
    [["AAAA", ["ZZZZ"]]],
    [["AAAA", ["AAAA"]]],
    [["AAAA", ["BBBB", "BBBB"]]],
    [
      ["AAAA", []],
      ["AAAA", []],
    ],
  ])
    assert.throws(() => validateProofUses(data(rows), assertions));
  assert.throws(() =>
    validateProofUses({ schema: "other", assertions: [] }, assertions),
  );
});
test("frontier displays missing evidence, review state and exact provenance without certifying correspondence", () => {
  const authored = validateProofUses(data([["AAAA", []]]), assertions);
  assert.match(
    frontierPage(assertions, { reviews: [] }, authored),
    /frontier is unavailable/,
  );
  const e = evidence();
  e.provenance = {
    runUrl: "https://github.com/tomhutchcroft/lrp/actions/runs/123",
    commit: "a".repeat(40),
  };
  const html = frontierPage(assertions, e, authored);
  assert.match(html, /Ready by prerequisites \(1\)/);
  assert.match(html, /Correspondence review: missing/);
  assert.match(html, /a{40}/);
  assert.match(html, /href="\/tag\/AAAA\/"/);
});
