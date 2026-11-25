import test from "node:test";
import assert from "node:assert/strict";
import fs from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import {assembleRecords, loadRecords} from "../src/records.mjs";

const catalog = {sources: [{id: "notes"}], collections: [{id: "methods"}]};
const articles = [{id: "alpha"}, {id: "beta"}];
const assertions = [{tag: "AAAA", article: "alpha"}, {tag: "BBBB", article: "beta"}];
const record = (article) => ({schema: "perclib-article-records-v1", article,
  collections: [{collection: "methods", order: 1}],
  sourceOccurrences: [{source: "notes", order: 1, label: article}],
  occursIn: [], proofUses: []});

test("independent article records preserve both contributions without catalog edits", () => {
  const before = structuredClone(catalog), alpha = record("alpha"), beta = record("beta");
  alpha.occursIn.push({order: 0, tag: "AAAA", locator: "A"});
  beta.occursIn.push({order: 1, tag: "BBBB", locator: "B"});
  const merged = assembleRecords(catalog, [beta, alpha], articles, assertions);
  assert.deepEqual(catalog, before);
  assert.deepEqual(merged.collections[0].pages, ["alpha", "beta"]);
  assert.deepEqual(merged.sources[0].occurrences, [{label: "alpha", pageId: "alpha"}, {label: "beta", pageId: "beta"}]);
  assert.deepEqual(merged.occursIn.occurrences.map((r) => r.tag), ["AAAA", "BBBB"]);
});
test("article records reject foreign tags, duplicate owners and missing catalog targets", () => {
  const alpha = record("alpha");
  alpha.proofUses.push({order: 0, tag: "BBBB", proof_uses: [], reason: "wrong owner"});
  assert.throws(() => assembleRecords(catalog, [alpha], articles, assertions), /does not belong/);
  assert.throws(() => assembleRecords(catalog, [record("alpha"), record("alpha")], articles, assertions), /duplicate/);
  const beta = record("beta"); beta.collections[0].collection = "absent";
  assert.throws(() => assembleRecords(catalog, [beta], articles, assertions), /unknown/);
});

test("a merge cannot silently discard a resurrected shared relation file", async () => {
  const root = await fs.mkdtemp(path.join(os.tmpdir(), "wiki-records-"));
  try {
    await fs.mkdir(path.join(root, "relations"));
    await fs.writeFile(path.join(root, "relations/occurs-in.json"), JSON.stringify({
      schema: "perclib-occurs-in-v1", occurrences: [{tag: "AAAA", locator: "new contribution"}],
    }));
    await assert.rejects(loadRecords(root, articles, assertions), /migrate legacy shared file/);
  } finally { await fs.rm(root, {recursive: true, force: true}); }
});
