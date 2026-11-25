import test from "node:test";
import assert from "node:assert/strict";
import {validateErrata, errataPage, articleErrata} from "../src/errata.mjs";
const source = {id: "notes", shortName: "Notes", title: "Notes", edition: "Pinned draft", url: "https://example.org/notes"};
const assertions = [{tag: "AAAA", article: "alpha", title: "Affected assertion"}];
const absent = {entries: null, reviews: [], provenance: null};
const fixture = () => ({schema: "perclib-source-errata-v1", source: "notes", entries: [{
  id: "sign", title: "A sign", status: "provisional", locator: "Lemma 1",
  claim: "<script>source</script>", problem: "A missing sign.", correction: "Still unresolved.", leanImpact: "Keep <scope> explicit.",
  tags: ["AAAA"], issues: ["https://github.com/example/repo/issues/1"]}]});
test("provisional source diagnoses stay provisional on source and article pages", () => {
  const data = validateErrata(fixture(), [source], assertions);
  const html = errataPage(data, source, assertions, absent);
  assert.ok(html.includes("Editorial status: provisional"));
  assert.ok(html.includes("Awaiting Tom's confirmation"));
  assert.ok(html.includes("&lt;script&gt;source&lt;/script&gt;"));
  assert.ok(!html.includes("<script>"));
  assert.ok(articleErrata("alpha", [data], assertions).includes("/errata/notes/#sign"));
  assert.equal(articleErrata("beta", [data], assertions), "");
});
test("confirmation, withdrawal, and assertion references require explicit records", () => {
  const data = fixture(); data.entries[0].status = "confirmed";
  assert.throws(() => validateErrata(data, [source], assertions), /confirmation/);
  data.entries[0].confirmationUrl = "https://github.com/example/repo/issues/1#issuecomment-2";
  assert.ok(errataPage(validateErrata(data, [source], assertions), source, assertions, absent).includes("Tom's confirmation"));
  data.entries[0].status = "withdrawn";
  assert.throws(() => validateErrata(data, [source], assertions), /withdrawal/);
  Object.assign(data.entries[0], {withdrawalReason: "No fault.", withdrawalUrl: source.url});
  const html = errataPage(validateErrata(data, [source], assertions), source, assertions, absent);
  assert.ok(html.includes('id="sign"'));
  assert.ok(html.includes("This entry has been withdrawn"));
  assert.ok(!html.includes("Reported problem"));
  data.entries[0].tags = ["ZZZZ"];
  assert.throws(() => validateErrata(data, [source], assertions), /tag/);
});
test("errata distinguish absent evidence, statement review, proof debts and source confirmation", () => {
  const data = validateErrata(fixture(), [source], assertions);
  const noManifest = errataPage(data, source, assertions, absent);
  assert.ok(noManifest.includes("Formal status: unavailable"));
  assert.ok(!noManifest.includes("Formal status: unformalised"));
  assert.ok(noManifest.includes("&lt;scope&gt;"));
  assert.ok(noManifest.includes('/articles/alpha/#formal-evidence'));
  const fingerprint = {schema: "perclib-statement-v1", sha256: "a".repeat(64)};
  const entry = {tag: "AAAA", proof_status: "statement-only", fingerprint, inputs: []};
  const evidence = {entries: new Map([["AAAA", entry]]), reviews: [], provenance: {
    repository: "tomhutchcroft/lrp", commit: "b".repeat(40),
    runUrl: "https://github.com/tomhutchcroft/lrp/actions/runs/123"
  }};
  let html = errataPage(data, source, assertions, evidence);
  assert.ok(html.includes("Compiled statement; correspondence pending"));
  assert.ok(html.includes("Wiki/Lean correspondence review: missing"));
  assert.ok(html.includes('/articles/alpha/#formal-AAAA'));
  assert.ok(html.includes(evidence.provenance.commit));
  assert.ok(html.includes(evidence.provenance.runUrl));
  evidence.reviews.push({tag: "AAAA", fingerprint: {...fingerprint}});
  html = errataPage(data, source, assertions, evidence);
  assert.ok(html.includes("Formal status: stated"));
  assert.ok(html.includes("Editorial status: provisional"));
  entry.fingerprint = {...fingerprint, sha256: "c".repeat(64)};
  html = errataPage(data, source, assertions, evidence);
  assert.ok(html.includes("Wiki/Lean correspondence review: stale"));
  assert.ok(!html.includes("Formal status: stated"));
  data.entries[0].status = "confirmed";
  data.entries[0].confirmationUrl = source.url;
  entry.proof_status = "proved-modulo";
  entry.inputs = ["Synthetic.<Input>"];
  html = errataPage(data, source, assertions, evidence);
  assert.ok(html.includes("Editorial status: confirmed"));
  assert.ok(html.includes("Formal status: proved-modulo"));
  assert.ok(html.includes("Named inputs still to discharge"));
  assert.ok(html.includes("Synthetic.&lt;Input&gt;"));
  assert.ok(html.includes("Wiki/Lean correspondence review: stale"));
  entry.proof_status = "proved"; entry.inputs = [];
  html = errataPage(data, source, assertions, evidence);
  assert.ok(html.includes("Formal status: proved."));
  assert.ok(html.includes("Wiki/Lean correspondence review: stale"));
  data.entries[0].status = "withdrawn";
  data.entries[0].withdrawalReason = "No fault.";
  data.entries[0].withdrawalUrl = source.url;
  html = errataPage(data, source, assertions, evidence);
  assert.ok(!html.includes("Consequences for Lean"));
  assert.ok(!html.includes("Formal status: proved"));
});
test("authored formal statuses and missing formalisation consequences fail closed", () => {
  const data = fixture();
  data.entries[0].formalStatus = "proved";
  assert.throws(() => validateErrata(data, [source], assertions), /invalid entry/);
  delete data.entries[0].formalStatus;
  delete data.entries[0].leanImpact;
  assert.throws(() => validateErrata(data, [source], assertions), /invalid entry/);
});
