# Wiki article editing and assertion tags

The twelve articles live in `articles/*.md`. W-1 preserves the original prototype
exposition exactly. The static generator renders these sources at real article URLs.

## Build and checks

```sh
cd wiki
npm ci
npm run build
```

This runs regression tests and checks content preservation, identities, internal
references and mathematics. Output is generated in `wiki/dist/` and is ignored by
Git. Serve that directory at the web origin root, for example with
`python3 -m http.server 8000 --directory dist`. No Lean command is invoked.
The old `wiki/prototype` npm entry point delegates to this build for existing CI.

Handwritten renderer, CSS, browser search/menu code, and bibliography records live
in `src/`. Articles are complete HTML pages at `/articles/<id>/`; KaTeX runs only
at build time. `/tag/XXXX/` redirects to the article assertion, with a visible link
as a fallback. A static server should normalize directory requests (`/tag/XXXX`)
to their trailing-slash path. Withdrawn identities have permanent tombstone pages.
Search uses `search-index.json`; reading and navigation do not require JavaScript.
All generated local links and fragments are checked before output is replaced.

For just the article/tag checks, run `node wiki/scripts/check-articles.mjs` from
the repository root. `node wiki/scripts/check-articles.mjs <base-commit>` also
checks history against an explicit revision. A local build compares with HEAD
and works offline. In GitHub Actions, the event's PR base or push-before commit is
used; a shallow checkout fetches that one commit if necessary. Failure to obtain
that base fails validation rather than silently skipping history. Source archives
without Git still validate their current ledger and content.

## File format

Front matter is JSON between `---` delimiters (JSON is a YAML subset). It holds
article discovery metadata and the original `context` array of running notation
and assumptions. It contains no assertion tag, authored formal status, or Lean
declaration name. Article filenames match their `id`.

Sections use `## Heading {#section-section-id}`. Their bodies retain the original
HTML, valid inside Markdown, so mathematical delimiters, links, whitespace, and
hypothesis placement survive the migration without a conversion round trip.
Sections are separated by a blank line; the file ends with one newline. The reader implements this
small explicit format; it is not a general-purpose Markdown parser.

An assertion anchor immediately precedes the original statement block:

```html
<a id="tag-0A3F" data-assertion="theorem" data-title="Short assertion title"></a>
```

`0A3F` here is illustrative, not a reservation. Kinds are `definition`,
`proposition`, `theorem`, and `corollary`. A tag identifies a citable assertion,
not a page or every displayed intermediate calculation. Compound theorem
conclusions can share one tag; independently useful results receive separate
tags. The statement still inherits its article's running context. Never move a
theorem-specific hypothesis into that context when editing.

The anchors are deliberately invisible, preserving the approved prototype design.
Legacy `PC-...` references in source bodies resolve through the migration baseline;
they are not assertion identities. `prototypeUses` preserves editorial reading
links, not extracted Lean dependency data. The build converts old hash links to
static paths while leaving the authored article bodies unchanged. Each assertion's
destination is `/articles/<id>/#tag-XXXX`.

## Allocate and withdraw

From the repository root:

```sh
wiki/scripts/new_tag
```

This reserves a random four-character uppercase base-36 tag in `tags.json` and
prints it. Add its anchor beside the statement, and commit the article and ledger
together. Unused allocations remain reserved. A lock excludes concurrent writers;
a second writer fails explicitly. The replacement ledger is written atomically.
After integrating another branch, validate again: independently allocated tags
can collide and CI rejects the collision. Do not delete ledger entries.

To withdraw an assertion, first remove its anchor, then run:

```sh
wiki/scripts/new_tag --withdraw XXXX
```

The ledger retains a tombstone forever. History validation rejects a removed
reservation, reactivated tombstone, or removed assertion without its tombstone.
Moving an assertion between articles preserves its tag. Mathematical changes to
an assertion's identity need editorial review; a validator cannot decide whether
two different mathematical statements mean the same thing.

## Migration evidence

`migration-baseline.json` records SHA-256 digests of each original section body and
article metadata, plus the original Git revision. Checks strip only the exact
assertion anchor syntax and compare every section. The original JSON remains in
Git history; it is no longer an independently editable source. The digests prove
preservation relative to that recorded snapshot, not mathematical correctness.
Changing prose intentionally in a later package requires explicit review and an
update to this temporary preservation check. Do not update digests merely to hide
an accidental migration difference.

The superseded W-1 PR #35 (`cdf39dac239a5183393fdc534dd6ec3d7c6be6b2`)
allocated 33 other tags before the duplicate writer was retired. Those identities
are retained as withdrawn reservations in `tags.json`; they must never be reused.
All 49 section bodies and all 33 tagged sections were compared with this migration:
the prose is identical and every tagged section has assertion coverage here.
The continuing PR #36 supplies the 65 active assertion anchors. The withdrawn
identities do not introduce additional assertions or a second registry.

## Compiled evidence (W-4)

A normal build works without Lean and without an artifact. In that case formal
status is unavailable; absence of a supplied manifest is not a claim that every
assertion is unformalised. No repository measurement/status snapshot is committed.

The publishing environment obtains a successful W-3 `assertion-manifest` artifact
using its GitHub artifact ID (Python 3 standard library; `GH_TOKEN` or `GITHUB_TOKEN`
is used for authenticated downloads):

```sh
python3 wiki/scripts/fetch-manifest.py ARTIFACT_ID --output wiki/.artifacts
cd wiki
WIKI_MANIFEST=.artifacts/manifest.json \
WIKI_MANIFEST_RECEIPT=.artifacts/receipt.json npm run build
```

The downloader checks GitHub's archive digest and artifact/run association, requires
a completed successful run, and binds the exact manifest bytes into a receipt.
The build validates that receipt offline. Use receipts from this trusted download
step; a JSON receipt is not a digital signature and cannot authenticate a hand-edited
file. Neither artifacts nor receipts belong in Git. A PR artifact may identify the
synthetic merge checkout, which differs from the run's head SHA. The displayed
commit comes from the artifact and the run link from the matching successful run.

The consumer accepts W-3's `perclib-manifest-v1` schema and requires complete coverage
of the current active assertion tags. Unknown/duplicate tags, missing declarations,
invalid source locations or dependency references, forbidden axioms, contradictory
Input debts, unsupported fingerprints, or mismatched evidence fail the build.
The article locations used for links come from the current wiki; Lean names and
statements come only from the artifact. Missing source lines remain unavailable.

`reviews/correspondence.json` stores real correspondence reviews, never authored
proof statuses. Its schema is `perclib-reviews-v1`, with a `reviews` array. Each entry
contains `tag`, `fingerprint` (`schema` and `sha256` copied from the reviewed artifact),
`reviewer`, `date` (`YYYY-MM-DD`), and `url` linking the actual GitHub review/discussion.
Do not create a review merely because Lean compiled. No reviews are fabricated by
the default empty file. A changed definition changes the fingerprint; old records
remain visible as stale. A fingerprint schema change requires consumer support and
fresh review, not silent acceptance.

Raw `statement-only` becomes D-4 `stated` only with a matching correspondence review.
Otherwise it is shown as a compiled statement awaiting correspondence, without a
D-4 status claim. `proved` and `proved-modulo` describe the extracted Lean statement;
correspondence to the prose is displayed separately. `proved-modulo` always shows
its named inputs. Statement and proof dependencies are shown on separate axes.
No new Lean association or mathematical review is supplied by this consumer.

To link published doc-gen4 output, additionally set `WIKI_DOCGEN_BASE` to its HTTPS
root and `WIKI_DOCGEN_COMMIT` to the exact artifact commit. Without that binding,
the site links the exact Lean source and explicitly says API documentation has not
been supplied; it never guesses a current hosted documentation URL.

Run `python3 wiki/tests/test_artifact.py` for downloader digest/redirect regressions.
The ordinary npm test suite includes artifact/review join, stale-review, status,
dependency, source-link and generated-page integration tests. Their synthetic Lean
statements and reviews are fixtures only, never published evidence.

### Tagged source concordance

`records/<article-id>.json` stores each article’s `occursIn` source-occurrence
records. The loader assembles the `perclib-occurs-in-v1` input for validation. It contains no proof statuses and allocates no tags. Each occurrence names
an existing `source` catalog ID and active `tag`, the exact catalog `source_url` and
`edition`, a precise `locator`, a `relationship`, and a mathematical `note` explaining
the relationship. Relationships are `source-statement`, `generalization` (the wiki
assertion generalizes the source), `specialization`, or `definition`. Changing a
source URL or edition requires reconciling its records; stale records fail the build.

The source index, each source page, and the associated assertion's article render
these records from one input. Formal status and wiki/Lean review staleness come only
from the validated compiled evidence. A source record never supplies a correspondence
review and does not certify source fidelity. Legacy editorial reading links remain
visible and are explicitly distinguished from tagged occurrences.

No occurrence is inferred from article titles, similar
statements or a theorem's name. In particular, the uniform-row generalization and its
zero-row case must not be advertised as the source's verbatim transitive theorem.
### Generated proof frontier

`/frontier/` is rebuilt from the same validated manifest and receipt as the evidence
panels. Each article’s `records/<article-id>.json` stores `proofUses` records for intended
proof prerequisites, never statuses. Each record contains `tag`, `proof_uses` (unique active tags) and `reason`
(the mathematical justification for this prerequisite list). A missing record is
unknown; an explicit empty list asserts that no additional tagged proof prerequisites
are needed. Article reading links are not proof dependencies.

For each unproved assertion with a record, the build takes the union of extracted
statement dependencies, extracted proof dependencies, and authored `proof_uses`.
It is ready by prerequisites exactly when every member is `proved` in the supplied
snapshot. `proved-modulo` does not satisfy a prerequisite. Named inputs and the
fingerprint correspondence review remain visible; readiness is not an assignment
or an approval to skip statement review. Proved assertions are omitted and their
authored proof prerequisites ignored (D-14). Cyclic unproved prerequisites remain
blocked. No manifest means no computed readiness.

The old COORDINATION §6 table is a package scheduling table, not a list of tagged
assertions. It cannot establish assertion-level frontier equivalence. Its removal
and any package-queue migration belong to INTEGRATOR; this package edits only `wiki/`.


### Articles after the migration

New articles may be added now that W-1 through W-4 have merged. The migration
baseline remains immutable: the original twelve articles must still be present with
identical metadata, sections and text. Additional articles use the same parser, tag
ledger, link checks and math renderer; they do not enter or rewrite that baseline.
Reserve tags with `scripts/new_tag` before inserting their anchors. Article prose
never claims a Lean status; the compiled evidence panel supplies it when available.

### Growth analytics

`/metrics/library/` and `/metrics/wiki/` are generated from committed Git snapshots;
`/metrics/history.json` contains the complete series used by their charts and tables.
The default tip is `HEAD`. Set `WIKI_HISTORY_REF` to an available revision (for example,
`origin/main`) to analyze that history instead. The resolved commit is displayed.
The reference comparison defaults to the locally recorded `refs/remotes/origin/main`.
Set `WIKI_HISTORY_REFERENCE` to another available revision to override it. The JSON
records its resolved commit, source counts, common ancestor (when known), and the
relationship to the selected tip. The pages compare complete tree counts; a divergent
reference is not treated as the branch's contribution. A missing reference leaves the
growth series available and marks the comparison unavailable. A shallow or disconnected
history can leave ancestry unknown even when both trees can be counted. References are
never assumed current with GitHub.
The build never fetches history or runs Lean. Use a full checkout for the full range;
a shallow checkout is visibly marked as incomplete. An exported source archive with
no Git metadata displays history as unavailable.

Snapshots follow the first-parent history, retaining commits that changed `PercLib/`,
`wiki/articles/` or `wiki/tags.json`, plus the selected tip. Charts use equally spaced
snapshots rather than an elapsed-time axis. Tables give commit timestamps, exact
counts and adjacent-snapshot changes. Dirty working files are excluded.

Lean counts measure tracked source files and nonblank lines, including comments and
definitions, not verified theorem totals. Article word counts measure whitespace
separated source tokens including metadata and markup. Anchors, permanent tag
reservations and withdrawals are separate series. Earlier prototype HTML is not
counted as canonical articles. Historical proof and correspondence status require
historical manifests/reviews; no such series is inferred from source text.


The growth pages also show a file-level inventory for the selected tip and the
recorded comparison revision. Each path links to its exact committed contents;
blob identities distinguish edits that leave source counts unchanged. Added and
removed mean absent from one of these trees, not newly authored or deleted by a
particular contributor. Renamed paths appear separately. The inventories and
per-file counts are in `metrics/history.json`; the CSV remains the snapshot time
series. Missing reference inventories do not imply an empty baseline. These
source inventories do not supply historical compiled or reviewed status.

## Source reading maps

`/coverage/` renders the canonical worklist. Its article links may include a
section or assertion fragment; the final site link check verifies the destination.
Version-specific reading maps live in `wiki/sources/<slug>.md` and appear at
`/coverage/sources/<slug>/`, in the coverage list and in browser search. Worklist
links use `sources/<slug>.md`; missing maps fail the build. A source archive with
no maps directory simply has no reading-map entries.

The intentionally small reading-map format accepts a standalone `# Title`,
paragraphs, `##`/`###` headings, HTTPS links, article links and simple pipe tables.
Raw HTML is escaped. This is a reading inventory, not another tag registry or an
authored formalization status. Maps render into the static site and are therefore
included in the standalone preview without fetching their Markdown at runtime.

### Article-owned records

Each article has one optional `records/<article-id>.json` file with schema
`perclib-article-records-v1` and an `article` matching the filename. Its arrays are
`collections` (collection ID and display order), `sourceOccurrences` (source ID,
display order and editorial reading records), `occursIn` (tagged source records)
and `proofUses` (tagged proof prerequisites). Tagged records must belong to that
article. `order` preserves the historical display order; ties use the article ID.
New articles may choose an order without renumbering other articles.

`src/content/catalog.json` holds only source bibliography and subject descriptions.
Do not add article rows there. Add or revise an article's rows in its own record
file. The compiled manifest, formal review records and permanent tag ledger remain
separate from these authored reading and relation records.

### Source errata

`/errata/` links one page per source. Entries live in `errata/<source-id>.json`
with schema `perclib-source-errata-v1`, a catalog `source`, and `entries`. Each
entry has a permanent local `id`, title, exact locator, paraphrased source claim,
reported problem, corrected statement or explicit unresolved scope, existing
assertion tags and issue URLs. The required `leanImpact` explains the mathematical
consequences for formalisation: the corrected contract or proof dependency, the
hypotheses a workaround adds, and any targets left unaffected. It is not a hand-kept
proof status and contains no Lean declaration names. The build links affected articles and source pages
and includes the entries in search. Errata never allocate assertion tags.

The editorial status starts as `provisional`. Change it to `confirmed` only after
Tom explicitly confirms the correction, and retain his `confirmationUrl`.
A review by an agent or a successful build is not Tom's confirmation. Withdraw
an incorrect report with status `withdrawn`, a `withdrawalReason` and
`withdrawalUrl`; retain its ID and source file so its URL remains a tombstone.
This status is separate from manifest-derived formal proof status.

Each source errata page joins its assertion tags to the same validated manifest
and fingerprint-bound correspondence reviews as the article pages. It displays
the compiled commit, evidence link, formal status and any named input debts, with
links to the statements and Lean evidence on the articles. Without a manifest,
formal status is unavailable (not inferred to be `unformalised`). A changed
fingerprint leaves the correspondence review stale; confirming an erratum does
not refresh that review or prove the correction. Authored formal-status fields
are rejected. Keep all diagnoses pinned to the edition actually inspected; do
not silently extend an arXiv-version discrepancy to a later published edition.
