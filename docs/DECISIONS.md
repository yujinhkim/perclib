# Decision record

**Opened 12 November 2026 by the project lead (Claude), at Tom Hutchcroft's request.**
This file is the authority on what has been decided. Where it disagrees with
`PROJECT_PLAN.md`, `WIKI_ARCHITECTURE.md`, `WIKI_PROTOTYPE.md` or `INITIAL_BACKLOG.md`,
this file wins; those four are now background reference. The order of work is in
[ROADMAP.md](ROADMAP.md) and the working rules are in [COORDINATION.md](COORDINATION.md).

The lead will not be executing work packages and is not continuously present. A decision
is changed by a PR that edits this file and is merged under D-20. Nobody changes a decision
by working around it.

## Why the reset

An audit of the repository on 12 November 2026 found three problems.

- The planning documents total about 100 KB and the Lean library is one smoke-test
  inequality. None of the architecture has been tested by a real theorem.
- `main` describes work that is not on `main`: the wiki cites the PR #2 port as checked,
  PR #2 is unmerged, and its own reuse document still says "pending CI".
- The repository is public, has no licence, and contains the unpublished notes.

## Reserved for Tom

These block the packages named. Nobody else decides them.

| ID | Question | Lead's recommendation | Blocks |
|---|---|---|---|
| R-1 | Should the repository be public while it holds `sources/notes/book_draft.tex` and the extracted paragraphs in `docs/sources/notes/`? | Make it private now. Reopen when the notes are meant to be public or have been moved out. | Everything outward-facing |
| R-2 | Which licence? | **Answered 12 November 2026:** Apache-2.0 for Lean and tooling. The notes (`sources/notes/`, `docs/sources/notes/`) are all rights reserved and say so in a notice in those directories. The wiki prose licence is deferred until public hosting is decided; until then it is all rights reserved. | Nothing now |
| R-3 | May `tomhutchcroft/near-critical-diffusivity` be used as a reuse source, given its co-authors and its vendored third-party code? | **Answered 12 November 2026: yes**, with per-file attribution as in PR #2. | Nothing now |
| R-4 | Who holds each role in COORDINATION §1? | **Answered 12 November 2026:** the Lean steward is a dedicated agent session subordinate to Tom. Its charter is COORDINATION §1a. | Nothing now |
| R-5 | Is a release that is proved modulo named cited inputs acceptable as a public milestone? | **Answered 12 November 2026: no.** The goal of this repository is results proved from the axioms. See D-4 and D-9. | Nothing now |

## Decided

### D-1. Planning freeze
No edits to the four reference documents and no new architecture documents until Gate B
(ROADMAP Phase 1 and Phase 2 complete). Corrections go here as new decisions.

### D-2. The bond interface
- A bond configuration on a vertex type `V` is a `Set (Sym2 V)`: the set of open pairs.
- The law is `PercLib.Probability.prodBernoulli q` with `q : Sym2 V → unitInterval`.
- The open graph is `SimpleGraph.fromEdgeSet ω`. Loops are discarded by that
  construction, so the value of `q` on the diagonal is irrelevant and is never a
  hypothesis.
- There is no host-graph parameter. A host graph is the special case `q = 0` off its
  edge set, with a lemma connecting the two views. That lemma is owed after P-2 and is
  package P-2b.
- Row sums of `q` over the neighbours of `v` exclude `w = v` explicitly, because `q` on
  the diagonal is arbitrary. The spelling is
  `∑' w, if w = v then 0 else (q s(v, w) : ℝ≥0∞)`.
- `Countable V` is a hypothesis of measurability and almost-sure statements only, not of
  definitions.
- Cluster volume is `ℕ∞`-valued. Expectations are `ℝ≥0∞`-valued; the susceptibility
  integrates the volume coerced to `ℝ≥0∞`. The cluster of `x` contains `x`. Thresholds
  for intensity families are `ℝ≥0∞`-valued.

The Lean steward may amend details that fail to compile or fight mathlib, by a PR to this
section before P-1 merges. After P-1 merges this interface is frozen.

**Amended 13 November 2026** after P-1 compiled (`PercLib/Percolation/Bond/Basic.lean`
at `ab0be77`). P-1 confirmed the interface and found no flaw. The amendment adds the
coercion in the susceptibility, the statement that a cluster contains its base vertex,
the explicit exclusion of the diagonal in row sums, and package P-2b for the host-graph
lemma. It was proposed by STEWARD under the clause above and reviewed and approved by
ARCHITECT on Tom's behalf. It takes effect when Tom merges the pull request that carries
it. D-2 is frozen when P-1 merges.

### D-3. Site percolation is a model, not the foundation
`Lrp/Percolation/Site/Basic.lean` from PR #2 moves to `Lrp/Models/Site/Basic.lean`. Its
real-valued threshold with `∪ {1}` is a convention of that model and is not copied
elsewhere. `Lrp/Probability/ProdBernoulli.lean` stays where it is and is canonical.
(After N-1 these paths begin `PercLib/`.) The cluster conventions differ and are not
interchangeable: a bond cluster always contains its base vertex, while the site cluster
of a closed vertex is empty.

### D-4. Proof status vocabulary
Every assertion has exactly one of four formal statuses.

| Status | Meaning |
|---|---|
| `unformalised` | No Lean statement. |
| `stated` | A Lean statement compiles and its correspondence has been reviewed. No proof. |
| `proved-modulo` | Proved from explicit hypotheses that stand for named literature results. |
| `proved` | Proved with only `propext`, `Classical.choice`, `Quot.sound`. |

A cited literature result is an explicit hypothesis, bundled as a structure whose name
ends in `Input`. It is never an `axiom`. Each `Input` is listed in `docs/CITED_INPUTS.md`
with its reference and exact locator. `proved-modulo` is a working status only (R-5). It is always displayed with its list of
inputs, it never counts as completing a target, and no release milestone is met by it.
Every `Input` is a debt: it has an open issue for its proof, and a target is done only
when it is `proved`.

### D-5. Non-vacuity is a compiled deliverable
Every `Input` structure and every theorem whose hypotheses are not obviously satisfiable
ships with a compiled witness: an `example` or instance showing the hypotheses hold in
the smallest relevant case and at the largest relevant parameter. A PR without it is not
ready for review.

### D-6. Reuse order
Look for existing code in this order: mathlib at the pinned revision;
`near-critical-diffusivity` (subject to R-3); `anthropics/formal-math`;
`percolation-after-anthropic`. Port with attribution as in PR #2. Generalise a lattice
result to a countable vertex type only when a roadmap target needs the general form.

### D-7. Wiki content freeze and simplification
- No new articles beyond the existing twelve until W-1 to W-4 are done.
- Relation types and the Lean link are now governed by D-12 and D-14, which replace the
  earlier four-type list.
- A displayed formal statement is rendered from the Lean declaration, not retyped.
- Hand-written source does not live in `dist/`.

### D-8. Source inventories are on demand
The notes inventory already committed is enough for now. Grimmett and
Heydenreich–van der Hofstad are inventoried one section at a time, when a roadmap target
needs that section. Inventories hold locators and the project's own formulations, never
copied text. SRC-02 and SRC-03 of the old backlog are withdrawn as up-front tasks.

### D-9. Release scope
- **v0.1** The row-sum susceptibility theorem, its intensity corollary, four instances,
  and one wiki page whose status is generated from CI.
- **v0.2** Harris, BK and Russo on the D-2 interface, and finiteness of susceptibility
  below the threshold for summable long-range kernels.
- **v0.3** The hierarchical critical two-point estimate, `proved`, including the full closure of its
  prerequisites.

No coverage percentage and no completion date is published for the wider corpus.

### D-10. Evidence
A status claim cites a CI run on the exact commit. A document that says "checked",
"verified" or "passed" without a run URL for that commit is wrong and is fixed on sight.
`main` never describes unmerged work as present.

## Wiki and Lean integration at scale

Decided 13 November 2026 with Tom. The aim is a large library, so these replace the
pilot-sized design in the first version of ROADMAP Phase 2. Tom approved this as an
exception to D-1.

| ID | Reserved for Tom | Lead's recommendation |
|---|---|---|
| R-6 | The new name of the repository and of the Lean namespace (D-11). | **Answered 13 November 2026:** repository `perclib`, namespace and Lean library `PercLib`. |

### D-11. Rename
The repository and the root namespace `Lrp` are renamed, because the library is general
percolation and not only long-range. The new names are `perclib` and `PercLib` (R-6). The namespace rename is one
dedicated PR by the steward with no mathematics, and it merges **before P-1**. Tom renames
the GitHub repository himself; nobody else changes repository settings.

**Clarified 13 November 2026** (ARCHITECT, issue #18, comment 6844522555). N-1's
acceptance means that no `Lrp` identifier remains in the Lean library, its imports, the
Lake configuration, the CI build and audit roots, or any document describing the current
API. Records of earlier revisions keep the names those revisions used (D-10), the four
documents frozen by D-1 are unchanged, and repository URLs change when Tom renames the
repository. Wiki content that names Lean declarations does not block N-1: under D-12 the
wiki names no Lean declaration at all, and W-1's acceptance now says so. Where a roadmap
acceptance line conflicts with a decision in this file, the decision wins and the conflict
is raised as a `needs-decision` issue.

### D-12. Tags are the only link between the wiki and Lean
- Every citable assertion (a definition or result a mathematician would cite) has an
  opaque tag of four characters from `0-9A-Z`, for example `0A3F`. Tags are allocated at
  random by `scripts/new_tag`, checked for uniqueness in CI, and never reused. A
  withdrawn tag keeps a tombstone.
- A wiki article declares the tag beside its prose statement. A Lean declaration carries
  the same tag as an attribute, `@[tag "0A3F"]`.
- The wiki never contains a Lean declaration name and Lean never contains wiki prose. CI
  extracts tag to declaration, type, file, line and axioms into `manifest.json` for the
  built commit, and the site joins on the tag.
- Helper lemmas are not tagged. Expect roughly one tag per 20 to 50 declarations.
- This replaces the `PC-nnnnnn` scheme and the hand-kept registry of declaration names.

### D-13. Three layers
- **Library:** organised by mathematical dependency with mathlib naming and style, never
  by paper. A paper's exact theorem is restated in its own notation in
  `Sources/<Paper>.lean` and proved there in a few lines from the general result. That
  restatement carries the tag of the source occurrence.
- **Wiki:** a flat network of concept articles with tagged assertions.
- **API documentation:** generated by doc-gen4 for every declaration. The wiki links into
  it and does not document helpers.

### D-14. Compute, do not author
- **Status** (D-4) is computed from the manifest. No authored status field exists.
- **Dependencies between formalised assertions** are extracted from Lean and collapsed
  onto tagged declarations: `A` depends on `B` when `A` reaches `B` through untagged
  declarations only. The statement and the proof are extracted separately.
- **Authored relations** exist only where Lean cannot supply them: `proof_uses` for an
  assertion not yet proved, and `occurs_in` for source occurrences. When an assertion
  becomes `proved`, its authored `proof_uses` is ignored in favour of the extraction.
- **The work frontier** is computed: assertions not yet `proved` whose prerequisites are
  all `proved`. After v0.1 this list, not a hand-written table, is how work is chosen.

### D-15. Reviews are bound to a fingerprint
The manifest records, for each tag, a fingerprint of the statement together with every
project definition it unfolds to. A human correspondence review is stored as tag,
fingerprint, reviewer and date. If the fingerprint changes, the review is shown as
stale until redone. No page shows "reviewed" without a matching fingerprint.

### D-16. Statements before proofs
An unproved target is a tagged `def Name : Prop`. Its proof, when it exists, is a theorem
of that type carrying the same tag. This gives the `stated` status without any `sorry` on
`main`. A statement is reviewed (D-15) before proof work is assigned.

### D-17. The site
- Pre-rendered static pages, one per article, with real paths. `/tag/0A3F` resolves
  permanently. Mathematics is rendered at build time. Search uses a static index.
- The wiki build reads `manifest.json` as an artifact and never compiles Lean.
- The current single-page prototype is retired once its twelve articles are migrated. Its
  content is kept; its application code is not extended.
- Lean's Verso framework is not adopted, because it couples prose to the Lean build. The
  steward checked its current state once, as this bullet first required; the finding
  follows and the resulting decision is D-18.

**Finding on Verso, recorded 13 November 2026.** Read from GitHub that day by STEWARD
(pull request 20), with AUDITOR's correction on licensing. This paragraph records facts.

- `leanprover/verso` is active and maintained by the Lean FRO: Apache-2.0, a tag for each
  Lean release including `v4.35.0` (our pin), last pushed 12 November 2026.
- `leanprover/verso-blueprint` exists (pinned to Lean 4.35.0, last pushed 13 November
  2026, inspected at commit `4943d3335ffa`). It links informal statements to Lean
  declarations, computes progress from the Lean code (including `sorry`), draws
  dependency graphs, answers a work-queue query, and keeps three layers (sources,
  informal content, Lean) much like D-13. That overlaps most of D-14 and W-3 to W-5.
- In verso-blueprint the prose is written in Lean modules and the site is produced by
  `lake exe vbp build`, so building the wiki needs the Lean toolchain and the library.
- The repository has no `LICENSE` file and GitHub reports no licence. Individual source
  files, including `DependencyAnalysis.lean`, `VersoBlueprint.lean`, `Vbp.lean`,
  `VbpMain.lean` and `ProvedStatus.lean`, carry an explicit header naming Lean FRO LLC
  and Apache-2.0.

### D-18. verso-blueprint is a reuse source, not the platform
Decided 13 November 2026 by ARCHITECT (issue 19). It takes effect when the pull request
that carries it merges (D-20).

- **Not adopted as the site or as the home of the prose.** D-12 to D-17 stand as written,
  and so does W-2's acceptance line.
- **Why.** (1) In verso-blueprint the prose is Lean source and the site is built by
  Lake. Every wiki edit would go through a Lean build, a broken or slow Lean build would
  stop the site, W-2's acceptance (no Lean toolchain) would fail, and WIKI's editing
  responsibilities would have to be redrawn. Upstream's starter keeps the prose in its
  own Lake library, so the prose would not have to live under `PercLib/`; that is not
  the objection. (2) It does not provide what this design depends on: permanent opaque
  tags with `/tag/XXXX` and tombstones (D-12), reviews bound to a statement fingerprint
  (D-15), and this project's status mapping for tagged `Prop` definitions and their
  proofs (D-4, D-16). Upstream has its own status API, which distinguishes proved,
  missing, axiom-like and unverified declarations; it is not that mapping. These would
  have to be built anyway, inside a young framework that this project does not control
  and that moves with every Lean release. (3) The choice kept is the cheaper one to
  reverse. Markdown with tags plus a `manifest.json` can be fed to a Verso front end
  later; prose written as Lean modules cannot be moved out cheaply.
- **What is taken from it.** The extractor of W-3 is the one expensive custom component
  and is where the overlap is real. Before writing it, STEWARD reads verso-blueprint's
  dependency inference (`doc/HELPER_DEPENDENCY_INFERENCE.md` and
  `DependencyAnalysis.lean`). `leanprover/verso-blueprint` is added to the reuse order of
  D-6, after mathlib. A file that carries its own Apache-2.0 header may be adapted, with
  that header preserved and the source, revision and licence recorded as D-6 requires. A
  file without such a header is read for design only and is not copied.
- **The seam.** `manifest.json` is the only interface between Lean and the site. Its
  schema names nothing specific to the site generator, so the front end can be replaced
  without touching the library or the articles.
- **Revisit once,** when v0.1 is released, and earlier only if W-3 cannot produce the
  statement and proof dependencies of D-14 within its package. Otherwise this is not
  reopened.

### D-19. Wiki prose style
Recorded 13 November 2026. Tom approved a more concise mathematical prose style for the
wiki that day, in discussion with WIKI, after WIKI's research into Scott Armstrong's
manuscript process and Martin Hairer's essay on mathematical writing. The existing
proof-writing style of the twelve articles is not the standard.

- **Where the rules live.** WIKI writes them down in `wiki/STYLE.md`, as Tom approved
  them, and Tom approves that file. This decision does not restate them. Tom is the only
  judge of style; AUDITOR does not review style.
- **Revision is its own package.** Rewriting the existing articles in the approved style
  is W-1b. It starts after W-1 merges and is never mixed into the migration, which
  preserves the prose.
- **What a revision may not change.** Every tag and anchor is kept (D-12). The
  mathematical content of a tagged statement is unchanged. If a statement itself looks
  wrong or needs rewording that changes its meaning, that is raised separately for Tom
  and is not done as a style edit. AUDITOR checks these two points on every prose PR.
- **Scope.** D-7 still holds: no new articles before W-1 to W-4 are done. Every article
  written after `wiki/STYLE.md` is approved follows it. Lean docstrings are not covered.

### D-20. Tom does not handle pull requests
Decided 13 November 2026 on Tom's instruction ("I don't want to have to manually deal
with all these PRs"), and confirmed by him after ARCHITECT set out the terms below.
Where this conflicts with COORDINATION §1a or §5, this wins and COORDINATOR brings that
file into line.

- **Merging.** STEWARD merges every pull request, whoever wrote it, once CI is green on
  its final commit and AUDITOR has approved that commit. This includes pull requests to
  this file, to `ROADMAP.md` and to `COORDINATION.md`, and AUDITOR's own reports, which
  STEWARD reviews in AUDITOR's place. Nobody waits for Tom to merge or approve.
- **Decisions.** ARCHITECT writes a decision; AUDITOR checks it against the existing
  record; STEWARD merges it. Tom's approval is no longer a step. Tom can reverse any
  decision afterwards by saying so, and ARCHITECT records the reversal.
- **Housekeeping.** COORDINATOR closes superseded and duplicate pull requests and stale
  issues, and resolves collisions between agents, without asking.
- **What Tom sees.** One digest a day from COORDINATOR: what merged, and a list of at
  most five items that need him, each as a question he can answer in a line. Nothing
  else is addressed to Tom.
- **Still Tom's alone.** The reserved items R-n; repository settings, visibility and the
  rename; anything irreversible, including force pushes to `main`; scope and the
  fidelity of a target statement to its source; approval of `wiki/STYLE.md` (D-19).
  Work that does not depend on one of these never stops for it.
- **Known weakness.** Every agent posts from Tom's GitHub account, so AUDITOR's approval
  is a comment and nothing technical enforces this gate. It holds only because the
  agents follow it. AUDITOR reports any merge made without its approval in the next
  gate report.

### D-21. MANAGER keeps the Codex agents working
Recorded 13 November 2026. Tom added a Codex agent, MANAGER, whose one job is to make
sure the other Codex agents (AUDITOR, SCOUT, WIKI, PROVER-A, PROVER-B) are working
whenever they have work to do. COORDINATOR adds it to the roster in COORDINATION §1b.

- **What counts as work to do.** A package the agent holds with a confirmed claim; a
  pull request of its own with changes requested or failing CI; for AUDITOR, any pull
  request awaiting review; a package on the frontier that the roster gives to that agent
  and whose dependencies are met.
- **What MANAGER does.** It checks each Codex agent against that list and starts or
  nudges the ones that are idle with work waiting. It tells COORDINATOR when an agent
  is stuck, does not respond, or has nothing it can start.
- **One session per role.** Before starting an agent, MANAGER confirms that no session
  of that role is already running. Two WIKI sessions produced two pull requests for W-1;
  that is the failure this rule prevents. It also respects the one-build-per-machine
  rule of COORDINATION §4.
- **What MANAGER does not do.** It does not assign or reassign packages, confirm claims,
  triage, decide, review, merge, or write Lean, wiki or documents. Assignment and triage
  stay with COORDINATOR, review with AUDITOR, merging with STEWARD. It does not manage
  the Claude sessions (STEWARD, COORDINATOR, ARCHITECT). It writes issue comments only.
- **Order of attention.** AUDITOR's review queue first, because under D-20 every merge
  waits on it; then agents with changes requested; then unstarted frontier packages.

### D-22. No gate is held by an agent that is not running
Decided 14 November 2026 by ARCHITECT, after Tom reported that the agents were working
far under capacity. Where this conflicts with D-20, D-21, COORDINATION or a roadmap
dependency column, this wins.

**What went wrong.** Nothing merged between 05:19 UTC on 13 November and this decision,
about forty hours. In that time P-1, P-4, T-1, W-1 and the COORDINATOR charter were all
approved by AUDITOR with green CI and sat unmerged. Every step that moves work forward
(merging, confirming claims, confirming signatures, deciding) was held by STEWARD,
COORDINATOR or ARCHITECT, which are Claude sessions that run only when Tom starts them,
and none ran after 07:05 UTC on 13 November. The Codex agents woke every hour, found the
same gates closed, and wrote a report saying so. That design was ARCHITECT's, and so
were two of the blockages: the pull request carrying D-18 to D-21 waited on a correction
only ARCHITECT could make, and the stacking question (issue 38) waited on ARCHITECT.

- **Merging.** AUDITOR merges a pull request itself as soon as it has approved the final
  commit and CI is green on it. STEWARD may also merge under the same condition; nobody
  waits for STEWARD. Stacked pull requests merge in dependency order, and AUDITOR
  retargets the next one to `main`. AUDITOR's own gate reports touch only `docs/audits/`
  and merge on green CI without a second reviewer. This replaces the first bullet of
  D-20; the rest of D-20 stands.
- **Starting.** An agent starts a package as soon as each prerequisite is either merged
  or an open pull request with green CI, and stacks its branch on that pull request.
  This holds for every agent (issue 38, option b, without the requirement that the
  prerequisite be reviewed first). If the prerequisite later changes, the dependent
  rebases; that cost is accepted.
- **Claims.** The assignment below, and afterwards the roster, is the claim. No
  confirmation is needed. A package with no assignee belongs to the first agent of the
  right kind that comments `claim` on its issue.
- **Signatures.** AUDITOR's approval of the pull request that defines a signature is the
  confirmation a dependent needs. P-1's signatures are confirmed.
- **Evidence (clarifies D-10).** The evidence for a pull request is the green CI run
  GitHub associates with its latest commit, cited by URL in the pull request. That run
  tests the merge with `main`, which is what should be tested; its tree need not equal
  the branch head's tree. Evidence is not restated in committed files, and a commit that
  changes only documents does not void an approval of the Lean it did not touch.
- **Questions do not stop work.** An agent with an open question for Tom or ARCHITECT
  proceeds on the reading it recommends, says so in the pull request, and marks the
  affected statements. An ARCHITECT decision posted as an issue comment is in force at
  once; the record in this file follows.
- **Idle reports.** An agent with nothing runnable posts that once and takes the next
  unassigned package on the list below. It does not post again until something changes.
- **The frontier is widened.** T-2, T-3 and T-4 depend only on `prodBernoulli` and start
  now; they do not wait for v0.1. The unscheduled tracks stay unscheduled.
- **Assignments from this decision,** until the roster is updated:
  PROVER-A: P-2, P-3, P-5, P-2b, then T-3.
  PROVER-B: W-3 (taken from STEWARD, because it gates v0.1), then T-2, T-4, and P-6 and
  P-7 once P-5 is an open pull request.
  WIKI: W-2 stacked on W-1, `wiki/STYLE.md` (D-19), H-4, then W-4.
  SCOUT: F-1 on its recommended readings of issues 52 and 53, then reuse findings for
  T-2 to T-5.
  AUDITOR: merge the approved queue first, then review in dependency order.
  STEWARD and COORDINATOR keep their charters when they are running, and nothing waits
  for them when they are not.

### D-23. Throughput
Decided 14 November 2026 by ARCHITECT. Tom's target is at least tens of thousands of
lines of Lean a day. The measure is lines of Lean merged into `main` per day that build
with `--wfail` and pass the axiom audit. On 14 November `main` held 345 lines and the
open branches about 770 more, after two days.

- **Review is of statements, not proofs.** The kernel checks proofs. AUDITOR reads the
  tagged and target statements, the definitions they unfold to, `Input` structures,
  non-vacuity witnesses and attribution headers. It does not read proof bodies or helper
  lemmas; the build and the axiom audit are their gate. For a pull request that adds no
  definition and no tagged or target statement, AUDITOR confirms exactly that and merges.
- **Review never holds a queue.** AUDITOR reviews in dependency order and merges at
  once. If more than five pull requests are waiting, MANAGER tells COORDINATOR and Tom
  in the digest that a second AUDITOR is needed.
- **Porting comes first.** Verified upstream Lean is the fastest source of lines. Every
  row of `docs/REUSE_INVENTORY.md` marked port or generalise is a package now. A port
  lands on the D-2 interface and `prodBernoulli`, not on a second copy of upstream's
  definitions, and carries its D-6 header. SCOUT opens one issue per row.
- **Small pull requests, opened early.** One file or one coherent group of lemmas per
  pull request, opened as soon as it compiles. Nobody holds work back to finish a
  package.
- **The frontier stays ahead of the provers.** SCOUT's standing duty is to keep at least
  three unclaimed, startable packages open for every prover, by decomposing Phase 3,
  Phase 4 and the inventory. A prover that finishes takes the next one without asking.
- **More provers.** Any new prover session joins by commenting `claim` on an unassigned
  package (D-22). No roster change is needed first. Two provers cannot reach the target;
  the number of prover sessions is Tom's lever.
- **What is not traded away.** D-4, D-5 and the axiom rule stand. Lines that duplicate
  definitions, restate mathlib, or sit off the D-2 interface do not count and are not
  merged.

### D-24. Work in long sessions; separate interface from proofs
Decided 14 November 2026 by ARCHITECT, after Tom observed that the agents wake hourly
and work for about two minutes. The hourly wake was treated as the unit of work: each
wake re-read the governing documents, checked for permission, found none and reported.
The process ARCHITECT wrote asked for exactly that.

**The work loop.** This replaces the per-session ritual of COORDINATION §1b and §7.

1. A session takes the first startable package in its queue (D-22) and works on it
   until a pull request is open with green CI. It then takes the next one in the same
   session. It does not stop to wait for review, a merge, a claim or an answer.
2. A session ends only when nothing in its queue is startable and no unassigned package
   is startable either, or when the tool ends it. A scheduled wake exists to restart a
   session that ended, not to do a unit of work.
3. On start an agent reads the governing documents only if they changed since its last
   session, and reads only the change.
4. A handoff note is written when a session ends, not on every wake, and never to say
   that nothing changed.
5. A build failure or a proof that will not close is not a reason to stop. The agent
   narrows the lemma, tries another route, or opens the pull request as a draft with
   what compiles and moves to the next package.

**Two kinds of pull request.** This is how definitions stay coherent without a steward.

- An **interface pull request** adds or changes definitions, structures, instances,
  notation or tagged statements (D-16). It is small, contains no long proofs, and gets
  AUDITOR's full review. Definitions live only in files named `Basic.lean` or
  `Defs.lean`, one per directory.
- A **proof pull request** adds theorems and lemmas only. CI checks that it adds no
  definition and changes no interface file. It merges on green CI with no reading.
- Before proposing a definition, an agent searches the definitions index and mathlib.
  A second definition of an existing notion is rejected, whatever proofs depend on it.
- CI publishes a **definitions index**: every public definition with its file and type.
  ARCHITECT reads the change to that index at each check, and AUDITOR lists new
  definitions in each gate report. This is the standing review of the interface.
- The CI check and the index are one package, assigned with W-3.

### D-25. STEWARD and COORDINATOR are retired; INTEGRATOR replaces them
Decided 14 November 2026. Tom retired both roles that day and allowed ARCHITECT to
replace them with Claude Opus 5.5 agents. Where this conflicts with D-20 to D-24 or with
`COORDINATION.md`, this wins. The prompts that run every agent are in
[AGENT_PROMPTS.md](AGENT_PROMPTS.md).

- **Correction to D-22.** D-22 gave merging to AUDITOR. AUDITOR's instructions from Tom
  forbid it to merge, and it rightly declined; ARCHITECT assumed otherwise without
  checking. A reviewer that does not merge is also the better design. Twenty-three pull
  requests were open and none had merged when this was found.
- **INTEGRATOR** is one Claude Opus 5.5 session that keeps itself awake on a schedule.
  It merges every pull request that is mergeable under the rule below, bottom of each
  stack first, retargets the next one, resolves conflicts in `PercLib.lean` and other
  shared files, and reruns CI when needed. It owns `PercLib.lean`, `.github/`, the
  toolchain and dependency pins (upgrades remain Tom's), and the CI check and
  definitions index of D-24. It closes superseded pull requests and stale issues,
  writes one digest a day for Tom (D-20), and rewrites `COORDINATION.md` once to match
  D-20 to D-25. It writes no mathematics.
- **When a pull request is mergeable.** CI is green on its latest commit, and either
  AUDITOR has approved that commit (interface pull requests, documents, wiki), or it is
  a proof pull request under D-24 and INTEGRATOR has confirmed from the diff that it
  adds no definition and changes no interface file. AUDITOR's gate reports merge on
  green CI.
- **AUDITOR** reviews and never merges. Its scope is D-23.
- **Nothing else replaces STEWARD or COORDINATOR.** W-3 is PROVER-B's (D-22). Liveness is
  MANAGER's (D-21). Coherence of definitions is held by D-24. Questions for ARCHITECT
  are labelled `for-architect` by whoever raises them.
- **Finding work.** SCOUT keeps the label `startable` on every package issue whose
  prerequisites are merged or open with green CI and that nobody has claimed. A prover
  takes the lowest-numbered one by commenting `claim`.
- **D-24 transition.** Pull requests open on 14 November that put definitions outside
  `Basic.lean` or `Defs.lean` merge as they are. The rule binds pull requests opened
  afterwards. INTEGRATOR moves the earlier definitions in one later pull request.
- **Sorted imports.** `PercLib.lean` keeps one import per line in alphabetical order, so
  that concurrent additions rarely conflict.
- **If INTEGRATOR stops.** MANAGER reports in issue 34 when a mergeable pull request has
  waited two hours. That is the signal for Tom to restart it.

### D-26. Events, not timers
Decided 14 November 2026 by ARCHITECT, after Tom said that timed wake-ups are the wrong
organising principle. He is right. A timer makes every handoff wait for the next tick of
whichever agent holds it, and each tick is spent finding out whether anything happened.

- **Merging is done by GitHub, not by an agent.** A workflow runs when CI finishes, when
  a review or comment is posted and when a pull request changes. It merges a pull
  request that satisfies D-25, retargets the pull requests stacked on it, and labels
  new pull requests that need AUDITOR `needs-audit`. A pull request labelled `hold` is
  never merged. INTEGRATOR writes and owns this workflow and otherwise acts only on
  what it cannot do: conflicts and a red `main`.
- **Merge on green, without first updating with `main`,** unless GitHub reports a
  conflict. The CI run on `main` after each merge is the safety net; a merge that
  breaks `main` is reverted at once and returned to its author.
- **Agents pull from queues.** A queue is a GitHub query: issues labelled `startable`
  for provers, pull requests labelled `needs-audit` for AUDITOR. An agent works its
  queue until it is empty (D-24) and never waits for another agent.
- **Timers are a watchdog only.** A scheduled wake exists to restart a session that has
  died. It carries no work, and no handoff depends on it.
- Where an agent tool can be started by a GitHub event (a mention, a label, a review
  request), that replaces its timer. ARCHITECT does not know which of Tom's tools
  support this.

**Note of 14 November 2026: Codex automatic review.** Tom turned on Codex's automatic
review of pull requests. Its instructions are the "Code Review Rules" section of
`AGENTS.md`. It is an experiment that runs beside AUDITOR. Its verdict line is
`CODEX-REVIEW verdict:` and `merge-bot` ignores it; only `AUDITOR verdict:` counts for
merging. ARCHITECT compares the two on interface pull requests and decides, by an
amendment here, whether the automatic review may replace AUDITOR for any class of pull
request.

### D-27. Redundant roles on two platforms, with disjoint queues
Decided 14 November 2026 on Tom's suggestion. The gating roles run twice, once as a
Codex agent and once as a Claude agent started by ARCHITECT, so that neither platform
stalling stops the project. Two agents never work on the same item.

- **AUDITOR (Codex) and AUDITOR-2 (Claude).** Both write the same verdict line and
  either approval is sufficient to merge. Review is across model families: AUDITOR-2
  takes pull requests written by Codex agents, AUDITOR takes those written by Claude
  agents and by ARCHITECT. Either takes any pull request that has waited thirty minutes.
  A CHANGES REQUIRED verdict is cleared only by the auditor that gave it, or by the
  other once the listed changes are visibly made.
- **SCOUT (Codex) and SCOUT-2 (Claude).** SCOUT keeps the reuse inventory, the port
  packages and F-1. SCOUT-2 keeps the `startable` label correct on every issue and
  decomposes the roadmap and the standard material into packages. Before opening an
  issue each searches the open issues for the same statements.
- **Provers** are redundant by nature: any number on either platform, kept apart by
  claims.
- **Not duplicated.** INTEGRATOR and WIKI stay single, because two writers of the same
  shared files collide. MANAGER stays on Codex and also reports on issue 34 if the
  Claude agents go quiet for an hour, which is the sign that ARCHITECT's session has
  ended and Tom must restart it.
- Codex automatic review remains an experiment beside both auditors and does not merge.

### D-28. Outside contributors
Decided 14 November 2026 by ARCHITECT, at Tom's request, before his collaborators'
agents arrive. Their instructions are in [CONTRIBUTING.md](../CONTRIBUTING.md).

- **Access.** The repository is private (observed 14 November 2026), so a contributor
  must be invited by Tom before anything else. On a private repository owned by a
  personal account every invited collaborator can push, so the rule is a convention
  until Tom protects `main` or moves the repository to an organisation: outside
  contributors push only branches named `work/<handle>-…`, or work from a fork, and
  never push to `main` or to anyone else's branch. All changes reach `main` by pull
  request.
- **Their queue.** The label `open-to-all` marks packages whose prerequisites are merged
  and which can therefore be done from a fork. SCOUT-2 keeps at least ten such packages
  open and unclaimed, and does not put work on that label that an internal prover has
  started. Claims are by comment, as for everyone (D-22).
- **Review.** Every pull request from an account other than the repository owner's needs
  an AUDITOR verdict, including proof pull requests; the mechanical proof-only route of
  D-25 does not apply to them. AUDITOR-2 takes these first.
- **Verdicts cannot be forged.** `merge-bot` counts an `AUDITOR verdict:` line only when
  the review or comment was posted from the repository owner's account. A pull request
  from a fork that touches `.github/`, `scripts/`, `lakefile.toml`, `lake-manifest.json`
  or `lean-toolchain` is never merged by the workflow; INTEGRATOR handles it by hand
  after an auditor has approved it.
- **Names.** An outside agent's name begins with its owner's GitHub handle. One session
  per name.
- **Licence.** Contributions are accepted under Apache-2.0 (R-2). The notes stay all
  rights reserved. R-1, whether the repository should be public while it holds the
  notes, is still open and is more pressing now; it remains Tom's.
- **Coordination.** ARCHITECT answers outside contributors' questions on issues labelled
  `question`, and at each check looks at pull requests from new authors and at
  collisions between outside and internal claims.
