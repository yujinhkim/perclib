# Roadmap

**12 November 2026.** This replaces the ordering in `INITIAL_BACKLOG.md`. Decisions cited
as D-n and R-n are in [DECISIONS.md](DECISIONS.md). Working rules are in
[COORDINATION.md](COORDINATION.md).

Each package below is written so that a contributor who has read only this file,
`DECISIONS.md`, `COORDINATION.md` and `AGENTS.md` can start it. A package is done when
its acceptance line holds on a commit with a passing CI run.

## Order at a glance

```text
Phase 0  H-1 → H-2 → H-3, H-4            hygiene; nothing else merges first
Phase 1  P-1 → P-2 ─┐   (P-2 → P-2b, off the critical path)
               P-3 ─┼→ P-5 → P-6 → P-7   pilot theorem          (Gate B, with Phase 2)
         P-4 ───────┘
Phase 2  N-1; W-1 → W-2; W-3 → W-4 → W-5, W-6   wiki linked to Lean (release v0.1)
Phase 3  T-1 → T-2, T-3, T-4 → T-5       shared toolkit         (release v0.2)
Phase 4  F-1 → F-2 …                     hierarchical two-point (release v0.3)
```

**Start rule (D-22).** A package starts when each dependency is merged or is an open pull request with green CI. T-2, T-3 and T-4 start now and do not wait for v0.1.

P-4 can start as soon as P-1's signatures are agreed. W-1 and W-2 can start after H-3 and need no Lean skill. N-1 merges before P-1. T-1 is read-only and can start now (R-3 is answered).

## Phase 0: hygiene

| ID | Work | Acceptance |
|---|---|---|
| H-1 | Tom answers R-1. R-2 is answered. | Answer recorded in `DECISIONS.md`. |
| H-2 | Rebase `reuse/percolation-foundations` on `main`. Move the site module per D-3. Add a top-level Apache-2.0 `LICENSE` and the all-rights-reserved notices for the notes directories (R-2). Correct `docs/UPSTREAM_REUSE.md` so its status cites the CI run on the final commit. Merge PR #2. | `main` contains `Lrp.Probability.ProdBernoulli`; CI green on the merge commit; no document on `main` calls unmerged work checked. |
| H-3 | CI changes, in one PR with no mathematics. (a) Fail if any `Lrp/**/*.lean` is not in the import closure of `Lrp.lean`. (b) Trigger on `pull_request` and on `push` to `main` only. (c) Add a job that runs the wiki build. (d) Delete `scripts/AuditImportedPercolation.lean`; the rooted axiom audit replaces it. (e) One always-run final job that requires the others. | A PR adding an unimported file fails. A PR with a broken wiki link fails. |
| H-4 | Rewrite the root `README.md`: what exists, what is proved (with D-4 statuses), where the plan is. | README names no result that is absent from `main`. |

## Phase 1: the pilot theorem

**Target.** Let `V` be countable and `q : Sym2 V → [0,1]`. If `0 ≤ m < 1` and
`∑_w q(v,w) ≤ m` for every `v`, with the sum over `w ≠ v`, then `χ(v) ≤ 1/(1−m)` for
every `v`, and almost surely every cluster is finite.

The signatures below were drafts that fixed intent. P-1 compiled them on 13 November
2026 with one change, the coercion in `chi`, recorded under D-2. The compiled file,
`PercLib/Percolation/Bond/Basic.lean`, is the reference; this block is a summary.

```lean
namespace PercLib.Percolation.Bond
abbrev Config (V : Type*) := Set (Sym2 V)
def law (q : Sym2 V → unitInterval) : Measure (Config V) := prodBernoulli q
def openGraph (ω : Config V) : SimpleGraph V := SimpleGraph.fromEdgeSet ω
def conn (x y : V) : Set (Config V) := {ω | (openGraph ω).Reachable x y}
def cluster (ω : Config V) (x : V) : Set V := {y | (openGraph ω).Reachable x y}
def tau (q) (x y : V) : ℝ≥0∞ := law q (conn x y)
def chi (q) (x : V) : ℝ≥0∞ := ∫⁻ ω, ((cluster ω x).encard : ℝ≥0∞) ∂(law q)
```

| ID | Work | Depends | Acceptance |
|---|---|---|---|
| P-1 | `PercLib/Percolation/Bond/Basic.lean`: the definitions above; `conn` is reflexive and symmetric; `conn` and `{ω | (cluster ω x).Infinite}` are measurable for countable `V`. The site proofs in PR #2 are the model for the measurability arguments. | H-2 | Compiles; the interface in D-2 is confirmed or amended. |
| P-2 | `PercLib/Probability/Cylinder.lean`: for a finite set `F` of indices, `prodBernoulli p {ω | ↑F ⊆ ω} = ∏ i ∈ F, p i`. Check mathlib's `Measure.infinitePi` API and upstream `ProdBernoulliIndependence` first (D-6). | H-2 | Stated for a general index type, not only for edges. |
| P-2b | `PercLib/Percolation/Bond/Host.lean`: the host-graph lemma of D-2. For a simple graph `G` on countable `V`, if `q = 0` on every pair that is not an edge of `G`, then almost surely no pair outside the edge set of `G` is open, and the open graph is a subgraph of `G`. | P-2 | Stated for an arbitrary `G`; not needed by P-5. |
| P-3 | `PercLib/Percolation/Bond/Susceptibility.lean`: `ω ↦ (cluster ω x).encard` is measurable for countable `V`; then `chi q x = ∑' y, tau q x y`, by Tonelli. | P-1 | The measurability lemma is proved, not assumed. The identity holds with infinite values; no finiteness hypothesis. |
| P-4 | `PercLib/Percolation/Bond/WalkSum.lean`, deterministic. For `a : V → V → ℝ≥0∞` with `∑' w, a v w ≤ m` for all `v`, the `n`-step walk weight from any `v` is at most `m ^ n`, and the total over `n` is at most `(1 − m)⁻¹` when `m < 1`. P-5 applies this with `a v w = if w = v then 0 else (q s(v, w) : ℝ≥0∞)`, so nothing here may assume `a v v = 0` or use `a v v`'s value beyond the row-sum bound. | P-1 signatures | No probability imports. |
| P-5 | `PercLib/Percolation/Bond/RowSum.lean`: the row-sum hypothesis is spelled `∀ v, ∑' w, (if w = v then 0 else (q s(v, w) : ℝ≥0∞)) ≤ m`, with the diagonal excluded explicitly (D-2). `tau q x y` is at most the sum over simple paths from `x` to `y` of the product of `q` along the path (existence of a path witness, P-2, union bound). Then the target theorem, and almost-sure finiteness of all clusters. | P-2, P-3, P-4 | The target as stated above. The proof never multiplies probabilities along a walk with a repeated edge. |
| P-6 | `PercLib/Percolation/Bond/Intensity.lean`: `q_β = 1 − exp(−β J)` for `J ≥ 0`, `β ≥ 0`; root and global thresholds in `ℝ≥0∞`; if `∑_w J(v,w) ≤ M` for all `v` then `χ_β ≤ 1/(1−βM)` when `βM < 1` and every threshold is at least `1/M`. | P-5 | `M = 0` gives infinite thresholds, handled without division by zero. |
| P-7 | `PercLib/Models/…`: four instances of P-5 or P-6: a finite graph; the complete graph with constant `p` and `(n−1)p < 1`; `ℤ^d` with a summable translation-invariant kernel; the hierarchical lattice with a radial summable kernel. | P-6 | Each compiles against the unchanged P-1 interface. These are the non-vacuity witnesses required by D-5. |

Gate B is passed when P-7 and W-4 are merged. The lead's expectation is that P-1 exposes
at least one flaw in D-2. Report it; do not work around it.

## Phase 2: link the wiki to Lean

Designed for a large library (D-12 to D-18). W-1 and W-2 need no Lean skill and can start
after H-3. W-3 is the steward's.

| ID | Work | Depends | Acceptance |
|---|---|---|---|
| N-1 | Rename the root namespace and Lean library to `PercLib` and the package to `perclib` (D-11). Update `lakefile.toml`, the CI audit root, and every document describing the current API. Tom renames the GitHub repository. No mathematics. | H-2 | CI green. No `Lrp` identifier remains in the Lean library, its imports, the Lake configuration, the CI build and audit roots, or any document describing the current API. Records of earlier revisions keep the names those revisions used (D-10). The four reference documents frozen by D-1 are unchanged. Repository URLs change when Tom renames the repository (D-11). Merged before P-1. |
| W-1 | Migrate the twelve articles to one Markdown file each with front matter. Give every citable assertion a tag from `scripts/new_tag` (write that script) and an anchor. Content otherwise unchanged. | H-3 | Every assertion has a unique tag; CI rejects a duplicate. No Lean declaration name remains in article content (D-12). |
| W-1b | WIKI writes `wiki/STYLE.md`, the prose style Tom approved (D-19), then revises the twelve articles to it. Off the critical path; W-2 does not wait for it. | W-1 | Tom has approved `wiki/STYLE.md`. Every tag and anchor is unchanged and no tagged statement has changed its mathematical content. |
| W-2 | Static site generator: one pre-rendered page per article, `/tag/XXXX` redirect pages, build-time mathematics, static search index. Retire the single-page app. Source lives in `src/`; `dist/` is generated and ignored. | W-1 | A fresh clone builds the site with no Lean toolchain installed. |
| W-3 | The `@[tag]` attribute and the extractor. CI emits `manifest.json` for the built commit: tag, declaration, type, file, line, axioms, statement fingerprint (D-15), and tag-level dependencies of statement and of proof (D-14). CI fails on a tag that is absent from the wiki or duplicated. Read verso-blueprint's dependency inference before writing the extractor, and reuse it where D-18 allows. | P-1, W-1 | Renaming a tagged declaration changes nothing on the site except the displayed name. |
| W-4 | The site consumes the manifest: computed status, rendered Lean statement, dependency panel from the extraction, review records with staleness, link to doc-gen4 output. Remove the committed `repository-metrics.json`. | P-5, W-2, W-3 | The row-sum page shows `proved` with commit and run, with no hand edit. Changing a definition in its statement marks its review stale. |
| W-5 | The frontier page: assertions not yet `proved` whose prerequisites are `proved`, generated on each build. | W-4 | Matches the hand-written frontier in COORDINATION §6 at v0.1, which is then deleted. |
| W-6 | `Sources/` convention: restate the pilot result as it appears in Hutchcroft (2021) and in the notes, each tagged as a source occurrence. | P-6, W-3 | The source concordance page is generated from these tags and the `occurs_in` records. |

## Phase 3: the shared toolkit

| ID | Work | Acceptance |
|---|---|---|
| T-1 | Reuse inventory of `near-critical-diffusivity` (D-6). One table: file, main statements, vertex type and generality, dependencies, whether it ports unchanged to the D-2 interface. Cover at least `Bernoulli`, `Harris`, `OpenEventHarris`, `BK`, `CylinderBK`, `CountableBK`, `LatticeRusso`, and `Percolation/Literature/SharpnessDCT*`. Read-only. | `docs/REUSE_INVENTORY.md` merged; each row marked port, generalise, or rewrite. |
| T-2 | Harris inequality for increasing events under `prodBernoulli`, general index type. | Finite and countable index sets. |
| T-3 | BK inequality for increasing events, finite index set first, then cylinder and countable forms. State the disjoint-occurrence convention once and reuse it. | The form needed by T-5 and F-1 is identified before work starts. |
| T-4 | Russo's formula on a finite index set, with differentiation in a parameter through `q`. | Covers both `p` and `β` parametrisations. |
| T-5 | Finite susceptibility below the threshold for a summable, translation-invariant long-range kernel on `ℤ^d`. Exponential decay in distance is not part of this target and is false for power-law kernels. | `proved`. A `proved-modulo` version may merge as an intermediate step with each input tracked as an open issue; the package stays open until none remain. |
| T-6 | Universal tightness of the largest cluster intersection, with the constants `1/9` and `27` of Hutchcroft (2021). | Statement reviewed against the paper before proof work. |

## Phase 4: the first critical theorem

| ID | Work | Acceptance |
|---|---|---|
| F-1 | Dependency decomposition of the hierarchical two-point theorem (arXiv 2103.17013): Theorem 1.1 (averaged) and Corollary 1.2 (pointwise, radial) as separate targets, each with its list of inputs marked available or planned. Every literature input is itself a proof obligation (R-5), so the decomposition continues down to mathlib. No proof work. | Reviewed by Tom. Becomes the Phase 4 package list. |
| F-2… | Defined by F-1. | |

## Not on the roadmap

Planar theory, lace expansion, finite random graph scaling limits, IIC, and the full book
inventories stay in scope for the project and are not scheduled. They are scheduled by a
decision in `DECISIONS.md` once v0.2 exists.
