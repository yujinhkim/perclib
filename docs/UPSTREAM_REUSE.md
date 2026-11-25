# Existing-library reuse: pinned audit and first integration

Audit date: 2026-11-12. This record distinguishes the observed upstream verification from
verification of the adapted `perclib` files.

## Status of the perclib port

Under DECISIONS D-10 a status claim cites a CI run on the exact commit. The evidence is:

| Revision | What it is | Evidence | Status |
| --- | --- | --- | --- |
| `4b1f7bf859d00d0a5fff781820f1cf7312f2e2bf` | Head of `reuse/percolation-foundations` (PR #2) before the rebase. The site module was at `Lrp/Percolation/Site/Basic.lean`. | [Run 43324614451](https://github.com/tomhutchcroft/lrp/actions/runs/43324614451) (push, exact checkout of this commit): `lake build --wfail` and the axiom audit rooted at `Lrp`, 47 declarations, only `propext`, `Classical.choice`, `Quot.sound`. Read with `gh` on 13 November 2026. | Passed. Historical; never on `main`. |
| `e5e55213a0d7873f1020ef1c6fc4655b972ed720` | `work/H-2-reuse-foundations`: PR #2 rebased on `main` at `f38c177`, with the site module moved to `Lrp/Models/Site/Basic.lean` (D-3). | [Run 43364411092](https://github.com/tomhutchcroft/lrp/actions/runs/43364411092), [job 131685302148](https://github.com/tomhutchcroft/lrp/actions/runs/43364411092/job/131685302148) (push, exact checkout of this commit): `lake build --wfail` and the axiom audit rooted at `Lrp`, 47 declarations, only `propext`, `Classical.choice`, `Quot.sound`. Read with `gh` on 13 November 2026. | Passed. |

Each row is evidence for the revision named in it and for no other. Later commits on the
branch, including the one that adds this table, need their own run (D-10); the run on the
final revision of the H-2 pull request is cited in that pull request.

The names in the table are those in use at each revision. On 13 November 2026 the
library root was renamed from `Lrp` to `PercLib` and the package from `lrp` to `perclib`
(DECISIONS D-11, package N-1); the rest of this document uses the new names. The GitHub
repository URL is unchanged until Tom renames the repository.

## Concrete integration

Keep the current `lean-toolchain`, `lakefile.toml` and `lake-manifest.json` unchanged.
The first integration uses the already pinned Mathlib probability and graph library and
adapts a small, attributed selection of percolation foundations to that toolchain.

| perclib module | Reused content | Source |
| --- | --- | --- |
| `PercLib.Probability.ProdBernoulli` | Inhomogeneous product law, probability-measure instance, map representation, specialization to Mathlib's `setBernoulli` | [ProdBernoulli.lean](https://github.com/anthropics/formal-math/blob/795efb86f191735c5481675763537cfb4ff37e55/percolation/Percolation/Literature/LatticeModels/ProdBernoulli.lean), [ProdBernoulliProofs.lean](https://github.com/anthropics/formal-math/blob/795efb86f191735c5481675763537cfb4ff37e55/percolation/Percolation/Literature/LatticeModels/ProdBernoulliProofs.lean) |
| `PercLib.Models.Site.Basic` | Open site graph, cluster and connection events; elementary consistency lemmas; measurability of connection and infinite-cluster events on countable graphs | [SiteStatements.lean](https://github.com/nitromannitol/percolation-after-anthropic/blob/a5cc72bd7627f313abbb00bcb47616678abbeb35/Hypergraph/SiteStatements.lean) |
| `PercLib.Models.Site.Basic` | Lattice vocabulary, critical parameter as an infimum, proofs that it is in the unit interval | [SolutionBasic.lean](https://github.com/nitromannitol/percolation-after-anthropic/blob/a5cc72bd7627f313abbb00bcb47616678abbeb35/PercolationAudit/SiteCriticality/SolutionBasic.lean) |

`PercLib.lean` publicly imports `PercLib.Probability.ProdBernoulli` and `PercLib.Models.Site.Basic`
as well as the existing `PercLib.Basic`. This makes the new public declarations reachable by
the project's normal build and transitive axiom audit. Site percolation is a model, not
the foundation (D-3): its declarations are in the namespace `PercLib.Models.Site`, and its
real-valued threshold with `∪ {1}` is a convention of that model only. CI also runs
`scripts/check_import_closure.py`, which fails if a file under `PercLib/` is not reachable
from `PercLib.lean`. The explicit list `scripts/AuditImportedPercolation.lean` was removed in
H-3; the rooted audit replaces it.

The copied source carries prominent modification notices and exact upstream revisions.
The full Apache-2.0 license and both retained notices are in `third_party/percolation/`.

### Adaptations

1. Use the `PercLib.Probability` and `PercLib.Models.Site` namespaces and the Lean 4.35
   `module` / `public import` convention.
2. Replace the old Mathlib names `MeasurableEquiv.setOf` and `Set.mem_setOf_eq` with
   `MeasurableEquiv.setOfPred` and `Set.mem_ofPred_eq`. Name the local lattice vertex
   type `LatticeSite` to avoid a duplicated `Site.Site` namespace warning.
3. Express the two-point law using current Mathlib's `bernoulliMeasure`. The theorem
   `prodBernoulli_eq_weighted`, proved by `rfl`, records definitional agreement with
   the weighted-Dirac expression used in the original audit vocabulary.
4. State the indicator specialization directly as `prodBernoulli_indicator`, instead of
   the original pair of a named proposition and its proof. Its proof follows the source
   proof and uses Mathlib's Bernoulli simplification lemmas. The constant-parameter
   specialization `prodBernoulli_const` is a new immediate corollary.
5. Restrict imports to the required probability, graph and measure modules. This removes
   the original foundational file's import of the complete Kozma–Nitzan development.

These are explicit source adaptations, not a claim that the whole older package compiles
on the perclib toolchain. They must pass `lake build --wfail` and the project's axiom audit
before they receive a checked status.

## Exact upstream revisions and compatibility

| Library | Revision | Lean | Mathlib |
| --- | --- | --- | --- |
| Existing perclib Mathlib dependency | `56a005855ea17e0b0958f73ec801ae140b0a1679` | 4.35.0 | same revision |
| Percolation after Anthropic | `a5cc72bd7627f313abbb00bcb47616678abbeb35` | 4.32.0 | `81a5d257c8e410db227a6665ed08f64fea08e997` |
| Anthropic PercolationContinuity dependency, `percolation/` | `795efb86f191735c5481675763537cfb4ff37e55` | 4.32.0, as used by the audited upstream build | `81a5d257c8e410db227a6665ed08f64fea08e997`, as resolved by that build |

The package `percolation_after_anthropic` requires `PercolationContinuity` from
`anthropics/formal-math` at the exact revision above, with `subDir = "percolation"`.
Its Mathlib pin is inherited through that dependency. The source has no top-level
`PercolationAudit.lean`; the concrete solution import is
`PercolationAudit.SiteCriticality.Solution`.

A blanket dependency addition would select code written for a different Lean and Mathlib
revision. This first integration therefore does not add that dependency. A full import
should be a separate compatibility change: port the dependency closure to the current
pin or deliberately coordinate a project-wide version decision. Do not silently replace
the perclib pins.

## What the upstream audit actually establishes

The following were inspected through the GitHub connector at the exact revision above:

- The actual theorem and definitions in `Challenge.lean`, `SolutionBasic.lean`,
  `Solution.lean`, `SiteCriticalityBridge.lean`, `Hypergraph/SiteStatements.lean`
  and `Hypergraph/FinalCriticality.lean`.
- The actual comparator configuration and build/audit scripts.
- [CI run 43273898161](https://github.com/nitromannitol/percolation-after-anthropic/actions/runs/43273898161)
  and job 131377082968. The job succeeded. Its decoded log reports 14 audited
  declarations with only `propext`, `Classical.choice` and `Quot.sound`, including
  `KNAll.Site.site_no_percolation_at_critical`.
- [Comparator run 43273970309](https://github.com/nitromannitol/percolation-after-anthropic/actions/runs/43273970309)
  and job 131384892087. The job succeeded. Its decoded log records acceptance by
  nanoda and successful comparator validation. These are observed build records,
  rather than the README's self-reported status.

The comparator target is

```lean
KNAll.StatementAudit.SiteCriticality.site_no_percolation_at_critical
    (d : ℕ) (hd : 3 ≤ d) :
  thetaSite d (criticalProbSiteI d) = 0
```

Its actual solution is the direct use of
`KNAll.Site.site_no_percolation_at_critical d hd`. The support module records
definitional identifications between the audit vocabulary and the original library.
The original theorem's explicit hypotheses are the dimension and `3 ≤ d`; the
source constructs the internal `NeZero d` instance from that bound.

**Scope:** this is nearest-neighbour Bernoulli site percolation on integer lattices in
dimension at least three. It is not a theorem about an arbitrary long-range kernel.
The first perclib port does not include this theorem or its large proof dependency closure.
Its observed upstream audit status is recorded separately from perclib integration status.
The mathematical correspondence of any future imported result still needs the project's
normal statement review.

### The intentional incomplete challenge

`PercolationAudit.SiteCriticality.Challenge` contains one intentional `sorry`.
It is a statement comparison input, not a production proof. The solution does not import
the challenge. The upstream target `lake build PercolationAudit` also builds the
challenge because of its module glob, so a warning from that target alone must not be
misread as a clean production import.

No challenge file, incomplete proof or assumed criticality result is included by the
new `PercLib` imports. The new production source contains no `sorry`, `admit`,
`axiom`, or `native_decide`.

## Attribution

- **Percolation after Anthropic:** the retained NOTICE identifies Ahmed Bou-Rabee as the
  person prompting the subsequent Kozma–Nitzan, hypergraph and site development,
  produced with ChatGPT and Claude. Repository: [nitromannitol/percolation-after-anthropic](https://github.com/nitromannitol/percolation-after-anthropic).
- **PercolationContinuity:** copyright 2026 Anthropic, PBC; its retained notice identifies
  Justin Leder as responsible author and maintainer, with Lean source written by Claude
  under his direction. The exact historical source is pinned above.
- **Mathlib:** use the existing dependency, retaining its source-level author and
  copyright notices. The directly used set-Bernoulli module credits Yaël Dillies;
  the Bernoulli-distribution module credits Etienne Marion and David Ledvinka.
  Other imported modules retain their own attributions.
- The copied percolation source is Apache-2.0. The full upstream license and relevant
  upstream notices accompany the adapted files. These notices attribute upstream work
  and do not imply endorsement or maintenance of perclib by upstream contributors.

## Next reusable modules

After the small foundations compile, review the following at their exact pins, prioritising
their hypotheses and reusable interfaces rather than headline claims:

| Module | Candidate content | Integration state |
| --- | --- | --- |
| [Mathlib.Probability.Independence.InfinitePi](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Probability/Independence/InfinitePi.lean) | `iIndepFun_infinitePi`, restriction of product measures along injections | Existing Mathlib dependency; use directly where needed |
| [ProdBernoulliIndependence](https://github.com/anthropics/formal-math/blob/795efb86f191735c5481675763537cfb4ff37e55/percolation/Percolation/Literature/LatticeModels/ProdBernoulliIndependence.lean) | Cylinder probabilities and independence for sets of indices | Candidate; proof source and dependency closure still to audit |
| [ProdBernoulliCoupling](https://github.com/anthropics/formal-math/blob/795efb86f191735c5481675763537cfb4ff37e55/percolation/Percolation/Literature/LatticeModels/ProdBernoulliCoupling.lean) | Monotone couplings | Candidate; proof source and dependency closure still to audit |
| [ProdBernoulliBK](https://github.com/anthropics/formal-math/blob/795efb86f191735c5481675763537cfb4ff37e55/percolation/Percolation/Literature/LatticeModels/ProdBernoulliBK.lean) | Disjoint-occurrence inequality | Candidate; scope and proof closure still to audit |
| [Hypergraph.FinalCriticality](https://github.com/nitromannitol/percolation-after-anthropic/blob/a5cc72bd7627f313abbb00bcb47616678abbeb35/Hypergraph/FinalCriticality.lean) | Observed upstream criticality certificate | Upstream checked; requires a separate large compatibility integration |

## Verification commands

Run in the perclib checkout:

```sh
python3 scripts/check_import_closure.py PercLib
lake build --wfail
```

The acceptance gate is CI: the import-closure check, `lake build --wfail`, and the axiom
audit rooted at `PercLib`, which allows only `propext`, `Classical.choice` and `Quot.sound`.
Record the passing commit and run URL in the status table at the top of this file.
