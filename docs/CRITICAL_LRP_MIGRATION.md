# Critical long-range percolation migration

This branch migrates the source project identified in every `CriticalLRP` file
header, at integration revision
`3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf`. It does **not** claim that the
104-page source paper is completely formalized. The retained statement audit is
in [CRITICAL_LRP_COVERAGE.md](CRITICAL_LRP_COVERAGE.md); it classifies the source
items as 15 FULL, 42 PARTIAL and 18 NOT FORMALIZED. It is not a fresh fidelity
review of the migrated declarations.

## Interface migration

The canonical countable-product model uses native PercLib:

- configuration type: `PercLib.Percolation.Bond.Config`;
- law: `PercLib.Percolation.Bond.law` (through the compatibility abbreviation
  `edgeMeasure`, not a competing product-measure definition);
- graph and cluster: native `openGraph` and `cluster`;
- connection: reachability in the native open graph, with explicit bridges to
  native `conn`;
- volume: the native cluster's `encard`, coerced to `ℝ≥0∞`.

`edgeMeasure_eq_infinitePi` proves the transported finite-product representation
once. Subsequent cylinder, permutation and ghost-coupling results use that
identity explicitly. Native finite-witness and tail-limit theorems are used in
`LRPTailBridge` and `LRPTailBounds` rather than duplicating the associated
definitions.

The older edge-labelled `BondGraph` development used by the generalized BK
arguments is not indiscriminately replaced by the complete-graph bond interface:
it is a separate generalized model. Finite-graph cluster definitions likewise
remain separate from the infinite-volume canonical cluster.

The real-volume results keep the explicit tail-or-infinite-event workaround.
They do not assume that `ENNReal.toReal` is monotone at infinite volume and do
not discard its infinity behavior.

Some important target-paper results remain conditional on their stated moment,
band, coupling, restoration or sharpness inputs. In particular, the I.3.1
package is not a proof of the complete critical high-dimensional Proposition
I.3.1. The Russo infinite-volume local-uniformity inputs must not be mistaken
for a complete proof of Lemma I.4.1 or for sharpness of the phase transition.

## Current local checks

The migration has been checked in this checkout with:

```sh
lake build --wfail
python3 scripts/check_import_closure.py PercLib
python3 scripts/test_manifest.py
python3 scripts/test_proof_pr.py
```

The successful results on the working tree were 9,433 build jobs, all 386 PercLib
modules in the root import closure, 17 passed manifest tests and 5 passed
pull-request-policy tests. The real raw manifest extractor produced 8,717
declaration records; their reported axiom sets were restricted to `propext`,
`Classical.choice` and `Quot.sound` (with no additional axiom dependencies).
These are local checks, not a CI run on a pushed commit. Full manifest generation has not completed because `node` is unavailable in the
VM: `scripts/build_manifest.py` fails with `FileNotFoundError` when it invokes
Node. Passing its Python tests and extracting the raw manifest are not presented
as a full manifest build.

A comment-aware scan of all migrated Lean modules found no `sorry`, `admit`,
`native_decide` or extra `axiom` syntax. Declaration-level `#print axioms`
checks cover the principal declarations reported in the migration handoff.
Conditional hypotheses in a theorem's statement are mathematical input, not
proof that the corresponding source result has been established.

Source and licensing records are in `third_party/critical-lrp/NOTICE.md`. No
old PercLib snapshot, paper attachments, source notes or `.ultramath` workspaces
are part of this migration.

## Review and PR scope

The complete import tree is a large migration, not a theorem-only change.
PercLib's contribution rules distinguish carefully between small interface PRs
and proof-only PRs and review definitions, non-vacuity witnesses, stated inputs
and source fidelity. Opening a fork-internal PR would not address that review or
Tom Hutchcroft's `main`.

The intention is a cross-fork comparison from
`yujinhkim/lrp:critical-lrp-1` into
`tomhutchcroft/lrp:main`. The upstream PR description should preserve these
limitations and should not report success until its actual CI run is green.
