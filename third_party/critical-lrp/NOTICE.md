# CriticalLRP migration: sources and third-party notices

The `PercLib/CriticalLRP/` modules were migrated from
<https://github.com/yujinhkim/Critical-Long-range-percolation> at integration
revision `3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf`. Migration changes include
namespace and module-system conversion, Elan/Mathlib compatibility fixes,
use of native PercLib bond percolation definitions, and associated proof repairs.

PercLib Lean sources and tooling are contributed under Apache License 2.0.
`PERCLIB_LICENSE.txt` retains the Apache licence of the original bundled
`tomhutchcroft/lrp` Lean sources, and `PERCLIB_NOTICE.md` retains its source
notice. The obsolete bundled PercLib snapshot is not copied into this branch:
current native PercLib definitions and proofs are imported instead. That
snapshot was identified as revision
`3c0755b692bb6fa71ff6521ce423948feae4fe40`.

No source paper PDF, lecture notes or wiki prose is copied. In particular, the
original PercLib notice identifies those materials as all rights reserved.

## OpenAI mathematical code

The migrated `BK/Graph.lean` and `BK/Association.lean` include adapted material
from <https://github.com/openai/math>, commit
`4eaee87548250b2682affda7d05d947c05554bae`:

- `lean/OAI/Probability/UnimodularPercolation/Graph/Basic.lean`
- `lean/OAI/Probability/UnimodularPercolation/ProductMeasure/Association.lean`
- related tail-product proof ideas in `CountableProduct/ZeroOne.lean`.

The upstream material is Apache License 2.0; its licence is retained here as
`OPENAI_MATH_LICENSE.txt`. Module layout, namespaces and some statements were
changed during the original formalization and again during migration.
File-specific notices remain in the modules. No correspondence between the
migrated statements and the source paper is inferred from compilation alone.

## Mathematical source, not a bundled proof

The finite-spanning-tree construction in `Tightness/TreePieces.lean` follows the
partition method of Tom Hutchcroft's *Power-law bounds for critical long-range
percolation below the upper-critical dimension*, arXiv:2008.11197v2, Lemma 2.4.
The formal statement is modified to rooted pieces containing between `lam` and
`2 * lam - 1` marked vertices; it is not that source lemma verbatim and does not
prove universal tightness by itself.

The mathematical target is Hutchcroft, *Critical long-range percolation I:
High effective dimension*, arXiv:2508.18807v1. The paper has not been completely
formalized. See `docs/CRITICAL_LRP_COVERAGE.md` for the retained 75-item source
coverage ledger and its qualifications.
