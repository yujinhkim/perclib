# Frozen-anchor approval record

Scope: Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1. The author has
instructed the orchestrator to proceed without further approval requests. This record documents
that delegated, noninteractive authorization; it is not a claim of independent mathematical review.

## No splitting

The two moment anchors use `NOT_SPLIT`: each source theorem and its shared constant/family remains
one joint declaration. `A` in I.1.6 is common to the moment and tail conclusions; `(A_r,A_n^*)` in
I.1.15 and their mutually inverse scale normalizations remain one joint declaration. No proof-step
conclusion is admitted into a source hypothesis.

Exact files/exports, independently elaborated with the only expected manifest-registered warning:

- `PercLib.CriticalLRP.Orchestration.SourceNorm` in `PercLib/CriticalLRP/Orchestration/SourceNorm.lean`.
- `PercLib.CriticalLRP.Orchestration.SourceModel` in `PercLib/CriticalLRP/Orchestration/SourceModel.lean`.
- `PercLib.CriticalLRP.Orchestration.theorem_I_1_6` in `PercLib/CriticalLRP/Orchestration/HighDimensionalMoments.lean`.
- `PercLib.CriticalLRP.Orchestration.theorem_I_1_15` in `PercLib/CriticalLRP/Orchestration/CriticalDimensionMoments.lean`.

The sealed definitions satisfy the source-normalized kernel and unit-ball normalization, include
homogeneity and logarithmic integrability, and preserve cutoff/uncut conventions, the exact
coefficient `(2p-3)!!`, and quantifier order. They carry no proof-hole. The theorem files each
carry exactly one authorized `DRAFT_SORRY`. Their registered provider imports do not import a draft.
No root is imported into production code.

## Independent review status: BLOCKED

The noninteractive authorization covers coding and repository administration, not a finding that every source-facing declaration is mathematically faithful. Elaboration and file hashes do not grant declaration approval, and no theorem anchor here is proved or authorized for production use.

- `theorem_I_1_6` v1 is **rejected** for declaration repair, not accepted: HD3's unguarded `(Real.log rho)^-1` is zero at rho=1 and negative below it, and the beta_c denominator has no established positivity premise. A versioned log(1+rho) candidate is isolated under `.scratch/anchor-v2/` for independent source review; it is not a registered root or a replacement.
- `theorem_I_1_15` v1 has a favorable independent 15-unit statement review, but that review is not a complete approved root: beta_c positivity is under literature review and the semantic hash closure is incomplete. No production theorem is asserted.
- Both v1 types depend on meaning-carrying helpers outside `SourceNorm.lean` and `SourceModel.lean`. The transitive semantic-import hash guard has been added and tested in `scripts/check_semantic_closure.py`; its manifest integration and independent review are not complete.
- `SOURCE-RESTITUTION GUARD OK` concerns only the pinned text artifacts. The frozen-anchor core guard is scoped to real module sources and excludes `.scratch/`/`.ultramath/` probe directories; that does not weaken validation when candidates are promoted into production.
- Independent HD-v2, beta_c, and I.4.18 repair reviews are in progress. `PROVED_MODULO` and unconditional `PROVED` remain distinct, and no declaration has been sealed as a theorem.

Counting a declaration as frozen/mechanically registered is separate from accepting it. The current draft anchors remain quarantined, with exactly `by sorry` proof bodies and no production consumers.
