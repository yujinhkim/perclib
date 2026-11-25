# Shifted-log source-norm Case 3 tail

Integrated from the accepted `smwu4e7s3/m1` packet in
`Analysis/OpenTriangle/Case3SourceNorm/{Defs,Main}.lean`. These are theorems about the explicitly
repaired `log (1 + ρ)` input, **not** the literal printed `log ρ` hypothesis. Printed HD3 and its
separate proof in `Case3SrcNorm` are unchanged.

`Case3ShiftedBound M C` requires, at every nonzero displacement,

`M.twoPoint M.betaCrit x y ≤ C * (Real.log (1 + ρ))⁻¹ * ρ^(-4)`,

where `ρ = M.S.ρ (toVec (x - y))`. `HDCase3Shifted M` adds `M.d = 6`, `M.α = 2`, and existence of
`C > 0`. Neither predicate is claimed to generate or be equivalent to `Orchestration.HD M`.
`case3ShiftedBound_of_printedBound_shell` records only the one-way comparison on `ρ ≥ 2`, where
printed domination implies shifted domination with constant `2C`. No non-vacuity assertion is made
for a prescribed model.

The input comparison proves, for `0 < c ≤ 1` and `s ≥ 1`,

`log (1 + s) ≤ logShiftConst c * log (1 + c*s)`.

The proof covers both `s ≤ 2/c` and `s ≥ 2/c`, so intermediate normalized-norm shells are not
skipped. `HD_to_supNorm_case3Shifted` uses this with `srcLowerUnit` and its negative fourth power
to produce exactly the sup-norm shell hypothesis of `Case3Literal`. On the output side,
`logUpperConst` and `srcUpperConst` convert the square-logarithmic pointwise bound back to the real
source radius `M.S.dist 0 y`; their contribution is squared in `case3SrcConst`.

The main results are:

* `openTriangle_toReal_le_logMajorant_case3Shifted` and
  `openTriangle_ne_top_case3Shifted`: pointwise square-log decay and finiteness;
* `logRadialBound_openTriangle_case3Shifted`: the same bound at the source radius;
* `nablaTail_le_logMajorant_case3Shifted` and its real-valued form: explicit tail bounds;
* `tendsto_nablaTail_zero_of_HD_case3Shifted`: vanishing of the extended-real source tail;
* `isLogErrorFunction_nablaTail_of_HD_case3Shifted` and
  `isLogErrorFunction_nablaTail_of_HDCase3Shifted`: logarithmic integrability and convergence to
  zero of `(M.nablaTail r).toReal`;
* `case3SourceBridge_shifted`: the packaged bridge retaining all of these conclusions.

All 25 theorem reports in `Main.lean` use only `propext`, `Classical.choice`, and `Quot.sound`.
Independent fresh builds of `Defs`, `Main`, and the statement inventory passed the strict flags
with no warnings. A text-restitution check compared these proofs with the independently reviewed
original packet.

This is a conditional auxiliary theorem about the repaired hypothesis. It adds no coverage claim
beyond the literal printed Lemma I.4.3 established in `Case23`, and proves no HD domination,
Kozma/Gram factorization, critical operator, moment existence, Russo derivative, or ODE.
