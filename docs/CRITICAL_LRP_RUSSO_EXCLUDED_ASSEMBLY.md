# Standardized excluded-flux and finite-window Russo assembly

Integrated from the accepted `smwu62ffl/m1` packet in
`Analysis/Cutoff/Fibre/RussoAssembly/{Defs,Main}.lean`.

The pointwise theorem `ofReal_closed_exclIncr_eq_edgeIncr` identifies the real closed-event
increment used by `cutEdgeDeriv_mul_pivotalFlux_eq_excl` with the truncated `ℝ≥0∞` edge
increment. Both ordered directions are carried explicitly. When a non-loop edge is already open,
the two endpoints are connected and both sides vanish; when it is closed, the anchor/excluded
split is exactly the ordered-pair increment. The truncated values are bounded by finite window
cardinalities, so their `ofReal`/`toReal` conversions are lossless.

For every edge `e`, `cutEdgeDeriv_mul_pivotalFlux_eq_edgeIncr` rewrites the truncated per-edge
Russo flux as `β_c (-deriv K)` times the real value of the `cutLaw`-integral of the edge increment.
Loops and out-of-range edges give zero on both sides.
`sum_cutEdgeDeriv_mul_pivotalFlux_eq_sum_pairIncr` sums this over `X.sym2` and uses the proved
ordered-pair/Sym2 fibre reindexing to give an
`X × X` excluded-increment expectation. This is a genuine finite-window identity, not an infinite
Russo derivative.

## Excluded mass and untruncated limits

`exclMass_eq_iSup_iSup_lintegral_window` expresses the excluded mass as the double supremum
over truncation and window of the corresponding ordered-pair expectation. Removing the truncation
gives `exclMass_eq_iSup_lintegral_windowSumFull`. Tonelli proves the unconditional `ℝ≥0∞`
per-edge decomposition

`E1Sign.exclMass M r = ∑' e, ∫⁻ ω, edgeIncrFull (cutDist M r) … ω 0 e ∂M.cutLaw r`.

No summability or finite moment is required for these extended-nonnegative identities.

The closed-event full-cluster limit is also proved in `ℝ≥0∞`:
`iSup_ofReal_one_sub_mul_pivotalFlux_eq_lintegral_edgeIncrFull` takes the finite-truncation
supremum to exactly the integral of `edgeIncrFull`. This unweighted statement requires a non-loop
and `dist x y ≤ r`, because outside the support the flip increment need not vanish while the
cutoff edge increment is zero. A conditional real upper bound is available when that full edge
integral is finite.

`sum_cutEdgeDeriv_mul_pivotalFlux_le_exclMass` dominates each finite-window standardized Russo
sum by `β_c (-deriv K) exclMass.toReal`, assuming `deriv K r ≤ 0` and `exclMass ≠ ⊤`.
`tendsto_sum_cutEdgeDeriv_mul_pivotalFlux` gives convergence along the cofinal diagonal
`codeWindow` sequence to that value, assuming `exclMass ≠ ⊤`; the packaged domination also
retains the sign hypothesis. These are limits of finite standardized sums, not claims of absolute
summability or a radius-uniform majorant.

## The real uncapped obstruction

`ofReal_toReal_eq_self_iff`, `pairIncrFull_eq_top`, and `not_exists_real_eq_edgeIncrFull` record
that an uncapped edge increment equal to `⊤` cannot be represented by `ENNReal.ofReal` of any real
number. Infinite far-cluster volume with the excluded pattern is a hypothesis of that obstruction;
the artifact does **not** fabricate a model configuration satisfying it. In particular, the
all-open infinite-cluster example is connected everywhere and is not itself such a configuration.
The bounded real one-edge factorization therefore cannot simply be applied to an uncapped
full-cluster moment. Appropriate almost-everywhere finiteness and dominated convergence remain
separate inputs if a real full-volume statement is wanted.

All 50 declaration audits use only `propext`, `Classical.choice`, and `Quot.sound`, with some
purely combinatorial helpers using only `propext` and `Quot.sound`.

**Not proved:** absolute summability of the real edge series, a radius-uniform degree majorant,
finite large-radius moments, the complete infinite-volume Russo derivative, local absolute
continuity, or an ODE. These results exclude no possible future derivative proof; they delimit
precisely which identity has been established and why the naive real uncapped limit is invalid.
