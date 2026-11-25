# Exact witness radii and the closed-cutoff empty regime

Production: `Analysis/Cutoff/OffCorner/SourceWitnessSmallRadius.lean`.

For any source norm which is a positive scalar multiple of the lattice sup norm,
`SourceNormData.attainedRadii_eq_mul_nat` proves that the attained radii are precisely the
positive scalar multiples `c * n` for natural `n ≥ 1`. Axis vectors realize every
multiple. At the explicit witness with scale `2`, this gives
`attainedRadii = {2 * n | n ≥ 1}`, including attainment at `2`.

More generally, if all distinct lattice points are at source distance at least `c`, then
`SourceModelData.cutKernel_eq_zero_of_separated` proves that the closed cutoff kernel
vanishes at every `r ≤ c`: longer edges lie outside the cutoff, while at `r = c` a
critical pair has profile `K(c)-K(c) = 0`. Loops are absent by `radialSym`.
Consequently `cutLaw` is the Dirac law at the empty configuration and every cutoff
moment is exactly `1`.

At the literal witness this yields:

- `cutKernel_eq_zero_of_le_two` for **all** `r ≤ 2`, not merely `r < 2`;
- `cutLaw_eq_dirac_empty_of_le_two`;
- `cutMoment_eq_one_of_le_two` and finiteness of every cutoff moment;
- an input-free normalized-pivot continuity statement at `0 < r₀ < 2`.

The `r ≤ 2` result uses the actual continuous cutoff profile with closed convention
`s ≤ r`. It is not a replacement of that profile by a hard truncation or by the uncut
kernel, where the boundary weight would be nonzero. The elementary percolation content
is deliberately non-asymptotic and does not supply moments, derivatives, or nontrivial
cluster behaviour at larger radii. All 19 theorem axiom reports from the reconstructed
audit contain only `propext`, `Classical.choice`, and `Quot.sound`.
