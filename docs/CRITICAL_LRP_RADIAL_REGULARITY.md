# Radial and first-moment inputs of Case 3

`Analysis/SecondMomentCase3/RadialRegularity` removes several wrapper-specific
inputs from the direct Case-3 product-gap consumer. This is a reduction of the
remaining model obligations, not a canonical-model instantiation or a proof of
I.4.20.

## Exhausting windows and AC/AE derivatives

`Defs.lean` constructs a monotone exhaustive family of finite subsets of any
countable nonempty type, hence of `Sym2 M.V`. This family was bookkeeping in
`SecondMomentCornerIdentity`, not a model assumption.

`ACAE.lean` then applies the already-proved corner identity and interval FTC.
`ac_and_ae_toReal_two_farTail` gives a radius above which, on every later tail,
finiteness of the cutoff second moment supplies both the interval absolute
continuity and almost-everywhere derivative with actual right-hand side
`M.rhsScalarTwo`. The consumer versions remove `hac`, `hae`, `hmR`, `h1`, and
the `E₂`/normalized-error measurability hypotheses by deriving each from the
second-moment tail or from Proposition I.4.2.

## First-moment source package

`FirstMomentSource.lean` proves the first-moment package with the following
changes rather than weakening statements:

* `cutMoment 1` and `cutMassAt` finiteness follow from `cutMoment 2`;
* `cutMassReal → ∞` follows from the uncut critical mean being infinite;
* the truncated-law defect and its bounded vanishing limit follow from the
  triangle condition plus the open-triangle radial log bound;
* the vertex/edge exhaustions and both kernel-tail bounds come from
  countability and `M.exists_deriv_bounds`;
* `α > 0` is read from the source structure itself.

Hence `case3_firstMoment_inputs_of_triangle` and the fully reduced
`case3_firstMoment_inputs_of_source` derive exactly `hP`, `hlogH`, and `hlogE0`.
The first two host the first-moment asymptotic and logarithmic error of
Proposition I.4.2. There is no truncation, `toReal ⊤ = 0`, or invented finite
critical first moment involved.

## Combined Case-3 interfaces

`secondMoment_asymptotic_case3_p21_hP_discharged`,
`regularlyVarying_two_p21_hP_discharged`, and the combined
`secondMoment_asymptotic_case3_p21_of_model` (plus its regular-variation
counterpart) preserve the direct product-gap conclusion. `case3_hAend_hAmid_cutPoly_source_hP_discharged`
passes the same first-moment package to the direct I.4.20 ratio-limit input,
retaining its finite-higher-moment, homogeneity, polygon, tail and denominator
hypotheses.

The retained inputs are explicit: tail finiteness of the second moment, the
moment gap, triangle and open-triangle radial-tail conditions, the uncut
critical mean being infinite, and continuity of the pair flux, `K'` and the
excluded scalar on a radius tail. The frequency/asymptotic data and the
exhausting sets are derived rather than assumed. No claim is made that those
retained packages are jointly instantiated by the canonical critical model,
that the critical tail or triangle condition has been proved, or that
Proposition I.4.20 / Cases 1–2 of I.4.15 are complete.

## Subsequent tail-only and HD(3) reductions

`I420Connect` and `TailRoute` now expose the Case-3 regular variation in the
higher-moment `momOf` vocabulary. The repaired bundle needs only vanishing of
`∇_r`, not the pointwise log-radial bound; its driver becomes logarithmically
integrable from logarithmic integrability of `∇_r` by Lemma I.4.19. The
`p = 3` connector derives its `hRV2` premise from this chain. Its other I.4.20
inputs are unchanged.

`TriangleFromHD` independently derives a finite triangle and the logarithmic
tail from the literal HD(3) premise. This does not instantiate HD(3) itself.
The other reductions and their exact limitations are collected in
[the Case-3 reduction note](CRITICAL_LRP_CASE3_REDUCTIONS.md).


## Corner-sensitive flux continuity

`CornerContinuity` redirects the remaining radial-continuity investigation. The
cutoff derivative coefficient vanishes on the left of an attained radius and is
generically nonzero at and to its right, so it has a jump there. It is
continuous away from attained radii under continuity of `deriv K`. The attained
set is unbounded and countable.

This does not prove that the whole summed flux is discontinuous. For the
corrected corner-free and almost-everywhere continuity statements, continuity
of each pivotal summand plus a locally summable dominator is sufficient. These
remain explicit hypotheses. The monotone-window Dini reduction identifies the
missing quantity as a radius-uniform window tail, not mere pointwise
convergence. See [the corner note](CRITICAL_LRP_RADIAL_CORNERS.md).
