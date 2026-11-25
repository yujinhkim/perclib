# Conditional logarithmic integrability of the cutoff defect

`Analysis/Cutoff/CutoffDefect/LogIntegrable.lean`, accepted from swarm `smwtvrwnn` member `m2`, assembles the actual-cut-law logarithmic-integrability consequences of the previously proved defect bounds. Hutchcroft's Lemma I.4.13 is the separate integral-transformation lemma; this package does not prove that lemma.

## Main results

- The analytic layer preserves logarithmically integrable error functions under `r ↦ h(r^c) + r^(-c)` for `c > 0`, and identifies the square-root scale in the source bound with `c = 1/2`. Comparison theorems turn eventual logarithmic or polynomial majorants into finite tail integrals of `|T(r)|/r`.
- `CutoffDefect.isLogErrorFunction_cutE1` proves that the actual signed `cutE1` is logarithmically integrable and tends to zero. Its explicit inputs are the finite uncut self-triangle, eventual finiteness of the first cutoff moment, the pointwise `LogRadialBound` with exponent `p > 1`, and measurability of `cutE1` in the radius. None of these inputs is discharged by this package.
- `exists_tendsto_intervalIntegral_cutE1_div` gives the corresponding convergent improper logarithmic integral. `logarithmicallyIntegrable_cutE1_of_powRadialBound` and `isLogErrorFunction_cutE1_of_powRadialBound` give the polynomial-decay companion.
- `sourceLogErrorFunction_cutE1` adds the local integrability clause, but only with a separate local-boundedness premise on positive compact intervals.
- `measurable_cutE1_of_measurable_stats` and `aemeasurable_cutE1_of_aemeasurable_stats` reduce the remaining radius-measurability obligation to `pairMass` and `connMass`. The mass uses monotonicity on a finite-mass tail and the ball count is monotone.

`lintegral_abs_div_cutE1_lt_top` separately bounds the extended nonnegative integral without measurability of `cutE1`, by comparison with an explicitly constructed measurable integrable majorant. This does not remove the measurability hypothesis from the Bochner-integrability or logarithmically-integrable-error-function theorems.

## What remains open

This is not a proof of the HD convolution estimates, large-radius finite first cutoff moment, measurability of `pairMass` or `connMass`, local boundedness of `cutE1`, or Proposition I.4.2 Case 3. It is a conditional assembly over the existing signed defect-rate and vanishing theorems, not a new probabilistic estimate.
