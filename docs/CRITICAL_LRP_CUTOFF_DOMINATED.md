# Definition I.1.5: dominance and finite-moment transfer

`CriticalLRP/CutoffDominated.lean` proves the complete edge/probability/measure
chain from the cutoff profile dominance of Definition I.1.5 to laws and to
finite second and joint-window moments at the reduced parameter.

For an antitone profile `K`, with `K r > 0`, `K 1 > 0`, `K 0 = 0` and `r ≥ 1`,
put `ε(r) = K r / K 1`. Then

```text
0 < ε ≤ 1,  0 ≤ 1 - ε < 1, and β(1-ε) < β for β > 0.
```

`cutoffSymKernel_le_scaled` proves `J_r ≤ (1-ε)J` on every `Sym2` edge. The
scalar `cutoffProfile_dominated` applies at positive lattice distances (at least
one), and diagonal pairs vanish on both sides by `K 0 = 0`.
`bernoulliEdgeProb_cutoff_le_scaled` compares the corresponding open
probabilities, and `longRangeMeasure_cutoff_dominated` applies stochastic
monotonicity to increasing events.

The compatibility theorems identify the `Sym2` kernels with the two-variable
`KernelGeometry.cutoffKernel` and `radialKernel` away from diagonal pairs. They
do not use `cutoffPiFamily`; the latter's nonnegativity hypothesis is false for
the power-law diagonal profile, while the loop-safe `cutoffSymKernel` is zero on
loops by construction.

`modelProfile_cutoffSymKernel_le_scaled` and
`modelProfile_longRangeMeasure_cutoff_dominated` instantiate this for the source
power-law `r^{-(d+α)}`, with `ε(r) = r^{-(d+α)}` and `α > 0`.

## What follows and what remains

The uncut first moment at the reduced parameter is independent of the root, by
translation invariance. Hence a finite upstream mean makes the cutoff first
moment finite, and the already established homogeneous cubic bound makes its
second and joint-window moments finite. The fixed-root proof explicitly uses
pointwise second-moment monotonicity, then the dominating cubic estimate. The
joint-window proof gives that estimate at each site, using the proved pairwise
comparisons of uncut expected cluster volumes. The theorem therefore removes
the need for an independent second-moment input at that parameter; it does not
merely restate it.

The remaining premise is precisely **finiteness of the uncut reduced-parameter
mean**. A further wrapper,
`lintegral_clusterVol_cutoff_ne_top_of_subcritical`, accepts that mean-finiteness
for every parameter up to `β₀` whenever the reduced parameter is at most `β₀`.
It does not assert it. This remains the sharpness/susceptibility input meant by
`P_{(1−ε)β_c}` in the source. The newer `PowerLawHighTemp` module supplies a
finite mean in the explicit regime `β M < 1`, and `chi_lt_top_of_le_powerLaw`
transfers it to smaller pair intensities. This proves a genuine small-parameter
interval but does not reach `β_c(1−ε)` near the critical threshold. See
`docs/CRITICAL_LRP_HIGH_TEMPERATURE.md`.

The dominance maps use `r ≥ 1`. They should not be silently generalized to all
positive radii when quoting the paper's bounds for very small cutoffs: that
range requires an appropriate source profile convention or a separate argument.

## Boundary conditions and expanded audit

The independently rebuilt and accepted `smwxuymqb/m2` review found that the core
31-declaration chain was already integrated, so it is not claimed as new work.
Its focused build is repaired with only lexical changes; the separate audit is
now checked for all 43 declarations. The additional
`CutoffDominated.AuditExtras` lemmas establish:

* The edge comparison needs only `0 ≤ K 0` at a loop, although the Bernoulli-law
  construction still uses `K 0 = 0` for nonnegativity and for agreement with the
  radial kernel. A negative diagonal gives an explicit counterexample to the loop
  comparison as well as to nonnegativity of the uncut kernel.
* `K 1 > 0` is essential for strict domination. With `K 1 = 0`, the division
  convention makes `1 − K r / K 1 = 1`. With `K 1 > 0`, strict domination holds
  exactly when `K r > 0`; if the profile is normalized to `K 1 = 1`, the
  coefficient is simply `K r`.
* On the raw sup-norm lattice, the cutoff kernel is zero for `r ≤ 1`. Hence there
  is a radius-dependent positive coefficient for every real `r`, obtained by the
  reduction at `r ≥ 1` and by a trivial comparison at `r ≤ 1`. This is only an
  edge/domination result for the raw sup-norm, **not** a claim for every normalized
  source norm, and it supplies no moment finiteness or critical asymptotic.

The finite upstream reduced-parameter mean (`hfin`) remains **unproved**. The
threshold control `β(1−ε) < β`, `cutoffPiFamily`, and monomial-splitting were not
introduced or revived by this auxiliary extension.

## General source norms versus the raw sup-norm coefficient

The formula `ε(r) = K r / K 1` above is for the **raw sup-norm lattice**, where
all nonzero lattice distances are at least one. It is not valid for every
`SourceNormData`. `Orchestration/SourceModelNonvacuity.lean` records the audited
counterexample `Flat.flatSourceNorm`: a normalized flat box for which
`Flat.flat_dist_e1 = 1/2`. At the displayed power law,
`Flat.flat_coefficient_bound_false` refutes the raw coefficient at that point,
whereas `Flat.flat_source_epsilon_works` verifies the source's own positive
epsilon. The reduced-parameter map therefore must not be transported to an
arbitrary `SourceModelData` norm.

For the general source model, `MomentMonotonicity/SourceModelMoments.lean` proves
`SourceModelData.cutKernel_le_kernel` by `cutoffProfile_le`, without using this
coefficient. Its `SourceModelData.cutoff_mono_beta_and_le_uncut` supplies the
increasing-event, all-natural-moment, and two-point comparisons for arbitrary
normalized source norms. `Orchestration/ModelWitness/Defs.lean` constructs an
actual normalized source model and
`Witness.sourceModelData_nonempty` records its non-vacuity.

## Strict domination at an arbitrary normalized norm

The separate `MomentMonotonicity/StrictCutoffEpsilon.lean` proves the general
`SourceModelData` dominance, with positive attained lattice spacing and a proof
of positivity of the profile at each positive argument. Its radius-dependent
coefficient is `min (1/2) (K r/(2 K t₀))`, in `(0,1)`. For a nonzero lattice
length `s ≤ r`, `K s ≤ K t₀`, which gives the required strict inequality; small
radii and loops are included. The flat normalized norm still falsifies the raw
`K r/K 1` formula, but not this correctly radius-dependent construction.

`SourceModelData.exists_epsilon_domination_attained` is the strengthened current
version of the recorded `hutchcroft.i.1.5.step.subcritical`.  It yields
reduced-law stochastic domination and no infinite cluster at the uncut law at
criticality when `β_c > 0`, not finite moments.  Positivity of `K` is proved
from the actual derivative/error fields rather than assumed, including the
small-cutoff case.  The tree-graph/first-moment input for moments remains open.

## Verification

All 31 declarations compile with warnings treated as errors, and every focused
axiom check uses only `propext`, `Classical.choice`, and `Quot.sound`. These are
local checks on the integrated candidate, not upstream CI. The finite upstream
susceptibility input is explicit throughout.
