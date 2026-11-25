# Cutoff-radius measurability and window-flux continuity caveat

Recovered from the abandoned `smwuges40/m5` artifact, with production rebuild, public-module
structure, and statement/axiom checks. Modules:
`Analysis/Cutoff/OffCorner/RadiusMeasurability/{Defs,Main}`.

`monotone_cutProb` proves the cut open probability is monotone on all of `ℝ`, using the vanishing
nonpositive branch. Monotone maps of increasing events then give a measurable real function of
`r`. Forced open and forced closed configurations of the finite-window cluster indicator are used
to express each pivotal flux as the difference of two such increasing-event probabilities.
Together with `measurable_cutEdgeDeriv`, this gives `measurable_windowFluxOf_singleton` and
`aeStronglyMeasurable_windowFluxOf_singleton`: the `hmeasK` premise for all finite windows, with
no moment hypothesis or radius-uniformity claim.

The package also gives `stronglyMeasurableAtFilter_sMomentInfFlux`: measurability-at-filter of
the infinite singleton flux at an interior point, using `truncate-to-sum` conversion at finite
first cutoff moment. This is not a continuity theorem. An alternative independent `m1_...`
lemma derives measurability-at-filter through the landed `tendsto_windowFlux` from `hmeasK`.

Crucially, `cutEdgeDeriv_at_dist` shows an individual cutoff edge weight jumps at an attained
edge length whenever the pivotal flux is nonzero. In `windowFluxOf`, `cutFun` makes this jump
visible, so one cannot prove continuity by uniform convergence of these window fluxes. The
precision of this counterexample is why `hcontinf` and `hGcont` are left open here, not inferred
from a formal measurability result.

The derivative wrapper `hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_measurability`
discharges `hmeasK` and the other existing endpoint/scalar hypotheses. Its `hboundint` input is
supplied separately by `RadiusPivotalWeight.intervalIntegrable_pivotalWeight_of_envelope` and
the endpoint wrapper there, under a local bound on `-K'` and a negative derivative at the
comparison radius. The extra envelope data is retained explicitly. Per-`y` flux continuity
`hcontinf` and summed-flux continuity `hGcont` remain open, as do large-radius moments. No
complete ODE or corner statement is implied.

The 19 theorem audits on `Main` use only `propext`, `Classical.choice`, and `Quot.sound`; the
four event constructions in `Defs` are covered by the production axiom audit.
