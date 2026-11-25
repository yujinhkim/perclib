# Temperature-parameter cutoff moment transfer

`MomentMonotonicity/Temperature/Defs.lean` defines
`SourceModelData.cutMassAtBeta`, the cutoff first moment at arbitrary intensity
and vertex. `MomentMonotonicity/Temperature.lean` proves its extended-real
monotonicity and left continuity in intensity at a positive critical parameter.
The endpoint may be infinite; no finite critical mean is hidden in `toReal`.

The endpoint transfer preserves stated bounds on whole left neighbourhoods.
`cutMassAt_le_two_alpha_rpow_of_Ico` is the Lemma-I.4.9 last-line shape on
`[β_C/2,β_C)` with a common radius threshold. It yields eventual finite critical
cutoff mass from that stipulated uniform prior bound. A variant replaces the
rate-shaped bound by one finite uniform bound on the *subcritical uncut* means.

The uniform subcritical estimate and positivity of `β_C` remain explicit
hypotheses. No vanishing-percolation-probability shortcut or finite-window
inference supplies them. The package transfers first moments only and proves
neither the ODE nor asymptotics. It also proves that real-valued left continuity
of the model's `toReal` moments is equivalent to finite endpoint mass when the
subcritical values are finite, isolating why the real-only interface cannot
prove that finiteness circularly.
