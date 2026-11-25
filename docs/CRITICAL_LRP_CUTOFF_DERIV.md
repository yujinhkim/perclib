# Cutoff edge and mass derivative interfaces

`Analysis/Cutoff/Deriv/Defs.lean` defines the actual off-corner edge-derivative
weight at an arbitrary `SourceNormData`. `Analysis/Cutoff/Deriv.lean` proves the
corresponding edge derivative, finite-window Russo formula, two-point
slope, and a conditional mass derivative with a summable radius-uniform
per-vertex majorant.

The diagonal loop edge is handled separately. Off-corner derivatives use the
source slope `deriv M.K`, not a fixed power-law coefficient. Finite-window
identities correctly evaluate to `M.cutTwoPoint` and their finite sums.

For the infinite cutoff mass the remaining inputs are explicit: summability
of edge weights with bounded-observable expectations, interval integrability
and measurability/continuity of window fluxes, local first-moment finiteness,
and a summable bound uniform in radius on every per-vertex flux. This is much
stronger than a total first-moment estimate. It is precisely the missing
standardized derivative-to-flux interchange, not a disguised replacement for
it. The mass-transport and ODE algebra in `Cutoff/FluxODE` is the consumer,
not a completed proof of the infinite derivative or Case 3.
