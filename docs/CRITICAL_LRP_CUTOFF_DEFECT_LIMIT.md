# Signed vanishing of the actual cutoff defect

`Analysis/Cutoff/CutoffDefect/Defs.lean` names `CutoffDefect.cutE1` at the actual
range-truncated critical law, with `pairMass`, `connMass`, and ball cardinality
from the configured source model. `CutoffDefect/Limit.lean` proves the two-scale
rate, sign, signed vanishing, and positivity of `1-cutE1`.

It also identifies `BallAverage.openTriangleNabla` with the literal
`TriTail.openTriangle` and the normalized tail supremum with `M.nablaTail`, so
its decay inputs are about the source's actual open triangle. Windowed triangle
finiteness follows from finite pointwise triangle mass rather than being an
assumed technical wrapper.

The main hypotheses are finite triangle mass, eventual finite first cutoff
moment, and a suitable tail condition: radial decay, pointwise logarithmic or
polynomial decay of the uncut triangle, or an explicitly summable Cesàro-type
alternative. The first finite-moment condition and the HD/convolution estimate
remain separate. The package does not prove the mass derivative or ODE, Case 3,
or logarithmic integrability of `cutE1`; the last would need radial
measurability of the joint and connected window moments as well.
