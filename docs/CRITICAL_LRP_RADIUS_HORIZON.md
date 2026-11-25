# Finite-witness horizons and one-sided event continuity

Accepted from Ultramath `smwv2c2lw`, member `m1`. Production modules:
`Analysis/Cutoff/OffCorner/RadiusHorizon/{Defs,Main}.lean`.

A `CylinderOpen A` event has a finite positive witness for each of its configurations. These are
precisely positive-cylinder-open events, not general increasing events. The horizon truncation
keeps witnesses contained in a finite edge window and has a finite-window indicator. Cofinal
monotone windows exhaust the original event, and cofinal windows can be constructed from any
enumeration of the edge set. `horizonObs` makes the horizon integrable as an ordinary cylinder
expectation.

At every positive cutoff radius the horizon mass is continuous, via finite Bernoulli products.
It increases to the actual infinite-volume event mass. Consequently an increasing cylinder-open
event is lower semicontinuous in the radius. Stochastic monotonicity of the product law gives full
**left continuity**, `tendsto_nhdsLT_real_cutLaw`, without a moment or escape estimate. Instances
cover `Connects ω x y`, touching, raw forced-open and forced-closed cluster events, and the
unweighted fixed-edge singleton pivotal flux (by subtracting the two forced masses).

These are exact one-sided results. They do **not** prove the corresponding right limit,
`hcontinf`, normalized-pivotal-mass continuity, `hGcont`, or a complete ODE.

`continuousAt_iff_uniform_tail` states the Dini-type equivalence: continuity of the limiting
function is equivalent to a small horizon tail **uniformly in the radius near the point**. The
specialization `continuousAt_cutLaw_connects_iff_uniform_horizon` names this remaining obligation
for two-point continuity. An explicit analytic counterexample shows that continuity of each
horizon function, monotonicity in horizon and radius, and pointwise convergence together do not
suffice. This is not a percolation counterexample.

For a nonnegative frozen integrand, cylinder approximation is also **equivalent** to continuity
of its real moment; the converse constructs a constant observable on the empty window. Hence the
excluded-scalar's uniform cylinder approximation is equivalent to excluded-mass continuity,
not a weaker sufficient condition whose satisfaction can be claimed without giving that
continuity.

The `NormalizedAggregate/Left` local assembly lifts these one-sided results to the full weighted
normalized pivotal mass, using only the frozen cutoff factor and the first-moment summable
envelope. With continuity of `deriv K`, it also proves left continuity of singleton flux. These
are left-limit results only, not a discharge of the remaining right-hand or two-sided hypotheses.

All 46 declarations were independently rebuilt via the generated combined audit, then checked
again after splitting into the production definition and proof modules. The only axioms are
`propext`, `Classical.choice`, and `Quot.sound`.

## Two-sided finite-moment continuation

`OffCorner/TwoPoint` subsequently provides a different, two-sided proof at every positive
radius under a finite first cutoff moment at a strictly larger radius. Its forced-edge analogue
also supplies normalized-pivotal continuity at off-corner radii, through the aggregate packet.
The horizon method therefore gives a genuinely useful one-sided result and identifies the
uniform-tail condition, while that later separate argument supplies right continuity under its
explicit moment input. No finite moment is claimed to exist without that input.
