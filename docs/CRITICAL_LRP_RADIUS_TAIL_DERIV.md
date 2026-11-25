# Tail derivative comparison for the off-corner mass

Accepted from Ultramath `smwuinbxz`, member `m4`. Production module:
`Analysis/Cutoff/OffCorner/RadiusTailDeriv.lean`.

The source's existing `exists_deriv_bounds` supplies `(1/2) r^p ≤ |K'(r)| ≤ 2 r^p` past a
positive threshold `R`, with `p = -d-α-1 < 0`. The new `deriv_K_neg_of_tail` combines its lower
bound with `K'(r) ≤ 0` to prove `K'(r) < 0`. `neg_deriv_K_le_of_tail` uses antitonicity of the
negative real power to bound `-K'(r) ≤ 2 a'^p` for `R < a' ≤ r`. No derivative-continuity premise
is introduced. `neg_deriv_K_window_sandwich` gives the corresponding two-sided bound on a compact
window.

These bounds specialize the interior-scale envelope and its total-pivotal-weight integrability
theorem. `intervalIntegrable_pivotalWeight_of_tail_window` supplies `hboundint` throughout an
off-corner `Ioo α β` when `R < α` and the second moment at `β` is finite. In
`hasDerivAt_cutMassReal_rhsScalar_of_endpoint_of_tail`, the generic derivative-bound, comparison
sign, positivity, and differentiability premises are discharged. The threshold-existential form
`exists_tail_hasDerivAt_cutMassReal_rhsScalar` obtains `R` from `exists_deriv_bounds`.

The result is explicitly tail-specific: the upper bound becomes unbounded as the left endpoint
approaches zero. It retains the finite second cutoff moment at the endpoint, the off-corner
premise, `hcontinf`, and `hGcont` verbatim. It proves no large-radius cluster moment, no
infinite-volume flux continuity, no corner statement, and no complete ODE.

`OffCorner/RadiusSummedFlux` additionally combines this tail result with the scalar closed form
of the vertex sum. Its `_of_endpoint_of_tail_of_scalar` wrapper replaces explicit summed-flux
continuity by continuity of `K'` and excluded mass; these remain inputs, not proved consequences.

All eight new declarations were independently rebuilt with the strict project flags. Their only
axioms are `propext`, `Classical.choice`, and `Quot.sound`.
