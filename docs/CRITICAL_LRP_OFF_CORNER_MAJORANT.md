# Off-corner standardized incident majorant

Integrated from the independently reviewed artifacts of the exhausted run `smwu19308/m1` in `Analysis/Cutoff/OffCorner/{Defs,StrictDecrease,Degree,Flux,Nonvacuity}.lean`.  The files passed fresh strict checks and production-target builds.  Integration corrected lint and `Decidable`-instance issues without changing the principal mathematical statements.

`vertexWeight_stdEdgeWeight_le_stdDegree` proves, at every `r>0` and for every finite edge set, the uniform per-vertex bound

`vertexWeight (stdEdgeWeight r) x u ≤ stdDegree r`.

The constant is `#(ball r) * (-K'(r)) / gapFloor r`.  Its card bound is obtained by injecting incident support edges into the actual normalized source ball, not by assuming an arbitrary source norm is the sup norm.  The gap floor is the positive minimum of the positive kernel gaps on the finite set of attained support radii below `r`, defaulting to one when that set is empty.  Nonpositive gaps have zero open probability and hence zero standardized weight by `div_zero`; they do not need a positive floor.  Antitonicity yields `-K'(r)≥0`.

`abs_sMomentInfFlux_le_stdDegree_mixed` proves, for `r>0` and `r ∉ attainedRadii`,
`|flux(y,r)| ≤ stdDegree r * mixedFluxDensity r y`,
provided the mixed expectation at that radius is finite.  The previously separate degree, sign and zero-open-probability inputs are discharged here.  Off-corner is essential: if a kernel gap vanishes at a strictly shorter distance, the source profile is constant on the intervening interval, forcing `K'(r)=0` by the left difference quotients.  At an attained radius, a zero-gap edge can instead have positive derivative weight.

The files also record the honest tail-only strict decrease `K_lt_of_lt_of_tail`: the model data permit bounded flat intervals of `K`, so no unrestricted small-radius strict decrease follows.  `exists_notMem_attainedRadii_gt` supplies off-corner radii at every scale using local finiteness.  An additional finite incident-series bound handles the different `Decidable` instances explicitly rather than relying on `rfl`.

**Not proved:** finite large-radius moments, a radius-uniform majorant for the actual flux, a complete infinite-volume derivative, or an ODE. The later `UniformObstruction` module proves that bounded compact *pointwise* majorants of `stdDegree` fail at every attained tail radius and that the proposed power-law majorant is false. A separated-radii bound is available instead. This is not a non-integrability theorem; see `CRITICAL_LRP_OFF_CORNER_UNIFORM_OBSTRUCTION.md` for the exact distinction.
