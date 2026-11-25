# Standardized flux and ODE assembly

`Analysis/Cutoff/FluxODE/Defs.lean` defines the standardized pivotal weight,
root-anchored excluded sum, binomial increment weights, and the two source
errors. `Analysis/Cutoff/FluxODE.lean` proves mass transport and the algebraic
handoff to the source ODE.

The paper double sum is reindexed by covariant translation on the actual
truncated law and Tonelli's theorem to equal `E1Sign.exclMass`. This proof is
valid even at infinite clusters because no extended-real subtraction is taken.
The general binomial transport preserves the real-weight convention of the
paper, with finite-cluster compatibility specialized to `p = 1`.

Under finite second cutoff moment, the flux agrees with
`pairMass - connMass` and with `|B_r| χ(r)^2 (1-E1)`, giving exactly the source
ODE when multiplied by the normalized derivative. `cutE0 → 0` is derived from
the source derivative error and normalized ball count.

The analytic part remains: `HasDerivAt` of the actual cut mass and the identity
between its derivative and this standardized flux. Second-moment finiteness,
positivity of `β_C`, and critical divergence remain premises of the final lower
comparison. Standardization through the `1-q_e` factor of the literal edge
profile is explicitly not claimed, so this is not yet the actual ODE or Case 3.
