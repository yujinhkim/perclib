# Kernel-factor decomposition of off-corner flux

Recovered locally from the abandoned `smwuinbxz/m3` counterexample search. The counterexample
itself was **not** found or accepted. This separate algebra-and-regularity packet was independently
reviewed and rebuilt before integration. Production files:
`Analysis/Cutoff/OffCorner/KernelFactor/{Defs,Main}.lean`.

`cutKernelFactor = β_c (-K'(r)) exp(β_c K(r))` factors out the common radius-dependent part of
activated cutoff edge weights. `cutPivotFactor` is `exp(-β_c K(d))` on activated non-loop edges
and zero elsewhere. `normalizedPivotMass` sums that factor against the infinite-volume singleton
pivotal flux. The exact identities factor each edge weight and each infinite singleton flux; no
summability of the original flux series is needed for this scalar-factor rearrangement.

At positive radii, continuity of `deriv M.K` supplies continuity of the kernel factor. With
`β_c ≠ 0`, continuity conversely transfers back from the factor to the derivative, using
`M.K_diff` for continuity of `K`. Continuity of normalized pivotal mass therefore, with kernel
regularity, gives a sufficiency theorem for per-vertex and summed flux continuity. The endpoint
wrapper `_of_envelope_of_kernelC1` consumes these inputs while retaining envelope bounds,
off-corner data, and finite endpoint second moment.

The **necessity** results are deliberately conditional: flux continuity gives derivative
continuity only when the relevant normalized pivotal mass is also continuous and nonzero there,
and `β_c ≠ 0`. They do not show that `hcontinf` alone forces `K'` to be continuous, nor that
normalised mass cannot cancel a kernel discontinuity. `normalizedPivotMass_nonneg` and positivity
from a single positive summand are proved separately. The individual cutoff edge jump at an
attained distance is also explicit, and is not confused with discontinuity of the infinite flux.

No normalized-pivotal-mass continuity, excluded-mass continuity, derivative continuity,
per-vertex or summed flux continuity, large-radius moment, full ODE, or explicit counterexample
is supplied. All 22 proof declarations compile with strict flags and use only the standard
axioms; the three definitions are covered by the production axiom audit.
