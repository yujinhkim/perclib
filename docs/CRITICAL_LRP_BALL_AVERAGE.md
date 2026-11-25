# The normalized open-triangle ball average

`Analysis/BallAverage.lean` closes `hutchcroft.i.4.2.s3` on the actual
`SourceModelData`, at any admissible normalized source norm.  The three
source definitions are in `Analysis/BallAverage/Defs.lean`:
`openTriangleNabla`, the far-distance `nablaSup`, and `ballSum`.

Let `f` be a nonnegative extended-real lattice weight.  If
`nablaSup M f 0 ≠ ⊤` and
`∫⁻ r in Ioi 1, nablaSup M f r / ofReal r ≠ ⊤`, then
`logIntegrable_openTriangle` proves finiteness of the corresponding tail
integral of the normalized ball average for the configured open triangle.  Any
normalized unit-cube constant `C` and `R` satisfying the implementation's
`R ≥ 1`, `C ≤ R`, `C² ≤ R` can be used.

The proof splits at `R = √r`, not `r/2`:

```text
r^{-d} ballSum f ≤ 2^d ((sup f) r^{-d/2} + nablaSup f (√r)).
```

The first summand is integrable because `d ≥ 1`; the second is controlled by
`u = √r`, with `dr/r = 2du/u`.  This is the reconstructed two-scale computation
in the graph.  Replacing `R` by `r/2` would leave a nonzero residual and is not
used.

For the real-valued `Analysis.LogarithmicallyIntegrable` packaging,
`measurable_normalized_ballSum_toReal` derives measurability from finiteness and
monotonicity of the ball sums, so no additional measurability premise remains.
The finite global tail also prevents a misuse of `toReal ⊤ = 0`.

This proves normalized ball-average log-integrability only.  It does not supply
the triangle diagonal bound, the tail log-integrability, the separate
`hutchcroft.a.tri.tail` decay (Kozma's square root), or either paper root.
