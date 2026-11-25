# Logarithmic integrability from pointwise tail bounds

`Analysis/LogTail/Defs.lean` defines logarithmic and polynomial majorants and a
radius-indexed tail supremum. `Analysis/LogTailCore.lean` proves the analytic
comparison. `Analysis/OpenTriangleLogTail.lean` applies it to the actual
normalized source model; `Analysis/TriTailLogTail.lean` gives the plain lattice
version, and `Analysis/TailLogIntegration.lean` connects it to the polygon
additive-tail error.

For exponent `p > 1`, the paper-log substitution gives
`∫_2^∞ (log r)^(-p) dr/r < ∞`. A pointwise bound on an `ℝ≥0∞`-valued diagram
therefore controls its antitone supremum and makes its real-valued tail a
logarithmically integrable error function. Polynomial decay `r^(-a)` with
`a > 0` has the analogous conclusion. Measurability is inherited by
antitonicity; tail supremum identifications are definitional.

The theorems use **explicit pointwise bounds on the uncut critical open
triangle**, at nonzero lattice points. They do not establish the HD-convolution
estimate that produces these bounds, and do not infer the missing Kozma Gram
factorization. Real-valued bound forms explicitly require pointwise finiteness,
since `toReal ⊤ = 0`. The resulting logarithmic and polynomial tail decay is an
ordinary consequence of the pointwise majorant, not a substitute for that
factorization.

The repository's `LogarithmicallyIntegrable` predicate asks for measurability
and an integrable logarithmic tail measure, but does **not** include the paper's
additional separate local-integrability clause. Thus this is conditional
preparation for Lemma I.4.3, not the full printed lemma under (HD).
