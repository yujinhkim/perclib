# Finite entropy ingredients for the two-intensity comparison

`Analysis/SecondMomentCase3/CriticalVolumeTail/Entropy/Bernoulli` defines the
finite weighted Bernoulli model on configurations `E → Bool`, with
$p_e=1-\exp(-\beta J_e)$, and proves normalisation and the exact finite-cylinder
mass identity. Positive edge weights and intensity give strict pointwise
positivity via `bem_pos`. There is a single shared `LRP.openProb` definition,
also used by the entropy module.

`Entropy/Pinsker` proves the finite log-sum inequality and its binary
Kullback–Leibler comparison
$$(a-b)^2\le2\max(a,b)\,\operatorname{bkl}(a,b),$$
including endpoint handling on the first parameter. General nonnegative
log-sum is used on an event and its complement to derive the interior
finite-probability sharpened Pinsker inequality. A one-edge example instantiates
`1-\exp(-\beta J_e)$ at two intensities, so that comparison is inhabited. The
proofs use explicit derivatives and monotonicity of comparison functions, not
a relative-entropy axiom or invocation of the final tail estimate.

The coefficient and direction agree with
[arXiv:2106.06400, Theorem 3.1 and its generalised Pinsker discussion](https://arxiv.org/html/2106.06400#S3.Thmthm1).
This makes them inputs to the cited decision-tree comparison. They do not prove
that comparison. Still missing are the per-edge exponential relative-entropy
bound, the transcript chain rule, the revealment estimate, and their final
assembly into `TwoIntensityTailComparison`. The separate susceptibility bound
and the critical tail remain as they were: explicit names, not derived facts.

The submitted candidate duplicated `openProb` across two files. Integration
keeps one canonical definition, removes unnecessary positivity premises from
the pure normalisation identity, and repairs deprecated names, typeclass scope,
and individual no-op tactics without weakening the analytic statements. Both
integrated files have passed strict shared-model elaboration and have no
nonstandard axiom dependencies.
