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

## Per-edge exponential-parameter estimate (subsequent result)

`Entropy/PerEdgeKL` proves source Lemma 3.3, equation (3.4):
$$D_{KL}(\operatorname{Ber}(1-e^{-a})\|\operatorname{Ber}(1-e^{-b}))
 =D_{KL}(\operatorname{Ber}(e^{-a})\|\operatorname{Ber}(e^{-b}))
 \le\frac{(a-b)^2}{2\min\{a,b\}},\qquad a,b>0.$$
The complement identity `bkl_one_sub` and the two-sided monotonicity proof are
formal. `bkl_openProb_le` specializes the estimate to the shared one-edge model
for $0<\beta_1\le\beta_2$ and $J_e>0$. This unweakened per-edge input is the
appropriate complement to Pinsker, which bounds divergence below rather than
above. Transcript chain algebra, revealment, and final tail assembly remain open.

## Finite transcript chain rule and assembly

`Entropy/TranscriptKL` models a fresh-query plan of fixed finite depth. It
recovers exact fibre probabilities from the normalized product law, then derives
the chain rule with the outer expectation at the **lower intensity** $\beta_1$.
This is the orientation used by source equation (3.5), not a generic invocation
of relative entropy. `Entropy/TranscriptEntropy` instantiates its per-edge input
with the proved lemma, yielding `kl_le_unconditional` for the finite plan.

`Entropy/TailAssembly` extends generalized Pinsker to degenerate event masses,
proves the exact finite tail-sum identity $E[\min(|K|,n)]
 =\sum_{k=1}^n P(|K|\ge k)$, and assembles the finite and countable versions of
the source's tail comparison from named transcript-entropy and revealment
inputs. It supplies precisely the next interface for the remaining exploration
proof. These results do **not** formalize the infinite transcript limit,
cluster-computed-event construction, infinite susceptibility, or canonical
two-intensity comparison. The separate finite exploration/revealment theorem
is documented in [the revealment note](CRITICAL_LRP_REVEALMENT.md).
