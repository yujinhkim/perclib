# Tail truncation at the source cutoff (Proposition I.4.15, route 3)

`Analysis/Route3` proves the probabilistic estimate behind the comparison between
the first and second cluster moments. It does not prove Proposition I.4.15 or
its asymptotic second-moment formula.

The generic `Analysis.Route3.cube_lintegral_le_of_tail` theorem concerns a
probability space with a measurable, integer-valued random variable `X ≥ 1`.
If its upper tail is bounded by `C / √n`, it proves in `ℝ≥0∞` that

```text
(∫⁻ X)^3 ≤ (4C + 1)^3 ∫⁻ X².
```

Layer-cake summation separates indices `n ≤ N` from the rest. The low terms
are bounded by `2C √N`; Markov's inequality gives the high terms by `m₂/N`.
The optimizing cutoff is `⌈(m₂)^(2/3)⌉`, with `m₂ = ∫⁻ X²`. Positivity,
measurability and infinite-moment cases are handled explicitly; there is no
conversion of an infinite integral to the real number zero.

The source cutoff specialization `cutMoment_one_cube_le_two_of_tail` uses the
actual cluster volume `|K₀|`, whose extended-natural value is either finite or
`⊤`. Finite-volume domination is **proved** by the monotone coupling at
positive radius (`cutLaw_tail_le_criticalLaw`), not assumed.

The remaining model input is only the infinite-volume critical upper tail
`P_{β_c}(|K| ≥ n) ≤ C / √n`. The paper obtains it under the triangle condition
from its cited external results. This module does not prove that tail bound.
The cutoff-to-uncut comparison is established, but a critical-tail theorem,
uniform power-law rate, or full second-moment asymptotic is not claimed.
