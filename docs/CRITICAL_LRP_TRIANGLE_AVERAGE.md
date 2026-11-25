# Triangle-ball averages and the uncut defect

`Analysis/TriangleAverage/Defs.lean` fixes the open threefold convolution
weight, normalized balls, critical uncut susceptibility, two window moments,
and the real source defect `cE1`. `Analysis/TriangleAverage.lean` contains the
proofs. These objects are at the **uncut** critical law; they are not silently
reinterpreted as the finite-cutoff model.

## Proven estimates

`normalized_ballSum_le_two_scale` converts the landed two-scale inequality to
real-valued form under finite pointwise sup mass. Eventually,
`r^(-d) Σ_{x∈B_r} f(x)` is bounded by
`2^d ∇_0 r^(-d/2) + 2^d ∇_(sqrt r)`.
Consequently `tendsto_normalized_ballSum_toReal` proves that this normalized
ball sum tends to zero when the pointwise sup is finite and the spatial tail
sup tends to zero. No summability of `f` is used.

`summable_kernel_cesaro_tendsto_zero` gives the separate elementary statement
for a globally summable weight and expanding finite windows.

`defect_le_normalized_ballSum` applies the landed finite-moment Lemma I.4.11
to these uncut model fields. `defect_le_two_scale` supplies the resulting
quantitative upper bound, `defect_upper_tendsto_zero_of_tail` gives eventual
upper bounds by each positive epsilon, and `defect_posPart_tendsto_zero_of_tail`
proves convergence of `max 0 E1` to zero.

## Remaining inputs and scope

The defect statements retain finite uncut critical susceptibility, finite joint
window moments, and finite pointwise triangle mass as hypotheses. The tail
limit of the open triangle is also a premise. These are not discharged here;
in particular, finite total triangle mass is not a route around critical mean
divergence. `suscept_le_triMass` records the diagonal bound `χ_βc ≤ Σ_y ∇(0,y)`
without assuming the unproved full factorization identity.

The sign `0 ≤ E1` is not supplied for this uncut formulation. Therefore this
module proves an upper/positive-part limit, **not** a two-sided limit of the
signed defect. It does not prove Kozma's theorem, a raw-sup-norm-to-source-norm
cutoff bridge, source cutoff finiteness, the actual cutoff ODE, or Case 3.
