# Logarithmic errors from the source normalizations

`Analysis/BallRatioLogError.lean` completes the algebraic and analytic content of
`hutchcroft.i.4.g9` for `SourceModelData`.

## Product closure

For an arbitrary-sign logarithmic error `δ` and a measurable `η` bounded by
`c/r` eventually, `isLogErrorFunction_mul_of_denominator_bound` proves that
`δη` is again a logarithmic error. The proof uses `δ → 0` to obtain an eventual
bound on `δ`, and the denominator comparison for `η`; neither sign nor a finite
cluster moment is required.

`isLogErrorFunction_one_sub_mul_of_denominator_bound` expands

```text
1 - (1 + δ)(1 + η) = -δ - η - δη
```

and proves that the complementary product error is logarithmically integrable.
The existing negation/subtraction API alone did not cover this second-order
product term.

## Actual normalized ball ratio

`SourceNormData.finite_ball` proves finiteness of integer lattice balls from the
cell-packing API. Positive outer radii use the unit-volume scaling identity;
the remaining case is contained in the singleton `{0}`. This gives monotonicity,
hence measurability, of the normalized ball count. No false claim that the count
depends only on `⌊r⌋` is used.

`SourceModelData.ball_ratio_error_bound` applies the proved Lemma I.4.6,
`|B_r| - r^d = O(r^{d-1})`, to obtain measurable relative error bounded by
`C/r`. Thus the product

```text
(1 + δ_r) (|B_r| / r^d)
```

has exactly the source's `1 + δ_r + O(1/r)` form.
`SourceModelData.isLogErrorFunction_one_sub_mul_ball_ratio` proves that its
complementary error is logarithmically integrable. This is the provider for
`i.4.g9`, with the source's arbitrary admissible normalized norm and unchanged
Lemma-I.4.6 dependency. An instantiation at the concrete source-normalized
power law with `δ ≡ 0` is checked in the same module.

This does **not** prove the probabilistic `E₁,r` estimates, finite critical
moments, `r0(β) < ∞`, Proposition I.4.2, or either paper root. The root
registration remains `DRAFT_SORRY`, and graph topology remains `PROPOSED`.
