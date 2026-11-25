# The radius threshold from the sharpness asymptotic

`Analysis/SubcriticalRadius.lean` proves the final threshold-existence step
`hutchcroft.i.4.g6` used in Proposition I.4.2.

If `E(r) = o(r^α)` with `α > 0` and `β > 0`, then
`exists_radius_of_isLittleO_rpow` supplies a finite **positive real** `r₀` such
that for all `r ≥ r₀`,

```text
E(r) ≤ (2α/β) r^α.
```

The little-o characterization gives convergence of `E(r)/r^α` to zero. Choose
a radius beyond which its absolute value is less than `2α/β`; the result follows
by multiplying by the positive power `r^α`. No monotonicity spectrum,
finite-moment assumption, or `⊤`-to-real conversion is needed in this scalar
step. A zero-function application is checked in the module.

This proves only existence after the sharpness asymptotic has been supplied.
It does **not** prove exponential tails or `E(r) = o(r^α)` from finite moments,
compute a uniform radius as `β` varies, or close Proposition I.4.2, Lemma
I.4.10, or either paper root.
