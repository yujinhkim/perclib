# Open-triangle tails: partial results and the remaining square root

`Analysis/TriTail.lean` defines the actual configured open triangle
`∑_u∑_v τ(x,u)τ(u,v)τ(v,y)`, its diagonal, and both the closed and strict
lattice-distance tails. The definitions live in `Analysis/TriTail/Defs.lean`.

The configured two-point function is identified with the native bond connection
kernel.  Native positive-semidefiniteness gives Cauchy–Schwarz and the diagonal
bound. Translation invariance identifies every diagonal with the origin, giving

```text
openTriangle 0 x ≤ openTriangleSelf 0,
openTriangleTail r ≤ openTriangleSelf 0.
```

These imply tail **boundedness**, not decay.  The tail has separate `≤ r` and
strict forms with the proved closed/strict-ball conversions, and the `I.4.18`-shaped
pointwise and radius-composition restatements are available.

`Analysis/TriTailSqrt.lean` proves Kozma's analytic ending.  If the open triangle
is `ofReal (∑_y ξ y ξ(y-x))` for summable `ξ²`, then finite-window plus
Cauchy–Schwarz/AM–GM bounds show that far translations are almost orthogonal and
`openTriangleTail` tends to zero.  This is a real proof of tail decay **from the
square-root factorisation**, not from diagonal finiteness alone.

## Remaining gap

The operator-theoretic construction of this `ℓ²` factorisation from the triangle
condition is not proved.  Hence `hutchcroft.a.tri.tail` remains open.  The
positive-semidefinite constant-kernel counterexample only demonstrates that the
diagonal argument cannot prove decay; it is not a percolation counterexample and
is not a refutation of Kozma's theorem.

Do not consume `openTriangle_le_diagonal`, `openTriangleTail_ne_top`, or the
square-root-factor implication as if they were the full triangle-to-tail
implication.
