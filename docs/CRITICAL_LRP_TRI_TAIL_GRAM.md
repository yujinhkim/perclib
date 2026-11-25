# Gram reductions for the open-triangle tail

`Analysis/TriTail/GramDefs.lean` contains the generic Gram-coordinate
definition and a constant-kernel counterexample object.
`Analysis/TriTailGram.lean` proves Parseval summability, the operator
autocorrelation identity, and conditional applications of the triangle-tail
square-root interface.

For a bounded operator with a translation-invariant kernel, its coordinate
vector is automatically square-summable and its autocorrelation is the kernel
of `S†S`. The intrinsic vector form identifies translates with the matrix
element `⟨Ξ,U(x)Ξ⟩` and supplies the diagonal bound. Constant kernels show that
positive semidefinite data with finite diagonal are not enough, and a finite
`ℓ²` row with value at another point exceeding its origin value cannot be an
autocorrelation.

The remaining input is the **model's** bounded translation-invariant two-point
operator and the identification of its third matrix power with the open
triangle (or the explicit Gram matrix element). The code does not construct
that operator, apply continuous functional calculus over `ℝ`, or assert
Kozma's theorem for the source model. Therefore tail decay and the triangle
condition remain conditional on the displayed factorization premise.
