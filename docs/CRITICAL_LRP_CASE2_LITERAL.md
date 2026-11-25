# Literal Case 2 open triangle and log tail

Integrated from the independently refactored and freshly checked artifact of `smwu2am6k/m1`, in `Analysis/OpenTriangle/Case2Literal/{Defs,Main,Model,Link}.lean`.

`HD.openTriangle_eq_tsum_ENNReal` is an unconditional translation-invariant identification:
for a translation-invariant kernel, the literal `TriTail.openTriangle` is
`∑'_b ((∑'_a τ(0,a) τ(0,b-a)) * τ(0,x-b))`.
Tonelli commutes the outer sums and factors the outer leg.  No summability or finite moment is needed for this ENNReal equality.  `HD.openTriangle_eq_ofReal_tsum` converts to the real radial profile `litT`, using exactly the two summability conclusions already supplied by the Case 2 convolution assembly and deriving, rather than assuming, `HD.openTriangle_ne_top`.

Under the explicit HD Case 2 hypotheses `d>6`, `C≥1`, and `τβ(0,x) ≤ ofReal (C‖x‖^(-d+2))` on nonzero lattice points, the literal open triangle is finite and bounded by `ofReal (case2Const d C * Wt (d-6) 0 ‖x‖)`, with `case2Const d C = K³ convConst(d,2,2,0,0) convConst(d,4,2,0,0)`, `K=C2^(d-2)`.  The pointwise raw-power and radial-tail forms follow, and `isLogErrorFunction_openTriangleTail` gives the plain sup-norm log tail.  The two summability facts that make finite conversion meaningful come from the convolution proofs, not a separate finite-triangle premise.

At a `SourceModelData`, `HD_to_supNorm` uses `srcLowerUnit` in the correct negative-exponent direction.  Return to source norm uses `srcUpperConst^(d-6)`, with all constants visible in `srcCase2Const`.  `isLogErrorFunction_nablaTail_of_HD_case2` and the second-disjunct form prove that the uncut `M.nablaTail` is a logarithmically integrable error function under HD(2).  `tendsto_nablaTail_zero_of_HD_case2` also gives vanishing of the ENNReal tail from the polynomial decay.

The `polyK` link proves `polyK_three_eq_triPoint` under HD(2), giving the `hlink` premise of the existing polygon statements, and produces `summable_uncut_two` and `summable_uncut_three`.  `nabla_eq_openTriangle` is a definitional bridge to `TriangleAverage.nabla`; it does not switch the argument to a distinct triangle diagram.

Fresh focused production builds of all four modules passed, and the 31 in-file axiom reports are limited to the three standard foundational axioms.  No arbitrary HD domination is asserted as a theorem.  This does not prove Kozma factorization, critical operator positivity, finite large-radius cutoff moments, or local compact integrability support beyond the established improper log-integrable tail.  Case 3 is handled separately.