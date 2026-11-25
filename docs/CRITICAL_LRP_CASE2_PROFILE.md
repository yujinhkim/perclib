# The Case 2 threefold convolution profile

Developed locally and integrated in `Analysis/OpenTriangle/Case2Profile.lean` as a proof-only module.  Its source statement from the PDF is explicit: the HD Case 2 assumption is `d>6` and `Pβc(x↔y)≼‖x-y‖^(-d+2)` on nonzero differences.  It is not a theorem produced by the convolution estimates.

For a nonnegative real-valued `t : (Fin d → ℤ) → ℝ` with `t 0=1`, a constant `C≥1`, and `t x≤C‖x‖^(-d+2)` away from zero, `abs_le_conv_wt_of_case2` proves the shifted-weight domination

`|t x| ≤ (C 2^(d-2)) Wt (d-2) 0 ‖x‖`.

The factor `2^(d-2)` comes from `1+‖x‖≤2‖x‖` for a nonzero lattice point.  Missing this factor would reverse the requested comparison between the raw and shifted norms; the explicit conversion retains it rather than silently absorbing it.

`convolution_two_case2` applies the strict convolution assembly with zero logarithmic exponents.  It proves summability and a bound by `K^2 convConst(d,2,2,0,0) Wt (d-4) 0 ‖x‖`, where `K=C 2^(d-2)`.  `triple_convolution_case2` applies it again and yields

`K^3 convConst(d,2,2,0,0) convConst(d,4,2,0,0) Wt (d-6) 0 ‖x‖`

for the iterated real double convolution, including summability.  `Wt (d-6) 0 ‖x‖` is the source's `⟨x⟩^(-d+6)` profile.  A strict production build and the in-file axiom reports passed with only the three standard axioms.

**Completed continuation:** `Analysis/OpenTriangle/Case2Literal/Link` now identifies the iterated convolution with `TriTail.openTriangle` and the definitionally equal `TriangleAverage.nabla`, proves the literal Case 2 profile and finiteness, and obtains the plain sup-norm and configured-model logarithmically integrable tails under the explicit HD(2) domination (see `CRITICAL_LRP_CASE2_LITERAL.md`).  It also establishes the `polyK` equality and the two convolution summabilities.

The HD two-point domination itself remains an explicit assumption in those theorems, not a consequence proved here.  No Kozma factorization or finite large-radius cutoff moment is inferred.  Case 3 is a separate remaining case; local compact-integrability clauses beyond the established improper logarithmic tail require separate support.