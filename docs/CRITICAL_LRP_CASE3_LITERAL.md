# Literal Case 3 open triangle and log tail

Integrated from the accepted packet `smwu3to7x/m1` in
`Analysis/OpenTriangle/Case3Literal/Main.lean`. Its companion abstract convolution estimates are
in `Analysis/OpenTriangle/Case3Profile/{Defs,Main}.lean`.

The theorem `HD.openTriangle_eq_ofReal_tsum_case3Shell`, and its raw-input analogue, identify the
literal `TriTail.openTriangle` at the origin with `ENNReal.ofReal` of the abstract iterated
convolution of `litT`. The underlying `HD.openTriangle_eq_tsum_ENNReal` uses translation invariance.
Both required real summability facts are derived before `ofReal` is moved through either sum: the
inner one from the strict first convolution, and the outer one from the strict-then-marginal Case 3
assembly. Consequently the real identification and `openTriangle_ne_top_case3Shell/Raw` do not
infer finiteness from `ENNReal.toReal ⊤ = 0`.

At `d = 6`, the pointwise bound has the square-logarithmic majorant
`case3Conv3ConstShell C * Wt 0 2 ‖x‖` in the shell variant, or `case3Conv3Const C * Wt 0 2 ‖x‖`
in the raw variant. The packaged results `HD.case3LiteralBridge_case3Shell/Raw` combine this bound
with the literal identification, finiteness, and
`HD.isLogErrorFunction_openTriangleTail_case3Shell/Raw`. These tail results concern the plain
sup-norm `TriTail.openTriangleTail`, whose radius predicate remains `r ≤ latticeDist 0 x`.

Both input forms require a translation-invariant nonnegative kernel and retain the HD(3)
two-point domination as an explicit hypothesis. The shell variant asks for decay when `‖z‖ ≥ 2`
and derives the remaining `litT ≤ 1` bound from the probability interface. The raw variant asks
for decay at every `z ≠ 0`. Under the raw Lean convention `log 1 = 0` and `0⁻¹ = 0`, that hypothesis
forces `litT = 0` on the unit shell; `litT_eq_zero_of_one_le_norm_of_raw` records this extra
strength rather than hiding or reinterpreting it.

The 32 in-file axiom reports use only `propext`, `Classical.choice`, and `Quot.sound`.

**Scope limitations.** This module itself is a conditional plain-sup-norm bridge and log-tail
proof under explicit HD(3) domination. The subsequent `Case3SrcNorm` module transports the
literal printed, unshifted-log input through arbitrary normalized source norms and proves the
actual `M.nablaTail` result; `Case23` supplies the joint Case 2-or-Case 3 wrapper. See
`CRITICAL_LRP_CASE3_SOURCE_NORM.md`. These results do not prove HD itself, its non-vacuity on a
prescribed model, a Kozma/Gram factorization, a critical operator, moment existence, Russo
differentiation, or an ODE.
