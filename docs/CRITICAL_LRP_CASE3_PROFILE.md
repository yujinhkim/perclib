# Log-corrected Case 3 convolution profile

Independently reviewed and integrated from `smwu2am6k/m2` in `Analysis/OpenTriangle/Case3Profile/{Defs,Main}.lean`.  These are real-valued profile theorems.  The separate accepted literal bridge is now in `Analysis/OpenTriangle/Case3Literal/Main.lean` and is documented in `CRITICAL_LRP_CASE3_LITERAL.md`.

The definitions isolate the conversion and assembly constants.  `abs_le_conv_wt_of_case3Raw` converts the literal nonzero input `t x ≤ C‖x‖^(-d+2)(log‖x‖)^(-1)` to a domination by `case3LogConst d C * Wt (d-2) 1 ‖x‖`, with `case3LogConst d C = C(3·2^(d-2))+1`, for `d>2`, nonnegative `t`, `t0=1` and `C≥0`.

The literal raw-log form at norm one forces `t x ≤ 0`, because `log 1 = 0` and `0^(-1)=0`; it is not confused with a nonzero conclusion.  The more useful source-shaped alternative `abs_le_conv_wt_of_case3Shell` assumes `0≤t≤1` everywhere and the decay only for `‖x‖≥2`, with an explicit constant handling origin and unit shell.  `case3Shell_hypotheses_inhabited` asserts and proves both that this hypothesis class is inhabited and that the constructed input satisfies `t 0 = 1`.  Thus the inhabited statement now includes the normalization it was intended to exhibit.

`convolution_two_case3` applies the strict assembly for `d>4` and yields summability and the intermediate `Wt (d-4) 2 ‖x‖` bound.  At `d=6`, `triple_convolution_case3` then applies the actual marginal assembly with `a=4`, `b=2`, `ah=2`, `bh=1`, giving summability and the bound `case3Conv3Const C * Wt 0 2 ‖x‖`.  The log exponent is exactly `1-(2+1)=-2`; it is not the invalid unreduced marginal exponent.  The named constants keep every power/log and convolution-assembly factor explicit.

There are frozen-Λ and generic-`Wt` interfaces and a `d>6` companion producing `Wt (d-6) 3 ‖x‖`.  The split source modules and barrel, independent verification and 23 in-file plus 14 verification axiom reports passed with only `propext`, `Classical.choice` and `Quot.sound`.

**Literal continuation:** `Case3Literal` supplies the conditional plain sup-norm identification, finite `ENNReal` values, and log tail under the explicit HD(3) domination; see `CRITICAL_LRP_CASE3_LITERAL.md`. `Case3SrcNorm` transports the literal printed input through arbitrary normalized source norms and proves the actual `M.nablaTail` result; see `CRITICAL_LRP_CASE3_SOURCE_NORM.md`. The HD domination and its non-vacuity are not generated. No critical operator, first-moment or ODE result is inferred from these profiles.
