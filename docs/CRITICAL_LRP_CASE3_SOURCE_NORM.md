# Literal printed Case 3 at arbitrary normalized source norms

Integrated from the reviewed artifact `smwu4e7s3/m2` after coordinator-owned production packaging.
Theorems are in `Analysis/OpenTriangle/Case3SrcNorm/{Defs,Main}.lean`; the joint Lemma I.4.3
wrapper is in `Analysis/OpenTriangle/Case23.lean`. The original artifact's proof and definition
text was checked for unchanged restitution after the `Defs`/`Main` split.

The central result is `HD3_to_supNorm`. It converts the literal third alternative of
`Orchestration.HD`, with unshifted `(Real.log ρ)⁻¹`, into the sup-norm shell domination required by
`Case3Literal`. There is no `log (1 + ρ)` substitution in the hypothesis, no added positive gap,
and no additional large-radius assumption.

The raw logarithm has two important consequences. For `0 < ρ < 1`, its inverse is negative, so
nonnegativity of the two-point probability makes the printed HD hypothesis impossible on such a
nonzero displacement. Hence `one_le_srcNorm_of_HD3` proves `ρ ≥ 1`. At `ρ = 1`, Lean's
`(log 1)⁻¹ = 0` forces the two-point function to vanish, recorded by
`twoPoint_eq_zero_of_srcNorm_one`. These are rigidity facts about the printed hypothesis, not
claims that it is nonvacuous for an arbitrary prescribed normalized norm.

For the actual norm transfer, let `c = srcLowerUnit S` and `T = max 2 (4 / c)`. On the shell
`‖z‖ ≥ T`, one has `c‖z‖ ≥ 4`, so `log (c‖z‖) ≥ log 4` and

`log ‖z‖ / log (c‖z‖) ≤ 1 + (-log c) / log 4`.

The remaining bounded shell `2 ≤ ‖z‖ ≤ T` is handled using only `τ ≤ 1`. The explicit
`case3SrcConst` takes the maximum of the genuine-transfer term and the bounded-shell term `(T^e)⁻¹
log T`, then adds one. Thus no intermediate radii are skipped and no globally fictitious lower
source-distance gap is used.

At the output, `case3SrcOutConst` retains `case3Conv3ConstShell` and the square of
`srcLogConstUpper`. The resulting theorem `openTriangle_toReal_le_logMajorant_case3` bounds the
literal open triangle by a square-logarithmic majorant at the actual `M.S.dist 0 y` radius.
`openTriangle_ne_top_case3` proves finiteness before real conversion;
`nablaTail_le_logMajorant_case3` and `tendsto_nablaTail_zero_of_HD3` give the source-tail bounds
and `isLogErrorFunction_nablaTail_of_HD_third_disjunct` consumes the printed third disjunct
verbatim. `HD_of_HD3` checks that this disjunct really is the third alternative of `HD M`.

Finally, `SourceModelData.isLogErrorFunction_nablaTail_of_HD_case2_or_case3` packages exactly the
Case 2-or-Case 3 alternative. Together with the earlier Case 2 result, it establishes Lemma I.4.3
at the model's normalized-source open-triangle tail, conditional on the corresponding HD input.
The stronger `IsLogErrorFunction` conclusion includes both logarithmic integrability and
convergence to zero.

The production split has 37 axiom reports in `Case3SrcNorm.Main`, and `Case23` has one for its
joint wrapper. All use only `propext`, `Classical.choice`, and `Quot.sound`.

The explicitly repaired `log (1 + ρ)` variant is proved separately in `Case3SourceNorm`; see
`CRITICAL_LRP_CASE3_SHIFTED.md`. It is not used for this literal printed source claim.

**Not claimed:** non-vacuity of printed HD3 on an arbitrary source model, the HD domination itself,
a Kozma/Gram factorization, critical operator positivity, Russo differentiation, finite cutoff
moments, an ODE, or any of the paper's principal main theorems. Lemma I.4.3 does not cover Case 1
of HD and is not Proposition I.4.2.
