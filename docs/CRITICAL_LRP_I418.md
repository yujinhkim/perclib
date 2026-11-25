# Lemma I.4.18: polygon diagrams

`Analysis/KernelPower`, `Analysis/Cutoff`, and `Analysis/Polygon` prove the
infinite-cutoff diagonal maximality, matrix-power calculus, and a conditional
analytic assembly for Lemma I.4.18 (supplied PDF p. 46). The remaining source
estimates are identified explicitly below; the full lemma is not claimed.

## Matrix powers and diagonal maximality

`KernelPower.Kpow K n x y` is the genuine `n`-fold matrix power of a nonnegative
kernel on any vertex type, defined by iterated `tsum`. Its zero power is the
Kronecker delta and `Kpow_one` proves that the one-fold power is exactly `K`.
`KpowF K S n` instead restricts every intermediate vertex to a finite set `S`.
The two notions are deliberately not identified.

The main generic results are:

* `KpowF_eq_matpow`: on `S`, the truncated iterated sum is literally the
  corresponding principal-submatrix power.
* `matrix_pow_entry_sq_le`: for a positive-semidefinite real matrix `A`,
  every power satisfies `(A^n i j)^2 ≤ (A^n i i)(A^n j j)`.
* `Kpow_eq_iSup_KpowS`: for a nonnegative real kernel, the full `ℝ≥0∞` matrix
  power is the supremum of its finite truncations. This is the directed
  monotone-convergence argument, not a finite-window theorem.
* `Kpow_le_diag`: if the full power has constant diagonal, each off-diagonal
  entry is bounded by that diagonal. No finiteness hypothesis is needed; an
  infinite diagonal is handled separately.
* `tau_Kpow_iSup_diag`: the native percolation connection kernel has the same
  diagonal-maximality property when it is translation invariant. Native
  positive semidefiniteness is supplied by `PercLib.Percolation.Bond.posSemidef_tau`.

`SourceModelData.cutTwoPoint_Kpow_le_diag` and
`SourceModelData.cutTwoPoint_Kpow_iSup_diag` instantiate this at the actual
cutoff kernel `M.cutKernel r` and critical parameter `M.betaCrit`:

```text
(⨆ y, Kpow (T_{β_c,r}) ℓ 0 y) = Kpow (T_{β_c,r}) ℓ 0 0.
```

`cutLaw r` is definitionally the long-range law of that same kernel and parameter,
on the full infinite lattice `Fin M.d → ℤ`. `M.cutKernel` is translation invariant.
`exists_sourceModel_cutKpow_iSup_diag` supplies a concrete non-vacuity instance.
Focused exports are listed in `Analysis/KernelPower/Audit.lean`.

## Cutoff matrix-power calculus

`Analysis/Cutoff` defines the two-point function directly from the actual cutoff
law `M.cutLaw r`, with its extended-nonnegative form `cutTwoPointE` and cluster
mass `cutMassAt`. Definition I.1.5 evaluates the truncated kernel at the critical
parameter of the *original* kernel, which is exactly `M.betaCrit`; no new
cutoff-dependent critical parameter is introduced.

The principal additions are:

* `Kpow_add`, the composition identity for genuine infinite matrix powers;
* `Kpow_rowSum`, `Kpow_colSum`, and `Kpow_colSum_of_symm`, giving all-`n`
  row/column sums `χ^n` from the base row sums, including when `χ = ⊤`;
* `cutKpow_comp`, with the **same cutoff kernel** in both factors:
  `Kpow (cutTwoPointE r) (n + 3) 0 0 = ∑' y,
    Kpow (cutTwoPointE r) 3 0 y * Kpow (cutTwoPointE r) n y 0`;
* `cutKpow_entry`, giving the uniform bound used for the near sum; and
* `cutKpow_rowSum_toReal`, `cutKpow_colSum_toReal`, whose finite-real forms
  explicitly require `cutMassAt r 0 ≠ ⊤` and prove each summand finite before
  applying `ENNReal.tsum_toReal_eq`.

Translation invariance, native positive semidefineness, and cutoff/uncut
monotonicity are proved in this layer. `cutMassAt r 0 = cutMoment 1 r` identifies
the susceptibility with the configured source moment.

## Source statement checks

The primary arXiv display `S4.Ex51` has right-hand side
`C (∇_{r^c} + r^{-c}) χ^(ℓ-3)`: the susceptibility power multiplies both terms.
The stronger transcription `C (∇_{r^c} + r^{-c} χ^(ℓ-3))` is not equivalent and is
not the result targeted here.

The printed `ℓ = 3` instance also has a genuine obstruction. Reflexivity gives
`T(0,0) = 1`, so the cutoff threefold diagonal is at least `1`
(`one_le_cutThreefold`). Yet its proposed bound at `ℓ = 3` is
`C (∇_{r^c} + r^{-c})`, which tends to `0` whenever the far tail descends to zero
(`not_source_ell_three_bound`). Thus the analytic estimate is meaningful here for
`ℓ ≥ 4`; `cutThreefold_le_uncutThreefold` gives the separate uncut-triangle
comparison available at `ℓ = 3`. This is a recorded source gap, not something to
hide by changing the diagonal convention.

## Analytic assembly and remaining inputs

`Analysis/Polygon` proves the near/far split and the scale arithmetic. In particular,
`split_bound` uses the cutoff threefold power as a kernel in its own right, rather
than confusing it with the uncut open triangle. `near_arith` and `rpow_card` choose
`R = r^(α/(2d))` and give `c = α/(4d)` with a constant independent of `ℓ` and `r`.
The source-model statement `source_polygon_bound` therefore produces, for `ℓ ≥ 4`
and `r ≥ 1`, the source-form bound

```text
T^ℓ(0,x) ≤ max 1 (∇_{β_c} K / c₀) * (∇_{r^c} + r^{-c}) * χ^(ℓ-3).
```

Two interface results make this consumer usable without redundantly assuming its matrix
handoffs. `cutKpow_toReal_eq_polyK` identifies the extended-real `Kpow` with the real
`polyK` when the cutoff susceptibility is finite. `source_powerInputs` then derives all
`PowerInputs` fields from `cutKpow_comp`, the all-`n` row sums, and the finite-sum
conversions. `source_polyK_le_diag` transports diagonal maximality to `polyK`.
Consequently `source_polygon_bound_of_cutoff_data` has no manually supplied
`PowerInputs` or `hdiag` hypothesis.

`UncutLink` strengthens this interface. `KernelPower.Kpow_mono` compares truncated and
uncut powers in `ℝ≥0∞`, and `Kpow_twoPointE_three_eq_openTriangle` identifies the
threefold uncut power with the configured open triangle. `source_powerInputs'` and
`source_polygon_bound_of_cutoff_data'` therefore eliminate `hB2`, `hB3`, and `hlink`,
without changing the real-valued bound or its constants. `source_triSup'` and
`source_triTail'` retain only the finite-cutoff-moment and finite-triangle hypotheses.
Independently, `hB2_hB3_hlink_derived` recovers the three earlier hypotheses from
`∇ < ∞`, proving that they were redundant rather than counterexamples to the old interface.
`source_ell_three_le` gives the separate constant bound at `ℓ = 3`.

The interface is further reduced by three packages:

* `NearBall.exists_card_const` and `exists_near_ball` produce the finite ball and its bound
  for the actual model seminorm whenever `R ≥ 1`. `exists_small_ball_count` supplies a
  complementary bound at small radii, but does not itself complete the small-`r` assembly.
* `SourceModelData.nablaTail` defines the actual open-triangle tail at the model norm.
  `source_polygon_bound_tail_source_c` eliminates `htailc` and `htrc` and permits the
  source value `c = α/(2d)`. It says nothing unconditional about tail decay.
* `ChiInput.exists_chi_lower_uniform` turns the lower half of the source first-moment
  asymptotic into a uniform comparison for all positive radii. That comparison implies
  the finite-real conversion `hχfin`; it also forces the uncut critical first moment to
  diverge. No finite critical susceptibility is inferred from these bounds.

`Assembly.exists_uniform_source_polygon_bound_of_triangle_first_moment` combines these
packages. It requires only the finite triangle and the ratio convergence of the cutoff first
moment. The latter itself gives positivity of `β_c`. It produces uniform constants and the
diagonal equality for `ℓ ≥ 4` and `r ≥ 1`.

`SmallRadius` now closes the complementary small-radius program. Finiteness of `χ` at one
cutoff `r₁ ≥ 1`, propagated downwards by monotonicity, supplies every finite conversion for
`r ≤ 1`. `χ ≥ 1` replaces the large-ball estimate; no additional asymptotic is needed below
radius one. For every `c > 0` the package produces the compensated count and the bound at
radius `r^c`. `exists_uniform_source_polygon_bound_of_triangle_first_moment_all_radii`
then combines the two ranges and proves uniform constants and the diagonal equality for
`ℓ ≥ 4` for every positive radius. The remaining source dependency for this assembly is
therefore Proposition I.4.2, Case 3, not a separate small-radius construction.

`ChiLower` adds the weaker lower-comparison alternative. With the cutoff ODE, divergence, and
`(1-E₀)(1-E₁) ≤ 1`, it obtains a positive lower bound for `χ`. With `E₁ ≥ 0` and `E₀ → 0`, the
comparison is eventual with constant `α/(2β_c)`. The usual uniform `c₀r^α ≤ χ` and `χ ≠ ⊤`
then follow from `ChiInput`'s extension. `bounded_defect_insufficient` verifies that discarding
`E₁ ≥ 0` cannot save the claim. None of these results instantiates the model ODE or E₁ sign at
criticality, and none asserts or uses the sharp `χ(r) / ((α/β_c) r^α) → 1` limit.

The genuine remaining gap for the full source statement is Proposition I.4.2, Case 3:
the exact limit `χ(r) / ((α/β_c) r^α) → 1` at the cutoff law. The old high-dimensional
first-moment theorem is not a substitute for this case.

`ConstantSharp` additionally checks the abstract constant on a finite constant-kernel example.
It is a sharpness and non-vacuity test of the analytic estimate, not a percolation model on
an infinite lattice.

Accordingly this remains a conditional analytic assembly for `ℓ ≥ 4` and every positive
radius, not a complete proof of Lemma I.4.18. The source hypothesis `∇ < ∞` is preserved
throughout.