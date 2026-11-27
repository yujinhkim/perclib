/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted from Ultramath `smwzg77c3`, member `m2`, independently rebuilt.
Production integration based on commit `81c6038182e9a883ffcd3d870aed7cd4829649d4`.
Original direction `d5`.

# Why the `ℓ = 2` residual is a genuine two-point input, not a formal identity

`Main.twoTermBound_of_chi_mul_square_le` reduces the source's `q = 0`, `p = 3` two-term
per-vertex estimate to the comparison of consecutive powers of the cutoff two-point matrix,

```lean
χ · T^2(0,y) ≤ K · T^3(0,y)      (qzeroChiMulSquareLe)
```

(resp. its fourth-power form `χ² T² ≤ K T⁴`).  Normalizing `T = χ · S`, with `S` the symmetric
stochastic matrix of row sums `1`, that comparison is *exactly*

```lean
S^2(0,y) ≤ K · S^3(0,y).
```

This file records a machine-checked obstruction: no such comparison is a formal consequence of
`symmetric + stochastic` alone.  The witness is the two-point swap kernel `S = [[0,1],[1,0]]`
(equivalently `T = χ · S` with `χ = 1`), which is symmetric and doubly stochastic, has
`S² = 1` on the diagonal and `S³ = S`, so `S²(0,0) = 1` while `S³(0,0) = 0`.

This is an abstract kernel, **not** the percolation two-point function (whose cutoff matrix is
aperiodic: `T(x,y) > 0` for all pairs, `T(x,x) = 1`).  The point of the file is scope: the
residual of the `ℓ = 2` class cannot be discharged by symmetry/double-stochasticity bookkeeping —
it needs an aperiodicity / non-degeneracy input about the cutoff two-point function itself.  The
one-vertex kernel is recorded as a non-vacuity anchor.
-/
module

public import Mathlib

/-! # An abstract no-go for the `ℓ = 2` absorption -/

set_option autoImplicit false

open scoped BigOperators

@[expose] public section

noncomputable section

namespace PercLib.CriticalLRP.QZeroGapNoGo

/-- The two-point swap kernel: symmetric, doubly stochastic, aperiodic-free (period `2`). -/
def swapK : Fin 2 → Fin 2 → ℝ := fun i j => if i = j then 0 else 1

theorem swapK_symm (i j : Fin 2) : swapK i j = swapK j i := by
  fin_cases i <;> fin_cases j <;> simp [swapK]

theorem swapK_nonneg (i j : Fin 2) : 0 ≤ swapK i j := by
  fin_cases i <;> fin_cases j <;> simp [swapK]

theorem swapK_stochastic (i : Fin 2) : ∑ j, swapK i j = 1 := by
  fin_cases i <;> simp [swapK, Fin.sum_univ_two]

/-- `S² = 1` (the identity): the swap has period `2`. -/
theorem swapK_sq (i j : Fin 2) : ∑ k, swapK i k * swapK k j = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [swapK, Fin.sum_univ_two]

/-- `S³ = S`. -/
theorem swapK_cube (i j : Fin 2) :
    ∑ k, (∑ l, swapK i l * swapK l k) * swapK k j = swapK i j := by
  fin_cases i <;> fin_cases j <;> simp [swapK, Fin.sum_univ_two]

/-- The diagonal of `S²` is `1`. -/
theorem swapK_sq_diag : ∑ k, swapK 0 k * swapK k 0 = 1 := by
  rw [swapK_sq]; simp

/-- The diagonal of `S³` is `0`. -/
theorem swapK_cube_diag : ∑ k, (∑ l, swapK 0 l * swapK l k) * swapK k 0 = 0 := by
  rw [swapK_cube]; simp [swapK]

/-- **No symmetric doubly stochastic kernel satisfies the absorption comparison by fiat.**
For the swap kernel no constant `K` can make `S²(0,0) ≤ K · S³(0,0)` hold, so the `ℓ = 2`
absorption inequality is not a formal consequence of symmetry and unit row sums. -/
theorem no_forall_sq_le_mul_cube (K : ℝ) :
    ¬ (∀ i j : Fin 2, ∑ k, swapK i k * swapK k j
        ≤ K * ∑ k, (∑ l, swapK i l * swapK l k) * swapK k j) := by
  intro h
  have h00 := h 0 0
  rw [swapK_sq_diag, swapK_cube_diag, mul_zero] at h00
  linarith

/-- Non-vacuity anchor: on the one-point vertex set the comparison holds with `K = 1`
(`S = 1`, `S² = S³ = 1`). -/
theorem one_point_comparison :
    ∀ _i _j : PUnit, (1 : ℝ) ≤ 1 * 1 := fun _ _ => by norm_num

end PercLib.CriticalLRP.QZeroGapNoGo

/-! ## Axiom audit -/

namespace PercLib.CriticalLRP.QZeroGapNoGoAudit

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.QZeroGapNoGo.swapK_sq
#print axioms PercLib.CriticalLRP.QZeroGapNoGo.swapK_cube
#print axioms PercLib.CriticalLRP.QZeroGapNoGo.no_forall_sq_le_mul_cube

end PercLib.CriticalLRP.QZeroGapNoGoAudit
