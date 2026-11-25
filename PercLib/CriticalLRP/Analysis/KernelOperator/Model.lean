/-
The cutoff two-point kernel of the long-range model as a Schur kernel.

Swarm `smwtrtcqs`, member `m1`, direction D6.  At the actual range-truncated law, the row sum
of the two-point matrix is the expected cluster volume `χ = M.cutMassAt r 0` (the landed
`tsum_cutTwoPointE_eq_cutMassAt`), so finiteness of `χ` is exactly the Schur row-sum bound.
-/
module

public import Mathlib
public import PercLib.CriticalLRP.Analysis.KernelOperator.Operator
public import PercLib.CriticalLRP.Analysis.Cutoff.RowSum
public import PercLib.CriticalLRP.Analysis.Cutoff.Translation
public import PercLib.CriticalLRP.Analysis.Cutoff.Basic

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP.KernelOperator

open PercLib.CriticalLRP.Orchestration

variable (M : SourceModelData)

/-- The truncated two-point function in `ℝ≥0∞` is never `⊤`. -/
theorem cutTwoPointE_ne_top (r : ℝ) (x y : M.V) : M.cutTwoPointE r x y ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (M.cutTwoPointE_le_one r x y)

/-- The rows of the truncated two-point matrix are summable with sum the truncated cluster
mass. -/
theorem summable_cutTwoPoint_row (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) (x : M.V) :
    Summable fun y => M.cutTwoPoint r x y := by
  have hrow : (∑' y, M.cutTwoPointE r x y) = M.cutMassAt r x := M.tsum_cutTwoPointE_eq_cutMassAt r x
  have hχx : M.cutMassAt r x ≠ ⊤ := by
    rw [M.cutMassAt_eq_zero r x]
    exact hχ
  refine summable_of_sum_le (c := (M.cutMassAt r x).toReal)
    (fun y => ENNReal.toReal_nonneg) fun u => ?_
  have h1 : ∑ y ∈ u, M.cutTwoPointE r x y ≤ M.cutMassAt r x := by
    rw [← hrow]
    exact ENNReal.sum_le_tsum u
  have hstep : ∑ y ∈ u, M.cutTwoPoint r x y
      = ∑ y ∈ u, (M.cutTwoPointE r x y).toReal := rfl
  rw [hstep, ← ENNReal.toReal_sum fun y _ => cutTwoPointE_ne_top M r x y]
  exact ENNReal.toReal_mono hχx h1

/-- **The truncated two-point kernel is a Schur kernel with constant `χ = E_{β_c,r}|K|`.** -/
theorem cutTwoPoint_schurKernel (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) :
    SchurKernel (fun x y : M.V => M.cutTwoPoint r x y) (M.cutMassAt r 0).toReal where
  nonneg := fun x y => M.cutTwoPoint_nonneg r x y
  symm := fun x y => M.cutTwoPoint_comm r x y
  nonneg_A := ENNReal.toReal_nonneg
  row_summable := fun x => summable_cutTwoPoint_row M r hχ x
  row_le := by
    intro x
    have hrow : (∑' y, M.cutTwoPointE r x y) = M.cutMassAt r x :=
      M.tsum_cutTwoPointE_eq_cutMassAt r x
    have h1 : (∑' y, M.cutTwoPoint r x y) = (M.cutMassAt r x).toReal := by
      rw [show (∑' y, M.cutTwoPoint r x y) = ∑' y, (M.cutTwoPointE r x y).toReal from rfl,
        ← ENNReal.tsum_toReal_eq fun y => cutTwoPointE_ne_top M r x y, hrow]
    rw [h1, M.cutMassAt_eq_zero r x]

/-- **The cutoff operator is bounded on `ℓ²` with norm at most `χ = E_{β_c,r}|K|`.**  This is
the Schur bound of `Operator.lean` at the actual truncated law. -/
theorem cutTwoPoint_tsum_sq_le (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) (f : M.V → ℝ)
    (hf : Summable fun y => f y ^ 2) :
    Summable (fun x => (∑' y, M.cutTwoPoint r x y * f y) ^ 2) ∧
      ∑' x, (∑' y, M.cutTwoPoint r x y * f y) ^ 2
        ≤ (M.cutMassAt r 0).toReal ^ 2 * ∑' y, f y ^ 2 := by
  have h := schur_tsum_sq_kernelApply_le (κ := fun x y : M.V => M.cutTwoPoint r x y)
    (A := (M.cutMassAt r 0).toReal) (cutTwoPoint_schurKernel M r hχ) f hf
  simpa only [kernelApply] using h

/-- **The `toReal` encoding pitfall.**  If the `ℝ≥0∞` row sum of the two-point function is
infinite, then the real-valued row sum of its `toReal` entries is *zero*, not infinite, because
`(⊤ : ℝ≥0∞).toReal = 0`.  So an infinite `ℝ≥0∞` row cannot be detected as a divergent real row;
the Schur hypothesis has to be imposed on the `ℝ≥0∞` side (finiteness of `χ`), which is what
`cutTwoPoint_schurKernel` does at the truncated law. -/
theorem twoPoint_tsum_toReal_eq_zero_of_tsum_top (β : ℝ≥0) (x : M.V)
    (hdiv : (∑' y : M.V, M.twoPointE β x y) = ⊤) :
    (∑' y : M.V, (M.twoPointE β x y).toReal) = 0 := by
  have hne : ∀ y : M.V, M.twoPointE β x y ≠ ⊤ := fun y =>
    ne_top_of_le_ne_top ENNReal.one_ne_top
      (twoPointFunction_le_one M.kernel M.kernel_nonneg β x y)
  rw [← ENNReal.tsum_toReal_eq hne, hdiv]
  rfl

end PercLib.CriticalLRP.KernelOperator
