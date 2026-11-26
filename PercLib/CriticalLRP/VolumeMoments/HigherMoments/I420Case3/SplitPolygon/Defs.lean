/- Integrated from `.scratch/case3-split-draft/Defs.lean` at production base
`1266415364a0ad5f96cb689b36fbed1778a2af1f`. -/

module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.Defs

/-! # A split polygon interface for the threefold corner -/

@[expose] public section

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal

set_option linter.unusedSectionVars false

namespace PercLib.CriticalLRP

namespace I420Case3

variable {V : Type*} [Countable V]

/-- A polygon bound that does not require the threefold diagonal to be small.

At `j = 3`, the hypothesis is on the sum over the finite window, which is the quantity
that actually enters the averaged Case-3 discrepancy. At every `4 ≤ j ≤ p + 2`,
it is the usual pointwise tail estimate. Both constants are explicit and may vary
with the law and radius in applications. -/
structure HasSplitPolygonBound (π : Sym2 V → unitInterval) (o : V) (B : Finset V)
    (p : ℕ) (poly : V → ℕ → ℝ≥0∞) (Bthree Btail : ℝ) : Prop where
  nonneg_three : 0 ≤ Bthree
  nonneg_tail : 0 ≤ Btail
  three : ∑ y ∈ B, poly y 3 ≤ (B.card : ℝ≥0∞) * ENNReal.ofReal Bthree
  tail : ∀ y ∈ B, ∀ j ∈ Finset.Icc 4 (p + 2),
    poly y j ≤ ENNReal.ofReal Btail * I420Case1.powMomentAt π 1 o ^ (j - 3)

/-- The old uniform interface gives the split interface with the same factor in
both slots. This is a conservative conversion; it does not make a nonvanishing
threefold factor tend to zero. -/
theorem HasPolygonBound.hasSplitPolygonBound {π : Sym2 V → unitInterval} {o : V}
    {B : Finset V} {p : ℕ} (hp : 1 ≤ p) {poly : V → ℕ → ℝ≥0∞} {Bpoly : ℝ}
    (h : HasPolygonBound π o B p poly Bpoly) :
    HasSplitPolygonBound π o B p poly Bpoly Bpoly where
  nonneg_three := h.nonneg
  nonneg_tail := h.nonneg
  three := by
    have hb : ∀ y ∈ B, poly y 3 ≤
        ENNReal.ofReal Bpoly * I420Case1.powMomentAt π 1 o ^ (3 - 3) :=
      fun y hy => h.bound y hy 3 (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)
    simpa using Finset.sum_le_sum hb
  tail := fun y hy j hj => h.bound y hy j (Finset.mem_Icc.mpr ⟨by
    have := (Finset.mem_Icc.mp hj).1
    omega, (Finset.mem_Icc.mp hj).2⟩)

end I420Case3

end PercLib.CriticalLRP
