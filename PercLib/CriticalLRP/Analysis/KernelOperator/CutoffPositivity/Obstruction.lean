/-
The finite first cutoff moment is not removable: at an infinite cutoff moment no Schur bound exists.

Swarm `smwtxo95t`, member `m6`, direction (E).

The positivity theorems of this package all take `hχ : M.cutMassAt r 0 ≠ ⊤`, which enters only
through the Schur hypothesis (row summability and the row bound).  This file records the matching
obstruction: if the truncated cluster mass at any vertex is `⊤`, then the truncated two-point matrix
is not a Schur kernel with *any* constant, so `kernelCLM` cannot be formed there.  The proof is the
converse of `SourceModelData.summable_cutTwoPoint_row`: a summable nonnegative real row would make
the `ℝ≥0∞`-valued row sum finite, but that row sum is `M.cutMassAt r x` by
`SourceModelData.tsum_cutTwoPointE_eq_cutMassAt`.
-/
module

public import PercLib.CriticalLRP.Analysis.KernelOperator.CutoffPositivity.Cutoff

/-!
# Obstruction: an infinite cutoff moment admits no Schur bound
-/

@[expose] public section

noncomputable section

open scoped ENNReal NNReal lp

namespace PercLib.CriticalLRP.CutoffPositivity

open PercLib.CriticalLRP.KernelOperator
open PercLib.CriticalLRP.Orchestration

/-- **An infinite truncated cluster mass at one vertex admits no Schur constant.**  Hence the
finite-first-moment hypothesis of `cutKernelCLM_quadForm_nonneg` is not removable: at
`M.cutMassAt r x = ⊤` the operator itself does not exist. -/
theorem not_schurKernel_of_cutMassAt_eq_top (M : SourceModelData) (r : ℝ) (x : M.V)
    (hx : M.cutMassAt r x = ⊤) (A : ℝ) : ¬ SchurKernel (cutKernel M r) A := by
  intro h
  have hsum : Summable (fun y => M.cutTwoPoint r x y) := h.row_summable x
  have hnn : ∀ y, 0 ≤ M.cutTwoPoint r x y := fun y => M.cutTwoPoint_nonneg r x y
  have htsum : (∑' y, M.cutTwoPointE r x y) = M.cutMassAt r x :=
    M.tsum_cutTwoPointE_eq_cutMassAt r x
  have hofreal : (∑' y, ENNReal.ofReal (M.cutTwoPoint r x y))
      = ENNReal.ofReal (∑' y, M.cutTwoPoint r x y) :=
    (ENNReal.ofReal_tsum_of_nonneg hnn hsum).symm
  have hstep : (∑' y, M.cutTwoPointE r x y)
      = ENNReal.ofReal (∑' y, M.cutTwoPoint r x y) := by
    rw [← hofreal]
    exact tsum_congr fun y => M.cutTwoPointE_eq_ofReal r x y
  have htop : (⊤ : ℝ≥0∞) = ENNReal.ofReal (∑' y, M.cutTwoPoint r x y) := by
    rw [← hx, ← htsum]
    exact hstep
  exact ENNReal.ofReal_ne_top htop.symm

/-- The obstruction at the reference vertex: an infinite truncated cluster mass at `0` admits no
Schur constant. -/
theorem not_schurKernel_of_cutMassAt_zero_eq_top (M : SourceModelData) (r : ℝ)
    (hx : M.cutMassAt r 0 = ⊤) (A : ℝ) : ¬ SchurKernel (cutKernel M r) A :=
  not_schurKernel_of_cutMassAt_eq_top M r 0 hx A

end PercLib.CriticalLRP.CutoffPositivity
