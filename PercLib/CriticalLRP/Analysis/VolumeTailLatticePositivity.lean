/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Positive volume tails for the power-law lattice kernel

At positive intensity, every off-diagonal edge of the power-law kernel has
positive opening probability. A nonzero integer-lattice direction is
nonperiodic, so the repeated-step paths of `VolumeTailPositivity` prove exact
all-natural tail positivity for the canonical percolation model. Almost-sure
finiteness is retained explicitly, as it is in the I.3.1 package itself.
-/

module

public import PercLib.CriticalLRP.Analysis.VolumeTailPositivity
public import PercLib.CriticalLRP.CountableProduct.Lattice

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open Filter Set MeasureTheory
open scoped ENNReal Topology BigOperators

namespace PercLib.CriticalLRP

variable {V : Type*} [Countable V]

/-- Positive intensity and positive edge weight give a positive opening probability. -/
theorem bernoulliEdgeProb_pos {J : Sym2 V → ℝ} (hJ : ∀ e, 0 ≤ J e)
    {β : NNReal} (hβ : 0 < β) {e : Sym2 V} (he : 0 < J e) :
    0 < (bernoulliEdgeProb J hJ β e : ℝ) := by
  rw [bernoulliEdgeProb_coe]
  have hβR : 0 < (β : ℝ) := by exact_mod_cast hβ
  have hprod : 0 < (β : ℝ) * J e := mul_pos hβR he
  have hexp : Real.exp (-((β : ℝ) * J e)) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  linarith

/-- Off-diagonal pairs have positive weight in the power-law kernel. -/
theorem lrKernel_pos_of_ne (d : ℕ) (α : ℝ) {x y : Fin d → ℤ} (hxy : x ≠ y) :
    0 < lrKernel d α s(x, y) := by
  simp only [lrKernel, Sym2.lift_mk]
  apply Real.rpow_pos_of_pos
  rw [norm_pos_iff, sub_ne_zero]
  exact hxy

/-- Multiples of a nonzero integer-lattice vector have no period. -/
theorem lattice_nsmul_injective {d : ℕ} (v : Fin d → ℤ) (hv : v ≠ 0) :
    Function.Injective (fun k : ℕ => k • v) := by
  have hex : ∃ i, v i ≠ (0 : ℤ) := by
    simpa only [Function.ne_iff, Pi.zero_apply] using hv
  obtain ⟨i, hi⟩ := hex
  intro m n hmn
  have hcoord : (m : ℤ) * v i = (n : ℤ) * v i := by
    simpa only [Pi.smul_apply, nsmul_eq_mul] using congrFun hmn i
  have hmnZ : (m : ℤ) = (n : ℤ) := mul_right_cancel₀ hi hcoord
  exact_mod_cast hmnZ

/-- Every positive-intensity power-law lattice law has arbitrarily long simple
paths with positive edge probabilities, in every nonzero lattice direction. -/
theorem arbitrarilyLongPositivePaths_lrKernel (d : ℕ) (α : ℝ)
    {β : NNReal} (hβ : 0 < β) (v : Fin d → ℤ) (hv : v ≠ 0) :
    ArbitrarilyLongPositivePaths
      (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β) 0 := by
  have hinj : Function.Injective (fun k : ℕ => (0 : Fin d → ℤ) + k • v) := by
    simpa using lattice_nsmul_injective v hv
  apply PositivePaths.arbitrarilyLongPositivePaths_of_translationInvariant
    (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β)
    (0 : Fin d → ℤ) v hv hinj
  · exact bernoulliEdgeProb_pos (lrKernel_nonneg d α) hβ
      (lrKernel_pos_of_ne d α (Ne.symm hv))
  · intro a x y
    have hshift := bernoulliEdgeProb_shift (lrKernel_shift_invariant d α)
      (lrKernel_nonneg d α) β a s(x, y)
    simpa only [Sym2.map_mk, add_comm] using hshift

/-- The exact `hTailPos` input for the canonical positive-intensity power-law
lattice model, from any nonzero direction and almost-sure finiteness. -/
theorem volumeLaw_nat_tail_pos_lrKernel (d : ℕ) (α : ℝ)
    {β : NNReal} (hβ : 0 < β) (v : Fin d → ℤ) (hv : v ≠ 0)
    (hfin : ∀ᵐ ω ∂edgeMeasure (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β),
      clusterVol ω (0 : Fin d → ℤ) ≠ ⊤) :
    ∀ n : ℕ, 1 ≤ n →
      0 < (volumeLaw (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β)
        (0 : Fin d → ℤ) (Ici (n : ℝ))).toReal :=
  volumeLaw_nat_tail_pos _ _ (arbitrarilyLongPositivePaths_lrKernel d α hβ v hv) hfin

end PercLib.CriticalLRP

#print axioms PercLib.CriticalLRP.bernoulliEdgeProb_pos
#print axioms PercLib.CriticalLRP.lrKernel_pos_of_ne
#print axioms PercLib.CriticalLRP.lattice_nsmul_injective
#print axioms PercLib.CriticalLRP.arbitrarilyLongPositivePaths_lrKernel
#print axioms PercLib.CriticalLRP.volumeLaw_nat_tail_pos_lrKernel
