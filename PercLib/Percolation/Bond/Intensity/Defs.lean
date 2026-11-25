/-
PercLib intensity interface, following DECISIONS D-2 and the P-6 target reviewed
on issue #40. New definitions using mathlib's real exponential and complete-lattice
infimum; no upstream probability foundation is copied.
-/
module

public import PercLib.Percolation.Bond.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Finite intensities and extended-valued thresholds

The parameter and pair intensities are finite nonnegative numbers. Only the
thresholds are extended-valued. Loops are discarded by the existing open graph;
no diagonal restriction is imposed on the intensity. A threshold is an infimum
of parameters giving positive probability of an infinite cluster, not a
susceptibility threshold. The infimum of the empty set is infinity.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-- The canonical bond profile at finite intensity beta. -/
def intensityProfile (J : Sym2 V → ℝ≥0) (β : ℝ≥0) : Sym2 V → unitInterval :=
  fun e => ⟨1 - Real.exp (-(β : ℝ) * (J e : ℝ)), by
    constructor
    · apply sub_nonneg.mpr
      apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr β.coe_nonneg) (J e).coe_nonneg
    · exact sub_le_self _ (Real.exp_pos _).le⟩

/-- Infimum of finite parameters giving a positive probability of an infinite
cluster at the specified root. No percolation assertion at the infimum is implied. -/
def rootCriticalIntensity (J : Sym2 V → ℝ≥0) (x : V) : ℝ≥0∞ :=
  sInf {b | ∃ β : ℝ≥0, (β : ℝ≥0∞) = b ∧
    0 < law (intensityProfile J β) {ω | (cluster ω x).Infinite}}

/-- Infimum of finite parameters giving a positive probability that some infinite
cluster exists. This need not equal the threshold at an arbitrary root. -/
def globalCriticalIntensity (J : Sym2 V → ℝ≥0) : ℝ≥0∞ :=
  sInf {b | ∃ β : ℝ≥0, (β : ℝ≥0∞) = b ∧
    0 < law (intensityProfile J β) {ω | ∃ x, (cluster ω x).Infinite}}

-- Finite parameters, including beta = 0, inhabit the interface with nonzero J.
example : Sym2 Unit → unitInterval := intensityProfile (fun _ => 1) 0
example : ℝ≥0∞ := rootCriticalIntensity (fun _ : Sym2 Unit => 1) ()
example : ℝ≥0∞ := globalCriticalIntensity (fun _ : Sym2 Empty => 1)

end PercLib.Percolation.Bond
