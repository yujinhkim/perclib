/-
Adapted from PercolationContinuity (Anthropic, PBC), Copyright 2026.
Source: https://github.com/anthropics/formal-math/blob/795efb86f191735c5481675763537cfb4ff37e55/percolation/Percolation/Literature/LatticeModels/ProdBernoulliIndependence.lean
Released under the Apache License 2.0; see third_party/percolation/LICENSE
and third_party/percolation/NOTICE.

Modified for PercLib on 2026-11-14: retain the ENNReal finite-cylinder argument,
use the existing inhomogeneous law and pinned setOfPred API, and add singleton
and boundary specializations. No ambient countability assumption is used.
-/
module

public import PercLib.Probability.ProdBernoulli

/-!
# Finite all-open cylinders

The probability that every index in a finite set is open is the product of
the individual opening probabilities. The index type can be uncountable.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PercLib.Probability

variable {ι : Type*}

/-- The general-index finite-cylinder target, keeping probabilities in ENNReal. -/
def CylinderProbability (ι : Type*) : Prop :=
  ∀ (p : ι → unitInterval) (F : Finset ι),
    prodBernoulli p {ω | (F : Set ι) ⊆ ω} =
      ∏ i ∈ F, (unitInterval.toNNReal (p i) : ℝ≥0∞)

/-- Finite all-open cylinder probabilities for independent, inhomogeneous indices. -/
theorem prodBernoulli_subset (p : ι → unitInterval) (F : Finset ι) :
    prodBernoulli p {ω | (F : Set ι) ⊆ ω} =
      ∏ i ∈ F, (unitInterval.toNNReal (p i) : ℝ≥0∞) := by
  rw [prodBernoulli_eq_map]
  change (Measure.map (MeasurableEquiv.setOfPred : (ι → Prop) ≃ᵐ Set ι)
    (Measure.infinitePi fun i => bernoulliMeasure True False (p i))) _ = _
  rw [MeasurableEquiv.setOfPred.map_apply]
  have h : MeasurableEquiv.setOfPred ⁻¹' {ω | (F : Set ι) ⊆ ω} =
      Set.pi (F : Set ι) (fun _ => ({True} : Set Prop)) := by
    ext f
    simp [Set.subset_def, Set.mem_pi]
  rw [h, Measure.infinitePi_pi (μ := fun i : ι => bernoulliMeasure True False (p i))
    (s := F) (t := fun _ => ({True} : Set Prop)) (fun _ _ => measurableSet_singleton True)]
  apply Finset.prod_congr rfl
  intro i _
  simp [bernoulliMeasure_def]

/-- The finite-cylinder target is realized for every index type. -/
theorem cylinderProbability (ι : Type*) : CylinderProbability ι :=
  prodBernoulli_subset

/-- The marginal probability that a specified index is open. -/
theorem prodBernoulli_setOf_mem (p : ι → unitInterval) (i : ι) :
    prodBernoulli p {ω | i ∈ ω} = (unitInterval.toNNReal (p i) : ℝ≥0∞) := by
  simpa using prodBernoulli_subset p {i}

-- Boundary and generality witnesses: the empty finite set, an inhomogeneous pair,
-- and an uncountable index type. No finiteness or countability instance is needed.
example (p : ι → unitInterval) : prodBernoulli p {ω | (∅ : Set ι) ⊆ ω} = 1 := by
  simp

example : prodBernoulli (fun b : Bool => if b then 1 else 0)
    {ω | ({false, true} : Set Bool) ⊆ ω} = 0 := by
  simpa using prodBernoulli_subset (fun b : Bool => if b then 1 else 0) {false, true}

example (p : ℝ → unitInterval) (F : Finset ℝ) :
    prodBernoulli p {ω | (F : Set ℝ) ⊆ ω} =
      ∏ i ∈ F, (unitInterval.toNNReal (p i) : ℝ≥0∞) :=
  prodBernoulli_subset p F

end PercLib.Probability
