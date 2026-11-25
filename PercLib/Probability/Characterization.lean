/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New for this project (issue 200, Q-39). No upstream proof is copied.
-/
module

public import PercLib.Probability.Superposition

/-!
# Characterisation of `prodBernoulli` by its all-open probabilities

A probability measure on `Set ι` equals `prodBernoulli q` as soon as, for every finite `F`, the
probability that all of `F` is open is `∏_{i ∈ F} q i`. The π-system of these events and the
fact that it generates the σ-algebra are `isPiSystem_finset_subset` and
`generateFrom_finset_subset` in `Superposition.lean`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace PercLib.Probability

variable {ι κ : Type*}

/-- **Characterisation.** A probability law on configurations with the all-open probabilities
of `prodBernoulli q` is `prodBernoulli q`. -/
theorem eq_prodBernoulli_of_subset (μ : Measure (Set ι)) [IsProbabilityMeasure μ]
    (q : ι → unitInterval)
    (h : ∀ F : Finset ι, μ {ω | (F : Set ι) ⊆ ω} = ∏ i ∈ F, (unitInterval.toNNReal (q i) : ℝ≥0∞)) :
    μ = prodBernoulli q :=
  measure_ext_of_finset_subset μ _ fun F => by rw [h, prodBernoulli_subset]

/-- The all-open events of finite sets are measurable. -/
theorem measurableSet_setOf_finset_coe_subset (F : Finset ι) :
    MeasurableSet {ω : Set ι | (F : Set ι) ⊆ ω} :=
  generateFrom_finset_subset (ι := ι) ▸ MeasurableSpace.measurableSet_generateFrom ⟨F, rfl⟩

/-- A push-forward of a Bernoulli law is a Bernoulli law exactly when the all-open
probabilities match. -/
theorem map_prodBernoulli_eq_iff (q : ι → unitInterval) {f : Set ι → Set κ}
    (hf : Measurable f) (r : κ → unitInterval) :
    (prodBernoulli q).map f = prodBernoulli r ↔
      ∀ F : Finset κ, prodBernoulli q (f ⁻¹' {ω | (F : Set κ) ⊆ ω}) =
        ∏ i ∈ F, (unitInterval.toNNReal (r i) : ℝ≥0∞) := by
  constructor
  · intro h F
    rw [← Measure.map_apply hf (measurableSet_setOf_finset_coe_subset F), h,
      prodBernoulli_subset]
  · intro h
    have : IsProbabilityMeasure ((prodBernoulli q).map f) :=
      (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).2 inferInstance
    refine eq_prodBernoulli_of_subset _ r fun F => ?_
    rw [Measure.map_apply hf (measurableSet_setOf_finset_coe_subset F), h]

/-! ### Corollaries, as tests -/

/-- The identity map: `prodBernoulli q` is characterised by its own all-open probabilities. -/
example (q : ι → unitInterval) : (prodBernoulli q).map id = prodBernoulli q :=
  (map_prodBernoulli_eq_iff q measurable_id q).2 fun F => by
    rw [preimage_id, prodBernoulli_subset]

/-- Complementing twice is the identity, re-derived from the characterisation. -/
example (q : ι → unitInterval) :
    (prodBernoulli q).map (compl ∘ compl) = prodBernoulli q := by
  refine (map_prodBernoulli_eq_iff q ?_ q).2 fun F => ?_
  · exact (Measurable.of_mem fun i => (measurable_set_mem i).not).comp
      (Measurable.of_mem fun i => (measurable_set_mem i).not)
  · have : (compl ∘ compl : Set ι → Set ι) ⁻¹' {ω | (F : Set ι) ⊆ ω} =
        {ω | (F : Set ι) ⊆ ω} := by
      ext ω
      simp
    rw [this, prodBernoulli_subset]

/-- The empty index type: the only configuration is `∅`. -/
example (μ : Measure (Set Empty)) [IsProbabilityMeasure μ] :
    μ = prodBernoulli (fun _ => 0) :=
  eq_prodBernoulli_of_subset μ _ fun F => by
    rw [Finset.eq_empty_of_isEmpty F]
    simp only [Finset.coe_empty, empty_subset, ofPred_true, measure_univ, Finset.prod_empty]

end PercLib.Probability

end
