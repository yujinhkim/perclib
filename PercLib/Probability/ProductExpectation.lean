/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Adapted from NearCritical/ProductExpectation.lean at
tomhutchcroft/near-critical-diffusivity@c820fea91a7482c1755de0ec94ecb9f59ccfcacc,
under Tom Hutchcroft's reuse permission (docs/DECISIONS.md R-3).
The native upstream file has no licence header; no upstream Apache licence is asserted.
Changed on 2026-11-14: canonical Set configurations and prodBernoulli, arbitrary
coordinate profiles and ambient indices, with no lattice probability foundation.
-/
module

public import PercLib.Probability.ProdBernoulli
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.Data.Fintype.Powerset

/-!
# Explicit finite-profile expectations

The weights include both open and closed coordinates. Arbitrary profiles,
including mixtures of zero and one, are handled under the existing law.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

namespace PercLib.Probability

variable {ι : Type*}

/-- Full configuration masses for finite, inhomogeneous Bernoulli coordinates. -/
theorem prodBernoulli_singleton [Fintype ι] (p : ι → unitInterval) (ω : Set ι) :
    prodBernoulli p {ω} = ∏ i : ι,
      if i ∈ ω then (unitInterval.toNNReal (p i) : ℝ≥0∞)
      else (unitInterval.toNNReal (unitInterval.symm (p i)) : ℝ≥0∞) := by
  rw [prodBernoulli_eq_map]
  change (Measure.map (MeasurableEquiv.setOfPred : (ι → Prop) ≃ᵐ Set ι)
    (Measure.infinitePi fun i => bernoulliMeasure True False (p i))) _ = _
  rw [MeasurableEquiv.setOfPred.map_apply]
  have he : MeasurableEquiv.setOfPred ⁻¹' {ω} = {fun i => i ∈ ω} := by
    ext f
    change ({i | f i} = ω) ↔ f = fun i => i ∈ ω
    constructor
    · intro h
      funext i
      exact propext (Set.ext_iff.mp h i)
    · rintro rfl
      rfl
  rw [he, Measure.infinitePi_eq_pi, Measure.pi_singleton]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ ω <;> simp [hi, bernoulliMeasure_def]

theorem prodBernoulli_real_singleton [Fintype ι] (p : ι → unitInterval) (ω : Set ι) :
    (prodBernoulli p).real {ω} =
      ∏ i : ι, if i ∈ ω then (p i : ℝ) else 1 - (p i : ℝ) := by
  rw [measureReal_def, prodBernoulli_singleton, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ ω <;> simp [hi]

/-- Every real observable on finite configurations has the explicit weighted-sum integral. -/
theorem integral_prodBernoulli [Fintype ι] (p : ι → unitInterval) (f : Set ι → ℝ) :
    ∫ ω, f ω ∂prodBernoulli p =
      ∑ ω : Set ι, f ω * ∏ i : ι, if i ∈ ω then (p i : ℝ) else 1 - (p i : ℝ) := by
  rw [integral_fintype (Integrable.of_finite : Integrable f _)]
  simp only [prodBernoulli_real_singleton, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro ω _
  exact mul_comm _ _

/-- Restricting an arbitrary-index configuration gives the canonical finite-profile law. -/
theorem prodBernoulli_map_restrict (p : ι → unitInterval) (s : Finset ι) :
    (prodBernoulli p).map (fun ω => (Subtype.val ⁻¹' ω : Set s)) =
      prodBernoulli (fun i : s => p i) := by
  have hm : Measurable (fun ω : Set ι => (Subtype.val ⁻¹' ω : Set s)) := by
    apply Measurable.of_mem
    intro i
    exact (measurableSet_mem i.val).mem
  have he : Measurable (fun f : ι → Prop => {i | f i}) :=
    MeasurableEquiv.setOfPred.measurable
  have hs : Measurable (fun f : s → Prop => {i | f i}) :=
    MeasurableEquiv.setOfPred.measurable
  rw [prodBernoulli_eq_map, prodBernoulli_eq_map, Measure.map_map hm he]
  change Measure.map ((fun f : s → Prop => {i | f i}) ∘ s.restrict)
      (Measure.infinitePi fun i => bernoulliMeasure True False (p i)) = _
  rw [← Measure.map_map hs (Finset.measurable_restrict _),
    Measure.infinitePi_map_restrict, Measure.infinitePi_eq_pi]

/-- Finite-cylinder expectations on arbitrary ambient indices, with arbitrary profiles. -/
theorem integral_prodBernoulli_cylinder (p : ι → unitInterval) (s : Finset ι)
    (f : Set s → ℝ) :
    ∫ ω, f (Subtype.val ⁻¹' ω) ∂prodBernoulli p =
      ∑ η : Set s, f η * ∏ i : s, if i ∈ η then (p i : ℝ) else 1 - (p i : ℝ) := by
  have hm : Measurable (fun ω : Set ι => (Subtype.val ⁻¹' ω : Set s)) := by
    apply Measurable.of_mem
    intro i
    exact (measurableSet_mem i.val).mem
  rw [← integral_map hm.aemeasurable (measurable_of_finite f).aestronglyMeasurable,
    prodBernoulli_map_restrict, integral_prodBernoulli]

example (p : Empty → unitInterval) (f : Set Empty → ℝ) :
    ∫ ω, f ω ∂prodBernoulli p = f ∅ := by
  rw [integral_prodBernoulli]
  simp
  exact congrArg f (Subsingleton.elim _ _)

example (p : Bool → unitInterval) :
    (prodBernoulli p).real {({true} : Set Bool)} =
      (p true : ℝ) * (1 - (p false : ℝ)) := by
  simp [prodBernoulli_real_singleton]

example (f : Set Bool → ℝ) :
    ∫ ω, f ω ∂prodBernoulli (fun b : Bool => if b then 1 else 0) = f {true} := by
  rw [integral_prodBernoulli]
  rw [Finset.sum_eq_single ({true} : Set Bool)]
  · simp
  · intro ω _ hω
    by_cases ht : true ∈ ω <;> by_cases hf : false ∈ ω
    · simp [ht, hf]
    · exfalso
      apply hω
      ext b
      cases b <;> simp [ht, hf]
    · simp [ht, hf]
    · simp [ht, hf]
  · simp

end PercLib.Probability

