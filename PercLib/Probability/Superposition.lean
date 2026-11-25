/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New for this project (issue 127, Q-11, items 1 to 3). No upstream proof is copied.
-/
module

public import PercLib.Probability.Cylinder
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Restriction, complement, thinning and superposition of Bernoulli configurations

For a profile `p : ι → unitInterval` on an arbitrary index type:

* restricting to any subset `S` gives the law with the restricted profile;
* complementing gives the law with profile `σ ∘ p`, where `σ = unitInterval.symm`;
* the intersection of independent configurations has the product profile `p * r`;
* the union of independent configurations has profile `σ (σ p * σ r)`, that is open
  probability `1 - (1 - p)(1 - r)`.

Thinning is proved by identifying the two laws on the π-system of events
`{ω | F ⊆ ω}`, `F` finite, which generates the σ-algebra. Superposition follows from thinning
and complements by De Morgan.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal unitInterval

namespace PercLib.Probability

variable {ι : Type*}

/-! ### Restriction -/

/-- Restricting a configuration to any subset `S` gives the law of the restricted profile.
This generalises `prodBernoulli_map_restrict` from finite sets. -/
theorem prodBernoulli_map_preimage_val (p : ι → unitInterval) (S : Set ι) :
    (prodBernoulli p).map (fun ω => (Subtype.val ⁻¹' ω : Set S)) =
      prodBernoulli (fun i : S => p i) := by
  have hm : Measurable (fun ω : Set ι => (Subtype.val ⁻¹' ω : Set S)) := by
    apply Measurable.of_mem
    intro i
    exact (measurableSet_mem i.val).mem
  have he : Measurable (fun f : ι → Prop => {i | f i}) :=
    MeasurableEquiv.setOfPred.measurable
  have hs : Measurable (fun f : S → Prop => {i | f i}) :=
    MeasurableEquiv.setOfPred.measurable
  rw [prodBernoulli_eq_map, prodBernoulli_eq_map, Measure.map_map hm he]
  change Measure.map ((fun f : S → Prop => {i | f i}) ∘ S.domRestrict)
      (Measure.infinitePi fun i => bernoulliMeasure True False (p i)) = _
  rw [← Measure.map_map hs (by fun_prop), Measure.infinitePi_map_restrict']

/-! ### Complement -/

theorem bernoulliMeasure_map_not (p : unitInterval) :
    (bernoulliMeasure True False p).map Not = bernoulliMeasure True False (σ p) := by
  have hm : Measurable Not := Measurable.of_discrete
  rw [bernoulliMeasure_def, bernoulliMeasure_def, Measure.map_add _ _ hm,
    Measure.map_smul _ hm.aemeasurable, Measure.map_smul _ hm.aemeasurable,
    Measure.map_dirac' hm, Measure.map_dirac' hm, unitInterval.symm_symm, add_comm]
  simp

/-- Complementing a configuration replaces the profile `p` by `σ ∘ p`.

The same statement is `prodBernoulli_map_compl` in #149 (`HarrisDecreasing.lean`); this copy
has its own name so that both pull requests build, and is to be deduplicated once both merge. -/
theorem prodBernoulli_map_compl_eq_symm (p : ι → unitInterval) :
    (prodBernoulli p).map compl = prodBernoulli (fun i => σ (p i)) := by
  have he : Measurable (fun f : ι → Prop => {i | f i}) :=
    MeasurableEquiv.setOfPred.measurable
  have hc : Measurable (compl : Set ι → Set ι) :=
    Measurable.of_mem fun i => (measurable_set_mem i).not
  rw [prodBernoulli_eq_map, prodBernoulli_eq_map, Measure.map_map hc he]
  have hpi := Measure.infinitePi_map_pi (μ := fun i => bernoulliMeasure True False (p i))
    (f := fun _ => Not) (fun _ => Measurable.of_discrete)
  simp only [bernoulliMeasure_map_not] at hpi
  rw [← hpi, Measure.map_map he (by fun_prop)]
  rfl

/-! ### Thinning -/

/-- The all-open events `{ω | F ⊆ ω}` over finite `F` generate the σ-algebra. -/
theorem generateFrom_finset_subset :
    MeasurableSpace.generateFrom {A : Set (Set ι) | ∃ F : Finset ι, A = {ω | (F : Set ι) ⊆ ω}} =
      Set.instMeasurableSpace := by
  refine le_antisymm (MeasurableSpace.generateFrom_le ?_) ?_
  · rintro A ⟨F, rfl⟩
    have : {ω : Set ι | (F : Set ι) ⊆ ω} = ⋂ i ∈ F, {ω | i ∈ ω} := by
      ext ω
      simp [Set.subset_def]
    rw [this]
    exact Finset.measurableSet_biInter F fun i _ => measurableSet_mem i
  · have hid : Measurable[MeasurableSpace.generateFrom
        {A : Set (Set ι) | ∃ F : Finset ι, A = {ω | (F : Set ι) ⊆ ω}}] (id : Set ι → Set ι) := by
      refine @Measurable.of_mem _ _ (MeasurableSpace.generateFrom _) _ fun i => ?_
      refine @measurable_to_prop _ (MeasurableSpace.generateFrom _) _ ?_
      refine MeasurableSpace.measurableSet_generateFrom ⟨{i}, ?_⟩
      ext ω
      simp
    simpa [MeasurableSpace.comap_id] using hid.comap_le

theorem isPiSystem_finset_subset :
    IsPiSystem {A : Set (Set ι) | ∃ F : Finset ι, A = {ω | (F : Set ι) ⊆ ω}} := by
  classical
  rintro A ⟨F, rfl⟩ B ⟨G, rfl⟩ -
  refine ⟨F ∪ G, ?_⟩
  ext ω
  simp [Set.union_subset_iff]

/-- Two probability laws on configurations agree once they agree on the all-open events of
finite sets. -/
theorem measure_ext_of_finset_subset (μ ν : Measure (Set ι)) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (h : ∀ F : Finset ι, μ {ω | (F : Set ι) ⊆ ω} = ν {ω | (F : Set ι) ⊆ ω}) : μ = ν :=
  ext_of_generate_finite _ generateFrom_finset_subset.symm isPiSystem_finset_subset
    (by rintro _ ⟨F, rfl⟩; exact h F) (by simp)

/-- **Thinning.** The intersection of independent configurations has the product profile. -/
theorem prodBernoulli_prod_map_inter (p r : ι → unitInterval) :
    ((prodBernoulli p).prod (prodBernoulli r)).map (fun ω => ω.1 ∩ ω.2) =
      prodBernoulli (fun i => p i * r i) := by
  have hm : Measurable (fun ω : Set ι × Set ι => ω.1 ∩ ω.2) :=
    measurable_fst.inter measurable_snd
  have : IsProbabilityMeasure (((prodBernoulli p).prod (prodBernoulli r)).map
      (fun ω : Set ι × Set ι => ω.1 ∩ ω.2)) :=
    (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance
  refine measure_ext_of_finset_subset _ _ fun F => ?_
  have hF : MeasurableSet {ω : Set ι | (F : Set ι) ⊆ ω} :=
    generateFrom_finset_subset (ι := ι) ▸
      MeasurableSpace.measurableSet_generateFrom ⟨F, rfl⟩
  rw [Measure.map_apply hm hF]
  have hpre : (fun ω : Set ι × Set ι => ω.1 ∩ ω.2) ⁻¹' {ω | (F : Set ι) ⊆ ω} =
      {ω : Set ι | (F : Set ι) ⊆ ω} ×ˢ {ω : Set ι | (F : Set ι) ⊆ ω} := by
    ext ω
    simp [Set.subset_inter_iff]
  rw [hpre, Measure.prod_prod, prodBernoulli_subset, prodBernoulli_subset,
    prodBernoulli_subset, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← ENNReal.coe_mul]
  congr 1

/-! ### Superposition -/

/-- **Superposition.** The union of independent configurations has open probability
`1 - (1 - p)(1 - r)`. -/
theorem prodBernoulli_prod_map_union (p r : ι → unitInterval) :
    ((prodBernoulli p).prod (prodBernoulli r)).map (fun ω => ω.1 ∪ ω.2) =
      prodBernoulli (fun i => σ (σ (p i) * σ (r i))) := by
  have hc : Measurable (compl : Set ι → Set ι) :=
    Measurable.of_mem fun i => (measurable_set_mem i).not
  have hi : Measurable (fun ω : Set ι × Set ι => ω.1 ∩ ω.2) :=
    measurable_fst.inter measurable_snd
  have hcc : Measurable (Prod.map (compl : Set ι → Set ι) (compl : Set ι → Set ι)) :=
    hc.prodMap hc
  have hcomp : (fun ω : Set ι × Set ι => ω.1 ∪ ω.2) =
      compl ∘ (fun ω : Set ι × Set ι => ω.1 ∩ ω.2) ∘ Prod.map compl compl := by
    funext ω
    simp [Set.compl_inter]
  rw [hcomp, ← Measure.map_map hc (hi.comp hcc), ← Measure.map_map hi hcc,
    ← Measure.map_prod_map _ _ hc hc, prodBernoulli_map_compl_eq_symm,
    prodBernoulli_map_compl_eq_symm, prodBernoulli_prod_map_inter, prodBernoulli_map_compl_eq_symm]

/-! ### Non-vacuity -/

/-- Superposition with an always-open configuration is always open. -/
example (p : ι → unitInterval) :
    ((prodBernoulli p).prod (prodBernoulli (fun _ => (1 : unitInterval)))).map
      (fun ω => ω.1 ∪ ω.2) = prodBernoulli (fun _ => (1 : unitInterval)) := by
  rw [prodBernoulli_prod_map_union]
  congr 1
  funext i
  simp

/-- Thinning by an always-closed configuration is always closed. -/
example (p : ι → unitInterval) :
    ((prodBernoulli p).prod (prodBernoulli (fun _ => (0 : unitInterval)))).map
      (fun ω => ω.1 ∩ ω.2) = prodBernoulli (fun _ => (0 : unitInterval)) := by
  rw [prodBernoulli_prod_map_inter]
  congr 1
  funext i
  simp

/-- Restriction to an infinite subset: the even integers. -/
example (p : ℤ → unitInterval) :
    (prodBernoulli p).map (fun ω => (Subtype.val ⁻¹' ω : Set {n : ℤ | Even n})) =
      prodBernoulli (fun i : {n : ℤ | Even n} => p i) :=
  prodBernoulli_map_preimage_val p _

end PercLib.Probability

end
