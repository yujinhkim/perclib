/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New for this project (issue 191, Q-31). No upstream proof is copied.
-/
module

public import PercLib.Probability.Superposition
public import PercLib.Percolation.Bond.Basic

/-!
# One coordinate of a Bernoulli product law

On an arbitrary index type, forcing coordinate `e` open (`ω ↦ insert e ω`) or closed
(`ω ↦ ω \ {e}`) gives the laws with `q e` replaced by `1` or `0`, and
`prodBernoulli q = q_e • prodBernoulli q[e ↦ 1] + (1 - q_e) • prodBernoulli q[e ↦ 0]` as
measures. Hence every probability is affine in `q e`, with slope
`P(insert e ω ∈ A) - P(ω \ {e} ∈ A)`, which for an increasing event is the probability that
`e` is pivotal. This is Russo's formula for one coordinate, with no finiteness assumption.
All laws are identified on the all-open events of finite sets (`measure_ext_of_finset_subset`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal unitInterval

namespace PercLib.Probability

variable {ι : Type*}

theorem measurable_insert (e : ι) : Measurable fun ω : Set ι => insert e ω := by
  classical
  refine Measurable.of_mem fun i => ?_
  by_cases h : i = e
  · subst h
    simp only [mem_insert_iff, true_or]
    exact measurable_const
  · simp only [mem_insert_iff, h, false_or]
    exact measurable_set_mem i

theorem measurable_diff_singleton (e : ι) : Measurable fun ω : Set ι => ω \ {e} := by
  classical
  refine Measurable.of_mem fun i => ?_
  by_cases h : i = e
  · subst h
    simp only [mem_sdiff, mem_singleton_iff, not_true_eq_false, and_false]
    exact measurable_const
  · simp only [mem_sdiff, mem_singleton_iff, h, not_false_eq_true, and_true]
    exact measurable_set_mem i

theorem measurableSet_setOf_finset_subset' (F : Finset ι) :
    MeasurableSet {ω : Set ι | (F : Set ι) ⊆ ω} :=
  generateFrom_finset_subset (ι := ι) ▸ MeasurableSpace.measurableSet_generateFrom ⟨F, rfl⟩

variable [DecidableEq ι]

theorem prod_toNNReal_update (q : ι → unitInterval) (e : ι) (t : unitInterval)
    (F : Finset ι) :
    ∏ i ∈ F, (unitInterval.toNNReal (update q e t i) : ℝ≥0∞) =
      if e ∈ F then (unitInterval.toNNReal t : ℝ≥0∞) *
          ∏ i ∈ F.erase e, (unitInterval.toNNReal (q i) : ℝ≥0∞)
        else ∏ i ∈ F, (unitInterval.toNNReal (q i) : ℝ≥0∞) := by
  have : (fun i => (unitInterval.toNNReal (update q e t i) : ℝ≥0∞)) =
      update (fun i => (unitInterval.toNNReal (q i) : ℝ≥0∞)) e (unitInterval.toNNReal t) := by
    funext i
    by_cases h : i = e
    · subst h; simp
    · simp [h]
  rw [this]
  split_ifs with he
  · rw [Finset.prod_update_of_mem he, Finset.sdiff_singleton_eq_erase]
  · exact Finset.prod_update_of_notMem he _ _

/-! ### Endpoint laws -/

/-- **Forcing a coordinate open.** -/
theorem prodBernoulli_map_insert (q : ι → unitInterval) (e : ι) :
    (prodBernoulli q).map (fun ω => insert e ω) = prodBernoulli (update q e 1) := by
  classical
  have : IsProbabilityMeasure ((prodBernoulli q).map fun ω => insert e ω) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_insert e).aemeasurable).2 inferInstance
  refine measure_ext_of_finset_subset _ _ fun F => ?_
  rw [Measure.map_apply (measurable_insert e) (measurableSet_setOf_finset_subset' F),
    prodBernoulli_subset, prod_toNNReal_update]
  have hpre : (fun ω : Set ι => insert e ω) ⁻¹' {ω | (F : Set ι) ⊆ ω} =
      {ω | ((F.erase e : Finset ι) : Set ι) ⊆ ω} := by
    ext ω
    simp only [mem_preimage, mem_ofPred_eq, Finset.coe_erase, sdiff_subset_iff,
      singleton_union]
  rw [hpre, prodBernoulli_subset]
  split_ifs with he
  · simp
  · rw [Finset.erase_eq_of_notMem he]

/-- **Forcing a coordinate closed.** -/
theorem prodBernoulli_map_diff_singleton (q : ι → unitInterval) (e : ι) :
    (prodBernoulli q).map (fun ω => ω \ {e}) = prodBernoulli (update q e 0) := by
  classical
  have : IsProbabilityMeasure ((prodBernoulli q).map fun ω => ω \ {e}) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_diff_singleton e).aemeasurable).2
      inferInstance
  refine measure_ext_of_finset_subset _ _ fun F => ?_
  rw [Measure.map_apply (measurable_diff_singleton e) (measurableSet_setOf_finset_subset' F),
    prodBernoulli_subset, prod_toNNReal_update]
  split_ifs with he
  · have hpre : (fun ω : Set ι => ω \ {e}) ⁻¹' {ω | (F : Set ι) ⊆ ω} = ∅ := by
      ext ω
      simp only [mem_preimage, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      intro h
      exact (h he).2 rfl
    simp [hpre]
  · have hpre : (fun ω : Set ι => ω \ {e}) ⁻¹' {ω | (F : Set ι) ⊆ ω} =
        {ω | (F : Set ι) ⊆ ω} := by
      ext ω
      simp only [mem_preimage, mem_ofPred_eq, subset_sdiff, disjoint_singleton_right,
        Finset.mem_coe, he, not_false_eq_true, and_true]
    rw [hpre, prodBernoulli_subset]

/-! ### Affinity -/

/-- **Affinity, as measures.** -/
theorem prodBernoulli_eq_smul_add_smul (q : ι → unitInterval) (e : ι) :
    prodBernoulli q = (unitInterval.toNNReal (q e)) • prodBernoulli (update q e 1) +
      (unitInterval.toNNReal (σ (q e))) • prodBernoulli (update q e 0) := by
  classical
  have hsum : (unitInterval.toNNReal (q e) : ℝ≥0∞) + unitInterval.toNNReal (σ (q e)) = 1 := by
    rw [← ENNReal.coe_add]
    have : unitInterval.toNNReal (q e) + unitInterval.toNNReal (σ (q e)) = 1 := by
      apply NNReal.eq
      rw [NNReal.coe_add]
      change (q e : ℝ) + (1 - q e) = 1
      ring
    rw [this, ENNReal.coe_one]
  have : IsProbabilityMeasure ((unitInterval.toNNReal (q e)) • prodBernoulli (update q e 1) +
      (unitInterval.toNNReal (σ (q e))) • prodBernoulli (update q e 0)) :=
    ⟨by simp⟩
  refine measure_ext_of_finset_subset _ _ fun F => ?_
  simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul, ENNReal.smul_def,
    prodBernoulli_subset, prod_toNNReal_update]
  split_ifs with he
  · rw [← Finset.mul_prod_erase F _ he]
    simp
  · rw [← add_mul, hsum, one_mul]

/-- **Affinity.** Every probability is affine in one coordinate. -/
theorem prodBernoulli_eq_affine (q : ι → unitInterval) (e : ι) (A : Set (Set ι)) :
    (prodBernoulli q).real A =
      (q e : ℝ) * (prodBernoulli (update q e 1)).real A +
        (1 - (q e : ℝ)) * (prodBernoulli (update q e 0)).real A := by
  conv_lhs => rw [prodBernoulli_eq_smul_add_smul q e]
  rw [measureReal_def, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    ENNReal.toReal_add (by simp [ENNReal.smul_def, ENNReal.mul_eq_top])
      (by simp [ENNReal.smul_def, ENNReal.mul_eq_top]),
    ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_mul, measureReal_def, measureReal_def, ENNReal.coe_toReal,
    ENNReal.coe_toReal]
  rfl

/-- **Endpoint laws, as probabilities.** -/
theorem prodBernoulli_update_one_apply (q : ι → unitInterval) (e : ι) {A : Set (Set ι)}
    (hA : MeasurableSet A) :
    prodBernoulli (update q e 1) A = prodBernoulli q {ω | insert e ω ∈ A} := by
  rw [← prodBernoulli_map_insert, Measure.map_apply (measurable_insert e) hA]
  rfl

theorem prodBernoulli_update_zero_apply (q : ι → unitInterval) (e : ι) {A : Set (Set ι)}
    (hA : MeasurableSet A) :
    prodBernoulli (update q e 0) A = prodBernoulli q {ω | ω \ {e} ∈ A} := by
  rw [← prodBernoulli_map_diff_singleton, Measure.map_apply (measurable_diff_singleton e) hA]
  rfl

/-! ### The slope -/

/-- **One-coordinate Russo.** Along `t ↦ q[e ↦ t]`, a probability is affine with slope
`P_q(insert e ω ∈ A) - P_q(ω \ {e} ∈ A)`. -/
theorem prodBernoulli_update_real_eq (q : ι → unitInterval) (e : ι) {A : Set (Set ι)}
    (hA : MeasurableSet A) (t : unitInterval) :
    (prodBernoulli (update q e t)).real A =
      (prodBernoulli q).real {ω | ω \ {e} ∈ A} +
        (t : ℝ) * ((prodBernoulli q).real {ω | insert e ω ∈ A} -
          (prodBernoulli q).real {ω | ω \ {e} ∈ A}) := by
  rw [prodBernoulli_eq_affine (update q e t) e A, update_self, update_idem, update_idem,
    measureReal_def, measureReal_def, prodBernoulli_update_one_apply q e hA,
    prodBernoulli_update_zero_apply q e hA, measureReal_def, measureReal_def]
  ring

omit [DecidableEq ι] in
/-- For an increasing event the slope is the probability that `e` is pivotal. -/
theorem prodBernoulli_real_insert_sub_diff_eq_pivotal (q : ι → unitInterval) (e : ι)
    {A : Set (Set ι)} (hA : MeasurableSet A) (hup : IsUpperSet A) :
    (prodBernoulli q).real {ω | insert e ω ∈ A} - (prodBernoulli q).real {ω | ω \ {e} ∈ A} =
      (prodBernoulli q).real {ω | insert e ω ∈ A ∧ ω \ {e} ∉ A} := by
  have h1 : MeasurableSet {ω : Set ι | insert e ω ∈ A} := measurable_insert e hA
  have h2 : MeasurableSet {ω : Set ι | ω \ {e} ∈ A} := measurable_diff_singleton e hA
  have hsub : {ω : Set ι | ω \ {e} ∈ A} ⊆ {ω | insert e ω ∈ A} := fun ω hω =>
    hup (fun i hi => mem_insert_of_mem e hi.1) hω
  have hdiff : {ω : Set ι | insert e ω ∈ A ∧ ω \ {e} ∉ A} =
      {ω | insert e ω ∈ A} \ {ω | ω \ {e} ∈ A} := rfl
  rw [hdiff, measureReal_sdiff hsub h2]

end PercLib.Probability

/-! ### Bond corollary -/

namespace PercLib.Percolation.Bond

open PercLib.Probability

variable {V : Type*}

/-- **One-pair Russo for `τ`.** Along `t ↦ q[e ↦ t]`, the two-point function is affine with
slope the probability that `e` is pivotal for `x ↔ y`. -/
theorem tau_update_real_eq [Countable V] [DecidableEq V] (q : Sym2 V → unitInterval) (e : Sym2 V) (x y : V)
    (t : unitInterval) :
    (tau (update q e t) x y).toReal =
      (law q).real {ω | ω \ {e} ∈ conn x y} +
        (t : ℝ) * (law q).real {ω | insert e ω ∈ conn x y ∧ ω \ {e} ∉ conn x y} := by
  rw [tau, ← measureReal_def]
  simp only [law]
  rw [prodBernoulli_update_real_eq q e (measurableSet_conn x y),
    prodBernoulli_real_insert_sub_diff_eq_pivotal q e (measurableSet_conn x y)
      fun _ _ h hω => conn_mono h hω]

/-- A diagonal pair is never pivotal, so `τ` does not depend on its parameter. -/
theorem setOf_pivotal_diag_eq_empty (e : Sym2 V) (he : e.IsDiag) (x y : V) :
    {ω : Config V | insert e ω ∈ conn x y ∧ ω \ {e} ∉ conn x y} = ∅ := by
  ext ω
  simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_not]
  intro h
  have hg : openGraph (insert e ω) = openGraph (ω \ {e}) := by
    ext a b
    simp only [openGraph_adj_iff, mem_insert_iff, mem_sdiff, mem_singleton_iff]
    constructor
    · rintro ⟨h1 | h1, h2⟩
      · exact absurd (h1 ▸ he) (Sym2.mk_isDiag_iff.not.2 h2)
      · exact ⟨⟨h1, fun h3 => (Sym2.mk_isDiag_iff.not.2 h2) (h3 ▸ he)⟩, h2⟩
    · rintro ⟨⟨h1, -⟩, h2⟩
      exact ⟨Or.inr h1, h2⟩
  rwa [mem_conn_iff, ← hg]

/-! ### Non-vacuity -/

/-- `A = {0 ∈ ω ∧ 1 ∈ ω}` on `ℕ`: the slope in coordinate `0` is the probability that `1` is
open, here instantiated through the general formula. -/
example (q : ℕ → unitInterval) (t : unitInterval) :
    (prodBernoulli (update q 0 t)).real {ω | 0 ∈ ω ∧ 1 ∈ ω} =
      (prodBernoulli q).real {ω | ω \ {0} ∈ {ω : Set ℕ | 0 ∈ ω ∧ 1 ∈ ω}} +
        (t : ℝ) * (prodBernoulli q).real {ω | insert 0 ω ∈ {ω : Set ℕ | 0 ∈ ω ∧ 1 ∈ ω} ∧
          ω \ {0} ∉ {ω : Set ℕ | 0 ∈ ω ∧ 1 ∈ ω}} := by
  have hA : MeasurableSet {ω : Set ℕ | 0 ∈ ω ∧ 1 ∈ ω} :=
    (measurableSet_mem 0).inter (measurableSet_mem 1)
  rw [prodBernoulli_update_real_eq q 0 hA,
    prodBernoulli_real_insert_sub_diff_eq_pivotal q 0 hA
      fun _ _ h hω => ⟨h hω.1, h hω.2⟩]

end PercLib.Percolation.Bond

end
