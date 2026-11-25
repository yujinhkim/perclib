/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New for this project (issue 127, Q-11, items 4 to 6). No upstream proof is copied.
-/
module

public import PercLib.Percolation.Bond.Intensity.Defs
public import PercLib.Probability.Superposition
public import PercLib.Probability.ProdBernoulliIndependence
public import PercLib.Probability.OpenEventHarris
public import Mathlib.Probability.BorelCantelli

/-!
# Sprinkling and the meaning of the intensity thresholds

The intensity profile at `β₁ + β₂` is the superposition of independent configurations at
`β₁` and `β₂`, because `e^{-(β₁+β₂)J} = e^{-β₁J} e^{-β₂J}`. Hence every measurable increasing
event is monotone in `β`, and the thresholds `rootCriticalIntensity` and
`globalCriticalIntensity` separate the parameters with no infinite cluster from those with
an infinite cluster with positive probability.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Set PercLib.Probability
open scoped ENNReal NNReal unitInterval

namespace PercLib.Percolation.Bond

variable {V : Type*}

/-! ### Additivity of the intensity -/

theorem coe_symm_intensityProfile (J : Sym2 V → ℝ≥0) (β : ℝ≥0) (e : Sym2 V) :
    ((σ (intensityProfile J β e) : unitInterval) : ℝ) = Real.exp (-(β : ℝ) * (J e : ℝ)) := by
  rw [unitInterval.coe_symm_eq]
  simp [intensityProfile]

/-- The intensity profile at `β₁ + β₂` is the superposition profile of those at `β₁` and
`β₂`. -/
theorem intensityProfile_add (J : Sym2 V → ℝ≥0) (β₁ β₂ : ℝ≥0) (e : Sym2 V) :
    intensityProfile J (β₁ + β₂) e =
      σ (σ (intensityProfile J β₁ e) * σ (intensityProfile J β₂ e)) := by
  apply Subtype.ext
  rw [unitInterval.coe_symm_eq, Set.Icc.coe_mul, coe_symm_intensityProfile,
    coe_symm_intensityProfile, ← Real.exp_add]
  simp only [intensityProfile, NNReal.coe_add]
  congr 2
  ring

/-- **Sprinkling.** The law at `β₁ + β₂` is the law of the union of independent
configurations at `β₁` and `β₂`. -/
theorem law_intensityProfile_add (J : Sym2 V → ℝ≥0) (β₁ β₂ : ℝ≥0) :
    law (intensityProfile J (β₁ + β₂)) =
      ((law (intensityProfile J β₁)).prod (law (intensityProfile J β₂))).map
        (fun ω => ω.1 ∪ ω.2) := by
  simp only [law]
  rw [prodBernoulli_prod_map_union]
  congr 1
  funext e
  exact intensityProfile_add J β₁ β₂ e

/-! ### Monotonicity in `β` -/

/-- Every measurable increasing event is monotone in the intensity. No countability is
needed. -/
theorem law_intensityProfile_mono {A : Set (Config V)} (hA : IsUpperSet A)
    (hAm : MeasurableSet A) (J : Sym2 V → ℝ≥0) {β₁ β₂ : ℝ≥0} (h : β₁ ≤ β₂) :
    law (intensityProfile J β₁) A ≤ law (intensityProfile J β₂) A := by
  obtain ⟨δ, rfl⟩ : ∃ δ, β₂ = β₁ + δ := ⟨β₂ - β₁, (add_tsub_cancel_of_le h).symm⟩
  have hu : Measurable (fun ω : Config V × Config V => ω.1 ∪ ω.2) :=
    measurable_fst.union measurable_snd
  rw [law_intensityProfile_add, Measure.map_apply hu hAm]
  calc law (intensityProfile J β₁) A
      = ((law (intensityProfile J β₁)).prod (law (intensityProfile J δ))) (A ×ˢ univ) := by
        rw [Measure.prod_prod, measure_univ, mul_one]
    _ ≤ _ := measure_mono fun ω hω => hA subset_union_left hω.1

/-! ### The thresholds -/

/-- The event that some cluster is infinite is increasing. -/
theorem isUpperSet_exists_cluster_infinite :
    IsUpperSet {ω : Config V | ∃ x, (cluster ω x).Infinite} := fun _ _ hle ⟨x, hx⟩ =>
  ⟨x, isUpperSet_cluster_infinite x hle hx⟩

theorem measurableSet_setOf_exists_cluster_infinite [Countable V] :
    MeasurableSet {ω : Config V | ∃ x, (cluster ω x).Infinite} := by
  have : {ω : Config V | ∃ x, (cluster ω x).Infinite} =
      ⋃ x, {ω : Config V | (cluster ω x).Infinite} := by
    ext ω
    simp
  rw [this]
  exact MeasurableSet.iUnion fun x => measurableSet_cluster_infinite x

/-- Below the root threshold the cluster of the root is almost surely finite. -/
theorem law_cluster_infinite_eq_zero_of_lt_rootCriticalIntensity (J : Sym2 V → ℝ≥0) (x : V)
    {β : ℝ≥0} (h : (β : ℝ≥0∞) < rootCriticalIntensity J x) :
    law (intensityProfile J β) {ω | (cluster ω x).Infinite} = 0 := by
  by_contra hne
  exact not_le.2 h (sInf_le ⟨β, rfl, pos_iff_ne_zero.2 hne⟩)

/-- Above the root threshold the cluster of the root is infinite with positive
probability. -/
theorem law_cluster_infinite_pos_of_rootCriticalIntensity_lt [Countable V]
    (J : Sym2 V → ℝ≥0) (x : V) {β : ℝ≥0} (h : rootCriticalIntensity J x < β) :
    0 < law (intensityProfile J β) {ω | (cluster ω x).Infinite} := by
  obtain ⟨b, ⟨β', rfl, hpos⟩, hlt⟩ := sInf_lt_iff.1 h
  exact hpos.trans_le (law_intensityProfile_mono (isUpperSet_cluster_infinite x)
    (measurableSet_cluster_infinite x) J (ENNReal.coe_le_coe.1 hlt.le))

/-- Below the global threshold there is almost surely no infinite cluster. -/
theorem law_exists_cluster_infinite_eq_zero_of_lt_globalCriticalIntensity
    (J : Sym2 V → ℝ≥0) {β : ℝ≥0} (h : (β : ℝ≥0∞) < globalCriticalIntensity J) :
    law (intensityProfile J β) {ω | ∃ x, (cluster ω x).Infinite} = 0 := by
  by_contra hne
  exact not_le.2 h (sInf_le ⟨β, rfl, pos_iff_ne_zero.2 hne⟩)

/-- Above the global threshold some cluster is infinite with positive probability. -/
theorem law_exists_cluster_infinite_pos_of_globalCriticalIntensity_lt [Countable V]
    (J : Sym2 V → ℝ≥0) {β : ℝ≥0} (h : globalCriticalIntensity J < β) :
    0 < law (intensityProfile J β) {ω | ∃ x, (cluster ω x).Infinite} := by
  obtain ⟨b, ⟨β', rfl, hpos⟩, hlt⟩ := sInf_lt_iff.1 h
  exact hpos.trans_le (law_intensityProfile_mono isUpperSet_exists_cluster_infinite
    measurableSet_setOf_exists_cluster_infinite J (ENNReal.coe_le_coe.1 hlt.le))

/-! ### Non-vacuity -/

/-- Additivity at `β₁ = 0` is the identity. -/
example (J : Sym2 V → ℝ≥0) (β : ℝ≥0) (e : Sym2 V) :
    intensityProfile J (0 + β) e =
      σ (σ (intensityProfile J 0 e) * σ (intensityProfile J β e)) :=
  intensityProfile_add J 0 β e

/-- On a finite vertex set no cluster is infinite, so the root threshold is `⊤` and the
hypothesis of `law_cluster_infinite_eq_zero_of_lt_rootCriticalIntensity` holds for every
finite `β`. -/
example (J : Sym2 Bool → ℝ≥0) (β : ℝ≥0) : (β : ℝ≥0∞) < rootCriticalIntensity J false := by
  have hempty : {b : ℝ≥0∞ | ∃ β' : ℝ≥0, (β' : ℝ≥0∞) = b ∧
      0 < law (intensityProfile J β') {ω | (cluster ω false).Infinite}} = ∅ := by
    ext b
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_exists, not_and]
    intro β' _
    have : {ω : Config Bool | (cluster ω false).Infinite} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, Set.not_infinite]
      exact Set.toFinite _
    rw [this, measure_empty]
    exact lt_irrefl 0
  rw [rootCriticalIntensity, hempty, sInf_empty]
  exact ENNReal.coe_lt_top

/-- On the complete graph on `ℕ` with unit intensities, the cluster of `0` is infinite with
positive probability at `β = 1/2` (by the second Borel–Cantelli lemma along the pairs
`s(0, n+1)`), so the hypothesis `rootCriticalIntensity J 0 < β` of
`law_cluster_infinite_pos_of_rootCriticalIntensity_lt` holds at `β = 1`. -/
example : rootCriticalIntensity (fun _ : Sym2 ℕ => (1 : ℝ≥0)) 0 < ((1 : ℝ≥0) : ℝ≥0∞) := by
  set J : Sym2 ℕ → ℝ≥0 := fun _ => 1
  set E : ℕ → Set (Config ℕ) := fun n => {ω | s(0, n + 1) ∈ ω}
  have hg : Function.Injective fun n : ℕ => s(0, n + 1) := by
    intro m n h
    simp only [Sym2.eq_iff] at h
    omega
  have hind : iIndepSet E (law (intensityProfile J (1 / 2))) :=
    (prodBernoulli_iIndepSet_mem _).precomp hg
  have hc : law (intensityProfile J (1 / 2)) (E 0) ≠ 0 := by
    simp only [E, law, prodBernoulli_setOf_mem, ne_eq, ENNReal.coe_eq_zero]
    intro h0
    have h1 := congrArg (fun x : ℝ≥0 => (x : ℝ)) h0
    simp only [unitInterval.toNNReal, NNReal.coe_zero, intensityProfile] at h1
    change (1 - Real.exp (-((1 / 2 : ℝ≥0) : ℝ) * ((1 : ℝ≥0) : ℝ)) : ℝ) = 0 at h1
    have : Real.exp (-((1 / 2 : ℝ≥0) : ℝ) * ((1 : ℝ≥0) : ℝ)) < 1 :=
      Real.exp_lt_one_iff.2 (by norm_num)
    linarith
  have hconst : ∀ n, law (intensityProfile J (1 / 2)) (E n) =
      law (intensityProfile J (1 / 2)) (E 0) := by
    intro n
    simp only [E, law, prodBernoulli_setOf_mem]
    rfl
  have hBC := measure_limsup_eq_one (fun n => measurableSet_mem _) hind
    (by rw [tsum_congr hconst]; exact ENNReal.tsum_const_eq_top_of_ne_zero hc)
  have hsub : Filter.limsup E Filter.atTop ⊆ {ω | (cluster ω 0).Infinite} := by
    intro ω hω
    rw [Filter.mem_limsup_iff_frequently_mem, Nat.frequently_atTop_iff_infinite] at hω
    refine ((hω.image (Nat.succ_injective.injOn)).mono ?_)
    rintro _ ⟨n, hn, rfl⟩
    exact mem_conn_of_mem (Nat.succ_ne_zero n).symm hn
  have hpos : 0 < law (intensityProfile J (1 / 2)) {ω | (cluster ω 0).Infinite} := by
    calc (0 : ℝ≥0∞) < 1 := zero_lt_one
      _ = _ := hBC.symm
      _ ≤ _ := measure_mono hsub
  refine lt_of_le_of_lt (sInf_le ⟨1 / 2, rfl, hpos⟩) ?_
  rw [ENNReal.coe_lt_coe]
  norm_num

end PercLib.Percolation.Bond

end
