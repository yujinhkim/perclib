/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
New proofs using the existing quantile and pinned mathlib order/topology APIs.
Source motivation: arXiv:2103.17013v1, section 2.1. The assertion of continuity is
replaced by left stability, following FIXER's provisional resolution of issue 53.
No source code is copied; no two-sided continuity of the integer quantile is claimed.
-/
module

public import PercLib.Percolation.Bond.Tightness.Defs
public import PercLib.Percolation.Bond.Intensity
public import PercLib.Probability.FiniteContinuity
public import PercLib.Probability.Coupling.Monotone
public import PercLib.Probability.OpenEventHarris

@[expose] public section
noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Classical

namespace PercLib.Percolation.Bond

variable {V : Type*}

private theorem maximum_le_card (Λ : Finset V) (ω : Config V) :
    maxClusterIntersection Λ ω ≤ Λ.card := by
  apply Finset.sup_le
  intro v _
  simpa using Set.ncard_le_ncard (Set.inter_subset_right :
    cluster ω v ∩ (Λ : Set V) ⊆ (Λ : Set V)) Λ.finite_toSet

private theorem quantile_set_nonempty (q : Sym2 V → unitInterval) (Λ : Finset V) :
    {n : ℕ | law q {ω | n ≤ maxClusterIntersection Λ ω} ≤
      ENNReal.ofReal (Real.exp (-1))}.Nonempty := by
  refine ⟨Λ.card + 1, ?_⟩
  have h : {ω : Config V | Λ.card + 1 ≤ maxClusterIntersection Λ ω} = ∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    have := maximum_le_card Λ ω
    omega
  simp only [Set.mem_ofPred_eq, h, measure_empty]
  exact bot_le

/-- The quantile is attained; no finiteness assumption on the ambient vertex type. -/
theorem law_max_tail_at_tightnessScale (q : Sym2 V → unitInterval) (Λ : Finset V) :
    law q {ω | tightnessScale q Λ ≤ maxClusterIntersection Λ ω} ≤
      ENNReal.ofReal (Real.exp (-1)) :=
  Nat.sInf_mem (quantile_set_nonempty q Λ)

/-- Every integer strictly below the quantile has tail probability strictly above the cutoff. -/
theorem lt_law_max_tail_of_lt_tightnessScale (q : Sym2 V → unitInterval)
    (Λ : Finset V) {n : ℕ} (hn : n < tightnessScale q Λ) :
    ENNReal.ofReal (Real.exp (-1)) < law q {ω | n ≤ maxClusterIntersection Λ ω} := by
  apply lt_of_not_ge
  intro h
  exact (not_le_of_gt hn) (Nat.sInf_le h)

/-- Tail probabilities at or above the quantile satisfy the cutoff. -/
theorem law_max_tail_le_of_tightnessScale_le (q : Sym2 V → unitInterval)
    (Λ : Finset V) {n : ℕ} (hn : tightnessScale q Λ ≤ n) :
    law q {ω | n ≤ maxClusterIntersection Λ ω} ≤
      ENNReal.ofReal (Real.exp (-1)) :=
  (measure_mono fun _ h => hn.trans h).trans (law_max_tail_at_tightnessScale q Λ)

/-- A useful characterization that retains the non-strict tail convention. -/
theorem tightnessScale_le_iff (q : Sym2 V → unitInterval) (Λ : Finset V) (n : ℕ) :
    tightnessScale q Λ ≤ n ↔ law q {ω | n ≤ maxClusterIntersection Λ ω} ≤
      ENNReal.ofReal (Real.exp (-1)) :=
  ⟨law_max_tail_le_of_tightnessScale_le q Λ, fun h => Nat.sInf_le h⟩

/-- A uniform finite bound, including an empty observation set. -/
theorem tightnessScale_le_card_add_one (q : Sym2 V → unitInterval) (Λ : Finset V) :
    tightnessScale q Λ ≤ Λ.card + 1 := by
  rw [tightnessScale_le_iff]
  have h : {ω : Config V | Λ.card + 1 ≤ maxClusterIntersection Λ ω} = ∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    have := maximum_le_card Λ ω
    omega
  rw [h, measure_empty]
  exact bot_le

/-- The empty observation set has quantile one, rather than zero. -/
theorem tightnessScale_empty (q : Sym2 V → unitInterval) :
    tightnessScale q ∅ = 1 := by
  have he : ENNReal.ofReal (Real.exp (-1)) < 1 :=
    ENNReal.ofReal_lt_one.2 (by simp)
  apply le_antisymm
  · rw [tightnessScale_le_iff]
    simp [maxClusterIntersection]
  · by_contra h
    have hzero : tightnessScale q ∅ = 0 := by omega
    have ht := law_max_tail_at_tightnessScale q ∅
    simp only [hzero, Nat.zero_le, Set.ofPred_true, measure_univ] at ht
    exact (not_le_of_gt he) ht

private theorem maximum_mono (Λ : Finset V) {ω ω' : Config V} (h : ω ⊆ ω') :
    maxClusterIntersection Λ ω ≤ maxClusterIntersection Λ ω' := by
  apply Finset.sup_le
  intro v hv
  exact (Set.ncard_le_ncard (Set.inter_subset_inter_left _ (cluster_mono h v))
    (Λ.finite_toSet.subset Set.inter_subset_right)).trans (Finset.le_sup (f := fun v => (cluster ω' v ∩ (Λ : Set V)).ncard) hv)

/-- On finite vertex types the quantile is monotone in every bond probability. -/
theorem tightnessScale_mono_finite [Finite V] (Λ : Finset V)
    {p q : Sym2 V → unitInterval} (hpq : p ≤ q) :
    tightnessScale p Λ ≤ tightnessScale q Λ := by
  rw [tightnessScale_le_iff]
  apply le_trans _ (law_max_tail_at_tightnessScale q Λ)
  exact PercLib.Probability.prodBernoulli_mono_event p q hpq
    (Set.toFinite _).measurableSet (fun _ _ h hn => hn.trans (maximum_mono Λ h))

/-- Finite-profile continuity gives stability at a profile when approached from below
in the pointwise order. This also covers the empty observation set. -/
theorem eventually_tightnessScale_eq_of_profile_le [Finite V]
    {α : Type*} [TopologicalSpace α] (p : α → Sym2 V → unitInterval)
    {b : α} (hp : ContinuousAt p b) (Λ : Finset V) :
    ∀ᶠ a in 𝓝 b, p a ≤ p b → tightnessScale (p a) Λ = tightnessScale (p b) Λ := by
  let m := tightnessScale (p b) Λ
  by_cases hm : m = 0
  · exact Filter.Eventually.of_forall fun a ha => by
      have hle := tightnessScale_mono_finite Λ ha
      change tightnessScale (p a) Λ ≤ m at hle
      change tightnessScale (p a) Λ = m
      omega
  · have hstrict := lt_law_max_tail_of_lt_tightnessScale (p b) Λ
        (show m - 1 < tightnessScale (p b) Λ by change m - 1 < m; omega)
    have hc : ContinuousAt (fun a => law (p a) {ω | m - 1 ≤ maxClusterIntersection Λ ω}) b :=
      (PercLib.Probability.continuous_prodBernoulli_finite_apply _).continuousAt.comp hp
    filter_upwards [hc.eventually_const_lt hstrict] with a ha hpa
    apply le_antisymm (tightnessScale_mono_finite Λ hpa)
    have hnot : ¬ tightnessScale (p a) Λ ≤ m - 1 := by
      intro hle
      exact (not_le_of_gt ha) (law_max_tail_le_of_tightnessScale_le (p a) Λ hle)
    change m ≤ tightnessScale (p a) Λ
    omega

/-- Along the canonical intensity family, the finite quantile is constant sufficiently
close on the left. The stronger closed-left neighborhood includes the endpoint. -/
theorem finite_quantile_left_stable [Finite V] (J : Sym2 V → ℝ≥0)
    (Λ : Finset V) (b : ℝ≥0) :
    ∀ᶠ a in 𝓝[Set.Iic b] b,
      tightnessScale (intensityProfile J a) Λ = tightnessScale (intensityProfile J b) Λ := by
  have hp : Continuous (fun a : ℝ≥0 => intensityProfile J a) := by
    unfold intensityProfile
    fun_prop
  have hs := eventually_tightnessScale_eq_of_profile_le (fun a => intensityProfile J a)
    (b := b) hp.continuousAt Λ
  filter_upwards [hs.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with a ha hab
  exact ha (intensityProfile_mono J hab)

/-- The punctured left limit used to pass a subcritical bound to its endpoint. -/
theorem finite_quantile_left_limit [Finite V] (J : Sym2 V → ℝ≥0)
    (Λ : Finset V) (b : ℝ≥0) :
    Tendsto (fun a => tightnessScale (intensityProfile J a) Λ)
      (𝓝[Set.Iio b] b) (𝓝 (tightnessScale (intensityProfile J b) Λ)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [(finite_quantile_left_stable J Λ b).filter_mono
    (nhdsWithin_mono b Set.Iio_subset_Iic_self)] with a ha
  exact ha.symm

/-- A subcritical squared-quantile estimate passes to a positive finite endpoint with
the full endpoint quantile. There is no loss of one in that quantile. -/
theorem finite_quantile_sq_bound_at_endpoint [Finite V] (J : Sym2 V → ℝ≥0)
    (Λ : Finset V) {b : ℝ≥0} (hb : 0 < b) {C : ℝ}
    (hC : ∀ a : ℝ≥0, 0 < a → a < b →
      (a : ℝ) * (tightnessScale (intensityProfile J a) Λ : ℝ) ^ 2 ≤ C) :
    (b : ℝ) * (tightnessScale (intensityProfile J b) Λ : ℝ) ^ 2 ≤ C := by
  have : (𝓝[Set.Iio b] b).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hb⟩
  have hc : Continuous (fun a : ℝ≥0 =>
      (a : ℝ) * (tightnessScale (intensityProfile J b) Λ : ℝ) ^ 2) := by fun_prop
  apply le_of_tendsto (x := 𝓝[Set.Iio b] b) ((hc.tendsto b).mono_left nhdsWithin_le_nhds)
  have hs := (finite_quantile_left_stable J Λ b).filter_mono
    (nhdsWithin_mono b Set.Iio_subset_Iic_self)
  have hpos : ∀ᶠ a : ℝ≥0 in 𝓝[Set.Iio b] b, 0 < a :=
    (eventually_gt_nhds hb).filter_mono nhdsWithin_le_nhds
  filter_upwards [hs, hpos, self_mem_nhdsWithin] with a ha hapos hab
  simpa only [ha] using hC a hapos hab

-- Positive finite intensity, a nonzero kernel and a genuine two-vertex observation set.
example : ∀ᶠ a in 𝓝[Set.Iic (1 : ℝ≥0)] 1,
    tightnessScale (intensityProfile (fun _ : Sym2 Bool => 1) a) Finset.univ =
      tightnessScale (intensityProfile (fun _ : Sym2 Bool => 1) 1) Finset.univ :=
  finite_quantile_left_stable _ _ _

example (J : Sym2 Empty → ℝ≥0) (b : ℝ≥0) :
    tightnessScale (intensityProfile J b) ∅ = 1 := tightnessScale_empty _

example (J : Sym2 Unit → ℝ≥0) (b : ℝ≥0) :
    tightnessScale (intensityProfile J b) {()} = 2 := tightnessScale_singleton _ _

-- The endpoint lemma's assumptions hold for a nonzero two-vertex model.
example : (tightnessScale (intensityProfile (fun _ : Sym2 Bool => 1) 1)
    Finset.univ : ℝ) ^ 2 ≤ 9 := by
  have h := finite_quantile_sq_bound_at_endpoint (fun _ : Sym2 Bool => 1) Finset.univ
    (b := 1) (by norm_num) (C := 9) (by
      intro a _ ha
      have hm := tightnessScale_le_card_add_one
        (intensityProfile (fun _ : Sym2 Bool => 1) a) Finset.univ
      have hm' : (tightnessScale (intensityProfile (fun _ : Sym2 Bool => 1) a)
          Finset.univ : ℝ) ≤ 3 := by exact_mod_cast hm
      have hm0 : (0 : ℝ) ≤ tightnessScale (intensityProfile (fun _ : Sym2 Bool => 1) a)
          Finset.univ := Nat.cast_nonneg _
      have ha' : (a : ℝ) < 1 := ha
      nlinarith [sq_nonneg (tightnessScale (intensityProfile (fun _ : Sym2 Bool => 1) a)
        Finset.univ : ℝ)])
  simpa using h

end PercLib.Percolation.Bond
