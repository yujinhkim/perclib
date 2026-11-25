/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Harris--FKG at the level of infinite clusters

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.2.1 (p. 21), second and third inequalities: the proof uses
Harris--FKG to compare `E_β[F(K_x) G(K_y)]` with `E_β F(K_x) E_β G(K_y)`.  The applications
include `F = G = 1{|K| = ∞}`, whose event is *not* finitely witnessed; it is the decreasing
intersection of the level sets `{|K| ≥ n}`, so FKG passes to the limit there.

No `sorry`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.CountableProduct.ClusterInfinite

set_option autoImplicit true

set_option linter.unusedSectionVars false

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval Filter
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- The intersection of two finitely witnessed increasing events is finitely witnessed. -/
theorem finiteWitness_inter {E : Type*} [Countable E] (A B : Set (Set E))
    (hA : IsUpperSet A) (hB : IsUpperSet B)
    (hfA : Percolation.FiniteWitness A) (hfB : Percolation.FiniteWitness B) :
    Percolation.FiniteWitness (A ∩ B) := by
  intro ω hω
  obtain ⟨s, hs, hsa⟩ := hfA ω hω.1
  obtain ⟨t, ht, htb⟩ := hfB ω hω.2
  refine ⟨s ∪ t, ?_, ?_⟩
  · simpa only [Finset.coe_union] using Set.union_subset hs ht
  · refine ⟨hA ?_ hsa, hB ?_ htb⟩
    · simp
    · simp

/-- **Harris--FKG for infinite clusters.** `P(|K_x| = ∞, |K_y| = ∞) ≥ P(|K_x| = ∞) P(|K_y| = ∞)`.
Both events are decreasing intersections of the finitely witnessed increasing level sets
`{|K_x| ≥ n}`, so FKG passes to the limit.  This is the form of FKG used in the proof of
Lemma I.2.1(ii). -/
theorem edgeMeasure_fkg_infinite (π : Sym2 V → unitInterval) (x y : V) :
    (edgeMeasure π).real {ω : Config V | (cluster ω x).Infinite} *
        (edgeMeasure π).real {ω : Config V | (cluster ω y).Infinite} ≤
      (edgeMeasure π).real ({ω : Config V | (cluster ω x).Infinite} ∩
        {ω : Config V | (cluster ω y).Infinite}) := by
  have hanti : Antitone fun n => clusterCardLarge x n ∩ clusterCardLarge y n :=
    fun m n hmn => Set.inter_subset_inter (clusterCardLarge_antitone x hmn)
      (clusterCardLarge_antitone y hmn)
  have hmeas : ∀ n, MeasurableSet (clusterCardLarge x n ∩ clusterCardLarge y n) := fun n =>
    (measurableSet_clusterCardLarge x n).inter (measurableSet_clusterCardLarge y n)
  have hInter : (⋂ n, clusterCardLarge x n ∩ clusterCardLarge y n) =
      {ω : Config V | (cluster ω x).Infinite} ∩ {ω : Config V | (cluster ω y).Infinite} := by
    rw [Set.iInter_inter_distrib, clusterInfinite_eq_iInter x, clusterInfinite_eq_iInter y]
  have hlimA : Tendsto (fun n => (edgeMeasure π).real (clusterCardLarge x n)) atTop
      (𝓝 ((edgeMeasure π).real {ω : Config V | (cluster ω x).Infinite})) := by
    have h := tendsto_measure_iInter_atTop (μ := edgeMeasure π)
      (fun n => (measurableSet_clusterCardLarge x n).nullMeasurableSet)
      (clusterCardLarge_antitone x) ⟨0, measure_ne_top _ _⟩
    rw [← clusterInfinite_eq_iInter x] at h
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
  have hlimB : Tendsto (fun n => (edgeMeasure π).real (clusterCardLarge y n)) atTop
      (𝓝 ((edgeMeasure π).real {ω : Config V | (cluster ω y).Infinite})) := by
    have h := tendsto_measure_iInter_atTop (μ := edgeMeasure π)
      (fun n => (measurableSet_clusterCardLarge y n).nullMeasurableSet)
      (clusterCardLarge_antitone y) ⟨0, measure_ne_top _ _⟩
    rw [← clusterInfinite_eq_iInter y] at h
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
  have hlimAB : Tendsto (fun n => (edgeMeasure π).real (clusterCardLarge x n ∩
      clusterCardLarge y n)) atTop
      (𝓝 ((edgeMeasure π).real ({ω : Config V | (cluster ω x).Infinite} ∩
        {ω : Config V | (cluster ω y).Infinite}))) := by
    have h := tendsto_measure_iInter_atTop (μ := edgeMeasure π)
      (fun n => (hmeas n).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
    rw [hInter] at h
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
  refine le_of_tendsto_of_tendsto (hlimA.mul hlimB) hlimAB (Eventually.of_forall fun n => ?_)
  exact edgeMeasure_fkg π (clusterCardLarge x n) (clusterCardLarge y n)
    (clusterCardLarge_upper x n) (clusterCardLarge_upper y n)
    (finiteWitness_clusterCardLarge x n) (finiteWitness_clusterCardLarge y n)

/-- Harris--FKG for infinite clusters, for the paper's law `P_β`. -/
theorem longRangeMeasure_fkg_infinite {J : Sym2 V → ℝ} (hJ : ∀ e, 0 ≤ J e) (β : NNReal)
    (x y : V) :
    (longRangeMeasure J hJ β).real {ω : Config V | (cluster ω x).Infinite} *
        (longRangeMeasure J hJ β).real {ω : Config V | (cluster ω y).Infinite} ≤
      (longRangeMeasure J hJ β).real ({ω : Config V | (cluster ω x).Infinite} ∩
        {ω : Config V | (cluster ω y).Infinite}) :=
  edgeMeasure_fkg_infinite _ x y

end PercLib.CriticalLRP
