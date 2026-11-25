/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# The two-cluster inequality for infinite clusters

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.2.1 (p. 21), in the case `F = G = 1{|K| = ∞}`.

The level sets `{|K_x| ≥ n}` are increasing and finitely witnessed, so Lemma I.2.1(i) applies to
them (`edgeMeasure_twoCluster_card`).  The infinite-cluster event `{|K_x| = ∞}` is the decreasing
intersection `⋂ n {|K_x| ≥ n}`, so the same inequality passes to the limit.  This is the exact
instance of "applying BK to events depending on infinitely many edges via simple limiting
arguments" (p. 21, footnote 11) that the paper uses in practice: for `{|K_x| = ∞}` the cylinder
approximation of `bk_approx` is empty, but the *level-set* approximation works, because the level
sets are finitely witnessed.

No `sorry`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.CountableProduct.ClusterLevelSets

set_option autoImplicit true

set_option linter.unusedSectionVars false

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval Filter
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- **Lemma I.2.1(i) for infinite clusters.** `P(x ↮ y, |K_x| = ∞, |K_y| = ∞) ≤
P(|K_x| = ∞) P(|K_y| = ∞)`. -/
theorem edgeMeasure_twoCluster_infinite (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (x y : V) :
    (edgeMeasure π).real ({ω : Config V | (cluster ω x).Infinite} ∩
        {ω : Config V | (cluster ω y).Infinite} ∩ {ω | ¬ Connects ω x y}) ≤
      (edgeMeasure π).real {ω : Config V | (cluster ω x).Infinite} *
        (edgeMeasure π).real {ω : Config V | (cluster ω y).Infinite} := by
  have hanti : Antitone fun n => clusterCardLarge x n ∩ clusterCardLarge y n ∩
      {ω : Config V | ¬ Connects ω x y} := by
    intro m n hmn
    exact Set.inter_subset_inter (Set.inter_subset_inter (clusterCardLarge_antitone x hmn)
      (clusterCardLarge_antitone y hmn)) (fun _ h => h)
  have hmeas : ∀ n, MeasurableSet (clusterCardLarge x n ∩ clusterCardLarge y n ∩
      {ω : Config V | ¬ Connects ω x y}) := fun n =>
    ((measurableSet_clusterCardLarge x n).inter (measurableSet_clusterCardLarge y n)).inter
      (measurableSet_connects x y).compl
  have hInter : (⋂ n, clusterCardLarge x n ∩ clusterCardLarge y n ∩
      {ω : Config V | ¬ Connects ω x y}) =
      {ω : Config V | (cluster ω x).Infinite} ∩ {ω : Config V | (cluster ω y).Infinite} ∩
        {ω : Config V | ¬ Connects ω x y} := by
    ext ω
    constructor
    · intro h
      have h' : ∀ n : ℕ, ω ∈ clusterCardLarge x n ∧ ω ∈ clusterCardLarge y n ∧
          ω ∈ {ω : Config V | ¬ Connects ω x y} := fun n => by
        have hn := Set.mem_iInter.1 h n
        exact ⟨hn.1.1, hn.1.2, hn.2⟩
      have hx : ω ∈ ⋂ n, clusterCardLarge x n := Set.mem_iInter.2 fun n => (h' n).1
      have hy : ω ∈ ⋂ n, clusterCardLarge y n := Set.mem_iInter.2 fun n => (h' n).2.1
      rw [← clusterInfinite_eq_iInter] at hx
      rw [← clusterInfinite_eq_iInter] at hy
      exact ⟨⟨hx, hy⟩, (h' 0).2.2⟩
    · intro h
      obtain ⟨⟨hx, hy⟩, hC⟩ := h
      rw [clusterInfinite_eq_iInter] at hx
      rw [clusterInfinite_eq_iInter] at hy
      exact Set.mem_iInter.2 fun n => ⟨⟨Set.mem_iInter.1 hx n, Set.mem_iInter.1 hy n⟩, hC⟩
  have hlimL : Tendsto (fun n => (edgeMeasure π).real (clusterCardLarge x n ∩
      clusterCardLarge y n ∩ {ω : Config V | ¬ Connects ω x y})) atTop
      (𝓝 ((edgeMeasure π).real ({ω : Config V | (cluster ω x).Infinite} ∩
        {ω : Config V | (cluster ω y).Infinite} ∩ {ω : Config V | ¬ Connects ω x y}))) := by
    have h := tendsto_measure_iInter_atTop (μ := edgeMeasure π)
      (fun n => (hmeas n).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
    rw [hInter] at h
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
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
  have hbound : ∀ n, (edgeMeasure π).real (clusterCardLarge x n ∩ clusterCardLarge y n ∩
      {ω : Config V | ¬ Connects ω x y}) ≤
      (edgeMeasure π).real (clusterCardLarge x n) * (edgeMeasure π).real (clusterCardLarge y n) :=
    fun n => edgeMeasure_twoCluster_card π hπ x y n n
  exact le_of_tendsto_of_tendsto hlimL (hlimA.mul hlimB) (Eventually.of_forall hbound)

/-- Lemma I.2.1(i) for infinite clusters, for the paper's law `P_β`. -/
theorem longRangeMeasure_twoCluster_infinite {J : Sym2 V → ℝ} (hJ : ∀ e, 0 ≤ J e) (β : NNReal)
    (x y : V) :
    (longRangeMeasure J hJ β).real ({ω : Config V | (cluster ω x).Infinite} ∩
        {ω : Config V | (cluster ω y).Infinite} ∩ {ω | ¬ Connects ω x y}) ≤
      (longRangeMeasure J hJ β).real {ω : Config V | (cluster ω x).Infinite} *
        (longRangeMeasure J hJ β).real {ω : Config V | (cluster ω y).Infinite} :=
  edgeMeasure_twoCluster_infinite _ (fun e => bernoulliEdgeProb_lt_one hJ β e) x y

end PercLib.CriticalLRP
