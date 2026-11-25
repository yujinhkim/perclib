/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Cluster-volume level sets inside a finite window

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, §I.4.1 and (I.4.16)/(I.4.17): the quantities bounded there are moments of
`|K_x ∩ B_r|`, i.e. the number of vertices of the ball `B_r` that lie in the cluster of `x`.
The corresponding level events

  `{|K_x ∩ W| ≥ n} = {ω | there are n distinct vertices of the finite window W connected to x}`

are increasing and finitely witnessed, so Lemma I.2.1(i) applies to them; their intersection over
`n` is `{|K_x ∩ W| = ∞}`.

No `sorry`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.CountableProduct.ClusterFKG

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

set_option linter.unusedSectionVars false

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval Filter
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- **`{|K_x ∩ W| ≥ n}`**: at least `n` vertices of the finite window `W` are connected to `x`. -/
def clusterWindowLarge (W : Finset V) (x : V) (n : ℕ) : Set (Config V) :=
  {ω | ∃ t : Finset V, t ⊆ W ∧ n ≤ t.card ∧ ∀ y ∈ t, Connects ω x y}

theorem clusterWindowLarge_upper (W : Finset V) (x : V) (n : ℕ) :
    IsUpperSet (clusterWindowLarge W x n) := by
  rintro ω ω' h ⟨t, htW, htn, hc⟩
  exact ⟨t, htW, htn, fun y hy => connects_mono (fun e he => h he) (hc y hy)⟩

theorem finiteWitness_clusterWindowLarge (W : Finset V) (x : V) (n : ℕ) :
    Percolation.FiniteWitness (clusterWindowLarge W x n) := by
  rintro ω ⟨t, htW, htn, hc⟩
  obtain ⟨s, hs, hsc⟩ := Percolation.finiteWitness_conn_finset (idBondGraph V) x t ω
    (fun y hy => (conn_idBondGraph_iff ω x y).mpr (hc y hy))
  exact ⟨s, hs, t, htW, htn,
    fun y hy => (conn_idBondGraph_iff (s : Set (Sym2 V)) x y).mp (hsc y hy)⟩

theorem measurableSet_clusterWindowLarge (W : Finset V) (x : V) (n : ℕ) :
    MeasurableSet (clusterWindowLarge W x n) :=
  Percolation.measurableSet_finiteWitness _ (clusterWindowLarge_upper W x n)
    (finiteWitness_clusterWindowLarge W x n)

theorem clusterWindowLarge_antitone (W : Finset V) (x : V) : Antitone (clusterWindowLarge W x) :=
  fun m n hmn ω ⟨t, htW, htn, hc⟩ => ⟨t, htW, le_trans hmn htn, hc⟩

/-- `{|K_x ∩ W| ≥ n}` is determined by the cluster of `x`. -/
theorem clusterEvent_clusterWindowLarge (W : Finset V) (x : V) (n : ℕ) :
    ClusterEvent x (clusterWindowLarge W x n) := by
  intro ω ω' hcl
  have hc : ∀ y, Connects ω x y ↔ Connects ω' x y := by
    intro y
    rw [← mem_cluster_iff, ← mem_cluster_iff, hcl]
  constructor
  · rintro ⟨t, htW, htn, hconn⟩
    exact ⟨t, htW, htn, fun y hy => (hc y).mp (hconn y hy)⟩
  · rintro ⟨t, htW, htn, hconn⟩
    exact ⟨t, htW, htn, fun y hy => (hc y).mpr (hconn y hy)⟩

/-- `{|K_x ∩ W| = ∞}` is the intersection of the level sets. -/
theorem clusterWindowInfinite_eq_iInter (W : Finset V) (x : V) :
    {ω : Config V | (cluster ω x ∩ (W : Set V)).Infinite} =
      ⋂ n, clusterWindowLarge W x n := by
  ext ω
  simp only [Set.mem_iInter, Set.mem_ofPred_eq, clusterWindowLarge]
  constructor
  · intro h n
    obtain ⟨t, ht, hcard⟩ := h.exists_subset_card_eq n
    have hcoe : ∀ y, y ∈ (t : Finset V) → y ∈ (t : Set V) := fun y hy => by simpa using hy
    exact ⟨t, fun y hy => (ht (hcoe y hy)).2, hcard.ge,
      fun y hy => mem_cluster_iff.mp (ht (hcoe y hy)).1⟩
  · rintro h hfin
    obtain ⟨t, htW, htn, hc⟩ := h (hfin.toFinset.card + 1)
    have hsub : t ⊆ hfin.toFinset := fun y hy => hfin.mem_toFinset.mpr
      ⟨mem_cluster_iff.mpr (hc y hy), by simpa using htW hy⟩
    have h1 : t.card ≤ hfin.toFinset.card := Finset.card_le_card hsub
    omega

/-- **Lemma I.2.1(i) inside a finite window.** -/
theorem edgeMeasure_twoCluster_window (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (W W' : Finset V) (x y : V) (n m : ℕ) :
    (edgeMeasure π).real (clusterWindowLarge W x n ∩ clusterWindowLarge W' y m ∩
        {ω | ¬ Connects ω x y}) ≤
      (edgeMeasure π).real (clusterWindowLarge W x n) *
        (edgeMeasure π).real (clusterWindowLarge W' y m) :=
  edgeMeasure_twoCluster_bk π hπ x y _ _ (clusterWindowLarge_upper W x n)
    (finiteWitness_clusterWindowLarge W x n) (clusterEvent_clusterWindowLarge W x n)
    (clusterWindowLarge_upper W' y m) (finiteWitness_clusterWindowLarge W' y m)
    (clusterEvent_clusterWindowLarge W' y m)

/-- **Lemma I.2.1(i) inside a finite window, for `P_β`.** -/
theorem longRangeMeasure_twoCluster_window {J : Sym2 V → ℝ} (hJ : ∀ e, 0 ≤ J e) (β : NNReal)
    (W W' : Finset V) (x y : V) (n m : ℕ) :
    (longRangeMeasure J hJ β).real (clusterWindowLarge W x n ∩ clusterWindowLarge W' y m ∩
        {ω | ¬ Connects ω x y}) ≤
      (longRangeMeasure J hJ β).real (clusterWindowLarge W x n) *
        (longRangeMeasure J hJ β).real (clusterWindowLarge W' y m) :=
  edgeMeasure_twoCluster_window _ (fun e => bernoulliEdgeProb_lt_one hJ β e) W W' x y n m

/-- **Lemma I.2.1(i) inside a finite window, infinite-cluster form.** -/
theorem edgeMeasure_twoCluster_windowInfinite (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (W W' : Finset V) (x y : V) :
    (edgeMeasure π).real ({ω : Config V | (cluster ω x ∩ (W : Set V)).Infinite} ∩
        {ω : Config V | (cluster ω y ∩ (W' : Set V)).Infinite} ∩ {ω | ¬ Connects ω x y}) ≤
      (edgeMeasure π).real {ω : Config V | (cluster ω x ∩ (W : Set V)).Infinite} *
        (edgeMeasure π).real {ω : Config V | (cluster ω y ∩ (W' : Set V)).Infinite} := by
  have hanti : Antitone fun n => clusterWindowLarge W x n ∩ clusterWindowLarge W' y n ∩
      {ω : Config V | ¬ Connects ω x y} := by
    intro m n hmn
    exact Set.inter_subset_inter (Set.inter_subset_inter (clusterWindowLarge_antitone W x hmn)
      (clusterWindowLarge_antitone W' y hmn)) (fun _ h => h)
  have hmeas : ∀ n, MeasurableSet (clusterWindowLarge W x n ∩ clusterWindowLarge W' y n ∩
      {ω : Config V | ¬ Connects ω x y}) := fun n =>
    ((measurableSet_clusterWindowLarge W x n).inter (measurableSet_clusterWindowLarge W' y n)).inter
      (measurableSet_connects x y).compl
  have hInter : (⋂ n, clusterWindowLarge W x n ∩ clusterWindowLarge W' y n ∩
      {ω : Config V | ¬ Connects ω x y}) =
      {ω : Config V | (cluster ω x ∩ (W : Set V)).Infinite} ∩
        {ω : Config V | (cluster ω y ∩ (W' : Set V)).Infinite} ∩
        {ω : Config V | ¬ Connects ω x y} := by
    ext ω
    constructor
    · intro h
      have h' : ∀ n : ℕ, ω ∈ clusterWindowLarge W x n ∧ ω ∈ clusterWindowLarge W' y n ∧
          ω ∈ {ω : Config V | ¬ Connects ω x y} := fun n => by
        have hn := Set.mem_iInter.1 h n
        exact ⟨hn.1.1, hn.1.2, hn.2⟩
      have hx : ω ∈ ⋂ n, clusterWindowLarge W x n := Set.mem_iInter.2 fun n => (h' n).1
      have hy : ω ∈ ⋂ n, clusterWindowLarge W' y n := Set.mem_iInter.2 fun n => (h' n).2.1
      rw [← clusterWindowInfinite_eq_iInter] at hx
      rw [← clusterWindowInfinite_eq_iInter] at hy
      exact ⟨⟨hx, hy⟩, (h' 0).2.2⟩
    · intro h
      obtain ⟨⟨hx, hy⟩, hC⟩ := h
      rw [clusterWindowInfinite_eq_iInter] at hx
      rw [clusterWindowInfinite_eq_iInter] at hy
      exact Set.mem_iInter.2 fun n =>
        ⟨⟨Set.mem_iInter.1 hx n, Set.mem_iInter.1 hy n⟩, hC⟩
  have hlimL : Tendsto (fun n => (edgeMeasure π).real (clusterWindowLarge W x n ∩
      clusterWindowLarge W' y n ∩ {ω : Config V | ¬ Connects ω x y})) atTop
      (𝓝 ((edgeMeasure π).real ({ω : Config V | (cluster ω x ∩ (W : Set V)).Infinite} ∩
        {ω : Config V | (cluster ω y ∩ (W' : Set V)).Infinite} ∩
        {ω : Config V | ¬ Connects ω x y}))) := by
    have h := tendsto_measure_iInter_atTop (μ := edgeMeasure π)
      (fun n => (hmeas n).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
    rw [hInter] at h
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
  have hlimA : Tendsto (fun n => (edgeMeasure π).real (clusterWindowLarge W x n)) atTop
      (𝓝 ((edgeMeasure π).real {ω : Config V | (cluster ω x ∩ (W : Set V)).Infinite})) := by
    have h := tendsto_measure_iInter_atTop (μ := edgeMeasure π)
      (fun n => (measurableSet_clusterWindowLarge W x n).nullMeasurableSet)
      (clusterWindowLarge_antitone W x) ⟨0, measure_ne_top _ _⟩
    rw [← clusterWindowInfinite_eq_iInter] at h
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
  have hlimB : Tendsto (fun n => (edgeMeasure π).real (clusterWindowLarge W' y n)) atTop
      (𝓝 ((edgeMeasure π).real {ω : Config V | (cluster ω y ∩ (W' : Set V)).Infinite})) := by
    have h := tendsto_measure_iInter_atTop (μ := edgeMeasure π)
      (fun n => (measurableSet_clusterWindowLarge W' y n).nullMeasurableSet)
      (clusterWindowLarge_antitone W' y) ⟨0, measure_ne_top _ _⟩
    rw [← clusterWindowInfinite_eq_iInter] at h
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h
  refine le_of_tendsto_of_tendsto hlimL (hlimA.mul hlimB) (Eventually.of_forall fun n => ?_)
  exact edgeMeasure_twoCluster_window π hπ W W' x y n n

/-- **Lemma I.2.1(i) inside a finite window, infinite form, for `P_β`.** -/
theorem longRangeMeasure_twoCluster_windowInfinite {J : Sym2 V → ℝ} (hJ : ∀ e, 0 ≤ J e)
    (β : NNReal) (W W' : Finset V) (x y : V) :
    (longRangeMeasure J hJ β).real ({ω : Config V | (cluster ω x ∩ (W : Set V)).Infinite} ∩
        {ω : Config V | (cluster ω y ∩ (W' : Set V)).Infinite} ∩ {ω | ¬ Connects ω x y}) ≤
      (longRangeMeasure J hJ β).real {ω : Config V | (cluster ω x ∩ (W : Set V)).Infinite} *
        (longRangeMeasure J hJ β).real {ω : Config V | (cluster ω y ∩ (W' : Set V)).Infinite} :=
  edgeMeasure_twoCluster_windowInfinite _ (fun e => bernoulliEdgeProb_lt_one hJ β e) W W' x y

end PercLib.CriticalLRP
