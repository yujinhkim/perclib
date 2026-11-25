/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Compatibility lemmas for the countable independent-edge cluster API.
-/
module

public import PercLib.CriticalLRP.CountableProduct.Lattice

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal

namespace PercLib.CriticalLRP

section CountableAPI

variable {V : Type*} [Countable V]

/-- The `Set.encard` characterization of an infinite cluster, matching the old API. -/
theorem clusterVol_eq_top_iff (ω : Config V) (v : V) :
    clusterVol ω v = ⊤ ↔ (cluster ω v).Infinite :=
  inInfiniteCluster_iff_infinite ω v

/-- Compatibility name of the infinite-cluster condition. -/
theorem inInfiniteCluster_iff (ω : Config V) (v : V) :
    InInfiniteCluster ω v ↔ (cluster ω v).Infinite :=
  inInfiniteCluster_iff_infinite ω v

theorem edgeMeasure_cylinder_closed (π : Sym2 V → unitInterval) (s : Finset (Sym2 V)) :
    edgeMeasure π {ω : Config V | ∀ e ∈ s, e ∉ ω} =
      ∏ e ∈ s, (toNNReal (σ (π e)) : ℝ≥0∞) := by
  have key : Measure.infinitePi (X := fun _ : Sym2 V => Prop)
        (fun e => bernoulliMeasure (True : Prop) (False : Prop) (π e))
        (Set.pi (s : Set (Sym2 V)) (fun _ => ({q : Prop | ¬q} : Set Prop))) =
      ∏ e ∈ s, (toNNReal (σ (π e)) : ℝ≥0∞) := by
    rw [Measure.infinitePi_pi _ (fun _ _ => by measurability)]
    refine Finset.prod_congr rfl fun e _ => ?_
    simp [bernoulliMeasure_def]
  have hset : ({ω : Config V | ∀ e ∈ s, e ∉ ω} : Set (Config V))
      = Set.pi (s : Set (Sym2 V)) (fun _ => ({q : Prop | ¬q} : Set Prop)) := rfl
  rw [hset, edgeMeasure_eq_infinitePi π]
  exact key



theorem edgeMeasure_zero : edgeMeasure (fun _ => (0 : unitInterval)) = dirac (∅ : Config V) := by
  rw [edgeMeasure, PercLib.Percolation.Bond.law]
  simpa using
    PercLib.Probability.prodBernoulli_deterministic (∅ : Set (Sym2 V))


theorem clusterVol_mono {ω ω' : Config V} (h : ∀ e, e ∈ ω → e ∈ ω') (v : V) :
    clusterVol ω v ≤ clusterVol ω' v := by
  classical
  rw [clusterVol_eq_tsum ω v, clusterVol_eq_tsum ω' v]
  refine ENNReal.tsum_le_tsum fun w => ?_
  rw [Set.indicator_apply, Set.indicator_apply]
  by_cases hw : w ∈ cluster ω v
  · have hw' : w ∈ cluster ω' v := cluster_mono h v hw
    simp [hw, hw']
  · simp [hw]


/-- `|K_v ∩ W|`, the truncated cluster volume that the paper writes `|K ∩ W|`
(used for `M_β(W)` in §I.2.1 and in Theorem I.2.3 / Corollary I.2.5). -/
noncomputable def clusterVolIn (ω : Config V) (v : V) (W : Set V) : ℝ≥0∞ :=
  (((cluster ω v) ∩ W).encard : ℕ∞)

theorem clusterVolIn_eq_tsum (ω : Config V) (v : V) (W : Set V) :
    clusterVolIn ω v W = ∑' w : V, ((cluster ω v) ∩ W).indicator (fun _ => (1 : ℝ≥0∞)) w := by
  rw [clusterVolIn, tsum_indicator_eq_encard]

theorem clusterVolIn_eq_top_iff (ω : Config V) (v : V) (W : Set V) :
    clusterVolIn ω v W = ⊤ ↔ ((cluster ω v) ∩ W).Infinite := by
  rw [clusterVolIn]
  simp

theorem clusterVolIn_univ (ω : Config V) (v : V) :
    clusterVolIn ω v Set.univ = clusterVol ω v := by
  simp only [clusterVolIn, Set.inter_univ]



theorem clusterVol_pos (ω : Config V) (v : V) : 0 < clusterVol ω v := by
  have h : 0 < (cluster ω v).encard := Set.encard_pos.mpr ⟨v, cluster_mem_self ω v⟩
  rw [clusterVol_eq_encard]
  exact_mod_cast h

theorem measurable_clusterVolIn (v : V) (W : Set V) :
    Measurable fun ω : Config V => clusterVolIn ω v W := by
  have h : (fun ω : Config V => clusterVolIn ω v W) =
      fun ω => ∑' w : V, ((cluster ω v) ∩ W).indicator (fun _ => (1 : ℝ≥0∞)) w := by
    funext ω; exact clusterVolIn_eq_tsum ω v W
  rw [h]
  refine Measurable.tsum fun w => ?_
  by_cases hw : w ∈ W
  · have h1 : (fun ω : Config V => ((cluster ω v) ∩ W).indicator (fun _ => (1 : ℝ≥0∞)) w)
        = fun ω => (cluster ω v).indicator (fun _ => (1 : ℝ≥0∞)) w := by
      funext ω
      by_cases hwv : w ∈ cluster ω v
      · rw [Set.indicator_of_mem (Set.mem_inter hwv hw), Set.indicator_of_mem hwv]
      · rw [Set.indicator_of_notMem (fun hh => hwv (Set.mem_of_mem_inter_left hh)),
          Set.indicator_of_notMem hwv]
    rw [h1]
    exact Measurable.indicator measurable_const (measurableSet_cluster_mem v w)
  · have h0 : (fun ω : Config V => ((cluster ω v) ∩ W).indicator (fun _ => (1 : ℝ≥0∞)) w)
        = fun _ => (0 : ℝ≥0∞) := by
      funext ω
      exact Set.indicator_of_notMem (fun hh => hw (Set.mem_of_mem_inter_right hh)) _
    rw [h0]
    exact measurable_const





end CountableAPI

end PercLib.CriticalLRP
