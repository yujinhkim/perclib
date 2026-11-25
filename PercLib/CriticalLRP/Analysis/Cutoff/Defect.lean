/-
E1 sign (Lemma I.4.7), part 1: cluster volumes as sums of connection indicators.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.Defect.Defs
public import PercLib.CriticalLRP.Correlation.CovarianceGapGeneral
public import PercLib.CriticalLRP.Analysis.Polygon.ChiLower

/-! # Sign and upper bound of the defect at the actual cutoff law -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP

variable {V : Type*} [Countable V]

/-- `|K_v|` written as the sum, over `w`, of the indicator of the connection event `v ↔ w`. -/
theorem clusterVol_eq_tsum_connSet (ω : Config V) (v : V) :
    clusterVol ω v = ∑' w : V, (connSet v w).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
  rw [clusterVol_eq_tsum]
  refine tsum_congr fun w => ?_
  by_cases h : w ∈ cluster ω v
  · have hc : ω ∈ connSet v w := mem_cluster_iff.mp h
    rw [Set.indicator_of_mem h, Set.indicator_of_mem hc]
  · have hc : ω ∉ connSet v w := fun hh => h (mem_cluster_iff.mpr hh)
    rw [Set.indicator_of_notMem h, Set.indicator_of_notMem hc]

theorem measurable_indicator_connSet (v w : V) :
    Measurable ((connSet v w).indicator (fun _ => (1 : ℝ≥0∞))) :=
  measurable_const.indicator (measurableSet_connects v w)

/-- `∫⁻ |K_v| ∂ν = ∑_w ν(v ↔ w)`, unconditionally in `ℝ≥0∞`. -/
theorem lintegral_clusterVol (ν : Measure (Config V)) (v : V) :
    ∫⁻ ω, clusterVol ω v ∂ν = ∑' w : V, ν (connSet v w) := by
  have hpt : ∀ ω : Config V, clusterVol ω v
      = ∑' w : V, (connSet v w).indicator (fun _ => (1 : ℝ≥0∞)) ω :=
    fun ω => clusterVol_eq_tsum_connSet (V := V) ω v
  calc ∫⁻ ω, clusterVol ω v ∂ν
      = ∫⁻ ω, ∑' w : V, (connSet v w).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂ν :=
        lintegral_congr hpt
    _ = ∑' w : V, ∫⁻ ω, (connSet v w).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂ν := by
        rw [lintegral_tsum]
        intro w
        exact (measurable_indicator_connSet v w).aemeasurable
    _ = ∑' w : V, ν (connSet v w) :=
        tsum_congr fun w => lintegral_indicator_one (measurableSet_connects v w)

/-- `∫⁻ |K_x| |K_y| ∂ν = ∑_z ∑_w ν(x ↔ z, y ↔ w)`, unconditionally in `ℝ≥0∞`. -/
theorem lintegral_clusterVol_mul (ν : Measure (Config V)) (x y : V) :
    ∫⁻ ω, clusterVol ω x * clusterVol ω y ∂ν
      = ∑' z : V, ∑' w : V, ν (connSet x z ∩ connSet y w) := by
  -- expand only the first cluster volume, keeping the second measurable
  have hpt : ∀ ω : Config V, clusterVol ω x * clusterVol ω y
      = ∑' z : V, ((connSet x z).indicator (fun _ => (1 : ℝ≥0∞)) ω * clusterVol ω y) := by
    intro ω
    rw [clusterVol_eq_tsum_connSet]
    exact (ENNReal.tsum_mul_right).symm
  -- inner: `∫⁻ 1_{x↔z} |K_y| = ∑_w ν(x ↔ z, y ↔ w)`
  have hz : ∀ z : V, ∫⁻ ω, ((connSet x z).indicator (fun _ => (1 : ℝ≥0∞)) ω
      * clusterVol ω y) ∂ν = ∑' w : V, ν (connSet x z ∩ connSet y w) := by
    intro z
    have h1 : ∀ ω : Config V, (connSet x z).indicator (fun _ => (1 : ℝ≥0∞)) ω
        * clusterVol ω y
        = ∑' w : V, ((connSet x z).indicator (fun _ => (1 : ℝ≥0∞)) ω
            * (connSet y w).indicator (fun _ => (1 : ℝ≥0∞)) ω) := by
      intro ω
      rw [clusterVol_eq_tsum_connSet, ENNReal.tsum_mul_left]
    calc ∫⁻ ω, ((connSet x z).indicator (fun _ => (1 : ℝ≥0∞)) ω * clusterVol ω y) ∂ν
        = ∫⁻ ω, ∑' w : V, ((connSet x z).indicator (fun _ => (1 : ℝ≥0∞)) ω
            * (connSet y w).indicator (fun _ => (1 : ℝ≥0∞)) ω) ∂ν :=
          lintegral_congr h1
      _ = ∑' w : V, ∫⁻ ω, ((connSet x z).indicator (fun _ => (1 : ℝ≥0∞)) ω
            * (connSet y w).indicator (fun _ => (1 : ℝ≥0∞)) ω) ∂ν := by
          rw [lintegral_tsum]
          intro w
          exact ((measurable_indicator_connSet x z).mul
            (measurable_indicator_connSet y w)).aemeasurable
      _ = ∑' w : V, ν (connSet x z ∩ connSet y w) := by
          refine tsum_congr fun w => ?_
          have h1 : ∫⁻ ω, (connSet x z ∩ connSet y w).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂ν
              = ν (connSet x z ∩ connSet y w) :=
            lintegral_indicator_one
              ((measurableSet_connects x z).inter (measurableSet_connects y w))
          rw [← h1]
          refine lintegral_congr fun ω => ?_
          by_cases hx : ω ∈ connSet x z <;> by_cases hy : ω ∈ connSet y w <;>
            simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx, hy]
  calc ∫⁻ ω, clusterVol ω x * clusterVol ω y ∂ν
      = ∫⁻ ω, ∑' z : V, ((connSet x z).indicator (fun _ => (1 : ℝ≥0∞)) ω
          * clusterVol ω y) ∂ν := lintegral_congr hpt
    _ = ∑' z : V, ∫⁻ ω, ((connSet x z).indicator (fun _ => (1 : ℝ≥0∞)) ω
          * clusterVol ω y) ∂ν := by
        rw [lintegral_tsum]
        intro z
        exact ((measurable_indicator_connSet x z).mul (measurable_clusterVol y)).aemeasurable
    _ = ∑' z : V, ∑' w : V, ν (connSet x z ∩ connSet y w) := tsum_congr hz

/-- For a measurable `s`, `∫⁻ g ∂(ν.restrict s) = ∫⁻ g · 1_s ∂ν`. -/
theorem lintegral_restrict_eq_mul_indicator (ν : Measure (Config V)) {s : Set (Config V)}
    (hs : MeasurableSet s) (g : Config V → ℝ≥0∞) :
    ∫⁻ ω, g ω ∂(ν.restrict s)
      = ∫⁻ ω, g ω * s.indicator (fun _ => (1 : ℝ≥0∞)) ω ∂ν := by
  rw [← lintegral_indicator hs g]
  refine lintegral_congr fun ω => ?_
  by_cases h : ω ∈ s
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
    exact (mul_one _).symm
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]

/-- On the connection event, the two cluster volumes agree. -/
theorem clusterVol_eq_of_connects {ω : Config V} {x y : V} (h : Connects ω x y) :
    clusterVol ω x = clusterVol ω y := by
  rw [clusterVol_eq_encard, clusterVol_eq_encard]
  rw [cluster_eq_iff.mpr h]

end PercLib.CriticalLRP

/-! ## Part 2: the cluster-weight two-point covariance bound -/

namespace PercLib.CriticalLRP

variable {V : Type*} [Countable V]

/-- Convert a real inequality between finite `ℝ≥0∞` quantities back to `ℝ≥0∞`. -/
theorem ennreal_le_of_toReal_le {a b c d : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) (hc : c ≠ ⊤)
    (hd : d ≠ ⊤) (h : a.toReal ≤ b.toReal * c.toReal + d.toReal) : a ≤ b * c + d := by
  have hbc : b * c ≠ ⊤ := ENNReal.mul_ne_top hb hc
  have hsum : b * c + d ≠ ⊤ := ENNReal.add_ne_top.2 ⟨hbc, hd⟩
  rw [← ENNReal.toReal_le_toReal ha hsum]
  rwa [ENNReal.toReal_add hbc hd, ENNReal.toReal_mul]

/-- **Lemma I.2.1 (third display), per pair of connection events, in `ℝ≥0∞`.**

`P(x↔z, y↔w) ≤ P(x↔z) P(y↔w) + P(x↔z, y↔w, x↔y)` in the canonical product model. -/
theorem edgeMeasure_conn_le (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (x y : V)
    (z w : V) :
    (edgeMeasure π) (connSet x z ∩ connSet y w)
      ≤ (edgeMeasure π) (connSet x z) * (edgeMeasure π) (connSet y w)
        + (edgeMeasure π) (connSet x z ∩ connSet y w ∩ connSet x y) := by
  have hprob : ∀ s : Set (Config V), (edgeMeasure π) s ≤ 1 := by
    intro s
    calc (edgeMeasure π) s ≤ (edgeMeasure π) Set.univ := measure_mono (Set.subset_univ s)
      _ = 1 := measure_univ
  have hne : ∀ s : Set (Config V), (edgeMeasure π) s ≠ ⊤ := fun s =>
    ne_top_of_le_ne_top (by simp) (hprob s)
  obtain ⟨-, hup⟩ := edgeMeasure_twoCluster_upper π hπ x y (connSet x z) (connSet y w)
    (isUpper_connSet x z) (finiteWitness_connSet x z) (clusterEvent_connSet x z)
    (isUpper_connSet y w) (finiteWitness_connSet y w) (clusterEvent_connSet y w)
  refine ennreal_le_of_toReal_le (hne _) (hne _) (hne _) (hne _) ?_
  rw [Measure.real_def, Measure.real_def, Measure.real_def, Measure.real_def] at hup
  change ((edgeMeasure π) (connSet x z ∩ connSet y w)).toReal ≤
      ((edgeMeasure π) (connSet x z)).toReal * ((edgeMeasure π) (connSet y w)).toReal +
        ((edgeMeasure π) (connSet x z ∩ connSet y w ∩ {ω : Config V | Connects ω x y})).toReal
  linarith

/-- **The cluster-weight two-point covariance bound.**

`E|K_x||K_y| ≤ E|K_x| E|K_y| + E[|K_x|² 1(x↔y)]`.

This is the `F = G = |·|` case of Lemma I.2.1's third display; it is the input that makes
the defect `𝓔_{1,r}` of (I.4.5)–(I.4.7) nonnegative. -/
theorem edgeMeasure_clusterVol_pair_le (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (x y : V) :
    ∫⁻ ω, clusterVol ω x * clusterVol ω y ∂(edgeMeasure π)
      ≤ (∫⁻ ω, clusterVol ω x ∂(edgeMeasure π)) * (∫⁻ ω, clusterVol ω y ∂(edgeMeasure π))
        + ∫⁻ ω, clusterVol ω x ^ 2 * (connSet x y).indicator (fun _ => (1 : ℝ≥0∞)) ω
            ∂(edgeMeasure π) := by
  calc ∫⁻ ω, clusterVol ω x * clusterVol ω y ∂(edgeMeasure π)
      = ∑' z : V, ∑' w : V, (edgeMeasure π) (connSet x z ∩ connSet y w) :=
        lintegral_clusterVol_mul (edgeMeasure π) x y
    _ ≤ ∑' z : V, ∑' w : V, ((edgeMeasure π) (connSet x z) * (edgeMeasure π) (connSet y w)
          + (edgeMeasure π) (connSet x z ∩ connSet y w ∩ connSet x y)) :=
        ENNReal.tsum_le_tsum fun z => ENNReal.tsum_le_tsum fun w => edgeMeasure_conn_le π hπ x y z w
    _ = (∑' z : V, (edgeMeasure π) (connSet x z))
          * (∑' w : V, (edgeMeasure π) (connSet y w))
          + ∑' z : V, ∑' w : V, (edgeMeasure π) (connSet x z ∩ connSet y w ∩ connSet x y) := by
        simp_rw [ENNReal.tsum_add]
        congr 1
        simp_rw [ENNReal.tsum_mul_left]
        rw [ENNReal.tsum_mul_right]
    _ = (∫⁻ ω, clusterVol ω x ∂(edgeMeasure π)) * (∫⁻ ω, clusterVol ω y ∂(edgeMeasure π))
          + ∫⁻ ω, clusterVol ω x ^ 2 * (connSet x y).indicator (fun _ => (1 : ℝ≥0∞)) ω
              ∂(edgeMeasure π) := by
        rw [lintegral_clusterVol, lintegral_clusterVol]
        congr 1
        have hres : ∀ z w : V, (edgeMeasure π) (connSet x z ∩ connSet y w ∩ connSet x y)
            = ((edgeMeasure π).restrict (connSet x y)) (connSet x z ∩ connSet y w) := by
          intro z w
          exact (Measure.restrict_apply (μ := edgeMeasure π) (s := connSet x y)
            (t := connSet x z ∩ connSet y w)
            ((measurableSet_connects x z).inter (measurableSet_connects y w))).symm
        simp_rw [hres]
        have hkey : ∑' z : V, ∑' w : V,
            ((edgeMeasure π).restrict (connSet x y)) (connSet x z ∩ connSet y w)
            = ∫⁻ ω, clusterVol ω x * clusterVol ω y
                ∂((edgeMeasure π).restrict (connSet x y)) :=
          (lintegral_clusterVol_mul ((edgeMeasure π).restrict (connSet x y)) x y).symm
        rw [hkey]
        have hrestr : ∫⁻ ω, clusterVol ω x * clusterVol ω y
              ∂((edgeMeasure π).restrict (connSet x y))
            = ∫⁻ ω, (clusterVol ω x * clusterVol ω y)
                * (connSet x y).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂(edgeMeasure π) :=
          lintegral_restrict_eq_mul_indicator (edgeMeasure π) (measurableSet_connects x y) _
        rw [hrestr]
        refine lintegral_congr fun ω => ?_
        by_cases h : ω ∈ connSet x y
        · have hcc : clusterVol ω x = clusterVol ω y :=
            clusterVol_eq_of_connects (x := x) (y := y) h
          rw [Set.indicator_of_mem h, hcc, mul_one, mul_one, pow_two]
        · rw [Set.indicator_of_notMem h]
          simp

end PercLib.CriticalLRP

/-! ## Part 3: the defect `𝓔_{1,r}` at the source model -/
namespace PercLib.CriticalLRP
namespace E1Sign

open Orchestration

variable (M : SourceModelData)

/-- Per-vertex form of the two-point cluster-weight covariance bound at the source model. -/
theorem pair_le' (r : ℝ) (y : M.V) :
    ∫⁻ ω, clusterVol ω (0 : M.V) * clusterVol ω y ∂(M.cutLaw r)
      ≤ (∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.cutLaw r))
          * (∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.cutLaw r))
        + ∫⁻ ω, clusterVol ω (0 : M.V) ^ 2
            * (connSet (0 : M.V) y).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂(M.cutLaw r) := by
  have h := edgeMeasure_clusterVol_pair_le (M.cutProb r) (cutProb_lt_one M r) (0 : M.V) y
  rw [← cutLaw_eq M r] at h
  have htrans : ∫⁻ ω, clusterVol ω y ∂(M.cutLaw r)
      = ∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.cutLaw r) := by
    simpa only [SourceModelData.cutMassAt] using M.cutMassAt_eq_zero r y
  rw [htrans] at h
  exact h

/-- Per-vertex form of the two-point cluster-weight covariance bound, in `χ` notation. -/
theorem pair_le (r : ℝ) (y : M.V) :
    ∫⁻ ω, clusterVol ω (0 : M.V) * clusterVol ω y ∂(M.cutLaw r)
      ≤ M.cutMassAt r 0 * M.cutMassAt r 0
        + ∫⁻ ω, clusterVol ω (0 : M.V) ^ 2
            * (connSet (0 : M.V) y).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂(M.cutLaw r) := by
  simpa only [SourceModelData.cutMassAt] using pair_le' M r y

/-- The square summand identity behind (I.4.5):

`|K_0| |K_y| = |K_0|² 1(y ∈ K_0) + |K_0| 1(y ∉ K_0) |K_y|`. -/
theorem summand_split (ω : Config M.V) (y : M.V) :
    clusterVol ω (0 : M.V) * clusterVol ω y
      = clusterVol ω (0 : M.V) ^ 2
          * (cluster ω (0 : M.V)).indicator (fun _ => (1 : ℝ≥0∞)) y
        + clusterVol ω (0 : M.V)
            * (((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y
                * clusterVol ω y) := by
  by_cases h : y ∈ cluster ω (0 : M.V)
  · have hconn : Connects ω (0 : M.V) y := mem_cluster_iff.mp h
    have hcc : clusterVol ω y = clusterVol ω (0 : M.V) :=
      (clusterVol_eq_of_connects hconn).symm
    rw [Set.indicator_of_mem h, Set.indicator_of_notMem (s := (cluster ω (0 : M.V))ᶜ)
      (by simpa using h), hcc, pow_two]
    simp
  · rw [Set.indicator_of_notMem h, Set.indicator_of_mem (s := (cluster ω (0 : M.V))ᶜ)
      (by simpa using h)]
    simp

/-- **The (I.4.5) split at the model:**
`E|K| ∑_{B_r} |K_y| = E[|K|²|K∩B_r|] + E[|K|∑_{B_r} 1(y∉K)|K_y|]`,
with no `∞ - ∞`. -/
theorem pairMass_eq (r : ℝ) : pairMass M r = connMass M r + exclMass M r := by
  have hf : Measurable fun ω : Config M.V => clusterVol ω (0 : M.V) ^ 2
      * ∑ y ∈ ballF M r, (cluster ω (0 : M.V)).indicator (fun _ => (1 : ℝ≥0∞)) y :=
    ((measurable_clusterVol (0 : M.V)).pow_const 2).mul
      (Finset.measurable_sum _ fun y _ =>
        measurable_const.indicator (measurableSet_cluster_mem (0 : M.V) y))
  have hpt : ∀ ω : Config M.V, clusterVol ω (0 : M.V) * ∑ y ∈ ballF M r, clusterVol ω y
      = clusterVol ω (0 : M.V) ^ 2
          * ∑ y ∈ ballF M r, (cluster ω (0 : M.V)).indicator (fun _ => (1 : ℝ≥0∞)) y
        + clusterVol ω (0 : M.V) * ∑ y ∈ ballF M r,
            ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y := by
    intro ω
    rw [Finset.mul_sum, Finset.mul_sum (s := ballF M r) (a := clusterVol ω (0 : M.V) ^ 2),
      Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun y _ => summand_split M ω y
  rw [pairMass, connMass, exclMass]
  calc ∫⁻ ω, clusterVol ω (0 : M.V) * ∑ y ∈ ballF M r, clusterVol ω y ∂(M.cutLaw r)
      = ∫⁻ ω, (clusterVol ω (0 : M.V) ^ 2
            * ∑ y ∈ ballF M r, (cluster ω (0 : M.V)).indicator (fun _ => (1 : ℝ≥0∞)) y
          + clusterVol ω (0 : M.V) * ∑ y ∈ ballF M r,
              ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y)
          ∂(M.cutLaw r) := lintegral_congr hpt
    _ = _ := lintegral_add_left hf _


/-- The indicator of a connection event, viewed at `y` versus at `ω`. -/
theorem indicator_connSet_eq (ω : Config M.V) (y : M.V) :
    (connSet (0 : M.V) y).indicator (fun _ => (1 : ℝ≥0∞)) ω
      = (cluster ω (0 : M.V)).indicator (fun _ => (1 : ℝ≥0∞)) y := by
  by_cases h : y ∈ cluster ω (0 : M.V)
  · have hc : ω ∈ connSet (0 : M.V) y := mem_cluster_iff.mp h
    rw [Set.indicator_of_mem hc, Set.indicator_of_mem h]
  · have hc : ω ∉ connSet (0 : M.V) y := fun hh => h (mem_cluster_iff.mpr hh)
    rw [Set.indicator_of_notMem hc, Set.indicator_of_notMem h]

/-- **The ball sum of the pair bounds:** `E|K| ∑_{B_r}|K_y| ≤ |B_r| χ² + E[|K|²|K∩B_r|]`. -/
theorem pairMass_le (r : ℝ) :
    pairMass M r ≤ ((M.ball r).ncard : ℝ≥0∞) * (M.cutMassAt r 0) ^ 2 + connMass M r := by
  have hsplit : ∀ ω : Config M.V, clusterVol ω (0 : M.V) * ∑ y ∈ ballF M r, clusterVol ω y
      = ∑ y ∈ ballF M r, clusterVol ω (0 : M.V) * clusterVol ω y := fun ω =>
    Finset.mul_sum (s := ballF M r) (f := fun y => clusterVol ω y) (a := clusterVol ω (0 : M.V))
  have hsum : ∑ y ∈ ballF M r, ∫⁻ ω, clusterVol ω (0 : M.V) ^ 2
        * (connSet (0 : M.V) y).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂(M.cutLaw r)
      = ∫⁻ ω, clusterVol ω (0 : M.V) ^ 2
          * ∑ y ∈ ballF M r, (connSet (0 : M.V) y).indicator (fun _ => (1 : ℝ≥0∞)) ω
            ∂(M.cutLaw r) := by
    rw [← lintegral_finsetSum]
    · exact lintegral_congr fun ω => (Finset.mul_sum (s := ballF M r)
        (f := fun y => (connSet (0 : M.V) y).indicator (fun _ => (1 : ℝ≥0∞)) ω)
        (a := clusterVol ω (0 : M.V) ^ 2)).symm
    · intro y _
      exact (measurable_clusterVol (0 : M.V)).pow_const 2 |>.mul
        (measurable_const.indicator (measurableSet_connects (0 : M.V) y))
  rw [pairMass, connMass]
  calc ∫⁻ ω, clusterVol ω (0 : M.V) * ∑ y ∈ ballF M r, clusterVol ω y ∂(M.cutLaw r)
      = ∫⁻ ω, ∑ y ∈ ballF M r, clusterVol ω (0 : M.V) * clusterVol ω y ∂(M.cutLaw r) :=
        lintegral_congr hsplit
    _ = ∑ y ∈ ballF M r, ∫⁻ ω, clusterVol ω (0 : M.V) * clusterVol ω y ∂(M.cutLaw r) :=
        lintegral_finsetSum _ (fun y _ =>
          (measurable_clusterVol (0 : M.V)).mul (measurable_clusterVol y))
    _ ≤ ∑ y ∈ ballF M r, (M.cutMassAt r 0 * M.cutMassAt r 0
          + ∫⁻ ω, clusterVol ω (0 : M.V) ^ 2
              * (connSet (0 : M.V) y).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂(M.cutLaw r)) :=
        Finset.sum_le_sum fun y _ => pair_le M r y
    _ = ((M.ball r).ncard : ℝ≥0∞) * (M.cutMassAt r 0 * M.cutMassAt r 0)
          + ∑ y ∈ ballF M r, ∫⁻ ω, clusterVol ω (0 : M.V) ^ 2
              * (connSet (0 : M.V) y).indicator (fun _ => (1 : ℝ≥0∞)) ω ∂(M.cutLaw r) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, card_ballF M r, nsmul_eq_mul]
    _ = ((M.ball r).ncard : ℝ≥0∞) * (M.cutMassAt r 0) ^ 2
          + ∫⁻ ω, clusterVol ω (0 : M.V) ^ 2
              * ∑ y ∈ ballF M r, (cluster ω (0 : M.V)).indicator (fun _ => (1 : ℝ≥0∞)) y
                ∂(M.cutLaw r) := by
        have hpt : ∀ ω : Config M.V, clusterVol ω (0 : M.V) ^ 2
            * ∑ y ∈ ballF M r, (connSet (0 : M.V) y).indicator (fun _ => (1 : ℝ≥0∞)) ω
            = clusterVol ω (0 : M.V) ^ 2
              * ∑ y ∈ ballF M r, (cluster ω (0 : M.V)).indicator (fun _ => (1 : ℝ≥0∞)) y := by
          intro ω
          congr 1
        rw [hsum, lintegral_congr hpt, pow_two]


/-- Every cluster has at least the root. -/
theorem one_le_clusterVol (ω : Config M.V) (v : M.V) : (1 : ℝ≥0∞) ≤ clusterVol ω v := by
  rw [clusterVol_eq_tsum_connSet]
  calc (1 : ℝ≥0∞) = (connSet v v).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
        rw [Set.indicator_of_mem (show ω ∈ connSet v v from connects_refl ω v)]
    _ = ∑ w ∈ ({v} : Finset M.V), (connSet v w).indicator (fun _ => (1 : ℝ≥0∞)) ω := by simp
    _ ≤ ∑' w : M.V, (connSet v w).indicator (fun _ => (1 : ℝ≥0∞)) ω := ENNReal.sum_le_tsum {v}

theorem clusterVol_le_sq (ω : Config M.V) (v : M.V) :
    clusterVol ω v ≤ clusterVol ω v ^ 2 := by
  have h1 : (1 : ℝ≥0∞) ≤ clusterVol ω v := one_le_clusterVol M ω v
  calc clusterVol ω v = 1 * clusterVol ω v := (one_mul _).symm
    _ ≤ clusterVol ω v * clusterVol ω v := by gcongr
    _ = clusterVol ω v ^ 2 := (pow_two _).symm

/-- `χ(r)`) is bounded by the second cutoff moment. -/
theorem cutMassAt_le_cutMoment_two (r : ℝ) : M.cutMassAt r 0 ≤ M.cutMoment 2 r := by
  simp only [SourceModelData.cutMassAt, SourceModelData.cutMoment]
  exact lintegral_mono fun ω => clusterVol_le_sq M ω (0 : M.V)

/-- The connection mass is bounded by `|B_r|` times the second cutoff moment. -/
theorem connMass_le (r : ℝ) :
    connMass M r ≤ ((M.ball r).ncard : ℝ≥0∞) * M.cutMoment 2 r := by
  have hcard : ∀ ω : Config M.V,
      ∑ y ∈ ballF M r, (cluster ω (0 : M.V)).indicator (fun _ => (1 : ℝ≥0∞)) y
        ≤ ((M.ball r).ncard : ℝ≥0∞) := by
    intro ω
    calc ∑ y ∈ ballF M r, (cluster ω (0 : M.V)).indicator (fun _ => (1 : ℝ≥0∞)) y
        ≤ ∑ y ∈ ballF M r, (1 : ℝ≥0∞) := by
          refine Finset.sum_le_sum fun y _ => ?_
          by_cases h : y ∈ cluster ω (0 : M.V)
          · rw [Set.indicator_of_mem h]
          · rw [Set.indicator_of_notMem h]
            exact zero_le_one
      _ = ((M.ball r).ncard : ℝ≥0∞) := by
          rw [Finset.sum_const, card_ballF M r, nsmul_eq_mul, mul_one]
  have hle : ∀ ω : Config M.V, clusterVol ω (0 : M.V) ^ 2
        * ∑ y ∈ ballF M r, (cluster ω (0 : M.V)).indicator (fun _ => (1 : ℝ≥0∞)) y
      ≤ ((M.ball r).ncard : ℝ≥0∞) * clusterVol ω (0 : M.V) ^ 2 := by
    intro ω
    calc clusterVol ω (0 : M.V) ^ 2
          * ∑ y ∈ ballF M r, (cluster ω (0 : M.V)).indicator (fun _ => (1 : ℝ≥0∞)) y
        ≤ clusterVol ω (0 : M.V) ^ 2 * ((M.ball r).ncard : ℝ≥0∞) := by
          gcongr
          exact hcard ω
      _ = ((M.ball r).ncard : ℝ≥0∞) * clusterVol ω (0 : M.V) ^ 2 := mul_comm _ _
  rw [connMass, SourceModelData.cutMoment]
  calc ∫⁻ ω, clusterVol ω (0 : M.V) ^ 2
        * ∑ y ∈ ballF M r, (cluster ω (0 : M.V)).indicator (fun _ => (1 : ℝ≥0∞)) y
          ∂(M.cutLaw r)
      ≤ ∫⁻ ω, ((M.ball r).ncard : ℝ≥0∞) * clusterVol ω (0 : M.V) ^ 2 ∂(M.cutLaw r) :=
        lintegral_mono hle
    _ = ((M.ball r).ncard : ℝ≥0∞) * ∫⁻ ω, clusterVol ω (0 : M.V) ^ 2 ∂(M.cutLaw r) :=
        lintegral_const_mul _ ((measurable_clusterVol (0 : M.V)).pow_const 2)

theorem connMass_ne_top (r : ℝ) (h2 : M.cutMoment 2 r ≠ ⊤) : connMass M r ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simp) h2) (connMass_le M r)

/-- **The excluded expectation is dominated by `|B_r| χ(r)²`** — Lemma I.4.7's inequality
`E[|K|∑_{B_r}1(y∉K)|K_y|] ≤ |B_r|(E|K|)²` in the source's own `apartSet`-free form,
at the actual truncated law. -/
theorem exclMass_le (r : ℝ) (hT : connMass M r ≠ ⊤) :
    exclMass M r ≤ ((M.ball r).ncard : ℝ≥0∞) * (M.cutMassAt r 0) ^ 2 := by
  have h1 := pairMass_le M r
  have h2 := pairMass_eq M r
  rw [h2, add_comm (connMass M r) (exclMass M r)] at h1
  exact ENNReal.le_of_add_le_add_right hT h1

/-- **Corollary (in the paper's terms).**
`(|B_r| χ² - E[|K|∑_{B_r}1(y∉K)|K_y|])/(|B_r|χ²) ≥ 0`. -/
theorem exclRate_nonneg (r : ℝ) (h2 : M.cutMoment 2 r ≠ ⊤) :
    0 ≤ (((M.ball r).ncard : ℝ) * (M.cutMassAt r 0).toReal ^ 2 - (exclMass M r).toReal)
        / (((M.ball r).ncard : ℝ) * (M.cutMassAt r 0).toReal ^ 2) := by
  have hA : M.cutMassAt r 0 ≠ ⊤ := ne_top_of_le_ne_top h2 (cutMassAt_le_cutMoment_two M r)
  have hA2 : M.cutMassAt r 0 ^ 2 ≠ ⊤ := ENNReal.pow_ne_top hA
  have hT : connMass M r ≠ ⊤ := connMass_ne_top M r h2
  have htop : ((M.ball r).ncard : ℝ≥0∞) * (M.cutMassAt r 0) ^ 2 ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) hA2
  have hle := exclMass_le M r hT
  have hreal : (exclMass M r).toReal
      ≤ (((M.ball r).ncard : ℝ≥0∞) * (M.cutMassAt r 0) ^ 2).toReal :=
    ENNReal.toReal_mono htop hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast] at hreal
  refine div_nonneg ?_ (by positivity)
  linarith

/-- **Lemma I.4.7, sign half, at the source model — the form consumed by `ChiLower`.**

With `A = χ(r) = E_{β_c,r}|K|`, `S = E[|K|∑_{y∈B_r}|K_y|]`, `T = E[|K|²|K∩B_r|]`,
`b = |B_r|`, the source's defect `𝓔_{1,r} = (b A² - S + T)/(b A²)` of (I.4.5)–(I.4.7) is
nonnegative.  The only hypothesis is finiteness of the second cutoff moment, which makes
`A`, `S`, `T` real numbers. -/
theorem cE1_nonneg (r : ℝ) (h2 : M.cutMoment 2 r ≠ ⊤) :
    0 ≤ VolumeMoments.cE1 (M.cutMassAt r 0).toReal (pairMass M r).toReal
      (connMass M r).toReal ((M.ball r).ncard : ℝ) := by
  have hA : M.cutMassAt r 0 ≠ ⊤ := ne_top_of_le_ne_top h2 (cutMassAt_le_cutMoment_two M r)
  have hA2 : M.cutMassAt r 0 ^ 2 ≠ ⊤ := ENNReal.pow_ne_top hA
  have hT : connMass M r ≠ ⊤ := connMass_ne_top M r h2
  have htop : ((M.ball r).ncard : ℝ≥0∞) * (M.cutMassAt r 0) ^ 2 ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) hA2
  have hsumtop : ((M.ball r).ncard : ℝ≥0∞) * (M.cutMassAt r 0) ^ 2 + connMass M r ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨htop, hT⟩
  have hreal : (pairMass M r).toReal
      ≤ (((M.ball r).ncard : ℝ≥0∞) * (M.cutMassAt r 0) ^ 2).toReal + (connMass M r).toReal := by
    have h1 : (pairMass M r).toReal
        ≤ (((M.ball r).ncard : ℝ≥0∞) * (M.cutMassAt r 0) ^ 2 + connMass M r).toReal :=
      ENNReal.toReal_mono hsumtop (pairMass_le M r)
    rwa [ENNReal.toReal_add htop hT] at h1
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast] at hreal
  simp only [VolumeMoments.cE1]
  refine div_nonneg ?_ (by positivity)
  linarith


/-- **Lemma I.4.7's inequality in `I411` coordinates:**

`E_r[|K_0| ∑_{y∈B_r} 1(y ∉ K_0)|K_y|] ≤ |B_r| (E_r|K_0|)²`.

The excluded expectation is the `I411.exclMoment` of `Correlation/I411/Basic.lean`, whose
expansion `exclMoment_eq_tsum_apartSet` runs over the source's `apartSet`; nothing here is
replaced by `disjSet`. -/
theorem exclMoment_le (r : ℝ) (h2 : M.cutMoment 2 r ≠ ⊤) :
    I411.exclMoment (M.cutProb r) (0 : M.V) (ballF M r)
      ≤ ((M.ball r).ncard : ℝ≥0∞) * (M.cutMassAt r 0) ^ 2 := by
  rw [← exclMass_eq_exclMoment M r]
  exact exclMass_le M r (connMass_ne_top M r h2)

/-- **The `hE1` hypothesis of `Analysis/Polygon/ChiLower` at the source model.**

`ChiLower.eventually_lower_of_ode_of_E1_nonneg_of_tendsto_E0` consumes
`hE1 : ∀ t, r₀ ≤ t → 0 ≤ E1 t`.  This is that hypothesis for the source's actual defect
`𝓔_{1,r} = (|B_r| χ(r)² - E[|K|∑_{B_r}|K_y|] + E[|K|²|K∩B_r|])/(|B_r| χ(r)²)`, on any
interval `[r₀,∞)` on which the second cutoff moment is finite. -/
theorem chiLower_E1_nonneg (r₀ : ℝ) (h2 : ∀ r : ℝ, r₀ ≤ r → M.cutMoment 2 r ≠ ⊤) :
    ∀ t : ℝ, r₀ ≤ t → 0 ≤ VolumeMoments.cE1 (M.cutMassAt t 0).toReal
      (pairMass M t).toReal (connMass M t).toReal ((M.ball t).ncard : ℝ) :=
  fun t ht => cE1_nonneg M t (h2 t ht)


/-! ## Part 5: the FKG half — `E1 ≤ E[|K|²|K∩B_r|]/(b χ²)` -/

variable {V : Type*} [Countable V]

/-- Convert a real product inequality between finite `ℝ≥0∞` quantities back to `ℝ≥0∞`. -/
theorem ennreal_mul_le_of_toReal_le {a b c : ℝ≥0∞} (ha : a ≠ ⊤) (hb : b ≠ ⊤) (hc : c ≠ ⊤)
    (h : a.toReal * b.toReal ≤ c.toReal) : a * b ≤ c := by
  rw [← ENNReal.toReal_le_toReal (ENNReal.mul_ne_top ha hb) hc, ENNReal.toReal_mul]
  exact h

/-- **Harris–FKG for pairs of connection events**, in `ℝ≥0∞`:
`P(x↔z) P(y↔w) ≤ P(x↔z, y↔w)`.

`|·|` is a decreasing function of the edge configuration but an increasing function of the
cluster, so the cluster-event form of FKG applies; this is the lower half of Lemma I.2.1(iii)
that the paper's Lemma I.4.7 proof quotes. -/
theorem edgeMeasure_conn_ge (π : Sym2 V → unitInterval) (x y : V) (z w : V) :
    (edgeMeasure π) (connSet x z) * (edgeMeasure π) (connSet y w)
      ≤ (edgeMeasure π) (connSet x z ∩ connSet y w) := by
  have hprob : ∀ s : Set (Config V), (edgeMeasure π) s ≤ 1 := by
    intro s
    calc (edgeMeasure π) s ≤ (edgeMeasure π) Set.univ := measure_mono (Set.subset_univ s)
      _ = 1 := measure_univ
  have hne : ∀ s : Set (Config V), (edgeMeasure π) s ≠ ⊤ := fun s =>
    ne_top_of_le_ne_top (by simp) (hprob s)
  have h := edgeMeasure_fkg π (connSet x z) (connSet y w) (isUpper_connSet x z)
    (isUpper_connSet y w) (finiteWitness_connSet x z) (finiteWitness_connSet y w)
  rw [Measure.real_def, Measure.real_def, Measure.real_def] at h
  exact ennreal_mul_le_of_toReal_le (hne _) (hne _) (hne _) h

/-- **The cluster-weight two-point covariance bound, FKG half:**
`E|K_x| E|K_y| ≤ E|K_x||K_y|`. -/
theorem edgeMeasure_clusterVol_pair_ge (π : Sym2 V → unitInterval) (x y : V) :
    (∫⁻ ω, clusterVol ω x ∂(edgeMeasure π)) * (∫⁻ ω, clusterVol ω y ∂(edgeMeasure π))
      ≤ ∫⁻ ω, clusterVol ω x * clusterVol ω y ∂(edgeMeasure π) := by
  rw [lintegral_clusterVol, lintegral_clusterVol, lintegral_clusterVol_mul]
  calc (∑' z : V, (edgeMeasure π) (connSet x z)) * (∑' w : V, (edgeMeasure π) (connSet y w))
      = ∑' z : V, ∑' w : V,
          (edgeMeasure π) (connSet x z) * (edgeMeasure π) (connSet y w) := by
        rw [← ENNReal.tsum_mul_right]
        simp_rw [ENNReal.tsum_mul_left]
    _ ≤ ∑' z : V, ∑' w : V, (edgeMeasure π) (connSet x z ∩ connSet y w) :=
        ENNReal.tsum_le_tsum fun z => ENNReal.tsum_le_tsum fun w => edgeMeasure_conn_ge π x y z w

theorem pair_ge' (r : ℝ) (y : M.V) :
    (∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.cutLaw r))
        * (∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.cutLaw r))
      ≤ ∫⁻ ω, clusterVol ω (0 : M.V) * clusterVol ω y ∂(M.cutLaw r) := by
  have h := edgeMeasure_clusterVol_pair_ge (M.cutProb r) (0 : M.V) y
  rw [← cutLaw_eq M r] at h
  have htrans : ∫⁻ ω, clusterVol ω y ∂(M.cutLaw r)
      = ∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.cutLaw r) := by
    simpa only [SourceModelData.cutMassAt] using M.cutMassAt_eq_zero r y
  rwa [htrans] at h

/-- FKG half at the source model, in `χ` notation. -/
theorem pair_ge (r : ℝ) (y : M.V) :
    M.cutMassAt r 0 * M.cutMassAt r 0
      ≤ ∫⁻ ω, clusterVol ω (0 : M.V) * clusterVol ω y ∂(M.cutLaw r) := by
  simpa only [SourceModelData.cutMassAt] using pair_ge' M r y

/-- **`|B_r| χ² ≤ E|K| ∑_{B_r}|K_y|`** — the FKG half of Lemma I.4.7. -/
theorem pairMass_ge (r : ℝ) :
    ((M.ball r).ncard : ℝ≥0∞) * (M.cutMassAt r 0) ^ 2 ≤ pairMass M r := by
  have hsplit : ∀ ω : Config M.V, clusterVol ω (0 : M.V) * ∑ y ∈ ballF M r, clusterVol ω y
      = ∑ y ∈ ballF M r, clusterVol ω (0 : M.V) * clusterVol ω y := fun ω =>
    Finset.mul_sum (s := ballF M r) (f := fun y => clusterVol ω y) (a := clusterVol ω (0 : M.V))
  rw [pairMass]
  calc ((M.ball r).ncard : ℝ≥0∞) * (M.cutMassAt r 0) ^ 2
      = ∑ y ∈ ballF M r, M.cutMassAt r 0 * M.cutMassAt r 0 := by
        rw [Finset.sum_const, card_ballF M r, nsmul_eq_mul, pow_two]
    _ ≤ ∑ y ∈ ballF M r, ∫⁻ ω, clusterVol ω (0 : M.V) * clusterVol ω y ∂(M.cutLaw r) :=
        Finset.sum_le_sum fun y _ => pair_ge M r y
    _ = ∫⁻ ω, ∑ y ∈ ballF M r, clusterVol ω (0 : M.V) * clusterVol ω y ∂(M.cutLaw r) := by
        rw [lintegral_finsetSum]
        exact fun y _ => (measurable_clusterVol (0 : M.V)).mul (measurable_clusterVol y)
    _ = ∫⁻ ω, clusterVol ω (0 : M.V) * ∑ y ∈ ballF M r, clusterVol ω y ∂(M.cutLaw r) :=
        lintegral_congr fun ω => (hsplit ω).symm


theorem pairMass_ne_top (r : ℝ) (h2 : M.cutMoment 2 r ≠ ⊤) : pairMass M r ≠ ⊤ := by
  have hA : M.cutMassAt r 0 ≠ ⊤ := ne_top_of_le_ne_top h2 (cutMassAt_le_cutMoment_two M r)
  have hA2 : M.cutMassAt r 0 ^ 2 ≠ ⊤ := ENNReal.pow_ne_top hA
  have hT : connMass M r ≠ ⊤ := connMass_ne_top M r h2
  have hE : exclMass M r ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simp) hA2) (exclMass_le M r hT)
  rw [pairMass_eq M r]
  exact ENNReal.add_ne_top.2 ⟨hT, hE⟩

/-- `χ(r) ≥ 1`, since the root is in its own cluster. -/
theorem one_le_cutMassAt (r : ℝ) : (1 : ℝ≥0∞) ≤ M.cutMassAt r 0 := by
  simp only [SourceModelData.cutMassAt]
  calc (1 : ℝ≥0∞) = ∫⁻ ω, (1 : ℝ≥0∞) ∂(M.cutLaw r) := by
        rw [lintegral_one, measure_univ]
    _ ≤ ∫⁻ ω, clusterVol ω (0 : M.V) ∂(M.cutLaw r) :=
        lintegral_mono fun ω => one_le_clusterVol M ω (0 : M.V)

/-- **Lemma I.4.7, upper half, at the source model:**
`𝓔_{1,r} ≤ E[|K|²|K∩B_r|]/(|B_r| χ(r)²)`. -/
theorem cE1_le (r : ℝ) (hr : 0 ≤ r) (h2 : M.cutMoment 2 r ≠ ⊤) :
    VolumeMoments.cE1 (M.cutMassAt r 0).toReal (pairMass M r).toReal
        (connMass M r).toReal ((M.ball r).ncard : ℝ)
      ≤ (connMass M r).toReal
          / (((M.ball r).ncard : ℝ) * (M.cutMassAt r 0).toReal ^ 2) := by
  have hA : M.cutMassAt r 0 ≠ ⊤ := ne_top_of_le_ne_top h2 (cutMassAt_le_cutMoment_two M r)
  have hzero : (0 : M.V) ∈ M.ball r := by
    change M.S.ρ (toVec (0 : M.V)) ≤ r
    have h0 : toVec (0 : M.V) = 0 := by
      funext i
      simp [toVec]
    rw [h0, M.S.ρ_zero]
    exact hr
  have hbpos : 0 < (M.ball r).ncard :=
    (Set.ncard_pos (M.finite_ball r)).mpr ⟨0, hzero⟩
  have hbR : (0 : ℝ) < ((M.ball r).ncard : ℝ) := by exact_mod_cast hbpos
  have hA1 : (1 : ℝ) ≤ (M.cutMassAt r 0).toReal := by
    have h := ENNReal.toReal_mono hA (one_le_cutMassAt M r)
    simpa using h
  have hden : 0 < ((M.ball r).ncard : ℝ) * (M.cutMassAt r 0).toReal ^ 2 := by
    have : (0 : ℝ) < (M.cutMassAt r 0).toReal := by linarith
    positivity
  have hSge : ((M.ball r).ncard : ℝ) * (M.cutMassAt r 0).toReal ^ 2 ≤ (pairMass M r).toReal := by
    have h := ENNReal.toReal_mono (pairMass_ne_top M r h2) (pairMass_ge M r)
    rwa [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast] at h
  simp only [VolumeMoments.cE1]
  rw [div_le_div_iff_of_pos_right hden]
  linarith

/-- **Lemma I.4.7 in full at the source model:** both the sign and the upper bound,
`0 ≤ 𝓔_{1,r} ≤ E[|K|²|K∩B_r|]/(|B_r| χ(r)²)`. -/
theorem cE1_mem_Icc (r : ℝ) (hr : 0 ≤ r) (h2 : M.cutMoment 2 r ≠ ⊤) :
    0 ≤ VolumeMoments.cE1 (M.cutMassAt r 0).toReal (pairMass M r).toReal
          (connMass M r).toReal ((M.ball r).ncard : ℝ) ∧
      VolumeMoments.cE1 (M.cutMassAt r 0).toReal (pairMass M r).toReal
          (connMass M r).toReal ((M.ball r).ncard : ℝ)
        ≤ (connMass M r).toReal
            / (((M.ball r).ncard : ℝ) * (M.cutMassAt r 0).toReal ^ 2) :=
  ⟨cE1_nonneg M r h2, cE1_le M r hr h2⟩

/-- **Lemma I.4.7 in full, `I411` coordinate form:**
`0 ≤ 1 - exclMoment/(|B_r| χ²) ≤ 1 - (χ²|B_r| - E[|K|²|K∩B_r|])/(|B_r|χ²)`, i.e. the
excluded expectation is squeezed between the two bounds the paper uses. -/
theorem exclRate_mem_Icc (r : ℝ) (hr : 0 ≤ r) (h2 : M.cutMoment 2 r ≠ ⊤) :
    0 ≤ (((M.ball r).ncard : ℝ) * (M.cutMassAt r 0).toReal ^ 2 - (exclMass M r).toReal)
          / (((M.ball r).ncard : ℝ) * (M.cutMassAt r 0).toReal ^ 2) ∧
      (((M.ball r).ncard : ℝ) * (M.cutMassAt r 0).toReal ^ 2 - (exclMass M r).toReal)
          / (((M.ball r).ncard : ℝ) * (M.cutMassAt r 0).toReal ^ 2)
        ≤ (connMass M r).toReal
            / (((M.ball r).ncard : ℝ) * (M.cutMassAt r 0).toReal ^ 2) :=
  ⟨exclRate_nonneg M r h2, by
    have hE : (exclMass M r) ≠ ⊤ := by
      have hA : M.cutMassAt r 0 ≠ ⊤ := ne_top_of_le_ne_top h2 (cutMassAt_le_cutMoment_two M r)
      exact ne_top_of_le_ne_top
        (ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top hA))
        (exclMass_le M r (connMass_ne_top M r h2))
    have hT : connMass M r ≠ ⊤ := connMass_ne_top M r h2
    have hsplit : (pairMass M r).toReal = (connMass M r).toReal + (exclMass M r).toReal := by
      rw [pairMass_eq M r, ENNReal.toReal_add hT hE]
    have h := cE1_le M r hr h2
    have hnum : (↑(M.ball r).ncard * (M.cutMassAt r 0).toReal ^ 2
          - ((connMass M r).toReal + (exclMass M r).toReal) + (connMass M r).toReal)
        = ↑(M.ball r).ncard * (M.cutMassAt r 0).toReal ^ 2 - (exclMass M r).toReal := by
      ring
    simp only [VolumeMoments.cE1] at h
    rw [hsplit, hnum] at h
    exact h⟩


/-- **Corollary I.4.8 at the source model, with the model's own defect.**

`ChiLower.eventually_cutMassAt_rpow_le_of_E1_nonneg_of_tendsto_E0` asks for
`hE1 : ∀ t ≥ r₀, 0 ≤ E1 t` for the `E1` appearing in its ODE hypothesis.  Taking that `E1` to be
the model defect `t ↦ cE1 χ(t) S(t) T(t) |B_t|`, `hE1` is discharged by
`chiLower_E1_nonneg`, so the conclusion holds as soon as the ODE (I.4.6) — with the *same* defect —
and `𝓔_{0,r} → 0` are supplied. -/
theorem eventually_cutMassAt_rpow_le_of_model_defect {r₀ : ℝ} {F' E0 : ℝ → ℝ}
    (hβ : 0 < (M.betaCrit : ℝ)) (hr₀ : 0 < r₀)
    (hderiv : ∀ t, r₀ ≤ t →
      HasDerivAt (fun t => (M.cutMassAt t 0).toReal) (F' t) t)
    (hpos : ∀ t, r₀ ≤ t → 0 < (M.cutMassAt t 0).toReal)
    (hinf : Tendsto (fun t => (M.cutMassAt t 0).toReal) atTop atTop)
    (hode : ∀ t, r₀ ≤ t → F' t
      = (1 - (1 - (1 - E0 t) * (1 - VolumeMoments.cE1 (M.cutMassAt t 0).toReal
            (pairMass M t).toReal (connMass M t).toReal ((M.ball t).ncard : ℝ))))
          * (M.betaCrit : ℝ) * t ^ (-M.α - 1) * ((M.cutMassAt t 0).toReal) ^ 2)
    (hE0 : Tendsto E0 atTop (𝓝 0))
    (h2 : ∀ t : ℝ, r₀ ≤ t → M.cutMoment 2 t ≠ ⊤) :
    ∀ᶠ r : ℝ in atTop,
      M.α / ((M.betaCrit : ℝ) * 2) * r ^ M.α ≤ (M.cutMassAt r 0).toReal :=
  I418C.ChiLower.eventually_cutMassAt_rpow_le_of_E1_nonneg_of_tendsto_E0 M hβ hr₀ hderiv hpos hinf
    hode (chiLower_E1_nonneg M r₀ h2) hE0

end E1Sign
end PercLib.CriticalLRP
