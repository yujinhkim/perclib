/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
-/

module

public import PercLib.CriticalLRP.Correlation.Susceptibility
public import PercLib.CriticalLRP.VolumeMoments.SecondMoment

/-
Monotonicity of cluster-volume expectations in the edge probabilities, and
its consequences for finite second and joint moments.
-/

set_option autoImplicit false

@[expose] public section

namespace PercLib.CriticalLRP

open MeasureTheory
open scoped ENNReal NNReal

variable {V : Type*} [Countable V]

/-- Increasing every edge probability increases the expected cluster volume,
in `ℝ≥0∞` without any finite-moment assumption. -/
theorem lintegral_clusterVol_mono_of_le {π κ : Sym2 V → unitInterval}
    (hpq : ∀ e, π e ≤ κ e) (o : V) :
    (∫⁻ ω, clusterVol ω o ∂(edgeMeasure π)) ≤
      ∫⁻ ω, clusterVol ω o ∂(edgeMeasure κ) := by
  rw [lintegral_clusterVol_eq_tsum_connSet, lintegral_clusterVol_eq_tsum_connSet]
  exact ENNReal.tsum_le_tsum fun y =>
    edgeMeasure_mono_of_le hpq (measurableSet_connSet o y) (isUpper_connSet o y)

/-- Pointwise edge domination also increases the second cluster moment. -/
theorem lintegral_clusterVol_sq_mono_of_le {π κ : Sym2 V → unitInterval}
    (hpq : ∀ e, π e ≤ κ e) (o : V) :
    (∫⁻ ω, clusterVol ω o * clusterVol ω o ∂(edgeMeasure π)) ≤
      ∫⁻ ω, clusterVol ω o * clusterVol ω o ∂(edgeMeasure κ) := by
  rw [lintegral_clusterVol_mul_clusterVol, lintegral_clusterVol_mul_clusterVol]
  refine ENNReal.tsum_le_tsum fun x => ENNReal.tsum_le_tsum fun y => ?_
  apply edgeMeasure_mono_of_le hpq ((measurableSet_connSet o x).inter (measurableSet_connSet o y))
  exact (isUpper_connSet o x).inter (isUpper_connSet o y)

/-- If the dominating law has finite and root-independent first moment, its
homogeneous cubic bound gives finite second moment for the dominated law. -/
theorem lintegral_clusterVol_sq_ne_top_of_mono {π κ : Sym2 V → unitInterval}
    (hpq : ∀ e, π e ≤ κ e) (hκ : ∀ e, κ e < 1) (o : V)
    (hS : ∀ a : V, (∫⁻ ω, clusterVol ω a ∂(edgeMeasure κ)) =
      ∫⁻ ω, clusterVol ω o ∂(edgeMeasure κ))
    (hfin : (∫⁻ ω, clusterVol ω o ∂(edgeMeasure κ)) ≠ ∞) :
    (∫⁻ ω, clusterVol ω o * clusterVol ω o ∂(edgeMeasure π)) ≠ ∞ := by
  apply ne_top_of_le_ne_top ?_ (lintegral_clusterVol_sq_mono_of_le hpq o)
  refine lintegral_clusterVol_sq_ne_top κ hκ o (fun a => ?_) hfin
  rw [hS a, hS o]

/-- Under those homogeneous-mean assumptions, the dominating law's finite
first moment also gives a finite joint window moment for the dominated law. -/
theorem joint_windowMoment_ne_top_of_mono {π κ : Sym2 V → unitInterval}
    (hpq : ∀ e, π e ≤ κ e) (hκ : ∀ e, κ e < 1) (o : V) (B : Finset V)
    (hS : ∀ a : V, (∫⁻ ω, clusterVol ω a ∂(edgeMeasure κ)) =
      ∫⁻ ω, clusterVol ω o ∂(edgeMeasure κ))
    (hfin : (∫⁻ ω, clusterVol ω o ∂(edgeMeasure κ)) ≠ ∞) :
    (∫⁻ ω, clusterVol ω o * ∑ y ∈ B, clusterVol ω y ∂(edgeMeasure π)) ≠ ∞ := by
  have hsecond : ∀ a : V,
      (∫⁻ ω, clusterVol ω a * clusterVol ω a ∂(edgeMeasure κ)) ≠ ∞ := by
    intro a
    refine lintegral_clusterVol_sq_ne_top κ hκ a (fun b => ?_) (by rw [hS a]; exact hfin)
    rw [hS b, hS a]
  have hdom : (∫⁻ ω, clusterVol ω o * ∑ y ∈ B, clusterVol ω y ∂(edgeMeasure π)) ≤
      ∑ y ∈ B, ((∫⁻ ω, clusterVol ω o * clusterVol ω o ∂(edgeMeasure κ)) +
        ∫⁻ ω, clusterVol ω y * clusterVol ω y ∂(edgeMeasure κ)) :=
    by
      have hb := (joint_windowMoment_le_sum_second_moments π o B).trans
        (Finset.sum_le_sum fun y _ => by
          have h0 : (∫⁻ ω, Percolation.cardFun (cluster ω o) *
              Percolation.cardFun (cluster ω o) ∂(edgeMeasure π)) ≤
              ∫⁻ ω, clusterVol ω o * clusterVol ω o ∂(edgeMeasure κ) := by
            simpa only [Percolation.cardFun_eq_encard] using
              lintegral_clusterVol_sq_mono_of_le hpq o
          have hy : (∫⁻ ω, Percolation.cardFun (cluster ω y) *
              Percolation.cardFun (cluster ω y) ∂(edgeMeasure π)) ≤
              ∫⁻ ω, clusterVol ω y * clusterVol ω y ∂(edgeMeasure κ) := by
            simpa only [Percolation.cardFun_eq_encard] using
              lintegral_clusterVol_sq_mono_of_le hpq y
          exact add_le_add h0 hy)
      simpa only [Percolation.cardFun_eq_encard] using hb
  refine ne_top_of_le_ne_top ?_ hdom
  rw [ENNReal.sum_ne_top]
  intro y _
  exact ENNReal.add_ne_top.mpr ⟨hsecond o, hsecond y⟩

end PercLib.CriticalLRP
