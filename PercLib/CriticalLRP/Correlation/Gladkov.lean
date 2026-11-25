/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.

The Gladkov inequality itself is packaged in `GladkovInput`, at the user's
request to assume it temporarily. It is not introduced as an axiom or asserted
as a proved theorem. Corollary I.2.8 and its cutoff specialization are proved
from that exact hypothesis and ordinary transitivity/root independence.
-/

module

public import PercLib.CriticalLRP.Correlation.Gladkov.Defs
public import PercLib.Percolation.Bond.ClusterMoments
public import PercLib.CriticalLRP.CutoffDominated
public import PercLib.CriticalLRP.CountableProduct.LRPTailBounds
public import PercLib.CriticalLRP.Analysis.ENNRealCauchy

set_option autoImplicit false

@[expose] public section

namespace PercLib.CriticalLRP.Correlation

open scoped ENNReal

namespace Gladkov

attribute [local instance] Classical.propDecidable

theorem gladkov_constant : (8 : ℝ≥0∞) ^ (1 / 2 : ℝ) = (2 : ℝ≥0∞) ^ (3 / 2 : ℝ) := by
  symm
  calc
    (2 : ℝ≥0∞) ^ (3 / 2 : ℝ) = ((2 : ℝ≥0∞) ^ (3 : ℝ)) ^ (1 / 2 : ℝ) := by
      have h := ENNReal.rpow_mul (2 : ℝ≥0∞) (3 : ℝ) (1 / 2 : ℝ)
      norm_num at h ⊢
      exact h
    _ = ((2 : ℝ≥0∞) ^ (3 : ℕ)) ^ (1 / 2 : ℝ) :=
      congrArg (fun a : ℝ≥0∞ => a ^ (1 / 2 : ℝ)) (ENNReal.rpow_natCast 2 3)
    _ = (8 : ℝ≥0∞) ^ (1 / 2 : ℝ) := by norm_num

private theorem rpow_half_sq (a : ℝ≥0∞) : (a ^ (1 / 2 : ℝ)) ^ 2 = a := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

private theorem half_self_mul (a : ℝ≥0∞) : a ^ (1 / 2 : ℝ) * a ^ (1 / 2 : ℝ) = a := by
  rw [← pow_two, rpow_half_sq]

private theorem rpow_half_le_of_sq_le {a b : ℝ≥0∞} (h : a ^ 2 ≤ b) :
    a ≤ b ^ (1 / 2 : ℝ) := by
  calc
    a = (a ^ 2) ^ (1 / 2 : ℝ) := by
      symm
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
      norm_num
    _ ≤ _ := ENNReal.rpow_le_rpow h (by norm_num)

/-- The inner summation bound for the assumed three-point Gladkov inequality.
Only the precise squared input and root-independence of the mean are required. -/
theorem inner_sum_bound {V : Type*} (x : V) (τ T : V → V → ℝ≥0∞) (χ : ℝ≥0∞)
    (hmean : ∀ z, ∑' y, τ y z = χ) (hxmean : ∑' y, τ x y = χ)
    (hgl : ∀ y z, T y z ^ 2 ≤ 8 * τ x y * τ y z * τ z x) (z : V) :
    ∑' y, T y z ≤
      (8 : ℝ≥0∞) ^ (1 / 2 : ℝ) * χ * (τ z x) ^ (1 / 2 : ℝ) := by
  calc
    ∑' y, T y z ≤
        ∑' y, (8 * τ x y * τ y z * τ z x) ^ (1 / 2 : ℝ) :=
      ENNReal.tsum_le_tsum fun y => rpow_half_le_of_sq_le (a := T y z) (hgl y z)
    _ = ∑' y, (8 : ℝ≥0∞) ^ (1 / 2 : ℝ) * (τ z x) ^ (1 / 2 : ℝ) *
        (τ x y * τ y z) ^ (1 / 2 : ℝ) := by
      congr 1
      funext y
      simp only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      ring
    _ = (8 : ℝ≥0∞) ^ (1 / 2 : ℝ) * (τ z x) ^ (1 / 2 : ℝ) *
        ∑' y, (τ x y * τ y z) ^ (1 / 2 : ℝ) := by rw [ENNReal.tsum_mul_left]
    _ ≤ (8 : ℝ≥0∞) ^ (1 / 2 : ℝ) * (τ z x) ^ (1 / 2 : ℝ) *
        ((∑' y, τ x y) ^ (1 / 2 : ℝ) * (∑' y, τ y z) ^ (1 / 2 : ℝ)) := by
      exact mul_le_mul le_rfl
        (PercLib.CriticalLRP.Analysis.tsum_rpow_half_mul_le (fun y => τ x y) (fun y => τ y z))
        (by positivity) (by positivity)
    _ = (8 : ℝ≥0∞) ^ (1 / 2 : ℝ) * χ * (τ z x) ^ (1 / 2 : ℝ) := by
      rw [hxmean, hmean z, half_self_mul]
      ring

/-- **The mixed-moment summation consequence of Gladkov's inequality.** The
input is the exact squared three-point bound. Both unwindowed means are supplied
by `hxmean` and `hmean`; no finite-mean assumption is made. -/
theorem window_sum_bound {V : Type*} (x : V) (τ T : V → V → ℝ≥0∞) (χ : ℝ≥0∞)
    (hmean : ∀ z, ∑' y, τ y z = χ) (hxmean : ∑' y, τ x y = χ)
    (hgl : ∀ y z, T y z ^ 2 ≤ 8 * τ x y * τ y z * τ z x)
    (W : Finset V) :
    ∑' y, ∑' z, (if z ∈ W then T y z else 0) ≤
      (8 : ℝ≥0∞) ^ (1 / 2 : ℝ) * χ *
        (((W.card : ℝ≥0∞) * ∑' z, (if z ∈ W then τ z x else 0)) ^ (1 / 2 : ℝ)) := by
  classical
  have hcard : (∑' z, if z ∈ W then (1 : ℝ≥0∞) else 0) = (W.card : ℝ≥0∞) := by
    rw [tsum_eq_sum (s := W) (by intro z hz; simp [hz])]
    simp
  have hprod :
      (∑' z, (if z ∈ W then τ z x else 0)) ^ (1 / 2 : ℝ) *
          ((W.card : ℝ≥0∞)) ^ (1 / 2 : ℝ) =
        (((W.card : ℝ≥0∞) * ∑' z, (if z ∈ W then τ z x else 0)) ^ (1 / 2 : ℝ)) := by
    calc
      _ = ((∑' z, (if z ∈ W then τ z x else 0)) * (W.card : ℝ≥0∞)) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      _ = _ := by rw [mul_comm]
  calc
    ∑' y, ∑' z, (if z ∈ W then T y z else 0) =
        ∑' z, ∑' y, (if z ∈ W then T y z else 0) := ENNReal.tsum_comm
    _ ≤ ∑' z, (if z ∈ W then
        (8 : ℝ≥0∞) ^ (1 / 2 : ℝ) * χ * (τ z x) ^ (1 / 2 : ℝ) else 0) := by
      refine ENNReal.tsum_le_tsum fun z => ?_
      by_cases hz : z ∈ W
      · simp only [hz, ite_eq_left]
        exact inner_sum_bound x τ T χ hmean hxmean hgl z
      · simp [hz]
    _ = ∑' z, (8 : ℝ≥0∞) ^ (1 / 2 : ℝ) * χ *
        (if z ∈ W then (τ z x) ^ (1 / 2 : ℝ) else 0) := by
      apply tsum_congr
      intro z
      by_cases hz : z ∈ W <;> simp [hz]
    _ = (8 : ℝ≥0∞) ^ (1 / 2 : ℝ) * χ *
        ∑' z, (if z ∈ W then (τ z x) ^ (1 / 2 : ℝ) else 0) := by
      rw [ENNReal.tsum_mul_left]
    _ = (8 : ℝ≥0∞) ^ (1 / 2 : ℝ) * χ *
        ∑' z, ((if z ∈ W then τ z x else 0) *
          (if z ∈ W then (1 : ℝ≥0∞) else 0)) ^ (1 / 2 : ℝ) := by
      congr 2
      funext z
      by_cases hz : z ∈ W <;> simp [hz]
    _ ≤ (8 : ℝ≥0∞) ^ (1 / 2 : ℝ) * χ *
        ((∑' z, (if z ∈ W then τ z x else 0)) ^ (1 / 2 : ℝ) *
          (∑' z, if z ∈ W then (1 : ℝ≥0∞) else 0) ^ (1 / 2 : ℝ)) := by
      apply mul_le_mul le_rfl _ (by positivity) (by positivity)
      exact PercLib.CriticalLRP.Analysis.tsum_rpow_half_mul_le
        (fun z => if z ∈ W then τ z x else 0) (fun z => if z ∈ W then 1 else 0)
    _ = _ := by
      rw [hcard, hprod]

open MeasureTheory

/-- Exact double-summation identity for a full cluster volume times its
intersection with a finite window. No finiteness assumption is needed. -/
theorem lintegral_cluster_mul_inter_eq_tsum {V : Type*} [Countable V]
    (π : Sym2 V → unitInterval) (x : V) (W : Finset V) :
    (∫⁻ ω, ((PercLib.Percolation.Bond.cluster ω x).encard : ℝ≥0∞) *
      (((PercLib.Percolation.Bond.cluster ω x ∩ (W : Set V)).encard) : ℝ≥0∞)
      ∂(PercLib.Percolation.Bond.law π)) =
      ∑' y, ∑' z, (if z ∈ W then
        PercLib.Percolation.Bond.law π
          (PercLib.Percolation.Bond.conn x y ∩ PercLib.Percolation.Bond.conn x z) else 0) := by
  classical
  have hpoint : ∀ ω : PercLib.Percolation.Bond.Config V,
      ((PercLib.Percolation.Bond.cluster ω x).encard : ℝ≥0∞) *
        (((PercLib.Percolation.Bond.cluster ω x ∩ (W : Set V)).encard) : ℝ≥0∞) =
      ∑' y, ∑' z, (if z ∈ W then
        ((PercLib.Percolation.Bond.conn x y ∩ PercLib.Percolation.Bond.conn x z).indicator
          (fun _ => (1 : ℝ≥0∞)) ω) else 0) := by
    intro ω
    calc
      ((PercLib.Percolation.Bond.cluster ω x).encard : ℝ≥0∞) *
          (((PercLib.Percolation.Bond.cluster ω x ∩ (W : Set V)).encard) : ℝ≥0∞) =
          ∑ z ∈ W, ∑' y, (PercLib.Percolation.Bond.conn x y).indicator
            (fun _ => (1 : ℝ≥0∞)) ω *
              (PercLib.Percolation.Bond.conn x z).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
        rw [PercLib.Percolation.Bond.encard_cluster_eq_tsum,
          PercLib.Percolation.Bond.encard_cluster_inter_finset_eq_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z hz
        rw [ENNReal.tsum_mul_right]
      _ = ∑ z ∈ W, (if z ∈ W then ∑' y,
            (PercLib.Percolation.Bond.conn x y).indicator (fun _ => (1 : ℝ≥0∞)) ω *
              (PercLib.Percolation.Bond.conn x z).indicator (fun _ => (1 : ℝ≥0∞)) ω
            else 0) := by
        apply Finset.sum_congr rfl
        intro z hz
        simp [hz]
      _ = ∑' z, if z ∈ W then ∑' y, (PercLib.Percolation.Bond.conn x y).indicator
            (fun _ => (1 : ℝ≥0∞)) ω *
              (PercLib.Percolation.Bond.conn x z).indicator (fun _ => (1 : ℝ≥0∞)) ω else 0 :=
        (tsum_eq_sum (s := W)
          (f := fun z => if z ∈ W then ∑' y,
            (PercLib.Percolation.Bond.conn x y).indicator (fun _ => (1 : ℝ≥0∞)) ω *
              (PercLib.Percolation.Bond.conn x z).indicator (fun _ => (1 : ℝ≥0∞)) ω
            else 0) (by intro z hz; simp [hz])).symm
      _ = ∑' y, ∑' z, (if z ∈ W then (PercLib.Percolation.Bond.conn x y).indicator
            (fun _ => (1 : ℝ≥0∞)) ω *
              (PercLib.Percolation.Bond.conn x z).indicator (fun _ => (1 : ℝ≥0∞)) ω else 0) := by
        rw [ENNReal.tsum_comm]
        apply tsum_congr
        intro z
        by_cases hz : z ∈ W <;> simp [hz]
      _ = _ := by
        apply tsum_congr
        intro y
        apply tsum_congr
        intro z
        by_cases hz : z ∈ W
        · simp only [hz, ite_eq_left]
          by_cases hy : ω ∈ PercLib.Percolation.Bond.conn x y <;>
            by_cases hx : ω ∈ PercLib.Percolation.Bond.conn x z <;>
              simp [Set.indicator, hy, hx]
        · simp [hz]
  have hf (y z : V) : Measurable (fun ω : PercLib.Percolation.Bond.Config V =>
      if z ∈ W then (PercLib.Percolation.Bond.conn x y ∩
        PercLib.Percolation.Bond.conn x z).indicator (fun _ => (1 : ℝ≥0∞)) ω else 0) := by
    by_cases hz : z ∈ W
    · simp only [hz, ite_eq_left]
      exact measurable_const.indicator ((PercLib.Percolation.Bond.measurableSet_conn x y).inter
        (PercLib.Percolation.Bond.measurableSet_conn x z))
    · simp [hz]
  simp_rw [hpoint]
  rw [lintegral_tsum (fun y => Measurable.tsum (hf y) |>.aemeasurable)]
  congr 1
  funext y
  rw [lintegral_tsum (fun z => (hf y z).aemeasurable)]
  congr 1
  funext z
  by_cases hz : z ∈ W
  · simp only [hz, ite_eq_left]
    exact MeasureTheory.lintegral_indicator_one
      ((PercLib.Percolation.Bond.measurableSet_conn x y).inter
        (PercLib.Percolation.Bond.measurableSet_conn x z))
  · simp [hz]

open PercLib.Percolation.Bond PercLib.CriticalLRP.FiniteVolume
open PercLib.CriticalLRP.CutoffKernel
open PercLib.CriticalLRP.CutoffLimit

/-- The expected volume of a cluster intersection with a finite window. -/
theorem lintegral_cluster_inter_eq_tsum {V : Type*} [Countable V]
    (π : Sym2 V → unitInterval) (x : V) (W : Finset V) :
    (∫⁻ ω, ((cluster ω x ∩ (W : Set V)).encard : ℝ≥0∞) ∂(law π)) =
      ∑' z, (if z ∈ W then law π (conn x z) else 0) := by
  classical
  calc
    (∫⁻ ω, ((cluster ω x ∩ (W : Set V)).encard : ℝ≥0∞) ∂(law π)) =
        ∑ z ∈ W, law π (conn x z) := by
      simp_rw [encard_cluster_inter_finset_eq_sum]
      rw [lintegral_finsetSum W (fun z hz => measurable_const.indicator (measurableSet_conn x z))]
      congr 1
      funext z
      exact MeasureTheory.lintegral_indicator_one (measurableSet_conn x z)
    _ = ∑' z, (if z ∈ W then law π (conn x z) else 0) := by
      rw [tsum_eq_sum (s := W) (by intro z hz; simp [hz])]
      apply Finset.sum_congr rfl
      intro z hz
      simp [hz]

/-- **I.2.8 from the exact Gladkov inequality and root independence.** The
`GladkovInput` is precisely the source three-point inequality. No finiteness
assumption on the full unwindowed mean is made. -/
theorem mixed_moment_le_of_gladkov {V : Type*} [Countable V]
    (π : Sym2 V → unitInterval) (x : V)
    (hroot : ∀ z, chi π z = chi π x)
    (input : GladkovInput π x)
    (W : Finset V) :
    (∫⁻ ω, ((cluster ω x).encard : ℝ≥0∞) *
      (((cluster ω x ∩ (W : Set V)).encard) : ℝ≥0∞) ∂(law π)) ≤
      (8 : ℝ≥0∞) ^ (1 / 2 : ℝ) * chi π x *
        ((W.card : ℝ≥0∞) *
          (∫⁻ ω, ((cluster ω x ∩ (W : Set V)).encard : ℝ≥0∞) ∂(law π))) ^ (1 / 2 : ℝ) := by
  have hmean : ∀ z, (∑' y, law π (conn z y)) = chi π x := by
    intro z
    exact (chi_eq_tsum_tau π z).symm.trans (hroot z)
  have hxmean : (∑' y, law π (conn y x)) = chi π x := by
    calc
      ∑' y, law π (conn y x) = ∑' y, tau π x y := by
        apply tsum_congr
        intro y
        exact (tau_comm π x y).symm
      _ = chi π x := (chi_eq_tsum_tau π x).symm
  rw [lintegral_cluster_mul_inter_eq_tsum, lintegral_cluster_inter_eq_tsum]
  exact window_sum_bound x (fun a b => law π (conn b a))
    (fun y z => law π (conn x y ∩ conn x z)) (chi π x) hmean hxmean (by
      intro y z
      calc
        law π (conn x y ∩ conn x z) ^ 2 ≤
            8 * law π (conn x y) * law π (conn y z) * law π (conn z x) :=
          input.three_point_sq_le y z
        _ = 8 * law π (conn y x) * law π (conn z y) * law π (conn x z) := by
          rw [conn_symm x y, conn_symm y z, conn_symm z x]) W

/-- The conditional mixed-moment bound at the loop-safe cutoff law. Translation
invariance supplies the root-independence; the Gladkov input remains explicit. -/
theorem mixed_moment_le_of_gladkov_cutoff {d : ℕ} {K : ℝ → ℝ}
    (hK : AntitoneOn K (Set.Ioi 0)) (r : ℝ) (β : NNReal) (x : Fin d → ℤ)
    (input : GladkovInput (bernoulliEdgeProb (CutoffKernel.cutoffSymKernel K d r)
      (fun e => cutoffSymKernel_nonneg' hK d r e) β) x)
    (W : Finset (Fin d → ℤ)) :
    (∫⁻ ω, ((PercLib.CriticalLRP.cluster ω x).encard : ℝ≥0∞) *
      (((PercLib.CriticalLRP.cluster ω x ∩ (W : Set (Fin d → ℤ))).encard) : ℝ≥0∞)
      ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
        (fun e => cutoffSymKernel_nonneg' hK d r e) β)) ≤
      (8 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
        (∫⁻ ω, ((PercLib.CriticalLRP.cluster ω x).encard : ℝ≥0∞)
          ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
            (fun e => cutoffSymKernel_nonneg' hK d r e) β)) *
        ((W.card : ℝ≥0∞) *
          (∫⁻ ω, (((PercLib.CriticalLRP.cluster ω x ∩ (W : Set (Fin d → ℤ))).encard) : ℝ≥0∞)
            ∂(longRangeMeasure (CutoffKernel.cutoffSymKernel K d r)
              (fun e => cutoffSymKernel_nonneg' hK d r e) β))) ^ (1 / 2 : ℝ) := by
  have hcomm : ∀ z : Fin d → ℤ,
      chi (bernoulliEdgeProb (CutoffKernel.cutoffSymKernel K d r)
        (fun e => cutoffSymKernel_nonneg' hK d r e) β) z =
      chi (bernoulliEdgeProb (CutoffKernel.cutoffSymKernel K d r)
        (fun e => cutoffSymKernel_nonneg' hK d r e) β) x := by
    intro z
    simpa only [chi, longRangeMeasure,
      PercLib.CriticalLRP.Percolation.cardFun_eq_encard] using
      PercLib.CriticalLRP.Hvol.hvol_cardFun
        (bernoulliEdgeProb_shift (CutoffKernel.cutoffSymKernel_shift K d r)
          (fun e => cutoffSymKernel_nonneg' hK d r e) β) x z
  simpa only [longRangeMeasure, PercLib.CriticalLRP.edgeMeasure_eq_law, chi] using
    mixed_moment_le_of_gladkov
      (π := bernoulliEdgeProb (CutoffKernel.cutoffSymKernel K d r)
        (fun e => cutoffSymKernel_nonneg' hK d r e) β) x hcomm
      (by simpa only [longRangeMeasure] using input) W

end Gladkov
end PercLib.CriticalLRP.Correlation
