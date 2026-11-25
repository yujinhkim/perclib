/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
-/

module

public import PercLib.CriticalLRP.Correlation.I411.ApartGap
public import PercLib.CriticalLRP.VolumeMoments.ErrorBounds

/-
Finite-moment passage from the exact I.4.11 display to its real `cE1`
form. Infinite expectations are not assigned a real difference.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP.I411

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- The joint window moment splits into its excluded and connected parts.
This additive identity requires no moment-finiteness hypothesis. -/
theorem joint_eq_excluded_add_windowMoment (π : Sym2 V → unitInterval)
    (o : V) (B : Finset V) :
    exclMoment π o B +
        ∫⁻ ω, ((B.filter fun y => y ∈ cluster ω o).card : ℝ≥0∞) *
          (Percolation.cardFun (cluster ω o) * Percolation.cardFun (cluster ω o))
          ∂(edgeMeasure π)
      = ∫⁻ ω, Percolation.cardFun (cluster ω o) *
          ∑ y ∈ B, Percolation.cardFun (cluster ω y) ∂(edgeMeasure π) := by
  have hm : Measurable fun ω : Config V => Percolation.cardFun (cluster ω o) :=
    Hrest.measurable_cardFun_cluster_canonical o
  have hexpand :
      ∫⁻ ω, clusterVol ω o * ∑ y ∈ B, (cluster ω o)ᶜ.indicator
          (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y ∂(edgeMeasure π)
        = ∑ y ∈ B, ∫⁻ ω, (cluster ω o)ᶜ.indicator
          (fun _ => (1 : ℝ≥0∞)) y * (clusterVol ω o * clusterVol ω y)
            ∂(edgeMeasure π) := by
    calc
      _ = ∫⁻ ω, ∑ y ∈ B, (cluster ω o)ᶜ.indicator
          (fun _ => (1 : ℝ≥0∞)) y * (clusterVol ω o * clusterVol ω y)
            ∂(edgeMeasure π) := by
        refine lintegral_congr fun ω => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => by ring
      _ = _ := lintegral_finsetSum B fun y _ =>
        (measurable_const.indicator (measurableSet_cluster_mem o y).compl).mul
          ((measurable_clusterVol o).mul (measurable_clusterVol y))
  calc
    exclMoment π o B + _ = _ := by
      rw [exclMoment, hexpand, Hrest.lintegral_joint_cardFun_sum,
        Hrest.lintegral_connected_cardFun_sum]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun y _ => ?_
      have hnot :
          (∫⁻ ω, (cluster ω o)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) y *
            (clusterVol ω o * clusterVol ω y) ∂(edgeMeasure π)) =
          ∫⁻ ω, {ω : Config V | ¬ Connects ω o y}.indicator
            (fun _ => (1 : ℝ≥0∞)) ω *
            (Percolation.cardFun (cluster ω o) * Percolation.cardFun (cluster ω y))
            ∂(edgeMeasure π) := by
        congr 1
        funext ω
        by_cases h : Connects ω o y
        · have hy : y ∈ cluster ω o := mem_cluster_iff.mpr h
          simp [h, hy, Percolation.cardFun_eq_encard]
        · have hy : y ∉ cluster ω o := fun hy => h (mem_cluster_iff.mp hy)
          simp [h, hy, Percolation.cardFun_eq_encard]
      rw [hnot]
      calc
        (∫⁻ ω, {ω : Config V | ¬ Connects ω o y}.indicator
              (fun _ => (1 : ℝ≥0∞)) ω *
            (Percolation.cardFun (cluster ω o) * Percolation.cardFun (cluster ω y))
            ∂(edgeMeasure π)) +
            ∫⁻ ω, {ω : Config V | Connects ω o y}.indicator
              (fun _ => (1 : ℝ≥0∞)) ω *
              (Percolation.cardFun (cluster ω o) * Percolation.cardFun (cluster ω o))
              ∂(edgeMeasure π)
          = (∫⁻ ω, {ω : Config V | ¬ Connects ω o y}.indicator
              (fun _ => (1 : ℝ≥0∞)) ω *
              (Percolation.cardFun (cluster ω o) * Percolation.cardFun (cluster ω y))
              ∂(edgeMeasure π)) +
            ∫⁻ ω, {ω : Config V | Connects ω o y}.indicator
              (fun _ => (1 : ℝ≥0∞)) ω *
              (Percolation.cardFun (cluster ω o) * Percolation.cardFun (cluster ω y))
              ∂(edgeMeasure π) := by
                rw [Hrest.integral_conn_agree o y
                  (fun K => Percolation.cardFun K) (fun K => Percolation.cardFun K)]
        _ = (∫⁻ ω, {ω : Config V | Connects ω o y}.indicator
              (fun _ => (1 : ℝ≥0∞)) ω *
              (Percolation.cardFun (cluster ω o) * Percolation.cardFun (cluster ω y))
              ∂(edgeMeasure π)) +
            ∫⁻ ω, {ω : Config V | ¬ Connects ω o y}.indicator
              (fun _ => (1 : ℝ≥0∞)) ω *
              (Percolation.cardFun (cluster ω o) * Percolation.cardFun (cluster ω y))
              ∂(edgeMeasure π) := add_comm _ _
        _ = ∫⁻ ω, Percolation.cardFun (cluster ω o) *
              Percolation.cardFun (cluster ω y) ∂(edgeMeasure π) :=
                (Hrest.integral_split_conn o y
                  (hm.mul (Hrest.measurable_cardFun_cluster_canonical y))).symm


/-- The real `cE1` bound of Lemma I.4.11, with finiteness premises that make
all real differences and the quotient meaningful. -/

theorem lemma_I_4_11_of_finite {d : ℕ} {J : Sym2 (Fin d → ℤ) → ℝ}
    (hJinv : ∀ (a : Fin d → ℤ) (e : Sym2 (Fin d → ℤ)),
      J (Sym2.map (fun x => x + a) e) = J e)
    (hJ : ∀ e, 0 ≤ J e) (β : NNReal) (B : Finset (Fin d → ℤ)) (hB : B.Nonempty)
    (hAfin : (∑' w : Fin d → ℤ, twoPointFunction J hJ β 0 w) ≠ ∞)
    (hJfin : (∫⁻ ω, Percolation.cardFun (cluster ω 0) *
        ∑ y ∈ B, Percolation.cardFun (cluster ω y)
          ∂(longRangeMeasure J hJ β)) ≠ ∞)
    (hDfin : (∑ y ∈ B, ∑' a : Fin d → ℤ, ∑' b : Fin d → ℤ,
        twoPointFunction J hJ β 0 a * twoPointFunction J hJ β a b *
          twoPointFunction J hJ β b y) ≠ ∞) :
    let A : ℝ≥0∞ := ∫⁻ ω, clusterVol ω 0 ∂(longRangeMeasure J hJ β)
    let Jm : ℝ≥0∞ := ∫⁻ ω, Percolation.cardFun (cluster ω 0) *
      ∑ y ∈ B, Percolation.cardFun (cluster ω y) ∂(longRangeMeasure J hJ β)
    let T : ℝ≥0∞ := ∫⁻ ω, ((B.filter fun y => y ∈ cluster ω 0).card : ℝ≥0∞) *
      (Percolation.cardFun (cluster ω 0) * Percolation.cardFun (cluster ω 0))
      ∂(longRangeMeasure J hJ β)
    VolumeMoments.cE1 A.toReal Jm.toReal T.toReal B.card ≤
      (B.card : ℝ)⁻¹ * (∑ y ∈ B, ∑' a : Fin d → ℤ, ∑' b : Fin d → ℤ,
        twoPointFunction J hJ β 0 a * twoPointFunction J hJ β a b *
          twoPointFunction J hJ β b y).toReal := by
  let A : ℝ≥0∞ := ∫⁻ ω, clusterVol ω 0 ∂(longRangeMeasure J hJ β)
  let T : ℝ≥0∞ := ∫⁻ ω, ((B.filter fun y => y ∈ cluster ω 0).card : ℝ≥0∞) *
    (Percolation.cardFun (cluster ω 0) * Percolation.cardFun (cluster ω 0))
    ∂(longRangeMeasure J hJ β)
  let D : ℝ≥0∞ := ∑ y ∈ B, ∑' a : Fin d → ℤ, ∑' b : Fin d → ℤ,
    twoPointFunction J hJ β 0 a * twoPointFunction J hJ β a b *
      twoPointFunction J hJ β b y
  have hA : A = ∑' w : Fin d → ℤ, twoPointFunction J hJ β 0 w :=
    lintegral_clusterVol_eq_tsum_twoPoint hJ β 0
  have hAne : A ≠ ∞ := by rw [hA]; exact hAfin
  have hDne : D ≠ ∞ := hDfin
  have hsplit := joint_eq_excluded_add_windowMoment
    (bernoulliEdgeProb J hJ β) (0 : Fin d → ℤ) B
  have hsplit' : exclMoment (bernoulliEdgeProb J hJ β) 0 B + T =
      ∫⁻ ω, Percolation.cardFun (cluster ω 0) *
        ∑ y ∈ B, Percolation.cardFun (cluster ω y) ∂(longRangeMeasure J hJ β) := by
    simpa only [T, longRangeMeasure] using hsplit
  have hexcl : exclMoment (bernoulliEdgeProb J hJ β) 0 B ≠ ∞ := by
    refine ne_top_of_le_ne_top hJfin ?_
    rw [← hsplit']
    exact self_le_add_right _ _
  have hTne : T ≠ ∞ := by
    refine ne_top_of_le_ne_top hJfin ?_
    rw [← hsplit']
    exact self_le_add_left _ _
  have hadd : A ^ 2 * D ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.pow_ne_top hAne) hDne
  have hI := I411_subtracted_display hJinv hJ β B
  rw [← hA] at hI
  change (B.card : ℝ≥0∞) * (A * A) - exclMoment (bernoulliEdgeProb J hJ β) 0 B
    ≤ (A * A) * D at hI
  have hreal : (B.card : ℝ) * A.toReal ^ 2 -
      (exclMoment (bernoulliEdgeProb J hJ β) 0 B).toReal ≤
      A.toReal ^ 2 * D.toReal := by
    have h₀ := (ENNReal.le_toReal_sub hexcl).trans
      (ENNReal.toReal_mono hadd (by simpa [sq] using hI))
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast, pow_two] using h₀
  have hJr : (∫⁻ ω, Percolation.cardFun (cluster ω 0) *
      ∑ y ∈ B, Percolation.cardFun (cluster ω y)
      ∂(longRangeMeasure J hJ β)).toReal =
        (exclMoment (bernoulliEdgeProb J hJ β) 0 B).toReal + T.toReal := by
    rw [← hsplit', ENNReal.toReal_add hexcl hTne]
  have hA1 : 1 ≤ A := by
    simpa only [A, longRangeMeasure, Percolation.cardFun_eq_encard] using
      (Hrest.one_le_lintegral_cardFun (π := bernoulliEdgeProb J hJ β) 0)
  have hApos : 0 < A.toReal :=
    ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans_le hA1)) hAne
  have hb : 0 < (B.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hB
  have hden : 0 < (B.card : ℝ) * A.toReal ^ 2 := mul_pos hb (sq_pos_of_pos hApos)
  apply (div_le_iff₀ hden).2
  change (B.card : ℝ) * A.toReal ^ 2 -
      (∫⁻ ω, Percolation.cardFun (cluster ω 0) *
        ∑ y ∈ B, Percolation.cardFun (cluster ω y)
        ∂(longRangeMeasure J hJ β)).toReal + T.toReal ≤
    ((B.card : ℝ)⁻¹ * D.toReal) * ((B.card : ℝ) * A.toReal ^ 2)
  calc
    _ ≤ A.toReal ^ 2 * D.toReal := by rw [hJr]; linarith
    _ = ((B.card : ℝ)⁻¹ * D.toReal) * ((B.card : ℝ) * A.toReal ^ 2) := by
      field_simp [hb.ne', hApos.ne']

end PercLib.CriticalLRP.I411
