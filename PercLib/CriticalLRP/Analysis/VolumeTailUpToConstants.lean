/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Unscaled size-biasing and the lower-tail band reduction

Ingredients for Proposition I.3.1(1) of Hutchcroft, *Critical long-range
percolation I* (arXiv:2508.18807v1, pp. 28-29).

`sizeBiasedBaseLaw` is the unscaled size-biased law `Phat`, unlike
`sizeBiasedLaw`, which additionally rescales its values to form `Q_r`.
The module proves the exact tail / inverse-moment identity and the band
estimate used before choosing `r = f⁻¹(n/c)` in the lower-tail argument.

Scope: the inverse/doubling scale bookkeeping and full-law percolation tail
comparison are not assembled here. Proposition I.3.1(2), whose proof uses the
ghost/restoration estimate (I.3.1), is not claimed at all.
-/

module

public import PercLib.CriticalLRP.Analysis.SizeBiasedMGF

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open Filter Set MeasureTheory
open scoped ENNReal Topology

namespace PercLib.CriticalLRP.Analysis.I32

/-- Unscaled size-biasing: the paper's `Phat` before the additional division by
`Ehat |K|` used to construct `Q_r`. -/
noncomputable def sizeBiasedBaseLaw (mu : Measure ℝ) : Measure ℝ :=
  mu.withDensity fun x => ENNReal.ofReal (x / mean mu)

theorem isProbabilityMeasure_sizeBiasedBaseLaw (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hmu : mu (Iio 0) = 0) (hint : Integrable (fun x : ℝ => x) mu) (hpos : 0 < mean mu) :
    IsProbabilityMeasure (sizeBiasedBaseLaw mu) := by
  constructor
  unfold sizeBiasedBaseLaw
  rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ]
  have hnn : 0 ≤ᵐ[mu] fun x : ℝ => x / mean mu := by
    filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hmu] with x hx
    simp only [mem_compl_iff, mem_Iio, not_lt] at hx
    exact div_nonneg hx hpos.le
  have hint' : Integrable (fun x : ℝ => x / mean mu) mu := hint.div_const _
  have hof := ofReal_integral_eq_lintegral_ofReal hint' hnn
  rw [Measure.restrict_univ, ← hof, integral_div]
  show ENNReal.ofReal (mean mu / mean mu) = 1
  rw [div_self hpos.ne', ENNReal.ofReal_one]

/-- Exact inverse-moment form of a cluster-volume tail under unscaled size-biasing. -/
theorem tail_toReal_eq_mean_mul_integral_sizeBiasedBaseLaw {mu : Measure ℝ}
    (hpos : 0 < mean mu) {n : ℝ} (hn : 1 ≤ n) :
    (mu (Ici n)).toReal = mean mu * ∫ x in Ici n, x⁻¹ ∂sizeBiasedBaseLaw mu := by
  unfold sizeBiasedBaseLaw
  rw [MeasureTheory.restrict_withDensity measurableSet_Ici]
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top) (fun x => x⁻¹)]
  rw [← integral_const_mul]
  change mu.real (Ici n) = _
  simp only [smul_eq_mul]
  calc
    mu.real (Ici n) = ∫ _x in Ici n, (1 : ℝ) ∂mu := by simp
    _ = ∫ x in Ici n, mean mu * ((ENNReal.ofReal (x / mean mu)).toReal * x⁻¹) ∂mu := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
      have hx1 : 1 ≤ x := hn.trans hx
      have hxpos : 0 < x := one_pos.trans_le hx1
      rw [ENNReal.toReal_ofReal (div_nonneg hxpos.le hpos.le)]
      field_simp


/-- Restricting the inverse moment to a finite band gives the lower
factor `Phat [a,b] / b`. -/
theorem band_toReal_div_le_integral_inv_sizeBiasedBaseLaw {mu : Measure ℝ}
    [IsProbabilityMeasure (sizeBiasedBaseLaw mu)] {n a b : ℝ}
    (hn : 1 ≤ n) (hna : n ≤ a) (hab : a ≤ b) :
    (sizeBiasedBaseLaw mu (Icc a b)).toReal / b ≤
      ∫ x in Ici n, x⁻¹ ∂sizeBiasedBaseLaw mu := by
  have ha : 0 < a := one_pos.trans_le (hn.trans hna)
  have hb : 0 < b := ha.trans_le hab
  have hsub : Icc a b ⊆ Ici n := fun x hx => hna.trans hx.1
  have hInt : IntegrableOn (fun x : ℝ => x⁻¹) (Ici n) (sizeBiasedBaseLaw mu) := by
    apply IntegrableOn.of_bound (measure_lt_top _ _) (by fun_prop) (n⁻¹)
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
    have hxpos : 0 < x := one_pos.trans_le (hn.trans hx)
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hxpos)]
    simpa only [one_div] using one_div_le_one_div_of_le (one_pos.trans_le hn) hx
  have htail : (∫ x in Icc a b, x⁻¹ ∂sizeBiasedBaseLaw mu) ≤
      ∫ x in Ici n, x⁻¹ ∂sizeBiasedBaseLaw mu := by
    apply setIntegral_mono_set hInt ?_ (Filter.Eventually.of_forall hsub)
    filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
    exact inv_nonneg.mpr (zero_le_one.trans (hn.trans hx))
  have hbandInt : IntegrableOn (fun x : ℝ => x⁻¹) (Icc a b) (sizeBiasedBaseLaw mu) :=
    hInt.mono_set hsub
  calc
    (sizeBiasedBaseLaw mu (Icc a b)).toReal / b =
        ∫ _x in Icc a b, b⁻¹ ∂sizeBiasedBaseLaw mu := by
      simp [Measure.real, div_eq_mul_inv, mul_comm]
    _ ≤ ∫ x in Icc a b, x⁻¹ ∂sizeBiasedBaseLaw mu := by
      apply setIntegral_mono_on integrableOn_const hbandInt measurableSet_Icc
      intro x hx
      simpa only [one_div] using one_div_le_one_div_of_le (ha.trans_le hx.1) hx.2
    _ ≤ ∫ x in Ici n, x⁻¹ ∂sizeBiasedBaseLaw mu := htail


/-- The tail is bounded below by the mean times the normalized band mass.
This is the per-scale inequality used in the proof of Proposition I.3.1(1). -/
theorem mean_mul_band_prob_div_le_tail_toReal {mu : Measure ℝ}
    [IsProbabilityMeasure (sizeBiasedBaseLaw mu)] {n a b : ℝ}
    (hpos : 0 < mean mu) (hn : 1 ≤ n) (hna : n ≤ a) (hab : a ≤ b) :
    mean mu * ((sizeBiasedBaseLaw mu (Icc a b)).toReal / b) ≤ (mu (Ici n)).toReal := by
  rw [tail_toReal_eq_mean_mul_integral_sizeBiasedBaseLaw hpos hn]
  exact mul_le_mul_of_nonneg_left (band_toReal_div_le_integral_inv_sizeBiasedBaseLaw hn hna hab)
    hpos.le

/-- The same estimate after inserting a uniform lower bound on the
size-biased probability of the band. -/
theorem mean_mul_probLower_div_le_tail_toReal {mu : Measure ℝ}
    [IsProbabilityMeasure (sizeBiasedBaseLaw mu)] {n a b q : ℝ}
    (hpos : 0 < mean mu) (hq : q ≤ (sizeBiasedBaseLaw mu (Icc a b)).toReal)
    (hb : 0 < b) (hn : 1 ≤ n) (hna : n ≤ a) (hab : a ≤ b) :
    mean mu * (q / b) ≤ (mu (Ici n)).toReal := by
  calc
    mean mu * (q / b) ≤ mean mu * ((sizeBiasedBaseLaw mu (Icc a b)).toReal / b) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hq hb.le) hpos.le
    _ ≤ (mu (Ici n)).toReal := mean_mul_band_prob_div_le_tail_toReal hpos hn hna hab

end PercLib.CriticalLRP.Analysis.I32

#print axioms PercLib.CriticalLRP.Analysis.I32.sizeBiasedBaseLaw
#print axioms PercLib.CriticalLRP.Analysis.I32.isProbabilityMeasure_sizeBiasedBaseLaw
#print axioms PercLib.CriticalLRP.Analysis.I32.tail_toReal_eq_mean_mul_integral_sizeBiasedBaseLaw
#print axioms PercLib.CriticalLRP.Analysis.I32.band_toReal_div_le_integral_inv_sizeBiasedBaseLaw
#print axioms PercLib.CriticalLRP.Analysis.I32.mean_mul_band_prob_div_le_tail_toReal
#print axioms PercLib.CriticalLRP.Analysis.I32.mean_mul_probLower_div_le_tail_toReal
