/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Upper-tail ingredients for Proposition I.3.1(2)

The ghost conversion, size-biased exponential split, restoration correction,
and percolation upper-tail bound from a doubling inverse scale. Only the real
restoration comparison is used: the invalid degree-tail-only shortcut is not.
-/

module

public import PercLib.CriticalLRP.Analysis.VolumeTailModel
public import PercLib.CriticalLRP.Analysis.VolumeTailLower
public import PercLib.CriticalLRP.Analysis.PercolationI32

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

open PercLib.CriticalLRP

/-- The ghost/indicator lower bound written directly for the volume law:
`(1-e⁻¹) P(X ≥ n) ≤ E[1-e^(-X/n)]`. -/
theorem one_sub_exp_neg_one_mul_tail_le_lapDefect {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hmu : μ (Iio 0) = 0) {n : ℝ} (hn : 1 ≤ n) :
    (1 - Real.exp (-1)) * (μ (Ici n)).toReal ≤ lapDefect μ (1 / n) := by
  have hnpos : 0 < n := one_pos.trans_le hn
  have hInt : Integrable (fun x : ℝ => 1 - Real.exp (-(1 / n * x))) μ := by
    apply Integrable.of_bound (by fun_prop) 2
    filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hmu] with x hx
    simp only [mem_compl_iff, mem_Iio, not_lt] at hx
    have hm : 0 ≤ (1 / n) * x := mul_nonneg (by positivity) hx
    have he : Real.exp (-(1 / n * x)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr he)]
    have hexp : 0 < Real.exp (-(1 / n * x)) := Real.exp_pos _
    linarith
  have hnn : 0 ≤ᵐ[μ] fun x : ℝ => 1 - Real.exp (-(1 / n * x)) := by
    filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hmu] with x hx
    simp only [mem_compl_iff, mem_Iio, not_lt] at hx
    have hm : 0 ≤ (1 / n) * x := mul_nonneg (by positivity) hx
    have he : Real.exp (-(1 / n * x)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith
    exact sub_nonneg.mpr he
  have hband : (1 - Real.exp (-1)) * (μ (Ici n)).toReal ≤
      ∫ x in Ici n, (1 - Real.exp (-(1 / n * x))) ∂μ := by
    calc
      (1 - Real.exp (-1)) * (μ (Ici n)).toReal =
          ∫ _x in Ici n, (1 - Real.exp (-1)) ∂μ := by
        simp [Measure.real, mul_comm]
      _ ≤ ∫ x in Ici n, (1 - Real.exp (-(1 / n * x))) ∂μ := by
        apply setIntegral_mono_on integrableOn_const hInt.restrict measurableSet_Ici
        intro x hx
        have hx' : n ≤ x := hx
        have hxprod : 1 ≤ (1 / n) * x := by
          calc
            1 = (1 / n) * n := by field_simp
            _ ≤ (1 / n) * x := mul_le_mul_of_nonneg_left hx' (by positivity)
        have hexp : Real.exp (-(1 / n * x)) ≤ Real.exp (-1) := by
          apply Real.exp_le_exp.mpr
          linarith
        linarith
  calc
    (1 - Real.exp (-1)) * (μ (Ici n)).toReal ≤
        ∫ x in Ici n, (1 - Real.exp (-(1 / n * x))) ∂μ := hband
    _ ≤ (∫ x in Ici n, (1 - Real.exp (-(1 / n * x))) ∂μ) +
        ∫ x in (Ici n)ᶜ, (1 - Real.exp (-(1 / n * x))) ∂μ := by
      apply le_add_of_nonneg_right
      exact integral_nonneg_of_ae (ae_restrict_of_ae hnn)
    _ = lapDefect μ (1 / n) := by
      rw [lapDefect]
      exact integral_add_compl measurableSet_Ici hInt

/-- Dividing by the positive constant `1-e⁻¹` gives the tail estimate used at
the end of the upper-half proof of Proposition I.3.1. -/
theorem tail_toReal_le_lapDefect_div_one_sub_exp_neg_one
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hmu : μ (Iio 0) = 0) {n : ℝ} (hn : 1 ≤ n) :
    (μ (Ici n)).toReal ≤ lapDefect μ (1 / n) / (1 - Real.exp (-1)) := by
  have hpos : 0 < 1 - Real.exp (-1) := by
    have hexp : Real.exp (-1) < 1 := by
      rw [Real.exp_lt_one_iff]
      norm_num
    linarith
  apply (le_div_iff₀ hpos).2
  simpa only [mul_comm] using one_sub_exp_neg_one_mul_tail_le_lapDefect hmu hn


/-- Splitting an exponential moment across the threshold `A/h` gives
`ν(Iic (A/h)) + exp(-A)`. -/
theorem integral_exp_neg_le_Iic_add_exp {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : ν (Iio 0) = 0) {A h : ℝ} (hA : 0 < A) (hh : 0 < h) :
    (∫ x, Real.exp (-(h * x)) ∂ν) ≤ (ν (Iic (A / h))).toReal + Real.exp (-A) := by
  have hInt : Integrable (fun x : ℝ => Real.exp (-(h * x))) ν := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hν] with x hx
    simp only [mem_compl_iff, mem_Iio, not_lt] at hx
    have hm : 0 ≤ h * x := mul_nonneg hh.le hx
    have he : Real.exp (-(h * x)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact he
  have hlow : (∫ x in Iic (A / h), Real.exp (-(h * x)) ∂ν) ≤
      (ν (Iic (A / h))).toReal := by
    calc
      (∫ x in Iic (A / h), Real.exp (-(h * x)) ∂ν) ≤
          ∫ _x in Iic (A / h), (1 : ℝ) ∂ν := by
        apply setIntegral_mono_ae hInt.restrict integrableOn_const
        filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hν] with x hx
        simp only [mem_compl_iff, mem_Iio, not_lt] at hx
        have hm : 0 ≤ h * x := mul_nonneg hh.le hx
        rw [Real.exp_le_one_iff]
        linarith
      _ = (ν (Iic (A / h))).toReal := by simp [Measure.real]
  have hhigh : (∫ x in (Iic (A / h))ᶜ, Real.exp (-(h * x)) ∂ν) ≤ Real.exp (-A) := by
    calc
      (∫ x in (Iic (A / h))ᶜ, Real.exp (-(h * x)) ∂ν) ≤
          ∫ _x in (Iic (A / h))ᶜ, Real.exp (-A) ∂ν := by
        apply setIntegral_mono_on hInt.restrict integrableOn_const measurableSet_Iic.compl
        intro x hx
        have hx' : A / h < x := by simpa only [mem_compl_iff, mem_Iic, not_le] using hx
        have hAx : A ≤ x * h := (div_lt_iff₀ hh).mp hx' |>.le
        have hAx' : A ≤ h * x := by simpa only [mul_comm] using hAx
        exact Real.exp_le_exp.mpr (by linarith)
      _ = (ν (Iic (A / h))ᶜ).toReal * Real.exp (-A) := by
        simp [Measure.real]
      _ ≤ Real.exp (-A) := by
        have hp := measureReal_le_one (μ := ν) (s := (Iic (A / h))ᶜ)
        exact mul_le_of_le_one_left (Real.exp_pos _).le hp
  calc
    (∫ x, Real.exp (-(h * x)) ∂ν) =
        (∫ x in Iic (A / h), Real.exp (-(h * x)) ∂ν) +
          ∫ x in (Iic (A / h))ᶜ, Real.exp (-(h * x)) ∂ν :=
      (integral_add_compl measurableSet_Iic hInt).symm
    _ ≤ (ν (Iic (A / h))).toReal + Real.exp (-A) := add_le_add hlow hhigh


/-- The usual `1 - exp(-h x) ≤ h x` estimate for a volume law. -/
theorem lapDefect_le_mul_mean {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hν : μ (Iio 0) = 0) {h : ℝ} (hh : 0 < h)
    (hint : Integrable (fun x : ℝ => x) μ) :
    lapDefect μ h ≤ h * mean μ := by
  have hInt : Integrable (fun x : ℝ => 1 - Real.exp (-(h * x))) μ := by
    apply Integrable.of_bound (by fun_prop) 2
    filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hν] with x hx
    simp only [mem_compl_iff, mem_Iio, not_lt] at hx
    have hm : 0 ≤ h * x := mul_nonneg hh.le hx
    have he : Real.exp (-(h * x)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr he)]
    have hepos : 0 < Real.exp (-(h * x)) := Real.exp_pos _
    linarith
  have hmono : ∀ᵐ x ∂μ, (1 - Real.exp (-(h * x))) ≤ h * x := by
    filter_upwards with x
    have he := Real.add_one_le_exp (-(h * x))
    linarith
  calc
    lapDefect μ h = ∫ x, (1 - Real.exp (-(h * x))) ∂μ := rfl
    _ ≤ ∫ x, h * x ∂μ := by
      apply integral_mono_ae hInt (hint.const_mul h) hmono
    _ = h * mean μ := by rw [integral_const_mul, mean]


/-- Factor an exponentially damped first moment through the unscaled
size-biased law. -/
theorem integral_mul_exp_eq_mean_mul_integral_sizeBiasedBaseLaw
    {μ : Measure ℝ} (hμ : μ (Iio 0) = 0) (hpos : 0 < mean μ) (h : ℝ) :
    (∫ x, x * Real.exp (-(h * x)) ∂μ) =
      mean μ * ∫ x, Real.exp (-(h * x)) ∂sizeBiasedBaseLaw μ := by
  unfold sizeBiasedBaseLaw
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)
    (fun x => Real.exp (-(h * x)))]
  rw [← integral_const_mul]
  simp only [smul_eq_mul]
  apply integral_congr_ae
  filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hμ] with x hx
  simp only [mem_compl_iff, mem_Iio, not_lt] at hx
  rw [ENNReal.toReal_ofReal (div_nonneg hx hpos.le)]
  field_simp


/-- A small lower-tail event and an exponential tail make the restoration
correction at most `1/4`. -/
theorem restoration_error_le_quarter
    {μ : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure (sizeBiasedBaseLaw μ)]
    {f : ℝ → ℝ} {r A δ h B C α : ℝ}
    (hμ : μ (Iio 0) = 0) (hpos : 0 < mean μ)
    (hr : 1 ≤ r) (hB : 0 < B) (hC : 0 < C) (hα : 0 < α)
    (hmean : mean μ ≤ B * r ^ α) (hfδ : 0 < δ * f r)
    (hA : 0 < A) (hh : 0 < h) (hhrel : A ≤ h * (δ * f r))
    (hband : (sizeBiasedBaseLaw μ (Iic (δ * f r))).toReal ≤ 1 / (8 * max 1 (B * C)))
    (hexp : Real.exp (-A) ≤ 1 / (8 * max 1 (B * C))) :
    C * r ^ (-α) * (∫ x, x * Real.exp (-(h * x)) ∂μ) ≤ 1 / 4  := by
  have hrpos : 0 < r := one_pos.trans_le hr
  have hM : 0 < max 1 (B * C) := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hthreshold : A / h ≤ δ * f r := by
    apply (div_le_iff₀ hh).2
    simpa only [mul_comm] using hhrel
  have hsub : Iic (A / h) ⊆ Iic (δ * f r) := by
    intro x hx
    exact hx.trans hthreshold
  have hcdf : (sizeBiasedBaseLaw μ (Iic (A / h))).toReal ≤ 1 / (8 * max 1 (B * C)) :=
    (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)).trans hband
  have hbasezero : sizeBiasedBaseLaw μ (Iio 0) = 0 := by
    unfold sizeBiasedBaseLaw
    rw [MeasureTheory.withDensity_apply _ measurableSet_Iio]
    show (∫⁻ _x, ENNReal.ofReal _ ∂(μ.restrict (Iio 0))) = 0
    rw [Measure.restrict_eq_zero.mpr hμ]
    simp
  have hexp_bound : (∫ x, Real.exp (-(h * x)) ∂sizeBiasedBaseLaw μ) ≤
      1 / (4 * max 1 (B * C)) := by
    calc
      (∫ x, Real.exp (-(h * x)) ∂sizeBiasedBaseLaw μ) ≤
          (sizeBiasedBaseLaw μ (Iic (A / h))).toReal + Real.exp (-A) :=
        integral_exp_neg_le_Iic_add_exp (ν := sizeBiasedBaseLaw μ) hbasezero hA hh
      _ ≤ 1 / (8 * max 1 (B * C)) + 1 / (8 * max 1 (B * C)) :=
        add_le_add hcdf hexp
      _ = 1 / (4 * max 1 (B * C)) := by ring
  have hexp_nonneg : 0 ≤ ∫ x, Real.exp (-(h * x)) ∂sizeBiasedBaseLaw μ :=
    integral_nonneg fun x => (Real.exp_pos _).le
  have hcfac : 0 ≤ C * r ^ (-α) :=
    mul_nonneg hC.le (Real.rpow_nonneg hrpos.le (-α))
  rw [integral_mul_exp_eq_mean_mul_integral_sizeBiasedBaseLaw hμ hpos h]
  calc
    C * r ^ (-α) * (mean μ * ∫ x, Real.exp (-(h * x)) ∂sizeBiasedBaseLaw μ) ≤
        C * r ^ (-α) * ((B * r ^ α) * ∫ x, Real.exp (-(h * x)) ∂sizeBiasedBaseLaw μ) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmean hexp_nonneg) hcfac
    _ = (B * C) * ∫ x, Real.exp (-(h * x)) ∂sizeBiasedBaseLaw μ := by
      have hsplit : r ^ (-α) * r ^ α = 1 := by
        rw [← Real.rpow_add hrpos]
        simp
      rw [show C * r ^ (-α) * ((B * r ^ α) * ∫ x, Real.exp (-(h * x)) ∂sizeBiasedBaseLaw μ) =
        (B * C) * ((r ^ (-α) * r ^ α) * ∫ x, Real.exp (-(h * x)) ∂sizeBiasedBaseLaw μ) by ring]
      rw [hsplit]
      simp
    _ ≤ (B * C) * (1 / (4 * max 1 (B * C))) :=
      mul_le_mul_of_nonneg_left hexp_bound (mul_nonneg hB.le hC.le)
    _ ≤ max 1 (B * C) * (1 / (4 * max 1 (B * C))) := by
      apply mul_le_mul_of_nonneg_right (le_max_right _ _)
      positivity
    _ = 1 / 4 := by field_simp [hM.ne']



/-- The full-law Laplace bound obtained when the restoration coefficient is
below one quarter. -/
theorem laplace_le_two_mul_mean_of_restoration
    {V : Type*} [Countable V] {π ρ : Sym2 V → unitInterval} {o : V}
    {f : ℝ → ℝ} {r A δ B C α : ℝ} {h : NNReal}
    (hρπ : ∀ e, ρ e ≤ π e)
    (hpos : 0 < mean (volumeLaw ρ o))
    (hfinρ : ∀ᵐ ω ∂edgeMeasure ρ, clusterVol ω o ≠ ⊤)
    (hfinπ : ∀ᵐ ω ∂edgeMeasure π, clusterVol ω o ≠ ⊤)
    (hintWeight : Integrable (fun ω : Config V =>
      (clusterVol ω o).toReal * Real.exp (-(h : ℝ) * (clusterVol ω o).toReal))
      (edgeMeasure ρ))
    (hD : ∀ x : V, (∑' y : V, ENNReal.ofReal ((shiftProb π ρ (s(x, y)) : unitInterval) : ℝ))
      ≤ ENNReal.ofReal (C * r ^ (-α)))
    (hG : ∀ y : V, ghostHits π h y ≤ ghostHits π h o)
    (hL1 : Integrable (fun x : ℝ => x) (volumeLaw ρ o))
    (hr : 1 ≤ r) (hB : 0 < B) (hC : 0 < C) (hα : 0 < α)
    (hmean : mean (volumeLaw ρ o) ≤ B * r ^ α) (hfδ : 0 < δ * f r)
    (hA : 0 < A) (hh : 0 < h) (hhrel : A ≤ (h : ℝ) * (δ * f r))
    (hband : (sizeBiasedBaseLaw (volumeLaw ρ o) (Iic (δ * f r))).toReal ≤
      1 / (8 * max 1 (B * C)))
    (hexp : Real.exp (-A) ≤ 1 / (8 * max 1 (B * C))) :
    lapDefect (volumeLaw π o) (h : ℝ) ≤ 2 * B * (h : ℝ) * r ^ α := by
  let : IsProbabilityMeasure (volumeLaw ρ o) := isProbabilityMeasure_volumeLaw ρ o
  let : IsProbabilityMeasure (sizeBiasedBaseLaw (volumeLaw ρ o)) :=
    isProbabilityMeasure_sizeBiasedBaseLaw _ (volumeLaw_Iio_zero ρ o) hL1 hpos
  have herr := restoration_error_le_quarter (μ := volumeLaw ρ o) (volumeLaw_Iio_zero ρ o)
    hpos hr hB hC hα hmean hfδ hA hh hhrel hband hexp
  obtain ⟨_, hrest⟩ := restoration_volumeLaw_of_degree π ρ hρπ o hh
    (one_pos.trans_le hr) hC.le hα.le hfinρ hfinπ hintWeight hD hG
  have hrest' := by simpa only [neg_mul] using hrest
  have hnonneg : 0 ≤ lapDefect (volumeLaw π o) (h : ℝ) :=
    lapDefect_nonneg (volumeLaw_Iio_zero π o) hh
  have hcutnonneg : 0 ≤ lapDefect (volumeLaw ρ o) (h : ℝ) :=
    lapDefect_nonneg (volumeLaw_Iio_zero ρ o) hh
  have hfrac := mul_le_mul_of_nonneg_right (by simpa only [neg_mul] using herr) hnonneg
  have hrest₂ : lapDefect (volumeLaw π o) (h : ℝ) ≤ lapDefect (volumeLaw ρ o) (h : ℝ) +
      (1 / 4 : ℝ) * lapDefect (volumeLaw π o) (h : ℝ) :=
    hrest'.trans (add_le_add_right hfrac _)
  have htwo : lapDefect (volumeLaw π o) (h : ℝ) ≤
      2 * lapDefect (volumeLaw ρ o) (h : ℝ) := by
    nlinarith only [hrest₂, hcutnonneg, hnonneg]
  have hle1 : lapDefect (volumeLaw ρ o) (h : ℝ) ≤ (h : ℝ) * mean (volumeLaw ρ o) :=
    lapDefect_le_mul_mean (volumeLaw_Iio_zero ρ o) hh hL1
  have hle2 : (h : ℝ) * mean (volumeLaw ρ o) ≤ (h : ℝ) * (B * r ^ α) :=
    mul_le_mul_of_nonneg_left hmean hh.le
  have hscaled : 2 * lapDefect (volumeLaw ρ o) (h : ℝ) ≤ 2 * B * (h : ℝ) * r ^ α := by
    nlinarith [hle1, hle2]
  exact htwo.trans hscaled



/-- First-moment domination suffices for integrability of an exponentially
weighted nonnegative random variable with a uniformly positive rate. -/
theorem integrable_mul_exp_of_firstMoment {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : μ (Iio 0) = 0) {h : NNReal} (hh : 0 < h)
    (hint : Integrable (fun x : ℝ => x) μ) :
    Integrable (fun x : ℝ => x * Real.exp (-(h : ℝ) * x)) μ := by
  apply hint.mono' (by fun_prop)
  filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hμ] with x hx
  simp only [mem_compl_iff, mem_Iio, not_lt] at hx
  have hm : 0 ≤ (h : ℝ) * x := mul_nonneg hh.le hx
  have he : Real.exp (-(h : ℝ) * x) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hx (Real.exp_pos _).le)]
  exact mul_le_of_le_one_right hx he

/-- The configuration form of first-moment exponential integrability. -/
theorem integrable_volumeLaw_weighted_config_of_firstMoment
    {V : Type*} [Countable V] (π : Sym2 V → unitInterval) (o : V)
    {h : NNReal} (hh : 0 < h)
    (hint : Integrable (fun x : ℝ => x) (volumeLaw π o)) :
    Integrable (fun ω : Config V =>
      (clusterVol ω o).toReal * Real.exp (-(h : ℝ) * (clusterVol ω o).toReal))
      (edgeMeasure π) := by
  have hm : Measurable (fun ω : Config V => (clusterVol ω o).toReal) :=
    ENNReal.measurable_toReal.comp (measurable_clusterVol o)
  have hg : AEStronglyMeasurable (fun x : ℝ => x * Real.exp (-(h : ℝ) * x))
      (volumeLaw π o) := by fun_prop
  have hb := integrable_mul_exp_of_firstMoment (μ := volumeLaw π o)
    (volumeLaw_Iio_zero π o) hh hint
  have hmapped : Integrable ((fun x : ℝ => x * Real.exp (-(h : ℝ) * x)) ∘
      (fun ω : Config V => (clusterVol ω o).toReal)) (edgeMeasure π) := by
    apply (integrable_map_measure hg hm.aemeasurable).mp
    simpa [volumeLaw] using hb
  exact hmapped


/-- Upper-tail estimate from the size-biased lower-tail hypothesis and a
restored full-law ghost estimate. The inverse scale is doubling, and the
conclusion is supplied on a threshold determined by its normalization. -/
theorem exists_volume_tail_upper_of_inverse_doubling
    {V : Type*} [Countable V]
    {π : ℝ → Sym2 V → unitInterval} {πinf : Sym2 V → unitInterval} {o : V}
    {f g : ℝ → ℝ} {B C D α : ℝ}
    (hρπ : ∀ r e, π r e ≤ πinf e) (hB : 0 < B) (hC : 0 < C) (hα : 0 < α)
    (hfin : ∀ᵐ ω ∂edgeMeasure πinf, clusterVol ω o ≠ ⊤)
    (hEpos : ∀ r : ℝ, 1 ≤ r → 0 < mean (volumeLaw (π r) o))
    (hL1 : ∀ r : ℝ, 1 ≤ r → Integrable (fun x : ℝ => x) (volumeLaw (π r) o))
    (hmean : ∀ r : ℝ, 1 ≤ r → mean (volumeLaw (π r) o) ≤ B * r ^ α)
    (hD : ∀ r : ℝ, 1 ≤ r → ∀ x : V,
      (∑' y : V, ENNReal.ofReal ((shiftProb πinf (π r) (s(x, y)) : unitInterval) : ℝ))
        ≤ ENNReal.ofReal (C * r ^ (-α)))
    (hG : ∀ h : NNReal, ∀ y : V, ghostHits πinf h y ≤ ghostHits πinf h o)
    (hTail : ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 1 ≤ r →
      (sizeBiasedBaseLaw (volumeLaw (π r) o) (Iic (δ * f r))).toReal ≤ η)
    (hf : ∀ r : ℝ, 1 ≤ r → 0 < f r)
    (hgmono : Monotone g) (hgpos : ∀ x : ℝ, 0 < x → 0 < g x)
    (hDbl : 0 < D) (hdouble : ∀ x : ℝ, 1 ≤ x → g (2 * x) ≤ D * g x)
    (hgAtTop : Tendsto g atTop atTop) (hgf : ∀ x : ℝ, 0 < x → f (g x) = x) :
    ∃ N κ : ℝ, 0 < κ ∧
      ∀ n : ℝ, N ≤ n → (volumeLaw πinf o (Ici n)).toReal ≤ κ * (g n) ^ α / n := by
  obtain ⟨δ, hδ, hTailδ⟩ := hTail (1 / (8 * max 1 (B * C))) (by positivity)
  let A := Real.log (8 * max 1 (B * C))
  have hM : 0 < 8 * max 1 (B * C) := by positivity
  have hMgt : 1 < 8 * max 1 (B * C) := by
    have hm : 1 ≤ max 1 (B * C) := le_max_left _ _
    nlinarith
  have hA : 0 < A := Real.log_pos hMgt
  set c := A / δ with hc
  have hcpos : 0 < c := div_pos hA hδ
  obtain ⟨N, K, hK, hscale⟩ := inverse_doubling_scale_of_le_two hgmono hgpos hDbl hcpos hdouble
  have hscaled : Tendsto (fun n : ℝ => g (c * n)) atTop atTop :=
    hgAtTop.comp ((tendsto_const_mul_atTop_of_pos hcpos).mpr tendsto_id)
  have hMnum : 0 < 8 * max 1 (B * C) := hM
  obtain ⟨M, hM⟩ := eventually_atTop.1 (hscaled.eventually (eventually_ge_atTop 1))
  let N₀ := max (N / c) (max M 1)
  let den : ℝ := 1 - Real.exp (-1)
  have hden : 0 < den := by
    dsimp [den]
    have he : Real.exp (-1) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
    linarith
  refine ⟨N₀, 2 * B * K ^ α / (1 - Real.exp (-1)),
    div_pos (mul_pos (by positivity) (Real.rpow_pos_of_pos hK _)) hden, ?_⟩
  intro n hn
  have hnN : N / c ≤ n := by
    dsimp [N₀] at hn
    exact (max_le_iff.mp hn).1
  have hn1 : 1 ≤ n := by
    dsimp [N₀] at hn
    exact (max_le_iff.mp (max_le_iff.mp hn).2).2
  have hnM : M ≤ n := by
    dsimp [N₀] at hn
    exact (max_le_iff.mp (max_le_iff.mp hn).2).1
  have hnpos : 0 < n := one_pos.trans_le hn1
  have hr : 1 ≤ g (c * n) := hM n hnM
  have hrpos : 0 < g (c * n) := one_pos.trans_le hr
  have hfr : f (g (c * n)) = c * n := hgf _ (mul_pos hcpos hnpos)
  let hNN : NNReal := ⟨1 / n, by positivity⟩
  have hh : 0 < hNN := by exact div_pos zero_lt_one hnpos
  have hexpA : Real.exp (-A) ≤ 1 / (8 * max 1 (B * C)) := by
    dsimp [A]
    norm_num [Real.exp_neg, Real.exp_log hMnum, one_div]

  have hL : lapDefect (volumeLaw πinf o) (hNN : ℝ) ≤
      2 * B * (hNN : ℝ) * (g (c * n)) ^ α :=
    laplace_le_two_mul_mean_of_restoration (V := V) (π := πinf) (ρ := π (g (c * n)))
      (o := o) (f := f) (r := g (c * n)) (A := A) (δ := δ) (B := B) (C := C) (α := α)
      (h := hNN) (hρπ _) (hEpos _ hr)
      (ae_finite_of_volumeLaw_mono (hρπ _) o hfin) hfin
      (integrable_volumeLaw_weighted_config_of_firstMoment _ _ hh (hL1 _ hr))
      (hD _ hr) (hG hNN) (hL1 _ hr) hr hB hC hα (hmean _ hr)
      (mul_pos hδ (hf _ hr)) hA hh
      (by
        rw [hfr, hc, show ((hNN : NNReal) : ℝ) = 1 / n from rfl]
        dsimp [A]
        field_simp [hδ.ne', hnpos.ne'] ; rfl)
      (hTailδ _ hr)
      hexpA
  have htailL := tail_toReal_le_lapDefect_div_one_sub_exp_neg_one
    (volumeLaw_Iio_zero πinf o) (n := n) hn1
  have htail' : (volumeLaw πinf o (Ici n)).toReal ≤ lapDefect (volumeLaw πinf o) (1 / n) / den := by
    have hce : ((hNN : ℝ) : ℝ) = 1 / n := rfl
    simpa only [hce] using htailL
  have heq : lapDefect (volumeLaw πinf o) (1 / n) ≤
      2 * B * (1 / n) * (g (c * n)) ^ α := by
    simpa only [show ((hNN : NNReal) : ℝ) = 1 / n from rfl] using hL
  have hcn : N ≤ c * n := by
    have h' : N ≤ n * c := (div_le_iff₀ hcpos).mp hnN
    simpa only [mul_comm] using h'
  have hsp : g (c * n) ≤ K * g n := by
    simpa only [mul_div_cancel_left₀ n hcpos.ne'] using hscale (c * n) hcn
  have hfinal : (volumeLaw πinf o (Ici n)).toReal ≤
      2 * B * K ^ α / den * (g n) ^ α / n := by
    have hsppow : (g (c * n)) ^ α ≤ (K * g n) ^ α :=
      Real.rpow_le_rpow (hgpos _ (mul_pos hcpos hnpos)).le hsp hα.le
    calc
      (volumeLaw πinf o (Ici n)).toReal ≤ lapDefect (volumeLaw πinf o) (1 / n) / den := htail'
      _ ≤ (2 * B * (1 / n) * (g (c * n)) ^ α) / den :=
        div_le_div_of_nonneg_right heq hden.le
      _ = (2 * B / den) * ((g (c * n)) ^ α / n) := by ring
      _ ≤ (2 * B / den) * ((K * g n) ^ α / n) := by
        have hp : 0 ≤ 2 * B / den := by positivity
        exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsppow hnpos.le) hp
      _ = 2 * B * K ^ α / den * (g n) ^ α / n := by
        rw [Real.mul_rpow hK.le (hgpos n hnpos).le]
        ring
  exact hfinal

end PercLib.CriticalLRP.Analysis.I32

#print axioms PercLib.CriticalLRP.Analysis.I32.one_sub_exp_neg_one_mul_tail_le_lapDefect
#print axioms PercLib.CriticalLRP.Analysis.I32.tail_toReal_le_lapDefect_div_one_sub_exp_neg_one

#print axioms PercLib.CriticalLRP.Analysis.I32.integral_exp_neg_le_Iic_add_exp

#print axioms PercLib.CriticalLRP.Analysis.I32.lapDefect_le_mul_mean

#print axioms PercLib.CriticalLRP.Analysis.I32.integral_mul_exp_eq_mean_mul_integral_sizeBiasedBaseLaw

#print axioms PercLib.CriticalLRP.Analysis.I32.restoration_error_le_quarter

#print axioms PercLib.CriticalLRP.Analysis.I32.laplace_le_two_mul_mean_of_restoration

#print axioms PercLib.CriticalLRP.Analysis.I32.integrable_mul_exp_of_firstMoment
#print axioms PercLib.CriticalLRP.Analysis.I32.integrable_volumeLaw_weighted_config_of_firstMoment

#print axioms PercLib.CriticalLRP.Analysis.I32.exists_volume_tail_upper_of_inverse_doubling