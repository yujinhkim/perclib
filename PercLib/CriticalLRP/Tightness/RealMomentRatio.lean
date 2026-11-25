/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Corollary I.2.5 of arXiv:2508.18807v1 for real exponents

Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Corollary I.2.5 states: for a weighted graph `G = (V,E,J)`, every
`p, q ≥ 0`, `β ≥ 0`, `x ∈ V` and finite `W ⊆ V`,

  `E_β |K_x ∩ W|^{p+q} ⪯_{p,q} M_β(W)^q E_β |K_x ∩ W|^p`,

where `M_β(W)` is the *edian* `min{n ≥ 0 : P_β(|K_max(W)| ≥ n) ≤ e^{-1}}` of the maximum
cluster size, and the single input is the exponential tail estimate (I.2.6) of the universal
tightness theorem I.2.3.

The paper proves this by the integration-by-parts ("layer cake") formula

  `E X^r = r ∫_0^∞ t^{r-1} P(X ≥ t) dt`

(section I.2.1) and the change of variables `s = t/9M`.  The existing project file
`Tightness/MomentRatio.lean` proves the *integer* case `p ≥ 1, q ≥ 0` by a discrete layer cake.
This file proves the statement for **real** exponents `p > 0`, `q ≥ 0` -- the form in which the
paper actually states and uses the corollary -- using Mathlib's continuous layer cake
`MeasureTheory.lintegral_rpow_eq_lintegral_meas_le_mul`, with the explicit constant
`momentConstR p q = (p+q)/p + e (p+q) 9^{p+q} Γ(p+q)`.

The only hypothesis beyond measurability is the exponential tail (I.2.6) above the scale `M`;
everything else (the layer cake, the Gamma integral `∫_M^∞ t^{r-1} e^{-t/9M} dt ≤ (9M)^r Γ(r)`,
the moment bookkeeping) is proved here.  In particular no probability hypothesis on `μ` is used:
the inequality is homogeneous in `μ`.
-/
module

public import Mathlib

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Tightness

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The explicit constant -/

/-- The explicit constant `C(p,q) = (p+q)/p + e (p+q) 9^{p+q} Γ(p+q)` in the real-exponent
moment ratio.  The two summands are the contributions of the "lower" part `t ≤ M` and the
"upper" part `t > M` of the layer cake integral respectively. -/
noncomputable def momentConstR (p q : ℝ) : ℝ :=
  (p + q) / p + Real.exp 1 * (p + q) * 9 ^ (p + q) * Real.Gamma (p + q)

lemma momentConstR_pos {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) : 0 < momentConstR p q := by
  have h1 : 0 < (p + q) / p := div_pos (by linarith) hp
  have h2 : 0 < Real.exp 1 * (p + q) * 9 ^ (p + q) * Real.Gamma (p + q) := by positivity
  simp only [momentConstR]
  linarith

/-! ### Layer cake with real exponent (the paper's integration by parts) -/

/-- The paper's identity `E X^s = s ∫_0^∞ t^{s-1} P(X ≥ t) dt`, in `ℝ≥0∞` form (so no
integrability of `X^s` is needed): for an a.e. nonnegative measurable `f` and `s > 0`,
`∫⁻ f^s = s ∫⁻_{t>0} μ{t ≤ f} t^{s-1}`. -/
theorem lintegral_rpow_eq_meas (μ : Measure Ω) {f : Ω → ℝ} (hf_nn : 0 ≤ f)
    (hf : AEMeasurable f μ) {s : ℝ} (hs : 0 < s) :
    ∫⁻ ω, ENNReal.ofReal (f ω ^ s) ∂μ =
      ENNReal.ofReal s * ∫⁻ t in Ioi (0 : ℝ), μ {ω | t ≤ f ω} * ENNReal.ofReal (t ^ (s - 1)) :=
  lintegral_rpow_eq_lintegral_meas_le_mul μ (Eventually.of_forall hf_nn) hf hs

/-! ### Auxiliary measurability and integral bounds -/

/-- `t ↦ t^c` is a.e.-measurable for the measure restricted to a set avoiding `0`. -/
lemma aemeasurable_rpow_const_restrict {s : Set ℝ} (hms : MeasurableSet s) (hpos : s ⊆ Ioi (0 : ℝ))
    (c : ℝ) : AEMeasurable (fun t : ℝ => t ^ c) (volume.restrict s) :=
  ContinuousOn.aemeasurable
    (fun x hx => (Real.continuousAt_rpow_const x c (Or.inl (ne_of_gt (hpos hx)))).continuousWithinAt)
    hms

/-- **The Gamma tail bound.**  For `r > 0` and `M > 0`,
`∫_M^∞ t^{r-1} e^{-t/(9M)} dt ≤ (9M)^r Γ(r)`, the change of variables `s = t/9M` of the
paper's proof of Corollary I.2.5. -/
lemma integral_rpow_mul_exp_neg_le {r M : ℝ} (hr : 0 < r) (hM : 0 < M) :
    ∫ t in Ioi M, t ^ (r - 1) * Real.exp (-(t / (9 * M))) ≤ (9 * M) ^ r * Real.Gamma r := by
  have hc : 0 < 1 / (9 * M) := by positivity
  have hkey : ∀ t : ℝ, Real.exp (-(t / (9 * M))) = Real.exp (-((1 / (9 * M)) * t)) := by
    intro t
    congr 1
    field_simp
  have hbase := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := r) (r := 1 / (9 * M)) hr hc
  have hint : IntegrableOn (fun t : ℝ => t ^ (r - 1) * Real.exp (-((1 / (9 * M)) * t)))
      (Ioi 0) :=
    .of_integral_ne_zero (by rw [hbase]; positivity)
  have hsub : Ioi M ⊆ Ioi (0 : ℝ) := Ioi_subset_Ioi hM.le
  calc ∫ t in Ioi M, t ^ (r - 1) * Real.exp (-(t / (9 * M)))
      = ∫ t in Ioi M, t ^ (r - 1) * Real.exp (-((1 / (9 * M)) * t)) := by
        refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
        rw [hkey t]
    _ ≤ ∫ t in Ioi (0 : ℝ), t ^ (r - 1) * Real.exp (-((1 / (9 * M)) * t)) := by
        apply setIntegral_mono_set hint _ hsub.eventuallySubset
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le
    _ = (9 * M) ^ r * Real.Gamma r := by
        rw [hbase]
        have h9 : 1 / (1 / (9 * M)) = 9 * M := by rw [one_div_div, div_one]
        rw [h9]

/-- **Moment lower bound at a level.**  For `M ≥ 0` and `p > 0`,
`M^p μ{M ≤ f} ≤ ∫⁻ f^p`; the `ℝ≥0∞` version of the Markov-type bound used in the paper's
estimate of the upper part of the layer cake integral. -/
lemma ofReal_rpow_mul_meas_le_lintegral {μ : Measure Ω} {f : Ω → ℝ} (hf : Measurable f)
    {M : ℝ} (hM : 0 ≤ M) {p : ℝ} (hp : 0 < p) :
    ENNReal.ofReal (M ^ p) * μ {ω | M ≤ f ω} ≤ ∫⁻ ω, ENNReal.ofReal (f ω ^ p) ∂μ := by
  have hmeas : MeasurableSet {ω : Ω | M ≤ f ω} := measurableSet_le measurable_const hf
  have hind : AEMeasurable ({ω : Ω | M ≤ f ω}.indicator (1 : Ω → ℝ≥0∞)) μ :=
    (measurable_const.indicator hmeas).aemeasurable
  have hpt : ∀ ω : Ω,
      ENNReal.ofReal (M ^ p) * ({ω : Ω | M ≤ f ω}.indicator (1 : Ω → ℝ≥0∞)) ω ≤
        ENNReal.ofReal (f ω ^ p) := by
    intro ω
    rw [Set.indicator_apply]
    split_ifs with h
    · simp only [Pi.one_apply, mul_one]
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hM h hp.le)
    · rw [mul_zero]
      exact bot_le
  calc ENNReal.ofReal (M ^ p) * μ {ω | M ≤ f ω}
      = ENNReal.ofReal (M ^ p) *
          ∫⁻ ω, ({ω : Ω | M ≤ f ω}.indicator (1 : Ω → ℝ≥0∞)) ω ∂μ := by
        rw [lintegral_indicator_one hmeas]
    _ = ∫⁻ ω, ENNReal.ofReal (M ^ p) *
          ({ω : Ω | M ≤ f ω}.indicator (1 : Ω → ℝ≥0∞)) ω ∂μ := by
        rw [lintegral_const_mul'' _ hind]
    _ ≤ ∫⁻ ω, ENNReal.ofReal (f ω ^ p) ∂μ := lintegral_mono hpt


/-! ### The real-exponent moment ratio -/

/-- **The upper part of the layer cake integral** -- the second term in the paper's proof of
Corollary I.2.5.  For `r > 0`, the exponential tail estimate (I.2.6) above the scale `M` gives

  `∫_M^∞ μ{t ≤ f} t^{r-1} dt ≤ μ{M ≤ f} · e · (9M)^r Γ(r)`,

by the change of variables `s = t/9M` and `∫_0^∞ s^{r-1} e^{-s} ds = Γ(r)`. -/
lemma upper_part_bound {μ : Measure Ω} {f : Ω → ℝ} {M : ℝ} (hM : 0 < M) {r : ℝ} (hr : 0 < r)
    (htail : ∀ t : ℝ, M ≤ t → μ {ω | t ≤ f ω} ≤
      ENNReal.ofReal (Real.exp 1 * Real.exp (-(t / (9 * M)))) * μ {ω | M ≤ f ω}) :
    ∫⁻ t in Ioi M, μ {ω : Ω | t ≤ f ω} * ENNReal.ofReal (t ^ (r - 1)) ≤
      μ {ω : Ω | M ≤ f ω} * ENNReal.ofReal (Real.exp 1 * ((9 * M) ^ r * Real.Gamma r)) := by
  have hptB : ∀ t : ℝ, t ∈ Ioi M →
      μ {ω : Ω | t ≤ f ω} * ENNReal.ofReal (t ^ (r - 1))
        ≤ (ENNReal.ofReal (Real.exp 1) * μ {ω : Ω | M ≤ f ω}) *
            (ENNReal.ofReal (Real.exp (-(t / (9 * M)))) * ENNReal.ofReal (t ^ (r - 1))) := by
    intro t ht
    have htM : M ≤ t := le_of_lt ht
    have h1 := htail t htM
    rw [ENNReal.ofReal_mul (Real.exp_pos 1).le] at h1
    calc μ {ω : Ω | t ≤ f ω} * ENNReal.ofReal (t ^ (r - 1))
        ≤ ((ENNReal.ofReal (Real.exp 1) * ENNReal.ofReal (Real.exp (-(t / (9 * M))))) *
            μ {ω : Ω | M ≤ f ω}) * ENNReal.ofReal (t ^ (r - 1)) := mul_le_mul_left h1 _
      _ = (ENNReal.ofReal (Real.exp 1) * μ {ω : Ω | M ≤ f ω}) *
            (ENNReal.ofReal (Real.exp (-(t / (9 * M)))) * ENNReal.ofReal (t ^ (r - 1))) := by
          ring
  have hae : AEMeasurable (fun t : ℝ =>
      ENNReal.ofReal (Real.exp (-(t / (9 * M)))) * ENNReal.ofReal (t ^ (r - 1)))
      (volume.restrict (Ioi M)) := by
    have h1 : Measurable fun t : ℝ => Real.exp (-(t / (9 * M))) := by fun_prop
    exact (h1.ennreal_ofReal).aemeasurable.mul
      (ENNReal.measurable_ofReal.comp_aemeasurable
        (aemeasurable_rpow_const_restrict measurableSet_Ioi (fun x hx => lt_trans hM hx) _))
  have hint0 : IntegrableOn
      (fun t : ℝ => t ^ (r - 1) * Real.exp (-((1 / (9 * M)) * t))) (Ioi 0) :=
    .of_integral_ne_zero (by
      rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hr (by positivity)]
      positivity)
  have hintU : IntegrableOn (fun t : ℝ => t ^ (r - 1) * Real.exp (-(t / (9 * M))))
      (Ioi 0) := by
    refine hint0.congr_fun ?_ measurableSet_Ioi
    intro t _
    field_simp
  have hint : IntegrableOn (fun t : ℝ => t ^ (r - 1) * Real.exp (-(t / (9 * M))))
      (Ioi M) := hintU.mono_set (Ioi_subset_Ioi hM.le)
  calc ∫⁻ t in Ioi M, μ {ω : Ω | t ≤ f ω} * ENNReal.ofReal (t ^ (r - 1))
      ≤ ∫⁻ t in Ioi M, (ENNReal.ofReal (Real.exp 1) * μ {ω : Ω | M ≤ f ω}) *
          (ENNReal.ofReal (Real.exp (-(t / (9 * M)))) * ENNReal.ofReal (t ^ (r - 1))) := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        exact hptB t ht
    _ = (ENNReal.ofReal (Real.exp 1) * μ {ω : Ω | M ≤ f ω}) * ∫⁻ t in Ioi M,
          (ENNReal.ofReal (Real.exp (-(t / (9 * M)))) * ENNReal.ofReal (t ^ (r - 1))) := by
        rw [lintegral_const_mul''
          (f := fun t : ℝ => ENNReal.ofReal (Real.exp (-(t / (9 * M)))) *
            ENNReal.ofReal (t ^ (r - 1))) _ hae]
    _ = (ENNReal.ofReal (Real.exp 1) * μ {ω : Ω | M ≤ f ω}) * ∫⁻ t in Ioi M,
          ENNReal.ofReal (t ^ (r - 1) * Real.exp (-(t / (9 * M)))) := by
        congr 1
        refine lintegral_congr_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        rw [mul_comm (ENNReal.ofReal (Real.exp (-(t / (9 * M))))),
          ← ENNReal.ofReal_mul (Real.rpow_nonneg (le_of_lt (lt_trans hM ht)) _)]
    _ = (ENNReal.ofReal (Real.exp 1) * μ {ω : Ω | M ≤ f ω}) *
          ENNReal.ofReal (∫ t in Ioi M, t ^ (r - 1) * Real.exp (-(t / (9 * M)))) := by
        congr 1
        exact (ofReal_integral_eq_lintegral_ofReal hint
          (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
              exact mul_nonneg (Real.rpow_nonneg (le_of_lt (lt_trans hM ht)) _)
                (Real.exp_pos _).le)).symm
    _ ≤ (ENNReal.ofReal (Real.exp 1) * μ {ω : Ω | M ≤ f ω}) *
          ENNReal.ofReal ((9 * M) ^ r * Real.Gamma r) := by
        refine mul_le_mul_right ?_ _
        exact ENNReal.ofReal_le_ofReal (integral_rpow_mul_exp_neg_le hr hM)
    _ = μ {ω : Ω | M ≤ f ω} * ENNReal.ofReal (Real.exp 1 * ((9 * M) ^ r * Real.Gamma r)) := by
        rw [ENNReal.ofReal_mul (Real.exp_pos 1).le]
        ring

/-- **Corollary I.2.5 of arXiv:2508.18807v1 for real exponents.**  Let `f ≥ 0` be measurable,
`M ≥ 1`, and suppose the exponential tail estimate (I.2.6) holds above the scale `M`:

  `μ{t ≤ f} ≤ e · exp(-t/9M) · μ{M ≤ f}`  for all `t ≥ M`.

Then for all real `p > 0`, `q ≥ 0`,

  `∫⁻ f^{p+q} ≤ C(p,q) · M^q · ∫⁻ f^p`,  `C(p,q) = momentConstR p q`,

with the convention `∞ ≤ ∞`.  No probability hypothesis on `μ` is needed. -/
theorem moment_ratio_le_rpow {μ : Measure Ω} {f : Ω → ℝ} (hf : Measurable f) (hf_nn : 0 ≤ f)
    {M : ℝ} (hM : 1 ≤ M)
    (htail : ∀ t : ℝ, M ≤ t → μ {ω | t ≤ f ω} ≤
      ENNReal.ofReal (Real.exp 1 * Real.exp (-(t / (9 * M)))) * μ {ω | M ≤ f ω})
    {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) :
    ∫⁻ ω, ENNReal.ofReal (f ω ^ (p + q)) ∂μ ≤
      ENNReal.ofReal (momentConstR p q) * ENNReal.ofReal (M ^ q) *
        ∫⁻ ω, ENNReal.ofReal (f ω ^ p) ∂μ := by
  classical
  have hMpos : (0 : ℝ) < M := by linarith
  have hs : 0 < p + q := by linarith
  -- the tail measure is antitone, hence measurable, in the level
  have hTanti : Antitone fun t : ℝ => μ {ω : Ω | t ≤ f ω} :=
    fun a b hab => measure_mono fun _ hω => le_trans hab hω
  have hT : Measurable fun t : ℝ => μ {ω : Ω | t ≤ f ω} := hTanti.measurable
  -- measurability of the two integrands, restricted to sets avoiding `0`
  have haemeas : ∀ (c : ℝ) {s : Set ℝ}, MeasurableSet s → s ⊆ Ioi (0 : ℝ) →
      AEMeasurable (fun t : ℝ => μ {ω : Ω | t ≤ f ω} * ENNReal.ofReal (t ^ c))
        (volume.restrict s) := by
    intro c s hms hpos
    exact hT.aemeasurable.mul
      ((ENNReal.measurable_ofReal.comp_aemeasurable
        (aemeasurable_rpow_const_restrict hms hpos c)))
  -- abbreviations
  set TM : ℝ≥0∞ := μ {ω : Ω | M ≤ f ω} with hTM
  set EfP : ℝ≥0∞ := ∫⁻ ω, ENNReal.ofReal (f ω ^ p) ∂μ with hEfP
  set Ig : ℝ≥0∞ := ∫⁻ t in Ioi (0 : ℝ), μ {ω | t ≤ f ω} * ENNReal.ofReal (t ^ (p + q - 1))
    with hIg
  set Ip : ℝ≥0∞ := ∫⁻ t in Ioi (0 : ℝ), μ {ω : Ω | t ≤ f ω} * ENNReal.ofReal (t ^ (p - 1))
    with hIp
  set I1 : ℝ≥0∞ := ∫⁻ t in Ioc (0 : ℝ) M, μ {ω : Ω | t ≤ f ω} * ENNReal.ofReal (t ^ (p + q - 1))
    with hI1
  set I2 : ℝ≥0∞ := ∫⁻ t in Ioi M, μ {ω : Ω | t ≤ f ω} * ENNReal.ofReal (t ^ (p + q - 1))
    with hI2
  -- the two layer cake identities
  have hlc_s : ∫⁻ ω, ENNReal.ofReal (f ω ^ (p + q)) ∂μ = ENNReal.ofReal (p + q) * Ig := by
    rw [hIg]
    exact lintegral_rpow_eq_meas μ hf_nn hf.aemeasurable hs
  have hlc_p : EfP = ENNReal.ofReal p * Ip := by
    rw [hEfP, hIp]
    exact lintegral_rpow_eq_meas μ hf_nn hf.aemeasurable hp
  -- splitting the layer cake integral at the scale `M`
  have hdisj : Disjoint (Ioc (0 : ℝ) M) (Ioi M) := Ioc_disjoint_Ioi le_rfl
  have hsplit : Ig = I1 + I2 := by
    rw [hIg, hI1, hI2, ← Ioc_union_Ioi_eq_Ioi hMpos.le,
      lintegral_union (A := Ioc (0 : ℝ) M) (B := Ioi M) measurableSet_Ioi hdisj]
  -- ## Part A: the lower part `t ≤ M`
  have hptA : ∀ t : ℝ, t ∈ Ioc (0 : ℝ) M →
      μ {ω : Ω | t ≤ f ω} * ENNReal.ofReal (t ^ (p + q - 1))
        ≤ (μ {ω : Ω | t ≤ f ω} * ENNReal.ofReal (t ^ (p - 1))) * ENNReal.ofReal (M ^ q) := by
    intro t ht
    obtain ⟨ht0, htM⟩ := ht
    have htpos : 0 < t := ht0
    have hpow : t ^ (p + q - 1) = t ^ (p - 1) * t ^ q := by
      rw [← Real.rpow_add htpos]
      ring_nf
    have hle : t ^ (p + q - 1) ≤ t ^ (p - 1) * M ^ q := by
      rw [hpow]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow htpos.le htM hq)
        (Real.rpow_nonneg htpos.le _)
    have hof : ENNReal.ofReal (t ^ (p + q - 1)) ≤
        ENNReal.ofReal (t ^ (p - 1)) * ENNReal.ofReal (M ^ q) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg htpos.le _)]
      exact ENNReal.ofReal_le_ofReal hle
    calc μ {ω : Ω | t ≤ f ω} * ENNReal.ofReal (t ^ (p + q - 1))
        ≤ μ {ω : Ω | t ≤ f ω} *
            (ENNReal.ofReal (t ^ (p - 1)) * ENNReal.ofReal (M ^ q)) :=
          mul_le_mul_right hof _
      _ = (μ {ω : Ω | t ≤ f ω} * ENNReal.ofReal (t ^ (p - 1))) *
            ENNReal.ofReal (M ^ q) := by ring
  have hA_main : I1 ≤ Ip * ENNReal.ofReal (M ^ q) := by
    calc I1 ≤ ∫⁻ t in Ioc (0 : ℝ) M,
          (μ {ω : Ω | t ≤ f ω} * ENNReal.ofReal (t ^ (p - 1))) * ENNReal.ofReal (M ^ q) := by
          rw [hI1]
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
          exact hptA t ht
      _ = (∫⁻ t in Ioc (0 : ℝ) M, μ {ω : Ω | t ≤ f ω} * ENNReal.ofReal (t ^ (p - 1))) *
            ENNReal.ofReal (M ^ q) := by
          rw [lintegral_mul_const'' _ (haemeas (p - 1) measurableSet_Ioc Ioc_subset_Ioi_self)]
      _ ≤ Ip * ENNReal.ofReal (M ^ q) := by
          rw [hIp]
          exact mul_le_mul_left (lintegral_mono_set Ioc_subset_Ioi_self) _
  have hA : ENNReal.ofReal (p + q) * I1 ≤
      ENNReal.ofReal ((p + q) / p) * ENNReal.ofReal (M ^ q) * EfP := by
    have hpne : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hp).ne'
    have hptop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
    have e1 : ENNReal.ofReal ((p + q) / p) * ENNReal.ofReal p = ENNReal.ofReal (p + q) := by
      rw [ENNReal.ofReal_div_of_pos hp, ENNReal.div_mul_cancel hpne hptop]
    calc ENNReal.ofReal (p + q) * I1
        ≤ ENNReal.ofReal (p + q) * (Ip * ENNReal.ofReal (M ^ q)) := mul_le_mul_right hA_main _
      _ = ENNReal.ofReal ((p + q) / p) * ENNReal.ofReal (M ^ q) * EfP := by
          rw [hlc_p, ← e1]
          ring
  -- ## Part B: the upper part `t > M`
  have hint0 : IntegrableOn
      (fun t : ℝ => t ^ (p + q - 1) * Real.exp (-((1 / (9 * M)) * t))) (Ioi 0) :=
    .of_integral_ne_zero (by
      rw [Real.integral_rpow_mul_exp_neg_mul_Ioi hs (by positivity)]
      positivity)
  have hintU : IntegrableOn (fun t : ℝ => t ^ (p + q - 1) * Real.exp (-(t / (9 * M))))
      (Ioi 0) := by
    refine hint0.congr_fun ?_ measurableSet_Ioi
    intro t _
    field_simp
  have hint : IntegrableOn (fun t : ℝ => t ^ (p + q - 1) * Real.exp (-(t / (9 * M))))
      (Ioi M) := hintU.mono_set (Ioi_subset_Ioi hMpos.le)
  have hB_main : I2 ≤
      TM * ENNReal.ofReal (Real.exp 1 * ((9 * M) ^ (p + q) * Real.Gamma (p + q))) :=
    upper_part_bound hMpos hs htail
  have hB : ENNReal.ofReal (p + q) * I2 ≤
      ENNReal.ofReal (Real.exp 1 * (p + q) * 9 ^ (p + q) * Real.Gamma (p + q)) *
        ENNReal.ofReal (M ^ q) * EfP := by
    have hreal : (p + q) * (Real.exp 1 * ((9 * M) ^ (p + q) * Real.Gamma (p + q)))
        = (Real.exp 1 * (p + q) * 9 ^ (p + q) * Real.Gamma (p + q)) * (M ^ p * M ^ q) := by
      rw [Real.mul_rpow (by norm_num) hMpos.le, ← Real.rpow_add hMpos]
      ring
    have hconst1 : (0 : ℝ) ≤ Real.exp 1 * (p + q) * 9 ^ (p + q) * Real.Gamma (p + q) := by
      have := Real.Gamma_pos_of_pos hs
      positivity
    have hconst2 : (0 : ℝ) ≤ M ^ p * M ^ q := by positivity
    have hstep : ENNReal.ofReal (p + q) *
        ENNReal.ofReal (Real.exp 1 * ((9 * M) ^ (p + q) * Real.Gamma (p + q)))
        = ENNReal.ofReal (Real.exp 1 * (p + q) * 9 ^ (p + q) * Real.Gamma (p + q)) *
            (ENNReal.ofReal (M ^ p) * ENNReal.ofReal (M ^ q)) := by
      have hsplit1 : ENNReal.ofReal
          ((Real.exp 1 * (p + q) * 9 ^ (p + q) * Real.Gamma (p + q)) * (M ^ p * M ^ q))
          = ENNReal.ofReal (Real.exp 1 * (p + q) * 9 ^ (p + q) * Real.Gamma (p + q)) *
            ENNReal.ofReal (M ^ p * M ^ q) := ENNReal.ofReal_mul hconst1
      have hsplit2 : ENNReal.ofReal (M ^ p * M ^ q)
          = ENNReal.ofReal (M ^ p) * ENNReal.ofReal (M ^ q) :=
        ENNReal.ofReal_mul (by positivity)
      rw [← ENNReal.ofReal_mul (le_of_lt hs), hreal, hsplit1, hsplit2]
    have hcombine : ENNReal.ofReal (p + q) *
        (TM * ENNReal.ofReal (Real.exp 1 * ((9 * M) ^ (p + q) * Real.Gamma (p + q))))
        = (ENNReal.ofReal (M ^ p) * TM) * ENNReal.ofReal (M ^ q) *
            ENNReal.ofReal (Real.exp 1 * (p + q) * 9 ^ (p + q) * Real.Gamma (p + q)) := by
      rw [← mul_assoc, mul_comm (ENNReal.ofReal (p + q)) TM, mul_assoc, hstep]
      ring
    calc ENNReal.ofReal (p + q) * I2
        ≤ ENNReal.ofReal (p + q) *
            (TM * ENNReal.ofReal (Real.exp 1 * ((9 * M) ^ (p + q) * Real.Gamma (p + q)))) :=
          mul_le_mul_right hB_main _
      _ = (ENNReal.ofReal (M ^ p) * TM) * ENNReal.ofReal (M ^ q) *
            ENNReal.ofReal (Real.exp 1 * (p + q) * 9 ^ (p + q) * Real.Gamma (p + q)) :=
          hcombine
      _ ≤ EfP * ENNReal.ofReal (M ^ q) *
            ENNReal.ofReal (Real.exp 1 * (p + q) * 9 ^ (p + q) * Real.Gamma (p + q)) := by
          refine mul_le_mul_left (mul_le_mul_left ?_ _) _
          rw [hEfP, hTM]
          exact ofReal_rpow_mul_meas_le_lintegral hf hMpos.le hp
      _ = ENNReal.ofReal (Real.exp 1 * (p + q) * 9 ^ (p + q) * Real.Gamma (p + q)) *
            ENNReal.ofReal (M ^ q) * EfP := by ring
  -- ## Assembly
  have hconst : ENNReal.ofReal ((p + q) / p) +
      ENNReal.ofReal (Real.exp 1 * (p + q) * 9 ^ (p + q) * Real.Gamma (p + q)) =
      ENNReal.ofReal (momentConstR p q) := by
    rw [← ENNReal.ofReal_add (le_of_lt (div_pos hs hp)) (by
      have := Real.Gamma_pos_of_pos hs
      positivity)]
    rfl
  calc ∫⁻ ω, ENNReal.ofReal (f ω ^ (p + q)) ∂μ
      = ENNReal.ofReal (p + q) * Ig := hlc_s
    _ = ENNReal.ofReal (p + q) * (I1 + I2) := by rw [hsplit]
    _ = ENNReal.ofReal (p + q) * I1 + ENNReal.ofReal (p + q) * I2 := by ring
    _ ≤ ENNReal.ofReal ((p + q) / p) * ENNReal.ofReal (M ^ q) * EfP +
        ENNReal.ofReal (Real.exp 1 * (p + q) * 9 ^ (p + q) * Real.Gamma (p + q)) *
          ENNReal.ofReal (M ^ q) * EfP := add_le_add hA hB
    _ = (ENNReal.ofReal ((p + q) / p) +
          ENNReal.ofReal (Real.exp 1 * (p + q) * 9 ^ (p + q) * Real.Gamma (p + q))) *
          ENNReal.ofReal (M ^ q) * EfP := by ring
    _ = ENNReal.ofReal (momentConstR p q) * ENNReal.ofReal (M ^ q) * EfP := by rw [hconst]
    _ = ENNReal.ofReal (momentConstR p q) * ENNReal.ofReal (M ^ q) *
          ∫⁻ ω, ENNReal.ofReal (f ω ^ p) ∂μ := by rw [hEfP]

/-! ### The case `p = 0` -/

/-- **Corollary I.2.5 with `p = 0`.**  The paper's statement is for `p, q ≥ 0`; for `p = 0` and a
probability measure the right-hand side `M^q E|K_x ∩ W|^0` is `M^q` (since `|K_x ∩ W| ≥ 1` for
`x ∈ W`), so the claim is the pure moment bound `E f^r ≤ (1 + e r 9^r Γ(r)) M^r`, proved here
from the same exponential tail (I.2.6) and the same layer cake.

This is *not* a consequence of `moment_ratio_le_rpow` (which requires `p > 0`) but the same
proof with `E f^p` replaced by `μ univ = 1` in the lower part of the layer cake. -/
theorem moment_le_rpow_of_tail {μ : Measure Ω} [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Measurable f) (hf_nn : 0 ≤ f) {M : ℝ} (hM : 1 ≤ M)
    (htail : ∀ t : ℝ, M ≤ t → μ {ω | t ≤ f ω} ≤
      ENNReal.ofReal (Real.exp 1 * Real.exp (-(t / (9 * M)))) * μ {ω | M ≤ f ω})
    {r : ℝ} (hr : 0 < r) :
    ∫⁻ ω, ENNReal.ofReal (f ω ^ r) ∂μ ≤
      ENNReal.ofReal (1 + Real.exp 1 * r * 9 ^ r * Real.Gamma r) * ENNReal.ofReal (M ^ r) := by
  have hMpos : (0 : ℝ) < M := by linarith
  have hTanti : Antitone fun t : ℝ => μ {ω : Ω | t ≤ f ω} :=
    fun a b hab => measure_mono fun _ hω => le_trans hab hω
  set Ig : ℝ≥0∞ := ∫⁻ t in Ioi (0 : ℝ), μ {ω : Ω | t ≤ f ω} * ENNReal.ofReal (t ^ (r - 1))
    with hIg
  set I1 : ℝ≥0∞ := ∫⁻ t in Ioc (0 : ℝ) M, μ {ω : Ω | t ≤ f ω} * ENNReal.ofReal (t ^ (r - 1))
    with hI1
  set I2 : ℝ≥0∞ := ∫⁻ t in Ioi M, μ {ω : Ω | t ≤ f ω} * ENNReal.ofReal (t ^ (r - 1))
    with hI2
  have hlc : ∫⁻ ω, ENNReal.ofReal (f ω ^ r) ∂μ = ENNReal.ofReal r * Ig := by
    rw [hIg]
    exact lintegral_rpow_eq_meas μ hf_nn hf.aemeasurable hr
  have hsplit : Ig = I1 + I2 := by
    rw [hIg, hI1, hI2, ← Ioc_union_Ioi_eq_Ioi hMpos.le,
      lintegral_union (A := Ioc (0 : ℝ) M) (B := Ioi M) measurableSet_Ioi (Ioc_disjoint_Ioi le_rfl)]
  -- the lower part: `μ{t ≤ f} ≤ 1` and `∫_0^M t^{r-1} dt = M^r/r`
  have hIntble : IntegrableOn (fun t : ℝ => t ^ (r - 1)) (Ioc (0 : ℝ) M) := by
    have h := intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := M)
      (r := r - 1) (by linarith)
    exact h.1
  have hIntVal : ∫ t in Ioc (0 : ℝ) M, t ^ (r - 1) = M ^ r / r := by
    rw [← intervalIntegral.integral_of_le hMpos.le,
      integral_rpow (a := (0 : ℝ)) (b := M) (Or.inl (by linarith))]
    rw [show r - 1 + 1 = r from by ring, Real.zero_rpow hr.ne', sub_zero]
  have hAint : ∫⁻ t in Ioc (0 : ℝ) M, ENNReal.ofReal (t ^ (r - 1)) =
      ENNReal.ofReal (M ^ r / r) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hIntble
      (by filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
          exact Real.rpow_nonneg (le_of_lt ht.1) _), hIntVal]
  have hA : I1 ≤ ENNReal.ofReal (M ^ r / r) := by
    rw [hI1]
    refine le_trans (lintegral_mono_ae ?_) (le_of_eq hAint)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have h1 : μ {ω : Ω | t ≤ f ω} ≤ 1 := by
      rw [← measure_univ (μ := μ)]
      exact measure_mono (subset_univ _)
    calc μ {ω : Ω | t ≤ f ω} * ENNReal.ofReal (t ^ (r - 1))
        ≤ 1 * ENNReal.ofReal (t ^ (r - 1)) := mul_le_mul_left h1 _
      _ = ENNReal.ofReal (t ^ (r - 1)) := one_mul _
  -- the upper part
  have hB : I2 ≤ ENNReal.ofReal (Real.exp 1 * ((9 * M) ^ r * Real.Gamma r)) := by
    rw [hI2]
    refine le_trans (upper_part_bound hMpos hr htail) ?_
    have h1 : μ {ω : Ω | M ≤ f ω} ≤ 1 := by
      rw [← measure_univ (μ := μ)]
      exact measure_mono (subset_univ _)
    calc μ {ω : Ω | M ≤ f ω} * ENNReal.ofReal (Real.exp 1 * ((9 * M) ^ r * Real.Gamma r))
        ≤ 1 * ENNReal.ofReal (Real.exp 1 * ((9 * M) ^ r * Real.Gamma r)) := mul_le_mul_left h1 _
      _ = ENNReal.ofReal (Real.exp 1 * ((9 * M) ^ r * Real.Gamma r)) := one_mul _
  -- assembly
  have hcpos : (0 : ℝ) ≤ Real.exp 1 * r * 9 ^ r * Real.Gamma r := by
    have := Real.Gamma_pos_of_pos hr
    positivity
  have hMsplit : (9 * M) ^ r = 9 ^ r * M ^ r := Real.mul_rpow (by norm_num) hMpos.le
  calc ∫⁻ ω, ENNReal.ofReal (f ω ^ r) ∂μ = ENNReal.ofReal r * Ig := hlc
    _ = ENNReal.ofReal r * (I1 + I2) := by rw [hsplit]
    _ = ENNReal.ofReal r * I1 + ENNReal.ofReal r * I2 := by ring
    _ ≤ ENNReal.ofReal r * ENNReal.ofReal (M ^ r / r) +
        ENNReal.ofReal r * ENNReal.ofReal (Real.exp 1 * ((9 * M) ^ r * Real.Gamma r)) :=
        add_le_add (mul_le_mul_right hA _) (mul_le_mul_right hB _)
    _ = ENNReal.ofReal (M ^ r) +
        ENNReal.ofReal (Real.exp 1 * r * 9 ^ r * Real.Gamma r) * ENNReal.ofReal (M ^ r) := by
        have hL1 : ENNReal.ofReal r * ENNReal.ofReal (M ^ r / r) = ENNReal.ofReal (M ^ r) := by
          rw [← ENNReal.ofReal_mul hr.le]
          congr 1
          field_simp
        have hL2 : ENNReal.ofReal r *
            ENNReal.ofReal (Real.exp 1 * ((9 * M) ^ r * Real.Gamma r))
            = ENNReal.ofReal (Real.exp 1 * r * 9 ^ r * Real.Gamma r) * ENNReal.ofReal (M ^ r) := by
          rw [← ENNReal.ofReal_mul hr.le]
          have h2 : r * (Real.exp 1 * ((9 * M) ^ r * Real.Gamma r))
              = (Real.exp 1 * r * 9 ^ r * Real.Gamma r) * M ^ r := by
            rw [hMsplit]; ring
          rw [h2, ENNReal.ofReal_mul hcpos]
        rw [hL1, hL2]
    _ = (1 + ENNReal.ofReal (Real.exp 1 * r * 9 ^ r * Real.Gamma r)) * ENNReal.ofReal (M ^ r) := by
        ring
    _ = ENNReal.ofReal (1 + Real.exp 1 * r * 9 ^ r * Real.Gamma r) * ENNReal.ofReal (M ^ r) := by
        rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm,
          ← ENNReal.ofReal_add zero_le_one hcpos]

end PercLib.CriticalLRP.Tightness
