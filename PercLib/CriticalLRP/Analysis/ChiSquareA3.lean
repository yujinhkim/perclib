/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Anchor instance for the constants of Proposition I.3.2

Proposition I.3.2 of the paper defines

  A3 = (A1 / A2^(1/a)) * lim_{λ→∞} λ^(-(a-1)/a) ∫_0^∞ (1 - e^{-λx})/x dQ∞(x),
  A4 = A3 / Γ(1/a),

and asserts that the λ→∞ limit implicit in the definition of `A3` is well defined.  In the paper's
application (proof of (I.1.7)) the limit law `Q∞` is the chi-square law with one degree of freedom,
i.e. the law of `Z^2` for `Z` standard normal, and `a = 2`.

This file supplies the anchor instance: it computes, exactly and unconditionally,

  ∫_0^∞ (1 - e^{-λx})/x dQ∞(x) = √(2λ+1) - 1   (the value printed in the paper),
  lim_{λ→∞} λ^{-1/2} ∫_0^∞ (1 - e^{-λx})/x dQ∞(x) = √2,

hence `A3 = √2 A1 / √A2` and `A4 = A3 / √π = √2 A1 / (√A2 √π)` for this `Q∞`, together with
non-vacuity of hypothesis 4 (`Q∞({0}) = 0`) and of the conclusion (`0 < A4`, `A3 = √π A4`).
No `sorry`, no new axioms; see the axiom audit at the end of the file.
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

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace PercLib.CriticalLRP.Anchor

/-! ### The chi-square law with one degree of freedom as a limit law `Q∞` -/

/-- The limit law `Q∞` of Proposition I.3.2 in the paper's application: the law of `Z ^ 2` for a
standard normal `Z`, i.e. the chi-square law with one degree of freedom. -/
noncomputable def Qinf : Measure ℝ := Measure.map (fun z : ℝ => z ^ 2) (gaussianReal 0 1)

instance : IsProbabilityMeasure Qinf := by
  unfold Qinf
  infer_instance

/-- **Hypothesis 4 of Proposition I.3.2 is satisfied**: `Q∞` has no atom at zero. -/
theorem Qinf_singleton_zero : Qinf {(0 : ℝ)} = 0 := by
  have hγ : gaussianReal (0 : ℝ) (1 : NNReal) {(0 : ℝ)} = 0 := by
    have h : NullSingletonClass (gaussianReal (0 : ℝ) (1 : NNReal)) :=
      nullSingletonClass_gaussianReal (by norm_num)
    exact measure_singleton 0
  unfold Qinf
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton 0)]
  have hpre : (fun z : ℝ => z ^ 2) ⁻¹' {(0 : ℝ)} = {(0 : ℝ)} := by
    ext z
    simp [pow_eq_zero_iff]
  rw [hpre, hγ]

/-! ### The layer-cake identity behind the `A3` kernel (general `Q∞`)

For every finite measure `Q` on `ℝ` with `Q {0} = 0` and every `λ ≥ 0`,

  `∫ (1 - e^{-λx})/x dQ(x) = ∫_0^λ (∫ e^{-tx} dQ(x)) dt`,

which is exactly the step used in the proof of Proposition I.3.2 to identify the `A3` kernel with the
integral of the Laplace transform of `Q∞` (the paper applies it with `Q = Q∞`, and with `Q = Q_r`
and the size-biased scaling for the `P_{r,h}` computation).  The singularity of the integrand at
`x = 0` is harmless: the identity is a.e. and `Q {0} = 0`. -/

/-- `Q∞` is supported on `[0, ∞)`. -/
theorem Qinf_ae_nonneg : ∀ᵐ x ∂Qinf, 0 ≤ x := by
  unfold Qinf
  rw [ae_map_iff (f := fun z : ℝ => z ^ 2) (p := fun x : ℝ => 0 ≤ x)
    (by fun_prop) (measurableSet_le measurable_const measurable_id)]
  filter_upwards with z
  exact sq_nonneg z

/-- Pointwise fundamental theorem of calculus: `∫_0^λ e^{-tx} dt = (1 - e^{-λx})/x` for `x ≠ 0`. -/
theorem intervalIntegral_exp_neg_mul (lam x : ℝ) (hx : x ≠ 0) :
    ∫ t in (0)..lam, Real.exp (-(t * x)) = (1 - Real.exp (-(lam * x))) / x := by
  have hderiv : ∀ t : ℝ,
      HasDerivAt (fun t : ℝ => (1 - Real.exp (-(t * x))) / x) (Real.exp (-(t * x))) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => -(t * x)) (-x) t := by
      have h0 : HasDerivAt (fun t : ℝ => t * x) x t := by
        simpa using (hasDerivAt_id t).mul_const x
      exact h0.neg
    have h2 : HasDerivAt (fun t : ℝ => Real.exp (-(t * x)))
        (Real.exp (-(t * x)) * (-x)) t := (Real.hasDerivAt_exp _).comp t h1
    have h3 : HasDerivAt (fun t : ℝ => 1 - Real.exp (-(t * x)))
        (-(Real.exp (-(t * x)) * (-x))) t := h2.const_sub 1
    have h4 : HasDerivAt (fun t : ℝ => (1 - Real.exp (-(t * x))) / x)
        (-(Real.exp (-(t * x)) * (-x)) / x) t := h3.div_const x
    convert h4 using 1
    field_simp
  have hint : IntervalIntegrable (fun t : ℝ => Real.exp (-(t * x))) volume 0 lam := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t) hint]
  simp

/-- The uncurried kernel `(t, x) ↦ e^{-tx}` is integrable on `[0,λ] ×` the space: it is bounded by
`1` on the a.e. domain and both reference measures are finite. -/
theorem integrable_uncurry_exp_neg_mul (Q : Measure ℝ) [IsFiniteMeasure Q]
    (hQpos : ∀ᵐ x ∂Q, 0 ≤ x) (lam : ℝ) (hlam : 0 ≤ lam) :
    Integrable (Function.uncurry fun t x : ℝ => Real.exp (-(t * x)))
      ((volume.restrict (Set.uIoc 0 lam)).prod Q) := by
  have : IsFiniteMeasure ((volume.restrict (Set.uIoc 0 lam)).prod Q) := by
    rw [Set.uIoc_of_le hlam]
    infer_instance
  refine Integrable.of_bound ?_ 1 ?_
  · exact Continuous.aestronglyMeasurable (by fun_prop)
  · rw [Measure.ae_prod_iff_ae_ae (measurableSet_le (by fun_prop) measurable_const)]
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    filter_upwards [hQpos] with x hx
    have ht0 : 0 ≤ t := by
      have h' : t ∈ Set.Ioc (0:ℝ) lam := by simpa [Set.uIoc_of_le hlam] using ht
      exact h'.1.le
    have hnn : 0 ≤ t * x := mul_nonneg ht0 hx
    rw [Function.uncurry_apply_pair, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-(t * x)) ≤ Real.exp 0 := by
          apply Real.exp_le_exp.mpr
          linarith
      _ = 1 := Real.exp_zero

/-- **Layer-cake identity for the `A3` kernel**: for a finite measure `Q` on `ℝ` with `Q {0} = 0`,
`∫ (1 - e^{-λx})/x dQ(x) = ∫_0^λ (∫ e^{-tx} dQ(x)) dt`. -/
theorem integral_one_sub_exp_div_eq_interval (Q : Measure ℝ) [IsFiniteMeasure Q]
    (hQpos : ∀ᵐ x ∂Q, 0 ≤ x) (hQ : Q {(0 : ℝ)} = 0) (lam : ℝ) (hlam : 0 ≤ lam) :
    ∫ x, (1 - Real.exp (-(lam * x))) / x ∂Q
      = ∫ t in (0)..lam, (∫ x, Real.exp (-(t * x)) ∂Q) := by
  have hae : ∀ᵐ x ∂Q, (∫ t in (0)..lam, Real.exp (-(t * x)))
      = (1 - Real.exp (-(lam * x))) / x := by
    have hne : ∀ᵐ x ∂Q, x ≠ 0 := by
      rw [ae_iff]
      simpa using hQ
    filter_upwards [hne] with x hx
    exact intervalIntegral_exp_neg_mul lam x hx
  rw [← integral_congr_ae hae]
  rw [← intervalIntegral_integral_swap (integrable_uncurry_exp_neg_mul Q hQpos lam hlam)]

/-! ### The Gaussian half-moment `E exp (-t Z^2) = (1 + 2t)^{-1/2}` -/


/-- Elementary normalisation: `(√(2π))⁻¹ √(π/(t+1/2)) = (1+2t)^{-1/2}` for `t ≥ 0`. -/
lemma sqrt_two_pi_inv_mul_sqrt_div (t : ℝ) (ht : 0 ≤ t) :
    (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (Real.pi / (t + 1 / 2))
      = (Real.sqrt (1 + 2 * t))⁻¹ := by
  have h1 : 0 < t + 1 / 2 := by linarith
  have hs1 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hs3 : 0 < Real.sqrt (t + 1 / 2) := Real.sqrt_pos.mpr h1
  have e1 : Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi :=
    Real.sqrt_mul (by norm_num) Real.pi
  have e2 : Real.sqrt (Real.pi / (t + 1 / 2)) = Real.sqrt Real.pi / Real.sqrt (t + 1 / 2) :=
    Real.sqrt_div' Real.pi h1.le
  have e3 : Real.sqrt (1 + 2 * t) = Real.sqrt 2 * Real.sqrt (t + 1 / 2) := by
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    ring
  rw [e1, e2, e3]
  field_simp

/-- The moment generating function of `Z ^ 2` at `-t`, for `t ≥ 0`. -/
theorem integral_exp_neg_mul_sq_gaussian (t : ℝ) (ht : 0 ≤ t) :
    ∫ z, Real.exp (-(t * z ^ 2)) ∂(gaussianReal 0 1) = (Real.sqrt (1 + 2 * t))⁻¹ := by
  rw [integral_gaussianReal_eq_integral_smul (v := (1 : NNReal)) (μ := 0) (by norm_num)]
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, smul_eq_mul]
  have hpt : ∀ x : ℝ, (√(2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) * Real.exp (-(t * x ^ 2))
      = (√(2 * Real.pi))⁻¹ * Real.exp (-((t + 1 / 2) * x ^ 2)) := by
    intro x
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  calc ∫ x, (√(2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) * Real.exp (-(t * x ^ 2))
      = ∫ x, (√(2 * Real.pi))⁻¹ * Real.exp ((-(t + 1 / 2)) * x ^ 2) := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only []
        rw [hpt x, neg_mul]
    _ = (√(2 * Real.pi))⁻¹ * ∫ x, Real.exp ((-(t + 1 / 2)) * x ^ 2) := integral_const_mul _ _
    _ = (√(2 * Real.pi))⁻¹ * (Real.sqrt (Real.pi / (t + 1 / 2))) := by
        rw [integral_gaussian (t + 1 / 2)]
    _ = (Real.sqrt (1 + 2 * t))⁻¹ := sqrt_two_pi_inv_mul_sqrt_div t ht

/-! ### The `A3` kernel integral for the chi-square limit law

The paper's displayed computation (p. 32) is
`∫_0^∞ (1 - e^{-λx})/x dQ∞(x) = √(2λ+1) - 1`.  We reproduce it here, with no asymptotic
input: the identity is exact for every `λ ≥ 0`. -/

/-- Pointwise: `∫_0^λ e^{-tz²} dt = (1 - e^{-λz²})/z²` for `z ≠ 0` (FTC). -/
theorem intervalIntegral_exp_neg_mul_sq (lam z : ℝ) (hz : z ≠ 0) :
    ∫ t in (0)..lam, Real.exp (-(t * z ^ 2)) = (1 - Real.exp (-(lam * z ^ 2))) / z ^ 2 := by
  have hderiv : ∀ t : ℝ,
      HasDerivAt (fun t : ℝ => (1 - Real.exp (-(t * z ^ 2))) / z ^ 2)
        (Real.exp (-(t * z ^ 2))) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => -(t * z ^ 2)) (-(z ^ 2)) t := by
      have h0 : HasDerivAt (fun t : ℝ => t * z ^ 2) (z ^ 2) t := by
        simpa using (hasDerivAt_id t).mul_const (z ^ 2)
      exact h0.neg
    have h2 : HasDerivAt (fun t : ℝ => Real.exp (-(t * z ^ 2)))
        (Real.exp (-(t * z ^ 2)) * (-(z ^ 2))) t := (Real.hasDerivAt_exp _).comp t h1
    have h3 : HasDerivAt (fun t : ℝ => 1 - Real.exp (-(t * z ^ 2)))
        (-(Real.exp (-(t * z ^ 2)) * (-(z ^ 2)))) t := h2.const_sub 1
    have h4 : HasDerivAt (fun t : ℝ => (1 - Real.exp (-(t * z ^ 2))) / z ^ 2)
        (-(Real.exp (-(t * z ^ 2)) * (-(z ^ 2))) / z ^ 2) t := h3.div_const (z ^ 2)
    convert h4 using 1
    field_simp
  have hint : IntervalIntegrable (fun t : ℝ => Real.exp (-(t * z ^ 2))) volume 0 lam := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t) hint]
  simp

/-- `gaussianReal 0 1` charges no mass at the origin. -/
theorem gaussian_ae_ne_zero : ∀ᵐ z ∂(gaussianReal (0 : ℝ) (1 : NNReal)), z ≠ 0 := by
  have h : (gaussianReal (0 : ℝ) (1 : NNReal)) {(0 : ℝ)} = 0 := by
    have : NullSingletonClass (gaussianReal (0 : ℝ) (1 : NNReal)) :=
      nullSingletonClass_gaussianReal (by norm_num)
    exact measure_singleton 0
  rw [ae_iff]
  simpa using h

/-- The integrand of the `A3` kernel is bounded by `1` on the integration region, which is enough
for `Integrable` since the reference measures are finite. -/
theorem integrable_uncurry_exp_neg_mul_sq (lam : ℝ) (hlam : 0 ≤ lam) :
    Integrable (Function.uncurry fun t z : ℝ => Real.exp (-(t * z ^ 2)))
      ((volume.restrict (Set.uIoc 0 lam)).prod (gaussianReal 0 1)) := by
  have : IsFiniteMeasure ((volume.restrict (Set.uIoc 0 lam)).prod (gaussianReal 0 1)) := by
    rw [Set.uIoc_of_le hlam]
    infer_instance
  refine Integrable.of_bound ?_ 1 ?_
  · exact (Continuous.aestronglyMeasurable (by fun_prop))
  · rw [Measure.ae_prod_iff_ae_ae (measurableSet_le (by fun_prop) measurable_const)]
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    filter_upwards [gaussian_ae_ne_zero] with z hz
    have ht0 : 0 ≤ t := by
      have : t ∈ Set.Ioc (0:ℝ) lam := by simpa [Set.uIoc_of_le hlam] using ht
      exact this.1.le
    have hnn : 0 ≤ t * z ^ 2 := mul_nonneg ht0 (sq_nonneg z)
    rw [Function.uncurry_apply_pair, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-(t * z ^ 2)) ≤ Real.exp 0 := by
          apply Real.exp_le_exp.mpr
          linarith
      _ = 1 := Real.exp_zero

/-- **The `A3` kernel integral for `Q∞` the chi-square law with one degree of freedom**:
`∫ (1 - e^{-λx})/x dQ∞(x) = √(2λ+1) - 1`, exactly as printed in the paper. -/
theorem integral_A3_kernel_Qinf (lam : ℝ) (hlam : 0 ≤ lam) :
    ∫ x, (1 - Real.exp (-(lam * x))) / x ∂Qinf = Real.sqrt (1 + 2 * lam) - 1 := by
  -- change of variables `x = z^2`
  have hmap : ∫ x, (1 - Real.exp (-(lam * x))) / x ∂Qinf
      = ∫ z, (1 - Real.exp (-(lam * z ^ 2))) / z ^ 2 ∂(gaussianReal 0 1) := by
    unfold Qinf
    refine integral_map (by fun_prop) ?_
    exact (by fun_prop : Measurable fun x : ℝ => (1 - Real.exp (-(lam * x))) / x).aestronglyMeasurable
  rw [hmap]
  -- replace the (a.e. defined) quotient by the interval integral
  have hae : ∀ᵐ z ∂(gaussianReal 0 1),
      (∫ t in (0)..lam, Real.exp (-(t * z ^ 2)))
        = (1 - Real.exp (-(lam * z ^ 2))) / z ^ 2 := by
    filter_upwards [gaussian_ae_ne_zero] with z hz
    exact intervalIntegral_exp_neg_mul_sq lam z hz
  rw [← integral_congr_ae hae]
  -- Fubini
  rw [← intervalIntegral_integral_swap (integrable_uncurry_exp_neg_mul_sq lam hlam)]
  -- the inner integral is the Gaussian half-moment
  have hstep : ∫ t in (0)..lam, (∫ z, Real.exp (-(t * z ^ 2)) ∂(gaussianReal 0 1))
      = ∫ t in (0)..lam, (Real.sqrt (1 + 2 * t))⁻¹ := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    have ht' := ht
    rw [Set.uIcc_of_le hlam] at ht'
    exact integral_exp_neg_mul_sq_gaussian t ht'.1
  rw [hstep]
  -- `∫_0^λ (1+2t)^{-1/2} dt = √(1+2λ) - 1`
  have hderiv : ∀ t : ℝ, t ∈ Set.uIcc (0:ℝ) lam → HasDerivAt (fun t : ℝ => Real.sqrt (1 + 2 * t))
      ((Real.sqrt (1 + 2 * t))⁻¹) t := by
    intro t ht
    have ht' := ht
    rw [Set.uIcc_of_le hlam] at ht'
    have hx : 1 + 2 * t ≠ 0 := by nlinarith [ht'.1]
    have h0 : HasDerivAt (fun t : ℝ => 1 + 2 * t) 2 t := by
      simpa using (hasDerivAt_id t).const_mul 2 |>.const_add 1
    have h1 : HasDerivAt ((fun x : ℝ => Real.sqrt x) ∘ (fun t : ℝ => 1 + 2 * t))
        ((1 / (2 * Real.sqrt (1 + 2 * t))) * 2) t :=
      HasDerivAt.comp t (Real.hasDerivAt_sqrt hx) h0
    have hder : (1 / (2 * Real.sqrt (1 + 2 * t))) * 2 = (Real.sqrt (1 + 2 * t))⁻¹ := by
      have hpos : 0 < Real.sqrt (1 + 2 * t) := Real.sqrt_pos.mpr (by linarith [ht'.1])
      field_simp
    rw [← hder]
    exact h1
  have hInt : IntervalIntegrable (fun t : ℝ => (Real.sqrt (1 + 2 * t))⁻¹) volume 0 lam := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have ht' := ht
    rw [Set.uIcc_of_le hlam] at ht'
    have hpos : 0 < 1 + 2 * t := by linarith [ht'.1]
    have hlin : ContinuousAt (fun t : ℝ => 1 + 2 * t) t := by fun_prop
    have hinner : ContinuousAt (fun t : ℝ => Real.sqrt (1 + 2 * t)) t :=
      Real.continuous_sqrt.continuousAt.comp hlin
    exact (hinner.inv₀ (ne_of_gt (Real.sqrt_pos.mpr hpos))).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hInt]
  simp

/-- **The Laplace transform of `Q∞`**: `∫ e^{-λx} dQ∞(x) = (1 + 2λ)^{-1/2}` for `λ ≥ 0`, i.e. the
moment generating function of `Z ^ 2`.  This is the `t`-integrand of the layer-cake identity, and it
is what the paper integrates over `t ∈ (0, λ)` to get `√(2λ+1) - 1`. -/
theorem laplace_Qinf (lam : ℝ) (hlam : 0 ≤ lam) :
    ∫ x, Real.exp (-(lam * x)) ∂Qinf = (Real.sqrt (1 + 2 * lam))⁻¹ := by
  unfold Qinf
  rw [integral_map (by fun_prop) (by fun_prop)]
  exact integral_exp_neg_mul_sq_gaussian lam hlam

/-- The same evaluation, obtained in the two steps the source uses: first the layer-cake identity
(valid for any `Q∞` supported on `[0,∞)` with no atom at `0`), then the Gaussian half-moment. -/
theorem integral_A3_kernel_Qinf_via_laplace (lam : ℝ) (hlam : 0 ≤ lam) :
    ∫ x, (1 - Real.exp (-(lam * x))) / x ∂Qinf
      = ∫ t in (0)..lam, (Real.sqrt (1 + 2 * t))⁻¹ := by
  rw [integral_one_sub_exp_div_eq_interval Qinf Qinf_ae_nonneg Qinf_singleton_zero lam hlam]
  refine intervalIntegral.integral_congr fun t ht => ?_
  have ht' := ht
  rw [Set.uIcc_of_le hlam] at ht'
  unfold Qinf
  rw [integral_map (by fun_prop) (by fun_prop)]
  exact integral_exp_neg_mul_sq_gaussian t ht'.1

/-! ### The `A3` limit: `λ^{-(a-1)/a} ∫ (1 - e^{-λx})/x dQ∞ → √2` at `a = 2`

The exponent is displayed in the source form `-(a-1)/a`, specialised to `a = 2`. -/

/-- `λ^{-1/2} = (√λ)^{-1}`. -/
lemma rpow_neg_half_eq (lam : ℝ) (hlam : 0 < lam) :
    lam ^ (-(1 / 2) : ℝ) = (Real.sqrt lam)⁻¹ := by
  rw [Real.rpow_neg hlam.le, ← Real.sqrt_eq_rpow]



/-- `√(2 + 1/λ) - (√λ)^{-1} → √2`. -/
theorem tendsto_sqrt_two_add_inv_sub_sqrt_inv :
    Tendsto (fun lam : ℝ => Real.sqrt (2 + 1 / lam) - (Real.sqrt lam)⁻¹) atTop (𝓝 (Real.sqrt 2)) := by
  have h1 : Tendsto (fun lam : ℝ => Real.sqrt (2 + 1 / lam)) atTop (𝓝 (Real.sqrt 2)) := by
    refine Real.continuous_sqrt.continuousAt.tendsto.comp ?_
    have h2 : Tendsto (fun _ : ℝ => (2:ℝ)) atTop (𝓝 2) := tendsto_const_nhds
    simpa using h2.add (tendsto_inv_atTop_zero (𝕜 := ℝ))
  have h2 : Tendsto (fun lam : ℝ => (Real.sqrt lam)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  simpa using h1.sub h2

/-- The `A3` kernel in the normalised form `λ^{1/a-1/2}·(√(2+1/λ) - (√λ)^{-1})`, eventually. -/
theorem A3_kernel_eventually_eq (a : ℝ) (hane : a ≠ 0) :
    (fun lam : ℝ => lam ^ (-((a - 1) / a) : ℝ)
        * ∫ x, (1 - Real.exp (-(lam * x))) / x ∂Qinf)
      =ᶠ[atTop] fun lam => lam ^ (1 / a - 1 / 2)
        * (Real.sqrt (2 + 1 / lam) - (Real.sqrt lam)⁻¹) := by
  filter_upwards [eventually_gt_atTop (0:ℝ)] with lam hlam
  rw [integral_A3_kernel_Qinf lam hlam.le]
  have h1 : Real.sqrt (1 + 2 * lam) - 1
      = Real.sqrt lam * (Real.sqrt (2 + 1 / lam) - (Real.sqrt lam)⁻¹) := by
    have hl : Real.sqrt lam ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hlam)
    have hm : Real.sqrt lam * Real.sqrt (2 + 1 / lam) = Real.sqrt (1 + 2 * lam) := by
      rw [← Real.sqrt_mul hlam.le]
      congr 1
      field_simp
      ring
    rw [mul_sub, hm, mul_inv_cancel₀ hl]
  have h2 : lam ^ (-((a - 1) / a) : ℝ) * Real.sqrt lam = lam ^ (1 / a - 1 / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hlam]
    congr 1
    field_simp
    ring
  rw [h1, ← mul_assoc, h2]

/-- **At `a > 2` the `A3` limit is `0`** for the chi-square limit law: the `A3` limit is finite and
non-zero only at `a = 2`. -/
theorem tendsto_A3_kernel_Qinf_of_gt_two (a : ℝ) (ha : 2 < a) :
    Tendsto (fun lam : ℝ => lam ^ (-((a - 1) / a) : ℝ)
        * ∫ x, (1 - Real.exp (-(lam * x))) / x ∂Qinf) atTop (𝓝 0) := by
  have ha0 : 0 < a := by linarith
  have hane : a ≠ 0 := ne_of_gt ha0
  rw [tendsto_congr' (A3_kernel_eventually_eq a hane)]
  have hsmall : Tendsto (fun lam : ℝ => lam ^ (1 / a - 1 / 2)) atTop (𝓝 0) := by
    have hexp : 0 < 1 / 2 - 1 / a := by
      field_simp
      ring_nf
      linarith
    have h := tendsto_rpow_neg_atTop (y := 1 / 2 - 1 / a) hexp
    convert h using 2
    ring
  simpa using hsmall.mul tendsto_sqrt_two_add_inv_sub_sqrt_inv

/-- **At `0 < a < 2` the `A3` kernel diverges to `+∞`** for the chi-square limit law. -/
theorem tendsto_A3_kernel_Qinf_of_lt_two (a : ℝ) (ha : 0 < a) (ha2 : a < 2) :
    Tendsto (fun lam : ℝ => lam ^ (-((a - 1) / a) : ℝ)
        * ∫ x, (1 - Real.exp (-(lam * x))) / x ∂Qinf) atTop atTop := by
  have hane : a ≠ 0 := ne_of_gt ha
  rw [tendsto_congr' (A3_kernel_eventually_eq a hane)]
  have hbig : Tendsto (fun lam : ℝ => lam ^ (1 / a - 1 / 2)) atTop atTop := by
    apply tendsto_rpow_atTop
    field_simp
    ring_nf
    linarith
  exact hbig.atTop_mul_pos (C := Real.sqrt 2) (Real.sqrt_pos.mpr (by norm_num))
    tendsto_sqrt_two_add_inv_sub_sqrt_inv

/-- The key elementary limit: `(√(1+2λ) - 1)/√λ → √2`. -/
theorem tendsto_sqrt_inv_mul_sub_one :
    Tendsto (fun lam : ℝ => (Real.sqrt lam)⁻¹ * (Real.sqrt (1 + 2 * lam) - 1))
      atTop (𝓝 (Real.sqrt 2)) := by
  have hsq : Tendsto (fun lam : ℝ => Real.sqrt (2 + 1 / lam)) atTop (𝓝 (Real.sqrt 2)) := by
    refine Real.continuous_sqrt.continuousAt.tendsto.comp ?_
    have h2 : Tendsto (fun _ : ℝ => (2:ℝ)) atTop (𝓝 2) := tendsto_const_nhds
    simpa using h2.add (tendsto_inv_atTop_zero (𝕜 := ℝ))
  have hinv : Tendsto (fun lam : ℝ => (Real.sqrt lam)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  have hkey : (fun lam : ℝ => (Real.sqrt lam)⁻¹ * (Real.sqrt (1 + 2 * lam) - 1))
      =ᶠ[atTop] fun lam => Real.sqrt (2 + 1 / lam) - (Real.sqrt lam)⁻¹ := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with lam hlam
    have hl : Real.sqrt lam ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hlam)
    have hdiv : Real.sqrt lam * Real.sqrt (2 + 1 / lam) = Real.sqrt (1 + 2 * lam) := by
      rw [← Real.sqrt_mul hlam.le]
      congr 1
      field_simp
      ring
    rw [mul_sub, ← hdiv]
    field_simp
  rw [tendsto_congr' hkey]
  simpa using hsq.sub hinv

/-- **The `A3` limit for the chi-square limit law**, in the source's exact shape: the exponent
`-(a-1)/a` at `a = 2`, applied to the kernel integral, converges to `√2`. -/
theorem tendsto_A3_kernel_Qinf :
    Tendsto (fun lam : ℝ => lam ^ (-((2 - 1) / 2) : ℝ)
        * ∫ x, (1 - Real.exp (-(lam * x))) / x ∂Qinf) atTop (𝓝 (Real.sqrt 2)) := by
  have hkey : (fun lam : ℝ => lam ^ (-((2 - 1) / 2) : ℝ)
      * ∫ x, (1 - Real.exp (-(lam * x))) / x ∂Qinf)
      =ᶠ[atTop] fun lam => (Real.sqrt lam)⁻¹ * (Real.sqrt (1 + 2 * lam) - 1) := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with lam hlam
    rw [integral_A3_kernel_Qinf lam hlam.le, show ((2 - 1) / 2 : ℝ) = 1 / 2 by norm_num,
      rpow_neg_half_eq lam hlam]
  rw [tendsto_congr' hkey]
  exact tendsto_sqrt_inv_mul_sub_one

/-! ### The constants `A3` and `A4` of Proposition I.3.2 at `a = 2` -/

/-- `A3` of Proposition I.3.2 for `Q∞`, written in the source's shape
`A3 = (A1 / A2^(1/a)) * L` where `L` is the `λ → ∞` limit of the kernel. -/
noncomputable def A3const (A1 A2 a L : ℝ) : ℝ := (A1 / A2 ^ (1 / a)) * L

/-- `A4 = A3 / Γ(1/a)` of Proposition I.3.2. -/
noncomputable def A4const (A3 a : ℝ) : ℝ := A3 / Real.Gamma (1 / a)

/-- The value of `A3` for the chi-square limit law at `a = 2`. -/
noncomputable def A3chi (A1 A2 : ℝ) : ℝ := A3const A1 A2 2 (Real.sqrt 2)

/-- The value of `A4` for the chi-square limit law at `a = 2`. -/
noncomputable def A4chi (A1 A2 : ℝ) : ℝ := A4const (A3chi A1 A2) 2

/-- **`A3 = √2 A1 / √A2`** for the chi-square limit law at `a = 2` (the source form
`A2^(1/a)` with `a = 2` is `√A2` for `A2 > 0`). -/
theorem A3chi_eq (A1 A2 : ℝ) (hA2 : 0 < A2) :
    A3chi A1 A2 = Real.sqrt 2 * A1 / Real.sqrt A2 := by
  have h : A2 ^ ((1:ℝ) / 2) = Real.sqrt A2 := by
    rw [← Real.sqrt_eq_rpow]
  unfold A3chi A3const
  rw [h]
  field_simp

/-- **`A4 = A3/Γ(1/2) = A3/√π = √2 A1 / (√A2 √π)`**, using `Γ(1/2) = √π`. -/
theorem A4chi_eq (A1 A2 : ℝ) (hA2 : 0 < A2) :
    A4chi A1 A2 = Real.sqrt 2 * A1 / (Real.sqrt A2 * Real.sqrt Real.pi) := by
  unfold A4chi A4const
  rw [show ((1:ℝ) / 2) = 1 / 2 by norm_num, Real.Gamma_one_half_eq, A3chi_eq A1 A2 hA2]
  rw [div_div]

/-- The paper's observation for `a = 2`: `A3 = √π A4` (equivalently `A4 = A3/Γ(1/2)`). -/
theorem A3chi_eq_sqrt_pi_mul_A4chi (A1 A2 : ℝ) (hA2 : 0 < A2) :
    A3chi A1 A2 = Real.sqrt Real.pi * A4chi A1 A2 := by
  rw [A4chi_eq A1 A2 hA2, A3chi_eq A1 A2 hA2]
  have hA2' : 0 < Real.sqrt A2 := Real.sqrt_pos.mpr hA2
  field_simp

/-- **Non-vacuity of the conclusion**: for `A1, A2 > 0` the constant `A3` is strictly positive and
finite, and `A4` is strictly positive. -/
theorem A3chi_pos (A1 A2 : ℝ) (hA1 : 0 < A1) (hA2 : 0 < A2) :
    0 < A3chi A1 A2 ∧ 0 < A4chi A1 A2 := by
  have h3 : 0 < A3chi A1 A2 := by
    rw [A3chi_eq A1 A2 hA2]
    positivity
  refine ⟨h3, ?_⟩
  rw [A4chi_eq A1 A2 hA2]
  positivity

/-- **Fidelity of (I.3.7) with the definition of `A3`**: the prefactor printed in (I.3.7),
`A1/(A2^{1/a} λ^{1-1/a})` applied to the kernel integral, tends to `A3` as `λ → ∞` (here `a = 2`,
`Q∞` the chi-square law).  This is the identity of the two constants that the source's argument
relies on. -/
theorem I37_bracket_tendsto_A3chi (A1 A2 : ℝ) (hA2 : 0 < A2) :
    Tendsto (fun lam : ℝ => A1 / (A2 ^ ((1:ℝ)/2) * lam ^ (1 - (1:ℝ)/2))
        * (Real.sqrt (1 + 2 * lam) - 1)) atTop (𝓝 (A3chi A1 A2)) := by
  have h : (fun lam : ℝ => A1 / (A2 ^ ((1:ℝ)/2) * lam ^ (1 - (1:ℝ)/2))
      * (Real.sqrt (1 + 2 * lam) - 1))
      =ᶠ[atTop] fun lam => A1 / A2 ^ ((1:ℝ)/2)
        * ((Real.sqrt lam)⁻¹ * (Real.sqrt (1 + 2 * lam) - 1)) := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with lam hlam
    rw [show (1:ℝ) - 1/2 = 1/2 by norm_num, ← Real.sqrt_eq_rpow]
    have hl : Real.sqrt lam ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hlam)
    field_simp
    simp only [Real.sqrt_eq_rpow]
    ring
  rw [tendsto_congr' h]
  have hlim := tendsto_sqrt_inv_mul_sub_one.const_mul (A1 / A2 ^ ((1:ℝ)/2))
  have hval : A1 / A2 ^ ((1:ℝ)/2) * Real.sqrt 2 = A3chi A1 A2 := by
    rw [A3chi_eq A1 A2 hA2]
    have hh : A2 ^ ((1:ℝ)/2) = Real.sqrt A2 := by rw [← Real.sqrt_eq_rpow]
    rw [hh]
    ring
  rw [← hval]
  exact hlim

/-- **Scale selection for `f r = r ^ (2α)` at `a = 2`** (the paper's application): the literal
inverse of `f` is `y ↦ y ^ (1/(2α))`, and the scale factor of (I.3.2) satisfies
`f^{-1}(λ/(A2 h))^α · h = √(λ/A2) · √h` — an exact identity, so at `a = 2` no asymptotic inverse is
needed for this `f`. -/
theorem scale_selection_sq (α A2 h lam : ℝ) (hα : 0 < α) (hA2 : 0 < A2) (hh : 0 < h)
    (hlam : 0 < lam) :
    ((lam / (A2 * h)) ^ (1 / (2 * α))) ^ α * h = Real.sqrt (lam / A2) * Real.sqrt h := by
  have hy : 0 < lam / (A2 * h) := by positivity
  have hexp : (1 / (2 * α)) * α = 1 / 2 := by
    field_simp
  have h1 : ((lam / (A2 * h)) ^ (1 / (2 * α))) ^ α = (lam / (A2 * h)) ^ ((1:ℝ)/2) := by
    rw [← Real.rpow_mul hy.le, hexp]
  have h2 : (lam / (A2 * h)) ^ ((1:ℝ)/2) = Real.sqrt (lam / (A2 * h)) := by
    rw [Real.sqrt_eq_rpow]
  have h3 : Real.sqrt (lam / (A2 * h)) * Real.sqrt h = Real.sqrt (lam / A2) := by
    rw [← Real.sqrt_mul (le_of_lt (by positivity : (0:ℝ) < lam / (A2 * h)))]
    congr 1
    field_simp
  have h4 : Real.sqrt h * Real.sqrt h = h := Real.mul_self_sqrt hh.le
  rw [h1, h2]
  calc Real.sqrt (lam / (A2 * h)) * h
      = Real.sqrt (lam / (A2 * h)) * (Real.sqrt h * Real.sqrt h) := by rw [h4]
    _ = Real.sqrt (lam / (A2 * h)) * Real.sqrt h * Real.sqrt h := by ring
    _ = Real.sqrt (lam / A2) * Real.sqrt h := by rw [h3]

/-- **Tail exponent at `a = 2`**: with `f r = r ^ (2α)`, the factor of (I.3.3) is
`f^{-1}(n)^α / n = n^{-1/2}`, so (I.3.3) reads `P(|K| ≥ n) ~ A4 / √n` in this case. -/
theorem tail_exponent_sq (α n : ℝ) (hα : 0 < α) (hn : 0 < n) :
    (n ^ (1 / (2 * α))) ^ α / n = (Real.sqrt n)⁻¹ := by
  have hexp : (1 / (2 * α)) * α = 1 / 2 := by field_simp
  have h1 : (n ^ (1 / (2 * α))) ^ α = n ^ ((1:ℝ)/2) := by
    rw [← Real.rpow_mul hn.le, hexp]
  have h2 : n ^ ((1:ℝ)/2) = Real.sqrt n := (Real.sqrt_eq_rpow n).symm
  have h3 : Real.sqrt n / n = (Real.sqrt n)⁻¹ := by
    have hs : Real.sqrt n ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hn)
    field_simp
    exact Real.sq_sqrt hn.le
  rw [h1, h2, h3]

/-- **Non-vacuity of hypotheses (3) and (4)**: the constant family `Q_r ≡ Q∞` (chi-square with one
degree of freedom) is weakly convergent in `ProbabilityMeasure ℝ`, and `Q∞` has no atom at zero.
The moment hypotheses (1), (2) are statements about the percolation model and are not instantiated
here; `A3` depends on the model only through `A1`, `A2` and `a`, which is why this instance pins
the constant. -/
theorem hypotheses_three_four_nonvacuous :
    Tendsto (fun _ : ℝ => (Measure.toProbabilityMeasure Qinf)) atTop
        (𝓝 (Measure.toProbabilityMeasure Qinf)) ∧ Qinf {(0 : ℝ)} = 0 := by
  have : OpensMeasurableSpace ℝ := BorelSpace.opensMeasurable
  exact ⟨tendsto_const_nhds, Qinf_singleton_zero⟩

/-! ### Axiom audit -/

#print axioms PercLib.CriticalLRP.Anchor.integral_exp_neg_mul_sq_gaussian
#print axioms PercLib.CriticalLRP.Anchor.Qinf_singleton_zero
#print axioms PercLib.CriticalLRP.Anchor.integral_A3_kernel_Qinf
#print axioms PercLib.CriticalLRP.Anchor.tendsto_A3_kernel_Qinf
#print axioms PercLib.CriticalLRP.Anchor.A3chi_eq
#print axioms PercLib.CriticalLRP.Anchor.A4chi_eq
#print axioms PercLib.CriticalLRP.Anchor.A3chi_eq_sqrt_pi_mul_A4chi
#print axioms PercLib.CriticalLRP.Anchor.A3chi_pos
#print axioms PercLib.CriticalLRP.Anchor.I37_bracket_tendsto_A3chi
#print axioms PercLib.CriticalLRP.Anchor.tendsto_A3_kernel_Qinf_of_gt_two
#print axioms PercLib.CriticalLRP.Anchor.tendsto_A3_kernel_Qinf_of_lt_two
#print axioms PercLib.CriticalLRP.Anchor.integral_one_sub_exp_div_eq_interval
#print axioms PercLib.CriticalLRP.Anchor.laplace_Qinf
#print axioms PercLib.CriticalLRP.Anchor.integral_A3_kernel_Qinf_via_laplace
#print axioms PercLib.CriticalLRP.Anchor.scale_selection_sq
#print axioms PercLib.CriticalLRP.Anchor.tail_exponent_sq
#print axioms PercLib.CriticalLRP.Anchor.hypotheses_three_four_nonvacuous

end PercLib.CriticalLRP.Anchor
