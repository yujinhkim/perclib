/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Chi-square tail integrals and weak convergence to the chi-square law

Two linked developments for Hutchcroft, *Critical long-range percolation I* (arXiv:2508.18807v1),
§I.1 and the proof of (I.1.7):

(a) the exact chi-square tail integral `∫_0^∞ (1-e^{-λx})/x dQ∞(x) = √(2λ+1) - 1` (p. 32 of
    arXiv v1), with the paper's displayed density form and the `√2` large-`λ` asymptotics;
(b) the weak-convergence transfer `Qᵣ → Q∞ ⟹ ∫(1-e^{-λx})/x dQᵣ → ∫(1-e^{-λx})/x dQ∞`, the
    uniform-integrability passage of one polynomial moment, and the chain
    "moment asymptotics `(2p-1)!!` ⇒ `Qᵣ ⇒ χ²₁` weakly ⇒ the tail integral tends to `√(2λ+1)-1`".

Drop-in location: `CriticalPercLib.CriticalLRP/MomentProblem/ChiSquareTail.lean`.
-/
module

public import PercLib.CriticalLRP.MomentProblem.ChiSquare

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BoundedContinuousFunction

namespace PercLib.CriticalLRP.MomentProblem


/-! ### The truncated Laplace profile `x ↦ ∫_0^λ e^{-tx} dt` -/

/-- `laplaceProfile lam x = ∫_0^lam e^{-t x} dt`; for `x ≠ 0` this is `(1 - e^{-lam x})/x`.

(The Lean integrand `(1 - e^{-lam x})/x` equals this only off `x = 0`, where Lean's division
convention gives `0`; on the measures below, `{0}` is null or the profile value `lam` is the
correct convention, so we keep the genuinely continuous object.) -/
noncomputable def laplaceProfile (lam x : ℝ) : ℝ := ∫ t in (0)..lam, Real.exp (-(t * x))

lemma laplaceProfile_of_ne {lam x : ℝ} (hx : x ≠ 0) :
    laplaceProfile lam x = (1 - Real.exp (-(lam * x))) / x := by
  have hderiv : ∀ t : ℝ,
      HasDerivAt (fun t => -Real.exp (-(t * x)) / x) (Real.exp (-(t * x))) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => t * x) x t := by
      simpa using (hasDerivAt_id t).mul_const x
    have h2 : HasDerivAt (fun t : ℝ => -(t * x)) (-x) t := h1.neg
    have h3 : HasDerivAt (fun t : ℝ => Real.exp (-(t * x))) (Real.exp (-(t * x)) * (-x)) t :=
      h2.exp
    have h4 : HasDerivAt (fun t : ℝ => Real.exp (-(t * x)) / (-x)) (Real.exp (-(t * x))) t := by
      refine (h3.div_const (-x)).congr_deriv ?_
      field_simp
    have h5 : (fun t : ℝ => Real.exp (-(t * x)) / (-x))
        = fun t => -Real.exp (-(t * x)) / x := by
      funext t; ring
    rw [← h5]
    exact h4
  have hInt : IntervalIntegrable (fun t : ℝ => Real.exp (-(t * x))) volume 0 lam :=
    ((by fun_prop : Continuous fun t : ℝ => Real.exp (-(t * x)))).intervalIntegrable _ _
  rw [laplaceProfile, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hderiv t) hInt]
  simp only [zero_mul, neg_zero, Real.exp_zero]
  field_simp
  ring

/-- On `x ≥ 0` the profile is nonnegative. -/
lemma laplaceProfile_nonneg {lam : ℝ} (hlam : 0 ≤ lam) (x : ℝ) : 0 ≤ laplaceProfile lam x := by
  rw [laplaceProfile]
  exact intervalIntegral.integral_nonneg hlam fun u _ => (Real.exp_pos _).le

/-- On `x ≥ 0` the profile is bounded by `lam`. -/
lemma laplaceProfile_le {lam : ℝ} (hlam : 0 ≤ lam) {x : ℝ} (hx : 0 ≤ x) :
    laplaceProfile lam x ≤ lam := by
  rw [laplaceProfile]
  have h := intervalIntegral.integral_mono_on hlam
    ((by fun_prop : Continuous fun t : ℝ => Real.exp (-(t * x))).intervalIntegrable _ _)
    (intervalIntegrable_const (μ := volume))
    (fun t ht => by
      rw [Real.exp_le_one_iff]
      nlinarith [ht.1])
  simpa using h

/-- The profile is continuous in `x` (the integral of a jointly continuous kernel over a compact
`t`-interval). -/
theorem continuous_laplaceProfile (lam : ℝ) : Continuous (laplaceProfile lam) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  have hbound_int : IntervalIntegrable (fun t : ℝ => Real.exp (-(t * x₀) + |t| * 1)) volume 0 lam :=
    (by fun_prop : Continuous fun t : ℝ => Real.exp (-(t * x₀) + |t| * 1)).intervalIntegrable _ _
  refine intervalIntegral.continuousAt_of_dominated_interval
    (F := fun x t => Real.exp (-(t * x)))
    (bound := fun t => Real.exp (-(t * x₀) + |t| * 1)) ?_ ?_ hbound_int ?_
  · filter_upwards with x
    exact (by fun_prop : Measurable fun t : ℝ => Real.exp (-(t * x))).aestronglyMeasurable
  · filter_upwards [Metric.ball_mem_nhds x₀ one_pos] with x hx
    filter_upwards with t ht
    have hdist : |x₀ - x| < 1 := by
      rw [← Real.dist_eq, dist_comm]
      exact hx
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_exp]
    have hkey : t * (x₀ - x) ≤ |t| * 1 := by
      calc t * (x₀ - x) ≤ |t * (x₀ - x)| := le_abs_self _
        _ = |t| * |x₀ - x| := abs_mul t (x₀ - x)
        _ ≤ |t| * 1 := by
            refine mul_le_mul_of_nonneg_left (le_of_lt hdist) (abs_nonneg t)
    have hsplit : -(t * x) = -(t * x₀) + t * (x₀ - x) := by ring
    rw [hsplit]
    linarith
  · filter_upwards with t ht
    exact (by fun_prop : ContinuousAt (fun x : ℝ => Real.exp (-(t * x))) x₀)

/-! ### Null sets and the Laplace transform of the chi-square law -/

/-- A measure vanishing on `(-∞,0]` is almost everywhere carried by `(0,∞)`. -/
lemma ae_pos_of_Iic {μ : Measure ℝ} (h : μ (Set.Iic 0) = 0) : ∀ᵐ x ∂μ, 0 < x := by
  rw [ae_iff]
  have hset : {x : ℝ | ¬ (0 < x)} = Set.Iic 0 := by
    simp [Set.Iic, not_lt]
  rw [hset]; exact h

lemma ae_ne_zero_of_Iic {μ : Measure ℝ} (h : μ (Set.Iic 0) = 0) : ∀ᵐ x ∂μ, x ≠ 0 :=
  (ae_pos_of_Iic h).mono fun x hx => ne_of_gt hx

/-- The chi-square measure with one degree of freedom vanishes on `(-∞,0]`. -/
lemma gammaMeasure_one_half_Iic_zero : gammaMeasure (1 / 2) (1 / 2) (Set.Iic 0) = 0 := by
  rw [gammaMeasure, withDensity_apply _ measurableSet_Iic]
  have hzero : ∀ x ∈ Set.Iic (0 : ℝ), gammaPDF (1 / 2) (1 / 2) x = 0 := by
    intro x hx
    have hx' : x ≤ 0 := hx
    rw [gammaPDF, gammaPDFReal]
    rcases lt_or_eq_of_le hx' with h | h
    · rw [ite_eq_right (by linarith : ¬ (0:ℝ) ≤ x), ENNReal.ofReal_zero]
    · subst h
      have hz : (0 : ℝ) ^ ((1 / 2 : ℝ) - 1) = 0 := Real.zero_rpow (by norm_num)
      rw [ite_eq_left le_rfl, hz]
      simp
  rw [setLIntegral_congr_fun measurableSet_Iic hzero, lintegral_zero]

/-- **Laplace transform of the chi-square law.** `E e^{-tX} = (1+2t)^{-1/2}` for `t > -1/2`. -/
lemma integral_exp_neg_mul_gammaMeasure_one_half {t : ℝ} (ht : -(1 / 2) < t) :
    ∫ x, Real.exp (-(t * x)) ∂(gammaMeasure (1 / 2) (1 / 2)) = 1 / Real.sqrt (1 + 2 * t) := by
  have ha : (0 : ℝ) < 1 / 2 := by norm_num
  have hr : (0 : ℝ) < t + 1 / 2 := by linarith
  rw [gammaMeasure, integral_withDensity_eq_integral_toReal_smul (measurable_gammaPDF' _ _)
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top) (fun x => Real.exp (-(t * x)))]
  have hpt : ∀ x : ℝ, (gammaPDF (1 / 2) (1 / 2) x).toReal • Real.exp (-(t * x))
      = gammaPDFReal (1 / 2) (1 / 2) x * Real.exp (-(t * x)) := by
    intro x
    rw [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha ha x), smul_eq_mul]
  simp_rw [hpt]
  have hzero : ∀ x : ℝ, x ∉ Set.Ioi (0 : ℝ) →
      gammaPDFReal (1 / 2) (1 / 2) x * Real.exp (-(t * x)) = 0 := by
    intro x hx
    have hx' : x ≤ 0 := by simpa using hx
    rcases lt_or_eq_of_le hx' with h | h
    · rw [gammaPDFReal, ite_eq_right (by linarith : ¬ (0 : ℝ) ≤ x), zero_mul]
    · subst h
      rw [gammaPDFReal, ite_eq_left le_rfl]
      have hz : (0 : ℝ) ^ ((1 / 2 : ℝ) - 1) = 0 := Real.zero_rpow (by norm_num)
      rw [hz]
      ring
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Ioi (0:ℝ)) hzero]
  have hfun : ∀ x ∈ Set.Ioi (0 : ℝ),
      gammaPDFReal (1 / 2) (1 / 2) x * Real.exp (-(t * x))
        = ((1 / 2 : ℝ) ^ (1 / 2 : ℝ) / Real.Gamma (1 / 2))
            * (x ^ ((1 / 2 : ℝ) - 1) * Real.exp (-((t + 1 / 2) * x))) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    rw [gammaPDFReal, ite_eq_left hx0.le]
    have hexp : Real.exp (-((1 / 2 : ℝ) * x)) * Real.exp (-(t * x))
        = Real.exp (-((t + 1 / 2) * x)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc (1 / 2 : ℝ) ^ (1 / 2 : ℝ) / Real.Gamma (1 / 2) * x ^ ((1 / 2 : ℝ) - 1)
          * Real.exp (-((1 / 2 : ℝ) * x)) * Real.exp (-(t * x))
        = (1 / 2 : ℝ) ^ (1 / 2 : ℝ) / Real.Gamma (1 / 2) * x ^ ((1 / 2 : ℝ) - 1)
            * (Real.exp (-((1 / 2 : ℝ) * x)) * Real.exp (-(t * x))) := by ring
      _ = (1 / 2 : ℝ) ^ (1 / 2 : ℝ) / Real.Gamma (1 / 2)
            * (x ^ ((1 / 2 : ℝ) - 1) * Real.exp (-((t + 1 / 2) * x))) := by
          rw [hexp]; ring
  rw [setIntegral_congr_fun measurableSet_Ioi hfun, integral_const_mul,
    Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1 / 2) (r := t + 1 / 2) (by norm_num) hr]
  have hG : (Real.Gamma (1 / 2)) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have hpos : (0 : ℝ) < 1 + 2 * t := by linarith
  have hA : ((1 / 2 : ℝ) ^ (1 / 2 : ℝ)) * ((1 / (t + 1 / 2)) ^ (1 / 2 : ℝ))
      = (1 / (1 + 2 * t)) ^ (1 / 2 : ℝ) := by
    have h1 : (t + 1 / 2) ≠ 0 := by linarith
    have h2 : (1 + 2 * t) ≠ 0 := by linarith
    have hp : (0:ℝ) ≤ 1 / (t + 1 / 2) := by
      have : (0:ℝ) < t + 1/2 := by linarith
      positivity
    rw [← Real.mul_rpow (by norm_num) hp]
    congr 1
    rw [mul_one_div, div_eq_div_iff h1 h2]
    ring
  have hB : (1 / (1 + 2 * t)) ^ (1 / 2 : ℝ) = 1 / Real.sqrt (1 + 2 * t) := by
    rw [one_div, Real.inv_rpow (le_of_lt hpos), Real.sqrt_eq_rpow, one_div]
    simp
  calc ((1 / 2 : ℝ) ^ (1 / 2 : ℝ) / Real.Gamma (1 / 2))
        * ((1 / (t + 1 / 2)) ^ (1 / 2 : ℝ) * Real.Gamma (1 / 2))
      = ((1 / 2 : ℝ) ^ (1 / 2 : ℝ) * (1 / (t + 1 / 2)) ^ (1 / 2 : ℝ))
          * ((Real.Gamma (1 / 2))⁻¹ * Real.Gamma (1 / 2)) := by ring
    _ = ((1 / 2 : ℝ) ^ (1 / 2 : ℝ) * (1 / (t + 1 / 2)) ^ (1 / 2 : ℝ)) := by
        rw [inv_mul_cancel₀ hG, mul_one]
    _ = (1 / (1 + 2 * t)) ^ (1 / 2 : ℝ) := hA
    _ = 1 / Real.sqrt (1 + 2 * t) := hB

/-! ### Fubini: the profile integral is the integral of the Laplace transform -/

/-- **Frullani + Fubini.** For a probability law on `(0,∞)`,
`∫ (∫_0^λ e^{-tx} dt) dμ(x) = ∫_0^λ (∫ e^{-tx} dμ(x)) dt`. -/
theorem integral_laplaceProfile_eq {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hsupp : μ (Set.Iic 0) = 0) {lam : ℝ} (hlam : 0 ≤ lam) :
    ∫ x, laplaceProfile lam x ∂μ
      = ∫ t, (∫ x, Real.exp (-(t * x)) ∂μ) ∂(volume.restrict (Set.Ioc 0 lam)) := by
  have hpos : ∀ᵐ x ∂μ, 0 < x := ae_pos_of_Iic hsupp
  have : IsFiniteMeasure (volume.restrict (Set.Ioc 0 lam)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioc]; exact ENNReal.ofReal_lt_top⟩
  have hInt : Integrable (Function.uncurry (fun x t : ℝ => Real.exp (-(t * x))))
      (μ.prod (volume.restrict (Set.Ioc 0 lam))) := by
    refine Integrable.of_bound ?_ 1 ?_
    · exact (by fun_prop : Measurable (Function.uncurry fun x t : ℝ => Real.exp (-(t * x)))).aestronglyMeasurable
    · rw [Measure.ae_prod_iff_ae_ae]
      · filter_upwards [hpos] with x hx
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        have ht0 : (0 : ℝ) ≤ t := le_of_lt ht.1
        have hle : Real.exp (-(t * x)) ≤ 1 := by
          rw [Real.exp_le_one_iff]; nlinarith
        rw [Function.uncurry_apply_pair, Real.norm_of_nonneg (Real.exp_pos _).le]
        exact hle
      · measurability
  have hswap := integral_integral_swap (μ := μ) (ν := volume.restrict (Set.Ioc 0 lam))
    (f := fun x t : ℝ => Real.exp (-(t * x))) hInt
  rw [← hswap]
  refine integral_congr_ae ?_
  filter_upwards with x
  rw [laplaceProfile, intervalIntegral.integral_of_le hlam]

/-- `∫_0^λ (1+2t)^{-1/2} dt = √(1+2λ) - 1`. -/
lemma integral_inv_sqrt_one_add_two_mul {lam : ℝ} (hlam : 0 ≤ lam) :
    ∫ t in (0)..lam, (Real.sqrt (1 + 2 * t))⁻¹ = Real.sqrt (1 + 2 * lam) - 1 := by
  have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) lam,
      HasDerivAt (fun t => Real.sqrt (1 + 2 * t)) ((Real.sqrt (1 + 2 * t))⁻¹) t := by
    intro t ht
    have ht0 : (0:ℝ) ≤ t := by
      rw [Set.uIcc_of_le hlam] at ht
      exact ht.1
    have hpos : (0:ℝ) < 1 + 2 * t := by linarith
    have hlin : HasDerivAt (fun t : ℝ => 1 + 2 * t) 2 t := by
      simpa using (hasDerivAt_id t).const_mul 2 |>.const_add 1
    have hs := hlin.sqrt hpos.ne'
    refine hs.congr_deriv ?_
    field_simp
  have hInt : IntervalIntegrable (fun t : ℝ => (Real.sqrt (1 + 2 * t))⁻¹) volume 0 lam := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hlam]
    apply ContinuousOn.inv₀ (by fun_prop)
    intro t ht
    have : (0:ℝ) < 1 + 2 * t := by linarith [ht.1]
    positivity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hInt]
  norm_num

/-- **The chi-square tail integral.** `∫_0^∞ (1-e^{-λx})/x dQ∞(x) = √(2λ+1) - 1`. -/
theorem integral_one_sub_exp_div_gammaMeasure_one_half {lam : ℝ} (hlam : 0 ≤ lam) :
    ∫ x, (1 - Real.exp (-(lam * x))) / x ∂(gammaMeasure (1 / 2) (1 / 2))
      = Real.sqrt (1 + 2 * lam) - 1 := by
  have hsupp : gammaMeasure (1 / 2) (1 / 2) (Set.Iic 0) = 0 := gammaMeasure_one_half_Iic_zero
  have : IsProbabilityMeasure (gammaMeasure (1 / 2) (1 / 2)) :=
    isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  have hpos : ∀ᵐ x ∂(gammaMeasure (1 / 2) (1 / 2)), 0 < x := ae_pos_of_Iic hsupp
  have hstep : ∫ x, (1 - Real.exp (-(lam * x))) / x ∂(gammaMeasure (1 / 2) (1 / 2))
      = ∫ x, laplaceProfile lam x ∂(gammaMeasure (1 / 2) (1 / 2)) := by
    refine integral_congr_ae ?_
    filter_upwards [hpos] with x hx
    exact (laplaceProfile_of_ne (ne_of_gt hx)).symm
  rw [hstep, integral_laplaceProfile_eq hsupp hlam]
  have hfun : ∀ t ∈ Set.Ioc (0:ℝ) lam,
      (∫ x, Real.exp (-(t * x)) ∂(gammaMeasure (1 / 2) (1 / 2))) = (Real.sqrt (1 + 2 * t))⁻¹ := by
    intro t ht
    have ht' : -(1 / 2 : ℝ) < t := by linarith [ht.1]
    rw [integral_exp_neg_mul_gammaMeasure_one_half ht', one_div]
  rw [setIntegral_congr_fun measurableSet_Ioc hfun, ← intervalIntegral.integral_of_le hlam]
  exact integral_inv_sqrt_one_add_two_mul hlam

/-! ### Transfer of the tail integral along weakly convergent laws on `(0,∞)`

This is the step from "the moments of `Q_r` converge to `(2p-1)!!`" (hence `Q_r → Q∞`, by
moment determinacy) to the value of `∫ (1-e^{-λx})/x dQ_r`, as used in (I.3.7). -/

/-- `x ↦ laplaceProfile lam (max x 0)` as a bounded continuous function, when `lam ≥ 0`. -/
noncomputable def laplaceProfileBCF {lam : ℝ} (hlam : 0 ≤ lam) : ℝ →ᵇ ℝ :=
  ⟨⟨fun x => laplaceProfile lam (max x 0), (continuous_laplaceProfile lam).comp (by fun_prop)⟩,
    ⟨lam, fun x y => by
      have hx0 : 0 ≤ laplaceProfile lam (max x 0) := laplaceProfile_nonneg hlam _
      have hx1 : laplaceProfile lam (max x 0) ≤ lam := laplaceProfile_le hlam (le_max_right _ _)
      have hy0 : 0 ≤ laplaceProfile lam (max y 0) := laplaceProfile_nonneg hlam _
      have hy1 : laplaceProfile lam (max y 0) ≤ lam := laplaceProfile_le hlam (le_max_right _ _)
      rw [Real.dist_eq, abs_sub_le_iff]
      constructor <;> linarith⟩⟩

@[simp]
lemma laplaceProfileBCF_apply {lam : ℝ} (hlam : 0 ≤ lam) (x : ℝ) :
    laplaceProfileBCF hlam x = laplaceProfile lam (max x 0) := rfl

/-- The profile of a law carried by `(0,∞)` agrees with `(1-e^{-λx})/x`. -/
lemma integral_laplaceProfile_eq_integral_one_sub_exp {μ : Measure ℝ}
    (hsupp : μ (Set.Iic 0) = 0) {lam : ℝ} :
    ∫ x, laplaceProfile lam x ∂μ = ∫ x, (1 - Real.exp (-(lam * x))) / x ∂μ := by
  refine integral_congr_ae ?_
  filter_upwards [ae_pos_of_Iic hsupp] with x hx
  exact laplaceProfile_of_ne (ne_of_gt hx)

/-- **Transfer along weak convergence.** If probability laws `μ i` on `(0,∞)`, indexed by an
arbitrary filter `l` (e.g. `l = atTop` for `r → ∞`, or `l = 𝓝[>] 0` for `h ↓ 0`), converge weakly
to a law `μlim` on `(0,∞)`, then `∫ (1-e^{-λx})/x dμ i → ∫ (1-e^{-λx})/x dμlim` along `l`.

No moment bound (hence no uniform integrability) is needed: the argument is that
`∫ (1-e^{-λx})/x dμ i = ∫_0^λ (∫ e^{-tx} dμ i) dt` by Fubini against the bounded kernel
`(x,t) ↦ e^{-tx}` on `(0,∞) × (0,λ)`, and each `x ↦ ∫_0^λ e^{-tx} dt = laplaceProfile lam x` extends
to the bounded continuous function `x ↦ laplaceProfile lam (max x 0)` on `ℝ`. -/
theorem tendsto_integral_one_sub_exp_div_of_tendsto
    {ι : Type*} {l : Filter ι} {μ : ι → ProbabilityMeasure ℝ} {μlim : ProbabilityMeasure ℝ}
    (hsupp : ∀ i, (μ i : Measure ℝ) (Set.Iic 0) = 0)
    (hsupplim : (μlim : Measure ℝ) (Set.Iic 0) = 0)
    (hconv : Tendsto μ l (𝓝 μlim)) {lam : ℝ} (hlam : 0 ≤ lam) :
    Tendsto (fun i => ∫ x, (1 - Real.exp (-(lam * x))) / x ∂((μ i : Measure ℝ))) l
      (𝓝 (∫ x, (1 - Real.exp (-(lam * x))) / x ∂(μlim : Measure ℝ))) := by
  have hfun : ∀ i, ∫ x, (1 - Real.exp (-(lam * x))) / x ∂((μ i : Measure ℝ))
      = ∫ x, laplaceProfileBCF hlam x ∂((μ i : Measure ℝ)) := by
    intro i
    rw [← integral_laplaceProfile_eq_integral_one_sub_exp (hsupp i)]
    refine integral_congr_ae ?_
    filter_upwards [ae_pos_of_Iic (hsupp i)] with x hx
    rw [laplaceProfileBCF_apply, max_eq_left hx.le]
  have hfunlim : ∫ x, (1 - Real.exp (-(lam * x))) / x ∂(μlim : Measure ℝ)
      = ∫ x, laplaceProfileBCF hlam x ∂(μlim : Measure ℝ) := by
    rw [← integral_laplaceProfile_eq_integral_one_sub_exp hsupplim]
    refine integral_congr_ae ?_
    filter_upwards [ae_pos_of_Iic hsupplim] with x hx
    rw [laplaceProfileBCF_apply, max_eq_left hx.le]
  rw [hfunlim]
  simp_rw [hfun]
  exact (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hconv) (laplaceProfileBCF hlam)

/-! ### The `√2` asymptotics -/

/-- `(√(1+2λ) - 1)/√λ → √2` as `λ → ∞`. -/
lemma tendsto_sqrt_one_add_two_mul_sub_one_div_sqrt :
    Tendsto (fun lam : ℝ => (Real.sqrt (1 + 2 * lam) - 1) / Real.sqrt lam) atTop
      (𝓝 (Real.sqrt 2)) := by
  have hinv : Tendsto (fun lam : ℝ => lam⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hfirst : Tendsto (fun lam : ℝ => Real.sqrt (2 + lam⁻¹)) atTop (𝓝 (Real.sqrt 2)) := by
    have hone : Tendsto (fun _ : ℝ => (2:ℝ)) atTop (𝓝 2) := tendsto_const_nhds
    have h : Tendsto (fun lam : ℝ => 2 + lam⁻¹) atTop (𝓝 2) := by
      simpa using hone.add hinv
    exact Real.continuous_sqrt.continuousAt.tendsto.comp h
  have hsecond : Tendsto (fun lam : ℝ => (Real.sqrt lam)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  have h : Tendsto (fun lam : ℝ => Real.sqrt (2 + lam⁻¹) - (Real.sqrt lam)⁻¹) atTop
      (𝓝 (Real.sqrt 2)) := by
    simpa using hfirst.sub hsecond
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with lam hlam
  have hlam' := hlam
  have hsqrt : (0:ℝ) < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hdiv : (1 + 2 * lam) / lam = 2 + lam⁻¹ := by
    field_simp
    ring
  rw [← hdiv, Real.sqrt_div' (1 + 2 * lam) hlam.le]
  field_simp

/-- **The `√2` constant.** `λ^{-1/2} ∫ (1-e^{-λx})/x dQ∞(x) → √2`. -/
theorem tendsto_integral_one_sub_exp_div_div_sqrt :
    Tendsto (fun lam : ℝ =>
        (∫ x, (1 - Real.exp (-(lam * x))) / x ∂(gammaMeasure (1 / 2) (1 / 2)))
          / Real.sqrt lam) atTop (𝓝 (Real.sqrt 2)) := by
  refine tendsto_sqrt_one_add_two_mul_sub_one_div_sqrt.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with lam hlam
  rw [integral_one_sub_exp_div_gammaMeasure_one_half hlam.le]


/-! ### The paper's displayed form of the tail integral

Hutchcroft (arXiv:2508.18807v1), p. 32, writes the identity with the chi-square density expanded as
`(1/√(2π)) ∫_0^∞ (1-e^{-λx}) e^{-x/2} x^{-3/2} dx`. The `x^{-3/2}` is not a typo for `x^{-1/2}`:
the extra `x^{-1}` is the `1/x` in the integrand. The corollary below verifies the displayed formula
literally.
-/


lemma gammaPDFReal_one_half_eq {x : ℝ} (hx : 0 < x) :
    gammaPDFReal (1 / 2) (1 / 2) x
      = (1 / Real.sqrt (2 * Real.pi)) * (Real.exp (-(x / 2)) * x ^ (-(1/2) : ℝ)) := by
  have hconst : (1 / 2 : ℝ) ^ (1 / 2 : ℝ) / Real.Gamma (1 / 2) = 1 / Real.sqrt (2 * Real.pi) := by
    rw [Real.Gamma_one_half_eq]
    have h1 : (1 / 2 : ℝ) ^ (1 / 2 : ℝ) = 1 / Real.sqrt 2 := by
      rw [one_div, Real.inv_rpow (by norm_num), Real.sqrt_eq_rpow (2:ℝ), one_div]
      norm_num
    rw [h1, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) Real.pi]
    have h2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have h3 : (0:ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    field_simp
  rw [gammaPDFReal, ite_eq_left hx.le, hconst]
  have hpow : x ^ ((1 / 2 : ℝ) - 1) = x ^ (-(1/2) : ℝ) := by
    congr 1
    ring
  rw [hpow]
  have hexp : (1 / 2 : ℝ) * x = x / 2 := by ring
  rw [hexp]
  ring

/-- **The tail integral in the paper's displayed form.** With the chi-square density written out,
`(1/√(2π)) ∫_0^∞ (1-e^{-λx}) e^{-x/2} x^{-3/2} dx = √(2λ+1) - 1`. -/
theorem integral_one_sub_exp_mul_exp_neg_half_rpow {lam : ℝ} (hlam : 0 ≤ lam) :
    (1 / Real.sqrt (2 * Real.pi)) *
      ∫ x in Set.Ioi (0:ℝ),
        (1 - Real.exp (-(lam * x))) * Real.exp (-(x / 2)) * x ^ (-(3/2) : ℝ)
      = Real.sqrt (1 + 2 * lam) - 1 := by
  have ha : (0 : ℝ) < 1 / 2 := by norm_num
  rw [← integral_one_sub_exp_div_gammaMeasure_one_half hlam]
  have hpoint : ∀ x ∈ Set.Ioi (0:ℝ),
      (gammaPDF (1 / 2) (1 / 2) x).toReal * ((1 - Real.exp (-(lam * x))) / x)
        = (1 / Real.sqrt (2 * Real.pi)) *
            ((1 - Real.exp (-(lam * x))) * Real.exp (-(x / 2)) * x ^ (-(3/2) : ℝ)) := by
    intro x hx
    have hx0 : (0:ℝ) < x := hx
    rw [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha ha x), gammaPDFReal_one_half_eq hx0]
    have hcomb : x⁻¹ * x ^ (-(1/2) : ℝ) = x ^ (-(3/2) : ℝ) := by
      rw [← Real.rpow_neg_one x, ← Real.rpow_add hx0]
      norm_num
    rw [div_eq_mul_inv]
    calc (1 / Real.sqrt (2 * Real.pi)) * (Real.exp (-(x / 2)) * x ^ (-(1/2) : ℝ))
          * ((1 - Real.exp (-(lam * x))) * x⁻¹)
        = (1 / Real.sqrt (2 * Real.pi)) * ((1 - Real.exp (-(lam * x))) * Real.exp (-(x / 2)))
            * (x⁻¹ * x ^ (-(1/2) : ℝ)) := by ring
      _ = (1 / Real.sqrt (2 * Real.pi)) * ((1 - Real.exp (-(lam * x))) * Real.exp (-(x / 2)))
            * x ^ (-(3/2) : ℝ) := by rw [hcomb]
      _ = (1 / Real.sqrt (2 * Real.pi)) *
            ((1 - Real.exp (-(lam * x))) * Real.exp (-(x / 2)) * x ^ (-(3/2) : ℝ)) := by ring
  have hzero : ∀ x : ℝ, x ∉ Set.Ioi (0:ℝ) →
      gammaPDFReal (1 / 2) (1 / 2) x * ((1 - Real.exp (-(lam * x))) / x) = 0 := by
    intro x hx
    have hx' : x ≤ 0 := by simpa using hx
    rcases lt_or_eq_of_le hx' with h | h
    · rw [gammaPDFReal, ite_eq_right (by linarith : ¬ (0:ℝ) ≤ x), zero_mul]
    · subst h
      rw [gammaPDFReal, ite_eq_left le_rfl]
      have hz : (0:ℝ) ^ ((1/2:ℝ) - 1) = 0 := Real.zero_rpow (by norm_num)
      rw [hz]
      ring
  have hzero' : ∀ x : ℝ, x ∉ Set.Ioi (0:ℝ) →
      (gammaPDF (1 / 2) (1 / 2) x).toReal * ((1 - Real.exp (-(lam * x))) / x) = 0 := by
    intro x hx
    rw [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha ha x)]
    exact hzero x hx
  rw [gammaMeasure, integral_withDensity_eq_integral_toReal_smul (measurable_gammaPDF' _ _)
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top) (fun x => (1 - Real.exp (-(lam * x))) / x)]
  simp only [smul_eq_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Ioi (0:ℝ)) hzero',
    setIntegral_congr_fun measurableSet_Ioi hpoint, integral_const_mul]







/-- `x ↦ min (max (-x) 0) 1` as a bounded continuous function: it is `0` on `[0,∞)` and strictly
positive on `(-∞,0)`. -/
noncomputable def negPartBCF : ℝ →ᵇ ℝ :=
  ⟨⟨fun x => min (max (-x) 0) 1, by fun_prop⟩, ⟨1, fun x y => by
    have hx0 : 0 ≤ min (max (-x) 0) 1 := le_min (le_max_right _ _) zero_le_one
    have hx1 : min (max (-x) 0) 1 ≤ 1 := min_le_right _ _
    have hy0 : 0 ≤ min (max (-y) 0) 1 := le_min (le_max_right _ _) zero_le_one
    have hy1 : min (max (-y) 0) 1 ≤ 1 := min_le_right _ _
    rw [Real.dist_eq, abs_sub_le_iff]
    constructor <;> linarith⟩⟩

@[simp] lemma negPartBCF_apply (x : ℝ) : negPartBCF x = min (max (-x) 0) 1 := rfl

lemma negPartBCF_eq_zero {x : ℝ} (hx : 0 ≤ x) : negPartBCF x = 0 := by
  rw [negPartBCF_apply, max_eq_right (by linarith : -x ≤ 0), min_eq_left zero_le_one]

/-- A measure vanishing on `(-∞,0)` is almost everywhere carried by `[0,∞)`. -/
lemma ae_nonneg_of_Iio {μ : Measure ℝ} (h : μ (Set.Iio 0) = 0) : ∀ᵐ x ∂μ, 0 ≤ x := by
  rw [ae_iff]
  have hset : {x : ℝ | ¬ (0 ≤ x)} = Set.Iio 0 := by
    simp [Set.Iio]
  rw [hset]
  exact h

lemma negPartBCF_pos {x : ℝ} (hx : x < 0) : 0 < negPartBCF x := by
  rw [negPartBCF_apply]
  have h1 : 0 < max (-x) 0 := lt_max_of_lt_left (by linarith)
  exact lt_min h1 zero_lt_one

/-- **The weak limit of laws on `(0,∞)` is carried by `[0,∞)`.** -/
theorem measure_Iio_zero_of_tendsto
    {Q : ℕ → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ}
    (hsupp : ∀ n, (Q n : Measure ℝ) (Set.Iio 0) = 0)
    (hconv : Tendsto Q atTop (𝓝 ν)) :
    (ν : Measure ℝ) (Set.Iio 0) = 0 := by
  have hzero : ∀ n, ∫ x, negPartBCF x ∂((Q n : Measure ℝ)) = 0 := by
    intro n
    refine integral_eq_zero_of_ae ?_
    filter_upwards [ae_nonneg_of_Iio (hsupp n)] with x hx
    exact negPartBCF_eq_zero hx
  have hlim : ∫ x, negPartBCF x ∂(ν : Measure ℝ) = 0 := by
    have h := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hconv) negPartBCF
    rw [show (fun n => ∫ x, negPartBCF x ∂((Q n : Measure ℝ))) = fun _ => 0 from funext hzero]
      at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  -- a nonnegative function with vanishing integral vanishes almost everywhere
  have hint : Integrable (fun x => negPartBCF x) (ν : Measure ℝ) :=
    Integrable.of_bound negPartBCF.continuous.aestronglyMeasurable 1 (ae_of_all _ fun x => by
      rw [negPartBCF_apply, Real.norm_of_nonneg (le_min (le_max_right _ _) zero_le_one)]
      exact min_le_right _ _)
  have hae : ∀ᵐ x ∂(ν : Measure ℝ), negPartBCF x = 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x => le_min (le_max_right _ _) zero_le_one) hint).mp hlim
  have hsub : Set.Iio (0:ℝ) ⊆ {x : ℝ | ¬ negPartBCF x = 0} := by
    intro x hx
    exact ne_of_gt (negPartBCF_pos hx)
  exact measure_mono_null hsub (ae_iff.mp hae)



noncomputable def cutoff (s : ℝ) : ℝ := min (max (2 - s) 0) 1

lemma cutoff_nonneg (s : ℝ) : 0 ≤ cutoff s := le_min (le_max_right _ _) zero_le_one
lemma cutoff_le_one (s : ℝ) : cutoff s ≤ 1 := min_le_right _ _
lemma cutoff_eq_one {s : ℝ} (hs : s ≤ 1) : cutoff s = 1 := by
  rw [cutoff, max_eq_left (by linarith : (0:ℝ) ≤ 2 - s), min_eq_right (by linarith : (1:ℝ) ≤ 2 - s)]
lemma cutoff_eq_zero {s : ℝ} (hs : 2 ≤ s) : cutoff s = 0 := by
  rw [cutoff, max_eq_right (by linarith : 2 - s ≤ 0), min_eq_left zero_le_one]
lemma continuous_cutoff : Continuous cutoff := by unfold cutoff; fun_prop

noncomputable def powCut (p : ℕ) (R x : ℝ) : ℝ := (max x 0) ^ p * cutoff (x / R)

lemma continuous_powCut (p : ℕ) (R : ℝ) : Continuous (powCut p R) := by
  have h : powCut p R = fun x => (max x 0) ^ p * cutoff (x / R) := rfl
  rw [h]
  exact ((continuous_id.max continuous_const).pow p).mul
    (continuous_cutoff.comp (continuous_id.div_const R))

lemma powCut_nonneg (p : ℕ) (R x : ℝ) : 0 ≤ powCut p R x :=
  mul_nonneg (by positivity) (cutoff_nonneg _)

lemma powCut_le_pow {p : ℕ} {R x : ℝ} (hx : 0 ≤ x) : powCut p R x ≤ x ^ p := by
  rw [powCut, max_eq_left hx]
  exact mul_le_of_le_one_right (by positivity) (cutoff_le_one _)

lemma powCut_eq_pow {p : ℕ} {R x : ℝ} (hx0 : 0 ≤ x) (hxR : x ≤ R) :
    powCut p R x = x ^ p := by
  have hdiv : x / R ≤ 1 := by
    rcases le_or_gt R 0 with hR | hR
    · have hx : x = 0 := le_antisymm (le_trans hxR hR) hx0
      subst hx; simp
    · rw [div_le_one hR]; exact hxR
  rw [powCut, max_eq_left hx0, cutoff_eq_one hdiv, mul_one]

lemma pow_sub_powCut_le {p : ℕ} {R x : ℝ} (hR : 0 < R) (hx : 0 ≤ x) :
    x ^ p - powCut p R x ≤ x ^ (p + 1) / R := by
  rcases le_or_gt x R with hxR | hxR
  · rw [powCut_eq_pow hx hxR, sub_self]
    positivity
  · have h3 : x ^ p ≤ x ^ (p + 1) / R := by
      rw [le_div_iff₀ hR, pow_succ]
      exact mul_le_mul_of_nonneg_left hxR.le (by positivity)
    linarith [powCut_nonneg p R x]

noncomputable def powCutBCF (p : ℕ) (R : ℝ) (hR : 0 < R) : ℝ →ᵇ ℝ :=
  ⟨⟨fun x => powCut p R x, continuous_powCut p R⟩, ⟨(2 * R) ^ p, fun x y => by
    have hb : ∀ z : ℝ, 0 ≤ powCut p R z ∧ powCut p R z ≤ (2 * R) ^ p := by
      intro z
      refine ⟨powCut_nonneg p R z, ?_⟩
      rcases le_or_gt z (2 * R) with hz | hz
      · rw [powCut]
        calc (max z 0) ^ p * cutoff (z / R) ≤ (2 * R) ^ p * 1 := by
              refine mul_le_mul (pow_le_pow_left₀ (by positivity) (max_le hz (by positivity)) p)
                (cutoff_le_one _) (cutoff_nonneg _) (by positivity)
          _ = (2 * R) ^ p := mul_one _
      · rw [powCut, cutoff_eq_zero (by rw [le_div_iff₀ hR]; linarith), mul_zero]
        positivity
    obtain ⟨hx0, hx1⟩ := hb x
    obtain ⟨hy0, hy1⟩ := hb y
    rw [Real.dist_eq, abs_sub_le_iff]
    constructor <;> linarith⟩⟩

@[simp] lemma powCutBCF_apply (p : ℕ) (R : ℝ) (hR : 0 < R) (x : ℝ) :
    powCutBCF p R hR x = powCut p R x := rfl

/-- **Passage of one polynomial moment under weak convergence**, given a uniform bound on the next
moment: `∫ x^p dQₙ → ∫ x^p dν`. -/
theorem tendsto_integral_pow_of_uniform_bound
    {Q : ℕ → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ} {p : ℕ} {C : ℝ}
    (hC : 0 ≤ C)
    (hsupp : ∀ n, (Q n : Measure ℝ) (Set.Iio 0) = 0)
    (hconv : Tendsto Q atTop (𝓝 ν))
    (hintp : ∀ n, Integrable (fun x => x ^ p) (Q n : Measure ℝ))
    (hint1 : ∀ n, Integrable (fun x => x ^ (p + 1)) (Q n : Measure ℝ))
    (hbound : ∀ n, ∫ x, x ^ (p + 1) ∂(Q n : Measure ℝ) ≤ C)
    (hνintp : Integrable (fun x => x ^ p) (ν : Measure ℝ)) :
    Tendsto (fun n => ∫ x, x ^ p ∂(Q n : Measure ℝ)) atTop (𝓝 (∫ x, x ^ p ∂(ν : Measure ℝ))) := by
  have hνnn : ∀ᵐ x ∂(ν : Measure ℝ), 0 ≤ x := ae_nonneg_of_Iio (measure_Iio_zero_of_tendsto hsupp hconv)
  have htrunc : ∀ R : ℝ, 0 < R → Tendsto (fun n => ∫ x, powCut p R x ∂(Q n : Measure ℝ)) atTop
      (𝓝 (∫ x, powCut p R x ∂(ν : Measure ℝ))) := by
    intro R hR
    have h := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hconv) (powCutBCF p R hR)
    simpa using h
  have hsubQ : ∀ (n : ℕ) (R : ℝ), 0 < R → ∫ x, x ^ p - powCut p R x ∂(Q n : Measure ℝ)
      = ∫ x, x ^ p ∂(Q n : Measure ℝ) - ∫ x, powCut p R x ∂(Q n : Measure ℝ) :=
    fun n R hR => integral_sub (μ := (Q n : Measure ℝ)) (hintp n) (BoundedContinuousFunction.integrable (Q n : Measure ℝ) (powCutBCF p R hR))
  have hsubν : ∀ R : ℝ, 0 < R → ∫ x, x ^ p - powCut p R x ∂(ν : Measure ℝ)
      = ∫ x, x ^ p ∂(ν : Measure ℝ) - ∫ x, powCut p R x ∂(ν : Measure ℝ) :=
    fun R hR => integral_sub (μ := (ν : Measure ℝ)) hνintp (BoundedContinuousFunction.integrable (ν : Measure ℝ) (powCutBCF p R hR))
  -- nonnegativity and size of the truncation error, for `R > 0`
  have herr : ∀ (n : ℕ) (R : ℝ), 0 < R →
      0 ≤ ∫ x, x ^ p ∂(Q n : Measure ℝ) - ∫ x, powCut p R x ∂(Q n : Measure ℝ) ∧
      ∫ x, x ^ p ∂(Q n : Measure ℝ) - ∫ x, powCut p R x ∂(Q n : Measure ℝ) ≤ C / R := by
    intro n R hR
    constructor
    · rw [← hsubQ n R hR]
      refine integral_nonneg_of_ae ?_
      filter_upwards [ae_nonneg_of_Iio (hsupp n)] with x hx
      exact sub_nonneg.mpr (powCut_le_pow (p := p) (R := R) hx)
    · have hpt : ∀ᵐ x ∂(Q n : Measure ℝ), x ^ p - powCut p R x ≤ x ^ (p + 1) / R :=
        (ae_nonneg_of_Iio (hsupp n)).mono fun x hx => pow_sub_powCut_le hR hx
      have hmono : ∫ x, x ^ p - powCut p R x ∂(Q n : Measure ℝ)
          ≤ ∫ x, x ^ (p + 1) / R ∂(Q n : Measure ℝ) :=
        integral_mono_ae (μ := (Q n : Measure ℝ))
          ((hintp n).sub (BoundedContinuousFunction.integrable (Q n : Measure ℝ) (powCutBCF p R hR))) ((hint1 n).div_const R) hpt
      have hdiv : ∫ x, x ^ (p + 1) / R ∂(Q n : Measure ℝ)
          = (∫ x, x ^ (p + 1) ∂(Q n : Measure ℝ)) / R := by
        rw [show (fun x : ℝ => x ^ (p + 1) / R) = (fun x : ℝ => x ^ (p + 1) * R⁻¹) from by
          funext x; rw [div_eq_mul_inv], integral_mul_const, div_eq_mul_inv]
      rw [← hsubQ n R hR]
      refine le_trans hmono ?_
      rw [hdiv, div_le_div_iff_of_pos_right hR]
      exact hbound n
  have hνnonneg : ∀ R : ℝ, 0 < R → 0 ≤ ∫ x, x ^ p ∂(ν : Measure ℝ)
      - ∫ x, powCut p R x ∂(ν : Measure ℝ) := by
    intro R hR
    rw [← hsubν R hR]
    refine integral_nonneg_of_ae ?_
    filter_upwards [hνnn] with x hx
    exact sub_nonneg.mpr (powCut_le_pow (p := p) (R := R) hx)
  -- the truncation error in `ν` tends to `0`
  have hνerr : Tendsto (fun n : ℕ => ∫ x, x ^ p ∂(ν : Measure ℝ)
      - ∫ x, powCut p ((n : ℝ) + 1) x ∂(ν : Measure ℝ)) atTop (𝓝 0) := by
    have hmeas : ∀ n : ℕ, AEStronglyMeasurable
        (fun x => x ^ p - powCut p ((n : ℝ) + 1) x) (ν : Measure ℝ) :=
      fun n => ((continuous_id.pow p).sub (continuous_powCut p _)).aestronglyMeasurable
    have hbdd : ∀ n : ℕ, ∀ᵐ x ∂(ν : Measure ℝ),
        ‖x ^ p - powCut p ((n : ℝ) + 1) x‖ ≤ x ^ p := by
      intro n
      filter_upwards [hνnn] with x hx
      have h3 := powCut_le_pow (p := p) (R := (n : ℝ) + 1) hx
      have h4 := powCut_nonneg p ((n : ℝ) + 1) x
      rw [Real.norm_of_nonneg (sub_nonneg.mpr h3)]
      linarith
    have hlim : ∀ᵐ x ∂(ν : Measure ℝ),
        Tendsto (fun n : ℕ => x ^ p - powCut p ((n : ℝ) + 1) x) atTop (𝓝 0) := by
      filter_upwards [hνnn] with x hx
      have hev : ∀ᶠ n : ℕ in atTop, powCut p ((n : ℝ) + 1) x = x ^ p := by
        filter_upwards [eventually_ge_atTop ⌈x⌉₊] with n hn
        refine powCut_eq_pow hx (le_of_lt ?_)
        have h1 : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
        have h2 : (⌈x⌉₊ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        linarith
      have hzero : Tendsto (fun n : ℕ => x ^ p - powCut p ((n : ℝ) + 1) x) atTop (𝓝 (x ^ p - x ^ p)) :=
        Tendsto.const_sub _ (Tendsto.congr' (hev.mono fun n hn => hn.symm) tendsto_const_nhds)
      simpa using hzero
    have hDCT := tendsto_integral_of_dominated_convergence (μ := (ν : Measure ℝ))
      (F := fun (n : ℕ) (x : ℝ) => x ^ p - powCut p ((n : ℝ) + 1) x)
      (f := fun _ => (0 : ℝ)) (fun x => x ^ p) hmeas hνintp hbdd hlim
    have hDCT' : Tendsto (fun n : ℕ => ∫ x, x ^ p - powCut p ((n : ℝ) + 1) x ∂(ν : Measure ℝ))
        atTop (𝓝 0) := by simpa using hDCT
    refine hDCT'.congr' ?_
    filter_upwards with n
    exact hsubν ((n : ℝ) + 1) (by positivity)
  -- the `ε`-argument
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε3 : (0 : ℝ) < ε / 3 := by linarith
  have hCdiv : Tendsto (fun n : ℕ => C / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun n : ℕ => C * (((n : ℝ) + 1))⁻¹) atTop (𝓝 (C * 0)) :=
      tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp h1)
    simpa [div_eq_mul_inv] using h2
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp hνerr (ε / 3) hε3
  obtain ⟨N₂, hN₂⟩ := Metric.tendsto_atTop.mp hCdiv (ε / 3) hε3
  set N : ℕ := max N₁ N₂ with hNdef
  set R : ℝ := (N : ℝ) + 1 with hRdef
  have hR : 0 < R := by positivity
  obtain ⟨N₃, hN₃⟩ := Metric.tendsto_atTop.mp (htrunc R hR) (ε / 3) hε3
  refine ⟨max N N₃, fun n hn => ?_⟩
  have hnN : N ≤ n := le_trans (le_max_left _ _) hn
  have hnN₃ : N₃ ≤ n := le_trans (le_max_right _ _) hn
  -- the three error terms
  have hA : 0 ≤ ∫ x, x ^ p ∂(Q n : Measure ℝ) - ∫ x, powCut p R x ∂(Q n : Measure ℝ) := (herr n R hR).1
  have hB : ∫ x, x ^ p ∂(Q n : Measure ℝ) - ∫ x, powCut p R x ∂(Q n : Measure ℝ) ≤ C / R := (herr n R hR).2
  have hCb : C / R ≤ ε / 3 := by
    have h := hN₂ N (le_max_right N₁ N₂)
    rw [Real.dist_eq] at h
    rw [sub_zero, abs_of_nonneg (div_nonneg hC (by positivity))] at h
    rw [hRdef]
    exact le_of_lt h
  have hD : 0 ≤ ∫ x, x ^ p ∂(ν : Measure ℝ) - ∫ x, powCut p R x ∂(ν : Measure ℝ) := hνnonneg R hR
  have hE : ∫ x, x ^ p ∂(ν : Measure ℝ) - ∫ x, powCut p R x ∂(ν : Measure ℝ) ≤ ε / 3 := by
    have h := hN₁ N (le_max_left N₁ N₂)
    rw [Real.dist_eq] at h
    rw [sub_zero, abs_of_nonneg (hνnonneg R hR)] at h
    rw [hRdef]
    exact le_of_lt h
  have hF : |∫ x, powCut p R x ∂(Q n : Measure ℝ) - ∫ x, powCut p R x ∂(ν : Measure ℝ)| ≤ ε / 3 := by
    have h := hN₃ n hnN₃
    rw [Real.dist_eq] at h
    exact le_of_lt h
  have key : ∫ x, x ^ p ∂(Q n : Measure ℝ) - ∫ x, x ^ p ∂(ν : Measure ℝ)
      = (∫ x, x ^ p ∂(Q n : Measure ℝ) - ∫ x, powCut p R x ∂(Q n : Measure ℝ))
        + (∫ x, powCut p R x ∂(Q n : Measure ℝ) - ∫ x, powCut p R x ∂(ν : Measure ℝ))
        - (∫ x, x ^ p ∂(ν : Measure ℝ) - ∫ x, powCut p R x ∂(ν : Measure ℝ)) := by ring
  rw [Real.dist_eq, key, abs_lt]
  constructor
  · nlinarith [hA, hB, hCb, hD, hE, hF, (abs_le.mp hF).1, (abs_le.mp hF).2]
  · nlinarith [hA, hB, hCb, hD, hE, hF, (abs_le.mp hF).1, (abs_le.mp hF).2]


/-! ### Tightness from a uniform first-moment bound -/

/-- A family of probability laws on `[0,∞)` with a uniform bound on the first moment is tight. -/
lemma isTightMeasureSet_range_of_uniform_first_moment
    {Q : ℕ → ProbabilityMeasure ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ n, ∫⁻ x, ENNReal.ofReal |x| ∂(Q n : Measure ℝ) ≤ ENNReal.ofReal C) :
    IsTightMeasureSet (Set.range (fun n => (Q n : Measure ℝ))) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  rcases eq_or_ne ε ⊤ with htop | htop
  · exact ⟨∅, isCompact_empty, fun μ _ => by rw [htop]; exact le_top⟩
  have he0 : 0 < ε.toNNReal := ENNReal.toNNReal_pos hε.ne' htop
  have hεeq : ENNReal.ofReal ((ε.toNNReal : ℝ≥0) : ℝ) = ε := by
    rw [ENNReal.ofReal_coe_nnreal]
    exact ENNReal.coe_toNNReal htop
  have he0' : (0:ℝ) < (ε.toNNReal : ℝ) := by exact_mod_cast he0
  set R : ℝ := C / (ε.toNNReal : ℝ) + 1 with hRdef
  have hR0 : 0 < R := by positivity
  refine ⟨Set.Icc (-R) R, isCompact_Icc, ?_⟩
  rintro μ ⟨n, rfl⟩
  have hmeas : AEMeasurable (fun x : ℝ => ENNReal.ofReal |x|) (Q n : Measure ℝ) := by fun_prop
  have hmarkov := meas_ge_le_lintegral_div (μ := (Q n : Measure ℝ))
    (f := fun x : ℝ => ENNReal.ofReal |x|) (ε := ENNReal.ofReal R) hmeas
    (by simpa using hR0) (by simp)
  have hsub : (Set.Icc (-R) R)ᶜ ⊆ {x : ℝ | ENNReal.ofReal R ≤ ENNReal.ofReal |x|} := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx
    simp only [Set.mem_ofPred_eq]
    rw [ENNReal.ofReal_le_ofReal_iff (abs_nonneg x)]
    rcases hx with h' | h'
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  calc (Q n : Measure ℝ) (Set.Icc (-R) R)ᶜ
      ≤ (Q n : Measure ℝ) {x : ℝ | ENNReal.ofReal R ≤ ENNReal.ofReal |x|} := measure_mono hsub
    _ ≤ (∫⁻ x, ENNReal.ofReal |x| ∂(Q n : Measure ℝ)) / ENNReal.ofReal R := hmarkov
    _ ≤ ENNReal.ofReal C / ENNReal.ofReal R := by
        gcongr
        exact h n
    _ = ENNReal.ofReal (C / R) := (ENNReal.ofReal_div_of_pos hR0).symm
    _ ≤ ENNReal.ofReal (ε.toNNReal) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hRdef, div_le_iff₀ (by positivity)]
        field_simp
        nlinarith [hC, he0'.le]
    _ = ε := hεeq

/-! ### Integrability of the limit moments from the portmanteau theorem -/

/-- **Uniform bound on the `p`-th moment passes to any weak limit** (portmanteau/Fatou), so the
limit has a finite `p`-th moment. -/
lemma integrable_pow_of_uniform_lintegral_bound
    {Q : ℕ → ProbabilityMeasure ℝ} {ν : ProbabilityMeasure ℝ} {p : ℕ} {C : ℝ}
    (hsupp : ∀ n, (Q n : Measure ℝ) (Set.Iio 0) = 0)
    (hconv : Tendsto Q atTop (𝓝 ν))
    (h : ∀ n, ∫⁻ x, ENNReal.ofReal (x ^ p) ∂(Q n : Measure ℝ) ≤ ENNReal.ofReal C) :
    Integrable (fun x => x ^ p) (ν : Measure ℝ) := by
  have hνnn : ∀ᵐ x ∂(ν : Measure ℝ), 0 ≤ x := ae_nonneg_of_Iio (measure_Iio_zero_of_tendsto hsupp hconv)
  have hFatou := lintegral_le_liminf_lintegral_of_forall_isOpen_measure_le_liminf_measure
    (μ := (ν : Measure ℝ)) (μs := fun n => (Q n : Measure ℝ)) (f := fun x : ℝ => (max x 0) ^ p)
    (by fun_prop) (fun x => by positivity)
    (fun G hG => ProbabilityMeasure.le_liminf_measure_open_of_tendsto hconv hG)
  -- the same lintegral, with `x^p` replaced by `(max x 0)^p`
  have hcongr : ∀ (μ : Measure ℝ), μ (Set.Iio 0) = 0 →
      ∫⁻ x, ENNReal.ofReal ((max x 0) ^ p) ∂μ = ∫⁻ x, ENNReal.ofReal (x ^ p) ∂μ := by
    intro μ hμ
    refine lintegral_congr_ae ?_
    filter_upwards [ae_nonneg_of_Iio hμ] with x hx
    rw [max_eq_left hx]
  rw [hcongr (ν : Measure ℝ) (measure_Iio_zero_of_tendsto hsupp hconv)] at hFatou
  have hliminf : atTop.liminf (fun n => ∫⁻ x, ENNReal.ofReal (x ^ p) ∂(Q n : Measure ℝ))
      ≤ ENNReal.ofReal C := by
    refine liminf_le_of_le ⟨0, Filter.Eventually.of_forall fun n => zero_le⟩ ?_
    intro b hb
    obtain ⟨N, hN⟩ := eventually_atTop.1 hb
    exact le_trans (hN N le_rfl) (h N)
  have hliminf' : atTop.liminf (fun n => ∫⁻ x, ENNReal.ofReal ((max x 0) ^ p) ∂(Q n : Measure ℝ))
      ≤ ENNReal.ofReal C := by
    refine le_trans (le_of_eq ?_) hliminf
    congr 1
    funext n
    exact hcongr (Q n : Measure ℝ) (hsupp n)
  have hfin : ∫⁻ x, ENNReal.ofReal (x ^ p) ∂(ν : Measure ℝ) < ⊤ :=
    lt_of_le_of_lt (le_trans hFatou hliminf') ENNReal.ofReal_lt_top
  refine ⟨(by fun_prop : Measurable fun x : ℝ => x ^ p).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  refine lt_of_le_of_lt ?_ hfin
  refine lintegral_mono_ae ?_
  filter_upwards [hνnn] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]

/-- The chi-square law with one degree of freedom, as a probability measure. -/
noncomputable def chiSqPM : ProbabilityMeasure ℝ :=
  ⟨gammaMeasure (1 / 2) (1 / 2), isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)⟩

@[simp] lemma chiSqPM_coe : (chiSqPM : Measure ℝ) = gammaMeasure (1 / 2) (1 / 2) := rfl

/-- **Moment asymptotics identify the limit.** If `Qₙ` are laws on `(0,∞)` whose `p`-th moments tend
to `(2p-1)!!` and are uniformly bounded, then `Qₙ` converges weakly to the chi-square law with one
degree of freedom. This is the step "by Carleman's criterion" in the proof of (I.1.7). -/
theorem tendsto_chiSqPM_of_moment_tendsto
    {Q : ℕ → ProbabilityMeasure ℝ}
    (hsupp : ∀ n, (Q n : Measure ℝ) (Set.Iio 0) = 0)
    (hint : ∀ (p n : ℕ), Integrable (fun x => x ^ p) (Q n : Measure ℝ))
    (hbdd : ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
      ∫⁻ x, ENNReal.ofReal (x ^ p) ∂(Q n : Measure ℝ) ≤ ENNReal.ofReal C)
    (hmom : ∀ p : ℕ, Tendsto (fun n => ∫ x, x ^ p ∂(Q n : Measure ℝ)) atTop
      (𝓝 ((oddFact p : ℝ)))) :
    Tendsto Q atTop (𝓝 chiSqPM) := by
  obtain ⟨C₁, hC₁, h1⟩ := hbdd 1
  have htight : IsTightMeasureSet (Set.range (fun n => (Q n : Measure ℝ))) := by
    refine isTightMeasureSet_range_of_uniform_first_moment hC₁ ?_
    intro n
    have hnn : ∀ᵐ x ∂(Q n : Measure ℝ), 0 ≤ x := ae_nonneg_of_Iio (hsupp n)
    have hcongr : (fun x : ℝ => ENNReal.ofReal (x ^ 1)) =ᵐ[(Q n : Measure ℝ)]
        (fun x : ℝ => ENNReal.ofReal |x|) := by
      filter_upwards [hnn] with x hx
      rw [pow_one, abs_of_nonneg hx]
    rw [← lintegral_congr_ae hcongr]
    exact h1 n
  have hS : IsCompact (closure (Set.range Q)) := by
    refine isCompact_closure_of_isTightMeasureSet ?_
    convert htight using 2
    ext μ
    simp [eq_comm]
  -- every subsequential limit is the chi-square law
  have hkey : ∀ (ns : ℕ → ℕ), Tendsto ns atTop atTop → ∃ ms : ℕ → ℕ,
      Tendsto (fun k => Q (ns (ms k))) atTop (𝓝 chiSqPM) := by
    intro ns hns
    have hmem : ∀ k, Q (ns k) ∈ closure (Set.range Q) := fun k => subset_closure ⟨ns k, rfl⟩
    obtain ⟨ν', -, φ, hφ, hconv⟩ := hS.tendsto_subseq hmem
    have hconvPM : Tendsto (fun k => Q (ns (φ k))) atTop (𝓝 ν') := hconv
    -- moments of the limit
    have hmom' : ∀ p : ℕ, ∫ x, x ^ p ∂(ν' : Measure ℝ) = (oddFact p : ℝ) := by
      intro p
      obtain ⟨Cp, hCp0, hCp⟩ := hbdd p
      obtain ⟨Cp1, hCp10, hCp1⟩ := hbdd (p + 1)
      have hsub : ∀ k, (Q (ns (φ k)) : Measure ℝ) (Set.Iio 0) = 0 := fun k => hsupp _
      -- the uniform real bound on the `(p+1)`-st moments
      have hC' : ∀ k, ∫ x, x ^ (p + 1) ∂(Q (ns (φ k)) : Measure ℝ) ≤ Cp1 := by
        intro k
        have hnn' : 0 ≤ᵐ[(Q (ns (φ k)) : Measure ℝ)] fun x => x ^ (p + 1) :=
          (ae_nonneg_of_Iio (hsupp _)).mono fun x hx => pow_nonneg hx _
        have hfeas : AEStronglyMeasurable (fun x : ℝ => x ^ (p + 1)) (Q (ns (φ k)) : Measure ℝ) :=
          (hint (p + 1) _).aestronglyMeasurable
        rw [integral_eq_lintegral_of_nonneg_ae hnn' hfeas]
        calc (∫⁻ x, ENNReal.ofReal (x ^ (p + 1)) ∂(Q (ns (φ k)) : Measure ℝ)).toReal
            ≤ (ENNReal.ofReal Cp1).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hCp1 _)
          _ = Cp1 := ENNReal.toReal_ofReal hCp10
      have hνint : Integrable (fun x : ℝ => x ^ p) (ν' : Measure ℝ) :=
        integrable_pow_of_uniform_lintegral_bound hsub hconvPM (fun k => hCp (ns (φ k)))
      have hpass := tendsto_integral_pow_of_uniform_bound (p := p) hCp10 hsub hconvPM
        (fun k => hint p _) (fun k => hint (p + 1) _) hC' hνint
      refine tendsto_nhds_unique hpass ?_
      exact (hmom p).comp (hns.comp hφ.tendsto_atTop)
    have hν0 : ∀ᵐ x ∂(ν' : Measure ℝ), 0 ≤ x :=
      ae_nonneg_of_Iio (measure_Iio_zero_of_tendsto (fun k => hsupp _) hconvPM)
    have heq : (ν' : Measure ℝ) = gammaMeasure (1 / 2) (1 / 2) := by
      refine eq_gammaMeasure_of_forall_moment_eq hν0 ?_
      intro p
      rw [hmom' p, integral_pow_gammaMeasure_one_half p]
    refine ⟨φ, ?_⟩
    rw [show chiSqPM = ν' from Subtype.ext heq.symm]
    exact hconvPM
  exact tendsto_of_subseq_tendsto hkey

/-- **Capstone: moment asymptotics give the tail-integral limit.** Combining
`tendsto_chiSqPM_of_moment_tendsto` (moment asymptotics ⇒ weak convergence to `χ²₁`) with the
transfer `tendsto_integral_one_sub_exp_div_of_tendsto` and the exact value
`∫ (1-e^{-λx})/x dχ²₁ = √(2λ+1) - 1`. This is the logical chain in the proof of (I.1.7):
(I.1.6) ⇒ `Q_r → Q∞` ⇒ the Laplace/tail integral converges to `√(2λ+1) - 1`, which feeds (I.3.7). -/
theorem tendsto_integral_one_sub_exp_div_of_moment_tendsto
    {Q : ℕ → ProbabilityMeasure ℝ}
    (hsupp : ∀ n, (Q n : Measure ℝ) (Set.Iic 0) = 0)
    (hint : ∀ (p n : ℕ), Integrable (fun x => x ^ p) (Q n : Measure ℝ))
    (hbdd : ∀ p : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
      ∫⁻ x, ENNReal.ofReal (x ^ p) ∂(Q n : Measure ℝ) ≤ ENNReal.ofReal C)
    (hmom : ∀ p : ℕ, Tendsto (fun n => ∫ x, x ^ p ∂(Q n : Measure ℝ)) atTop
      (𝓝 ((oddFact p : ℝ))))
    {lam : ℝ} (hlam : 0 ≤ lam) :
    Tendsto (fun n => ∫ x, (1 - Real.exp (-(lam * x))) / x ∂(Q n : Measure ℝ)) atTop
      (𝓝 (Real.sqrt (1 + 2 * lam) - 1)) := by
  have hsupp' : ∀ n, (Q n : Measure ℝ) (Set.Iio 0) = 0 := by
    intro n
    exact measure_mono_null (Set.Iio_subset_Iic (le_refl 0)) (hsupp n)
  have hconv : Tendsto Q atTop (𝓝 chiSqPM) := tendsto_chiSqPM_of_moment_tendsto hsupp' hint hbdd hmom
  have hsupplim : (chiSqPM : Measure ℝ) (Set.Iic 0) = 0 := by
    rw [chiSqPM_coe]
    exact gammaMeasure_one_half_Iic_zero
  have htrans := tendsto_integral_one_sub_exp_div_of_tendsto (l := atTop) hsupp hsupplim hconv hlam
  rw [show (∫ x, (1 - Real.exp (-(lam * x))) / x ∂(chiSqPM : Measure ℝ))
      = Real.sqrt (1 + 2 * lam) - 1 from ?_] at htrans
  · exact htrans
  · rw [chiSqPM_coe]
    exact integral_one_sub_exp_div_gammaMeasure_one_half hlam




end PercLib.CriticalLRP.MomentProblem
