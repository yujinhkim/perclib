/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# The chi-square law with one degree of freedom: moments and moment determinacy

Hutchcroft, *Critical long-range percolation I* (arXiv:2508.18807v1), Remark I.1.7 and the proof of
(I.1.7) (p. 32 of the arXiv v1 PDF): the normalized size-biased cluster volume converges to "a
chi-squared distribution with one degree of freedom", and this is justified by showing that the
`p`-th moments converge to `(2p-1)!!` and invoking "Carleman's criterion".

Here the chi-square law with one degree of freedom is the Gamma law with shape `1/2` and rate `1/2`,
`μ_χ = ProbabilityTheory.gammaMeasure (1/2) (1/2)`, whose density on `(0,∞)` is
`x^{-1/2} e^{-x/2} / √(2π)`. We prove:

* `integral_pow_gammaMeasure`: `∫ x^n ∂μ_χ = (2n-1)!!` (Mathlib's Gamma measure and Γ-integral);
* `summable_moment_series_gammaMeasure`: the moment series has radius of convergence `1/2`;
* `eq_gammaMeasure_of_forall_moment_eq`: **moment determinacy of the chi-square law**: any finite
  measure on `[0,∞)` with the same moments as `μ_χ` equals `μ_χ`.

The last statement is what replaces "by Carleman's criterion" in the paper's argument, using
`Measure.eq_of_forall_moment_eq_of_summable` from `MomentDeterminacy.lean`.
-/
module

public import Mathlib
public import PercLib.CriticalLRP.MomentProblem.Moments

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

set_option maxHeartbeats 800000

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.MomentProblem

/-! ### The double factorial and the Gamma values `Γ (n + 1/2)` -/

/-- `oddFact n = (2n-1)!! = 1 * 3 * ... * (2n-1)`, with `oddFact 0 = (-1)!! = 1`. -/
def oddFact (n : ℕ) : ℕ := ∏ k ∈ Finset.range n, (2 * k + 1)

@[simp]
lemma oddFact_zero : oddFact 0 = 1 := by simp [oddFact]

lemma oddFact_succ (n : ℕ) : oddFact (n + 1) = oddFact n * (2 * n + 1) := by
  simp [oddFact, Finset.prod_range_succ, mul_comm]

/-- `Γ (n + 1/2) / Γ (1/2) = (2n-1)!! / 2^n`. -/
lemma Gamma_add_half_ratio (n : ℕ) :
    Real.Gamma ((n : ℝ) + 1 / 2) / Real.Gamma (1 / 2) = (oddFact n : ℝ) / 2 ^ n := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, zero_add, oddFact_zero, Nat.cast_one, pow_zero, div_one]
    exact div_self (Real.Gamma_pos_of_pos (by norm_num)).ne'
  | succ n ih =>
    have hs : ((n : ℝ) + 1 / 2) ≠ 0 := by positivity
    have harg : (((n + 1 : ℕ) : ℝ) + 1 / 2) = ((n : ℝ) + 1 / 2) + 1 := by push_cast; ring
    rw [harg, Real.Gamma_add_one hs, mul_div_assoc, ih, oddFact_succ]
    push_cast
    rw [pow_succ]
    have hG : (Real.Gamma (1 / 2)) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
    field_simp

end PercLib.CriticalLRP.MomentProblem

namespace PercLib.CriticalLRP.MomentProblem

/-! ### Moments of the chi-square law `gammaMeasure (1/2) (1/2)` -/

lemma measurable_gammaPDF' (a r : ℝ) : Measurable (gammaPDF a r) :=
  (measurable_gammaPDFReal a r).ennreal_ofReal

/-- **The moments of the chi-square law with one degree of freedom are `(2n-1)!!`.** -/
theorem integral_pow_gammaMeasure_one_half (n : ℕ) :
    ∫ x, x ^ n ∂(gammaMeasure (1 / 2) (1 / 2)) = (oddFact n : ℝ) := by
  have ha : (0 : ℝ) < 1 / 2 := by norm_num
  have hGamma : (0 : ℝ) < Real.Gamma (1 / 2) := Real.Gamma_pos_of_pos ha
  -- reduce to an integral against Lebesgue measure of the density times `x^n`
  rw [gammaMeasure, integral_withDensity_eq_integral_toReal_smul (measurable_gammaPDF' _ _)
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top) (fun x => x ^ n)]
  have hpt : ∀ x : ℝ, (gammaPDF (1 / 2) (1 / 2) x).toReal • x ^ n
      = gammaPDFReal (1 / 2) (1 / 2) x * x ^ n := by
    intro x
    rw [gammaPDF, ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha ha x), smul_eq_mul]
  simp_rw [hpt]
  -- the density vanishes off `(0,∞)`
  have hzero : ∀ x : ℝ, x ∉ Set.Ioi (0 : ℝ) → gammaPDFReal (1 / 2) (1 / 2) x * x ^ n = 0 := by
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
  -- compute the integral over `(0,∞)`
  have hfun : ∀ x ∈ Set.Ioi (0 : ℝ),
      gammaPDFReal (1 / 2) (1 / 2) x * x ^ n
        = ((1 / 2 : ℝ) ^ (1 / 2 : ℝ) / Real.Gamma (1 / 2))
            * (x ^ ((n : ℝ) + 1 / 2 - 1) * Real.exp (-((1 / 2 : ℝ) * x))) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    rw [gammaPDFReal, ite_eq_left hx0.le]
    have hpow : x ^ ((1 / 2 : ℝ) - 1) * x ^ n = x ^ ((n : ℝ) + 1 / 2 - 1) := by
      rw [← Real.rpow_natCast x n, ← Real.rpow_add hx0]
      congr 1
      ring
    calc (1 / 2 : ℝ) ^ (1 / 2 : ℝ) / Real.Gamma (1 / 2) * x ^ ((1 / 2 : ℝ) - 1)
          * Real.exp (-((1 / 2 : ℝ) * x)) * x ^ n
        = (1 / 2 : ℝ) ^ (1 / 2 : ℝ) / Real.Gamma (1 / 2)
            * (x ^ ((1 / 2 : ℝ) - 1) * x ^ n) * Real.exp (-((1 / 2 : ℝ) * x)) := by ring
      _ = (1 / 2 : ℝ) ^ (1 / 2 : ℝ) / Real.Gamma (1 / 2)
            * (x ^ ((n : ℝ) + 1 / 2 - 1) * Real.exp (-((1 / 2 : ℝ) * x))) := by
          rw [hpow]; ring
  rw [setIntegral_congr_fun measurableSet_Ioi hfun, integral_const_mul,
    Real.integral_rpow_mul_exp_neg_mul_Ioi (by positivity : (0:ℝ) < (n : ℝ) + 1 / 2) ha]
  -- simplify the constants
  have hA2 : (1 / 2 : ℝ) ^ (1 / 2 : ℝ) * Real.sqrt 2 = 1 := by
    have h1 : (1 / 2 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (1 / 2) := (Real.sqrt_eq_rpow _).symm
    rw [h1, ← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 1 / 2)]
    have h2 : (1 / 2 : ℝ) * 2 = 1 := by norm_num
    rw [h2, Real.sqrt_one]
  have hT : (2 : ℝ) ^ ((n : ℝ) + 1 / 2) = 2 ^ n * Real.sqrt 2 := by
    rw [Real.rpow_add (by norm_num : (0:ℝ) < 2), Real.rpow_natCast,
      show ((1 / 2 : ℝ)) = 1 / 2 by norm_num, Real.sqrt_eq_rpow]
  have hgn : Real.Gamma ((n : ℝ) + 1 / 2)
      = Real.Gamma (1 / 2) * ((oddFact n : ℝ) / 2 ^ n) := by
    rw [← Gamma_add_half_ratio n]
    field_simp
  rw [show (1 / (1 / 2 : ℝ)) = 2 by norm_num, hT, hgn, Real.Gamma_one_half_eq]
  have h2n : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  rw [show (1 / 2 : ℝ) ^ (1 / 2 : ℝ) / Real.sqrt Real.pi
      * ((2 : ℝ) ^ n * Real.sqrt 2 * (Real.sqrt Real.pi * ((oddFact n : ℝ) / 2 ^ n)))
      = ((1 / 2 : ℝ) ^ (1 / 2 : ℝ) * Real.sqrt 2) * ((oddFact n : ℝ) / 2 ^ n) * 2 ^ n
      by field_simp]
  rw [hA2, one_mul]
  exact div_mul_cancel₀ _ h2n.ne'

end PercLib.CriticalLRP.MomentProblem

namespace PercLib.CriticalLRP.MomentProblem

/-! ### The moment series of the chi-square law and its determinacy -/

lemma oddFact_le_two_pow_mul_factorial (n : ℕ) : oddFact n ≤ 2 ^ n * n.factorial := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [oddFact_succ, pow_succ, Nat.factorial_succ]
    calc oddFact n * (2 * n + 1) ≤ (2 ^ n * n.factorial) * (2 * n + 1) :=
          Nat.mul_le_mul_right _ ih
      _ ≤ (2 ^ n * n.factorial) * (2 * (n + 1)) := by
          refine Nat.mul_le_mul_left _ ?_
          omega
      _ = 2 ^ n * 2 * ((n + 1) * n.factorial) := by ring

/-- The moment series of the chi-square law with one degree of freedom converges for `r < 1/2`:
`(2n-1)!! / n! = binom(2n,n) / 2^n ≤ 2^n`. -/
lemma summable_gammaMeasure_moment_series {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1 / 2) :
    Summable (fun n : ℕ => r ^ n / n.factorial * (oddFact n : ℝ)) := by
  have hbound : ∀ n : ℕ, r ^ n / n.factorial * (oddFact n : ℝ) ≤ (2 * r) ^ n := by
    intro n
    have hfac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
    have h1 : (oddFact n : ℝ) ≤ 2 ^ n * (n.factorial : ℝ) := by
      exact_mod_cast oddFact_le_two_pow_mul_factorial n
    have h2 : 0 ≤ r ^ n / (n.factorial : ℝ) := by positivity
    calc r ^ n / n.factorial * (oddFact n : ℝ)
        ≤ r ^ n / n.factorial * (2 ^ n * (n.factorial : ℝ)) := mul_le_mul_of_nonneg_left h1 h2
      _ = (2 * r) ^ n := by
          rw [mul_pow]
          field_simp
  refine Summable.of_nonneg_of_le (fun n => by positivity) hbound ?_
  refine summable_geometric_of_lt_one (by positivity) ?_
  linarith

/-- The chi-square law with one degree of freedom is supported in `[0,∞)`. -/
lemma gammaMeasure_one_half_Iio_zero : gammaMeasure (1 / 2) (1 / 2) (Set.Iio 0) = 0 := by
  rw [gammaMeasure, withDensity_apply _ measurableSet_Iio]
  have hzero : ∀ x ∈ Set.Iio (0 : ℝ), gammaPDF (1 / 2) (1 / 2) x = 0 := by
    intro x hx
    exact gammaPDF_of_neg hx
  rw [setLIntegral_congr_fun measurableSet_Iio hzero, lintegral_zero]

lemma gammaMeasure_one_half_ae_nonneg : ∀ᵐ x ∂(gammaMeasure (1 / 2) (1 / 2)), 0 ≤ x := by
  rw [ae_iff]
  have hset : {x : ℝ | ¬ (0 ≤ x)} = Set.Iio 0 := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_Iio, not_le]
  rw [hset]
  exact gammaMeasure_one_half_Iio_zero

/-- All polynomial moments of the chi-square law are integrable. -/
lemma integrable_pow_gammaMeasure_one_half (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (gammaMeasure (1 / 2) (1 / 2)) := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => x ^ n) (gammaMeasure (1 / 2) (1 / 2)) := by
    fun_prop
  refine ⟨hmeas, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  have hnn : ∀ᵐ x ∂(gammaMeasure (1 / 2) (1 / 2)), 0 ≤ x ^ n := by
    filter_upwards [gammaMeasure_one_half_ae_nonneg] with x hx
    exact pow_nonneg hx n
  have hlin : ∫⁻ x, ENNReal.ofReal ‖x ^ n‖ ∂(gammaMeasure (1 / 2) (1 / 2))
      = ∫⁻ x, ENNReal.ofReal (x ^ n) ∂(gammaMeasure (1 / 2) (1 / 2)) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hnn] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg hx]
  rw [hlin]
  have hreal : (∫⁻ x, ENNReal.ofReal (x ^ n) ∂(gammaMeasure (1 / 2) (1 / 2))).toReal
      = (oddFact n : ℝ) := by
    rw [← integral_eq_lintegral_of_nonneg_ae hnn hmeas]
    exact integral_pow_gammaMeasure_one_half n
  have hpos : (0 : ℝ) < (oddFact n : ℝ) := by
    have : 0 < oddFact n := by
      rw [oddFact]
      exact Finset.prod_pos (fun k _ => by omega)
    exact_mod_cast this
  refine lt_top_iff_ne_top.mpr fun htop => ?_
  rw [htop, ENNReal.toReal_top] at hreal
  exact hpos.ne' hreal.symm

end PercLib.CriticalLRP.MomentProblem

namespace PercLib.CriticalLRP.MomentProblem

/-- Absolute moments of the chi-square law, in the form needed by the determinacy theorem. -/
lemma integral_abs_pow_gammaMeasure_one_half (n : ℕ) :
    ∫ x, |x| ^ n ∂(gammaMeasure (1 / 2) (1 / 2)) = (oddFact n : ℝ) := by
  rw [← integral_pow_gammaMeasure_one_half n]
  refine integral_congr_ae ?_
  filter_upwards [gammaMeasure_one_half_ae_nonneg] with x hx
  rw [abs_of_nonneg hx]

lemma integrable_abs_pow_gammaMeasure_one_half (n : ℕ) :
    Integrable (fun x : ℝ => |x| ^ n) (gammaMeasure (1 / 2) (1 / 2)) := by
  refine (integrable_pow_gammaMeasure_one_half n).congr ?_
  filter_upwards [gammaMeasure_one_half_ae_nonneg] with x hx
  rw [abs_of_nonneg hx]


/-- Moment equality with the chi-square law forces integrability of all moments. -/
lemma integrable_pow_of_forall_moment_eq_gammaMeasure {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν0 : ∀ᵐ x : ℝ ∂ν, 0 ≤ x)
    (hmom : ∀ n : ℕ, ∫ x, x ^ n ∂ν = ∫ x, x ^ n ∂(gammaMeasure (1 / 2) (1 / 2))) (n : ℕ) :
    Integrable (fun x : ℝ => |x| ^ n) ν := by
  have hmeas : AEStronglyMeasurable (fun x : ℝ => x ^ n) ν := by fun_prop
  have hnn : ∀ᵐ x ∂ν, 0 ≤ x ^ n := by
    filter_upwards [hν0] with x hx
    exact pow_nonneg hx n
  have habs : ∀ᵐ x ∂ν, |x| ^ n = x ^ n := by
    filter_upwards [hν0] with x hx
    rw [abs_of_nonneg hx]
  have hlin : ∫⁻ x, ENNReal.ofReal ‖|x| ^ n‖ ∂ν = ∫⁻ x, ENNReal.ofReal (x ^ n) ∂ν := by
    refine lintegral_congr_ae ?_
    filter_upwards [hnn, habs] with x hx hx'
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hx']
  refine ⟨hmeas.congr (by filter_upwards [habs] with x hx; exact hx.symm), ?_⟩
  rw [hasFiniteIntegral_iff_norm, hlin]
  have hreal : (∫⁻ x, ENNReal.ofReal (x ^ n) ∂ν).toReal = (oddFact n : ℝ) := by
    rw [← integral_eq_lintegral_of_nonneg_ae hnn hmeas, hmom n,
      integral_pow_gammaMeasure_one_half n]
  have hpos : (0 : ℝ) < (oddFact n : ℝ) := by
    have : 0 < oddFact n := by
      rw [oddFact]
      exact Finset.prod_pos (fun k _ => by omega)
    exact_mod_cast this
  refine lt_top_iff_ne_top.mpr fun htop => ?_
  rw [htop, ENNReal.toReal_top] at hreal
  exact hpos.ne' hreal.symm

/-- **Moment determinacy of the chi-square law with one degree of freedom.**

Any finite measure on `[0,∞)` whose `n`-th moment is `(2n-1)!!` for every `n` is the chi-square law
with one degree of freedom. This is the statement that the paper's proof of (I.1.7) obtains from
"Carleman's criterion"; here it is proved directly from the convergence of the moment series. -/
theorem eq_gammaMeasure_of_forall_moment_eq {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν0 : ∀ᵐ x : ℝ ∂ν, 0 ≤ x)
    (hmom : ∀ n : ℕ, ∫ x, x ^ n ∂ν = ∫ x, x ^ n ∂(gammaMeasure (1 / 2) (1 / 2))) :
    ν = gammaMeasure (1 / 2) (1 / 2) := by
  have : IsProbabilityMeasure (gammaMeasure (1 / 2) (1 / 2)) :=
    isProbabilityMeasure_gammaMeasure (by norm_num) (by norm_num)
  -- the moment values
  have hval : ∀ n : ℕ, ∫ x, x ^ n ∂(gammaMeasure (1 / 2) (1 / 2)) = (oddFact n : ℝ) :=
    integral_pow_gammaMeasure_one_half
  -- the moment series of `ν` converges at `r = 1/4`
  have hsum : Summable (fun n : ℕ => (1 / 4 : ℝ) ^ n / n.factorial * ∫ x, |x| ^ n ∂ν) := by
    have hcongr : (fun n : ℕ => (1 / 4 : ℝ) ^ n / n.factorial * ∫ x, |x| ^ n ∂ν)
        = fun n : ℕ => (1 / 4 : ℝ) ^ n / n.factorial * (oddFact n : ℝ) := by
      funext n
      have habs : ∫ x, |x| ^ n ∂ν = ∫ x, x ^ n ∂ν := by
        refine integral_congr_ae (hν0.mono fun x hx => ?_)
        simp only [abs_of_nonneg hx]
      rw [habs, hmom n, hval n]
    rw [hcongr]
    exact summable_gammaMeasure_moment_series (by norm_num) (by norm_num)
  exact (Measure.eq_of_forall_moment_eq_of_summable (μ := gammaMeasure (1 / 2) (1 / 2))
    (ν := ν) gammaMeasure_one_half_ae_nonneg hν0 integrable_abs_pow_gammaMeasure_one_half
    (integrable_pow_of_forall_moment_eq_gammaMeasure hν0 hmom) hmom (by norm_num) hsum).symm

end PercLib.CriticalLRP.MomentProblem

/-! ### Axiom audit -/

#print axioms PercLib.CriticalLRP.MomentProblem.eq_gammaMeasure_of_forall_moment_eq
#print axioms PercLib.CriticalLRP.MomentProblem.integral_pow_gammaMeasure_one_half
#print axioms PercLib.CriticalLRP.MomentProblem.summable_gammaMeasure_moment_series
#print axioms PercLib.CriticalLRP.MomentProblem.Gamma_add_half_ratio
