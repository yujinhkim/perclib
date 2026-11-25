/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Moment determinacy on `ℝ` and the chi-square limit law

Hutchcroft, *Critical long-range percolation I* (arXiv:2508.18807v1): after (I.1.6) one knows the
moments of the normalized size-biased volume law `Q_r`, and the paper concludes
(Hutchcroft, proof of (I.1.7), p. 32 of the arXiv v1 PDF)

  "It follows ... that any subsequential limit of the measures `Q_r` has `p`th moment `(2p-1)!!`
   for each integer `p ≥ 1` and hence by Carleman's criterion that `Q_r` converges to a chi-squared
   random variable with one degree of freedom",

i.e. it uses that the chi-square law with one degree of freedom is determined by its moment
sequence `(2p-1)!!`.

This file proves moment determinacy in the form actually used, without Carleman's criterion:

* `Measure.eq_of_forall_moment_eq_of_integrable_exp` : two probability measures on `ℝ` with the same
  moments of all orders coincide, provided **one** of them has a finite moment generating function
  in a neighbourhood of `0`.

The route is the classical analytic one, and is arranged so that the exponential-moment hypothesis is
propagated to the second measure (the paper only knows moments of a subsequential limit):

1. from `∫ exp (t |x|) ∂μ < ∞` and moment equality, the even moments of `ν` are bounded factorially,
   hence `∫ exp (t' |x|) ∂ν < ∞` for some `t' > 0`
   (`exists_integrable_exp_of_forall_moment_eq`);
2. on `(-δ, δ)` both mgfs are given by the *same* moment series `∑ s^n m_n / n!`
   (`mgf_eq_tsum_moment`);
3. the complex mgfs are analytic on the vertical strip where the mgf is finite
   (Mathlib: `ProbabilityTheory.analyticOnNhd_complexMGF`), they agree on the real interval
   `(-δ, δ)`, hence on the strip by the identity principle; evaluating on the imaginary axis gives
   equality of the characteristic functions, and `Measure.ext_of_charFun` finishes.

As a byproduct we fill the Mathlib `TODO` recorded in `Mathlib/Probability/Moments/ComplexMGF.lean`
("once we know that equal `mgf` implies equal distributions"): see `MgfDeterminacy.lean`.
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

open MeasureTheory Filter Real
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.MomentProblem

/-! ### Exponential moments and polynomial moments -/

/-- A monomial is dominated by the exponential moment: `|x|^n ≤ n!/t^n * exp (t |x|)`. -/
lemma abs_pow_le_factorial_div_mul_exp {t : ℝ} (ht : 0 < t) (n : ℕ) (x : ℝ) :
    |x| ^ n ≤ (n.factorial : ℝ) / t ^ n * Real.exp (t * |x|) := by
  have hfac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
  have htn : (0 : ℝ) < t ^ n := pow_pos ht n
  have key : t ^ n * |x| ^ n ≤ (n.factorial : ℝ) * Real.exp (t * |x|) := by
    have h := Real.pow_div_factorial_le_exp (t * |x|) (by positivity) n
    rw [div_le_iff₀ hfac] at h
    calc t ^ n * |x| ^ n = (t * |x|) ^ n := by rw [mul_pow]
      _ ≤ Real.exp (t * |x|) * (n.factorial : ℝ) := h
      _ = (n.factorial : ℝ) * Real.exp (t * |x|) := by ring
  rw [div_mul_eq_mul_div, le_div_iff₀ htn]
  calc |x| ^ n * t ^ n = t ^ n * |x| ^ n := by ring
    _ ≤ (n.factorial : ℝ) * Real.exp (t * |x|) := key

/-- If `exp (t |x|)` is integrable (`t > 0`), then every absolute moment is finite. -/
lemma integrable_abs_pow_of_integrable_exp {μ : Measure ℝ} {t : ℝ} (ht : 0 < t)
    (h : Integrable (fun x : ℝ => Real.exp (t * |x|)) μ) (n : ℕ) :
    Integrable (fun x : ℝ => |x| ^ n) μ := by
  have hc : Integrable (fun x : ℝ => (n.factorial : ℝ) / t ^ n * Real.exp (t * |x|)) μ :=
    h.const_mul _
  refine Integrable.mono' hc ((continuous_abs.pow n).aestronglyMeasurable) (Eventually.of_forall ?_)
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact abs_pow_le_factorial_div_mul_exp ht n x

/-- If `exp (t |x|)` is integrable then every (signed) moment is integrable. -/
lemma integrable_pow_of_integrable_exp {μ : Measure ℝ} {t : ℝ} (ht : 0 < t)
    (h : Integrable (fun x : ℝ => Real.exp (t * |x|)) μ) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) μ := by
  have habs := integrable_abs_pow_of_integrable_exp ht h n
  refine Integrable.mono' habs ((continuous_id.pow n).aestronglyMeasurable) (Eventually.of_forall ?_)
  intro x
  rw [Real.norm_eq_abs, abs_pow]

/-- Integrability of `exp (t |x|)` puts `0` in the interior of `integrableExpSet`. -/
lemma zero_mem_interior_integrableExpSet {μ : Measure ℝ} {t : ℝ} (ht : 0 < t)
    (h : Integrable (fun x : ℝ => Real.exp (t * |x|)) μ) :
    (0 : ℝ) ∈ interior (ProbabilityTheory.integrableExpSet id μ) := by
  have hsub : Set.Ioo (-t) t ⊆ ProbabilityTheory.integrableExpSet id μ := by
    intro s hs
    simp only [ProbabilityTheory.integrableExpSet, Set.mem_ofPred_eq, id_eq]
    refine Integrable.mono' h (by fun_prop) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr ?_
    calc s * x ≤ |s| * |x| := by
          calc s * x ≤ |s * x| := le_abs_self _
            _ = |s| * |x| := abs_mul s x
      _ ≤ t * |x| := by gcongr; exact le_of_lt (abs_lt.mpr hs)
  exact mem_interior_iff_mem_nhds.mpr
    (Filter.mem_of_superset (Ioo_mem_nhds (by linarith) (by linarith)) hsub)



/-! ### The moment generating function as the sum of its moment series -/

/-- Where the exponential moment is finite, the absolute moment series is summable. -/
lemma summable_abs_moment_series {μ : Measure ℝ} [IsFiniteMeasure μ] {t : ℝ} (ht : 0 < t)
    (h : Integrable (fun x : ℝ => Real.exp (t * |x|)) μ) {s : ℝ} (hs : |s| < t) :
    Summable (fun n : ℕ => |s| ^ n / n.factorial * ∫ x, |x| ^ n ∂μ) := by
  set C := ∫ x, Real.exp (t * |x|) ∂μ with hC
  have hCnn : 0 ≤ C := integral_nonneg fun x => (Real.exp_pos _).le
  have hbound : ∀ n : ℕ, |s| ^ n / n.factorial * ∫ x, |x| ^ n ∂μ ≤ (|s| / t) ^ n * C := by
    intro n
    have hfac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
    have hg : Integrable (fun x : ℝ => (n.factorial : ℝ) / t ^ n * Real.exp (t * |x|)) μ :=
      h.const_mul _
    have h1 : ∫ x, |x| ^ n ∂μ ≤ (n.factorial : ℝ) / t ^ n * C := by
      have hm := integral_mono (integrable_abs_pow_of_integrable_exp ht h n) hg
        (fun x => abs_pow_le_factorial_div_mul_exp ht n x)
      rwa [integral_const_mul] at hm
    have h2 : (0 : ℝ) ≤ |s| ^ n / (n.factorial : ℝ) := by positivity
    have h3 : |s| ^ n / (n.factorial : ℝ) * ((n.factorial : ℝ) / t ^ n * C)
        = (|s| / t) ^ n * C := by
      rw [div_pow]
      field_simp
    calc |s| ^ n / n.factorial * ∫ x, |x| ^ n ∂μ
        ≤ |s| ^ n / n.factorial * ((n.factorial : ℝ) / t ^ n * C) :=
          mul_le_mul_of_nonneg_left h1 h2
      _ = (|s| / t) ^ n * C := h3
  refine Summable.of_nonneg_of_le (fun n => by positivity) hbound ?_
  have hlt : |s| / t < 1 := by rw [div_lt_one ht]; exact hs
  exact (summable_geometric_of_lt_one (by positivity) hlt).mul_right C

/-- **The mgf is the sum of its moment series** on the interval where it is finite. -/
theorem mgf_eq_tsum_moment {μ : Measure ℝ} [IsFiniteMeasure μ] {t : ℝ} (ht : 0 < t)
    (h : Integrable (fun x : ℝ => Real.exp (t * |x|)) μ) {s : ℝ} (hs : |s| < t) :
    ∫ x, Real.exp (s * x) ∂μ = ∑' n : ℕ, s ^ n / n.factorial * ∫ x, x ^ n ∂μ := by
  have hFint : ∀ n : ℕ, Integrable (fun x : ℝ => (s * x) ^ n / n.factorial) μ := by
    intro n
    have hp := (integrable_pow_of_integrable_exp ht h n).const_mul (s ^ n / n.factorial)
    have hEq : (fun x : ℝ => (s * x) ^ n / n.factorial)
        = fun x => s ^ n / n.factorial * x ^ n := by
      funext x
      rw [mul_pow]
      ring
    rw [hEq]
    exact hp
  have hFsum : Summable (fun n : ℕ => ∫ x, ‖(s * x) ^ n / n.factorial‖ ∂μ) := by
    have hcongr : (fun n : ℕ => ∫ x, ‖(s * x) ^ n / n.factorial‖ ∂μ)
        = fun n : ℕ => |s| ^ n / n.factorial * ∫ x, |x| ^ n ∂μ := by
      funext n
      have hfac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
      have h1 : ∀ x : ℝ, ‖(s * x) ^ n / n.factorial‖
          = |s| ^ n / n.factorial * |x| ^ n := by
        intro x
        have hc : |(n.factorial : ℝ)| = (n.factorial : ℝ) := abs_of_pos hfac
        rw [Real.norm_eq_abs, abs_div, abs_pow, abs_mul, hc, mul_pow]
        ring
      simp_rw [h1]
      rw [integral_const_mul]
    rw [hcongr]
    exact summable_abs_moment_series ht h hs
  have hmain := hasSum_integral_of_summable_integral_norm hFint hFsum
  have hident : ∀ n : ℕ, ∫ x, (s * x) ^ n / n.factorial ∂μ
      = s ^ n / n.factorial * ∫ x, x ^ n ∂μ := by
    intro n
    rw [← integral_const_mul]
    congr with x
    ring
  have hpoint : ∀ x : ℝ, ∑' n : ℕ, (s * x) ^ n / n.factorial = Real.exp (s * x) := by
    intro x
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  simp only [hident, hpoint] at hmain
  exact hmain.tsum_eq.symm

end PercLib.CriticalLRP.MomentProblem

namespace PercLib.CriticalLRP.MomentProblem

/-! ### Laplace transforms of measures on `[0,∞)` and the moment series -/

/-- For a finite measure supported in `[0,∞)`, the negative half-line lies in the interior of the
exponential integrability set: `exp (t x)` is bounded by `1` for `t < 0`. -/
lemma Iio_subset_interior_integrableExpSet {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν0 : ∀ᵐ x ∂ν, 0 ≤ x) :
    Set.Iio 0 ⊆ interior (ProbabilityTheory.integrableExpSet id ν) := by
  have hmem : ∀ s : ℝ, s < 0 → s ∈ ProbabilityTheory.integrableExpSet id ν := by
    intro s hs
    simp only [ProbabilityTheory.integrableExpSet, Set.mem_ofPred_eq, id_eq]
    refine Integrable.of_bound (by fun_prop) 1 ?_
    filter_upwards [hν0] with x hx
    have hmul : s * x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hs.le hx
    rw [Real.norm_eq_abs, Real.abs_exp]
    exact Real.exp_le_one_iff.mpr hmul
  intro t ht
  have ht0 : t < 0 := ht
  have h2t : 2 * t < t := by linarith
  have ht2 : t < t / 2 := by linarith
  have hord := (ProbabilityTheory.convex_integrableExpSet (X := id) (μ := ν)).ordConnected
  have hsub : Set.Ioo (2 * t) (t / 2) ⊆ ProbabilityTheory.integrableExpSet id ν := by
    intro s hs
    exact hord.out (hmem (2 * t) (by linarith)) (hmem (t / 2) (by linarith))
      (Set.mem_Icc.mpr ⟨le_of_lt hs.1, le_of_lt hs.2⟩)
  exact mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (Ioo_mem_nhds h2t ht2) hsub)

/-- **The Laplace transform of a measure on `[0,∞)` is its moment series**, on the disc where the
moment series converges. -/
lemma integral_cexp_neg_mul_eq_tsum {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hint : ∀ n : ℕ, Integrable (fun x : ℝ => |x| ^ n) ν)
    {r : ℝ} (hr : 0 < r)
    (hsum : Summable (fun n : ℕ => r ^ n / n.factorial * ∫ x, |x| ^ n ∂ν))
    {z : ℂ} (hz : ‖z‖ < r) :
    ∫ x, Complex.exp (-(z * x)) ∂ν
      = ∑' n : ℕ, (-z) ^ n / n.factorial * ((∫ x, x ^ n ∂ν : ℝ) : ℂ) := by
  set F : ℕ → ℝ → ℂ := fun n x => (-(z * x)) ^ n / n.factorial with hF
  have hFint : ∀ n, Integrable (F n) ν := by
    intro n
    have hfac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
    have hbase : Integrable (fun x : ℝ => ‖z‖ ^ n / (n.factorial : ℝ) * |x| ^ n) ν :=
      (hint n).const_mul _
    refine Integrable.mono' hbase (by fun_prop) (Eventually.of_forall fun x => ?_)
    have hnorm : ‖(x : ℂ)‖ = |x| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    have hnfac : ‖(n.factorial : ℝ)‖ = (n.factorial : ℝ) := by
      rw [Real.norm_eq_abs, abs_of_pos hfac]
    have h1 : ‖F n x‖ = ‖z‖ ^ n / (n.factorial : ℝ) * |x| ^ n := by
      rw [hF]
      simp only [norm_div, norm_pow, norm_neg, norm_mul, hnorm, Complex.norm_natCast]
      ring
    rw [h1]
  have hFsum : Summable (fun n : ℕ => ∫ x, ‖F n x‖ ∂ν) := by
    have hcongr : (fun n : ℕ => ∫ x, ‖F n x‖ ∂ν)
        = fun n : ℕ => ‖z‖ ^ n / n.factorial * ∫ x, |x| ^ n ∂ν := by
      funext n
      have hfac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
      have hnorm : ∀ x : ℝ, ‖(x : ℂ)‖ = |x| := by
        intro x
        rw [Complex.norm_real, Real.norm_eq_abs]
      have hnfac : ‖(n.factorial : ℝ)‖ = (n.factorial : ℝ) := by
        rw [Real.norm_eq_abs, abs_of_pos hfac]
      have hpt : ∀ x : ℝ, ‖F n x‖ = ‖z‖ ^ n / (n.factorial : ℝ) * |x| ^ n := by
        intro x
        rw [hF]
        simp only [norm_div, norm_pow, norm_neg, norm_mul, hnorm, Complex.norm_natCast]
        ring
      simp_rw [hpt]
      rw [integral_const_mul]
    rw [hcongr]
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hsum
    have hle : ‖z‖ ^ n ≤ r ^ n := pow_le_pow_left₀ (norm_nonneg z) hz.le n
    have hfac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
    have hdiv : ‖z‖ ^ n / (n.factorial : ℝ) ≤ r ^ n / (n.factorial : ℝ) := by
      gcongr
    exact mul_le_mul_of_nonneg_right hdiv (integral_nonneg fun x => by positivity)
  have hmain := hasSum_integral_of_summable_integral_norm hFint hFsum
  have h1 : ∀ n : ℕ, ∫ x, F n x ∂ν = (-z) ^ n / n.factorial * ((∫ x, x ^ n ∂ν : ℝ) : ℂ) := by
    intro n
    have hpt : ∀ x : ℝ, F n x = ((-z) ^ n / n.factorial) * ((x ^ n : ℝ) : ℂ) := by
      intro x
      rw [hF, Complex.ofReal_pow]
      ring
    simp_rw [hpt]
    rw [integral_const_mul]
    norm_cast
  have h2 : ∀ x : ℝ, (∑' n : ℕ, F n x) = Complex.exp (-(z * x)) := by
    intro x
    rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]
  have h3 : (∫ x, ∑' n : ℕ, F n x ∂ν) = ∫ x, Complex.exp (-(z * x)) ∂ν := by
    congr 1 with x
    exact h2 x
  rw [h3] at hmain
  have h4 : (fun n : ℕ => ∫ x, F n x ∂ν)
      = fun n : ℕ => (-z) ^ n / n.factorial * ((∫ x, x ^ n ∂ν : ℝ) : ℂ) := by
    funext n
    exact h1 n
  rw [h4] at hmain
  exact hmain.tsum_eq.symm

end PercLib.CriticalLRP.MomentProblem

namespace PercLib.CriticalLRP.MomentProblem

/-! ### Continuity of the complex mgf on the closed left half-plane -/

/-- For a measure supported in `[0,∞)`, the complex mgf is continuous on the closed left half-plane
(the integrand is dominated by `1`). -/
lemma tendsto_complexMGF_sub_inv {ν : Measure ℝ} [IsFiniteMeasure ν]
    (hν0 : ∀ᵐ x ∂ν, 0 ≤ x) {w : ℂ} (hw : w.re ≤ 0) :
    Tendsto (fun n : ℕ => ProbabilityTheory.complexMGF id ν (w - (Complex.ofReal (((n : ℝ) + 1)⁻¹))))
      atTop (𝓝 (ProbabilityTheory.complexMGF id ν w)) := by
  have hbound_int : Integrable (fun _ : ℝ => (1 : ℝ)) ν := integrable_const 1
  have hmeas : ∀ n : ℕ, AEStronglyMeasurable
      (fun x : ℝ => Complex.exp ((w - (Complex.ofReal (((n : ℝ) + 1)⁻¹))) * (x : ℂ))) ν := fun n => by
    fun_prop
  have hdom : ∀ n : ℕ, ∀ᵐ x : ℝ ∂ν,
      ‖Complex.exp ((w - (Complex.ofReal (((n : ℝ) + 1)⁻¹))) * (x : ℂ))‖ ≤ 1 := by
    intro n
    refine hν0.mono fun x hx => ?_
    rw [Complex.norm_exp]
    have hcre : (w - (Complex.ofReal (((n : ℝ) + 1)⁻¹))).re = w.re - ((n : ℝ) + 1)⁻¹ := by
      rw [Complex.sub_re, Complex.ofReal_re]
    have hre : ((w - (Complex.ofReal (((n : ℝ) + 1)⁻¹))) * (x : ℂ)).re
        = w.re * x - ((n : ℝ) + 1)⁻¹ * x := by
      rw [Complex.mul_re, hcre]
      simp
      ring
    rw [hre]
    have hc : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
    refine Real.exp_le_one_iff.mpr (by nlinarith)
  have hlim : ∀ᵐ x : ℝ ∂ν, Tendsto
      (fun n : ℕ => Complex.exp ((w - (Complex.ofReal (((n : ℝ) + 1)⁻¹))) * (x : ℂ)))
      atTop (𝓝 (Complex.exp (w * (x : ℂ)))) := by
    refine Eventually.of_forall fun x => ?_
    have h0r : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    have h0 : Tendsto (fun n : ℕ => (Complex.ofReal (((n : ℝ) + 1)⁻¹))) atTop (𝓝 0) :=
      tendsto_ofReal_iff.mpr h0r
    have hcoef : Tendsto (fun n : ℕ => (w - (Complex.ofReal (((n : ℝ) + 1)⁻¹)))) atTop (𝓝 w) := by
      simpa using (tendsto_const_nhds.sub h0 : Tendsto
        (fun n : ℕ => w - (Complex.ofReal (((n : ℝ) + 1)⁻¹))) atTop (𝓝 (w - 0)))
    have hmul : Tendsto (fun n : ℕ => (w - (Complex.ofReal (((n : ℝ) + 1)⁻¹))) * (x : ℂ))
        atTop (𝓝 (w * (x : ℂ))) := hcoef.mul_const (x : ℂ)
    exact hmul.cexp
  simpa [ProbabilityTheory.complexMGF] using
    tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) hmeas hbound_int hdom hlim

end PercLib.CriticalLRP.MomentProblem

namespace PercLib.CriticalLRP.MomentProblem

/-! ### Moment determinacy -/

/-- **Moment determinacy on `[0,∞)`.** Two finite measures on `ℝ` supported in `[0,∞)` with the same
moments of all orders coincide, provided the moment series converges on a disc of positive radius.

This is the moment-problem statement used in the proof of (I.1.7) of Hutchcroft,
*Critical long-range percolation I*: the chi-square law with one degree of freedom has moments
`(2p-1)!!`, whose moment series has radius of convergence `1/2`. -/
theorem Measure.eq_of_forall_moment_eq_of_summable {μ ν : Measure ℝ} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hμ0 : ∀ᵐ x : ℝ ∂μ, 0 ≤ x) (hν0 : ∀ᵐ x : ℝ ∂ν, 0 ≤ x)
    (hμint : ∀ n : ℕ, Integrable (fun x : ℝ => |x| ^ n) μ)
    (hνint : ∀ n : ℕ, Integrable (fun x : ℝ => |x| ^ n) ν)
    (hmom : ∀ n : ℕ, ∫ x, x ^ n ∂ν = ∫ x, x ^ n ∂μ)
    {r : ℝ} (hr : 0 < r)
    (hsum : Summable (fun n : ℕ => r ^ n / n.factorial * ∫ x, |x| ^ n ∂ν)) :
    μ = ν := by
  -- absolute moments are the signed moments, since the measures live on `[0,∞)`
  have habsν : ∀ n : ℕ, ∫ x, |x| ^ n ∂ν = ∫ x, x ^ n ∂ν := by
    intro n
    refine integral_congr_ae (hν0.mono fun x hx => ?_)
    simp only [abs_of_nonneg hx]
  have habsμ : ∀ n : ℕ, ∫ x, |x| ^ n ∂μ = ∫ x, x ^ n ∂μ := by
    intro n
    refine integral_congr_ae (hμ0.mono fun x hx => ?_)
    simp only [abs_of_nonneg hx]
  -- the moment series of `μ` converges as well
  have hsumμ : Summable (fun n : ℕ => r ^ n / n.factorial * ∫ x, |x| ^ n ∂μ) := by
    refine hsum.congr fun n => ?_
    rw [habsν n, habsμ n, hmom n]
  -- Laplace transforms as holomorphic functions of `z`, written as `z ↦
  -- complexMGF id ν (-z)`; the analyticity comes from Mathlib's `complexMGF` theory
  have hanF : AnalyticOnNhd ℂ (fun z : ℂ => ProbabilityTheory.complexMGF id ν (-z))
      {z : ℂ | 0 < z.re} := by
    have hcomp := (ProbabilityTheory.analyticOnNhd_complexMGF (X := id) (μ := ν)).comp
      (analyticOnNhd_id.neg (𝕜 := ℂ) (s := {z : ℂ | 0 < z.re})) ?_
    · simpa [Function.comp_def] using hcomp
    · intro z hz
      have hz' : (-z).re < 0 := by simpa using hz
      exact Iio_subset_interior_integrableExpSet hν0 hz'
  have hanG : AnalyticOnNhd ℂ (fun z : ℂ => ProbabilityTheory.complexMGF id μ (-z))
      {z : ℂ | 0 < z.re} := by
    have hcomp := (ProbabilityTheory.analyticOnNhd_complexMGF (X := id) (μ := μ)).comp
      (analyticOnNhd_id.neg (𝕜 := ℂ) (s := {z : ℂ | 0 < z.re})) ?_
    · simpa [Function.comp_def] using hcomp
    · intro z hz
      have hz' : (-z).re < 0 := by simpa using hz
      exact Iio_subset_interior_integrableExpSet hμ0 hz'
  -- on the disc where the moment series converges both are given by that series
  have hseries : Set.EqOn (fun z : ℂ => ProbabilityTheory.complexMGF id ν (-z))
      (fun z : ℂ => ProbabilityTheory.complexMGF id μ (-z)) {z : ℂ | 0 < z.re ∧ ‖z‖ < r} := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := hz
    have hconvν : ProbabilityTheory.complexMGF id ν (-z) = ∫ x, Complex.exp (-(z * x)) ∂ν := by
      simp only [ProbabilityTheory.complexMGF, id_eq, neg_mul]
    have hconvμ : ProbabilityTheory.complexMGF id μ (-z) = ∫ x, Complex.exp (-(z * x)) ∂μ := by
      simp only [ProbabilityTheory.complexMGF, id_eq, neg_mul]
    show ProbabilityTheory.complexMGF id ν (-z) = ProbabilityTheory.complexMGF id μ (-z)
    rw [hconvν, hconvμ]
    have h1 := integral_cexp_neg_mul_eq_tsum hνint hr hsum hz2
    have h2 := integral_cexp_neg_mul_eq_tsum hμint hr hsumμ hz2
    rw [h1, h2]
    congr 1 with n
    rw [hmom n]
  have hEqOn : Set.EqOn (fun z : ℂ => ProbabilityTheory.complexMGF id ν (-z))
      (fun z : ℂ => ProbabilityTheory.complexMGF id μ (-z)) {z : ℂ | 0 < z.re} := by
    have hpre : IsPreconnected {z : ℂ | 0 < z.re} := (convex_halfSpace_re_gt 0).isPreconnected
    refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hanF hanG hpre
      (z₀ := ((r / 2 : ℝ) : ℂ)) ?_ ?_
    · simp only [Set.mem_ofPred_eq, Complex.ofReal_re]
      linarith
    · have hz₀ : ((r / 2 : ℝ) : ℂ) ∈ {z : ℂ | 0 < z.re ∧ ‖z‖ < r} := by
        simp only [Set.mem_ofPred_eq, Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by linarith : (0:ℝ) < r / 2)]
        constructor
        · linarith
        · linarith
      refine Filter.eventually_of_mem (IsOpen.mem_nhds ?_ hz₀) ?_
      · exact (isOpen_lt continuous_const Complex.continuous_re).inter
          (isOpen_lt continuous_norm continuous_const)
      · intro w hw
        exact hseries hw
  -- hence the characteristic functions agree
  have hchar : charFun μ = charFun ν := by
    funext u
    set c : ℕ → ℂ := fun n => Complex.ofReal (((n : ℝ) + 1)⁻¹) with hc
    have hw : ((u : ℂ) * Complex.I).re ≤ 0 := by simp
    have h1 := tendsto_complexMGF_sub_inv hν0 hw
    have h2 := tendsto_complexMGF_sub_inv hμ0 hw
    have heq : ∀ n : ℕ, ProbabilityTheory.complexMGF id ν ((u : ℂ) * Complex.I - c n)
        = ProbabilityTheory.complexMGF id μ ((u : ℂ) * Complex.I - c n) := by
      intro n
      have hcred : (c n).re = ((n : ℝ) + 1)⁻¹ := by
        rw [hc]
        exact Complex.ofReal_re _
      have hre0 : (((u : ℂ) * Complex.I).re) = 0 := by simp
      have hneg : 0 < (-((u : ℂ) * Complex.I - c n)).re := by
        simp only [Complex.neg_re, Complex.sub_re, hcred, hre0]
        have : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
        linarith
      have hFG := hEqOn hneg
      simpa using hFG
    have h2' : Tendsto (fun n : ℕ => ProbabilityTheory.complexMGF id μ ((u : ℂ) * Complex.I - c n))
        atTop (𝓝 (ProbabilityTheory.complexMGF id ν ((u : ℂ) * Complex.I))) :=
      h1.congr' (Filter.Eventually.of_forall heq)
    have hval : ProbabilityTheory.complexMGF id ν ((u : ℂ) * Complex.I)
        = ProbabilityTheory.complexMGF id μ ((u : ℂ) * Complex.I) :=
      tendsto_nhds_unique h2' h2
    rw [← ProbabilityTheory.complexMGF_id_mul_I u, ← ProbabilityTheory.complexMGF_id_mul_I u]
    simpa using hval.symm
  exact Measure.ext_of_charFun hchar

end PercLib.CriticalLRP.MomentProblem

/-! ### Axiom audit -/

#print axioms PercLib.CriticalLRP.MomentProblem.Measure.eq_of_forall_moment_eq_of_summable
#print axioms PercLib.CriticalLRP.MomentProblem.integral_cexp_neg_mul_eq_tsum
#print axioms PercLib.CriticalLRP.MomentProblem.mgf_eq_tsum_moment
#print axioms PercLib.CriticalLRP.MomentProblem.tendsto_complexMGF_sub_inv
#print axioms PercLib.CriticalLRP.MomentProblem.Iio_subset_interior_integrableExpSet
#print axioms PercLib.CriticalLRP.MomentProblem.summable_abs_moment_series
