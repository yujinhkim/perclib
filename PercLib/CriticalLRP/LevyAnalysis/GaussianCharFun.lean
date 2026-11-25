/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
The characteristic function of the explicit `Exp(1)`-Gaussian mixture `expGaussianMixture γ`:
`charFun (expGaussianMixture γ) u = (1 + B u u / 2)⁻¹` for `B = covarianceBilin γ`.

This is the same honest probability measure as in `GaussianMGF.lean`, so together the two files
identify the `α ≥ 2` (Brownian / Laplace) regime of Definition I.5.16 with a single explicit
pushforward: the law of `√T • Z` with `Z ~ γ`, `T ~ Exp(1)` independent.  Here the exponential
integral `∫_0^∞ e^{-t} e^{-t B u u/2} dt = (1 + B u u/2)⁻¹` converges for *every* `u` (the
characteristic function needs no restriction on `B u u`), which is why the domain
`{u | B u u < 2}` only appears for the moment generating function.
-/
module

public import PercLib.CriticalLRP.LevyAnalysis.GaussianMGF

set_option autoImplicit true

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology Pointwise

namespace PercLib.CriticalLRP.LevyAnalysis

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 400000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The covariance form at a rescaled vector: `B (c·u) (c·u) = c² B u u`. -/
theorem covarianceBilin_smul_smul (γ : Measure E) (u : E) (c : ℝ) :
    covarianceBilin γ (c • u) (c • u) = c ^ 2 * covarianceBilin γ u u := by
  rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.map_smul,
    smul_apply, smul_eq_mul, smul_eq_mul, sq]
  ring

/-- **The Gaussian integral of the exponential of a linear form at imaginary argument**: for
`t > 0`, `∫ z, exp (I * ⟪√t • z, u⟫) dγ = exp (-t B u u / 2)`. -/
theorem integral_cexp_smul_inner_gaussian (γ : Measure E) [IsGaussian γ]
    (hmean : ∫ x, id x ∂γ = 0) (u : E) {t : ℝ} (ht : 0 < t) :
    ∫ z, Complex.exp (↑(inner ℝ (Real.sqrt t • z) u) * Complex.I) ∂γ
      = Complex.exp (-((t * covarianceBilin γ u u / 2 : ℝ)) : ℂ) := by
  have h1 : ∀ z : E, Complex.exp (↑(inner ℝ (Real.sqrt t • z) u) * Complex.I)
      = Complex.exp (↑(inner ℝ z (Real.sqrt t • u)) * Complex.I) := by
    intro z
    rw [inner_smul_left, inner_smul_right]
    simp
  simp_rw [h1]
  rw [← charFun_apply, IsGaussian.charFun_eq', hmean]
  simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub]
  rw [covarianceBilin_smul_smul γ u (Real.sqrt t), Real.sq_sqrt ht.le]
  congr 1
  push_cast
  ring

/-- **The characteristic function of the explicit `Exp(1)`-Gaussian mixture**:
`charFun (expGaussianMixture γ) u = (1 + B u u / 2)⁻¹`. -/
theorem charFun_expGaussianMixture (γ : Measure E) [IsProbabilityMeasure γ] [IsGaussian γ]
    (hmean : ∫ x, id x ∂γ = 0) (u : E) :
    charFun (expGaussianMixture γ) u = (1 + ((covarianceBilin γ u u : ℝ) : ℂ) / 2)⁻¹ := by
  have hinner : ∀ t : ℝ, 0 < t →
      ∫ z, Complex.exp (↑(inner ℝ (Real.sqrt t • z) u) * Complex.I) ∂γ
        = Complex.exp (-((t * covarianceBilin γ u u / 2 : ℝ)) : ℂ) :=
    fun t ht => integral_cexp_smul_inner_gaussian γ hmean u ht
  have hstep1 : charFun (expGaussianMixture γ) u
      = ∫ t, (∫ z, Complex.exp (↑(inner ℝ (Real.sqrt t • z) u) * Complex.I) ∂γ)
          ∂expOne := by
    rw [charFun_apply, expGaussianMixture, integral_map measurable_expGaussianMixture_map.aemeasurable]
    · refine integral_prod _ ?_
      refine Integrable.of_bound (by fun_prop) 1 (Eventually.of_forall fun p => ?_)
      rw [Complex.norm_exp]
      simp
    · exact (by fun_prop : AEStronglyMeasurable
        (fun y : E => Complex.exp (↑(inner ℝ y u) * Complex.I))
        (Measure.map (fun p : ℝ × E => Real.sqrt p.1 • p.2) (expOne.prod γ)))
  rw [hstep1, integral_expOne]
  have hcongr : ∫ t in Ioi (0 : ℝ),
        (Real.exp (-t) : ℂ) * (∫ z, Complex.exp (↑(inner ℝ (Real.sqrt t • z) u) * Complex.I) ∂γ)
      = ∫ t in Ioi (0 : ℝ),
        (Real.exp (-t) : ℂ) * Complex.exp (-((t * covarianceBilin γ u u / 2 : ℝ)) : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [hinner t ht]
  rw [hcongr]
  have hcombine : ∀ t : ℝ,
      (Real.exp (-t) : ℂ) * Complex.exp (-((t * covarianceBilin γ u u / 2 : ℝ)) : ℂ)
        = ((Real.exp (-(((1 + covarianceBilin γ u u / 2) * t : ℝ))) : ℝ) : ℂ) := by
    intro t
    have h2 : Complex.exp (-((t * covarianceBilin γ u u / 2 : ℝ)) : ℂ)
        = ((Real.exp (-((t * covarianceBilin γ u u / 2) : ℝ)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    rw [h2, ← Complex.ofReal_mul, ← Real.exp_add,
      show (-t + -((t * covarianceBilin γ u u / 2))) = -(((1 + covarianceBilin γ u u / 2) * t))
        from by ring]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => hcombine t)]
  have hreal : ∫ t in Ioi (0 : ℝ), Real.exp (-(((1 + covarianceBilin γ u u / 2) * t : ℝ)))
      = (1 + covarianceBilin γ u u / 2)⁻¹ := by
    rw [show (fun t : ℝ => Real.exp (-(((1 + covarianceBilin γ u u / 2) * t : ℝ))))
        = fun t : ℝ => Real.exp ((-(1 + covarianceBilin γ u u / 2)) * t) from by
      funext t
      rw [neg_mul]]
    rw [integral_exp_mul_Ioi (a := -(1 + covarianceBilin γ u u / 2))
      (by linarith [covarianceBilin_self_nonneg (μ := γ) u]) 0, mul_zero, Real.exp_zero]
    field_simp
  calc ∫ t in Ioi (0 : ℝ), ((Real.exp (-(((1 + covarianceBilin γ u u / 2) * t : ℝ))) : ℝ) : ℂ)
      = ((∫ t in Ioi (0 : ℝ), Real.exp (-(((1 + covarianceBilin γ u u / 2) * t : ℝ))) : ℝ)
          : ℂ) := integral_ofReal
    _ = (((1 + covarianceBilin γ u u / 2)⁻¹ : ℝ) : ℂ) := by rw [hreal]
    _ = (((1 + covarianceBilin γ u u / 2 : ℝ)) : ℂ)⁻¹ := Complex.ofReal_inv _
    _ = (1 + ((covarianceBilin γ u u : ℝ) : ℂ) / 2)⁻¹ := by
        push_cast
        ring_nf

/-- **Definition I.5.16 and display (I.5.17) in the Gaussian regime, for one explicit honest
probability measure.**  `expGaussianMixture γ` is a probability measure; it has the
characteristic function `u ↦ (1 + B u u/2)⁻¹` that defines the `α ≥ 2` displacement law of
Definition I.5.16 (so, by `eq_of_charFun_laplace`, it *is* that law), and its moment generating
function is `u ↦ (1 - B u u/2)⁻¹` on the domain `{u | B u u < 2}` of display (I.5.17). -/
theorem charFun_and_integral_exp_expGaussianMixture (γ : Measure E) [IsProbabilityMeasure γ]
    [IsGaussian γ] (hmean : ∫ x, id x ∂γ = 0) :
    (∀ u : E, charFun (expGaussianMixture γ) u = (1 + ((covarianceBilin γ u u : ℝ) : ℂ) / 2)⁻¹)
      ∧ (∀ u : E, covarianceBilin γ u u < 2 →
          ∫ x, Real.exp (inner ℝ x u) ∂(expGaussianMixture γ)
            = (1 - covarianceBilin γ u u / 2)⁻¹) :=
  ⟨charFun_expGaussianMixture γ hmean, fun u hu =>
    integral_exp_inner_expGaussianMixture γ hmean u hu⟩

/-- **Canonicity**: the `α ≥ 2` displacement law of Definition I.5.16 is determined by its
characteristic function, so any probability measure with characteristic function
`u ↦ (1 + B u u/2)⁻¹` is the explicit exponential-Gaussian mixture.  (This is the Gaussian
analogue of `eq_of_charFun_levy` in `Dispersion.lean`.) -/
theorem eq_expGaussianMixture_of_charFun (γ : Measure E) [IsProbabilityMeasure γ] [IsGaussian γ]
    (hmean : ∫ x, id x ∂γ = 0) (ν : ProbabilityMeasure E)
    (hν : ∀ u : E, charFun (ν : Measure E) u = (1 + ((covarianceBilin γ u u : ℝ) : ℂ) / 2)⁻¹) :
    ν = ⟨expGaussianMixture γ, inferInstance⟩ := by
  have hmeq : (ν : Measure E) = expGaussianMixture γ := by
    refine Measure.ext_of_charFun ?_
    funext u
    rw [hν u]
    exact (charFun_expGaussianMixture γ hmean u).symm
  exact ProbabilityMeasure.toMeasure_injective hmeq

/-- The moment generating function identity (I.5.17) is a property of the *law*: it holds for
every probability measure with the characteristic function of the `α ≥ 2` displacement law.
(The Gaussian analogue of `forall_integral_exp_of_forall_charFun` in `DispersionMGF.lean`.) -/
theorem forall_integral_exp_of_forall_charFun_gaussian (γ : Measure E) [IsProbabilityMeasure γ]
    [IsGaussian γ] (hmean : ∫ x, id x ∂γ = 0) :
    ∀ ν : ProbabilityMeasure E,
      (∀ u : E, charFun (ν : Measure E) u
        = (1 + ((covarianceBilin γ u u : ℝ) : ℂ) / 2)⁻¹) →
      ∀ u : E, covarianceBilin γ u u < 2 →
        ∫ x, Real.exp (inner ℝ x u) ∂(ν : Measure E)
          = (1 - covarianceBilin γ u u / 2)⁻¹ := by
  intro ν hν u hu
  rw [eq_expGaussianMixture_of_charFun γ hmean ν hν]
  exact integral_exp_inner_expGaussianMixture γ hmean u hu

/-! ## A concrete instance: the standard Gaussian on `ℝ`

A non-vacuity check of the main theorem: for `γ = N(0,1)` on `E = ℝ` the covariance form is
`B u u = u²`, so the exponential-Gaussian mixture has MGF `u ↦ (1 - u²/2)⁻¹` for `|u| < √2`. -/

/-- For the standard Gaussian on `ℝ`, the explicit `Exp(1)`-Gaussian mixture has moment generating
function `u ↦ (1 - u²/2)⁻¹` on `(-√2, √2)`. -/
theorem integral_exp_stdGaussianReal_mixture (u : ℝ) (hu : u ^ 2 < 2) :
    ∫ x, Real.exp (u * x) ∂(expGaussianMixture (gaussianReal (0 : ℝ) 1))
      = (1 - u ^ 2 / 2)⁻¹ := by
  have hcov : covarianceBilin (gaussianReal (0 : ℝ) 1) u u = u ^ 2 := by
    rw [covarianceBilin_real_self]
    simp
  have h := integral_exp_inner_expGaussianMixture (gaussianReal (0 : ℝ) 1) (by simp) u
    (by rw [hcov]; exact hu)
  rw [hcov] at h
  simpa using h

/-- The same at the specific point `u = 1`: the exponential-Gaussian mixture of `N(0,1)` has
`∫ x, e^x d(expGaussianMixture (gaussianReal 0 1)) = 2`. -/
theorem integral_exp_stdGaussianReal_mixture_one :
    ∫ x, Real.exp (1 * x) ∂(expGaussianMixture (gaussianReal (0 : ℝ) 1)) = 2 := by
  rw [integral_exp_stdGaussianReal_mixture 1 (by norm_num)]
  norm_num

end PercLib.CriticalLRP.LevyAnalysis
