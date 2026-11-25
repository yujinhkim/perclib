/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
The Gaussian/Laplace regime of Definition I.5.16 and display (I.5.17) of
T. Hutchcroft, "Critical long-range percolation I: High effective dimension", arXiv:2508.18807v1.

For a centred Gaussian probability measure `γ` on a finite-dimensional real inner product space
`E` with covariance bilinear form `B = covarianceBilin γ`, this file constructs the
`Exp(1)`-Gaussian mixture -- the law of `√T • Z` with `Z ~ γ` and `T ~ Exp(1)` independent,
i.e. a Brownian motion with covariance `B` stopped at an independent unit exponential time --
as the *honest* pushforward `expGaussianMixture γ = (expOne.prod γ).map (fun p => √p.1 • p.2)`,
proves that it is a probability measure, and computes its moment generating function:

  `∫ x, exp ⟪x, u⟫ d(expGaussianMixture γ) = (1 - B u u / 2)⁻¹`   whenever `B u u < 2`.
-/
module

public import PercLib.CriticalLRP.LevyAnalysis.DispersionGaussian

set_option autoImplicit true

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology Pointwise
namespace PercLib.CriticalLRP.LevyAnalysis

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The exponential moment of a linear form under a centred Gaussian.**
For every real `s`, `∫ z, exp (s * ⟪z,u⟫) dγ = exp (s² * B u u / 2)`. -/
theorem integral_exp_mul_inner_gaussian (γ : Measure E) [IsGaussian γ]
    (hmean : ∫ x, id x ∂γ = 0) (u : E) (s : ℝ) :
    ∫ z, Real.exp (s * inner ℝ z u) ∂γ
      = Real.exp (s ^ 2 * covarianceBilin γ u u / 2) := by
  set L : E →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E u with hL
  have hLz : ∀ z : E, L z = inner ℝ u z := fun z => InnerProductSpace.toDual_apply_apply
  have hfun : (fun z : E => Real.exp (s * inner ℝ z u)) = fun z : E => Real.exp (s * L z) := by
    funext z
    rw [hLz z, real_inner_comm z u]
  have hmeanL : ∫ x, L x ∂γ = 0 := by
    rw [ContinuousLinearMap.integral_comp_id_comm (IsGaussian.integrable_id) L]
    rw [show (∫ x : E, x ∂γ) = 0 from hmean, map_zero]
  have hvarL : ProbabilityTheory.variance (fun z : E => L z) γ = covarianceBilin γ u u := by
    rw [covarianceBilin_self (IsGaussian.memLp_two_id) u]
    exact variance_congr (Eventually.of_forall fun z => hLz z)
  have hmap : γ.map L
      = gaussianReal 0 (ProbabilityTheory.variance (fun z : E => L z) γ).toNNReal := by
    rw [IsGaussian.map_eq_gaussianReal, hmeanL]
  rw [hfun]
  calc ∫ z, Real.exp (s * L z) ∂γ
      = mgf L γ s := rfl
    _ = mgf id (γ.map L) s := by rw [mgf_id_map (by fun_prop : AEMeasurable L γ)]
    _ = mgf id (gaussianReal 0 (ProbabilityTheory.variance (fun z : E => L z) γ).toNNReal) s := by
          rw [hmap]
    _ = Real.exp (0 * s + ((ProbabilityTheory.variance (fun z : E => L z) γ).toNNReal : ℝ)
            * s ^ 2 / 2) := by
          rw [mgf_id_gaussianReal]
    _ = Real.exp (s ^ 2 * covarianceBilin γ u u / 2) := by
          rw [Real.coe_toNNReal _ (variance_nonneg _ _), hvarL]
          ring_nf

/-- **Integrability of the exponential moment of a linear form** under a centred Gaussian:
`z ↦ exp (s * ⟪z,u⟫)` is integrable for every real `s`. -/
theorem integrable_exp_mul_inner_gaussian (γ : Measure E) [IsGaussian γ]
    (hmean : ∫ x, id x ∂γ = 0) (u : E) (s : ℝ) :
    Integrable (fun z : E => Real.exp (s * inner ℝ z u)) γ := by
  have hpos : 0 < mgf (fun z : E => inner ℝ z u) γ s := by
    show 0 < ∫ z, Real.exp (s * inner ℝ z u) ∂γ
    rw [integral_exp_mul_inner_gaussian γ hmean u s]
    exact Real.exp_pos _
  exact mgf_pos_iff.mp hpos

/-! ## The `Exp(1)`-Gaussian mixture as an honest probability measure

The `Exp(1)`-Gaussian mixture of Definition I.5.16 (the law of a Brownian motion with covariance
`B` at an independent unit exponential time) is the pushforward of `expOne ⊗ γ` under
`(t,z) ↦ √t • z`.  This is the *actual* exponential-Gaussian pushforward; nothing about it is
hypothetical.  -/

/-- The `Exp(1)`-Gaussian mixture: the pushforward of `Exp(1) ⊗ γ` under `(t,z) ↦ √t • z`. -/
noncomputable def expGaussianMixture (γ : Measure E) : Measure E :=
  (expOne.prod γ).map (fun p : ℝ × E => Real.sqrt p.1 • p.2)

theorem measurable_expGaussianMixture_map :
    Measurable fun p : ℝ × E => Real.sqrt p.1 • p.2 := by fun_prop

/-- The `Exp(1)`-Gaussian mixture of a probability measure is a probability measure. -/
instance isProbabilityMeasure_expGaussianMixture (γ : Measure E) [IsProbabilityMeasure γ] :
    IsProbabilityMeasure (expGaussianMixture γ) where
  measure_univ := by
    rw [expGaussianMixture, Measure.map_apply measurable_expGaussianMixture_map MeasurableSet.univ,
      Set.preimage_univ, ← Set.univ_prod_univ, Measure.prod_prod, expOne_univ, measure_univ,
      mul_one]

/-! ## The Fubini computation and the moment generating function (I.5.17)

Tonelli's theorem on the domain `(0,∞) × E` (all integrands are nonnegative, so no integrability
of the mixture is needed up front):
`∫⁻ x, exp ⟪x,u⟫ d(expGaussianMixture γ) = ∫⁻ t in (0,∞), e^{-t} ∫⁻ z, exp (√t ⟪z,u⟫) dγ`.
The inner integral is `exp (t B u u / 2)` by `integral_exp_mul_inner_gaussian`, and what is left
is the elementary exponential integral `∫₀^∞ e^{-t} e^{t B u u/2} dt = (1 - B u u/2)⁻¹`, valid
exactly on the domain `B u u < 2` of (I.5.17). -/

/-- The inner (Gaussian) integral of the Tonelli computation, as a lower integral. -/
theorem lintegral_ofReal_exp_smul_inner_gaussian (γ : Measure E) [IsGaussian γ]
    (hmean : ∫ x, id x ∂γ = 0) (u : E) (t : ℝ) (ht : 0 < t) :
    ∫⁻ z, ENNReal.ofReal (Real.exp (inner ℝ (Real.sqrt t • z) u)) ∂γ
      = ENNReal.ofReal (Real.exp (t * covarianceBilin γ u u / 2)) := by
  have hfun : (fun z : E => ENNReal.ofReal (Real.exp (inner ℝ (Real.sqrt t • z) u)))
      = fun z : E => ENNReal.ofReal (Real.exp (Real.sqrt t * inner ℝ z u)) := by
    funext z
    rw [inner_smul_left]
    simp
  rw [hfun, ← ofReal_integral_eq_lintegral_ofReal
    (integrable_exp_mul_inner_gaussian γ hmean u (Real.sqrt t))
    (Eventually.of_forall fun z => (Real.exp_pos _).le)]
  rw [integral_exp_mul_inner_gaussian γ hmean u (Real.sqrt t), Real.sq_sqrt ht.le]

/-- **The `ℝ≥0∞` form of the moment generating identity (I.5.17) for the `Exp(1)`-Gaussian
mixture**: `∫⁻ x, exp ⟪x,u⟫ d(expGaussianMixture γ) = (1 - B u u/2)⁻¹` for `B u u < 2`. -/
theorem lintegral_ofReal_exp_inner_expGaussianMixture (γ : Measure E) [IsGaussian γ]
    (hmean : ∫ x, id x ∂γ = 0) (u : E) (hu : covarianceBilin γ u u < 2) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (inner ℝ x u)) ∂(expGaussianMixture γ)
      = ENNReal.ofReal ((1 - covarianceBilin γ u u / 2)⁻¹) := by
  have hinner : ∀ t : ℝ, 0 < t →
      ∫⁻ z, ENNReal.ofReal (Real.exp (inner ℝ (Real.sqrt t • z) u)) ∂γ
        = ENNReal.ofReal (Real.exp (t * covarianceBilin γ u u / 2)) :=
    lintegral_ofReal_exp_smul_inner_gaussian γ hmean u
  have hmeas : Measurable fun t : ℝ =>
      ∫⁻ z, ENNReal.ofReal (Real.exp (inner ℝ (Real.sqrt t • z) u)) ∂γ := by fun_prop
  calc ∫⁻ x, ENNReal.ofReal (Real.exp (inner ℝ x u)) ∂(expGaussianMixture γ)
      = ∫⁻ p, ENNReal.ofReal (Real.exp (inner ℝ (Real.sqrt p.1 • p.2) u))
          ∂(expOne.prod γ) := by
        rw [expGaussianMixture, lintegral_map (by fun_prop) measurable_expGaussianMixture_map]
    _ = ∫⁻ t, (∫⁻ z, ENNReal.ofReal (Real.exp (inner ℝ (Real.sqrt t • z) u)) ∂γ)
          ∂expOne := by
        rw [lintegral_prod _ (by fun_prop)]
    _ = ∫⁻ t in Ioi (0 : ℝ),
          ENNReal.ofReal (Real.exp (-t))
            * (∫⁻ z, ENNReal.ofReal (Real.exp (inner ℝ (Real.sqrt t • z) u)) ∂γ) := by
        rw [expOne, lintegral_withDensity_eq_lintegral_mul (volume.restrict (Ioi (0 : ℝ)))
          (by fun_prop : Measurable
          fun t : ℝ => ENNReal.ofReal (Real.exp (-t))) hmeas]
        simp only [Pi.mul_apply]
    _ = ∫⁻ t in Ioi (0 : ℝ),
          ENNReal.ofReal (Real.exp (-t)) * ENNReal.ofReal (Real.exp (t * covarianceBilin γ u u / 2)) := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
        rw [hinner t ht]
    _ = ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-t) * Real.exp (t * covarianceBilin γ u u / 2)) := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
        rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
    _ = ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp ((covarianceBilin γ u u / 2 - 1) * t)) := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
        congr 1
        rw [← Real.exp_add]
        congr 1
        ring
    _ = ENNReal.ofReal (∫ t in Ioi (0 : ℝ), Real.exp ((covarianceBilin γ u u / 2 - 1) * t)) := by
        rw [ofReal_integral_eq_lintegral_ofReal
          (integrableOn_exp_mul_Ioi (by linarith) 0)
          (Eventually.of_forall fun t => (Real.exp_pos _).le)]
    _ = ENNReal.ofReal ((1 - covarianceBilin γ u u / 2)⁻¹) := by
        rw [integral_exp_mul_Ioi (by linarith : covarianceBilin γ u u / 2 - 1 < 0) 0, mul_zero,
          Real.exp_zero]
        congr 1
        rw [show (1 - covarianceBilin γ u u / 2) = -(covarianceBilin γ u u / 2 - 1) by ring,
          inv_neg]
        ring

/-- **The exponential moment of the mixture is finite** on the domain of (I.5.17): the MGF is an
honest finite integral, not merely a formal expression. -/
theorem integrable_exp_inner_expGaussianMixture (γ : Measure E) [IsProbabilityMeasure γ]
    [IsGaussian γ] (hmean : ∫ x, id x ∂γ = 0) (u : E) (hu : covarianceBilin γ u u < 2) :
    Integrable (fun x : E => Real.exp (inner ℝ x u)) (expGaussianMixture γ) := by
  refine (lintegral_ofReal_ne_top_iff_integrable
    (by fun_prop : AEStronglyMeasurable (fun x : E => Real.exp (inner ℝ x u))
      (expGaussianMixture γ))
    (Eventually.of_forall fun x => (Real.exp_pos _).le)).mp ?_
  rw [lintegral_ofReal_exp_inner_expGaussianMixture γ hmean u hu]
  exact ENNReal.ofReal_ne_top

/-- **Display (I.5.17) in the Gaussian regime, for the explicit exponential-Gaussian
pushforward**: if `γ` is a centred Gaussian probability measure on `E` and `B = covarianceBilin γ`,
then the moment generating function of the `Exp(1)`-Gaussian mixture `expGaussianMixture γ` is
`u ↦ (1 - B u u / 2)⁻¹` on the domain `B u u < 2`. -/
theorem integral_exp_inner_expGaussianMixture (γ : Measure E) [IsProbabilityMeasure γ]
    [IsGaussian γ] (hmean : ∫ x, id x ∂γ = 0) (u : E)
    (hu : covarianceBilin γ u u < 2) :
    ∫ x, Real.exp (inner ℝ x u) ∂(expGaussianMixture γ)
      = (1 - covarianceBilin γ u u / 2)⁻¹ := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => (Real.exp_pos _).le)
    (by fun_prop : AEStronglyMeasurable (fun x : E => Real.exp (inner ℝ x u))
      (expGaussianMixture γ))]
  rw [lintegral_ofReal_exp_inner_expGaussianMixture γ hmean u hu, ENNReal.toReal_ofReal]
  exact (inv_pos.mpr (by linarith : (0 : ℝ) < 1 - covarianceBilin γ u u / 2)).le

/-- **Definition I.5.16 and display (I.5.17) in the Gaussian regime.**  For a centred Gaussian
probability measure `γ` on a finite-dimensional real inner product space `E` there is an honest
probability measure `ν` -- namely the exponential-Gaussian mixture `expGaussianMixture γ`, the law
of `√T • Z` with `Z ~ γ` and `T ~ Exp(1)` independent -- whose moment generating function is
`u ↦ (1 - B u u / 2)⁻¹` on the domain `{u | B u u < 2}` of (I.5.17), where `B = covarianceBilin γ`
is the covariance form of `γ`. -/
theorem exists_expGaussianMixture_mgf (γ : Measure E) [IsProbabilityMeasure γ] [IsGaussian γ]
    (hmean : ∫ x, id x ∂γ = 0) :
    ∃ ν : ProbabilityMeasure E, ∀ u : E, covarianceBilin γ u u < 2 →
      ∫ x, Real.exp (inner ℝ x u) ∂(ν : Measure E) = (1 - covarianceBilin γ u u / 2)⁻¹ :=
  ⟨⟨expGaussianMixture γ, inferInstance⟩, fun u hu =>
    integral_exp_inner_expGaussianMixture γ hmean u hu⟩

/-- **Version with an explicit covariance form `B`** (the form in which the problem is usually
stated): if `B` is the covariance form of the centred Gaussian `γ`, i.e. `B u u = B_γ u u` for all
`u`, then the `Exp(1)`-Gaussian mixture has moment generating function `u ↦ (1 - B u u/2)⁻¹` on
`{u | B u u < 2}`. -/
theorem exists_expGaussianMixture_mgf_of_covarianceBilin (γ : Measure E) [IsProbabilityMeasure γ]
    [IsGaussian γ] (hmean : ∫ x, id x ∂γ = 0) (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ u : E, covarianceBilin γ u u = B u u) :
    ∃ ν : ProbabilityMeasure E, ∀ u : E, B u u < 2 →
      ∫ x, Real.exp (inner ℝ x u) ∂(ν : Measure E) = (1 - B u u / 2)⁻¹ := by
  obtain ⟨ν, hν⟩ := exists_expGaussianMixture_mgf γ hmean
  refine ⟨ν, fun u hu => ?_⟩
  have hu' : covarianceBilin γ u u < 2 := by rw [hB u]; exact hu
  rw [← hB u]
  exact hν u hu'

/-- The same statement with the covariance operator `rieszOp (covarianceBilin γ)` of
`DispersionGaussian.lean`, i.e. `⟨B u, u⟩ = covarianceBilin γ u u`; this is the exact Gaussian
analogue of the `α < 2` display (I.5.17) proved in `DispersionMGF.lean`. -/
theorem exists_expGaussianMixture_mgf_rieszOp (γ : Measure E) [Nontrivial E]
    [IsProbabilityMeasure γ] [IsGaussian γ] (hmean : ∫ x, id x ∂γ = 0) :
    ∃ ν : ProbabilityMeasure E, ∀ u : E, inner ℝ (rieszOp (covarianceBilin γ) u) u < 2 →
      ∫ x, Real.exp (inner ℝ x u) ∂(ν : Measure E)
        = (1 - inner ℝ (rieszOp (covarianceBilin γ) u) u / 2)⁻¹ := by
  obtain ⟨ν, hν⟩ := exists_expGaussianMixture_mgf γ hmean
  refine ⟨ν, fun u hu => ?_⟩
  rw [rieszOp_inner] at hu ⊢
  exact hν u hu

end PercLib.CriticalLRP.LevyAnalysis
