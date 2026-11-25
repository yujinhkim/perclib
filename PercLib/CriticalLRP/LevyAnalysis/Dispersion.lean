/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Formalization derived from T. Hutchcroft, "Critical long-range percolation I: High effective
dimension", arXiv:2508.18807v1, Definition I.5.16 and display (I.5.17):

the limiting displacement law `ν_disp` is "the law of the symmetric Lévy jump process with
Lévy measure `Pi₁` stopped at an independent `Exp(1)`-distributed random time", and its
moment generating function is
```
E[e^{⟨L_T,u⟩}] = (1 - ∫ (cosh ⟨u,x⟩ - 1) dPi₁)⁻¹ .
```

This file *constructs* that law as an honest probability measure, without invoking the
existence of a Lévy process.  Two regimes, exactly as in Definition I.5.16.

* α < 2 (`LevyAnalysis/nuDispExists`): the exponential-time law of the symmetric jump process
  with Lévy measure `Pi` is realized as the weak limit of explicit *compound geometric* laws
  `∑_k (1+Λ_ε)^{-(k+1)} (Pi_ε)^{*k}` of the finite truncations `Pi_ε = Pi(· ∩ {‖x‖ > ε})`.
  Since `Pi_ε` is finite, the corresponding symmetric jump process is a compound Poisson process,
  and the exponential-time mixture of a compound Poisson process is a compound *geometric*
  distribution: this is an explicit countable convex combination of convolution powers, hence a
  measure with no process theory behind it.  Its characteristic function is exactly
  `u ↦ (1 + ψ_ε(u))⁻¹` with `ψ_ε(u) = ∫_{‖x‖>ε} (1 - cos⟨u,x⟩) dPi`, and Lévy's continuity
  theorem identifies the limit as a probability measure with characteristic function
  `u ↦ (1 + ψ(u))⁻¹`.

* α ≥ 2 (the Brownian / Laplace regime): the law of `B_T` with `B` a Brownian motion of
  covariance `Σ` and `T ~ Exp(1)` independent is realized *explicitly* as the pushforward of
  `Exp(1) ⊗ N(0,Σ)` under `(t, z) ↦ t^{1/2} z`; its characteristic function is
  `u ↦ (1 + ⟨Σu,u⟩/2)⁻¹`.

Scope and honesty notes.
* Mathlib's `charFun` requires an inner product space, so the results here are stated for a
  finite-dimensional real inner product space `E`.  The paper allows an arbitrary norm `‖·‖` in
  (I.5.16); the pairing `⟨u,x⟩` there is a general continuous linear functional.  The π-system /
  Cramér–Wold variant for arbitrary norms is *not* formalized here (see the final section).
* The MGF identity `(I.5.17)` with `cosh` (analytic continuation off the imaginary axis) is not
  asserted; only the characteristic-function identity is proved.  The `cosh` Taylor series that
  the paper feeds into Proposition I.5.14 is available in `LevyCosh`/`LevyOddPart`.
* Absolute continuity of `ν_disp` (Lemma I.5.17) is *not* proved here.
-/
module

public import Mathlib
public import PercLib.CriticalLRP.LevyAnalysis.LevyOddPart

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal Topology Pointwise

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace PercLib.CriticalLRP.LevyAnalysis

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-! ## Elementary bounds on `1 - cos` -/

theorem one_sub_cos_nonneg (x : ℝ) : 0 ≤ 1 - Real.cos x := by
  linarith [Real.cos_le_one x]

theorem one_sub_cos_le_half_sq (x : ℝ) : 1 - Real.cos x ≤ x ^ 2 / 2 := by
  linarith [Real.one_sub_sq_div_two_le_cos (x := x)]

theorem one_sub_cos_le_two (x : ℝ) : 1 - Real.cos x ≤ 2 := by
  linarith [Real.neg_one_le_cos x]

/-- The key pointwise domination of the Lévy integrand by the Lévy-measure test function
`‖x‖² ∧ 1`. -/
theorem one_sub_cos_inner_le (u x : E) :
    1 - Real.cos (inner ℝ x u) ≤ 2 * max (‖u‖ ^ 2) 1 * min (‖x‖ ^ 2) 1 := by
  have hsq : (inner ℝ x u) ^ 2 ≤ ‖x‖ ^ 2 * ‖u‖ ^ 2 := by
    have h := abs_real_inner_le_norm x u
    have h1 : |inner ℝ x u| ^ 2 ≤ (‖x‖ * ‖u‖) ^ 2 := by
      apply pow_le_pow_left₀ (abs_nonneg _) h
    rwa [sq_abs, mul_pow] at h1
  have hmaxu : ‖u‖ ^ 2 ≤ max (‖u‖ ^ 2) 1 := le_max_left _ _
  have hmax1 : (1 : ℝ) ≤ max (‖u‖ ^ 2) 1 := le_max_right _ _
  have hxnn : (0 : ℝ) ≤ ‖x‖ ^ 2 := by positivity
  rcases le_or_gt (‖x‖ ^ 2) 1 with hx | hx
  · rw [min_eq_left hx]
    nlinarith [one_sub_cos_le_half_sq (inner ℝ x u), one_sub_cos_nonneg (inner ℝ x u)]
  · rw [min_eq_right hx.le]
    nlinarith [one_sub_cos_le_two (inner ℝ x u)]

/-! ## The Lévy exponent `ψ` -/

/-- The Lévy exponent of a symmetric Lévy measure `Pi`:
`ψ(u) = ∫ (1 - cos ⟪x,u⟫) dPi`.  For `Pi` which is only `σ`-finite, this Bochner integral is
meaningful precisely because `(‖x‖² ∧ 1)` is `Pi`-integrable; the integrability is proved in
`integrable_one_sub_cos_inner` below, and every statement about `levyPsi` carries it as a
hypothesis. -/
noncomputable def levyPsi (Pi : Measure E) (u : E) : ℝ :=
  ∫ x, (1 - Real.cos (inner ℝ x u)) ∂Pi

theorem levyPsi_nonneg (Pi : Measure E) (u : E) : 0 ≤ levyPsi Pi u :=
  integral_nonneg fun x => one_sub_cos_nonneg _

theorem levyPsi_zero (Pi : Measure E) : levyPsi Pi 0 = 0 := by
  simp [levyPsi]

/-- `‖x‖² ∧ 1` is `Pi`-integrable as soon as its `Pi`-integral is finite. -/
theorem integrable_min_norm_sq (Pi : Measure E)
    (hPi : ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂Pi ≠ ⊤) :
    Integrable (fun x : E => min (‖x‖ ^ 2) 1) Pi :=
  (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
    (Eventually.of_forall fun x => le_min (by positivity) zero_le_one)).mp hPi

/-- The Lévy integrand `x ↦ 1 - cos ⟪x,u⟫` is `Pi`-integrable for every `u`, for every symmetric
Lévy measure `Pi` in the sense `∫ (‖x‖² ∧ 1) dPi < ∞`. -/
theorem integrable_one_sub_cos_inner (Pi : Measure E)
    (hPi : ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂Pi ≠ ⊤) (u : E) :
    Integrable (fun x => 1 - Real.cos (inner ℝ x u)) Pi := by
  have hInt := integrable_min_norm_sq (Pi := Pi) hPi
  refine Integrable.mono' (hInt.const_mul (2 * max (‖u‖ ^ 2) 1)) (by fun_prop) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (one_sub_cos_nonneg _)]
  exact one_sub_cos_inner_le u x

/-- **Continuity of the Lévy exponent at the origin.**  This is the hypothesis needed to apply
Lévy's continuity theorem to the constructions below. -/
theorem tendsto_levyPsi_zero (Pi : Measure E)
    (hPi : ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂Pi ≠ ⊤) :
    Tendsto (levyPsi Pi) (𝓝 0) (𝓝 0) := by
  have hInt := integrable_min_norm_sq (Pi := Pi) hPi
  have hbound : Integrable (fun x : E => 2 * min (‖x‖ ^ 2) 1) Pi := hInt.const_mul 2
  have hmain : Tendsto (fun u : E => ∫ x, (1 - Real.cos (inner ℝ x u)) ∂Pi) (𝓝 0)
      (𝓝 (∫ x, (0 : ℝ) ∂Pi)) := by
    refine tendsto_integral_filter_of_dominated_convergence (l := 𝓝 (0 : E))
      (F := fun u x => 1 - Real.cos (inner ℝ x u)) (f := fun _ => 0)
      (bound := fun x : E => 2 * min (‖x‖ ^ 2) 1) ?_ ?_ hbound ?_
    · filter_upwards with u
      fun_prop
    · filter_upwards [Metric.ball_mem_nhds (0 : E) (by norm_num : (0 : ℝ) < 1)] with u hu
      have hu1 : ‖u‖ ≤ 1 := by
        have : ‖u - 0‖ < 1 := by simpa using hu
        simpa using this.le
      have hmax : max (‖u‖ ^ 2) 1 = 1 := by
        rw [max_eq_right]
        nlinarith [norm_nonneg u]
      filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (one_sub_cos_nonneg _)]
      have h := one_sub_cos_inner_le u x
      rw [hmax] at h
      simpa using h
    · filter_upwards with x
      have hcont : Continuous fun u : E => 1 - Real.cos (inner ℝ x u) := by fun_prop
      simpa using hcont.tendsto 0
  show Tendsto (fun u : E => ∫ x, (1 - Real.cos (inner ℝ x u)) ∂Pi) (𝓝 0) (𝓝 0)
  simpa using hmain

/-! ## Convolution powers and the compound geometric law

For a *finite* measure `ρ` on `E` (the truncated Lévy measure), the symmetric jump process with
Lévy measure `ρ` is a compound Poisson process.  Its exponential-time marginal is the law of
`∑_{j ≤ N} J_j` with `N` geometric and `J_j` i.i.d. of law `ρ`, i.e. the countable convex
combination `∑_k (1+Λ)^{-(k+1)} ρ^{*k}` with `Λ = ρ(E)`.  We build this measure directly, so no
Lévy process theory is needed. -/

/-- Convolution of two measures on the additive group `E`. -/
noncomputable def addConv (μ ν : Measure E) : Measure E :=
  (μ.prod ν).map (fun p : E × E => p.1 + p.2)

/-- Convolution powers `ρ^{*k}` of a measure `ρ` on `E`. -/
noncomputable def convPow (ρ : Measure E) : ℕ → Measure E
  | 0 => Measure.dirac 0
  | k + 1 => addConv (convPow ρ k) ρ

theorem addConv_univ (μ ν : Measure E) [SFinite μ] [SFinite ν] :
    addConv μ ν univ = μ univ * ν univ := by
  rw [addConv, Measure.map_apply measurable_add MeasurableSet.univ, Set.preimage_univ,
    ← Set.univ_prod_univ, Measure.prod_prod]

instance instIsFiniteMeasureAddConv (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    IsFiniteMeasure (addConv μ ν) where
  measure_univ_lt_top := by
    have : SFinite μ := inferInstance
    have : SFinite ν := inferInstance
    rw [addConv_univ]
    exact ENNReal.mul_lt_top (measure_lt_top μ univ) (measure_lt_top ν univ)

instance instIsFiniteMeasureConvPow (ρ : Measure E) [IsFiniteMeasure ρ] (k : ℕ) :
    IsFiniteMeasure (convPow ρ k) := by
  induction k with
  | zero => exact ⟨by simp [convPow]⟩
  | succ k ih =>
      have := ih
      exact instIsFiniteMeasureAddConv (convPow ρ k) ρ

theorem convPow_univ (ρ : Measure E) [IsFiniteMeasure ρ] :
    ∀ k : ℕ, convPow ρ k univ = (ρ univ) ^ k
  | 0 => by simp [convPow]
  | k + 1 => by
      have := instIsFiniteMeasureConvPow ρ k
      rw [convPow, addConv_univ, convPow_univ ρ k, pow_succ]

/-- The characteristic function of a convolution is the product of characteristic functions. -/
theorem charFun_addConv (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (u : E) :
    charFun (addConv μ ν) u = charFun μ u * charFun ν u := by
  have hfs : ∀ p : E × E, Complex.exp (↑(inner ℝ (p.1 + p.2) u) * Complex.I)
      = Complex.exp (↑(inner ℝ p.1 u) * Complex.I)
        * Complex.exp (↑(inner ℝ p.2 u) * Complex.I) := by
    intro p
    rw [← Complex.exp_add, inner_add_left]
    push_cast
    ring
  rw [charFun_apply, addConv, integral_map measurable_add.aemeasurable]
  · simp_rw [hfs]
    have := integral_prod_mul (μ := μ) (ν := ν)
      (f := fun x : E => Complex.exp (↑(inner ℝ x u) * Complex.I))
      (g := fun y : E => Complex.exp (↑(inner ℝ y u) * Complex.I))
    simpa only [charFun_apply] using this
  · exact (by fun_prop : AEStronglyMeasurable
      (fun y : E => Complex.exp (↑(inner ℝ y u) * Complex.I))
      (Measure.map (fun p : E × E => p.1 + p.2) (μ.prod ν)))

/-- The characteristic function of the `k`-th convolution power is the `k`-th power. -/
theorem charFun_convPow (ρ : Measure E) [IsFiniteMeasure ρ] :
    ∀ (k : ℕ) (u : E), charFun (convPow ρ k) u = (charFun ρ u) ^ k
  | 0, u => by
      rw [convPow, charFun_dirac]
      simp
  | k + 1, u => by
      have := instIsFiniteMeasureConvPow ρ k
      rw [convPow, charFun_addConv, charFun_convPow ρ k u, pow_succ]

/-- The characteristic function of a countable sum of measures is the sum of the characteristic
functions (when the total mass is finite). -/
theorem charFun_measure_sum (f : ℕ → Measure E) (hmass : (Measure.sum f) univ ≠ ⊤) (u : E) :
    charFun (Measure.sum f) u = ∑' k, charFun (f k) u := by
  have hfin : IsFiniteMeasure (Measure.sum f) := ⟨lt_top_iff_ne_top.mpr hmass⟩
  have hInt : Integrable (fun x : E => Complex.exp (↑(inner ℝ x u) * Complex.I))
      (Measure.sum f) := by
    refine Integrable.of_bound (by fun_prop) 1 (Eventually.of_forall fun x => ?_)
    rw [Complex.norm_exp]
    simp
  rw [charFun_apply, integral_sum_measure hInt]
  simp only [charFun_apply]

/-- **The exponential-time law of a finite symmetric Lévy measure** `ρ`:
`∑_{k≥0} (1+Λ)^{-(k+1)} ρ^{*k}` with `Λ = ρ(E)`. -/
noncomputable def expGeom (ρ : Measure E) : Measure E :=
  Measure.sum fun k => ENNReal.ofReal ((1 + ρ.real univ)⁻¹ ^ (k + 1)) • convPow ρ k

theorem expGeom_univ (ρ : Measure E) [IsFiniteMeasure ρ] : expGeom ρ univ = 1 := by
  rw [expGeom, Measure.sum_apply _ MeasurableSet.univ]
  set Λ := ρ.real univ with hΛ
  have hΛnn : 0 ≤ Λ := by rw [hΛ, Measure.real_def]; exact ENNReal.toReal_nonneg
  set c : ℝ := (1 + Λ)⁻¹ with hc
  have hcpos : 0 < c := by positivity
  have hcΛ_lt : c * Λ < 1 := by
    rw [hc, inv_mul_eq_div, div_lt_one (by linarith)]
    linarith
  have hgeom : ∑' k : ℕ, c ^ (k + 1) * Λ ^ k = 1 := by
    have h1 : ∀ k : ℕ, c ^ (k + 1) * Λ ^ k = c * (c * Λ) ^ k := by
      intro k
      rw [mul_pow, pow_succ]
      ring
    simp_rw [h1]
    rw [tsum_mul_left,
      tsum_geometric_of_norm_lt_one
        (by rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hcΛ_lt)]
    have hden : 1 - c * Λ = c := by
      rw [hc]
      field_simp
      ring
    rw [hden, mul_inv_cancel₀ (ne_of_gt hcpos)]
  have hterm : ∀ k : ℕ, (ENNReal.ofReal (c ^ (k + 1)) • convPow ρ k) univ
      = ENNReal.ofReal (c ^ (k + 1) * Λ ^ k) := by
    intro k
    have hΛcast : ρ univ = ENNReal.ofReal Λ := by
      rw [hΛ, Measure.real_def, ENNReal.ofReal_toReal (measure_ne_top ρ univ)]
    rw [Measure.smul_apply, smul_eq_mul, convPow_univ, hΛcast,
      ← ENNReal.ofReal_pow hΛnn,
      ← ENNReal.ofReal_mul (by positivity)]
  have hsummable : Summable fun k : ℕ => c ^ (k + 1) * Λ ^ k := by
    have h1 : Summable fun k : ℕ => c * (c * Λ) ^ k :=
      Summable.mul_left _ (summable_geometric_of_norm_lt_one
        (by rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hcΛ_lt))
    simpa only [show ∀ k : ℕ, c ^ (k + 1) * Λ ^ k = c * (c * Λ) ^ k from fun k => by
      rw [mul_pow, pow_succ]; ring] using h1
  simp_rw [hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsummable, hgeom,
    ENNReal.ofReal_one]

instance instIsProbabilityMeasureExpGeom (ρ : Measure E) [IsFiniteMeasure ρ] :
    IsProbabilityMeasure (expGeom ρ) :=
  ⟨expGeom_univ ρ⟩

/-- **A finite symmetric measure has real characteristic function `Λ - ψ`.** -/
theorem charFun_eq_real_sub (ρ : Measure E) [IsFiniteMeasure ρ]
    (hρ : Measure.map (fun x : E => -x) ρ = ρ) (u : E) :
    charFun ρ u = ((ρ.real univ : ℝ) : ℂ) - ((levyPsi ρ u : ℝ) : ℂ) := by
  have hcos_int : Integrable (fun x : E => Real.cos (inner ℝ x u)) ρ :=
    Integrable.of_bound (by fun_prop) 1
      (Eventually.of_forall fun x => by simpa using Real.abs_cos_le_one _)
  have hsin_int : Integrable (fun x : E => Real.sin (inner ℝ x u)) ρ :=
    Integrable.of_bound (by fun_prop) 1
      (Eventually.of_forall fun x => by simpa using Real.abs_sin_le_one (inner ℝ x u))
  have hsin_zero : ∫ x, Real.sin (inner ℝ x u) ∂ρ = 0 := by
    refine integral_eq_zero_of_odd_of_map_neg_eq_self hρ hsin_int (fun x => ?_)
    rw [inner_neg_left, Real.sin_neg]
  have hone : ∫ x : E, (1 : ℝ) ∂ρ = ρ.real univ := by
    rw [integral_const]
    simp
  have hcos_eq : ∫ x, Real.cos (inner ℝ x u) ∂ρ = ρ.real univ - levyPsi ρ u := by
    have h2 : ∫ x, (1 - Real.cos (inner ℝ x u)) ∂ρ
        = ∫ x, (1 : ℝ) ∂ρ - ∫ x, Real.cos (inner ℝ x u) ∂ρ :=
      integral_sub (integrable_const 1) hcos_int
    have h3 : ∫ x, (1 - Real.cos (inner ℝ x u)) ∂ρ = levyPsi ρ u := rfl
    linarith [h2, h3, hone]
  have hcosC : Integrable (fun x : E => (Real.cos (inner ℝ x u) : ℂ)) ρ :=
    Integrable.of_bound (by fun_prop) 1
      (Eventually.of_forall fun x => by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact Real.abs_cos_le_one _)
  have hsinC : Integrable (fun x : E => (Real.sin (inner ℝ x u) : ℂ) * Complex.I) ρ :=
    (Integrable.of_bound (by fun_prop) 1
      (Eventually.of_forall fun x => by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact Real.abs_sin_le_one _)).mul_const Complex.I
  have hsplit : ∫ x, Complex.exp (↑(inner ℝ x u) * Complex.I) ∂ρ
      = ((∫ x, Real.cos (inner ℝ x u) ∂ρ : ℝ) : ℂ)
        + ((∫ x, Real.sin (inner ℝ x u) ∂ρ : ℝ) : ℂ) * Complex.I := by
    have h1 : ∫ x, Complex.exp (↑(inner ℝ x u) * Complex.I) ∂ρ
        = ∫ x, ((Real.cos (inner ℝ x u) : ℂ) + (Real.sin (inner ℝ x u) : ℂ) * Complex.I) ∂ρ := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      exact Complex.exp_ofReal_mul_I _
    rw [h1, integral_add hcosC hsinC]
    refine congrArg₂ (· + ·) ?_ ?_
    · exact integral_ofReal
    · rw [integral_mul_const]
      exact congrArg (· * Complex.I) integral_ofReal
  rw [charFun_apply, hsplit, hsin_zero, hcos_eq, Complex.ofReal_zero, zero_mul, add_zero,
    ← Complex.ofReal_sub]

/-- **The exponential-time compound geometric law has characteristic function `(1+ψ)⁻¹`.** -/
theorem charFun_expGeom (ρ : Measure E) [IsFiniteMeasure ρ]
    (hρ : Measure.map (fun x : E => -x) ρ = ρ) (u : E) :
    charFun (expGeom ρ) u = ((1 + levyPsi ρ u : ℝ) : ℂ)⁻¹ := by
  have hmass : (Measure.sum fun k =>
      ENNReal.ofReal ((1 + ρ.real univ)⁻¹ ^ (k + 1)) • convPow ρ k) univ ≠ ⊤ := by
    rw [← expGeom, expGeom_univ]
    exact ENNReal.one_ne_top
  rw [expGeom, charFun_measure_sum _ hmass u]
  set Λ := ρ.real univ with hΛ
  have hΛnn : 0 ≤ Λ := by rw [hΛ, Measure.real_def]; exact ENNReal.toReal_nonneg
  set c : ℝ := (1 + Λ)⁻¹ with hc
  have hcpos : 0 < c := by positivity
  have hcΛ : c * Λ = 1 - c := by
    rw [hc]
    field_simp
    ring
  have hφ : charFun ρ u = ((Λ : ℝ) : ℂ) - ((levyPsi ρ u : ℝ) : ℂ) := by
    rw [hΛ]; exact charFun_eq_real_sub ρ hρ u
  have hone : ∫ x : E, (1 : ℝ) ∂ρ = Λ := by
    rw [integral_const]; simp [hΛ]
  have hφnorm : ‖charFun ρ u‖ ≤ Λ := by
    calc ‖charFun ρ u‖ = ‖∫ x, Complex.exp (↑(inner ℝ x u) * Complex.I) ∂ρ‖ := by
          rw [charFun_apply]
      _ ≤ ∫ x, ‖Complex.exp (↑(inner ℝ x u) * Complex.I)‖ ∂ρ := norm_integral_le_integral_norm _
      _ = ∫ x : E, (1 : ℝ) ∂ρ := by
            congr 1
            ext x
            rw [Complex.norm_exp]
            simp
      _ = Λ := hone
  have hcne : ((c : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt hcpos
  have hterm : ∀ k : ℕ, charFun (ENNReal.ofReal (c ^ (k + 1)) • convPow ρ k) u
      = ((c : ℝ) : ℂ) ^ (k + 1) * (charFun ρ u) ^ k := by
    intro k
    rw [charFun_apply, integral_smul_measure, ENNReal.toReal_ofReal (by positivity),
      ← charFun_apply, charFun_convPow, Complex.real_smul, Complex.ofReal_pow]
  have hlt : ‖((c : ℝ) : ℂ) * charFun ρ u‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcpos]
    nlinarith [hφnorm, hcΛ, hcpos]
  have hdenR : 1 - c * (Λ - levyPsi ρ u) = c * (1 + levyPsi ρ u) := by
    nlinarith [hcΛ]
  have hden : 1 - ((c : ℝ) : ℂ) * charFun ρ u
      = ((1 + levyPsi ρ u : ℝ) : ℂ) * ((c : ℝ) : ℂ) := by
    rw [hφ]
    have h1 : (1 : ℂ) - ((c : ℝ) : ℂ) * (((Λ : ℝ) : ℂ) - ((levyPsi ρ u : ℝ) : ℂ))
        = ((1 - c * (Λ - levyPsi ρ u) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h1, hdenR]
    push_cast
    ring
  have hgeo : ∑' k : ℕ, ((c : ℝ) : ℂ) ^ (k + 1) * (charFun ρ u) ^ k
      = ((c : ℝ) : ℂ) * (1 - ((c : ℝ) : ℂ) * charFun ρ u)⁻¹ := by
    have h1 : ∀ k : ℕ, ((c : ℝ) : ℂ) ^ (k + 1) * (charFun ρ u) ^ k
        = ((c : ℝ) : ℂ) * (((c : ℝ) : ℂ) * charFun ρ u) ^ k := by
      intro k
      rw [mul_pow, pow_succ]
      ring
    simp_rw [h1]
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hlt]
  simp_rw [hterm]
  rw [hgeo, hden, mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ hcne, one_mul]

/-! ## The Lévy exponent as a lower integral, and truncations

For a general (not necessarily finite) Lévy measure `Π` the Bochner integral defining `levyPsi`
is replaced by a lower integral, which behaves well under truncation. -/

/-- The lower-integral form of the Lévy exponent. -/
noncomputable def levyExp (Pi : Measure E) (u : E) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (1 - Real.cos (inner ℝ x u)) ∂Pi

theorem measurable_levyIntegrand (u : E) :
    Measurable fun x : E => ENNReal.ofReal (1 - Real.cos (inner ℝ x u)) := by
  fun_prop

theorem levyExp_le (Pi : Measure E) (u : E) :
    levyExp Pi u ≤ ENNReal.ofReal (2 * max (‖u‖ ^ 2) 1)
      * ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂Pi := by
  have h1 : levyExp Pi u ≤ ∫⁻ x, ENNReal.ofReal (2 * max (‖u‖ ^ 2) 1)
      * ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂Pi := by
    refine lintegral_mono fun x => ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal (one_sub_cos_inner_le u x)
  rwa [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h1

theorem levyExp_ne_top (Pi : Measure E)
    (hPi : ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂Pi ≠ ⊤) (u : E) :
    levyExp Pi u ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (levyExp_le Pi u)
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hPi

/-- The real (Bochner) integral form and the lower-integral form of the Lévy exponent agree. -/
theorem levyPsi_eq_levyExp_toReal (Pi : Measure E)
    (hPi : ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂Pi ≠ ⊤) (u : E) :
    levyPsi Pi u = (levyExp Pi u).toReal := by
  have hInt := integrable_one_sub_cos_inner Pi hPi u
  have h1 : ENNReal.ofReal (levyPsi Pi u) = levyExp Pi u :=
    ofReal_integral_eq_lintegral_ofReal hInt
      (Eventually.of_forall fun x => one_sub_cos_nonneg _)
  rw [← h1, ENNReal.toReal_ofReal (levyPsi_nonneg Pi u)]

/-- The truncation radii `ε_n = 1/(n+1) ↓ 0`. -/
noncomputable def truncRadius (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

/-- The truncation sets `{‖x‖ > ε_n} ↑ E \ {0}`. -/
noncomputable def truncSet (n : ℕ) : Set E := {x : E | truncRadius n < ‖x‖}

theorem measurableSet_truncSet (n : ℕ) : MeasurableSet (truncSet (E := E) n) :=
  measurableSet_lt measurable_const (by fun_prop : Measurable fun x : E => ‖x‖)

theorem monotone_truncSet : Monotone (truncSet (E := E)) := by
  intro m n hmn x hx
  simp only [truncSet, Set.mem_ofPred_eq] at hx ⊢
  have h1 : truncRadius n ≤ truncRadius m := by
    rw [truncRadius, truncRadius]
    refine one_div_le_one_div_of_le (by positivity) ?_
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    linarith
  exact lt_of_le_of_lt h1 hx

theorem iUnion_truncSet : (⋃ n, truncSet (E := E) n) = {x : E | ‖x‖ ≠ 0} := by
  ext x
  simp only [Set.mem_iUnion, truncSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨n, hn⟩
    have h1 : 0 < truncRadius n := by rw [truncRadius]; positivity
    exact ne_of_gt (lt_trans h1 hn)
  · intro hx
    have hpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx)
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (K := ℝ) hpos
    exact ⟨n, by simpa [truncRadius] using hn⟩

/-- A truncation of a Lévy measure is a finite measure. -/
theorem truncSet_ne_top (Pi : Measure E)
    (hPi : ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂Pi ≠ ⊤) (n : ℕ) :
    Pi (truncSet n) ≠ ⊤ := by
  set e : ℝ := truncRadius n with he
  have hepos : 0 < e := by rw [he, truncRadius]; positivity
  have hbound : ∀ x : E, x ∈ truncSet n →
      ENNReal.ofReal (e ^ 2) ≤ ENNReal.ofReal (min (‖x‖ ^ 2) 1) := by
    intro x hx
    have hxe : e < ‖x‖ := by
      have hx' := hx
      simp only [truncSet, Set.mem_ofPred_eq] at hx'
      rwa [he]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : (0:ℝ) ≤ ‖x‖ := norm_nonneg x
    have h2 : e ^ 2 ≤ ‖x‖ ^ 2 := by nlinarith
    have h3 : e ^ 2 ≤ 1 := by
      have h4 : e ≤ 1 := by
        rw [he, truncRadius, div_le_one (by positivity)]
        have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
        linarith
      nlinarith
    exact le_min h2 h3
  have h1 : ENNReal.ofReal (e ^ 2) * Pi (truncSet n)
      ≤ ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂Pi := by
    have h2 : ∫⁻ x, (truncSet n).indicator (fun _ => ENNReal.ofReal (e ^ 2)) x ∂Pi
        = ENNReal.ofReal (e ^ 2) * Pi (truncSet n) := by
      rw [lintegral_indicator_const (measurableSet_truncSet n)]
    rw [← h2]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ truncSet n
    · rw [Set.indicator_of_mem hx]; exact hbound x hx
    · rw [Set.indicator_of_notMem hx]; exact bot_le
  have h2 : ENNReal.ofReal (e ^ 2) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  by_contra htop
  rw [htop, ENNReal.mul_top h2] at h1
  exact absurd h1 (not_le.mpr (lt_top_iff_ne_top.mpr hPi))

/-! ## Symmetry of truncations and monotone convergence of the exponent -/

theorem map_neg_restrict_of_invariant (Pi : Measure E)
    (hsymm : Measure.map (fun x : E => -x) Pi = Pi) {s : Set E}
    (hsm : MeasurableSet s) (hs : ∀ x : E, x ∈ s ↔ -x ∈ s) :
    Measure.map (fun x : E => -x) (Pi.restrict s) = Pi.restrict s := by
  have hpre : (fun x : E => -x) ⁻¹' s = s := by
    ext x
    simp only [Set.mem_preimage]
    exact (hs x).symm
  ext t ht
  rw [Measure.map_apply measurable_neg ht, Measure.restrict_apply ht,
    Measure.restrict_apply (measurable_neg ht)]
  have h3 : (fun x : E => -x) ⁻¹' t ∩ s = (fun x : E => -x) ⁻¹' (t ∩ s) := by
    rw [Set.preimage_inter, hpre]
  rw [h3, ← Measure.map_apply measurable_neg (ht.inter hsm), hsymm]

theorem truncSet_neg (n : ℕ) (x : E) : x ∈ truncSet n ↔ -x ∈ truncSet n := by
  simp only [truncSet, Set.mem_ofPred_eq, norm_neg]

/-- Monotone convergence of the truncated Lévy exponents. -/
theorem tendsto_levyExp_trunc (Pi : Measure E) (u : E) :
    Tendsto (fun n => levyExp (Pi.restrict (truncSet n)) u) atTop (𝓝 (levyExp Pi u)) := by
  set g : E → ℝ≥0∞ := fun x => ENNReal.ofReal (1 - Real.cos (inner ℝ x u)) with hg
  have hgm : Measurable g := measurable_levyIntegrand u
  have hmono : Monotone fun n x => (truncSet n).indicator g x := by
    intro m n hmn x
    show (truncSet m).indicator g x ≤ (truncSet n).indicator g x
    by_cases hx : x ∈ truncSet m
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (monotone_truncSet hmn hx)]
    · rw [Set.indicator_of_notMem hx]; exact bot_le
  have hmono' : Monotone fun n : ℕ => ∫⁻ x, (truncSet n).indicator g x ∂Pi :=
    fun m n hmn => lintegral_mono (hmono hmn)
  have hmct := lintegral_iSup (μ := Pi) (f := fun n x => (truncSet n).indicator g x)
    (fun n => hgm.indicator (measurableSet_truncSet n)) hmono
  have hzero : g 0 = 0 := by simp [hg]
  have hsup : (fun x : E => ⨆ n, (truncSet n).indicator g x) = g := by
    funext x
    by_cases hx : x = 0
    · subst hx
      have h0 : ∀ n, (truncSet n).indicator g (0 : E) = 0 := by
        intro n
        rw [Set.indicator_of_notMem (by
          simp only [truncSet, Set.mem_ofPred_eq, truncRadius, norm_zero]
          intro h
          have hpos : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
          linarith)]
      show (⨆ n, (truncSet n).indicator g (0 : E)) = g 0
      rw [hzero]
      simp only [h0]
      exact iSup_const
    · have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (K := ℝ) hpos
      have hmem : x ∈ truncSet n := by simpa [truncSet, truncRadius] using hn
      refine le_antisymm (iSup_le fun m => ?_) ?_
      · by_cases hm : x ∈ truncSet m
        · rw [Set.indicator_of_mem hm]
        · rw [Set.indicator_of_notMem hm]; exact bot_le
      · calc g x = (truncSet n).indicator g x := (Set.indicator_of_mem hmem g).symm
          _ ≤ ⨆ m, (truncSet m).indicator g x := le_iSup (fun m => (truncSet m).indicator g x) n
  have hmct' : levyExp Pi u = ⨆ n, ∫⁻ x, (truncSet n).indicator g x ∂Pi := by
    have h := hmct
    rw [hsup] at h
    simpa only [hg, levyExp] using h
  have h2 : Tendsto (fun n : ℕ => ∫⁻ x, (truncSet n).indicator g x ∂Pi) atTop (𝓝 (levyExp Pi u)) := by
    have h3 := tendsto_atTop_iSup hmono'
    rwa [← hmct'] at h3
  have hind : ∀ n, ∫⁻ x, (truncSet n).indicator g x ∂Pi
      = levyExp (Pi.restrict (truncSet n)) u := by
    intro n
    rw [lintegral_indicator (measurableSet_truncSet n)]
    simp only [hg, levyExp]
  simpa only [hind] using h2

/-- Convergence of the truncated Lévy exponents, in Bochner-integral form. -/
theorem tendsto_levyPsi_trunc (Pi : Measure E)
    (hPi : ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂Pi ≠ ⊤) (u : E) :
    Tendsto (fun n => levyPsi (Pi.restrict (truncSet n)) u) atTop (𝓝 (levyPsi Pi u)) := by
  have h1 : ∀ n, levyPsi (Pi.restrict (truncSet n)) u
      = (levyExp (Pi.restrict (truncSet n)) u).toReal := by
    intro n
    refine levyPsi_eq_levyExp_toReal (Pi.restrict (truncSet n)) ?_ u
    refine ne_top_of_le_ne_top hPi (lintegral_mono' Measure.restrict_le_self (fun x => le_refl _))
  simp_rw [h1]
  have h2 := tendsto_levyExp_trunc Pi u
  have h3 : levyExp Pi u ≠ ⊤ := levyExp_ne_top Pi hPi u
  have h4 := (ENNReal.tendsto_toReal h3).comp h2
  rwa [levyPsi_eq_levyExp_toReal Pi hPi u]

/-! ## Existence of the exponential-time stopped law

The main theorem of the file: for any symmetric Lévy measure `Π` with `∫ (‖x‖² ∧ 1) dΠ < ∞`,
there is a probability measure `ν` whose characteristic function is `u ↦ (1 + ψ(u))⁻¹`,
`ψ(u) = ∫ (1 - cos ⟨u,x⟩) dΠ`.  This is exactly the law of the symmetric Lévy jump process with
Lévy measure `Π` at an independent `Exp(1)` time, obtained here as the weak limit of the explicit
compound geometric laws of the truncations `Π(· ∩ {‖x‖ > 1/(n+1)})`. -/

theorem exists_exp_stop_charFun (Pi : Measure E)
    (hPi : ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂Pi ≠ ⊤)
    (hsymm : Measure.map (fun x : E => -x) Pi = Pi) :
    ∃ ν : ProbabilityMeasure E, ∀ u : E,
      charFun (ν : Measure E) u = ((1 + levyPsi Pi u : ℝ) : ℂ)⁻¹ := by
  set rho : ℕ → Measure E := fun n => Pi.restrict (truncSet n) with hrho
  have hfin : ∀ n, IsFiniteMeasure (rho n) := fun n => ⟨by
    show (Pi.restrict (truncSet n)) univ < ⊤
    rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    exact lt_top_iff_ne_top.mpr (truncSet_ne_top Pi hPi n)⟩
  have hsymm_n : ∀ n, Measure.map (fun x : E => -x) (rho n) = rho n := fun n =>
    map_neg_restrict_of_invariant Pi hsymm (measurableSet_truncSet n) (truncSet_neg n)
  set nu : ℕ → ProbabilityMeasure E :=
    fun n => ⟨expGeom (rho n), instIsProbabilityMeasureExpGeom (rho n)⟩ with hnu
  have hprob : ∀ n, IsProbabilityMeasure ((nu n : Measure E)) := fun n => (nu n).2
  set f : E → ℂ := fun u => ((1 + levyPsi Pi u : ℝ) : ℂ)⁻¹ with hf
  have hconv : ∀ u : E, Tendsto (fun n => charFun ((nu n : Measure E)) u) atTop (𝓝 (f u)) := by
    intro u
    have h1 : ∀ n, charFun ((nu n : Measure E)) u = ((1 + levyPsi (rho n) u : ℝ) : ℂ)⁻¹ := by
      intro n
      exact charFun_expGeom (rho n) (hsymm_n n) u
    simp_rw [h1]
    have h2 : Tendsto (fun n => (1 + levyPsi (rho n) u : ℝ)) atTop (𝓝 (1 + levyPsi Pi u)) :=
      tendsto_const_nhds.add (tendsto_levyPsi_trunc Pi hPi u)
    have h3 : (1 + levyPsi Pi u : ℝ) ≠ 0 := by
      have := levyPsi_nonneg Pi u
      positivity
    have h4 : Tendsto (fun n => (1 + levyPsi (rho n) u : ℝ)⁻¹) atTop
        (𝓝 ((1 + levyPsi Pi u : ℝ)⁻¹)) := h2.inv₀ h3
    have h5 : Tendsto (fun n => (((1 + levyPsi (rho n) u : ℝ)⁻¹ : ℝ) : ℂ)) atTop
        (𝓝 (((1 + levyPsi Pi u : ℝ)⁻¹ : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto ((1 + levyPsi Pi u : ℝ)⁻¹)).comp h4
    simpa only [hf, Complex.ofReal_inv] using h5
  have hcont : ContinuousAt f 0 := by
    have hψ : Tendsto (fun u : E => levyPsi Pi u) (𝓝 0) (𝓝 0) := tendsto_levyPsi_zero Pi hPi
    have h1 : Tendsto (fun u : E => (1 + levyPsi Pi u : ℝ)) (𝓝 0) (𝓝 1) := by
      have := (tendsto_const_nhds (x := (1:ℝ)) (f := 𝓝 (0:E))).add hψ
      simpa using this
    have h2 : Tendsto (fun u : E => ((1 + levyPsi Pi u : ℝ) : ℂ)) (𝓝 0) (𝓝 (((1:ℝ)) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto (1:ℝ)).comp h1
    have h3 : Tendsto (fun u : E => (((1 + levyPsi Pi u : ℝ) : ℂ))⁻¹) (𝓝 0)
        (𝓝 ((((1:ℝ)) : ℂ))⁻¹) := h2.inv₀ (by norm_num)
    have h4 : f 0 = ((((1:ℝ)) : ℂ))⁻¹ := by simp [hf, levyPsi_zero]
    rw [ContinuousAt, h4]
    simpa only [hf] using h3
  have htight : IsTightMeasureSet (Set.range fun n => ((nu n : Measure E))) :=
    isTightMeasureSet_of_tendsto_charFun hcont hconv
  have hset : {x : Measure E | ∃ μ ∈ Set.range nu, (μ : Measure E) = x}
      = Set.range fun n => ((nu n : Measure E)) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_range, exists_exists_eq_and]
  have hcomp : IsCompact (closure (Set.range nu)) := by
    apply isCompact_closure_of_isTightMeasureSet
    rw [hset]
    exact htight
  obtain ⟨mu, -, phi, hphi, hlim⟩ :=
    hcomp.tendsto_subseq (fun n => subset_closure (Set.mem_range_self n))
  refine ⟨mu, fun u => ?_⟩
  have hchar : ∀ u : E, charFun (mu : Measure E) u = f u := by
    intro u
    have h2 : Tendsto (fun n => charFun ((nu (phi n) : Measure E)) u) atTop
        (𝓝 (charFun (mu : Measure E) u)) :=
      (ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hlim) u
    have h3 : Tendsto (fun n => charFun ((nu (phi n) : Measure E)) u) atTop (𝓝 (f u)) :=
      (hconv u).comp hphi.tendsto_atTop
    exact tendsto_nhds_unique h2 h3
  exact hchar u

/-! ## Symmetry of the constructed law -/

/-- The characteristic function of the image of `μ` under `x ↦ -x`. -/
theorem charFun_map_neg (μ : Measure E) (u : E) :
    charFun (Measure.map (fun x : E => -x) μ) u = charFun μ (-u) := by
  rw [charFun_apply, charFun_apply, integral_map measurable_neg.aemeasurable]
  · refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show Complex.exp (↑(inner ℝ (-x) u) * Complex.I)
      = Complex.exp (↑(inner ℝ x (-u)) * Complex.I)
    rw [inner_neg_left, inner_neg_right]
  · exact (by fun_prop : AEStronglyMeasurable
      (fun y : E => Complex.exp (↑(inner ℝ y u) * Complex.I))
      (Measure.map (fun x : E => -x) μ))

/-- A probability measure whose characteristic function is real is invariant under `x ↦ -x`. -/
theorem map_neg_eq_self_of_charFun_real (ν : ProbabilityMeasure E)
    (hν : ∀ u, charFun (ν : Measure E) u = ((charFun (ν : Measure E) u).re : ℂ)) :
    Measure.map (fun x : E => -x) (ν : Measure E) = (ν : Measure E) := by
  refine Measure.ext_of_charFun ?_
  funext u
  rw [charFun_map_neg, charFun_neg, hν u, Complex.conj_ofReal]

/-- The exponential-time stopped law of a symmetric Lévy measure is symmetric. -/
theorem exists_exp_stop_symm (Pi : Measure E)
    (hPi : ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂Pi ≠ ⊤)
    (hsymm : Measure.map (fun x : E => -x) Pi = Pi) :
    ∃ ν : ProbabilityMeasure E,
      (∀ u : E, charFun (ν : Measure E) u = ((1 + levyPsi Pi u : ℝ) : ℂ)⁻¹)
        ∧ Measure.map (fun x : E => -x) (ν : Measure E) = (ν : Measure E) := by
  obtain ⟨ν, hν⟩ := exists_exp_stop_charFun Pi hPi hsymm
  refine ⟨ν, hν, map_neg_eq_self_of_charFun_real ν (fun u => ?_)⟩
  rw [hν u]
  have hre : ((Complex.ofReal (1 + levyPsi Pi u))⁻¹).re = (1 + levyPsi Pi u)⁻¹ := by
    rw [← Complex.ofReal_inv, Complex.ofReal_re]
  rw [hre, ← Complex.ofReal_inv]

/-! ## The cut-off measures `Π₁` of (I.5.16): Definition I.5.16 for `α < 2` -/

/-- **Definition I.5.16 for `0 < α < 2`.**  The limiting displacement law `ν_disp` of the
`α`-stable regime exists as an honest probability measure on `E`, it is symmetric, and its
characteristic function is
`u ↦ (1 + ∫ (1 - cos ⟨u,x⟩) dΠ₁)⁻¹`,
i.e. the law of the symmetric Lévy jump process with Lévy measure `Π₁` of (I.5.16) at an
independent `Exp(1)` time. -/
theorem exists_nuDisp (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ} (hα : 0 < α) (hα2 : α < 2) :
    ∃ ν : ProbabilityMeasure E,
      (∀ u : E, charFun (ν : Measure E) u
          = ((1 + ∫ x, (1 - Real.cos (inner ℝ x u)) ∂(PiOne α μ) : ℝ) : ℂ)⁻¹)
        ∧ Measure.map (fun x : E => -x) (ν : Measure E) = (ν : Measure E) :=
  exists_exp_stop_symm (PiOne α μ) (PiOne_levy_measure μ hα hα2) (PiOne_symm μ α)

/-! ## The Brownian / Laplace regime `α ≥ 2`

Definition I.5.16 for `α ≥ 2` takes `ν_disp` to be the multivariate Laplace distribution, i.e. the
law of a Brownian motion with covariance `Σ` stopped at an independent `Exp(1)` time.  Since
`B_t` has the law of `t^{1/2} Z` with `Z ~ N(0,Σ)`, this law is the explicit pushforward of
`Exp(1) ⊗ N(0,Σ)` under `(t,z) ↦ t^{1/2} z`, and its characteristic function is computed here
directly: `u ↦ (1 + ⟨Σu,u⟩/2)⁻¹`. -/

/-- The unit-rate exponential law, presented as an explicit density on `(0,∞)`. -/
noncomputable def expOne : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity (fun t => ENNReal.ofReal (Real.exp (-t)))

theorem measurable_expOne_density :
    Measurable fun t : ℝ => ENNReal.ofReal (Real.exp (-t)) := by fun_prop

/-- Integration against the unit-rate exponential law, in density form. -/
theorem integral_expOne (f : ℝ → ℂ) :
    ∫ t, f t ∂expOne = ∫ t in Ioi (0 : ℝ), (Real.exp (-t) : ℂ) * f t := by
  rw [expOne, integral_withDensity_eq_integral_toReal_smul measurable_expOne_density
    (Eventually.of_forall fun t => ENNReal.ofReal_lt_top)]
  refine setIntegral_congr_fun measurableSet_Ioi ?_
  intro t ht
  show (ENNReal.ofReal (Real.exp (-t))).toReal • f t = (Real.exp (-t) : ℂ) * f t
  rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, Complex.real_smul]

theorem expOne_univ : expOne univ = 1 := by
  rw [expOne, withDensity_apply _ MeasurableSet.univ]
  simp only [setLIntegral_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_neg_Ioi 0)
    (Eventually.of_forall fun t => (Real.exp_pos _).le)]
  have h1 : ∫ t in Ioi (0 : ℝ), Real.exp (-t) = 1 := by
    have h2 : ∫ t in Ioi (0 : ℝ), Real.exp ((-1 : ℝ) * t) = 1 := by
      rw [integral_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) (0 : ℝ)]
      norm_num
    simpa using h2
  rw [h1, ENNReal.ofReal_one]

instance instIsProbabilityMeasureExpOne : IsProbabilityMeasure expOne := ⟨expOne_univ⟩

/-- **The Gaussian/Laplace regime of Definition I.5.16.**  If `γ` is the law of a Gaussian with
covariance form `u ↦ ⟨T u, u⟩` (i.e. `charFun γ u = exp(-⟨Tu,u⟩/2)`, the covariance `T` being
positive semidefinite), then the law of `B_T` for `B` Brownian of covariance `T` and `T ~ Exp(1)`
exists as an honest probability measure, and its characteristic function is
`u ↦ (1 + ⟨Tu,u⟩/2)⁻¹`. -/
theorem exists_laplaceMixture (γ : Measure E) [IsProbabilityMeasure γ]
    (T : E →L[ℝ] E) (hT : ∀ u : E, 0 ≤ (inner ℝ (T u) u : ℝ))
    (hγ : ∀ u : E, charFun γ u = Complex.exp (-((inner ℝ (T u) u : ℝ) : ℂ) / 2)) :
    ∃ ν : ProbabilityMeasure E, ∀ u : E,
      charFun (ν : Measure E) u = (1 + (((inner ℝ (T u) u : ℝ)) : ℂ) / 2)⁻¹ := by
  set a : E → ℝ := fun u => (inner ℝ (T u) u : ℝ) / 2 with ha
  have hprod : IsProbabilityMeasure (expOne.prod γ) := inferInstance
  set ν₀ : Measure E := (expOne.prod γ).map (fun p : ℝ × E => Real.sqrt p.1 • p.2) with hν₀
  have hmap : Measurable fun p : ℝ × E => Real.sqrt p.1 • p.2 := by fun_prop
  have hν₀prob : IsProbabilityMeasure ν₀ := by
    constructor
    rw [hν₀, Measure.map_apply hmap MeasurableSet.univ, Set.preimage_univ,
      ← Set.univ_prod_univ, Measure.prod_prod, expOne_univ, measure_univ, mul_one]
  refine ⟨⟨ν₀, hν₀prob⟩, fun u => ?_⟩
  show charFun ν₀ u = (1 + ((inner ℝ (T u) u : ℝ) : ℂ) / 2)⁻¹
  have hinner : ∀ t : ℝ, 0 < t →
      ∫ z, Complex.exp (↑(inner ℝ (Real.sqrt t • z) u) * Complex.I) ∂γ
        = Complex.exp (-((t * a u : ℝ)) : ℂ) := by
    intro t ht
    have h1 : ∀ z : E, Complex.exp (↑(inner ℝ (Real.sqrt t • z) u) * Complex.I)
        = Complex.exp (↑(inner ℝ z (Real.sqrt t • u)) * Complex.I) := by
      intro z
      rw [inner_smul_left, inner_smul_right]
      simp
    simp_rw [h1]
    have hreal : ((inner ℝ (T (Real.sqrt t • u)) (Real.sqrt t • u) : ℝ)) / 2 = t * a u := by
      rw [ha, map_smul, inner_smul_left, inner_smul_right]
      simp
      have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
      ring_nf
      rw [hsq]
      ring
    have hrealC : -((inner ℝ (T (Real.sqrt t • u)) (Real.sqrt t • u) : ℝ) : ℂ) / 2
        = -((t * a u : ℝ) : ℂ) := by
      rw [show ((inner ℝ (T (Real.sqrt t • u)) (Real.sqrt t • u) : ℝ) : ℂ)
          = ((inner ℝ (T (Real.sqrt t • u)) (Real.sqrt t • u) : ℝ) : ℂ) from rfl]
      rw [← hreal]
      push_cast
      ring
    rw [← charFun_apply, hγ, hrealC]
  have hstep1 : charFun ν₀ u
      = ∫ t, (∫ z, Complex.exp (↑(inner ℝ (Real.sqrt t • z) u) * Complex.I) ∂γ) ∂expOne := by
    rw [charFun_apply, hν₀, integral_map hmap.aemeasurable]
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
      = ∫ t in Ioi (0 : ℝ), (Real.exp (-t) : ℂ) * Complex.exp (-((t * a u : ℝ)) : ℂ) := by
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro t ht
    show (Real.exp (-t) : ℂ)
          * (∫ z, Complex.exp (↑(inner ℝ (Real.sqrt t • z) u) * Complex.I) ∂γ)
        = (Real.exp (-t) : ℂ) * Complex.exp (-((t * a u : ℝ)) : ℂ)
    rw [hinner t ht]
  rw [hcongr]
  have hexp : ∀ t ∈ Ioi (0 : ℝ), (Real.exp (-t) : ℂ) * Complex.exp (-((t * a u : ℝ)) : ℂ)
      = ((Real.exp (-(((1 + a u) * t : ℝ))) : ℝ) : ℂ) := by
    intro t ht
    have h2 : Complex.exp (-((t * a u : ℝ)) : ℂ)
        = ((Real.exp (-((t * a u) : ℝ)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    rw [h2, ← Complex.ofReal_mul, ← Real.exp_add,
      show (-t + -((t * a u))) = -((1 + a u) * t) from by ring]
  rw [setIntegral_congr_fun measurableSet_Ioi hexp]
  have hreal : ∫ t in Ioi (0 : ℝ), Real.exp (-(((1 + a u) * t : ℝ))) = (1 + a u)⁻¹ := by
    have ha0 : (0:ℝ) ≤ a u := by rw [ha]; linarith [hT u]
    rw [show (fun t : ℝ => Real.exp (-(((1 + a u) * t : ℝ))))
        = fun t : ℝ => Real.exp ((-(1 + a u)) * t) from by
      funext t
      rw [neg_mul]]
    rw [integral_exp_mul_Ioi (a := -(1 + a u)) (by linarith) 0, mul_zero, Real.exp_zero]
    field_simp
  calc ∫ t in Ioi (0 : ℝ), ((Real.exp (-(((1 + a u) * t : ℝ))) : ℝ) : ℂ)
      = ((∫ t in Ioi (0 : ℝ), Real.exp (-(((1 + a u) * t : ℝ))) : ℝ) : ℂ) := integral_ofReal
    _ = (((1 + a u)⁻¹ : ℝ) : ℂ) := by rw [hreal]
    _ = (((1 + a u : ℝ)) : ℂ)⁻¹ := Complex.ofReal_inv _
    _ = (1 + ((inner ℝ (T u) u : ℝ) : ℂ) / 2)⁻¹ := by
        rw [ha]
        push_cast
        ring_nf

/-! ## Canonicity: the exponential-time law is determined by its characteristic function -/

/-- Any two probability measures whose characteristic functions are `(1+ψ)⁻¹` coincide: the
exponential-time stopped law of a symmetric Lévy measure is canonical. -/
theorem eq_of_charFun_levy (Pi : Measure E) {ν ν' : ProbabilityMeasure E}
    (hν : ∀ u : E, charFun (ν : Measure E) u = ((1 + levyPsi Pi u : ℝ) : ℂ)⁻¹)
    (hν' : ∀ u : E, charFun (ν' : Measure E) u = ((1 + levyPsi Pi u : ℝ) : ℂ)⁻¹) :
    ν = ν' := by
  have h : (ν : Measure E) = (ν' : Measure E) := by
    refine Measure.ext_of_charFun ?_
    funext u
    rw [hν u, hν' u]
  exact ProbabilityMeasure.toMeasure_injective h

/-- Uniqueness in the Gaussian/Laplace regime. -/
theorem eq_of_charFun_laplace (T : E →L[ℝ] E) {ν ν' : ProbabilityMeasure E}
    (hν : ∀ u : E, charFun (ν : Measure E) u = (1 + (((inner ℝ (T u) u : ℝ)) : ℂ) / 2)⁻¹)
    (hν' : ∀ u : E, charFun (ν' : Measure E) u = (1 + (((inner ℝ (T u) u : ℝ)) : ℂ) / 2)⁻¹) :
    ν = ν' := by
  have h : (ν : Measure E) = (ν' : Measure E) := by
    refine Measure.ext_of_charFun ?_
    funext u
    rw [hν u, hν' u]
  exact ProbabilityMeasure.toMeasure_injective h
