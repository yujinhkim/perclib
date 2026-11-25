/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Formalization derived from T. Hutchcroft, "Critical long-range percolation I: High effective
dimension", arXiv:2508.18807v1, Section I.5.2: the symmetry (odd-part) cancellation in (I.5.17).

The paper computes, for `ℓ` a linear functional on `ℝ^d` (`⟨u,·⟩` in the paper) and `0 < α < 2`,
```
  ∫ (e^{ℓ x} - 1 - ℓ x) dΠ₁ = ∫ (cosh (ℓ x) - 1) dΠ₁,
```
"where the second equality follows by symmetry of Π₁". The content of that step is:
* `Π₁` is supported in the unit ball and has a finite second moment, so `x ↦ sinh (ℓ x) - ℓ x`
  is `Π₁`-integrable (second-order Taylor estimate for `sinh`);
* it is odd, and `Π₁` is invariant under `x ↦ -x`, so its integral vanishes.

It also proves the companion facts that for `α < 1` the compensating linear terms `x ↦ ℓ x` and
`x ↦ x` are `Π₁`-integrable with vanishing integral (so the drift compensator of the limiting
displacement law at truncation function `x ↦ x` is `0`), and it combines the result with the
Taylor/Fubini series of `LevyCosh` (the paper's display following (I.5.17)).

The second half of the file treats the untruncated measure `Π_∞` (`dΠ_∞/dx = α ‖x‖^{-d-α}`), for
which the paper only uses the characteristic function:
* `Π_∞` is radially even (`PiInf_symm`);
* **`Π_∞` is a Lévy measure** for `0 < α < 2`: `∫ (‖x‖² ∧ 1) dΠ_∞ < ∞` (`PiInf_levy_measure`);
* the compensated odd part `x ↦ sin (ℓ x) - ℓ x 1(‖x‖ ≤ 1)` is `Π_∞`-integrable with vanishing
  integral (`integral_sin_sub_trunc_PiInf`), and the even part `∫ (1 - cos (ℓ x)) dΠ_∞` is finite
  (`lintegral_one_sub_cos_PiInf_ne_top`): the characteristic exponent of the symmetric `α`-stable
  law is real with zero drift;
* all three Lévy measures are absolutely continuous with respect to Lebesgue measure, the checkable
  input of the Sato criterion used in Lemma I.5.17.

Everything here is unconditional (no `sorry`, no added hypotheses); the only remaining inputs of the
paper's Section I.5.2 that are *not* formalized are the existence of the Lévy processes, the
displacement law `ν_disp` and its density (Definition I.5.16/ Lemma I.5.17).
-/
module

public import PercLib.CriticalLRP.LevyAnalysis.LevyCosh

set_option autoImplicit true

@[expose] public section

open MeasureTheory Metric Set Filter
open Module
open scoped ENNReal NNReal Topology Pointwise Interval BigOperators

namespace PercLib.CriticalLRP.LevyAnalysis

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-! ## Second-order estimate for `sinh` -/

/-- The Taylor remainder bound for `exp`: `|exp x - 1 - x| ≤ x ^ 2 * exp |x|`. -/
theorem abs_exp_sub_one_sub_id_le_exp (x : ℝ) :
    |Real.exp x - 1 - x| ≤ x ^ 2 * Real.exp |x| := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (x : ℂ) 2
  have hsum : (∑ m ∈ Finset.range 2, (x : ℂ) ^ m / ((m.factorial : ℕ) : ℂ)) = 1 + (x : ℂ) := by
    simp [Finset.sum_range_succ]
  rw [hsum] at h
  have hcast : ((Real.exp x - 1 - x : ℝ) : ℂ)
      = Complex.exp (x : ℂ) - (1 + (x : ℂ)) := by
    push_cast
    ring
  have hnorm : ‖Complex.exp (x : ℂ) - (1 + (x : ℂ))‖ = |Real.exp x - 1 - x| := by
    rw [← hcast, Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm] at h
  simpa [Complex.norm_real, Real.norm_eq_abs, sq_abs] using h

/-- `|sinh x - x| ≤ x ^ 2 * exp |x|`: `sinh - id` vanishes to second order. -/
theorem abs_sinh_sub_id_le_exp (x : ℝ) :
    |Real.sinh x - x| ≤ x ^ 2 * Real.exp |x| := by
  have h1 := abs_exp_sub_one_sub_id_le_exp x
  have h2 := abs_exp_sub_one_sub_id_le_exp (-x)
  rw [abs_neg] at h2
  have hEq : Real.sinh x - x
      = ((Real.exp x - 1 - x) - (Real.exp (-x) - 1 - (-x))) / 2 := by
    rw [Real.sinh_eq]
    field_simp
    ring
  rw [hEq, abs_div, abs_two]
  have htri : |(Real.exp x - 1 - x) - (Real.exp (-x) - 1 - (-x))|
      ≤ |Real.exp x - 1 - x| + |Real.exp (-x) - 1 - (-x)| := abs_sub _ _
  linarith

/-- The uniform second-order estimate on `|x| ≤ M`. -/
theorem abs_sinh_sub_id_le_exp_of_abs_le {M x : ℝ} (hx : |x| ≤ M) :
    |Real.sinh x - x| ≤ x ^ 2 * Real.exp M := by
  have h := abs_sinh_sub_id_le_exp x
  have hexp : Real.exp |x| ≤ Real.exp M := Real.exp_le_exp.mpr hx
  have hnn : (0 : ℝ) ≤ x ^ 2 := sq_nonneg x
  calc |Real.sinh x - x| ≤ x ^ 2 * Real.exp |x| := h
    _ ≤ x ^ 2 * Real.exp M := mul_le_mul_of_nonneg_left hexp hnn

/-! ## Vanishing of the integral of an odd function against a symmetric measure -/

/-- An odd integrable function has vanishing integral against a measure invariant under `x ↦ -x`.
This is the abstract symmetry-cancellation step behind the paper's "by symmetry of `Π₁`". -/
theorem integral_eq_zero_of_odd_of_map_neg_eq_self {G : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] {μ : Measure E} (hμ : Measure.map (fun x : E => -x) μ = μ)
    {f : E → G} (hf : Integrable f μ) (hodd : ∀ x, f (-x) = -f x) :
    ∫ x, f x ∂μ = 0 := by
  have hmap : ∫ y, f y ∂(Measure.map (fun x : E => -x) μ) = ∫ x, f (-x) ∂μ := by
    refine integral_map measurable_neg.aemeasurable ?_
    rw [hμ]
    exact hf.aestronglyMeasurable
  rw [hμ] at hmap
  have h2 : ∫ x, f (-x) ∂μ = ∫ x, -f x ∂μ :=
    integral_congr_ae (Eventually.of_forall hodd)
  have h3 : ∫ x, -f x ∂μ = -∫ x, f x ∂μ := integral_neg f
  have h4 : ∫ x, f x ∂μ = -(∫ x, f x ∂μ) := by
    calc ∫ x, f x ∂μ = ∫ x, f (-x) ∂μ := hmap
      _ = ∫ x, -f x ∂μ := h2
      _ = -(∫ x, f x ∂μ) := h3
  have h5 : ∫ x, f x ∂μ + ∫ x, f x ∂μ = 0 := by
    nth_rewrite 2 [h4]
    exact add_neg_cancel _
  have h6 : (2 : ℝ) • (∫ x, f x ∂μ) = 0 := by
    rw [two_smul]
    exact h5
  exact (smul_eq_zero.mp h6).resolve_left (by norm_num)

/-! ## `Π₁` is carried by the unit ball -/

/-- **`Π₁` is supported in the closed unit ball**: almost every point has `‖x‖ ≤ 1`.
This is the support statement used for every second-order estimate below. -/
theorem PiOne_ae_norm_le_one (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ} (hα : 0 < α) :
    ∀ᵐ x ∂(PiOne α μ), ‖x‖ ≤ 1 := by
  rw [ae_iff]
  have hset : {x : E | ¬ ‖x‖ ≤ 1} = (closedBall (0 : E) 1)ᶜ := by
    ext x
    simp [mem_closedBall, dist_zero_right]
  have hzero : ∀ x ∈ (closedBall (0 : E) 1)ᶜ, levyDensLam (E := E) α 1 x = 0 := by
    intro x hx
    rw [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] at hx
    exact levyDensOne_eq_zero_of_one_le hα hx.le
  rw [hset, PiOne, PiLam,
    withDensity_apply (levyDensLam (E := E) α 1) measurableSet_closedBall.compl,
    setLIntegral_congr_fun measurableSet_closedBall.compl hzero]
  simp

/-! ## The second moment of `Π₁` as a Bochner integral -/

/-- The second moment of `Π₁` is finite, hence `‖·‖^2` is `Π₁`-integrable. -/
theorem integrable_norm_sq_PiOne (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ} (hα : 0 < α)
    (hα2 : α < 2) :
    Integrable (fun x : E => ‖x‖ ^ 2) (PiOne α μ) := by
  have hfin : ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂(PiOne α μ) ≠ ⊤ := by
    rw [lintegral_norm_sq_PiOne μ hα hα2]
    exact ENNReal.ofReal_ne_top
  exact (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
    (Eventually.of_forall fun x => by positivity)).mp hfin

/-! ## Integrability and cancellation of the odd part `sinh (ℓ x) - ℓ x` -/

/-- **The odd part is `Π₁`-integrable**: `x ↦ sinh (ℓ x) - ℓ x` for every `0 < α < 2`.

This is the quantitative heart of the paper's "by symmetry of `Π₁`": the second-order Taylor
estimate `|sinh s - s| ≤ s² e^{|s|}` combined with the support in the unit ball and the finite
second moment of `Π₁` gives absolute convergence. Note that this convergence is *stronger* than
`Π₁`-integrability of `ℓ x` itself, which fails for `α ≥ 1`. -/
theorem integrable_sinh_sub_linear_PiOne (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ}
    (hα : 0 < α) (hα2 : α < 2) (ℓ : E →L[ℝ] ℝ) :
    Integrable (fun x : E => Real.sinh (ℓ x) - ℓ x) (PiOne α μ) := by
  refine Integrable.mono' ((integrable_norm_sq_PiOne μ hα hα2).const_mul
    (‖ℓ‖ ^ 2 * Real.exp ‖ℓ‖)) (by fun_prop) ?_
  filter_upwards [PiOne_ae_norm_le_one μ hα] with x hx
  have hop : |ℓ x| ≤ ‖ℓ‖ := by
    calc |ℓ x| = ‖ℓ x‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖ℓ‖ * ‖x‖ := ℓ.le_opNorm x
      _ ≤ ‖ℓ‖ * 1 := by gcongr
      _ = ‖ℓ‖ := mul_one ‖ℓ‖
  have hkey := abs_sinh_sub_id_le_exp_of_abs_le (M := ‖ℓ‖) hop
  have hsq : (ℓ x) ^ 2 ≤ (‖ℓ‖ * ‖x‖) ^ 2 := by
    have h0 : (0 : ℝ) ≤ ‖ℓ x‖ := norm_nonneg _
    calc (ℓ x) ^ 2 = ‖ℓ x‖ ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
      _ ≤ (‖ℓ‖ * ‖x‖) ^ 2 := by gcongr; exact ℓ.le_opNorm x
  have hexp : (0 : ℝ) ≤ Real.exp ‖ℓ‖ := (Real.exp_pos _).le
  calc ‖Real.sinh (ℓ x) - ℓ x‖ = |Real.sinh (ℓ x) - ℓ x| := Real.norm_eq_abs _
    _ ≤ (ℓ x) ^ 2 * Real.exp ‖ℓ‖ := hkey
    _ ≤ (‖ℓ‖ * ‖x‖) ^ 2 * Real.exp ‖ℓ‖ := by gcongr
    _ = (‖ℓ‖ ^ 2 * Real.exp ‖ℓ‖) * ‖x‖ ^ 2 := by ring

/-- **The odd part has vanishing `Π₁`-integral**, by symmetry of `Π₁` (I.5.17). -/
theorem integral_sinh_sub_linear_PiOne (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ}
    (hα : 0 < α) (hα2 : α < 2) (ℓ : E →L[ℝ] ℝ) :
    ∫ x, (Real.sinh (ℓ x) - ℓ x) ∂(PiOne α μ) = 0 := by
  refine integral_eq_zero_of_odd_of_map_neg_eq_self (PiOne_symm μ α) ?_ ?_
  · exact integrable_sinh_sub_linear_PiOne μ hα hα2 ℓ
  · intro x
    simp only [ContinuousLinearMap.map_neg, Real.sinh_neg]
    ring

/-! ## The exponent identity (I.5.17): even/odd decomposition -/

/-- `exp s - 1 - s = (cosh s - 1) + (sinh s - s)`. -/
theorem exp_sub_one_sub_id_eq (s : ℝ) :
    Real.exp s - 1 - s = (Real.cosh s - 1) + (Real.sinh s - s) := by
  rw [Real.sinh_eq, Real.cosh_eq]
  field_simp
  ring

theorem cosh_sub_one_nonneg (s : ℝ) : 0 ≤ Real.cosh s - 1 := by
  linarith [Real.one_le_cosh s]

/-- `sinh s - s` has the sign of `s`. -/
theorem sinh_sub_id_sign {s : ℝ} (hs : 0 ≤ s) : 0 ≤ Real.sinh s - s := by
  linarith [Real.self_le_sinh_iff.mpr hs]

theorem exp_sub_one_sub_id_nonneg (s : ℝ) : 0 ≤ Real.exp s - 1 - s := by
  linarith [Real.add_one_le_exp s]

/-! ## Finiteness of the two pieces -/

/-- `x ↦ cosh (ℓ x) - 1` is `Π₁`-integrable. -/
theorem integrable_cosh_sub_one_PiOne (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ}
    (hα : 0 < α) (hα2 : α < 2) (ℓ : E →L[ℝ] ℝ) :
    Integrable (fun x : E => Real.cosh (ℓ x) - 1) (PiOne α μ) := by
  refine (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
    (Eventually.of_forall fun x => cosh_sub_one_nonneg _)).mp ?_
  exact lintegral_cosh_sub_one_PiOne_ne_top μ hα hα2 ℓ

/-- `x ↦ e^{ℓ x} - 1 - ℓ x` is `Π₁`-integrable. -/
theorem integrable_exp_sub_one_sub_linear_PiOne (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ}
    (hα : 0 < α) (hα2 : α < 2) (ℓ : E →L[ℝ] ℝ) :
    Integrable (fun x : E => Real.exp (ℓ x) - 1 - ℓ x) (PiOne α μ) := by
  have hsum : Integrable (fun x : E =>
      (Real.cosh (ℓ x) - 1) + (Real.sinh (ℓ x) - ℓ x)) (PiOne α μ) :=
    (integrable_cosh_sub_one_PiOne μ hα hα2 ℓ).add
      (integrable_sinh_sub_linear_PiOne μ hα hα2 ℓ)
  refine hsum.congr (Eventually.of_forall fun x => ?_)
  exact (exp_sub_one_sub_id_eq (ℓ x)).symm

/-! ## The identity (I.5.17) of the paper -/

/-- **The identity (I.5.17) in real form**:
`∫ (e^{ℓ x} - 1 - ℓ x) dΠ₁ = ∫ (cosh (ℓ x) - 1) dΠ₁`. -/
theorem integral_exp_sub_one_sub_linear_PiOne (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ}
    (hα : 0 < α) (hα2 : α < 2) (ℓ : E →L[ℝ] ℝ) :
    ∫ x, (Real.exp (ℓ x) - 1 - ℓ x) ∂(PiOne α μ)
      = ∫ x, (Real.cosh (ℓ x) - 1) ∂(PiOne α μ) := by
  have hcongr : ∫ x, (Real.exp (ℓ x) - 1 - ℓ x) ∂(PiOne α μ)
      = ∫ x, ((Real.cosh (ℓ x) - 1) + (Real.sinh (ℓ x) - ℓ x)) ∂(PiOne α μ) :=
    integral_congr_ae (Eventually.of_forall fun x => exp_sub_one_sub_id_eq (ℓ x))
  rw [hcongr, integral_add (integrable_cosh_sub_one_PiOne μ hα hα2 ℓ)
    (integrable_sinh_sub_linear_PiOne μ hα hα2 ℓ),
    integral_sinh_sub_linear_PiOne μ hα hα2 ℓ, add_zero]

/-- **The identity (I.5.17) of the paper, exponent form**:
`∫⁻ (e^{ℓ x} - 1 - ℓ x) dΠ₁ = ∫⁻ (cosh (ℓ x) - 1) dΠ₁`.

The left side is the (nonnegative) integrand of the Lévy–Khintchine exponent with the linear
compensator `⟨u,x⟩` of the paper; the right side is the even part. The difference of the two is the
odd part `sinh (ℓ x) - ℓ x`, whose integral vanishes by the symmetry of `Π₁`. -/
theorem lintegral_exp_sub_one_sub_linear_PiOne (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ}
    (hα : 0 < α) (hα2 : α < 2) (ℓ : E →L[ℝ] ℝ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (ℓ x) - 1 - ℓ x) ∂(PiOne α μ)
      = ∫⁻ x, ENNReal.ofReal (Real.cosh (ℓ x) - 1) ∂(PiOne α μ) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_sub_one_sub_linear_PiOne μ hα hα2 ℓ)
      (Eventually.of_forall fun x => exp_sub_one_sub_id_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal (integrable_cosh_sub_one_PiOne μ hα hα2 ℓ)
      (Eventually.of_forall fun x => cosh_sub_one_nonneg _),
    integral_exp_sub_one_sub_linear_PiOne μ hα hα2 ℓ]


/-! ## The Taylor series form of (I.5.17) -/

/-- **(I.5.17) with the paper's explicit series**: for `0 < α < 2`,
`∫ (e^{ℓ x} - 1 - ℓ x) dΠ₁ = ∑_{p ≥ 1} α ∫_{B₁} (ℓ y)^{2p} dy / ((2p)! (2p - α))`,
written with the index `p : ℕ` giving the exponent `2p + 2`.

This is the paper's display following (I.5.17): the odd part cancels, and the even part is expanded
in the Taylor series of `cosh` and integrated termwise (`LevyCosh`). -/
theorem integral_exp_sub_one_sub_linear_PiOne_eq_tsum (μ : Measure E) [μ.IsAddHaarMeasure]
    {α : ℝ} (hα : 0 < α) (hα2 : α < 2) (ℓ : E →L[ℝ] ℝ) :
    ∫ x, (Real.exp (ℓ x) - 1 - ℓ x) ∂(PiOne α μ)
      = ∑' p : ℕ, levySeriesTerm (E := E) μ α ℓ p := by
  have hmain : ENNReal.ofReal (∫ x, (Real.exp (ℓ x) - 1 - ℓ x) ∂(PiOne α μ))
      = ENNReal.ofReal (∑' p : ℕ, levySeriesTerm (E := E) μ α ℓ p) := by
    rw [ofReal_integral_eq_lintegral_ofReal
        (integrable_exp_sub_one_sub_linear_PiOne μ hα hα2 ℓ)
        (Eventually.of_forall fun x => exp_sub_one_sub_id_nonneg _),
      lintegral_exp_sub_one_sub_linear_PiOne μ hα hα2 ℓ,
      lintegral_cosh_sub_one_PiOne μ hα hα2 ℓ,
      ENNReal.ofReal_tsum_of_nonneg (fun p => levySeriesTerm_nonneg μ hα hα2 ℓ p)
        (summable_levySeriesTerm μ hα hα2 ℓ)]
  exact ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun x => exp_sub_one_sub_id_nonneg _)
    (tsum_nonneg fun p => levySeriesTerm_nonneg μ hα hα2 ℓ p) |>.mp hmain

/-! ## The first moment of `Π₁` and the vanishing of the linear compensator

For `α < 1` the first moment of `Π₁` is finite, and then the individual linear terms `ℓ x` and `x`
are `Π₁`-integrable with vanishing integral: the "drift" compensator of the limiting displacement
law at truncation function `x ↦ x` is `0`. (For `1 ≤ α < 2` the first moment of `Π₁` diverges, which
is why the cancellation above had to be performed for the odd combination `sinh (ℓ x) - ℓ x` rather
than for `ℓ x` separately; we make no claim about `ℓ x` in that range.) -/

/-- **The first moment of `Π₁`** for `α < 1`: `∫ ‖x‖ dΠ₁ = α/(1-α) ∫_{B₁} ‖y‖ dy`. -/
theorem lintegral_norm_PiOne (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ} (hα : 0 < α)
    (hα1 : α < 1) :
    ∫⁻ x, ENNReal.ofReal ‖x‖ ∂(PiOne α μ)
      = ENNReal.ofReal (α / (1 - α) * ∫ x in ball (0 : E) 1, ‖x‖ ∂μ) := by
  have hα2 : α < 2 := by linarith
  have hhom : ∀ (c : ℝ), 0 < c → ∀ x : E, ‖c • x‖ = c ^ (1 : ℝ) * ‖x‖ := by
    intro c hc x
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc, Real.rpow_one]
  have hint : IntegrableOn (fun x : E => ‖x‖) (ball (0 : E) 1) μ :=
    (continuous_norm.continuousOn.integrableOn_compact
      (isCompact_closedBall 0 1)).mono_set ball_subset_closedBall
  exact lintegral_PiOne_of_hom μ hα hα2 (fun x => norm_nonneg x) (by fun_prop) hα1 hhom hint

/-- `‖·‖` is `Π₁`-integrable when `α < 1`. -/
theorem integrable_norm_PiOne (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ} (hα : 0 < α)
    (hα1 : α < 1) : Integrable (fun x : E => ‖x‖) (PiOne α μ) := by
  refine (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
    (Eventually.of_forall fun x => norm_nonneg x)).mp ?_
  rw [lintegral_norm_PiOne μ hα hα1]
  exact ENNReal.ofReal_ne_top

/-- `ℓ` is `Π₁`-integrable when `α < 1`. -/
theorem integrable_linear_PiOne (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ} (hα : 0 < α)
    (hα1 : α < 1) (ℓ : E →L[ℝ] ℝ) : Integrable (fun x : E => ℓ x) (PiOne α μ) :=
  Integrable.mono' ((integrable_norm_PiOne μ hα hα1).const_mul ‖ℓ‖) (by fun_prop)
    (Eventually.of_forall fun x => ℓ.le_opNorm x)

/-- **The linear compensator vanishes**: `∫ ℓ x dΠ₁ = 0` for `α < 1`. -/
theorem integral_linear_PiOne (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ} (hα : 0 < α)
    (hα1 : α < 1) (ℓ : E →L[ℝ] ℝ) : ∫ x, ℓ x ∂(PiOne α μ) = 0 := by
  have h : ∫ x, ℓ x ∂(PiOne α μ) = -∫ x, ℓ x ∂(PiOne α μ) := by
    calc ∫ x, ℓ x ∂(PiOne α μ) = ∫ x, ℓ (-x) ∂(PiOne α μ) := by
          have hmap : ∫ y, ℓ y ∂(Measure.map (fun x : E => -x) (PiOne α μ))
              = ∫ x, ℓ (-x) ∂(PiOne α μ) := by
            refine integral_map measurable_neg.aemeasurable ?_
            rw [PiOne_symm]
            exact (integrable_linear_PiOne μ hα hα1 ℓ).aestronglyMeasurable
          rw [PiOne_symm] at hmap
          exact hmap
      _ = ∫ x, -ℓ x ∂(PiOne α μ) :=
          integral_congr_ae (Eventually.of_forall fun _ => by simp)
      _ = -∫ x, ℓ x ∂(PiOne α μ) := integral_neg _
  linarith

/-- `x ↦ x` (the identity map) is `Π₁`-integrable when `α < 1`. -/
theorem integrable_id_PiOne (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ} (hα : 0 < α)
    (hα1 : α < 1) : Integrable (fun x : E => x) (PiOne α μ) :=
  Integrable.mono' (integrable_norm_PiOne μ hα hα1) measurable_id.aestronglyMeasurable
    (Eventually.of_forall fun _ => le_rfl)

/-- **The vector-valued compensator vanishes**: `∫ x dΠ₁ = 0` for `α < 1`. -/
theorem integral_id_PiOne (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ} (hα : 0 < α)
    (hα1 : α < 1) : ∫ x, x ∂(PiOne α μ) = 0 :=
  integral_eq_zero_of_odd_of_map_neg_eq_self (PiOne_symm μ α) (integrable_id_PiOne μ hα hα1)
    (fun _ => rfl)

/-! ## The Lévy measure `Π_∞`: symmetry, Lévy integrability and compensated odd part

(Paper Section I.5.2; see the file header.) -/

/-! ### Symmetry of `Π_∞` -/


/-- The `Π_∞`-density is even. -/
theorem levyDensInf_neg (α : ℝ) (x : E) : levyDensInf (E := E) α (-x) = levyDensInf (E := E) α x := by
  simp only [levyDensInf, norm_neg]

/-- **`Π_∞` is symmetric** (radially even), as used implicitly in (I.5.17). -/
theorem PiInf_symm (μ : Measure E) [μ.IsAddHaarMeasure] (α : ℝ) :
    Measure.map (fun x : E => -x) (PiInf α μ) = PiInf α μ := by
  have hρ : ∀ x : E, levyDensInf (E := E) α (-x) = levyDensInf (E := E) α x := fun x =>
    levyDensInf_neg α x
  have hρm : Measurable (levyDensInf (E := E) α) := measurable_levyDensInf α
  rw [PiInf]
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply measurable_neg hs, withDensity_apply _ (measurable_neg hs),
    withDensity_apply _ hs]
  have hstep : ∫⁻ x in (fun x : E => -x) ⁻¹' s, levyDensInf (E := E) α x ∂μ
      = ∫⁻ x, (s.indicator (levyDensInf (E := E) α)) (-x) ∂μ := by
    rw [← lintegral_indicator (measurable_neg hs)]
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ (fun x : E => -x) ⁻¹' s
    · have hx' : -x ∈ s := hx
      rw [indicator_of_mem hx, Set.indicator_of_mem hx', hρ]
    · have hx' : -x ∉ s := hx
      rw [indicator_of_notMem hx, Set.indicator_of_notMem hx']
  rw [hstep, ← lintegral_map (f := s.indicator (levyDensInf (E := E) α))
    (g := fun x : E => -x) (hρm.indicator hs) measurable_neg, map_neg_eq_self_haar μ,
    lintegral_indicator hs]

/-! ## Radial integrals against `Π_∞` -/

/-- **Radial integration against `Π_∞`** for a function `P` homogeneous of degree `k > α`:
```
  ∫_{B_R} P dΠ_∞ = (α/(d+α)) * ((k+d)/(k-α)) R^{k-α} * ∫_{B_1} P dx.
```
The exponent `k-α` is the exponent of the `Π_∞`-moment `∫_{B_R} P dΠ_∞`; for `P = ‖·‖²` and the
truncated second moment one sets `k = 2` and `α < 2`. -/
theorem lintegral_ball_PiInf (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ} (hα : 0 < α)
    {P : E → ℝ} (hP : ∀ x, 0 ≤ P x) (hPm : Measurable P) {k : ℝ}
    (hhom : ∀ (c : ℝ), 0 < c → ∀ x, P (c • x) = c ^ k * P x) (hk : α < k) {R : ℝ}
    (hR : 0 < R) :
    ∫⁻ x in ball (0 : E) R, ENNReal.ofReal (P x) ∂(PiInf α μ)
      = ENNReal.ofReal (α / ((finrank ℝ E : ℝ) + α))
        * (ENNReal.ofReal ((k + (finrank ℝ E : ℝ)) / (k - α) * R ^ (k - α))
          * ∫⁻ x in ball (0 : E) 1, ENNReal.ofReal (P x) ∂μ) := by
  have hd : (0 : ℝ) < (finrank ℝ E : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := ℝ) (M := E)
  have hc : (0 : ℝ) ≤ α / ((finrank ℝ E : ℝ) + α) := div_nonneg hα.le (by linarith)
  -- Step 1: unfold the density
  have hstep1 : ∫⁻ x in ball (0 : E) R, ENNReal.ofReal (P x) ∂(PiInf α μ)
      = ∫⁻ x in ball (0 : E) R,
          levyDensInf (E := E) α x * ENNReal.ofReal (P x) ∂μ := by
    rw [PiInf,
      show ∫⁻ x in ball (0 : E) R, ENNReal.ofReal (P x)
          ∂(μ.withDensity (levyDensInf (E := E) α))
        = ∫⁻ x, ENNReal.ofReal (P x)
          ∂((μ.withDensity (levyDensInf (E := E) α)).restrict (ball (0 : E) R)) from rfl,
      restrict_withDensity measurableSet_ball]
    rw [lintegral_withDensity_eq_lintegral_mul (μ := μ.restrict (ball (0 : E) R))
      (f := levyDensInf (E := E) α) (measurable_levyDensInf α) hPm.ennreal_ofReal]
    simp only [Pi.mul_apply]
  -- Step 2: pointwise combination of the two density factors
  have hpt : ∀ x : E, levyDensInf (E := E) α x * ENNReal.ofReal (P x)
      = ENNReal.ofReal (α / ((finrank ℝ E : ℝ) + α))
        * ENNReal.ofReal (P x * ‖x‖ ^ (-(finrank ℝ E : ℝ) - α)) := by
    intro x
    have h1 : levyDensInf (E := E) α x
        = ENNReal.ofReal (α / ((finrank ℝ E : ℝ) + α))
          * ENNReal.ofReal (‖x‖ ^ (-(finrank ℝ E : ℝ) - α)) := by
      rw [levyDensInf, ENNReal.ofReal_mul hc]
    rw [h1, mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg x) _),
      mul_comm (‖x‖ ^ (-(finrank ℝ E : ℝ) - α)) (P x)]
  rw [hstep1, lintegral_congr hpt]
  rw [show ∫⁻ x in ball (0 : E) R, ENNReal.ofReal (α / ((finrank ℝ E : ℝ) + α))
        * ENNReal.ofReal (P x * ‖x‖ ^ (-(finrank ℝ E : ℝ) - α)) ∂μ
      = ∫⁻ x, ENNReal.ofReal (α / ((finrank ℝ E : ℝ) + α))
        * ENNReal.ofReal (P x * ‖x‖ ^ (-(finrank ℝ E : ℝ) - α))
        ∂(μ.restrict (ball (0 : E) R)) from rfl]
  rw [lintegral_const_mul' (ENNReal.ofReal (α / ((finrank ℝ E : ℝ) + α)))
    (fun x : E => ENNReal.ofReal (P x * ‖x‖ ^ (-(finrank ℝ E : ℝ) - α))) ENNReal.ofReal_ne_top]
  rw [show -(finrank ℝ E : ℝ) - α = -((finrank ℝ E : ℝ) + α) from by ring]
  rw [lintegral_ball_hom_rpow (μ := μ) hP hPm hhom (by linarith : (0:ℝ) < (finrank ℝ E : ℝ) + α)
    (by linarith : (finrank ℝ E : ℝ) + α < k + (finrank ℝ E : ℝ)) hR]
  congr 2
  ring_nf

/-! ## The truncated second moment of `Π_∞` -/

/-- The radial `Π_∞`-integral of `‖·‖²` over the unit ball. -/
theorem lintegral_ball_norm_sq_PiInf (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ} (hα : 0 < α)
    (hα2 : α < 2) :
    ∫⁻ x in ball (0 : E) 1, ENNReal.ofReal (‖x‖ ^ 2) ∂(PiInf α μ)
      = ENNReal.ofReal (α / ((finrank ℝ E : ℝ) + α))
        * (ENNReal.ofReal (((2 : ℝ) + finrank ℝ E) / (2 - α))
          * ∫⁻ x in ball (0 : E) 1, ENNReal.ofReal (‖x‖ ^ 2) ∂μ) := by
  have hhom : ∀ (c : ℝ), 0 < c → ∀ x : E, ‖c • x‖ ^ 2 = c ^ (2 : ℝ) * ‖x‖ ^ 2 := by
    intro c hc x
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc, mul_pow, ← Real.rpow_natCast]
    norm_num
  have h := lintegral_ball_PiInf μ hα (P := fun x : E => ‖x‖ ^ 2) (fun x => by positivity)
    (by fun_prop) hhom (k := 2) (by linarith) (R := 1) one_pos
  simpa using h

/-- **The tail of `Π_∞` outside the unit ball has mass at most `|B₁|`**:
`Π_∞ (B₁ᶜ) ≤ |B₁|`, computed by comparison with `min (‖x‖^{-d-α}) 1` and
`lintegral_min_rpow`. -/
theorem lintegral_ball_compl_PiInf_le (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ}
    (hα : 0 < α) :
    ∫⁻ _x in (ball (0 : E) 1)ᶜ, (1 : ℝ≥0∞) ∂(PiInf α μ) ≤ μ (ball (0 : E) 1) := by
  have hc : (0 : ℝ) ≤ α / ((finrank ℝ E : ℝ) + α) := div_nonneg hα.le (by linarith)
  rw [setLIntegral_one, PiInf, withDensity_apply _ measurableSet_ball.compl]
  have hpt : ∀ x ∈ (ball (0 : E) 1)ᶜ, levyDensInf (E := E) α x
      = ENNReal.ofReal (α / ((finrank ℝ E : ℝ) + α))
        * ENNReal.ofReal (‖x‖ ^ (-(finrank ℝ E : ℝ) - α)) := by
    intro x _
    rw [levyDensInf, ENNReal.ofReal_mul hc]
  rw [setLIntegral_congr_fun measurableSet_ball.compl hpt,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hbound : ∫⁻ x in (ball (0 : E) 1)ᶜ, ENNReal.ofReal (‖x‖ ^ (-(finrank ℝ E : ℝ) - α)) ∂μ
      ≤ ∫⁻ x, ENNReal.ofReal
        (min (‖x‖ ^ (-(finrank ℝ E : ℝ) - α)) (1 ^ (-(finrank ℝ E : ℝ) - α))) ∂μ := by
    rw [← lintegral_indicator measurableSet_ball.compl]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ (ball (0 : E) 1)ᶜ
    · rw [indicator_of_mem hx, Real.one_rpow]
      have hx1 : (1 : ℝ) ≤ ‖x‖ := by
        have h : ¬ ‖x‖ < 1 := by simpa [mem_ball, dist_zero_right] using hx
        exact not_lt.mp h
      have hle : ‖x‖ ^ (-(finrank ℝ E : ℝ) - α) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
      exact ENNReal.ofReal_le_ofReal (le_min le_rfl hle)
    · rw [indicator_of_notMem hx]
      exact zero_le
  calc ENNReal.ofReal (α / ((finrank ℝ E : ℝ) + α))
        * ∫⁻ x in (ball (0 : E) 1)ᶜ, ENNReal.ofReal (‖x‖ ^ (-(finrank ℝ E : ℝ) - α)) ∂μ
      ≤ ENNReal.ofReal (α / ((finrank ℝ E : ℝ) + α))
        * ∫⁻ x, ENNReal.ofReal
          (min (‖x‖ ^ (-(finrank ℝ E : ℝ) - α)) (1 ^ (-(finrank ℝ E : ℝ) - α))) ∂μ := by
        gcongr
    _ = ENNReal.ofReal (α / ((finrank ℝ E : ℝ) + α))
        * (ENNReal.ofReal (((finrank ℝ E : ℝ) + α) / α) * μ (ball (0 : E) 1)) := by
        rw [lintegral_min_rpow μ hα one_pos, Real.one_rpow, mul_one]
    _ = μ (ball (0 : E) 1) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hc,
          show α / ((finrank ℝ E : ℝ) + α) * (((finrank ℝ E : ℝ) + α) / α) = 1 from by
            field_simp, ENNReal.ofReal_one, one_mul]

/-- **Pointwise split of the truncated second moment.** -/
theorem ofReal_min_norm_sq_eq_indicator (x : E) :
    ENNReal.ofReal (min (‖x‖ ^ 2) 1)
      = (ball (0 : E) 1).indicator (fun x => ENNReal.ofReal (‖x‖ ^ 2)) x
        + ((ball (0 : E) 1)ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) x := by
  by_cases hx : x ∈ ball (0 : E) 1
  · have hx1 : ‖x‖ < 1 := by simpa [mem_ball, dist_zero_right] using hx
    have hx2 : ‖x‖ ^ 2 < 1 := by nlinarith [norm_nonneg x]
    rw [indicator_of_mem hx, indicator_of_notMem (by simpa using hx), add_zero,
      min_eq_left hx2.le]
  · have hx1 : (1 : ℝ) ≤ ‖x‖ := by
      have h : ¬ ‖x‖ < 1 := by simpa [mem_ball, dist_zero_right] using hx
      exact not_lt.mp h
    have hx2 : (1 : ℝ) ≤ ‖x‖ ^ 2 := by nlinarith [norm_nonneg x]
    rw [indicator_of_notMem hx, indicator_of_mem (by simpa using hx), zero_add,
      min_eq_right hx2, ENNReal.ofReal_one]

/-- **The truncated second moment of `Π_∞` is finite**: the small jumps contribute through the
`Π_∞`-moment of `‖·‖²` over the unit ball, the large jumps through the mass of `B₁ᶜ`. -/
theorem lintegral_min_norm_sq_PiInf_le (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ}
    (hα : 0 < α) (hα2 : α < 2) :
    ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂(PiInf α μ)
      ≤ ENNReal.ofReal (α / ((finrank ℝ E : ℝ) + α))
          * (ENNReal.ofReal (((2 : ℝ) + finrank ℝ E) / (2 - α))
            * ∫⁻ x in ball (0 : E) 1, ENNReal.ofReal (‖x‖ ^ 2) ∂μ)
        + μ (ball (0 : E) 1) := by
  have hpt : ∀ x : E, ENNReal.ofReal (min (‖x‖ ^ 2) 1)
      = (ball (0 : E) 1).indicator (fun x => ENNReal.ofReal (‖x‖ ^ 2)) x
        + ((ball (0 : E) 1)ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) x :=
    ofReal_min_norm_sq_eq_indicator
  rw [show (fun x : E => ENNReal.ofReal (min (‖x‖ ^ 2) 1))
      = (fun x : E => (ball (0 : E) 1).indicator (fun x => ENNReal.ofReal (‖x‖ ^ 2)) x
        + ((ball (0 : E) 1)ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) x) from funext hpt,
    lintegral_add_left (Measurable.indicator (by fun_prop) measurableSet_ball),
    lintegral_indicator measurableSet_ball, lintegral_indicator measurableSet_ball.compl,
    lintegral_ball_norm_sq_PiInf μ hα hα2]
  gcongr
  exact lintegral_ball_compl_PiInf_le μ hα

/-- **`Π_∞` is a Lévy measure** for `0 < α < 2`: `∫ (‖x‖² ∧ 1) dΠ_∞ < ∞`. -/
theorem PiInf_levy_measure (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ} (hα : 0 < α)
    (hα2 : α < 2) :
    ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂(PiInf α μ) ≠ ⊤ := by
  have hfin : ∫⁻ x in ball (0 : E) 1, ENNReal.ofReal (‖x‖ ^ 2) ∂μ ≠ ⊤ := by
    have hb : ∫⁻ x in ball (0 : E) 1, ENNReal.ofReal (‖x‖ ^ 2) ∂μ
        ≤ ∫⁻ x in ball (0 : E) 1, (1 : ℝ≥0∞) ∂μ := by
      refine lintegral_mono_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
      have hx1 : ‖x‖ < 1 := by simpa [mem_ball, dist_zero_right] using hx
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by nlinarith [norm_nonneg x])
    rw [setLIntegral_one] at hb
    exact ne_of_lt (lt_of_le_of_lt hb measure_ball_lt_top)
  refine ne_of_lt (lt_of_le_of_lt (lintegral_min_norm_sq_PiInf_le μ hα hα2) ?_)
  have h1 : ENNReal.ofReal (α / ((finrank ℝ E : ℝ) + α))
      * (ENNReal.ofReal (((2 : ℝ) + finrank ℝ E) / (2 - α))
        * ∫⁻ x in ball (0 : E) 1, ENNReal.ofReal (‖x‖ ^ 2) ∂μ) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin)
  exact ENNReal.add_lt_top.mpr ⟨lt_top_iff_ne_top.mpr h1, measure_ball_lt_top⟩

/-- `min (‖·‖²) 1` is `Π_∞`-integrable. -/
theorem integrable_min_norm_sq_PiInf (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ}
    (hα : 0 < α) (hα2 : α < 2) :
    Integrable (fun x : E => min (‖x‖ ^ 2) 1) (PiInf α μ) :=
  (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
    (Eventually.of_forall fun x => le_min (by positivity) zero_le_one)).mp
    (PiInf_levy_measure μ hα hα2)

/-! ## The compensated odd part for `Π_∞`

`Π_∞` has infinite first moment for `α ≥ 1`, so the linear term `ℓ x` must be compensated with a
symmetric (even) truncation function; the paper uses `1(‖x‖ ≤ 1)`. The resulting integrand
`x ↦ sin (ℓ x) - ℓ x 1(‖x‖ ≤ 1)` is odd, is dominated by a multiple of `min (‖x‖²) 1`, and hence
has vanishing `Π_∞`-integral. -/

/-- **The truncated odd part is dominated by the truncated second moment.** -/
theorem abs_sin_sub_trunc_le (ℓ : E →L[ℝ] ℝ) (x : E) :
    |Real.sin (ℓ x) - ℓ x * (if ‖x‖ ≤ 1 then 1 else 0)|
      ≤ 2 * max 1 (‖ℓ‖ ^ 2) * min (‖x‖ ^ 2) 1 := by
  have hC : (1 : ℝ) ≤ 2 * max 1 (‖ℓ‖ ^ 2) := by
    nlinarith [le_max_left (1 : ℝ) (‖ℓ‖ ^ 2)]
  have hop : |ℓ x| ≤ ‖ℓ‖ * ‖x‖ := by
    calc |ℓ x| = ‖ℓ x‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖ℓ‖ * ‖x‖ := ℓ.le_opNorm x
  have hs : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  rcases lt_or_ge (1 : ℝ) ‖x‖ with hx | hx
  · -- `‖x‖ > 1`: the truncation kills the linear term and `min (‖x‖²) 1 = 1`
    rw [ite_eq_right (by linarith), mul_zero, sub_zero, min_eq_right (by nlinarith)]
    have h1 : |Real.sin (ℓ x)| ≤ 1 := Real.abs_sin_le_one (ℓ x)
    linarith
  · rw [ite_eq_left hx, mul_one, min_eq_left (by nlinarith)]
    rcases lt_or_ge (1 : ℝ) |ℓ x| with h2 | h2
    · -- `|ℓ x| > 1` and `‖x‖ ≤ 1`
      have h3 : (1 : ℝ) ≤ ‖ℓ‖ * ‖x‖ := le_trans h2.le hop
      have h4 : |ℓ x| ≤ ‖ℓ‖ ^ 2 * ‖x‖ ^ 2 := by
        have h5 : (‖ℓ‖ * ‖x‖) ^ 2 = ‖ℓ‖ ^ 2 * ‖x‖ ^ 2 := by ring
        calc |ℓ x| ≤ ‖ℓ‖ * ‖x‖ := hop
          _ ≤ (‖ℓ‖ * ‖x‖) ^ 2 := by nlinarith
          _ = ‖ℓ‖ ^ 2 * ‖x‖ ^ 2 := h5
      have h6 : |Real.sin (ℓ x) - ℓ x| ≤ 1 + |ℓ x| := by
        have h7 : |Real.sin (ℓ x)| ≤ 1 := Real.abs_sin_le_one (ℓ x)
        linarith [abs_sub (Real.sin (ℓ x)) (ℓ x)]
      have h8 : ‖ℓ‖ ^ 2 * ‖x‖ ^ 2 ≤ 2 * max 1 (‖ℓ‖ ^ 2) * ‖x‖ ^ 2 := by
        have h9 : ‖ℓ‖ ^ 2 ≤ max 1 (‖ℓ‖ ^ 2) := le_max_right _ _
        nlinarith [sq_nonneg ‖x‖]
      have h10 : (1 : ℝ) ≤ ‖ℓ‖ ^ 2 * ‖x‖ ^ 2 := by nlinarith
      have h11 : |Real.sin (ℓ x) - ℓ x| ≤ 2 * (‖ℓ‖ ^ 2 * ‖x‖ ^ 2) := by linarith
      have h12 : (2 : ℝ) * (‖ℓ‖ ^ 2 * ‖x‖ ^ 2)
          ≤ 2 * max 1 (‖ℓ‖ ^ 2) * ‖x‖ ^ 2 := by
        have h9 : ‖ℓ‖ ^ 2 * ‖x‖ ^ 2 ≤ max 1 (‖ℓ‖ ^ 2) * ‖x‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)
        have h9' : (0 : ℝ) ≤ max 1 (‖ℓ‖ ^ 2) * ‖x‖ ^ 2 :=
          mul_nonneg (le_trans zero_le_one (le_max_left _ _)) (sq_nonneg _)
        linarith
      linarith
    · -- `|ℓ x| ≤ 1` and `‖x‖ ≤ 1`: cubic control of `sin - id`
      have h3 : |Real.sin (ℓ x) - ℓ x| ≤ |ℓ x| ^ 3 / 6 := by
        simpa [abs_sub_comm] using Real.abs_sub_sin_le (ℓ x)
      have h4 : |ℓ x| ^ 3 / 6 ≤ |ℓ x| ^ 2 := by
        have h5 : |ℓ x| ^ 3 = |ℓ x| ^ 2 * |ℓ x| := by ring
        nlinarith [abs_nonneg (ℓ x)]
      have h5 : |ℓ x| ^ 2 ≤ ‖ℓ‖ ^ 2 * ‖x‖ ^ 2 := by
        have h6 : |ℓ x| ^ 2 ≤ (‖ℓ‖ * ‖x‖) ^ 2 := by nlinarith [abs_nonneg (ℓ x)]
        calc |ℓ x| ^ 2 ≤ (‖ℓ‖ * ‖x‖) ^ 2 := h6
          _ = ‖ℓ‖ ^ 2 * ‖x‖ ^ 2 := by ring
      have h6 : ‖ℓ‖ ^ 2 * ‖x‖ ^ 2 ≤ 2 * max 1 (‖ℓ‖ ^ 2) * ‖x‖ ^ 2 := by
        have h7 : ‖ℓ‖ ^ 2 * ‖x‖ ^ 2 ≤ max 1 (‖ℓ‖ ^ 2) * ‖x‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)
        have h7' : (0 : ℝ) ≤ max 1 (‖ℓ‖ ^ 2) * ‖x‖ ^ 2 :=
          mul_nonneg (le_trans zero_le_one (le_max_left _ _)) (sq_nonneg _)
        linarith
      linarith

/-- **Integrability of the compensated odd part for `Π_∞`.** -/
theorem integrable_sin_sub_trunc_PiInf (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ}
    (hα : 0 < α) (hα2 : α < 2) (ℓ : E →L[ℝ] ℝ) :
    Integrable (fun x : E => Real.sin (ℓ x) - ℓ x * (if ‖x‖ ≤ 1 then 1 else 0))
      (PiInf α μ) := by
  have hC : (0 : ℝ) ≤ 2 * max 1 (‖ℓ‖ ^ 2) := by positivity
  have hcond : Measurable fun x : E => if ‖x‖ ≤ 1 then (1 : ℝ) else 0 := by
    classical
    have h : (fun x : E => if x ∈ closedBall (0 : E) 1 then (1 : ℝ) else 0)
        = fun x : E => if ‖x‖ ≤ 1 then (1 : ℝ) else 0 := by
      funext x
      simp [mem_closedBall, dist_zero_right]
    rw [← h]
    exact Measurable.ite measurableSet_closedBall measurable_const measurable_const
  have hmeas : Measurable fun x : E =>
      Real.sin (ℓ x) - ℓ x * (if ‖x‖ ≤ 1 then (1 : ℝ) else 0) :=
    Measurable.sub (Real.continuous_sin.measurable.comp ℓ.measurable)
      (ℓ.measurable.mul hcond)
  refine Integrable.mono' ((integrable_min_norm_sq_PiInf μ hα hα2).const_mul
    (2 * max 1 (‖ℓ‖ ^ 2))) hmeas.aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_eq_abs]
  exact abs_sin_sub_trunc_le ℓ x

/-- **The compensated odd part of `Π_∞` has vanishing integral.** -/
theorem integral_sin_sub_trunc_PiInf (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ}
    (hα : 0 < α) (hα2 : α < 2) (ℓ : E →L[ℝ] ℝ) :
    ∫ x, (Real.sin (ℓ x) - ℓ x * (if ‖x‖ ≤ 1 then 1 else 0)) ∂(PiInf α μ) = 0 := by
  refine integral_eq_zero_of_odd_of_map_neg_eq_self (PiInf_symm μ α) ?_ ?_
  · exact integrable_sin_sub_trunc_PiInf μ hα hα2 ℓ
  · intro x
    have hnorm : ‖-x‖ = ‖x‖ := norm_neg x
    simp only [ContinuousLinearMap.map_neg, Real.sin_neg, hnorm]
    ring

/-- **The even part of the exponent is dominated by the truncated second moment.** -/
theorem one_sub_cos_le_trunc (ℓ : E →L[ℝ] ℝ) (x : E) :
    1 - Real.cos (ℓ x) ≤ 2 * max 1 (‖ℓ‖ ^ 2) * min (‖x‖ ^ 2) 1 := by
  have hop : |ℓ x| ≤ ‖ℓ‖ * ‖x‖ := by
    calc |ℓ x| = ‖ℓ x‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖ℓ‖ * ‖x‖ := ℓ.le_opNorm x
  have hmax : (0 : ℝ) ≤ max 1 (‖ℓ‖ ^ 2) := le_trans zero_le_one (le_max_left _ _)
  have hcos : -1 ≤ Real.cos (ℓ x) := Real.neg_one_le_cos (ℓ x)
  rcases lt_or_ge (1 : ℝ) ‖x‖ with hx | hx
  · -- `‖x‖ > 1`: `1 - cos ≤ 2` and `min (‖x‖²) 1 = 1`
    rw [min_eq_right (by nlinarith [norm_nonneg x])]
    have h1 : (1 : ℝ) ≤ max 1 (‖ℓ‖ ^ 2) := le_max_left _ _
    nlinarith
  · rw [min_eq_left (by nlinarith [norm_nonneg x])]
    rcases lt_or_ge (1 : ℝ) |ℓ x| with h2 | h2
    · -- `|ℓ x| > 1` and `‖x‖ ≤ 1`
      have h3 : (1 : ℝ) ≤ ‖ℓ‖ * ‖x‖ := le_trans h2.le hop
      have h4 : (1 : ℝ) ≤ ‖ℓ‖ ^ 2 * ‖x‖ ^ 2 := by
        have h5 : (‖ℓ‖ * ‖x‖) ^ 2 = ‖ℓ‖ ^ 2 * ‖x‖ ^ 2 := by ring
        nlinarith
      have h5 : ‖ℓ‖ ^ 2 * ‖x‖ ^ 2 ≤ max 1 (‖ℓ‖ ^ 2) * ‖x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)
      have h7 : (0 : ℝ) ≤ max 1 (‖ℓ‖ ^ 2) * ‖x‖ ^ 2 := mul_nonneg hmax (sq_nonneg _)
      nlinarith
    · -- `|ℓ x| ≤ 1` and `‖x‖ ≤ 1`: cosine is a contraction of `x²/2`
      have h1 : 1 - Real.cos (ℓ x) ≤ (ℓ x) ^ 2 / 2 := by
        have := Real.one_sub_sq_div_two_le_cos (x := ℓ x)
        linarith
      have h3 : (ℓ x) ^ 2 ≤ ‖ℓ‖ ^ 2 * ‖x‖ ^ 2 := by
        have h4 : |ℓ x| ^ 2 ≤ (‖ℓ‖ * ‖x‖) ^ 2 := by nlinarith [abs_nonneg (ℓ x)]
        calc (ℓ x) ^ 2 = |ℓ x| ^ 2 := by rw [sq_abs]
          _ ≤ (‖ℓ‖ * ‖x‖) ^ 2 := h4
          _ = ‖ℓ‖ ^ 2 * ‖x‖ ^ 2 := by ring
      have h5 : ‖ℓ‖ ^ 2 * ‖x‖ ^ 2 ≤ max 1 (‖ℓ‖ ^ 2) * ‖x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)
      have h6 : (0 : ℝ) ≤ max 1 (‖ℓ‖ ^ 2) * ‖x‖ ^ 2 := mul_nonneg hmax (sq_nonneg _)
      nlinarith

/-- **The even part of the `Π_∞` exponent is finite**:
`∫ (1 - cos (ℓ x)) dΠ_∞ < ∞`, dominated by `2 max 1 ‖ℓ‖² · ∫ (‖x‖² ∧ 1) dΠ_∞`. -/
theorem lintegral_one_sub_cos_PiInf_ne_top (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ}
    (hα : 0 < α) (hα2 : α < 2) (ℓ : E →L[ℝ] ℝ) :
    ∫⁻ x, ENNReal.ofReal (1 - Real.cos (ℓ x)) ∂(PiInf α μ) ≠ ⊤ := by
  have hC : (0 : ℝ) ≤ 2 * max 1 (‖ℓ‖ ^ 2) := by positivity
  have hInt : Integrable (fun x : E => 2 * max 1 (‖ℓ‖ ^ 2) * min (‖x‖ ^ 2) 1) (PiInf α μ) :=
    (integrable_min_norm_sq_PiInf μ hα hα2).const_mul _
  have hb : ∫⁻ x, ENNReal.ofReal (1 - Real.cos (ℓ x)) ∂(PiInf α μ)
      ≤ ENNReal.ofReal (∫ x, 2 * max 1 (‖ℓ‖ ^ 2) * min (‖x‖ ^ 2) 1 ∂(PiInf α μ)) := by
    calc ∫⁻ x, ENNReal.ofReal (1 - Real.cos (ℓ x)) ∂(PiInf α μ)
        ≤ ∫⁻ x, ENNReal.ofReal (2 * max 1 (‖ℓ‖ ^ 2) * min (‖x‖ ^ 2) 1) ∂(PiInf α μ) :=
          lintegral_mono fun x => ENNReal.ofReal_le_ofReal (one_sub_cos_le_trunc ℓ x)
      _ = ENNReal.ofReal (∫ x, 2 * max 1 (‖ℓ‖ ^ 2) * min (‖x‖ ^ 2) 1 ∂(PiInf α μ)) :=
          (ofReal_integral_eq_lintegral_ofReal hInt (Eventually.of_forall fun x =>
            mul_nonneg hC (le_min (by positivity) zero_le_one))).symm
  exact ne_of_lt (lt_of_le_of_lt hb ENNReal.ofReal_lt_top)

/-! ## Absolute continuity of the Lévy measures

Lemma I.5.17 attributes to [80, Theorem 27.7] (Sato) the fact that a Lévy law at a fixed time is
absolutely continuous with respect to Lebesgue measure as soon as the finite measure
`(‖x‖² ∧ 1) Π` is. The checkable input here is that our three Lévy measures are given by
`withDensity` of an explicit real function against Lebesgue measure; we record it. (The passage to
the law of `L_t` itself requires the Lévy process, which we do not construct here.) -/

theorem PiOne_absolutelyContinuous (μ : Measure E) [μ.IsAddHaarMeasure] (α : ℝ) :
    PiOne α μ ≪ μ :=
  withDensity_absolutelyContinuous μ (levyDensOne (E := E) α)

theorem PiLam_absolutelyContinuous (μ : Measure E) [μ.IsAddHaarMeasure] (α lam : ℝ) :
    PiLam α lam μ ≪ μ :=
  withDensity_absolutelyContinuous μ (levyDensLam (E := E) α lam)

theorem PiInf_absolutelyContinuous (μ : Measure E) [μ.IsAddHaarMeasure] (α : ℝ) :
    PiInf α μ ≪ μ :=
  withDensity_absolutelyContinuous μ (levyDensInf (E := E) α)

/-- **`Π_λ` is symmetric** (radially even). -/
theorem PiLam_symm (μ : Measure E) [μ.IsAddHaarMeasure] (α lam : ℝ) :
    Measure.map (fun x : E => -x) (PiLam α lam μ) = PiLam α lam μ := by
  have hρ : ∀ x : E, levyDensLam (E := E) α lam (-x) = levyDensLam (E := E) α lam x := by
    intro x
    simp only [levyDensLam, norm_neg]
  have hρm : Measurable (levyDensLam (E := E) α lam) := measurable_levyDensLam α lam
  rw [PiLam]
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply measurable_neg hs, withDensity_apply _ (measurable_neg hs),
    withDensity_apply _ hs]
  have hstep : ∫⁻ x in (fun x : E => -x) ⁻¹' s, levyDensLam (E := E) α lam x ∂μ
      = ∫⁻ x, (s.indicator (levyDensLam (E := E) α lam)) (-x) ∂μ := by
    rw [← lintegral_indicator (measurable_neg hs)]
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ (fun x : E => -x) ⁻¹' s
    · have hx' : -x ∈ s := hx
      rw [indicator_of_mem hx, Set.indicator_of_mem hx', hρ]
    · have hx' : -x ∉ s := hx
      rw [indicator_of_notMem hx, Set.indicator_of_notMem hx']
  rw [hstep, ← lintegral_map (f := s.indicator (levyDensLam (E := E) α lam))
    (g := fun x : E => -x) (hρm.indicator hs) measurable_neg, map_neg_eq_self_haar μ,
    lintegral_indicator hs]

/-! ## Infinite total mass: `Π₁(ℝ^d) = Π_∞(ℝ^d) = ⊤`

Both Lévy measures have infinite mass (`Π₁` and `Π_∞` differ by the finite measure `Π_∞ - Π₁` of
mass `|B₁|`, (I.5.18)): the associated symmetric jump processes have infinite activity. In
particular the stopped law of Definition I.5.16 is **not** the law of a compound Poisson process,
so it cannot be produced without genuine Lévy-process theory. -/

/-- The function `x ↦ ‖x‖ ^ (-d-α)` has infinite integral over the unit ball. -/
theorem lintegral_ball_norm_rpow_neg_top (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ}
    (hα : 0 < α) :
    ∫⁻ x in ball (0 : E) 1, ENNReal.ofReal (‖x‖ ^ (-(finrank ℝ E : ℝ) - α)) ∂μ = ⊤ := by
  set f : E → ℝ≥0∞ := fun x => ENNReal.ofReal (‖x‖ ^ (-(finrank ℝ E : ℝ) - α)) with hf
  have hfm : Measurable f := by fun_prop
  have hhom : ∀ (c : ℝ), 0 < c → ∀ x : E, ‖c • x‖ ^ (-(finrank ℝ E : ℝ) - α)
      = c ^ (-(finrank ℝ E : ℝ) - α) * ‖x‖ ^ (-(finrank ℝ E : ℝ) - α) := by
    intro c hc x
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc, Real.mul_rpow hc.le (norm_nonneg x)]
  have hscale : ∀ r : ℝ, 0 < r →
      ∫⁻ x in ball (0 : E) r, f x ∂μ
        = ENNReal.ofReal (r ^ (-α)) * ∫⁻ x in ball (0 : E) 1, f x ∂μ := by
    intro r hr
    have h := lintegral_ball_hom (μ := μ) (P := fun x : E => ‖x‖ ^ (-(finrank ℝ E : ℝ) - α))
      (fun x => Real.rpow_nonneg (norm_nonneg x) _) (by fun_prop) hhom (r := r) hr
    rwa [show -(finrank ℝ E : ℝ) - α + (finrank ℝ E : ℝ) = -α from by ring] at h
  by_contra htop
  have hC : ∫⁻ x in ball (0 : E) 1, f x ∂μ ≠ ⊤ := fun h => htop h
  -- split the ball into the half ball and the annulus
  have hpt : (ball (0 : E) 1).indicator f
      = (ball (0 : E) (1 / 2)).indicator f
        + ((ball (0 : E) 1) \ ball (0 : E) (1 / 2)).indicator f := by
    have hdisj : Disjoint (ball (0 : E) (1 / 2)) ((ball (0 : E) 1) \ ball (0 : E) (1 / 2)) :=
      disjoint_sdiff_right
    have hunion : ball (0 : E) (1 / 2) ∪ ((ball (0 : E) 1) \ ball (0 : E) (1 / 2))
        = ball (0 : E) 1 := by
      ext x
      constructor
      · rintro (h | h)
        · exact ball_subset_ball (by norm_num) h
        · exact h.1
      · intro h
        by_cases h2 : x ∈ ball (0 : E) (1 / 2)
        · exact Or.inl h2
        · exact Or.inr ⟨h, h2⟩
    conv_lhs => rw [← hunion]
    rw [Set.indicator_union_of_disjoint hdisj]
    rfl
  have hsum : ∫⁻ x in ball (0 : E) 1, f x ∂μ
      = ∫⁻ x in ball (0 : E) (1 / 2), f x ∂μ
        + ∫⁻ x in (ball (0 : E) 1) \ ball (0 : E) (1 / 2), f x ∂μ := by
    rw [← lintegral_indicator measurableSet_ball (f := f), hpt]
    simp only [Pi.add_apply]
    rw [lintegral_add_left (hfm.indicator measurableSet_ball),
      lintegral_indicator measurableSet_ball (f := f),
      lintegral_indicator (measurableSet_ball.diff measurableSet_ball) (f := f)]
  have hhalf : ∫⁻ x in ball (0 : E) (1 / 2), f x ∂μ
      = ENNReal.ofReal (2 ^ α) * ∫⁻ x in ball (0 : E) 1, f x ∂μ := by
    have h := hscale (1 / 2) (by norm_num)
    have hrw : ((1 : ℝ) / 2) ^ (-α) = 2 ^ α := by
      rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.inv_rpow (by norm_num),
        ← Real.rpow_neg (by norm_num)]
      ring_nf
    rwa [hrw] at h
  -- the ball integral is positive
  have hCpos : 0 < ∫⁻ x in ball (0 : E) 1, f x ∂μ := by
    have hge : ∫⁻ x in ball (0 : E) (1 / 2), f x ∂μ
        ≤ ∫⁻ x in ball (0 : E) 1, f x ∂μ :=
      lintegral_mono_set (ball_subset_ball (by norm_num))
    have hlow : ∫⁻ x in ball (0 : E) (1 / 2), (1 : ℝ≥0∞) ∂μ
        ≤ ∫⁻ x in ball (0 : E) (1 / 2), f x ∂μ := by
      refine lintegral_mono_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_ball,
        ae_mono Measure.restrict_le_self (ae_ne_zero (E := E) μ)] with x hx hx0
      rw [← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      have hx' : ‖x‖ < 1 / 2 := by simpa [mem_ball, dist_zero_right] using hx
      have hxpos : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx0
      have hexp : (-(finrank ℝ E : ℝ) - α) ≤ 0 := by
        have hd : (0 : ℝ) < (finrank ℝ E : ℝ) := by
          exact_mod_cast Module.finrank_pos (R := ℝ) (M := E)
        linarith
      have hmono : ((1 : ℝ) / 2) ^ (-(finrank ℝ E : ℝ) - α) ≤ ‖x‖ ^ (-(finrank ℝ E : ℝ) - α) :=
        Real.rpow_le_rpow_of_nonpos hxpos hx'.le hexp
      have hhalf : ((1 : ℝ) / 2) ^ (-(finrank ℝ E : ℝ) - α) ≥ 1 := by
        rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.inv_rpow (by norm_num),
          ← Real.rpow_neg (by norm_num)]
        refine Real.one_le_rpow (by norm_num) ?_
        have hd : (0 : ℝ) < (finrank ℝ E : ℝ) := by
          exact_mod_cast Module.finrank_pos (R := ℝ) (M := E)
        linarith
      linarith
    calc 0 < μ (ball (0 : E) (1 / 2)) := measure_ball_pos μ 0 (by norm_num)
      _ = ∫⁻ x in ball (0 : E) (1 / 2), (1 : ℝ≥0∞) ∂μ := (setLIntegral_one _).symm
      _ ≤ ∫⁻ x in ball (0 : E) 1, f x ∂μ := le_trans hlow hge
  -- the identity `C = 2^α C + S` with `S ≥ 0`
  have hmain : ∫⁻ x in ball (0 : E) 1, f x ∂μ
      = ENNReal.ofReal (2 ^ α) * ∫⁻ x in ball (0 : E) 1, f x ∂μ
        + ∫⁻ x in (ball (0 : E) 1) \ ball (0 : E) (1 / 2), f x ∂μ := by
    conv_lhs => rw [hsum]
    conv_lhs => rw [hhalf]
  have hle : ENNReal.ofReal (2 ^ α) * ∫⁻ x in ball (0 : E) 1, f x ∂μ
      ≤ ∫⁻ x in ball (0 : E) 1, f x ∂μ := by
    calc ENNReal.ofReal (2 ^ α) * ∫⁻ x in ball (0 : E) 1, f x ∂μ
        ≤ ENNReal.ofReal (2 ^ α) * ∫⁻ x in ball (0 : E) 1, f x ∂μ
          + ∫⁻ x in (ball (0 : E) 1) \ ball (0 : E) (1 / 2), f x ∂μ := le_self_add
      _ = ∫⁻ x in ball (0 : E) 1, f x ∂μ := hmain.symm
  have h2 : (1 : ℝ) < 2 ^ α := by
    rw [← Real.rpow_zero]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hα
  have hto : (ENNReal.ofReal (2 ^ α) * ∫⁻ x in ball (0 : E) 1, f x ∂μ).toReal
      ≤ (∫⁻ x in ball (0 : E) 1, f x ∂μ).toReal :=
    ENNReal.toReal_mono hC hle
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at hto
  have hpos : 0 < (∫⁻ x in ball (0 : E) 1, f x ∂μ).toReal :=
    ENNReal.toReal_pos hCpos.ne' hC
  nlinarith


/-- **`x ↦ ‖x‖ ^ (-d-α)` is not integrable near the origin**: its integral over the whole space
is infinite. (Near `0` the integrand is `‖x‖^{-d}·‖x‖^{-α}`, whose radial integral
`∫_0^1 r^{-α-1}dr` diverges.) -/
theorem lintegral_norm_rpow_neg_top (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ} (hα : 0 < α) :
    ∫⁻ x, ENNReal.ofReal (‖x‖ ^ (-(finrank ℝ E : ℝ) - α)) ∂μ = ⊤ := by
  have h := lintegral_add_compl (μ := μ)
    (f := fun x => ENNReal.ofReal (‖x‖ ^ (-(finrank ℝ E : ℝ) - α)))
    (s := ball (0 : E) 1) measurableSet_ball
  rw [← h, lintegral_ball_norm_rpow_neg_top (μ := μ) hα, top_add]

/-- **`Π_∞` has infinite total mass**: `Π_∞(ℝ^d) = ⊤`. In particular the symmetric `α`-stable
Lévy process has infinite activity: it is not a compound Poisson process. -/
theorem PiInf_apply_univ_eq_top (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ} (hα : 0 < α) :
    PiInf α μ Set.univ = ⊤ := by
  have hc : (0 : ℝ) < α / ((finrank ℝ E : ℝ) + α) := by positivity
  rw [PiInf, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hfun : (fun x : E => levyDensInf (E := E) α x)
      = fun x => ENNReal.ofReal (α / ((finrank ℝ E : ℝ) + α))
        * ENNReal.ofReal (‖x‖ ^ (-(finrank ℝ E : ℝ) - α)) := by
    funext x
    rw [levyDensInf, ENNReal.ofReal_mul hc.le]
  rw [hfun, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_norm_rpow_neg_top (μ := μ) hα]
  exact ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hc))

/-- **`Π₁` has infinite total mass**: `Π₁(ℝ^d) = ⊤`, and `Π_λ` likewise. (Near the origin the
density is `≈ (α/(d+α))‖x‖^{-d-α}`, which is not integrable, so the truncated process has infinite
activity; the gap `Π_∞ − Π₁` has finite mass `|B₁|` by (I.5.18), which forces the conclusion.) -/
theorem PiOne_apply_univ_eq_top (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ} (hα : 0 < α)
    (hα2 : α < 2) : PiOne α μ Set.univ = ⊤ := by
  have hle : levyDensOne (E := E) α ≤ levyDensInf (E := E) α := fun x =>
    levyDensLam_le_levyDensInf hα one_pos x
  have hgap : ∫⁻ x, (levyDensInf (E := E) α x - levyDensOne (E := E) α x) ∂μ ≠ ⊤ := by
    rw [lintegral_levyDens_gap_one μ hα hα2]
    exact measure_ball_lt_top.ne
  have hInf : ∫⁻ x, levyDensInf (E := E) α x ∂μ = ⊤ := by
    have := PiInf_apply_univ_eq_top (μ := μ) hα
    rwa [PiInf, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
  by_contra htop
  have hOne : ∫⁻ x, levyDensOne (E := E) α x ∂μ ≠ ⊤ := by
    intro h
    exact htop (by rw [PiOne, PiLam, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ]; exact h)
  have hsub := lintegral_sub' (f := levyDensInf (E := E) α) (g := levyDensOne (E := E) α)
    (measurable_levyDensOne α).aemeasurable hOne (Eventually.of_forall hle)
  rw [hsub, hInf, ENNReal.top_sub hOne] at hgap
  exact hgap rfl

end PercLib.CriticalLRP.LevyAnalysis
