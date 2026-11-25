/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Formalization derived from T. Hutchcroft, "Critical long-range percolation I: High effective
dimension", arXiv:2508.18807v1, Section I.5.2.

The analytic content of (I.5.17): the Taylor expansion of `cosh` together with termwise
integration (Fubini/Tonelli) gives

  `∫ (e^{ℓ x} - 1 - ℓ x) dΠ₁ = ∫ (cosh (ℓ x) - 1) dΠ₁
     = ∑_{p ≥ 1} α ∫_{B₁} (ℓ y)^{2p} dy / ((2p)! (2p - α))`.

We prove (a) the identity in `ℝ≥0∞` form (so nothing about integrability of the integrand has to be
assumed), (b) summability of the real right-hand side (the paper's "all relevant sums converge"),
and (c) finiteness of the resulting value. The passage from the first expression to the second is
parity cancellation (`sinh - id` is odd and `Π₁` is symmetric); we do not need it, since we compute
`∫ (cosh - 1) dΠ₁` directly, which is the quantity the paper evaluates.

The exponent is written `2p + 2` with `p : ℕ`, i.e. the paper's `2p`, `p ≥ 1`.
-/
module

public import PercLib.CriticalLRP.LevyAnalysis.Measures
public import PercLib.CriticalLRP.LevyAnalysis.LevyMass

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open MeasureTheory Metric Set Filter
open Module
open scoped ENNReal NNReal Topology Pointwise Interval BigOperators

namespace PercLib.CriticalLRP.LevyAnalysis

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- Even powers of real numbers are nonnegative. -/
theorem pow_of_two_dvd_nonneg {x : ℝ} {n : ℕ} (h : 2 ∣ n) : 0 ≤ x ^ n := by
  obtain ⟨k, rfl⟩ := h
  rw [pow_mul]
  exact pow_nonneg (sq_nonneg x) k

/-- Factorials of natural numbers are positive reals. -/
theorem factorial_cast_pos (n : ℕ) : (0 : ℝ) < (n.factorial : ℝ) := by
  exact_mod_cast Nat.factorial_pos n

/-! ## The shift of the `cosh` series -/

/-- `cosh t - 1 = ∑_{p ≥ 0} t^{2p+2}/(2p+2)!`. -/
theorem cosh_sub_one_eq_tsum (t : ℝ) :
    Real.cosh t - 1 = ∑' p : ℕ, t ^ (2 * p + 2) / ((2 * p + 2).factorial : ℝ) := by
  have hs : Summable (fun n : ℕ => t ^ (2 * n) / ((2 * n).factorial : ℝ)) :=
    (Real.hasSum_cosh t).summable
  rw [Real.cosh_eq_tsum t, hs.tsum_eq_zero_add]
  simp only [Nat.mul_zero, pow_zero, Nat.cast_one, Nat.factorial_zero, div_one]
  rw [add_sub_cancel_left]
  refine tsum_congr fun p => ?_
  rw [Nat.mul_succ]

/-! ## The displacement series -/

/-- The `p`-th term of the displacement series:
`α ∫_{B₁} (ℓ y)^{2p+2} dy / ((2p+2)! (2p+2-α))`. -/
noncomputable def levySeriesTerm (μ : Measure E) (α : ℝ) (ℓ : E →L[ℝ] ℝ) (p : ℕ) : ℝ :=
  α / (((2 * p + 2 : ℕ) : ℝ) - α)
    * (∫ y in ball (0 : E) 1, (ℓ y) ^ (2 * p + 2) ∂μ) / ((2 * p + 2).factorial : ℝ)

theorem levySeriesTerm_nonneg (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ} (hα : 0 < α)
    (hα2 : α < 2) (ℓ : E →L[ℝ] ℝ) (p : ℕ) : 0 ≤ levySeriesTerm (E := E) μ α ℓ p := by
  have hNpos : (0 : ℝ) < ((2 * p + 2 : ℕ) : ℝ) - α := by
    have h2 : (2 : ℝ) ≤ ((2 * p + 2 : ℕ) : ℝ) := by
      have : (2 : ℕ) ≤ 2 * p + 2 := by omega
      exact_mod_cast this
    linarith
  unfold levySeriesTerm
  have h1 : (0 : ℝ) ≤ α / (((2 * p + 2 : ℕ) : ℝ) - α) := div_nonneg hα.le hNpos.le
  have h2 : (0 : ℝ) ≤ ∫ y in ball (0 : E) 1, (ℓ y) ^ (2 * p + 2) ∂μ :=
    integral_nonneg fun y => pow_of_two_dvd_nonneg (x := ℓ y) ⟨p + 1, by ring⟩
  have h3 : (0 : ℝ) < ((2 * p + 2).factorial : ℝ) := factorial_cast_pos _
  exact div_nonneg (mul_nonneg h1 h2) h3.le

/-- **The Taylor/Fubini identity** (the display following (I.5.17) in the paper):
`∫ (cosh (ℓ x) - 1) dΠ₁ = ∑_{p ≥ 0} α ∫_{B₁} (ℓ y)^{2p+2} dy / ((2p+2)! (2p+2-α))`. -/
theorem lintegral_cosh_sub_one_PiOne (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ} (hα : 0 < α)
    (hα2 : α < 2) (ℓ : E →L[ℝ] ℝ) :
    ∫⁻ x, ENNReal.ofReal (Real.cosh (ℓ x) - 1) ∂(PiOne α μ)
      = ∑' p : ℕ, ENNReal.ofReal (levySeriesTerm (E := E) μ α ℓ p) := by
  classical
  have hpt : ∀ x : E, ENNReal.ofReal (Real.cosh (ℓ x) - 1)
      = ∑' p : ℕ, ENNReal.ofReal ((ℓ x) ^ (2 * p + 2) / ((2 * p + 2).factorial : ℝ)) := by
    intro x
    have hsum : Summable fun p : ℕ =>
        (ℓ x) ^ (2 * p + 2) / ((2 * p + 2).factorial : ℝ) := by
      have h := (summable_nat_add_iff 1).2 (Real.hasSum_cosh (ℓ x)).summable
      refine h.congr fun p => ?_
      rw [Nat.mul_succ]
    rw [cosh_sub_one_eq_tsum, ENNReal.ofReal_tsum_of_nonneg (fun p => div_nonneg (pow_of_two_dvd_nonneg (x := ℓ x) ⟨p + 1, by ring⟩) (factorial_cast_pos _).le) hsum]
  rw [show (fun x : E => ENNReal.ofReal (Real.cosh (ℓ x) - 1))
      = (fun x : E => ∑' p : ℕ,
          ENNReal.ofReal ((ℓ x) ^ (2 * p + 2) / ((2 * p + 2).factorial : ℝ))) from funext hpt]
  rw [lintegral_tsum (fun p => by fun_prop)]
  refine tsum_congr fun p => ?_
  have hfac : (0 : ℝ) < 1 / ((2 * p + 2).factorial : ℝ) :=
    div_pos one_pos (factorial_cast_pos _)
  have h1 : ∫⁻ x, ENNReal.ofReal ((ℓ x) ^ (2 * p + 2) / ((2 * p + 2).factorial : ℝ))
        ∂(PiOne α μ)
      = ENNReal.ofReal (1 / ((2 * p + 2).factorial : ℝ))
        * ∫⁻ x, ENNReal.ofReal ((ℓ x) ^ (2 * p + 2)) ∂(PiOne α μ) := by
    have hpt : ∀ x : E, ENNReal.ofReal ((ℓ x) ^ (2 * p + 2) / ((2 * p + 2).factorial : ℝ))
        = ENNReal.ofReal (1 / ((2 * p + 2).factorial : ℝ))
          * ENNReal.ofReal ((ℓ x) ^ (2 * p + 2)) := by
      intro x
      have hrw : (ℓ x) ^ (2 * p + 2) / ((2 * p + 2).factorial : ℝ)
          = (1 / ((2 * p + 2).factorial : ℝ)) * (ℓ x) ^ (2 * p + 2) := by ring
      rw [hrw, ENNReal.ofReal_mul hfac.le]
    rw [show (fun x : E => ENNReal.ofReal ((ℓ x) ^ (2 * p + 2) / ((2 * p + 2).factorial : ℝ)))
        = (fun x : E => ENNReal.ofReal (1 / ((2 * p + 2).factorial : ℝ))
          * ENNReal.ofReal ((ℓ x) ^ (2 * p + 2))) from funext hpt]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have h2 : ∫⁻ x, ENNReal.ofReal ((ℓ x) ^ (2 * p + 2)) ∂(PiOne α μ)
      = ENNReal.ofReal (α / (((2 * p + 2 : ℕ) : ℝ) - α)
          * ∫ y in ball (0 : E) 1, (ℓ y) ^ (2 * p + 2) ∂μ) := by
    have hm := lintegral_moment_PiOne μ hα hα2 ℓ (p + 1) (by omega)
    simpa [Nat.mul_succ] using hm
  rw [h1, h2, ← ENNReal.ofReal_mul hfac.le]
  congr 1
  unfold levySeriesTerm
  ring

/-! ## The moment bound and summability of the series -/

/-- **The moment bound on the unit ball**: `∫_{B₁} (ℓ y)^N dy ≤ ‖ℓ‖^N |B₁|`. -/
theorem integral_pow_le_of_norm_le (μ : Measure E) [μ.IsAddHaarMeasure] (ℓ : E →L[ℝ] ℝ) {N : ℕ}
    (hN : 2 ∣ N) :
    ∫ y in ball (0 : E) 1, (ℓ y) ^ N ∂μ ≤ ‖ℓ‖ ^ N * (∫⁻ y in ball (0 : E) 1,
      (1 : ℝ≥0∞) ∂μ).toReal := by
  have hInt : IntegrableOn (fun y : E => (ℓ y) ^ N) (ball (0 : E) 1) μ := by
    have hcont : Continuous fun y : E => (ℓ y) ^ N := by fun_prop
    exact (hcont.continuousOn.integrableOn_compact (isCompact_closedBall 0 1)).mono_set
      ball_subset_closedBall
  have hIntc : IntegrableOn (fun _ : E => ‖ℓ‖ ^ N) (ball (0 : E) 1) μ :=
    integrableOn_const measure_ball_lt_top.ne
  have hle : ∀ᵐ y ∂(μ.restrict (ball (0 : E) 1)), (ℓ y) ^ N ≤ ‖ℓ‖ ^ N := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    have hy1 : ‖y‖ < 1 := by simpa [mem_ball, dist_zero_right] using hy
    have h1 : ‖ℓ y‖ ≤ ‖ℓ‖ := by
      calc ‖ℓ y‖ ≤ ‖ℓ‖ * ‖y‖ := ℓ.le_opNorm y
        _ ≤ ‖ℓ‖ * 1 := by gcongr
        _ = ‖ℓ‖ := by rw [mul_one]
    have hnn : (0 : ℝ) ≤ (ℓ y) ^ N := pow_of_two_dvd_nonneg hN
    calc (ℓ y) ^ N = |(ℓ y) ^ N| := (abs_of_nonneg hnn).symm
      _ = ‖(ℓ y) ^ N‖ := (Real.norm_eq_abs _).symm
      _ = ‖ℓ y‖ ^ N := norm_pow _ _
      _ ≤ ‖ℓ‖ ^ N := pow_le_pow_left₀ (norm_nonneg _) h1 N
  have h := integral_mono_ae hInt hIntc hle
  rw [setIntegral_const, smul_eq_mul] at h
  have h2 : μ.real (ball (0 : E) 1) = (∫⁻ y in ball (0 : E) 1, (1 : ℝ≥0∞) ∂μ).toReal := by
    rw [setLIntegral_one, measureReal_def]
  rw [h2, mul_comm] at h
  exact h

/-- The majorant of the displacement series: termwise comparison with `‖ℓ‖^{2p+2}/(2p+2)!`. -/
theorem levySeriesTerm_le_majorant (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ} (hα : 0 < α)
    (hα2 : α < 2) (ℓ : E →L[ℝ] ℝ) (p : ℕ) :
    levySeriesTerm (E := E) μ α ℓ p
      ≤ (α / (2 - α) * (∫⁻ y in ball (0 : E) 1, (1 : ℝ≥0∞) ∂μ).toReal)
        * (‖ℓ‖ ^ (2 * p + 2) / ((2 * p + 2).factorial : ℝ)) := by
  have h2N : (2 : ℝ) ≤ ((2 * p + 2 : ℕ) : ℝ) := by
    have : (2 : ℕ) ≤ 2 * p + 2 := by omega
    exact_mod_cast this
  have hfac : (0 : ℝ) < ((2 * p + 2).factorial : ℝ) := factorial_cast_pos _
  have hratio : α / (((2 * p + 2 : ℕ) : ℝ) - α) ≤ α / (2 - α) :=
    div_le_div_of_nonneg_left hα.le (by linarith) (by linarith)
  have hI := integral_pow_le_of_norm_le (E := E) μ ℓ (N := 2 * p + 2) ⟨p + 1, by ring⟩
  have hInn : (0 : ℝ) ≤ ∫ y in ball (0 : E) 1, (ℓ y) ^ (2 * p + 2) ∂μ :=
    integral_nonneg fun y => pow_of_two_dvd_nonneg (x := ℓ y) ⟨p + 1, by ring⟩
  have hratio_nn : (0 : ℝ) ≤ α / (2 - α) := div_nonneg hα.le (by linarith)
  have hI' : α / (((2 * p + 2 : ℕ) : ℝ) - α)
        * (∫ y in ball (0 : E) 1, (ℓ y) ^ (2 * p + 2) ∂μ)
      ≤ α / (2 - α) * (‖ℓ‖ ^ (2 * p + 2)
        * (∫⁻ y in ball (0 : E) 1, (1 : ℝ≥0∞) ∂μ).toReal) :=
    mul_le_mul hratio hI hInn hratio_nn
  unfold levySeriesTerm
  calc α / (((2 * p + 2 : ℕ) : ℝ) - α)
        * (∫ y in ball (0 : E) 1, (ℓ y) ^ (2 * p + 2) ∂μ) / ((2 * p + 2).factorial : ℝ)
      ≤ (α / (2 - α) * (‖ℓ‖ ^ (2 * p + 2)
          * (∫⁻ y in ball (0 : E) 1, (1 : ℝ≥0∞) ∂μ).toReal)) / ((2 * p + 2).factorial : ℝ) :=
        div_le_div_of_nonneg_right hI' hfac.le
    _ = (α / (2 - α) * (∫⁻ y in ball (0 : E) 1, (1 : ℝ≥0∞) ∂μ).toReal)
          * (‖ℓ‖ ^ (2 * p + 2) / ((2 * p + 2).factorial : ℝ)) := by ring

/-- The majorant series is summable (it is a shifted `cosh` series). -/
theorem summable_levyMajorant (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ} (hα : 0 < α)
    (hα2 : α < 2) (ℓ : E →L[ℝ] ℝ) :
    Summable (fun p : ℕ => (α / (2 - α) * (∫⁻ y in ball (0 : E) 1, (1 : ℝ≥0∞) ∂μ).toReal)
      * (‖ℓ‖ ^ (2 * p + 2) / ((2 * p + 2).factorial : ℝ))) := by
  have hcosh : Summable (fun n : ℕ => ‖ℓ‖ ^ (2 * n) / ((2 * n).factorial : ℝ)) :=
    (Real.hasSum_cosh ‖ℓ‖).summable
  have hshift : Summable (fun p : ℕ => ‖ℓ‖ ^ (2 * p + 2) / ((2 * p + 2).factorial : ℝ)) := by
    have h := (summable_nat_add_iff 1).2 hcosh
    refine h.congr fun p => ?_
    rw [Nat.mul_succ]
  exact hshift.mul_left _

/-- **Summability of the displacement series** — the paper's "all relevant sums converge". -/
theorem summable_levySeriesTerm (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ} (hα : 0 < α)
    (hα2 : α < 2) (ℓ : E →L[ℝ] ℝ) : Summable (levySeriesTerm (E := E) μ α ℓ) :=
  Summable.of_nonneg_of_le (levySeriesTerm_nonneg μ hα hα2 ℓ)
    (levySeriesTerm_le_majorant μ hα hα2 ℓ) (summable_levyMajorant μ hα hα2 ℓ)

/-- **Finiteness**: `∫ (cosh (ℓ x) - 1) dΠ₁ ≠ ∞`, i.e. the exponent of the limiting displacement
law is finite for every `ℓ`. -/
theorem lintegral_cosh_sub_one_PiOne_ne_top (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ}
    (hα : 0 < α) (hα2 : α < 2) (ℓ : E →L[ℝ] ℝ) :
    ∫⁻ x, ENNReal.ofReal (Real.cosh (ℓ x) - 1) ∂(PiOne α μ) ≠ ⊤ := by
  have hmaj := summable_levyMajorant (E := E) μ hα hα2 ℓ
  have hbnd : ∑' p : ℕ, ENNReal.ofReal (levySeriesTerm (E := E) μ α ℓ p)
      ≤ ENNReal.ofReal (∑' p : ℕ, (α / (2 - α)
          * (∫⁻ y in ball (0 : E) 1, (1 : ℝ≥0∞) ∂μ).toReal)
          * (‖ℓ‖ ^ (2 * p + 2) / ((2 * p + 2).factorial : ℝ))) := by
    calc ∑' p : ℕ, ENNReal.ofReal (levySeriesTerm (E := E) μ α ℓ p)
        ≤ ∑' p : ℕ, ENNReal.ofReal ((α / (2 - α)
            * (∫⁻ y in ball (0 : E) 1, (1 : ℝ≥0∞) ∂μ).toReal)
            * (‖ℓ‖ ^ (2 * p + 2) / ((2 * p + 2).factorial : ℝ))) :=
          ENNReal.tsum_le_tsum fun p => ENNReal.ofReal_le_ofReal
            (levySeriesTerm_le_majorant μ hα hα2 ℓ p)
      _ = ENNReal.ofReal (∑' p : ℕ, (α / (2 - α)
            * (∫⁻ y in ball (0 : E) 1, (1 : ℝ≥0∞) ∂μ).toReal)
            * (‖ℓ‖ ^ (2 * p + 2) / ((2 * p + 2).factorial : ℝ))) := by
          rw [ENNReal.ofReal_tsum_of_nonneg (fun p => by positivity) hmaj]
  rw [lintegral_cosh_sub_one_PiOne μ hα hα2 ℓ]
  exact ne_of_lt (lt_of_le_of_lt hbnd ENNReal.ofReal_lt_top)



/-! ## The exponent is bounded by a shifted `cosh` and is `< 1` near the origin -/

/-- **The exponent bound**: `∫ (cosh (ℓ x) - 1) dΠ₁ ≤ (α/(2-α)) |B_1| (cosh ‖ℓ‖ - 1)`. -/
theorem lintegral_cosh_sub_one_PiOne_le (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ}
    (hα : 0 < α) (hα2 : α < 2) (ℓ : E →L[ℝ] ℝ) :
    ∫⁻ x, ENNReal.ofReal (Real.cosh (ℓ x) - 1) ∂(PiOne α μ)
      ≤ ENNReal.ofReal (α / (2 - α) * (∫⁻ y in ball (0 : E) 1, (1 : ℝ≥0∞) ∂μ).toReal
          * (Real.cosh ‖ℓ‖ - 1)) := by
  have hmaj := summable_levyMajorant (E := E) μ hα hα2 ℓ
  have hnn : ∀ p : ℕ, (0 : ℝ) ≤ (α / (2 - α)
      * (∫⁻ y in ball (0 : E) 1, (1 : ℝ≥0∞) ∂μ).toReal)
      * (‖ℓ‖ ^ (2 * p + 2) / ((2 * p + 2).factorial : ℝ)) := by
    intro p
    have h1 : (0 : ℝ) ≤ α / (2 - α) := div_nonneg hα.le (by linarith)
    have h2 : (0 : ℝ) ≤ (∫⁻ y in ball (0 : E) 1, (1 : ℝ≥0∞) ∂μ).toReal := ENNReal.toReal_nonneg
    have h3 : (0 : ℝ) ≤ ‖ℓ‖ ^ (2 * p + 2) := pow_of_two_dvd_nonneg ⟨p + 1, by ring⟩
    exact mul_nonneg (mul_nonneg h1 h2) (div_nonneg h3 (factorial_cast_pos _).le)
  rw [lintegral_cosh_sub_one_PiOne μ hα hα2 ℓ]
  calc ∑' p : ℕ, ENNReal.ofReal (levySeriesTerm (E := E) μ α ℓ p)
      ≤ ∑' p : ℕ, ENNReal.ofReal ((α / (2 - α)
          * (∫⁻ y in ball (0 : E) 1, (1 : ℝ≥0∞) ∂μ).toReal)
          * (‖ℓ‖ ^ (2 * p + 2) / ((2 * p + 2).factorial : ℝ))) :=
        ENNReal.tsum_le_tsum fun p =>
          ENNReal.ofReal_le_ofReal (levySeriesTerm_le_majorant μ hα hα2 ℓ p)
    _ = ENNReal.ofReal (∑' p : ℕ, (α / (2 - α)
          * (∫⁻ y in ball (0 : E) 1, (1 : ℝ≥0∞) ∂μ).toReal)
          * (‖ℓ‖ ^ (2 * p + 2) / ((2 * p + 2).factorial : ℝ))) := by
        rw [ENNReal.ofReal_tsum_of_nonneg hnn hmaj]
    _ = ENNReal.ofReal (α / (2 - α) * (∫⁻ y in ball (0 : E) 1, (1 : ℝ≥0∞) ∂μ).toReal
          * (Real.cosh ‖ℓ‖ - 1)) := by
        congr 1
        rw [tsum_mul_left, cosh_sub_one_eq_tsum]

/-- **The paper's "open neighbourhood of the origin"**: for small enough `ℓ` the exponent
`∫ (cosh (ℓ x) - 1) dΠ₁` is `< 1`, so the reciprocal appearing in (I.5.17) is a well-defined
positive real number. -/
theorem exists_norm_lt_lintegral_cosh_sub_one_lt_one (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ}
    (hα : 0 < α) (hα2 : α < 2) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ℓ : E →L[ℝ] ℝ, ‖ℓ‖ < δ →
      ∫⁻ x, ENNReal.ofReal (Real.cosh (ℓ x) - 1) ∂(PiOne α μ) < 1 := by
  have hK : (0 : ℝ) ≤ α / (2 - α) * (∫⁻ y in ball (0 : E) 1, (1 : ℝ≥0∞) ∂μ).toReal :=
    mul_nonneg (div_nonneg hα.le (by linarith)) ENNReal.toReal_nonneg
  have hcont : Tendsto (fun c : ℝ => Real.cosh c - 1) (𝓝 0) (𝓝 0) := by
    have h1 : Tendsto (fun c : ℝ => Real.cosh c - 1) (𝓝 (0 : ℝ)) (𝓝 (Real.cosh 0 - 1)) :=
      Real.continuous_cosh.continuousAt.sub_const 1
    simpa using h1
  have h2 : Tendsto (fun c : ℝ => α / (2 - α)
      * (∫⁻ y in ball (0 : E) 1, (1 : ℝ≥0∞) ∂μ).toReal * (Real.cosh c - 1))
      (𝓝 0) (𝓝 0) := by
    have := hcont.const_mul (α / (2 - α) * (∫⁻ y in ball (0 : E) 1, (1 : ℝ≥0∞) ∂μ).toReal)
    simpa using this
  have hev : ∀ᶠ c : ℝ in 𝓝 0, α / (2 - α)
      * (∫⁻ y in ball (0 : E) 1, (1 : ℝ≥0∞) ∂μ).toReal * (Real.cosh c - 1) < 1 := by
    have := h2.eventually_lt_const one_pos
    simpa using this
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  refine ⟨δ, hδ, fun ℓ hℓ => ?_⟩
  have hb := lintegral_cosh_sub_one_PiOne_le μ hα hα2 ℓ
  have hsmall : α / (2 - α) * (∫⁻ y in ball (0 : E) 1, (1 : ℝ≥0∞) ∂μ).toReal
      * (Real.cosh ‖ℓ‖ - 1) < 1 := by
    apply hball
    simpa [Real.dist_eq] using hℓ
  have hnn : (0 : ℝ) ≤ α / (2 - α) * (∫⁻ y in ball (0 : E) 1, (1 : ℝ≥0∞) ∂μ).toReal
      * (Real.cosh ‖ℓ‖ - 1) := by
    refine mul_nonneg hK ?_
    have := Real.one_le_cosh ‖ℓ‖
    linarith
  calc ∫⁻ x, ENNReal.ofReal (Real.cosh (ℓ x) - 1) ∂(PiOne α μ)
      ≤ ENNReal.ofReal (α / (2 - α) * (∫⁻ y in ball (0 : E) 1, (1 : ℝ≥0∞) ∂μ).toReal
          * (Real.cosh ‖ℓ‖ - 1)) := hb
    _ < 1 := ENNReal.ofReal_lt_one.mpr hsmall

end PercLib.CriticalLRP.LevyAnalysis
