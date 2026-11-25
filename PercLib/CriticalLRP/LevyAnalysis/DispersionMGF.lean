/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Formalization derived from T. Hutchcroft, "Critical long-range percolation I: High effective
dimension", arXiv:2508.18807v1, Section I.5.2, Definition I.5.16 and display (I.5.17).

# The moment generating function of the exponential-time stopped displacement law

The paper's display (I.5.17) is the identity

  `E[e^{⟨L_T,u⟩}] = (1 - ∫ (cosh ⟨u,x⟩ - 1) dΠ₁(x))⁻¹`

for `u` in an open neighbourhood of the origin, where `(L_t)` is the symmetric Lévy jump process
with Lévy measure `Π₁` of (I.5.16) and `T` an independent rate-1 exponential time.  The companion
file `Dispersion.lean` constructs the *law* of `L_T` (as `expGeom` of the truncations of `Π₁`) and
identifies its characteristic function; this file proves the moment generating function identity.

Two things are done, and they are separated.

* The *finite-measure* case (`integral_exp_expGeom`): for a finite symmetric measure `ρ` on `E`
  the compound geometric law `expGeom ρ` has

    `∫ x, e^{⟨x,u⟩} d(expGeom ρ) = (1 - ∫ x, (cosh ⟨x,u⟩ - 1) dρ)⁻¹`

  whenever the `cosh`-integral is `< 1`.  This is an exact computation: the exponential series of
  `convPow` converges absolutely because `ρ` is finite, and the geometric series is summed
  explicitly.  No approximation is involved.

* The *displacement law* (`integral_exp_nuDisp`): for `0 < α < 2` and **any** probability measure
  `ν` whose characteristic function is `u ↦ (1 + ∫ (1 - cos ⟨x,u⟩) dΠ₁)⁻¹` -- by
  `exists_exp_stop_symm` such a `ν` exists and by `eq_of_charFun_levy` it is unique, so this is
  Definition I.5.16 -- the identity (I.5.17) holds for every `u` with
  `∫ (cosh ⟨x,u⟩ - 1) dΠ₁ < 1`:

    `∫ x, e^{⟨x,u⟩} dν = (1 - ∫ x, (cosh ⟨x,u⟩ - 1) dΠ₁)⁻¹`.

  Here `Π₁` is *not* finite (its density behaves like `‖x‖^{-d-α}` at the origin), so this is
  genuinely a limit statement.  The proof is: `ν` is the weak limit of the laws
  `expGeom (Π₁ ↾ {‖x‖ > 1/(n+1)})` by Lévy's continuity theorem, each of which has the exact
  finite-measure MGF above; the `cosh` integrals increase to the `Π₁`-integral by monotone
  convergence; and a uniform-integrability argument (exponent `1 + δ` for a suitable `δ > 0`,
  made possible by the continuity of `s ↦ ∫ (cosh ⟨x,su⟩ - 1) dΠ₁` at `s = 1`) upgrades the
  weak convergence to convergence of the (unbounded) exponential moments.

Nothing here assumes the existence of a Lévy process: the stopped law is the explicit weak limit
of compound geometric laws.  `Π₁` has the closed form `dΠ₁/dx = α/(d+α) (‖x‖^{-d-α} - 1)` on the
unit ball, so all integrals are explicit.
-/
module

public import PercLib.CriticalLRP.LevyAnalysis.Dispersion

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal Topology Pointwise BigOperators

namespace PercLib.CriticalLRP.LevyAnalysis

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-! ## Elementary `sinh`/`cosh` bounds -/

theorem abs_sinh_le_cosh (t : ℝ) : |Real.sinh t| ≤ Real.cosh t := by
  rw [abs_le]
  constructor
  · have h := Real.sinh_add_cosh t
    have h2 := Real.exp_pos t
    linarith
  · have h := Real.cosh_sub_sinh t
    have h2 := Real.exp_pos (-t)
    linarith

theorem cosh_sub_one_nonneg' (t : ℝ) : 0 ≤ Real.cosh t - 1 := by
  linarith [Real.one_le_cosh t]

/-- `cosh t - 1 ≤ t ^ 2 * exp |t|` -- the second-order Taylor bound used to dominate the
`cosh` integrand by `‖x‖ ^ 2` on the unit ball. -/
theorem cosh_sub_one_le_sq_mul_exp (t : ℝ) : Real.cosh t - 1 ≤ t ^ 2 * Real.exp |t| := by
  have h1 := abs_exp_sub_one_sub_id_le_exp t
  have h2 := abs_exp_sub_one_sub_id_le_exp (-t)
  rw [abs_neg] at h2
  have hEq : Real.cosh t - 1
      = ((Real.exp t - 1 - t) + (Real.exp (-t) - 1 - (-t))) / 2 := by
    rw [Real.cosh_eq]
    field_simp
    ring
  have hle1 : Real.exp t - 1 - t ≤ |Real.exp t - 1 - t| := le_abs_self _
  have hle2 : Real.exp (-t) - 1 - (-t) ≤ |Real.exp (-t) - 1 - (-t)| := le_abs_self _
  have hnn : (0 : ℝ) ≤ t ^ 2 * Real.exp |t| := by positivity
  have h3 : |Real.exp (-t) - 1 - (-t)| ≤ (-t) ^ 2 * Real.exp |t| := by
    simpa using h2
  have h4 : |Real.exp t - 1 - t| ≤ t ^ 2 * Real.exp |t| := h1
  have h5 : ((Real.exp t - 1 - t) + (Real.exp (-t) - 1 - (-t))) / 2
      ≤ t ^ 2 * Real.exp |t| := by
    have h6 : (Real.exp t - 1 - t) + (Real.exp (-t) - 1 - (-t))
        ≤ t ^ 2 * Real.exp |t| + t ^ 2 * Real.exp |t| := by
      have h7 : (-t) ^ 2 = t ^ 2 := by ring
      linarith
    linarith
  linarith [hEq ▸ h5]

/-! ## The `cosh` exponent

`levyCoshExp Π u = ∫⁻ (cosh ⟨x,u⟩ - 1) dΠ` is the `ℝ≥0∞`-valued exponential exponent; it is
finite for `Π₁` and every `u` (`levyCoshExp_PiOne_ne_top`).  `levyCoshPsi` is its real value. -/

/-- The `cosh` (moment generating) exponent in lower-integral form. -/
noncomputable def levyCoshExp (Pi : Measure E) (u : E) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (Real.cosh (inner ℝ x u) - 1) ∂Pi

/-- The `cosh` (moment generating) exponent. -/
noncomputable def levyCoshPsi (Pi : Measure E) (u : E) : ℝ := (levyCoshExp Pi u).toReal

theorem measurable_cosh_inner_sub_one (u : E) :
    Measurable fun x : E => ENNReal.ofReal (Real.cosh (inner ℝ x u) - 1) := by
  fun_prop

theorem levyCoshExp_mono {Pi Pi' : Measure E} (h : Pi ≤ Pi') (u : E) :
    levyCoshExp Pi u ≤ levyCoshExp Pi' u :=
  lintegral_mono' h (fun _ => le_refl _)

theorem levyCoshPsi_nonneg (Pi : Measure E) (u : E) : 0 ≤ levyCoshPsi Pi u :=
  ENNReal.toReal_nonneg

theorem levyCoshPsi_zero (Pi : Measure E) : levyCoshPsi Pi 0 = 0 := by
  simp [levyCoshPsi, levyCoshExp]

/-- For a measure under which `x ↦ cosh ⟨x,u⟩` is integrable, the `ℝ≥0∞`-exponent is the
`ofReal` of the Bochner integral. -/
theorem levyCoshExp_eq_ofReal_integral (Pi : Measure E) (u : E)
    (h : Integrable (fun x : E => Real.cosh (inner ℝ x u) - 1) Pi) :
    levyCoshExp Pi u
      = ENNReal.ofReal (∫ x, (Real.cosh (inner ℝ x u) - 1) ∂Pi) := by
  rw [levyCoshExp, ← ofReal_integral_eq_lintegral_ofReal h
    (Eventually.of_forall fun x => cosh_sub_one_nonneg' _)]

/-! ## The base integral `∫⁻ e^{⟨x,u⟩} dρ` for a finite symmetric `ρ` -/

/-- **The base computation.**  For a finite symmetric measure `ρ` and `u` with
`x ↦ cosh ⟨x,u⟩` integrable,
`∫⁻ e^{⟨x,u⟩} dρ = ρ(E) + ∫ (cosh ⟨x,u⟩ - 1) dρ`;
the `sinh` part vanishes by symmetry, and the `cosh` part is `1 + (cosh - 1)`. -/
theorem lintegral_exp_of_symm (ρ : Measure E) [IsFiniteMeasure ρ]
    (hρ : Measure.map (fun x : E => -x) ρ = ρ) (u : E)
    (hcosh : Integrable (fun x : E => Real.cosh (inner ℝ x u)) ρ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (inner ℝ x u)) ∂ρ
      = ENNReal.ofReal (ρ.real univ + ∫ x, (Real.cosh (inner ℝ x u) - 1) ∂ρ) := by
  have hsinh : Integrable (fun x : E => Real.sinh (inner ℝ x u)) ρ := by
    refine hcosh.mono' (by fun_prop) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs]
    exact abs_sinh_le_cosh _
  have hsinh_zero : ∫ x, Real.sinh (inner ℝ x u) ∂ρ = 0 := by
    refine integral_eq_zero_of_odd_of_map_neg_eq_self hρ hsinh (fun x => ?_)
    rw [inner_neg_left, Real.sinh_neg]
  have hone : ∫ x, (1 : ℝ) ∂ρ = ρ.real univ := by
    rw [integral_const, smul_eq_mul, mul_one]
  have hcosh_sub : Integrable (fun x : E => Real.cosh (inner ℝ x u) - 1) ρ :=
    hcosh.sub (integrable_const 1)
  have hcosh_eq : ∫ x, Real.cosh (inner ℝ x u) ∂ρ
      = ∫ x, (Real.cosh (inner ℝ x u) - 1) ∂ρ + ρ.real univ := by
    have h := integral_add hcosh_sub
      (integrable_const (1 : ℝ) : Integrable (fun _ : E => (1 : ℝ)) ρ)
    rw [hone] at h
    rw [← h]
    exact integral_congr_ae (Eventually.of_forall fun x => by ring)
  have hexp_eq : ∫ x, Real.exp (inner ℝ x u) ∂ρ
      = ρ.real univ + ∫ x, (Real.cosh (inner ℝ x u) - 1) ∂ρ := by
    have h1 : (fun x : E => Real.exp (inner ℝ x u))
        = fun x => Real.cosh (inner ℝ x u) + Real.sinh (inner ℝ x u) := by
      funext x
      exact (Real.cosh_add_sinh _).symm
    rw [h1, integral_add hcosh hsinh, hsinh_zero, add_zero, hcosh_eq, add_comm]
  have hexp_int : Integrable (fun x : E => Real.exp (inner ℝ x u)) ρ := by
    have h := hcosh.add hsinh
    refine h.congr (Eventually.of_forall fun x => ?_)
    show Real.cosh (inner ℝ x u) + Real.sinh (inner ℝ x u) = Real.exp (inner ℝ x u)
    exact Real.cosh_add_sinh _
  rw [← ofReal_integral_eq_lintegral_ofReal hexp_int
    (Eventually.of_forall fun x => (Real.exp_pos _).le), hexp_eq]

/-! ## Convolution powers -/

/-- The exponential moment of a convolution power is the power of the exponential moment. -/
theorem lintegral_exp_convPow (ρ : Measure E) [IsFiniteMeasure ρ] (u : E) :
    ∀ k : ℕ, ∫⁻ x, ENNReal.ofReal (Real.exp (inner ℝ x u)) ∂(convPow ρ k)
      = (∫⁻ x, ENNReal.ofReal (Real.exp (inner ℝ x u)) ∂ρ) ^ k := by
  intro k
  induction k with
  | zero =>
      rw [show convPow ρ 0 = Measure.dirac (0 : E) from rfl]
      simp [Real.exp_zero]
  | succ k ih =>
      have := instIsFiniteMeasureConvPow ρ k
      rw [convPow, addConv]
      rw [lintegral_map (f := fun x : E => ENNReal.ofReal (Real.exp (inner ℝ x u)))
        (g := fun p : E × E => p.1 + p.2) (by fun_prop) measurable_add]
      have hpt : ∀ p : E × E, ENNReal.ofReal (Real.exp (inner ℝ (p.1 + p.2) u))
          = ENNReal.ofReal (Real.exp (inner ℝ p.1 u))
            * ENNReal.ofReal (Real.exp (inner ℝ p.2 u)) := by
        intro p
        rw [inner_add_left, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
      simp_rw [hpt]
      rw [lintegral_prod_mul
        (f := fun x : E => ENNReal.ofReal (Real.exp (inner ℝ x u)))
        (g := fun y : E => ENNReal.ofReal (Real.exp (inner ℝ y u)))
        (by fun_prop) (by fun_prop), ih, pow_succ]

/-! ## The compound geometric law -/

/-- **The exact MGF of the compound geometric law** (lower-integral form).  For a finite symmetric
`ρ`, if `∫ (cosh ⟨x,u⟩ - 1) dρ < 1` then the exponential moment of `expGeom ρ` is
`(1 - ∫ (cosh ⟨x,u⟩ - 1) dρ)⁻¹`. -/
theorem lintegral_exp_expGeom (ρ : Measure E) [IsFiniteMeasure ρ]
    (hρ : Measure.map (fun x : E => -x) ρ = ρ) (u : E)
    (hcosh : Integrable (fun x : E => Real.cosh (inner ℝ x u)) ρ)
    (hψ : ∫ x, (Real.cosh (inner ℝ x u) - 1) ∂ρ < 1) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (inner ℝ x u)) ∂(expGeom ρ)
      = ENNReal.ofReal ((1 - ∫ x, (Real.cosh (inner ℝ x u) - 1) ∂ρ)⁻¹) := by
  set Λ : ℝ := ρ.real univ with hΛ
  set ψ : ℝ := ∫ x, (Real.cosh (inner ℝ x u) - 1) ∂ρ with hψdef
  set c : ℝ := (1 + Λ)⁻¹ with hc
  have hΛnn : 0 ≤ Λ := ENNReal.toReal_nonneg
  have hψnn : 0 ≤ ψ := integral_nonneg fun x => cosh_sub_one_nonneg' _
  have hΛψ_nn : 0 ≤ Λ + ψ := by linarith
  have hcpos : 0 < c := by rw [hc]; positivity
  have hcΛ : c * Λ = 1 - c := by
    rw [hc]; field_simp; ring
  have hratio : c * (Λ + ψ) < 1 := by nlinarith
  have hbase := lintegral_exp_of_symm ρ hρ u hcosh
  have hmeasm : Measurable fun x : E => ENNReal.ofReal (Real.exp (inner ℝ x u)) := by fun_prop
  -- the geometric sum
  have hsumm : Summable fun k : ℕ => c ^ (k + 1) * (Λ + ψ) ^ k := by
    have h1 : Summable fun k : ℕ => c * (c * (Λ + ψ)) ^ k :=
      Summable.mul_left _ (summable_geometric_of_norm_lt_one
        (by rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hratio))
    refine h1.congr fun k => ?_
    rw [mul_pow, pow_succ]
    ring
  have hgeom : ∑' k : ℕ, c ^ (k + 1) * (Λ + ψ) ^ k = (1 - ψ)⁻¹ := by
    have h1 : ∀ k : ℕ, c ^ (k + 1) * (Λ + ψ) ^ k = c * (c * (Λ + ψ)) ^ k := by
      intro k
      rw [mul_pow, pow_succ]
      ring
    simp_rw [h1]
    rw [tsum_mul_left,
      tsum_geometric_of_norm_lt_one
        (by rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]; exact hratio)]
    have hden : 1 - c * (Λ + ψ) = c * (1 - ψ) := by
      rw [hc]; field_simp; ring
    rw [hden, mul_inv, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hcpos), one_mul]
  -- termwise evaluation
  have hterm : ∀ k : ℕ,
      ∫⁻ x, ENNReal.ofReal (Real.exp (inner ℝ x u))
        ∂(ENNReal.ofReal (c ^ (k + 1)) • convPow ρ k)
        = ENNReal.ofReal (c ^ (k + 1) * (Λ + ψ) ^ k) := by
    intro k
    rw [lintegral_smul_measure, lintegral_exp_convPow, hbase, smul_eq_mul]
    have hΛψ : ρ.real univ + ∫ x, (Real.cosh (inner ℝ x u) - 1) ∂ρ = Λ + ψ := by
      rw [hΛ, hψdef]
    rw [hΛψ, ← ENNReal.ofReal_pow hΛψ_nn]
    exact (ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ c ^ (k + 1))).symm
  rw [expGeom, lintegral_sum_measure]
  rw [show (∑' k, ∫⁻ x, ENNReal.ofReal (Real.exp (inner ℝ x u))
        ∂(ENNReal.ofReal (c ^ (k + 1)) • convPow ρ k))
      = ∑' k, ENNReal.ofReal (c ^ (k + 1) * (Λ + ψ) ^ k) from tsum_congr hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (f := fun k : ℕ => c ^ (k + 1) * (Λ + ψ) ^ k) (fun k => by positivity) hsumm, hgeom]

/-- **The exact MGF of the compound geometric law**: the Bochner-integral form of
`lintegral_exp_expGeom`. -/
theorem integral_exp_expGeom (ρ : Measure E) [IsFiniteMeasure ρ]
    (hρ : Measure.map (fun x : E => -x) ρ = ρ) (u : E)
    (hcosh : Integrable (fun x : E => Real.cosh (inner ℝ x u)) ρ)
    (hψ : ∫ x, (Real.cosh (inner ℝ x u) - 1) ∂ρ < 1) :
    ∫ x, Real.exp (inner ℝ x u) ∂(expGeom ρ)
      = (1 - ∫ x, (Real.cosh (inner ℝ x u) - 1) ∂ρ)⁻¹ := by
  have h := lintegral_exp_expGeom ρ hρ u hcosh hψ
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => (Real.exp_pos _).le)
    (by fun_prop), h, ENNReal.toReal_ofReal (by
      have : (0:ℝ) < 1 - ∫ x, (Real.cosh (inner ℝ x u) - 1) ∂ρ := by linarith
      positivity)]

/-! ## The truncations of `Π₁` and their compound geometric laws

`truncRho μ α n = Π₁ ↾ {‖x‖ > 1/(n+1)}` is a finite symmetric measure, and `truncRho μ α n ↑ Π₁`.
The compound geometric laws `expGeom (truncRho μ α n)` are the laws whose characteristic functions
converge to `u ↦ (1 + ψ(u))⁻¹`; by Lévy's continuity theorem they converge weakly to the
displacement law. -/

/-- The truncated Lévy measures `Π₁ ↾ {‖x‖ > 1/(n+1)}`. -/
noncomputable def truncRho (μ : Measure E) (α : ℝ) (n : ℕ) : Measure E :=
  (PiOne α μ).restrict (truncSet n)

theorem truncRho_univ_lt_top (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ} (hα : 0 < α)
    (hα2 : α < 2) (n : ℕ) : truncRho μ α n univ < ⊤ := by
  rw [truncRho, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  exact lt_top_iff_ne_top.mpr (truncSet_ne_top (PiOne α μ) (PiOne_levy_measure μ hα hα2) n)

theorem truncRho_symm (μ : Measure E) [μ.IsAddHaarMeasure] (α : ℝ) (n : ℕ) :
    Measure.map (fun x : E => -x) (truncRho μ α n) = truncRho μ α n :=
  map_neg_restrict_of_invariant (PiOne α μ) (PiOne_symm μ α) (measurableSet_truncSet n)
    (truncSet_neg n)

/-- The `cosh` integrand against `Π₁` is integrable. -/
theorem integrable_cosh_sub_one_PiOne_inner (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ}
    (hα : 0 < α) (hα2 : α < 2) (u : E) :
    Integrable (fun x : E => Real.cosh (inner ℝ x u) - 1) (PiOne α μ) := by
  have h := integrable_cosh_sub_one_PiOne μ hα hα2 (innerSL ℝ u)
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp [innerSL_apply_apply, real_inner_comm]

/-- The exponent `∫ (cosh ⟨x,u⟩ - 1) dΠ₁` is finite for every `u`. -/
theorem levyCoshExp_PiOne_ne_top (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ} (hα : 0 < α)
    (hα2 : α < 2) (u : E) : levyCoshExp (PiOne α μ) u ≠ ⊤ := by
  rw [levyCoshExp_eq_ofReal_integral _ _ (integrable_cosh_sub_one_PiOne_inner μ hα hα2 u)]
  exact ENNReal.ofReal_ne_top

/-- `levyCoshPsi` of `Π₁` is the Bochner integral. -/
theorem levyCoshPsi_PiOne_eq_integral (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ}
    (hα : 0 < α) (hα2 : α < 2) (u : E) :
    levyCoshPsi (PiOne α μ) u = ∫ x, (Real.cosh (inner ℝ x u) - 1) ∂(PiOne α μ) := by
  rw [levyCoshPsi, levyCoshExp_eq_ofReal_integral _ _
    (integrable_cosh_sub_one_PiOne_inner μ hα hα2 u), ENNReal.toReal_ofReal]
  exact integral_nonneg fun x => cosh_sub_one_nonneg' _

/-- The `cosh ⟨·,u⟩` integrand is bounded on the unit ball, hence integrable against a truncated
measure. -/
theorem integrable_cosh_truncRho (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ} (hα : 0 < α)
    (hα2 : α < 2) (n : ℕ) (u : E) :
    Integrable (fun x : E => Real.cosh (inner ℝ x u)) (truncRho μ α n) := by
  have : IsFiniteMeasure (truncRho μ α n) := ⟨truncRho_univ_lt_top μ hα hα2 n⟩
  refine Integrable.of_bound (by fun_prop) (Real.cosh ‖u‖) ?_
  filter_upwards [ae_mono Measure.restrict_le_self (PiOne_ae_norm_le_one μ hα)] with x hx
  rw [Real.norm_eq_abs]
  have hle : |inner ℝ x u| ≤ ‖u‖ := by
    calc |inner ℝ x u| ≤ ‖x‖ * ‖u‖ := abs_real_inner_le_norm x u
      _ ≤ 1 * ‖u‖ := by
          have hx1 : ‖x‖ ≤ 1 := by simpa [mem_closedBall, dist_zero_right] using hx
          exact mul_le_mul_of_nonneg_right hx1 (norm_nonneg u)
      _ = ‖u‖ := one_mul _
  have hcosh_nn : (0 : ℝ) ≤ Real.cosh (inner ℝ x u) :=
    le_trans zero_le_one (Real.one_le_cosh _)
  rw [abs_of_nonneg hcosh_nn]
  exact (Real.cosh_le_cosh).mpr (by simpa using hle)

/-- The `cosh - 1` integrand is integrable against a truncated measure. -/
theorem integrable_cosh_sub_one_truncRho (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ}
    (hα : 0 < α) (hα2 : α < 2) (n : ℕ) (u : E) :
    Integrable (fun x : E => Real.cosh (inner ℝ x u) - 1) (truncRho μ α n) := by
  have : IsFiniteMeasure (truncRho μ α n) := ⟨truncRho_univ_lt_top μ hα hα2 n⟩
  exact (integrable_cosh_truncRho μ hα hα2 n u).sub (integrable_const 1)

/-- `levyCoshPsi` of a truncation is the Bochner integral. -/
theorem levyCoshPsi_truncRho_eq_integral (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ}
    (hα : 0 < α) (hα2 : α < 2) (n : ℕ) (u : E) :
    levyCoshPsi (truncRho μ α n) u
      = ∫ x, (Real.cosh (inner ℝ x u) - 1) ∂(truncRho μ α n) := by
  rw [levyCoshPsi, levyCoshExp_eq_ofReal_integral _ _
    (integrable_cosh_sub_one_truncRho μ hα hα2 n u), ENNReal.toReal_ofReal]
  exact integral_nonneg fun x => cosh_sub_one_nonneg' _

/-- The exponents of the truncations are dominated by that of `Π₁`. -/
theorem levyCoshPsi_truncRho_le (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ} (hα : 0 < α)
    (hα2 : α < 2) (n : ℕ) (u : E) :
    levyCoshPsi (truncRho μ α n) u ≤ levyCoshPsi (PiOne α μ) u := by
  rw [levyCoshPsi_truncRho_eq_integral μ hα hα2 n u,
    levyCoshPsi_PiOne_eq_integral μ hα hα2 u]
  have h1 : ∫⁻ x, ENNReal.ofReal (Real.cosh (inner ℝ x u) - 1) ∂(truncRho μ α n)
      ≤ ∫⁻ x, ENNReal.ofReal (Real.cosh (inner ℝ x u) - 1) ∂(PiOne α μ) :=
    lintegral_mono' Measure.restrict_le_self (fun x => le_refl _)
  rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_cosh_sub_one_truncRho μ hα hα2 n u)
      (Eventually.of_forall fun x => cosh_sub_one_nonneg' _),
    ← ofReal_integral_eq_lintegral_ofReal
      (integrable_cosh_sub_one_PiOne_inner μ hα hα2 u)
      (Eventually.of_forall fun x => cosh_sub_one_nonneg' _)] at h1
  exact (ENNReal.ofReal_le_ofReal_iff
    (integral_nonneg fun x => cosh_sub_one_nonneg' _)).mp h1

/-- Monotone convergence of the `cosh` exponents of the truncations. -/
theorem tendsto_levyCoshExp_trunc (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ} (hα : 0 < α)
    (hα2 : α < 2) (u : E) :
    Tendsto (fun n => levyCoshExp (truncRho μ α n) u) atTop
      (𝓝 (levyCoshExp (PiOne α μ) u)) := by
  set g : E → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.cosh (inner ℝ x u) - 1) with hg
  have hgm : Measurable g := measurable_cosh_inner_sub_one u
  have hmono : Monotone fun n x => (truncSet n).indicator g x := by
    intro m n hmn x
    show (truncSet m).indicator g x ≤ (truncSet n).indicator g x
    by_cases hx : x ∈ truncSet m
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (monotone_truncSet hmn hx)]
    · rw [Set.indicator_of_notMem hx]; exact bot_le
  have hmono' : Monotone fun n : ℕ => ∫⁻ x, (truncSet n).indicator g x ∂(PiOne α μ) :=
    fun m n hmn => lintegral_mono (hmono hmn)
  have hmct := lintegral_iSup (μ := PiOne α μ)
    (f := fun n x => (truncSet n).indicator g x)
    (fun n => hgm.indicator (measurableSet_truncSet n)) hmono
  have hsup : (fun x : E => ⨆ n, (truncSet n).indicator g x) = g := by
    funext x
    rcases eq_or_ne x 0 with rfl | hx
    · have hg0 : g (0 : E) = 0 := by simp [hg, inner_zero_left]
      have h0 : ∀ n : ℕ, (truncSet n).indicator g (0 : E) = 0 := by
        intro n
        simp [hg0]
      simp [h0, hg0]
    · have hpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (K := ℝ) hpos
      have hmem : x ∈ truncSet n := by simpa [truncSet, truncRadius] using hn
      refine le_antisymm (iSup_le fun m => ?_) ?_
      · by_cases hm : x ∈ truncSet m
        · rw [Set.indicator_of_mem hm]
        · rw [Set.indicator_of_notMem hm]; exact bot_le
      · calc g x = (truncSet n).indicator g x := (Set.indicator_of_mem hmem g).symm
          _ ≤ ⨆ m, (truncSet m).indicator g x := le_iSup (fun m => (truncSet m).indicator g x) n
  have h2 : Tendsto (fun n : ℕ => ∫⁻ x, (truncSet n).indicator g x ∂(PiOne α μ)) atTop
      (𝓝 (levyCoshExp (PiOne α μ) u)) := by
    have h3 := tendsto_atTop_iSup hmono'
    rw [← hmct, hsup] at h3
    simpa [hg, levyCoshExp] using h3
  have hind : ∀ n, ∫⁻ x, (truncSet n).indicator g x ∂(PiOne α μ)
      = levyCoshExp (truncRho μ α n) u := by
    intro n
    rw [lintegral_indicator (measurableSet_truncSet n), truncRho, levyCoshExp]
  simpa only [hind] using h2

/-- Convergence of the real `cosh` exponents of the truncations. -/
theorem tendsto_levyCoshPsi_trunc (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ} (hα : 0 < α)
    (hα2 : α < 2) (u : E) :
    Tendsto (fun n => levyCoshPsi (truncRho μ α n) u) atTop
      (𝓝 (levyCoshPsi (PiOne α μ) u)) := by
  have h := tendsto_levyCoshExp_trunc μ hα hα2 u
  have hne : levyCoshExp (PiOne α μ) u ≠ ⊤ := levyCoshExp_PiOne_ne_top μ hα hα2 u
  have h' := (ENNReal.tendsto_toReal hne).comp h
  simp only [levyCoshPsi] at h' ⊢
  exact h'

/-! ## Continuity of the exponent along a ray

The set `{u : ∫ (cosh ⟨x,u⟩ - 1) dΠ₁ < 1}` is the domain of (I.5.17).  What is needed for the
uniform-integrability argument is only that `s ↦ ∫ (cosh ⟨x,su⟩ - 1) dΠ₁` is continuous at `s = 1`,
so that `∫ (cosh ⟨x,su⟩ - 1) dΠ₁ < 1` still holds for some `s > 1`. -/

theorem integrable_cosh_smul_inner_PiOne (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ}
    (hα : 0 < α) (hα2 : α < 2) (u : E) (s : ℝ) :
    Integrable (fun x : E => Real.cosh (s * (inner ℝ x u)) - 1) (PiOne α μ) := by
  refine Integrable.mono'
    ((integrable_norm_sq_PiOne μ hα hα2).const_mul
      (s ^ 2 * ‖u‖ ^ 2 * Real.exp (|s| * ‖u‖))) ?_ ?_
  · fun_prop
  · filter_upwards [PiOne_ae_norm_le_one μ hα] with x hx
    have hx1 : ‖x‖ ≤ 1 := by simpa [mem_closedBall, dist_zero_right] using hx
    have hinner : |inner ℝ x u| ≤ ‖u‖ := by
      calc |inner ℝ x u| ≤ ‖x‖ * ‖u‖ := abs_real_inner_le_norm x u
        _ ≤ 1 * ‖u‖ := mul_le_mul_of_nonneg_right hx1 (norm_nonneg u)
        _ = ‖u‖ := one_mul _
    have ht : |s * (inner ℝ x u)| ≤ |s| * ‖u‖ := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hinner (abs_nonneg s)
    have h1 : Real.cosh (s * (inner ℝ x u)) - 1
        ≤ (s * (inner ℝ x u)) ^ 2 * Real.exp |s * (inner ℝ x u)| :=
      cosh_sub_one_le_sq_mul_exp _
    have h2 : Real.exp |s * (inner ℝ x u)| ≤ Real.exp (|s| * ‖u‖) := Real.exp_le_exp.mpr ht
    have h3 : (s * (inner ℝ x u)) ^ 2 = s ^ 2 * (inner ℝ x u) ^ 2 := by ring
    have h4 : (inner ℝ x u) ^ 2 ≤ ‖x‖ ^ 2 * ‖u‖ ^ 2 := by
      have h := abs_real_inner_le_norm x u
      nlinarith [abs_nonneg (inner ℝ x u), norm_nonneg x, norm_nonneg u, sq_abs (inner ℝ x u)]
    have h5 : s ^ 2 * (inner ℝ x u) ^ 2 ≤ s ^ 2 * (‖x‖ ^ 2 * ‖u‖ ^ 2) := by
      have hs2 : (0:ℝ) ≤ s ^ 2 := sq_nonneg s
      nlinarith [h4]
    have hnn : (0 : ℝ) ≤ Real.cosh (s * (inner ℝ x u)) - 1 := cosh_sub_one_nonneg' _
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    calc Real.cosh (s * (inner ℝ x u)) - 1
        ≤ (s * (inner ℝ x u)) ^ 2 * Real.exp |s * (inner ℝ x u)| := h1
      _ ≤ (s ^ 2 * (‖x‖ ^ 2 * ‖u‖ ^ 2)) * Real.exp (|s| * ‖u‖) := by
          rw [h3]
          exact mul_le_mul h5 h2 (Real.exp_pos _).le (by positivity)
      _ = s ^ 2 * ‖u‖ ^ 2 * Real.exp (|s| * ‖u‖) * ‖x‖ ^ 2 := by ring


/-! ## Weak convergence of the compound geometric laws -/

/-- The compound geometric law of the `n`-th truncation, as a probability measure. -/
noncomputable def truncLaw (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ} (hα : 0 < α)
    (hα2 : α < 2) (n : ℕ) : ProbabilityMeasure E :=
  ⟨expGeom (truncRho μ α n), by
    have : IsFiniteMeasure (truncRho μ α n) := ⟨truncRho_univ_lt_top μ hα hα2 n⟩
    exact instIsProbabilityMeasureExpGeom (truncRho μ α n)⟩

theorem coe_truncLaw (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ} (hα : 0 < α)
    (hα2 : α < 2) (n : ℕ) : (truncLaw μ hα hα2 n : Measure E) = expGeom (truncRho μ α n) := rfl

/-- The characteristic functions of the compound geometric laws of the truncations converge to
`u ↦ (1 + ψ(u))⁻¹`. -/
theorem tendsto_charFun_expGeom_truncRho (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ}
    (hα : 0 < α) (hα2 : α < 2) (u : E) :
    Tendsto (fun n => charFun (expGeom (truncRho μ α n)) u) atTop
      (𝓝 (((1 + levyPsi (PiOne α μ) u : ℝ) : ℂ)⁻¹)) := by
  have h1 : ∀ n, charFun (expGeom (truncRho μ α n)) u
      = ((1 + levyPsi (truncRho μ α n) u : ℝ) : ℂ)⁻¹ := by
    intro n
    have : IsFiniteMeasure (truncRho μ α n) := ⟨truncRho_univ_lt_top μ hα hα2 n⟩
    exact charFun_expGeom (truncRho μ α n) (truncRho_symm μ α n) u
  simp only [h1]
  have h2 : Tendsto (fun n => levyPsi (truncRho μ α n) u) atTop (𝓝 (levyPsi (PiOne α μ) u)) :=
    tendsto_levyPsi_trunc (PiOne α μ) (PiOne_levy_measure μ hα hα2) u
  have h3 : Tendsto (fun n => (1 + levyPsi (truncRho μ α n) u : ℝ)) atTop
      (𝓝 (1 + levyPsi (PiOne α μ) u)) := tendsto_const_nhds.add h2
  have h4 : (1 + levyPsi (PiOne α μ) u : ℝ) ≠ 0 := by
    have := levyPsi_nonneg (PiOne α μ) u
    positivity
  have h5 : Tendsto (fun n => ((1 + levyPsi (truncRho μ α n) u : ℝ))⁻¹) atTop
      (𝓝 ((1 + levyPsi (PiOne α μ) u : ℝ)⁻¹)) := h3.inv₀ h4
  have h6 : Tendsto (fun n => (((1 + levyPsi (truncRho μ α n) u : ℝ)⁻¹ : ℝ) : ℂ)) atTop
      (𝓝 ((((1 + levyPsi (PiOne α μ) u : ℝ)⁻¹ : ℝ)) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto _).comp h5
  simpa only [Complex.ofReal_inv] using h6

/-- **Lévy's continuity theorem applied to the truncations**: the compound geometric laws of
`Π₁ ↾ {‖x‖ > 1/(n+1)}` converge weakly to any probability measure with characteristic function
`(1 + ψ)⁻¹`; by `eq_of_charFun_levy` there is exactly one such measure. -/
theorem tendsto_expGeom_truncRho (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ} (hα : 0 < α)
    (hα2 : α < 2) (ν : ProbabilityMeasure E)
    (hν : ∀ u : E, charFun (ν : Measure E) u = ((1 + levyPsi (PiOne α μ) u : ℝ) : ℂ)⁻¹) :
    Tendsto (fun n => truncLaw μ hα hα2 n) atTop (𝓝 ν) := by
  refine ProbabilityMeasure.tendsto_of_tendsto_charFun (μ₀ := ν) fun u => ?_
  rw [hν u]
  exact tendsto_charFun_expGeom_truncRho μ hα hα2 u

/-! ## Continuity of the exponent along a ray -/

/-- **Continuity of `s ↦ ∫ (cosh ⟨x,su⟩ - 1) dΠ` at `s = 1`** for a measure supported in the unit
ball with a finite second moment.  Dominated convergence, with dominating function
`4‖u‖²e^{2‖u‖}‖x‖²` -- on the unit ball `|⟨x,u⟩| ≤ ‖u‖`, so `cosh ⟨x,su⟩ - 1 ≤ (s⟨x,u⟩)²e^{|s⟨x,u⟩|}`
is bounded by a multiple of `‖x‖²` for `s` near `1`. -/
theorem tendsto_integral_cosh_line_of_integrable (Pi : Measure E) (u : E)
    (hInt : Integrable (fun x : E => ‖x‖ ^ 2) Pi)
    (hsupp : ∀ᵐ x ∂Pi, ‖x‖ ≤ 1) :
    Tendsto (fun s : ℝ => ∫ x, (Real.cosh (s * (inner ℝ x u)) - 1) ∂Pi)
      (𝓝 1) (𝓝 (∫ x, (Real.cosh (inner ℝ x u) - 1) ∂Pi)) := by
  have hEq : (fun x : E => Real.cosh (inner ℝ x u) - 1)
      = fun x : E => Real.cosh (1 * (inner ℝ x u)) - 1 := by
    funext x
    rw [one_mul]
  rw [hEq]
  refine tendsto_integral_filter_of_dominated_convergence
    (bound := fun x : E => (4 * ‖u‖ ^ 2 * Real.exp (2 * ‖u‖)) * ‖x‖ ^ 2) ?_ ?_ ?_ ?_
  · filter_upwards with s
    exact (by fun_prop : AEStronglyMeasurable (fun x : E => Real.cosh (s * (inner ℝ x u)) - 1) Pi)
  · filter_upwards [Metric.ball_mem_nhds (1 : ℝ) one_pos] with s hs
    have hs2 : |s| ≤ 2 := by
      have h1 : |s - 1| < 1 := by simpa [Real.dist_eq] using hs
      rw [abs_lt] at h1
      rw [abs_le]
      constructor <;> linarith [h1.1, h1.2]
    filter_upwards [hsupp] with x hx
    have hinner : |inner ℝ x u| ≤ ‖u‖ := by
      calc |inner ℝ x u| ≤ ‖x‖ * ‖u‖ := abs_real_inner_le_norm x u
        _ ≤ 1 * ‖u‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg u)
        _ = ‖u‖ := one_mul _
    have ht : |s * (inner ℝ x u)| ≤ 2 * ‖u‖ := by
      rw [abs_mul]
      exact mul_le_mul hs2 hinner (abs_nonneg _) (by norm_num)
    have h1 : Real.cosh (s * (inner ℝ x u)) - 1
        ≤ (s * (inner ℝ x u)) ^ 2 * Real.exp |s * (inner ℝ x u)| :=
      cosh_sub_one_le_sq_mul_exp _
    have h2 : Real.exp |s * (inner ℝ x u)| ≤ Real.exp (2 * ‖u‖) := Real.exp_le_exp.mpr ht
    have h4 : (inner ℝ x u) ^ 2 ≤ ‖x‖ ^ 2 * ‖u‖ ^ 2 := by
      have h := abs_real_inner_le_norm x u
      nlinarith [abs_nonneg (inner ℝ x u), norm_nonneg x, norm_nonneg u, sq_abs (inner ℝ x u)]
    have hs' : s ^ 2 ≤ 4 := by nlinarith [abs_nonneg s, sq_abs s]
    have h3 : (s * (inner ℝ x u)) ^ 2 ≤ 4 * ‖x‖ ^ 2 * ‖u‖ ^ 2 := by
      nlinarith [sq_nonneg (inner ℝ x u), norm_nonneg x, norm_nonneg u, sq_nonneg s]
    have h3' : (s * (inner ℝ x u)) ^ 2 * Real.exp |s * (inner ℝ x u)|
        ≤ (4 * ‖x‖ ^ 2 * ‖u‖ ^ 2) * Real.exp (2 * ‖u‖) :=
      mul_le_mul h3 h2 (Real.exp_pos _).le (by positivity)
    have hnn : (0 : ℝ) ≤ Real.cosh (s * (inner ℝ x u)) - 1 := cosh_sub_one_nonneg' _
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    have h6 : (4 * ‖x‖ ^ 2 * ‖u‖ ^ 2) * Real.exp (2 * ‖u‖)
        = (4 * ‖u‖ ^ 2 * Real.exp (2 * ‖u‖)) * ‖x‖ ^ 2 := by ring
    linarith [h1, h3', h6]
  · exact hInt.const_mul (4 * ‖u‖ ^ 2 * Real.exp (2 * ‖u‖))
  · filter_upwards [hsupp] with x hx
    exact (by fun_prop : Continuous fun s : ℝ => Real.cosh (s * (inner ℝ x u)) - 1).tendsto 1

/-- Continuity of the `Π₁` exponent along a ray. -/
theorem tendsto_integral_cosh_line (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ} (hα : 0 < α)
    (hα2 : α < 2) (u : E) :
    Tendsto (fun s : ℝ => ∫ x, (Real.cosh (s * (inner ℝ x u)) - 1) ∂(PiOne α μ))
      (𝓝 1) (𝓝 (∫ x, (Real.cosh (inner ℝ x u) - 1) ∂(PiOne α μ))) :=
  tendsto_integral_cosh_line_of_integrable (PiOne α μ) u
    (integrable_norm_sq_PiOne μ hα hα2) (PiOne_ae_norm_le_one μ hα)

/-- `levyCoshPsi` along a ray is the Bochner integral. -/
theorem levyCoshPsi_PiOne_smul_eq_integral (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ}
    (hα : 0 < α) (hα2 : α < 2) (u : E) (s : ℝ) :
    levyCoshPsi (PiOne α μ) (s • u)
      = ∫ x, (Real.cosh (s * (inner ℝ x u)) - 1) ∂(PiOne α μ) := by
  have hInt : Integrable (fun x : E => Real.cosh (inner ℝ x (s • u)) - 1) (PiOne α μ) := by
    refine (integrable_cosh_smul_inner_PiOne μ hα hα2 u s).congr
      (Eventually.of_forall fun x => ?_)
    simp only [inner_smul_right]
  rw [levyCoshPsi, levyCoshExp_eq_ofReal_integral _ _ hInt,
    ENNReal.toReal_ofReal (integral_nonneg fun x => cosh_sub_one_nonneg' _)]
  congr 1
  have hfun : (fun x : E => Real.cosh (inner ℝ x (s • u)) - 1)
      = fun x : E => Real.cosh (s * (inner ℝ x u)) - 1 := by
    funext x
    simp only [inner_smul_right]
  rw [hfun]

/-- **The domain of (I.5.17) is open**: if `∫ (cosh ⟨x,u⟩ - 1) dΠ₁ < 1` then the same holds at
`s • u` for some `s > 1`. -/
theorem exists_gt_one_levyCoshPsi (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ} (hα : 0 < α)
    (hα2 : α < 2) (u : E) (hu : levyCoshPsi (PiOne α μ) u < 1) :
    ∃ s : ℝ, 1 < s ∧ levyCoshPsi (PiOne α μ) (s • u) < 1 := by
  have htend : Tendsto (fun s : ℝ => levyCoshPsi (PiOne α μ) (s • u))
      (𝓝 1) (𝓝 (levyCoshPsi (PiOne α μ) u)) := by
    have h1 : (fun s : ℝ => levyCoshPsi (PiOne α μ) (s • u))
        = fun s => ∫ x, (Real.cosh (s * (inner ℝ x u)) - 1) ∂(PiOne α μ) := by
      funext s
      exact levyCoshPsi_PiOne_smul_eq_integral μ hα hα2 u s
    rw [h1, levyCoshPsi_PiOne_eq_integral μ hα hα2 u]
    exact tendsto_integral_cosh_line μ hα hα2 u
  have h2 : ∀ᶠ s : ℝ in 𝓝 1, levyCoshPsi (PiOne α μ) (s • u) < 1 :=
    htend.eventually (isOpen_Iio.mem_nhds hu)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp h2
  have hmem : (1 + ε / 2) ∈ Metric.ball (1 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq,
      show (1 + ε / 2) - 1 = ε / 2 from by ring, abs_of_pos (by positivity)]
    linarith
  exact ⟨1 + ε / 2, by linarith, hball hmem⟩

/-! ## The moment generating function (I.5.17) -/

/-- **Display (I.5.17)**: the moment generating function of the exponential-time stopped
displacement law.  If `ν` is a probability measure whose characteristic function is
`u ↦ (1 + ∫ (1 - cos ⟨x,u⟩) dΠ₁)⁻¹` (by `exists_exp_stop_symm` one exists, and by
`eq_of_charFun_levy` it is unique), then for every `u` with `∫ (cosh ⟨x,u⟩ - 1) dΠ₁ < 1`,

  `∫ x, exp ⟨x,u⟩ dν = (1 - ∫ (cosh ⟨x,u⟩ - 1) dΠ₁)⁻¹`. -/
theorem integral_exp_of_charFun_levy (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ} (hα : 0 < α)
    (hα2 : α < 2) (ν : ProbabilityMeasure E)
    (hν : ∀ u : E, charFun (ν : Measure E) u = ((1 + levyPsi (PiOne α μ) u : ℝ) : ℂ)⁻¹)
    (u : E) (hu : levyCoshPsi (PiOne α μ) u < 1) :
    ∫ x, Real.exp (inner ℝ x u) ∂(ν : Measure E) = (1 - levyCoshPsi (PiOne α μ) u)⁻¹ := by
  set M : ℝ := (1 - levyCoshPsi (PiOne α μ) u)⁻¹ with hMdef
  obtain ⟨p, hp1, hppsi⟩ := exists_gt_one_levyCoshPsi μ hα hα2 u hu
  set K : ℝ := (1 - levyCoshPsi (PiOne α μ) (p • u))⁻¹ with hK
  have hKden : 0 < 1 - levyCoshPsi (PiOne α μ) (p • u) := by linarith
  -- the exponent of each truncation is `< 1`
  have hψn : ∀ (n : ℕ) (w : E), levyCoshPsi (PiOne α μ) w < 1 →
      levyCoshPsi (truncRho μ α n) w < 1 := fun n w hw =>
    lt_of_le_of_lt (levyCoshPsi_truncRho_le μ hα hα2 n w) hw
  -- integrability of the exponential moments of the approximants
  have hIntExp : ∀ (n : ℕ) (w : E), levyCoshPsi (PiOne α μ) w < 1 →
      Integrable (fun x : E => Real.exp (inner ℝ x w)) (expGeom (truncRho μ α n)) := by
    intro n w hw
    have : IsFiniteMeasure (truncRho μ α n) := ⟨truncRho_univ_lt_top μ hα hα2 n⟩
    have hw' : ∫ x, (Real.cosh (inner ℝ x w) - 1) ∂(truncRho μ α n) < 1 := by
      rw [← levyCoshPsi_truncRho_eq_integral μ hα hα2 n w]
      exact hψn n w hw
    have hlin := lintegral_exp_expGeom (truncRho μ α n) (truncRho_symm μ α n) w
      (integrable_cosh_truncRho μ hα hα2 n w) hw'
    refine (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
      (Eventually.of_forall fun x => (Real.exp_pos _).le)).mp ?_
    rw [hlin]
    exact ENNReal.ofReal_ne_top
  -- the exact MGF of each approximant
  have hM : ∀ (n : ℕ) (w : E), levyCoshPsi (PiOne α μ) w < 1 →
      ∫ x, Real.exp (inner ℝ x w) ∂(expGeom (truncRho μ α n))
        = (1 - levyCoshPsi (truncRho μ α n) w)⁻¹ := by
    intro n w hw
    have : IsFiniteMeasure (truncRho μ α n) := ⟨truncRho_univ_lt_top μ hα hα2 n⟩
    have hw' : ∫ x, (Real.cosh (inner ℝ x w) - 1) ∂(truncRho μ α n) < 1 := by
      rw [← levyCoshPsi_truncRho_eq_integral μ hα hα2 n w]
      exact hψn n w hw
    have h := integral_exp_expGeom (truncRho μ α n) (truncRho_symm μ α n) w
      (integrable_cosh_truncRho μ hα hα2 n w) hw'
    rw [h, levyCoshPsi_truncRho_eq_integral μ hα hα2 n w]
  -- the value at `p • u` is bounded
  have hMp : ∀ n, ∫ x, Real.exp (inner ℝ x (p • u)) ∂(expGeom (truncRho μ α n)) ≤ K := by
    intro n
    rw [hM n (p • u) hppsi, hK]
    have h := levyCoshPsi_truncRho_le μ hα hα2 n (p • u)
    simpa only [one_div] using one_div_le_one_div_of_le hKden (by linarith : (1 : ℝ)
      - levyCoshPsi (PiOne α μ) (p • u) ≤ 1 - levyCoshPsi (truncRho μ α n) (p • u))
  -- the exponential tail bound
  have htail : ∀ (n : ℕ) (R : ℝ), 0 < R →
      ∫ x in {x : E | R < Real.exp (inner ℝ x u)}, Real.exp (inner ℝ x u)
        ∂(expGeom (truncRho μ α n)) ≤ R ^ (-(p - 1)) * K := by
    intro n R hR
    have hint_u : Integrable (fun x : E => Real.exp (inner ℝ x u))
        (expGeom (truncRho μ α n)) := hIntExp n u hu
    have hint_p : Integrable (fun x : E => Real.exp (inner ℝ x (p • u)))
        (expGeom (truncRho μ α n)) := hIntExp n (p • u) hppsi
    have hmeas : MeasurableSet {x : E | R < Real.exp (inner ℝ x u)} :=
      measurableSet_lt measurable_const (by fun_prop)
    have hpoint : ∀ x ∈ {x : E | R < Real.exp (inner ℝ x u)},
        Real.exp (inner ℝ x u) ≤ R ^ (-(p - 1)) * Real.exp (inner ℝ x (p • u)) := by
      intro x hx
      have h1 : R ^ (p - 1) ≤ Real.exp (inner ℝ x u) ^ (p - 1) :=
        Real.rpow_le_rpow hR.le hx.le (by linarith)
      have h2 : Real.exp (inner ℝ x u) ^ (p - 1)
          = Real.exp ((p - 1) * (inner ℝ x u)) := by
        rw [← Real.exp_mul]
        ring_nf
      have h3 : Real.exp (inner ℝ x (p • u))
          = Real.exp ((p - 1) * (inner ℝ x u)) * Real.exp (inner ℝ x u) := by
        rw [inner_smul_right, show p * (inner ℝ x u)
          = (p - 1) * (inner ℝ x u) + (inner ℝ x u) from by ring, Real.exp_add]
      have h4 : R ^ (p - 1) * Real.exp (inner ℝ x u) ≤ Real.exp (inner ℝ x (p • u)) := by
        rw [h3]
        exact mul_le_mul_of_nonneg_right (h2 ▸ h1) (Real.exp_pos _).le
      have hRpow : (0 : ℝ) < R ^ (p - 1) := Real.rpow_pos_of_pos hR _
      calc Real.exp (inner ℝ x u)
          = (R ^ (p - 1))⁻¹ * (R ^ (p - 1) * Real.exp (inner ℝ x u)) := by field_simp
        _ ≤ (R ^ (p - 1))⁻¹ * Real.exp (inner ℝ x (p • u)) :=
            mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = R ^ (-(p - 1)) * Real.exp (inner ℝ x (p • u)) := by rw [Real.rpow_neg hR.le]
    calc ∫ x in {x : E | R < Real.exp (inner ℝ x u)}, Real.exp (inner ℝ x u)
          ∂(expGeom (truncRho μ α n))
        = ∫ x, {x : E | R < Real.exp (inner ℝ x u)}.indicator
            (fun x => Real.exp (inner ℝ x u)) x ∂(expGeom (truncRho μ α n)) :=
          (integral_indicator hmeas).symm
      _ ≤ R ^ (-(p - 1)) * K := by
          have hmono : ∫ x, {x : E | R < Real.exp (inner ℝ x u)}.indicator
              (fun x => Real.exp (inner ℝ x u)) x ∂(expGeom (truncRho μ α n))
              ≤ R ^ (-(p - 1)) * ∫ x, Real.exp (inner ℝ x (p • u))
                ∂(expGeom (truncRho μ α n)) := by
            rw [← integral_const_mul]
            refine integral_mono_ae (hint_u.indicator hmeas) (hint_p.const_mul _)
              (Eventually.of_forall fun x => ?_)
            by_cases hx : x ∈ {x : E | R < Real.exp (inner ℝ x u)}
            · rw [Set.indicator_of_mem hx]
              exact hpoint x hx
            · rw [Set.indicator_of_notMem hx]
              exact mul_nonneg (Real.rpow_nonneg hR.le _) (Real.exp_pos _).le
          calc _ ≤ R ^ (-(p - 1)) * ∫ x, Real.exp (inner ℝ x (p • u))
                ∂(expGeom (truncRho μ α n)) := hmono
            _ ≤ R ^ (-(p - 1)) * K := by
                have h3 : (0:ℝ) ≤ R ^ (-(p - 1)) := Real.rpow_nonneg hR.le _
                nlinarith [hMp n]
  -- weak convergence
  have hweak : Tendsto (fun n => truncLaw μ hα hα2 n) atTop (𝓝 ν) :=
    tendsto_expGeom_truncRho μ hα hα2 ν hν
  -- the bound on the truncated exponential
  have hbound : ∀ R : ℝ, 0 < R →
      |∫ x, min (Real.exp (inner ℝ x u)) R ∂(ν : Measure E) - M| ≤ R ^ (-(p - 1)) * K := by
    intro R hR
    have hbc : ∀ x y : E,
        dist (min (Real.exp (inner ℝ x u)) R) (min (Real.exp (inner ℝ y u)) R) ≤ R := by
      intro x y
      rw [Real.dist_eq, abs_le]
      constructor
      · have h1 : (0:ℝ) ≤ min (Real.exp (inner ℝ x u)) R := le_min (Real.exp_pos _).le hR.le
        have h2 : min (Real.exp (inner ℝ y u)) R ≤ R := min_le_right _ _
        linarith
      · have h1 : (0:ℝ) ≤ min (Real.exp (inner ℝ y u)) R := le_min (Real.exp_pos _).le hR.le
        have h2 : min (Real.exp (inner ℝ x u)) R ≤ R := min_le_right _ _
        linarith
    let gR : BoundedContinuousFunction E ℝ := BoundedContinuousFunction.mkOfBound
      ⟨fun x => min (Real.exp (inner ℝ x u)) R, by fun_prop⟩ R hbc
    have hgR : ∀ x : E, (gR : E → ℝ) x = min (Real.exp (inner ℝ x u)) R := fun x => rfl
    have hlim1 : Tendsto (fun n => ∫ x, min (Real.exp (inner ℝ x u)) R
        ∂(expGeom (truncRho μ α n))) atTop
        (𝓝 (∫ x, min (Real.exp (inner ℝ x u)) R ∂(ν : Measure E))) := by
      have h := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℝ).mp hweak gR
      simpa only [hgR, coe_truncLaw] using h
    have hlim2 : Tendsto (fun n => (1 - levyCoshPsi (truncRho μ α n) u)⁻¹) atTop (𝓝 M) := by
      have h1 := tendsto_levyCoshPsi_trunc μ hα hα2 u
      have h2 : Tendsto (fun n => 1 - levyCoshPsi (truncRho μ α n) u) atTop
          (𝓝 (1 - levyCoshPsi (PiOne α μ) u)) := tendsto_const_nhds.sub h1
      have h3 : (1 - levyCoshPsi (PiOne α μ) u) ≠ 0 := by linarith
      have h4 := h2.inv₀ h3
      simpa only [hMdef] using h4
    have hstep : ∀ n, |∫ x, min (Real.exp (inner ℝ x u)) R ∂(expGeom (truncRho μ α n))
        - (1 - levyCoshPsi (truncRho μ α n) u)⁻¹| ≤ R ^ (-(p - 1)) * K := by
      intro n
      have : IsFiniteMeasure (truncRho μ α n) := ⟨truncRho_univ_lt_top μ hα hα2 n⟩
      have hint_u : Integrable (fun x : E => Real.exp (inner ℝ x u))
          (expGeom (truncRho μ α n)) := hIntExp n u hu
      have hmin_int : Integrable (fun x : E => min (Real.exp (inner ℝ x u)) R)
          (expGeom (truncRho μ α n)) := by
        refine Integrable.of_bound (by fun_prop) R ?_
        filter_upwards with x
        rw [Real.norm_eq_abs, abs_le]
        constructor
        · have := le_min (Real.exp_pos (inner ℝ x u)).le hR.le
          linarith
        · exact min_le_right _ _
      have h1 : ∫ x, min (Real.exp (inner ℝ x u)) R ∂(expGeom (truncRho μ α n))
          ≤ (1 - levyCoshPsi (truncRho μ α n) u)⁻¹ := by
        rw [← hM n u hu]
        exact integral_mono_ae hmin_int hint_u
          (Eventually.of_forall fun x => min_le_left _ _)
      have h2 : (1 - levyCoshPsi (truncRho μ α n) u)⁻¹
          - ∫ x, min (Real.exp (inner ℝ x u)) R ∂(expGeom (truncRho μ α n))
          ≤ R ^ (-(p - 1)) * K := by
        have hMeq : (1 - levyCoshPsi (truncRho μ α n) u)⁻¹
            = ∫ x, Real.exp (inner ℝ x u) ∂(expGeom (truncRho μ α n)) := (hM n u hu).symm
        have hmeasR : MeasurableSet {x : E | R < Real.exp (inner ℝ x u)} :=
          measurableSet_lt measurable_const (by fun_prop)
        rw [hMeq, ← integral_sub hint_u hmin_int]
        calc ∫ x, (Real.exp (inner ℝ x u) - min (Real.exp (inner ℝ x u)) R)
              ∂(expGeom (truncRho μ α n))
            ≤ ∫ x, {x : E | R < Real.exp (inner ℝ x u)}.indicator
                (fun x => Real.exp (inner ℝ x u)) x ∂(expGeom (truncRho μ α n)) := by
              refine integral_mono_ae (hint_u.sub hmin_int) (hint_u.indicator hmeasR)
                (Eventually.of_forall fun x => ?_)
              by_cases hx : x ∈ {x : E | R < Real.exp (inner ℝ x u)}
              · simp only [Set.indicator_of_mem hx,
                  min_eq_right (le_of_lt (show R < Real.exp (inner ℝ x u) from hx))]
                linarith
              · simp only [Set.indicator_of_notMem hx,
                  min_eq_left (le_of_not_gt (show ¬ R < Real.exp (inner ℝ x u) from hx))]
                simp
          _ = ∫ x in {x : E | R < Real.exp (inner ℝ x u)}, Real.exp (inner ℝ x u)
                ∂(expGeom (truncRho μ α n)) := integral_indicator hmeasR
          _ ≤ R ^ (-(p - 1)) * K := htail n R hR
      rw [abs_sub_le_iff]
      exact ⟨by linarith, by linarith⟩
    exact le_of_tendsto_of_tendsto ((hlim1.sub hlim2).abs) tendsto_const_nhds
      (Eventually.of_forall hstep)
  -- squeeze: the truncated exponentials converge to `M`
  have hmain : Tendsto (fun n : ℕ => ∫ x, min (Real.exp (inner ℝ x u)) ((n : ℝ) + 1)
      ∂(ν : Measure E)) atTop (𝓝 M) := by
    have hdelta : Tendsto (fun n : ℕ =>
        |∫ x, min (Real.exp (inner ℝ x u)) ((n : ℝ) + 1) ∂(ν : Measure E) - M|)
        atTop (𝓝 0) := by
      refine squeeze_zero (fun n => abs_nonneg _) (fun n => hbound _ (by positivity)) ?_
      have h2 : Tendsto (fun x : ℝ => x ^ (-(p - 1))) atTop (𝓝 0) :=
        tendsto_rpow_neg_atTop (by linarith)
      have h3 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)) atTop atTop :=
        tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
      have h4 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ (-(p - 1)) * K) atTop (𝓝 (0 * K)) :=
        (h2.comp h3).mul_const K
      simpa using h4
    have hsub : Tendsto (fun n : ℕ =>
        ∫ x, min (Real.exp (inner ℝ x u)) ((n : ℝ) + 1) ∂(ν : Measure E) - M)
        atTop (𝓝 0) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      simpa only [Real.norm_eq_abs, sub_zero] using hdelta
    have hfin := hsub.add_const M
    simpa using hfin
  -- monotone convergence: identify the Bochner integral
  have hofreal : Tendsto (fun n : ℕ =>
      ENNReal.ofReal (∫ x, min (Real.exp (inner ℝ x u)) ((n : ℝ) + 1)
        ∂(ν : Measure E))) atTop (𝓝 (ENNReal.ofReal M)) := ENNReal.tendsto_ofReal hmain
  have hminabs : ∀ n : ℕ,
      Integrable (fun x : E => min (Real.exp (inner ℝ x u)) ((n : ℝ) + 1)) (ν : Measure E) := by
    intro n
    refine Integrable.of_bound (by fun_prop) ((n : ℝ) + 1) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have := le_min (Real.exp_pos (inner ℝ x u)).le (by positivity : (0:ℝ) ≤ (n : ℝ) + 1)
      linarith
    · exact min_le_right _ _
  have heq : ∀ n : ℕ,
      ENNReal.ofReal (∫ x, min (Real.exp (inner ℝ x u)) ((n : ℝ) + 1) ∂(ν : Measure E))
      = ∫⁻ x, ENNReal.ofReal (min (Real.exp (inner ℝ x u)) ((n : ℝ) + 1))
        ∂(ν : Measure E) := by
    intro n
    rw [ofReal_integral_eq_lintegral_ofReal (hminabs n)]
    exact Eventually.of_forall fun x =>
      le_min (Real.exp_pos _).le (by positivity : (0:ℝ) ≤ (n : ℝ) + 1)
  simp only [heq] at hofreal
  have hmct : Tendsto (fun n : ℕ =>
      ∫⁻ x, ENNReal.ofReal (min (Real.exp (inner ℝ x u)) ((n : ℝ) + 1))
        ∂(ν : Measure E)) atTop
      (𝓝 (∫⁻ x, ENNReal.ofReal (Real.exp (inner ℝ x u)) ∂(ν : Measure E))) := by
    have hmono : Monotone (fun n : ℕ =>
        ∫⁻ x, ENNReal.ofReal (min (Real.exp (inner ℝ x u)) ((n : ℝ) + 1))
          ∂(ν : Measure E)) := by
      intro m n hmn
      refine lintegral_mono fun x => ?_
      refine ENNReal.ofReal_le_ofReal (min_le_min le_rfl ?_)
      have : (m : ℝ) ≤ n := by exact_mod_cast hmn
      linarith
    have hsup : (⨆ n : ℕ,
        ∫⁻ x, ENNReal.ofReal (min (Real.exp (inner ℝ x u)) ((n : ℝ) + 1))
          ∂(ν : Measure E))
        = ∫⁻ x, ENNReal.ofReal (Real.exp (inner ℝ x u)) ∂(ν : Measure E) := by
      have hli : ∫⁻ x, (⨆ n : ℕ,
            ENNReal.ofReal (min (Real.exp (inner ℝ x u)) ((n : ℝ) + 1))) ∂(ν : Measure E)
          = ⨆ n : ℕ, ∫⁻ x, ENNReal.ofReal (min (Real.exp (inner ℝ x u)) ((n : ℝ) + 1))
            ∂(ν : Measure E) :=
        lintegral_iSup
          (f := fun n x => ENNReal.ofReal (min (Real.exp (inner ℝ x u)) ((n : ℝ) + 1)))
          (fun n => by fun_prop)
          (fun m n hmn x => by
            refine ENNReal.ofReal_le_ofReal (min_le_min le_rfl ?_)
            have : (m : ℝ) ≤ n := by exact_mod_cast hmn
            linarith)
      rw [← hli]
      congr 1
      funext x
      refine le_antisymm (iSup_le fun n => ENNReal.ofReal_le_ofReal (min_le_left _ _)) ?_
      obtain ⟨n, hn⟩ := exists_nat_ge (Real.exp (inner ℝ x u))
      calc ENNReal.ofReal (Real.exp (inner ℝ x u))
          = ENNReal.ofReal (min (Real.exp (inner ℝ x u)) ((n : ℝ) + 1)) := by
            rw [min_eq_left (by linarith)]
        _ ≤ ⨆ m : ℕ, ENNReal.ofReal (min (Real.exp (inner ℝ x u)) ((m : ℝ) + 1)) :=
            le_iSup (fun m : ℕ => ENNReal.ofReal (min (Real.exp (inner ℝ x u)) ((m : ℝ) + 1))) n
    have h := tendsto_atTop_iSup hmono
    rwa [hsup] at h
  have hkey : ENNReal.ofReal M = ∫⁻ x, ENNReal.ofReal (Real.exp (inner ℝ x u))
      ∂(ν : Measure E) := tendsto_nhds_unique hofreal hmct
  rw [integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun x => (Real.exp_pos _).le) (by fun_prop), ← hkey,
    ENNReal.toReal_ofReal]
  have hpos : (0:ℝ) < 1 - levyCoshPsi (PiOne α μ) u := by linarith
  rw [hMdef]
  exact le_of_lt (inv_pos.mpr hpos)

/-! ## Continuity of the exponent on all of `E`, and the domain of (I.5.17) -/

/-- **Continuity of `u ↦ ∫ (cosh ⟨x,u⟩ - 1) dΠ`** for a measure supported in the unit ball with
a finite second moment.  Dominated convergence: on a ball `‖u‖ ≤ M`, `cosh ⟨x,u⟩ - 1` is bounded
by `M²e^M ‖x‖²`, which is integrable. -/
theorem continuous_integral_cosh_of_integrable (Pi : Measure E)
    (hInt : Integrable (fun x : E => ‖x‖ ^ 2) Pi)
    (hsupp : ∀ᵐ x ∂Pi, ‖x‖ ≤ 1) :
    Continuous fun u : E => ∫ x, (Real.cosh (inner ℝ x u) - 1) ∂Pi := by
  rw [continuous_iff_continuousAt]
  intro u₀
  set M : ℝ := ‖u₀‖ + 1 with hM
  have hMpos : 0 < M := by positivity
  refine tendsto_integral_filter_of_dominated_convergence
    (bound := fun x : E => (M ^ 2 * Real.exp M) * ‖x‖ ^ 2) ?_ ?_ ?_ ?_
  · filter_upwards with u
    exact (by fun_prop : AEStronglyMeasurable (fun x : E => Real.cosh (inner ℝ x u) - 1) Pi)
  · filter_upwards [Metric.ball_mem_nhds u₀ one_pos] with u hu
    have huM : ‖u‖ ≤ M := by
      have h1 : ‖u - u₀‖ < 1 := by simpa [dist_eq_norm] using hu
      calc ‖u‖ = ‖u₀ + (u - u₀)‖ := by rw [add_sub_cancel]
        _ ≤ ‖u₀‖ + ‖u - u₀‖ := norm_add_le _ _
        _ ≤ ‖u₀‖ + 1 := by linarith
        _ = M := hM
    filter_upwards [hsupp] with x hx
    have hinner : |inner ℝ x u| ≤ M := by
      calc |inner ℝ x u| ≤ ‖x‖ * ‖u‖ := abs_real_inner_le_norm x u
        _ ≤ 1 * M := mul_le_mul hx huM (norm_nonneg u) (by norm_num)
        _ = M := one_mul _
    have h1 : Real.cosh (inner ℝ x u) - 1
        ≤ (inner ℝ x u) ^ 2 * Real.exp |inner ℝ x u| := cosh_sub_one_le_sq_mul_exp _
    have h2 : Real.exp |inner ℝ x u| ≤ Real.exp M := Real.exp_le_exp.mpr hinner
    have h3 : (inner ℝ x u) ^ 2 ≤ M ^ 2 * ‖x‖ ^ 2 := by
      have h4 : (inner ℝ x u) ^ 2 ≤ ‖x‖ ^ 2 * ‖u‖ ^ 2 := by
        have h := abs_real_inner_le_norm x u
        nlinarith [abs_nonneg (inner ℝ x u), norm_nonneg x, norm_nonneg u,
          sq_abs (inner ℝ x u)]
      have h5 : ‖u‖ ^ 2 ≤ M ^ 2 := by nlinarith [norm_nonneg u]
      have hx2 : (0:ℝ) ≤ ‖x‖ ^ 2 := sq_nonneg _
      nlinarith
    have h3' : (inner ℝ x u) ^ 2 * Real.exp |inner ℝ x u| ≤ (M ^ 2 * ‖x‖ ^ 2) * Real.exp M :=
      mul_le_mul h3 h2 (Real.exp_pos _).le (by positivity)
    have hnn : (0 : ℝ) ≤ Real.cosh (inner ℝ x u) - 1 := cosh_sub_one_nonneg' _
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    have h6 : (M ^ 2 * ‖x‖ ^ 2) * Real.exp M = (M ^ 2 * Real.exp M) * ‖x‖ ^ 2 := by ring
    linarith [h1, h3', h6]
  · exact hInt.const_mul (M ^ 2 * Real.exp M)
  · filter_upwards [hsupp] with x hx
    exact (by fun_prop : Continuous fun u : E => Real.cosh (inner ℝ x u) - 1).tendsto u₀

/-- Continuity of `levyCoshPsi (Π₁)`. -/
theorem continuous_levyCoshPsi_PiOne (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ} (hα : 0 < α)
    (hα2 : α < 2) : Continuous fun u : E => levyCoshPsi (PiOne α μ) u := by
  have hEq : (fun u : E => levyCoshPsi (PiOne α μ) u)
      = fun u => ∫ x, (Real.cosh (inner ℝ x u) - 1) ∂(PiOne α μ) := by
    funext u
    exact levyCoshPsi_PiOne_eq_integral μ hα hα2 u
  rw [hEq]
  exact continuous_integral_cosh_of_integrable (PiOne α μ)
    (integrable_norm_sq_PiOne μ hα hα2) (PiOne_ae_norm_le_one μ hα)

/-- **The domain of (I.5.17) is open.** -/
theorem isOpen_setOf_levyCoshPsi_lt_one (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ}
    (hα : 0 < α) (hα2 : α < 2) :
    IsOpen {u : E | levyCoshPsi (PiOne α μ) u < 1} :=
  isOpen_lt (continuous_levyCoshPsi_PiOne μ hα hα2) continuous_const

/-- **The domain of (I.5.17) is a neighbourhood of the origin** (the paper's "open neighbourhood
of the origin"): `∫ (cosh ⟨x,0⟩ - 1) dΠ₁ = 0 < 1`. -/
theorem nhds_setOf_levyCoshPsi_lt_one (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ} (hα : 0 < α)
    (hα2 : α < 2) : {u : E | levyCoshPsi (PiOne α μ) u < 1} ∈ 𝓝 0 := by
  refine (isOpen_setOf_levyCoshPsi_lt_one μ hα hα2).mem_nhds ?_
  simp [levyCoshPsi_zero]

/-- **Definition I.5.16 and display (I.5.17), together.**

For `0 < α < 2` there is a probability measure `ν_disp` on `E` -- the law of the symmetric Lévy
jump process with Lévy measure `Π₁` of (I.5.16) stopped at an independent rate-1 exponential time
-- with the following two properties:

* its characteristic function is `u ↦ (1 + ∫ (1 - cos ⟨x,u⟩) dΠ₁)⁻¹` (this is what identifies the
  law: any two probability measures with this characteristic function coincide, by
  `eq_of_charFun_levy`);
* its moment generating function is

    `∫ x, e^{⟨x,u⟩} dν_disp = (1 - ∫ (cosh ⟨x,u⟩ - 1) dΠ₁)⁻¹`

  for every `u` with `∫ (cosh ⟨x,u⟩ - 1) dΠ₁ < 1` -- an open neighbourhood of the origin
  (`nhds_setOf_levyCoshPsi_lt_one`). -/
theorem exists_nuDisp_mgf (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ} (hα : 0 < α) (hα2 : α < 2) :
    ∃ ν : ProbabilityMeasure E,
      (∀ u : E, charFun (ν : Measure E) u = ((1 + levyPsi (PiOne α μ) u : ℝ) : ℂ)⁻¹) ∧
      (∀ u : E, levyCoshPsi (PiOne α μ) u < 1 →
        ∫ x, Real.exp (inner ℝ x u) ∂(ν : Measure E)
          = (1 - levyCoshPsi (PiOne α μ) u)⁻¹) := by
  obtain ⟨ν, hν, -⟩ :=
    exists_exp_stop_symm (PiOne α μ) (PiOne_levy_measure μ hα hα2) (PiOne_symm μ α)
  exact ⟨ν, hν, fun u hu => integral_exp_of_charFun_levy μ hα hα2 ν hν u hu⟩

/-- **The MGF identity is a property of the law**: it holds for every probability measure with the
characteristic function of `ν_disp`, i.e. by `eq_of_charFun_levy` for the unique stopped law. -/
theorem forall_integral_exp_of_forall_charFun (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ}
    (hα : 0 < α) (hα2 : α < 2) :
    ∀ ν : ProbabilityMeasure E,
      (∀ u : E, charFun (ν : Measure E) u = ((1 + levyPsi (PiOne α μ) u : ℝ) : ℂ)⁻¹) →
      ∀ u : E, levyCoshPsi (PiOne α μ) u < 1 →
        ∫ x, Real.exp (inner ℝ x u) ∂(ν : Measure E)
          = (1 - levyCoshPsi (PiOne α μ) u)⁻¹ :=
  fun ν hν u hu => integral_exp_of_charFun_levy μ hα hα2 ν hν u hu

/-- The identity at `u = 0` (the total mass): `∫ 1 dν_disp = 1 = (1 - 0)⁻¹`. -/
theorem integral_exp_zero_of_charFun_levy (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ}
    (hα : 0 < α) (hα2 : α < 2) (ν : ProbabilityMeasure E)
    (hν : ∀ u : E, charFun (ν : Measure E) u = ((1 + levyPsi (PiOne α μ) u : ℝ) : ℂ)⁻¹) :
    ∫ x, Real.exp (inner ℝ x (0 : E)) ∂(ν : Measure E) = 1 := by
  rw [integral_exp_of_charFun_levy μ hα hα2 ν hν 0 (by rw [levyCoshPsi_zero]; norm_num)]
  simp [levyCoshPsi_zero]

/-- **Uniqueness of the stopped law** (the `α < 2` case of Definition I.5.16): two probability
measures with the characteristic function `u ↦ (1 + ∫ (1 - cos ⟨x,u⟩) dΠ₁)⁻¹` coincide.  In
particular the law `ν_disp` of `exists_nuDisp_mgf` is the unique exponential-time stopped law of
the symmetric jump process with Lévy measure `Π₁`. -/
theorem eq_of_charFun_levy_PiOne (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ} (hα : 0 < α)
    (hα2 : α < 2) {ν ν' : ProbabilityMeasure E}
    (hν : ∀ u : E, charFun (ν : Measure E) u = ((1 + levyPsi (PiOne α μ) u : ℝ) : ℂ)⁻¹)
    (hν' : ∀ u : E, charFun (ν' : Measure E) u = ((1 + levyPsi (PiOne α μ) u : ℝ) : ℂ)⁻¹) :
    ν = ν' :=
  eq_of_charFun_levy (PiOne α μ) hν hν'
