/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Formalization derived from T. Hutchcroft, "Critical long-range percolation I:
High effective dimension", arXiv:2508.18807v1, Section I.5.2 (I.5.16) - (I.5.20).
-/
module

public import Mathlib
public import PercLib.CriticalLRP.LevyAnalysis.Radial
public import PercLib.CriticalLRP.LevyAnalysis.Rpow
public import PercLib.CriticalLRP.LevyAnalysis.Homogeneous

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

/-!
# The Lévy measures `Π₁`, `Π_lam`, `Π_∞` of Section I.5.2

The paper (I.5.16) defines, for `α > 0` and `d = dim`,
```
dΠ₁/dx  = α * 1(‖x‖ ≤ 1) * ∫_{‖x‖}^{1} s^{-d-α-1} ds
dΠ_∞/dx = α * ∫_{‖x‖}^{∞} s^{-d-α-1} ds
```
so that (evaluating the elementary integrals, see
`CLRP.levyDensOne_eq_integral` / `CLRP.levyDensInf_eq_integral`)
```
dΠ₁/dx  = α/(d+α) * (‖x‖^{-d-α} - 1)      on ‖x‖ ≤ 1
dΠ_∞/dx = α/(d+α) * ‖x‖^{-d-α}
dΠ_lam/dx = α/(d+α) * (‖x‖^{-d-α} - lam^{-d-α})  on ‖x‖ ≤ lam   (rescaled Π₁)
```
We use the closed forms as definitions and record the integral forms as lemmas.

All three densities are automatically `0` off their supports because `ENNReal.ofReal`
of a negative real is `0`: e.g. for `‖x‖ > 1` we have `‖x‖^{-d-α} < 1`, so the `Π₁`
density vanishes (`CLRP.levyDensOne_eq_zero_of_one_le`).
-/

@[expose] public section

open MeasureTheory Metric Set Filter
open Module
open scoped ENNReal NNReal Topology Pointwise Interval

namespace PercLib.CriticalLRP.LevyAnalysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- Measurability of the `Π_∞`-density. -/
theorem measurable_levyDensInf (α : ℝ) :
    Measurable (fun x : E => ENNReal.ofReal
      (α / ((finrank ℝ E : ℝ) + α) * ‖x‖ ^ (-(finrank ℝ E : ℝ) - α))) := by
  fun_prop

/-- Measurability of the `Π_lam`-density. -/
theorem measurable_levyDensLam (α lam : ℝ) :
    Measurable (fun x : E => ENNReal.ofReal (α / ((finrank ℝ E : ℝ) + α)
      * (‖x‖ ^ (-(finrank ℝ E : ℝ) - α) - lam ^ (-(finrank ℝ E : ℝ) - α)))) := by
  fun_prop

/-- The density of the `α`-stable Lévy measure `Π_∞` (I.5.16),
`α/(d+α) ‖x‖^{-d-α}`. -/
noncomputable def levyDensInf (α : ℝ) : E → ℝ≥0∞ := fun x => ENNReal.ofReal
  (α / ((finrank ℝ E : ℝ) + α) * ‖x‖ ^ (-(finrank ℝ E : ℝ) - α))

/-- The density of the cut-off Lévy measure `Π_lam` (I.5.16),
`α/(d+α) (‖x‖^{-d-α} - lam^{-d-α})` on `‖x‖ ≤ lam`. -/
noncomputable def levyDensLam (α lam : ℝ) : E → ℝ≥0∞ := fun x => ENNReal.ofReal
  (α / ((finrank ℝ E : ℝ) + α)
    * (‖x‖ ^ (-(finrank ℝ E : ℝ) - α) - lam ^ (-(finrank ℝ E : ℝ) - α)))

/-- The density of the cut-off Lévy measure `Π₁` of (I.5.16). -/
noncomputable def levyDensOne (α : ℝ) : E → ℝ≥0∞ := levyDensLam (E := E) α 1

/-- `Π_∞`, the Lévy measure of the symmetric `α`-stable Lévy process. -/
noncomputable def PiInf (α : ℝ) (μ : Measure E) : Measure E := μ.withDensity (levyDensInf α)

/-- `Π_lam`, the cut-off Lévy measures of (I.5.16). -/
noncomputable def PiLam (α lam : ℝ) (μ : Measure E) : Measure E := μ.withDensity (levyDensLam α lam)

/-- `Π₁ = Π_lam` at `lam = 1`. -/
noncomputable def PiOne (α : ℝ) (μ : Measure E) : Measure E := PiLam (E := E) α 1 μ

theorem measurable_levyDensOne (α : ℝ) : Measurable (levyDensOne (E := E) α) :=
  measurable_levyDensLam α 1

/-- The elementary antiderivative in (I.5.16):
`∫_{‖x‖}^{1} s^{-d-α-1} ds = (‖x‖^{-d-α} - 1)/(d+α)`. -/
theorem integral_rpow_neg_sub {α : ℝ} (hα : 0 < α) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∫ s in r..1, s ^ (-(finrank ℝ E : ℝ) - α - 1)
      = (r ^ (-(finrank ℝ E : ℝ) - α) - 1) / ((finrank ℝ E : ℝ) + α) := by
  have hne : (-(finrank ℝ E : ℝ) - α - 1) ≠ -1 := by
    intro h
    have hd : (0:ℝ) < (finrank ℝ E : ℝ) := by
      exact_mod_cast Module.finrank_pos (R := ℝ) (M := E)
    linarith
  rw [integral_rpow (Or.inr ⟨hne, by
    rw [uIcc_of_le hr1]
    simp only [mem_Icc, not_and]
    intro h
    linarith⟩)]
  have h1 : (1:ℝ) ^ (-(finrank ℝ E : ℝ) - α - 1 + 1) = 1 := Real.one_rpow _
  rw [h1]
  have hexp : -(finrank ℝ E : ℝ) - α - 1 + 1 = -(finrank ℝ E : ℝ) - α := by ring
  rw [hexp]
  have hK : (-(finrank ℝ E : ℝ) - α) ≠ 0 := by
    have hd : (0:ℝ) < (finrank ℝ E : ℝ) := by
      exact_mod_cast Module.finrank_pos (R := ℝ) (M := E)
    intro h
    linarith
  field_simp
  ring


/-- `Π₁`'s density vanishes off the unit ball (for `α > 0`). -/
theorem levyDensOne_eq_zero_of_one_le {α : ℝ} (hα : 0 < α) {x : E} (hx : 1 ≤ ‖x‖) :
    levyDensOne (E := E) α x = 0 := by
  have hd : (0:ℝ) < (finrank ℝ E : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := ℝ) (M := E)
  have h1 : ‖x‖ ^ (-(finrank ℝ E : ℝ) - α) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hx (by linarith)
  have h2 : (1:ℝ) ^ (-(finrank ℝ E : ℝ) - α) = 1 := Real.one_rpow _
  have hle : α / ((finrank ℝ E : ℝ) + α)
      * (‖x‖ ^ (-(finrank ℝ E : ℝ) - α) - 1 ^ (-(finrank ℝ E : ℝ) - α)) ≤ 0 := by
    rw [h2]
    have hc : (0:ℝ) ≤ α / ((finrank ℝ E : ℝ) + α) := by positivity
    nlinarith
  show ENNReal.ofReal (α / ((finrank ℝ E : ℝ) + α)
      * (‖x‖ ^ (-(finrank ℝ E : ℝ) - α) - 1 ^ (-(finrank ℝ E : ℝ) - α))) = 0
  rw [ENNReal.ofReal_eq_zero]
  exact hle


/-- Almost every point is nonzero, for an additive Haar measure on a nontrivial space. -/
theorem ae_ne_zero (μ : Measure E) [μ.IsAddHaarMeasure] : ∀ᵐ x ∂μ, x ≠ (0 : E) := by
  have hsing : μ ({(0 : E)} : Set E) = 0 := by
    have h := Measure.addHaar_smul μ (r := (0 : ℝ)) (s := (Set.univ : Set E))
    rw [zero_smul_set (Set.univ_nonempty (α := E)),
      zero_pow (Nat.pos_iff_ne_zero.mp (Module.finrank_pos (R := ℝ) (M := E))), abs_zero,
      ENNReal.ofReal_zero, zero_mul] at h
    exact h
  rw [MeasureTheory.ae_iff]
  simpa using hsing

/-- **The `2p`-th moment identity for `Π₁`** (the paper's display following (I.5.17)):
for `P ≥ 0` measurable, homogeneous of degree `k > α`, integrable on the unit ball,
`∫ P dΠ₁ = α/(k-α) * ∫_{B₁} P dx`.
The paper's case is `P x = ⟨u,x⟩^{2p}`, `k = 2p`, giving the constant `α/(2p-α)`. -/
theorem lintegral_PiOne_of_hom (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ} (hα : 0 < α)
    (hα2 : α < 2) {P : E → ℝ} (hP : ∀ x, 0 ≤ P x) (hPm : Measurable P) {k : ℝ}
    (hk : α < k) (hhom : ∀ (c : ℝ), 0 < c → ∀ x, P (c • x) = c ^ k * P x)
    (hint : IntegrableOn P (ball (0 : E) 1) μ) :
    ∫⁻ x, ENNReal.ofReal (P x) ∂(PiOne α μ)
      = ENNReal.ofReal (α / (k - α) * ∫ x in ball (0 : E) 1, P x ∂μ) := by
  have hd : (0:ℝ) < (finrank ℝ E : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := ℝ) (M := E)
  set J : ℝ := ∫ x in ball (0 : E) 1, P x ∂μ with hJdef
  have hJ_nn : 0 ≤ J := by
    rw [hJdef]; exact integral_nonneg hP
  -- Step A: rewrite through the density
  have stepA : ∫⁻ x, ENNReal.ofReal (P x) ∂(PiOne α μ)
      = ∫⁻ x, levyDensOne (E := E) α x * ENNReal.ofReal (P x) ∂μ := by
    rw [PiOne, PiLam]
    exact lintegral_withDensity_eq_lintegral_mul μ (measurable_levyDensOne α) hPm.ennreal_ofReal
  -- Step B: the density is supported in the unit ball
  have stepB : ∫⁻ x, levyDensOne (E := E) α x * ENNReal.ofReal (P x) ∂μ
      = ∫⁻ x in ball (0 : E) 1,
          levyDensOne (E := E) α x * ENNReal.ofReal (P x) ∂μ := by
    rw [← lintegral_indicator measurableSet_ball]
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ ball (0 : E) 1
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx]
      have h1 : (1:ℝ) ≤ ‖x‖ := by
        by_contra h
        exact hx (by simpa [mem_ball, dist_zero_right] using lt_of_not_ge h)
      rw [levyDensOne_eq_zero_of_one_le (E := E) hα h1]
      simp
  -- Step C: pointwise algebra and `lintegral_sub`
  have hG_meas : Measurable (fun x : E => ENNReal.ofReal (P x)) := hPm.ennreal_ofReal
  have hF_meas : Measurable (fun x : E =>
      ENNReal.ofReal (P x * ‖x‖ ^ (-(finrank ℝ E : ℝ) - α))) := by fun_prop
  have hG_top : ∫⁻ x in ball (0 : E) 1, ENNReal.ofReal (P x) ∂μ ≠ ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hP)]
    exact ENNReal.ofReal_ne_top
  have hGF : (fun x : E => ENNReal.ofReal (P x)) ≤ᵐ[μ.restrict (ball (0 : E) 1)]
      (fun x : E => ENNReal.ofReal (P x * ‖x‖ ^ (-(finrank ℝ E : ℝ) - α))) := by
    filter_upwards [ae_restrict_mem measurableSet_ball,
      ae_mono Measure.restrict_le_self (ae_ne_zero (E := E) μ)] with x hx hxne
    have hx1 : ‖x‖ < 1 := by simpa [mem_ball, dist_zero_right] using hx
    have hx0 : (0:ℝ) < ‖x‖ := norm_pos_iff.mpr hxne
    have hg1 : (1:ℝ) ≤ ‖x‖ ^ (-(finrank ℝ E : ℝ) - α) := by
      simpa using Real.rpow_le_rpow_of_nonpos (x := ‖x‖) (y := 1)
        (z := -(finrank ℝ E : ℝ) - α) hx0 hx1.le (by linarith)
    have : P x ≤ P x * ‖x‖ ^ (-(finrank ℝ E : ℝ) - α) :=
      le_mul_of_one_le_right (hP x) hg1
    exact ENNReal.ofReal_le_ofReal this
  have stepC : ∫⁻ x in ball (0 : E) 1,
        levyDensOne (E := E) α x * ENNReal.ofReal (P x) ∂μ
      = ENNReal.ofReal (α / ((finrank ℝ E : ℝ) + α)) *
        ((∫⁻ x in ball (0 : E) 1,
            ENNReal.ofReal (P x * ‖x‖ ^ (-(finrank ℝ E : ℝ) - α)) ∂μ)
          - ∫⁻ x in ball (0 : E) 1, ENNReal.ofReal (P x) ∂μ) := by
    have hpt : ∀ᵐ x ∂(μ.restrict (ball (0 : E) 1)),
        levyDensOne (E := E) α x * ENNReal.ofReal (P x)
          = ENNReal.ofReal (α / ((finrank ℝ E : ℝ) + α)) *
            (ENNReal.ofReal (P x * ‖x‖ ^ (-(finrank ℝ E : ℝ) - α)) - ENNReal.ofReal (P x)) := by
      filter_upwards [ae_restrict_mem measurableSet_ball,
        ae_mono Measure.restrict_le_self (ae_ne_zero (E := E) μ)] with x hx hxne
      have hx1 : ‖x‖ < 1 := by simpa [mem_ball, dist_zero_right] using hx
      have hx0 : (0:ℝ) < ‖x‖ := norm_pos_iff.mpr hxne
      have hgn : (0:ℝ) ≤ ‖x‖ ^ (-(finrank ℝ E : ℝ) - α) := Real.rpow_nonneg hx0.le _
      have hg1 : (1:ℝ) ≤ ‖x‖ ^ (-(finrank ℝ E : ℝ) - α) := by
        simpa using Real.rpow_le_rpow_of_nonpos (x := ‖x‖) (y := 1)
          (z := -(finrank ℝ E : ℝ) - α) hx0 hx1.le (by linarith)
      have hsub_nn : (0:ℝ) ≤ ‖x‖ ^ (-(finrank ℝ E : ℝ) - α) - 1 := by linarith
      have hcn : (0:ℝ) ≤ α / ((finrank ℝ E : ℝ) + α) := by positivity
      show ENNReal.ofReal (α / ((finrank ℝ E : ℝ) + α)
            * (‖x‖ ^ (-(finrank ℝ E : ℝ) - α) - 1 ^ (-(finrank ℝ E : ℝ) - α)))
          * ENNReal.ofReal (P x) = _
      rw [Real.one_rpow,
        ENNReal.ofReal_mul (p := α / ((finrank ℝ E : ℝ) + α))
          (q := ‖x‖ ^ (-(finrank ℝ E : ℝ) - α) - 1) hcn,
        ENNReal.ofReal_sub (‖x‖ ^ (-(finrank ℝ E : ℝ) - α)) zero_le_one, ENNReal.ofReal_one,
        mul_assoc, ENNReal.sub_mul (fun _ _ => ENNReal.ofReal_ne_top), one_mul,
        ← ENNReal.ofReal_mul hgn,
        mul_comm (‖x‖ ^ (-(finrank ℝ E : ℝ) - α)) (P x)]
    have hsub_meas : Measurable (fun x : E =>
        ENNReal.ofReal (P x * ‖x‖ ^ (-(finrank ℝ E : ℝ) - α)) - ENNReal.ofReal (P x)) := by
      fun_prop
    rw [lintegral_congr_ae hpt, lintegral_const_mul _ hsub_meas,
      lintegral_sub hG_meas hG_top hGF]
  -- Step D: the radial computation and the Bochner/lintegral bridge
  have hs : (0:ℝ) < (finrank ℝ E : ℝ) + α := by linarith
  have hsk : (finrank ℝ E : ℝ) + α < k + (finrank ℝ E : ℝ) := by linarith
  have hradial := lintegral_ball_hom_rpow (μ := μ) hP hPm hhom hs hsk (R := 1) one_pos
  have hexp2 : -(finrank ℝ E : ℝ) - α = -((finrank ℝ E : ℝ) + α) := by ring
  have hradial' : ∫⁻ x in ball (0 : E) 1,
        ENNReal.ofReal (P x * ‖x‖ ^ (-(finrank ℝ E : ℝ) - α)) ∂μ
      = ENNReal.ofReal ((k + (finrank ℝ E : ℝ)) / (k + (finrank ℝ E : ℝ)
          - ((finrank ℝ E : ℝ) + α))) *
        ∫⁻ x in ball (0 : E) 1, ENNReal.ofReal (P x) ∂μ := by
    simpa only [hexp2, Real.one_rpow, mul_one] using hradial
  have hexp : (k + (finrank ℝ E : ℝ)) - ((finrank ℝ E : ℝ) + α) = k - α := by ring
  have hI : ∫⁻ x in ball (0 : E) 1, ENNReal.ofReal (P x) ∂μ = ENNReal.ofReal J := by
    rw [hJdef, ← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hP)]
  rw [stepA, stepB, stepC, hradial', hI, hexp]
  -- final real arithmetic
  have hA_nn : (0:ℝ) ≤ (k + (finrank ℝ E : ℝ)) / (k - α) :=
    div_nonneg (by linarith) (by linarith)
  have hAJ : (0:ℝ) ≤ (k + (finrank ℝ E : ℝ)) / (k - α) * J := mul_nonneg hA_nn hJ_nn
  have hAJ_sub : (0:ℝ) ≤ (k + (finrank ℝ E : ℝ)) / (k - α) * J - J := by
    have h1 : (1:ℝ) ≤ (k + (finrank ℝ E : ℝ)) / (k - α) := by
      rw [le_div_iff₀ (by linarith : (0:ℝ) < k - α)]
      linarith
    nlinarith
  rw [← ENNReal.ofReal_mul hA_nn,
    ← ENNReal.ofReal_sub ((k + (finrank ℝ E : ℝ)) / (k - α) * J) hJ_nn,
    ← ENNReal.ofReal_mul (p := α / ((finrank ℝ E : ℝ) + α))
      (div_nonneg hα.le (by positivity))]
  congr 1
  have h1 : k - α ≠ 0 := by linarith
  have h2 : (finrank ℝ E : ℝ) + α ≠ 0 := by positivity
  field_simp
  ring

/-- **The paper's `2p`-th moment identity**: for a continuous linear functional `ℓ` playing the
role of `x ↦ ⟨u,x⟩` (the paper allows an arbitrary norm, so linear functionals are the correct
generality), with `P x = (ℓ x)^{2p}`, `k = 2p`:
`∫ (ℓ x)^{2p} dΠ₁ = α/(2p-α) ∫_B (ℓ y)^{2p} dy` for `0 < α < 2`, `p ≥ 1`. -/
theorem lintegral_moment_PiOne (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ} (hα : 0 < α)
    (hα2 : α < 2) (ℓ : E →L[ℝ] ℝ) (p : ℕ) (hp : 1 ≤ p) :
    ∫⁻ x, ENNReal.ofReal ((ℓ x) ^ (2 * p)) ∂(PiOne α μ)
      = ENNReal.ofReal (α / (((2 * p : ℕ) : ℝ) - α)
          * ∫ x in ball (0 : E) 1, (ℓ x) ^ (2 * p) ∂μ) := by
  have hk : α < ((2 * p : ℕ) : ℝ) := by
    have h2 : (2:ℝ) ≤ ((2 * p : ℕ) : ℝ) := by
      have : (2:ℕ) ≤ 2 * p := by omega
      exact_mod_cast this
    linarith
  have hhom : ∀ (c : ℝ), 0 < c → ∀ x : E,
      (ℓ (c • x)) ^ (2 * p) = c ^ (((2 * p : ℕ)) : ℝ) * (ℓ x) ^ (2 * p) := by
    intro c hc x
    rw [ContinuousLinearMap.map_smul, smul_eq_mul, mul_pow, ← Real.rpow_natCast]
  have hint : IntegrableOn (fun x : E => (ℓ x) ^ (2 * p)) (ball (0 : E) 1) μ := by
    have hcont : Continuous fun x : E => (ℓ x) ^ (2 * p) := by fun_prop
    exact (hcont.continuousOn.integrableOn_compact (isCompact_closedBall 0 1)).mono_set
      ball_subset_closedBall
  have hP_nn : ∀ x : E, 0 ≤ (ℓ x) ^ (2 * p) := fun x => by
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg _) p
  exact lintegral_PiOne_of_hom μ hα hα2 hP_nn (by fun_prop) hk hhom hint

/-! ## The Riesz / Green kernel of the limiting displacement law

The paper's `G` (Section I.5.4) is the Green function of the limiting spatial motion, and in the
two regimes it is a Riesz kernel `‖x‖^{β-d}` with `β = min {2, α}` (α-stable Lévy motion for
`α < 2`, Brownian motion for `α ≥ 2`). Lemma I.5.35 says that the density `κ` of the limiting
displacement law `ν_disp` rescales to `G`: `λ^{min{2,α}-d} κ(λ^{-1}x) → G(x)`, i.e. `κ` behaves
like a kernel that is homogeneous of degree `min{2,α}-d`, which is exactly the homogeneity
recorded in `rieszKernel_smul`. We record the quantitative facts about this kernel used by the
diagram moment bounds (Lemma I.5.34 and its proof). -/

/-- The Riesz kernel of exponent `β`. -/
noncomputable def rieszKernel (β : ℝ) : E → ℝ := fun x => ‖x‖ ^ (β - (finrank ℝ E : ℝ))

theorem rieszKernel_nonneg (β : ℝ) (x : E) : 0 ≤ rieszKernel (E := E) β x :=
  Real.rpow_nonneg (norm_nonneg x) _

/-- **Homogeneity of the Green function of degree `β - d`** — the content of the rescaling
statement of Lemma I.5.35. -/
theorem rieszKernel_smul (β c : ℝ) (hc : 0 < c) (x : E) :
    rieszKernel (E := E) β (c • x) = c ^ (β - (finrank ℝ E : ℝ)) * rieszKernel (E := E) β x := by
  unfold rieszKernel
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc, Real.mul_rpow hc.le (norm_nonneg x)]

/-- **The Green-function moment bound / mass of the Riesz kernel on a ball**:
`∫_{‖x‖ ≤ R} ‖x‖^{β-d} dx = (d/β) R^β |B₁|` for `0 < β < d`.
This is the bound that makes each diagram in the moment formula (I.1.11) contribute at most a
constant times `R^β` per edge, i.e. the "moment bound" input of Lemma I.5.34. -/
theorem lintegral_ball_riesz (μ : Measure E) [μ.IsAddHaarMeasure] {β : ℝ} (hβ : 0 < β)
    (hβd : β < (finrank ℝ E : ℝ)) {R : ℝ} (hR : 0 < R) :
    ∫⁻ x in ball (0 : E) R, ENNReal.ofReal (rieszKernel (E := E) β x) ∂μ
      = ENNReal.ofReal ((finrank ℝ E : ℝ) / β * R ^ β)
        * ∫⁻ x in ball (0 : E) 1, ENNReal.ofReal (1 : ℝ) ∂μ := by
  have hd : (0:ℝ) < (finrank ℝ E : ℝ) := by
    exact_mod_cast Module.finrank_pos (R := ℝ) (M := E)
  have hs : (0:ℝ) < (finrank ℝ E : ℝ) - β := by linarith
  have hsk : (finrank ℝ E : ℝ) - β < (0:ℝ) + (finrank ℝ E : ℝ) := by linarith
  have hexp : -((finrank ℝ E : ℝ) - β) = β - (finrank ℝ E : ℝ) := by ring
  have h1 : (finrank ℝ E : ℝ) - ((finrank ℝ E : ℝ) - β) = β := by ring
  have hmain : ∫⁻ x in ball (0 : E) R,
        ENNReal.ofReal (‖x‖ ^ (β - (finrank ℝ E : ℝ))) ∂μ
      = ENNReal.ofReal ((finrank ℝ E : ℝ) / β * R ^ β)
        * ∫⁻ x in ball (0 : E) 1, ENNReal.ofReal (1 : ℝ) ∂μ := by
    have h := lintegral_ball_hom_rpow (μ := μ) (P := fun _ : E => (1:ℝ))
      (fun _ => zero_le_one) measurable_const (k := 0) ?_ hs hsk hR
    · simpa only [hexp, h1, one_mul, Real.rpow_zero, mul_one, zero_add] using h
    · intro c hc x
      simp only [Real.rpow_zero, mul_one]
  simpa only [rieszKernel] using hmain

/-- **`Π₁` is a genuine Lévy measure** (the paper's claim after (I.5.16)): for `0 < α < 2`,
`∫ (‖x‖² ∧ 1) dΠ₁ < ∞`. Its density is supported in the unit ball, so the `∧ 1` is not needed
there; the bound follows from the second-moment computation below. -/
theorem lintegral_norm_sq_PiOne (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ} (hα : 0 < α)
    (hα2 : α < 2) :
    ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂(PiOne α μ)
      = ENNReal.ofReal (α / (2 - α) * ∫ x in ball (0 : E) 1, ‖x‖ ^ 2 ∂μ) := by
  have hk : α < (2 : ℝ) := by linarith
  have hhom : ∀ (c : ℝ), 0 < c → ∀ x : E, ‖c • x‖ ^ 2 = c ^ (2:ℝ) * ‖x‖ ^ 2 := by
    intro c hc x
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc, mul_pow, ← Real.rpow_natCast]
    norm_num
  have hint : IntegrableOn (fun x : E => ‖x‖ ^ 2) (ball (0 : E) 1) μ := by
    have hcont : Continuous fun x : E => ‖x‖ ^ 2 := by fun_prop
    exact (hcont.continuousOn.integrableOn_compact (isCompact_closedBall 0 1)).mono_set
      ball_subset_closedBall
  exact lintegral_PiOne_of_hom μ hα hα2 (fun x => by positivity) (by fun_prop) hk hhom hint

/-- `Π₁` is a Lévy measure: `∫ (‖x‖² ∧ 1) dΠ₁ < ∞` for `0 < α < 2`. -/
theorem PiOne_levy_measure (μ : Measure E) [μ.IsAddHaarMeasure] {α : ℝ} (hα : 0 < α)
    (hα2 : α < 2) :
    ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂(PiOne α μ) ≠ ⊤ := by
  have h1 : ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂(PiOne α μ)
      ≤ ENNReal.ofReal (α / (2 - α) * ∫ x in ball (0 : E) 1, ‖x‖ ^ 2 ∂μ) :=
    calc ∫⁻ x, ENNReal.ofReal (min (‖x‖ ^ 2) 1) ∂(PiOne α μ)
        ≤ ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂(PiOne α μ) :=
          lintegral_mono fun x => ENNReal.ofReal_le_ofReal (min_le_left _ _)
      _ = ENNReal.ofReal (α / (2 - α) * ∫ x in ball (0 : E) 1, ‖x‖ ^ 2 ∂μ) :=
          lintegral_norm_sq_PiOne μ hα hα2
  exact ne_of_lt (lt_of_le_of_lt h1 ENNReal.ofReal_lt_top)

/-- An additive Haar measure is invariant under `x ↦ -x`. -/
theorem map_neg_eq_self_haar (μ : Measure E) [μ.IsAddHaarMeasure] :
    Measure.map (fun x : E => -x) μ = μ := by
  have h := Measure.map_addHaar_smul μ (r := (-1 : ℝ))
  simpa using h

/-- **`Π₁` is a symmetric (radially even) measure** — its density depends only on `‖x‖`.
This is the symmetry input needed to cancel the odd part of `e^{⟨u,x⟩} - 1 - ⟨u,x⟩`
in the identity (I.5.17). -/
theorem PiOne_symm (μ : Measure E) [μ.IsAddHaarMeasure] (α : ℝ) :
    Measure.map (fun x : E => -x) (PiOne α μ) = PiOne α μ := by
  have hρ : ∀ x : E, levyDensLam (E := E) α 1 (-x) = levyDensLam (E := E) α 1 x := by
    intro x
    simp only [levyDensLam, norm_neg]
  have hρm : Measurable (levyDensLam (E := E) α 1) := measurable_levyDensLam α 1
  rw [PiOne, PiLam]
  refine Measure.ext fun s hs => ?_
  rw [Measure.map_apply measurable_neg hs, withDensity_apply _ (measurable_neg hs),
    withDensity_apply _ hs]
  have hstep : ∫⁻ x in (fun x : E => -x) ⁻¹' s, levyDensLam (E := E) α 1 x ∂μ
      = ∫⁻ x, (s.indicator (levyDensLam (E := E) α 1)) (-x) ∂μ := by
    rw [← lintegral_indicator (measurable_neg hs)]
    apply lintegral_congr
    intro x
    by_cases hx : x ∈ (fun x : E => -x) ⁻¹' s
    · have hx' : -x ∈ s := hx
      rw [indicator_of_mem hx, Set.indicator_of_mem hx', hρ]
    · have hx' : -x ∉ s := hx
      rw [indicator_of_notMem hx, Set.indicator_of_notMem hx']
  rw [hstep, ← lintegral_map (f := s.indicator (levyDensLam (E := E) α 1))
    (g := fun x : E => -x) (hρm.indicator hs) measurable_neg,
    map_neg_eq_self_haar μ, lintegral_indicator hs]

end PercLib.CriticalLRP.LevyAnalysis
