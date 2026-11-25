/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0 license.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.ScalarFactor.Defs
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.EdgeMajorant
public import PercLib.CriticalLRP.Analysis.Cutoff.ConnMassRegularity.Main

/-!
# The off-corner scalar factor `β_c (-K'(r)) (exclMass r).toReal`, outside the flux series

This file works the *scalar* (outer) factor of the off-corner Russo derivative
`(∑'_y flux_y r) = β_c (-K'(r)) (exclMass r).toReal`, i.e. the part of the right-hand side that
does not involve the vertex series at all.  Three things are proved, and one gap is isolated.

## 1. The window bound (this file's main content)

`exclMass_le_ball_mul_cutMoment_two`: on any radius window `r ≤ b`,
`exclMass r ≤ |B_b| · (cutMoment 2 b)²`, hence the real form
`exclScalar_le_of_le`: `(exclMass r).toReal ≤ |B_b| · (cutMoment 2 b).toReal²`, and the companion
`connMass_le_window`: `connMass r ≤ |B_b| · cutMoment 2 b`.  `exclMass_ne_top_of_le` is the
window form of the finiteness input `hE`.

Only the moment at the *single radius* `b` enters: `cutMoment 2` is monotone in the radius
(`cutMoment_monotone`), `cutMassAt r 0 ≤ cutMoment 2 r`, and `exclMass ≤ |B_r| (cutMassAt r 0)²`
is the landed Lemma I.4.7 inequality `E1Sign.exclMass_le`.  Combining with a bound `|K'| ≤ C` on
the window gives `abs_rhsScalar_le_of_window`, a bound for the whole scalar factor on the window
that is independent of `r` and therefore usable as an `r`-dominator.

## 2. What this does *not* give

No continuity of `r ↦ (exclMass r).toReal` is proved, and it is not derivable from what is
landed.  `continuousAt_rhsScalar_iff` shows that, given that `r ↦ K'(r)` is continuous at `r₀`
and `K'(r₀) ≠ 0`, the continuity of the scalar factor at `r₀` is *exactly* the continuity of
`r ↦ (exclMass r).toReal` there: the whole analytic content is in `exclMass`.  The excluded mass
is an `∫⁻` with a weight `clusterVol ω y` that is unbounded on the mark space and a moving
window `B_r`; the landed `connMass` regularity (`ConnMassRegularity/Main`) covers the *included*
indicator `1(y ∈ K)` with weight `|K|²`, not the excluded one, and it needs the strict window
`ballFLt` precisely because the closed window `B_r` jumps.  So the honest input is the
`connMass`-analogue for `exclMass`, and it is expected to hold only off the sphere radii.

Note that `K_diff` in `SourceModelData` gives *differentiability* of `K` on `Ioi 0`, not continuity
of `deriv K`; `continuousAt_rhsScalar_iff` therefore names `ContinuousAt (deriv M.K) r₀` as an
explicit hypothesis rather than deriving it.

## 3. Three inputs of the landed conditional derivative, derived

On the series side this file removes three hypotheses of
`hasDerivAt_cutMassReal_eq_betaCrit_mul_exclMass_of_cutMoment_two` instead of adding a majorant:

* `hfluxnn` (`0 ≤ flux_y r`) from `pairFlux_nonneg` and the `rfl` identification of the singleton
  flux with the edge series;
* `hmeasinf` from per-`y` continuity (`ContinuousAt.stronglyMeasurableAtFilter`);
* `hfluxintW` from per-`y` continuity (`ContinuousOn.intervalIntegrable` on the compact
  `uIcc a' b' ⊆ Ioo α β`);
* and the pointwise moment hypothesis `h2 : ∀ r ∈ Ioo α β, cutMoment 2 r ≠ ⊤` is replaced by its
  value at the single endpoint `β`, by monotonicity.

The result is `hasDerivAt_cutMassReal_eq_betaCrit_mul_exclMass_of_endpoint`, whose remaining
inputs are exactly `hboundint` (interval integrability of the dominator `sMomentWeight`),
`hmeasK` (window-flux measurability), `hcontinf` (per-`y` flux continuity) and `hGcont` (summed
flux continuity).  `hasDerivAt_cutMassReal_rhsScalar_of_endpoint` is the same statement with the
derivative value written as the scalar factor `M.rhsScalar r₀` of §1.
-/

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

attribute [local instance] Classical.propDecidable

/-! ## 1. Window bound for the scalar factor -/

/-- **The excluded mass on a window is bounded by the second moment at the outer endpoint.**

`exclMass r ≤ |B_r| (cutMassAt r 0)² ≤ |B_b| (cutMoment 2 b)²` for `r ≤ b`: the landed
Lemma I.4.7 inequality, monotonicity of the ball, and monotonicity of `cutMoment 2` in the radius.
Only the moment at `b` is used; no moment is assumed at `r` itself. -/
theorem exclMass_le_ball_mul_cutMoment_two {r b : ℝ} (hrb : r ≤ b)
    (h2b : M.cutMoment 2 b ≠ ⊤) :
    E1Sign.exclMass M r ≤ ((M.ball b).ncard : ℝ≥0∞) * (M.cutMoment 2 b) ^ 2 := by
  have h2r : M.cutMoment 2 r ≠ ⊤ := M.cutMoment_ne_top_of_le hrb 2 h2b
  have hT : E1Sign.connMass M r ≠ ⊤ := E1Sign.connMass_ne_top M r h2r
  have hcard : ((M.ball r).ncard : ℝ≥0∞) ≤ ((M.ball b).ncard : ℝ≥0∞) := by
    exact_mod_cast Set.ncard_le_ncard (PercLib.CriticalLRP.BallAverage.ball_mono M hrb)
      (M.finite_ball b)
  have hcut : M.cutMassAt r 0 ≤ M.cutMoment 2 b :=
    le_trans (E1Sign.cutMassAt_le_cutMoment_two M r) (M.cutMoment_monotone 2 hrb)
  calc E1Sign.exclMass M r
      ≤ ((M.ball r).ncard : ℝ≥0∞) * (M.cutMassAt r 0) ^ 2 := E1Sign.exclMass_le M r hT
    _ ≤ ((M.ball b).ncard : ℝ≥0∞) * (M.cutMoment 2 b) ^ 2 :=
        mul_le_mul hcard (pow_le_pow_left' hcut 2) bot_le bot_le

/-- The window bound of `exclMass` in `ℝ`, ready to be used as a scalar majorant. -/
theorem exclScalar_le_of_le {r b : ℝ} (hrb : r ≤ b) (h2b : M.cutMoment 2 b ≠ ⊤) :
    M.exclScalar r ≤ ((M.ball b).ncard : ℝ) * (M.cutMoment 2 b).toReal ^ 2 := by
  have htop : ((M.ball b).ncard : ℝ≥0∞) * (M.cutMoment 2 b) ^ 2 ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top h2b)
  have h := ENNReal.toReal_mono htop (M.exclMass_le_ball_mul_cutMoment_two hrb h2b)
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_natCast] at h
  simpa [exclScalar] using h

/-- **The scalar factor is bounded on a radius window by one endpoint moment and one bound on
`|K'|`.**  This is the `r`-dominator for `β_c (-K'(r)) (exclMass r).toReal`; no moment is assumed
at any interior radius and no uniformity over corner radii is claimed. -/
theorem abs_rhsScalar_le_of_window {a b C : ℝ} (ha : 0 ≤ a)
    (hC : ∀ r ∈ Set.Icc a b, |deriv M.K r| ≤ C) (hCnn : 0 ≤ C)
    (h2b : M.cutMoment 2 b ≠ ⊤) (hN : 0 ≤ ((M.ball b).ncard : ℝ)) :
    ∀ r ∈ Set.Icc a b, |M.rhsScalar r| ≤
      (M.betaCrit : ℝ) * C * (((M.ball b).ncard : ℝ) * (M.cutMoment 2 b).toReal ^ 2) := by
  intro r hr
  have hrb : r ≤ b := hr.2
  have h0r : 0 ≤ r := le_trans ha hr.1
  have hex := M.exclScalar_le_of_le hrb h2b
  have hexnn : 0 ≤ M.exclScalar r := ENNReal.toReal_nonneg
  have hβ : (0 : ℝ) ≤ (M.betaCrit : ℝ) := M.betaCrit.coe_nonneg
  have hK' : |deriv M.K r| ≤ C := hC r hr
  have hcoeff : |M.coeffRHS r| ≤ (M.betaCrit : ℝ) * C := by
    rw [coeffRHS, abs_mul, abs_neg, abs_of_nonneg hβ]
    exact mul_le_mul_of_nonneg_left hK' hβ
  have hstuff : 0 ≤ ((M.ball b).ncard : ℝ) * (M.cutMoment 2 b).toReal ^ 2 :=
    mul_nonneg hN (sq_nonneg _)
  calc |M.rhsScalar r| = |M.coeffRHS r| * M.exclScalar r := by
        rw [rhsScalar, abs_mul, abs_of_nonneg hexnn]
    _ ≤ ((M.betaCrit : ℝ) * C) * (((M.ball b).ncard : ℝ) * (M.cutMoment 2 b).toReal ^ 2) :=
        mul_le_mul hcoeff hex hexnn (by positivity : (0 : ℝ) ≤ (M.betaCrit : ℝ) * C)
    _ = (M.betaCrit : ℝ) * C *
          (((M.ball b).ncard : ℝ) * (M.cutMoment 2 b).toReal ^ 2) := by ring

/-- The excluded mass is finite on the whole window once the second moment is finite at the outer
endpoint.  This is the hypothesis `hE`/`hfin` of the landed conditional derivative, on a window
and from one endpoint value. -/
theorem exclMass_ne_top_of_le {r b : ℝ} (hrb : r ≤ b) (h2b : M.cutMoment 2 b ≠ ⊤) :
    E1Sign.exclMass M r ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top h2b))
    (M.exclMass_le_ball_mul_cutMoment_two hrb h2b)

/-- The connection mass on a window, bounded by the second moment at the outer endpoint. -/
theorem connMass_le_window {r b : ℝ} (hrb : r ≤ b) :
    E1Sign.connMass M r ≤ ((M.ball b).ncard : ℝ≥0∞) * M.cutMoment 2 b := by
  have hcard : ((M.ball r).ncard : ℝ≥0∞) ≤ ((M.ball b).ncard : ℝ≥0∞) := by
    exact_mod_cast Set.ncard_le_ncard (PercLib.CriticalLRP.BallAverage.ball_mono M hrb)
      (M.finite_ball b)
  calc E1Sign.connMass M r
      ≤ ((M.ball r).ncard : ℝ≥0∞) * M.cutMoment 2 r := E1Sign.connMass_le M r
    _ ≤ ((M.ball b).ncard : ℝ≥0∞) * M.cutMoment 2 b :=
        mul_le_mul hcard (M.cutMoment_monotone 2 hrb) bot_le bot_le

/-! ## 2. Where the continuity of the scalar factor really sits -/

/-- If `a` is continuous and nonzero at `x`, then `a · b` is continuous at `x` iff `b` is. -/
theorem continuousAt_mul_iff_of_left {a b : ℝ → ℝ} {x : ℝ}
    (ha : ContinuousAt a x) (hax : a x ≠ 0) :
    ContinuousAt (fun t => a t * b t) x ↔ ContinuousAt b x := by
  constructor
  · intro hab
    have hev : (fun t => a t * b t / a t) =ᶠ[𝓝 x] b := by
      filter_upwards [ha.eventually_ne hax] with t ht
      rw [mul_div_cancel_left₀ _ ht]
    have hdiv : ContinuousAt (fun t => a t * b t / a t) x := hab.div ha hax
    exact hdiv.congr hev
  · intro hb
    exact ha.mul hb

/-- **The continuity of the scalar factor is exactly the continuity of the excluded mass.**

Given `β_c ≠ 0`, `r ↦ K'(r)` continuous at `r₀` and `K'(r₀) ≠ 0`, the scalar factor
`β_c (-K'(r)) (exclMass r).toReal` is continuous at `r₀` if and only if
`r ↦ (exclMass r).toReal` is.  No continuity of `exclMass` is proved here; this isolates the
missing input. -/
theorem continuousAt_rhsScalar_iff {r₀ : ℝ} (hβ : (M.betaCrit : ℝ) ≠ 0)
    (hK : ContinuousAt (fun r => deriv M.K r) r₀) (hK0 : deriv M.K r₀ ≠ 0) :
    ContinuousAt M.rhsScalar r₀ ↔ ContinuousAt M.exclScalar r₀ := by
  have hcoeff : ContinuousAt M.coeffRHS r₀ := by
    have h : ContinuousAt (fun r => (M.betaCrit : ℝ) * (-(deriv M.K r))) r₀ :=
      continuousAt_const.mul hK.neg
    exact h
  have hne : M.coeffRHS r₀ ≠ 0 := by
    rw [coeffRHS]
    exact mul_ne_zero hβ (neg_ne_zero.mpr hK0)
  have h : ContinuousAt (fun t => M.coeffRHS t * M.exclScalar t) r₀ ↔
      ContinuousAt M.exclScalar r₀ := continuousAt_mul_iff_of_left hcoeff hne
  exact h

/-- The usable direction: continuity of `K'` and of the excluded mass gives continuity of the
scalar factor of the derivative value. -/
theorem continuousAt_rhsScalar {r₀ : ℝ} (hK : ContinuousAt (fun r => deriv M.K r) r₀)
    (hex : ContinuousAt M.exclScalar r₀) : ContinuousAt M.rhsScalar r₀ := by
  have hcoeff : ContinuousAt M.coeffRHS r₀ := by
    have h : ContinuousAt (fun r => (M.betaCrit : ℝ) * (-(deriv M.K r))) r₀ :=
      continuousAt_const.mul hK.neg
    exact h
  exact hcoeff.mul hex

/-! ## 3. Scalar inputs of the landed derivative, derived instead of assumed -/

/-- The singleton flux is nonnegative off the corner: it is the edge series of the nonnegative
`pairFlux`.  This is the hypothesis `hfluxnn` of the landed conditional derivative. -/
theorem nonneg_sMomentInfFlux (r : ℝ) (hr : 0 < r) (y : M.V) :
    0 ≤ sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
      M.cutProb M.cutEdgeDeriv r := by
  rw [PercLib.CriticalLRP.Orchestration.sMomentInfFlux_eq_tsum_pairIncrFlux M {y} r]
  exact tsum_nonneg fun e => M.pairFlux_nonneg hr y e

/-- Per-`y` flux continuity gives the strong measurability input `hmeasinf`
of the landed conditional derivative. -/
theorem stronglyMeasurableAt_sMomentInfFlux {α β : ℝ}
    (hcontinf : ∀ y : M.V, ∀ r ∈ Set.Ioo α β, ContinuousAt
      (sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv) r) :
    ∀ y : M.V, ∀ r ∈ Set.Ioo α β, StronglyMeasurableAtFilter
      (sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv) (𝓝 r) volume :=
  fun y => ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo (hcontinf y)

/-- Per-`y` flux continuity gives the interval integrability `hfluxintW`
of the landed conditional derivative, on any compact interval inside the off-corner window. -/
theorem intervalIntegrable_sMomentInfFlux {α β : ℝ}
    (hcontinf : ∀ y : M.V, ∀ r ∈ Set.Ioo α β, ContinuousAt
      (sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv) r)
    (y : M.V) {a' b' : ℝ} (ha' : a' ∈ Set.Ioo α β) (hb' : b' ∈ Set.Ioo α β) :
    IntervalIntegrable (fun r =>
      sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv r) volume a' b' := by
  have hsub : Set.uIcc a' b' ⊆ Set.Ioo α β := by
    intro x hx
    rcases le_total a' b' with h | h
    · rw [Set.uIcc_of_le h] at hx
      exact ⟨lt_of_lt_of_le ha'.1 hx.1, lt_of_le_of_lt hx.2 hb'.2⟩
    · rw [Set.uIcc_of_ge h] at hx
      exact ⟨lt_of_lt_of_le hb'.1 hx.1, lt_of_le_of_lt hx.2 ha'.2⟩
  exact ContinuousOn.intervalIntegrable fun x hx =>
    (hcontinf y x (hsub hx)).continuousWithinAt

/-! ## 4. The landed off-corner derivative with three inputs derived and the moment at one
endpoint only

The moment hypothesis `∀ r ∈ Ioo α β, cutMoment 2 r ≠ ⊤` is replaced by `cutMoment 2 β ≠ ⊤`,
`hfluxnn`, `hmeasinf` and `hfluxintW` are deleted.  What is left is exactly: the dominator's
interval integrability `hboundint`, window-flux measurability `hmeasK`, per-`y` flux continuity
`hcontinf` and summed flux continuity `hGcont`. -/
theorem hasDerivAt_cutMassReal_eq_betaCrit_mul_exclMass_of_endpoint
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {α β r0 : ℝ} (hα0 : 0 < α) (hαr0 : α < r0) (hr0β : r0 < β)
    (hoff : ∀ r ∈ Set.Ioo α β, r ∉ M.cornerRadii)
    (hKd : ∀ r ∈ Set.Ioo α β, DifferentiableAt ℝ M.K r)
    (h2β : M.cutMoment 2 β ≠ ⊤)
    (hboundint : ∀ y : M.V, ∀ a' ∈ Set.Ioo α β, ∀ b' ∈ Set.Ioo α β, IntervalIntegrable
      (sMomentWeight (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) volume a' b')
    (hmeasK : ∀ y : M.V, ∀ k : ℕ, AEStronglyMeasurable (windowFluxOf (0 : M.V)
      (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) {y}) S M.cutProb M.cutEdgeDeriv k) volume)
    (hcontinf : ∀ y : M.V, ∀ r ∈ Set.Ioo α β, ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hGcont : ∀ r ∈ Set.Ioo α β, ContinuousAt (fun r' => ∑' y : M.V,
      sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r') r) :
    HasDerivAt M.cutMassReal
      ((M.betaCrit : ℝ) * (-(deriv M.K r0)) * (E1Sign.exclMass M r0).toReal) r0 := by
  refine M.hasDerivAt_cutMassReal_eq_betaCrit_mul_exclMass_of_cutMoment_two T hTmono hT
    S hSmono hS hα0 hαr0 hr0β hoff hKd ?_ hboundint hmeasK ?_ hcontinf ?_ ?_ hGcont
  · exact fun r hr => M.cutMoment_ne_top_of_le (le_of_lt hr.2) 2 h2β
  · exact M.stronglyMeasurableAt_sMomentInfFlux hcontinf
  · exact fun y r hr => M.nonneg_sMomentInfFlux r (lt_trans hα0 hr.1) y
  · exact fun y a' ha' b' hb' => M.intervalIntegrable_sMomentInfFlux hcontinf y ha' hb'

/-- The same off-corner derivative, with the derivative value written as the scalar factor
`M.rhsScalar r0 = β_c (-K'(r0)) (exclMass r0).toReal` of §1. -/
theorem hasDerivAt_cutMassReal_rhsScalar_of_endpoint
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {α β r0 : ℝ} (hα0 : 0 < α) (hαr0 : α < r0) (hr0β : r0 < β)
    (hoff : ∀ r ∈ Set.Ioo α β, r ∉ M.cornerRadii)
    (hKd : ∀ r ∈ Set.Ioo α β, DifferentiableAt ℝ M.K r)
    (h2β : M.cutMoment 2 β ≠ ⊤)
    (hboundint : ∀ y : M.V, ∀ a' ∈ Set.Ioo α β, ∀ b' ∈ Set.Ioo α β, IntervalIntegrable
      (sMomentWeight (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) volume a' b')
    (hmeasK : ∀ y : M.V, ∀ k : ℕ, AEStronglyMeasurable (windowFluxOf (0 : M.V)
      (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) {y}) S M.cutProb M.cutEdgeDeriv k) volume)
    (hcontinf : ∀ y : M.V, ∀ r ∈ Set.Ioo α β, ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hGcont : ∀ r ∈ Set.Ioo α β, ContinuousAt (fun r' => ∑' y : M.V,
      sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r') r) :
    HasDerivAt M.cutMassReal (M.rhsScalar r0) r0 :=
  M.hasDerivAt_cutMassReal_eq_betaCrit_mul_exclMass_of_endpoint T hTmono hT S hSmono hS
    hα0 hαr0 hr0β hoff hKd h2β hboundint hmeasK hcontinf hGcont

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

set_option linter.hashCommand false

namespace PercLib.CriticalLRP.Orchestration

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exclMass_le_ball_mul_cutMoment_two
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exclScalar_le_of_le
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.abs_rhsScalar_le_of_window
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exclMass_ne_top_of_le
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.connMass_le_window
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.continuousAt_mul_iff_of_left
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.continuousAt_rhsScalar_iff
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.continuousAt_rhsScalar
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.nonneg_sMomentInfFlux
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.stronglyMeasurableAt_sMomentInfFlux
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.intervalIntegrable_sMomentInfFlux
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.hasDerivAt_cutMassReal_eq_betaCrit_mul_exclMass_of_endpoint
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.hasDerivAt_cutMassReal_rhsScalar_of_endpoint

end PercLib.CriticalLRP.Orchestration
