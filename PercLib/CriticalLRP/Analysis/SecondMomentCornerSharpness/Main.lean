/-
Accepted and independently rebuilt from Ultramath `smwywszgo`, member `m4`.

Sharpness witnesses for the corner hypotheses of the two radius bridges.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Swarm `smwywszgo`, member `m4`, direction `d10`.  Definitions live in `Sharpness/Defs.lean`.

No `sorry`, no `admit`, no `native_decide`, no custom axiom.
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.Analysis.Calculus.Deriv.Abs
public import PercLib.CriticalLRP.Analysis.SecondMomentCornerSharpness.Defs

/-!
# Sharpness witnesses for the corner hypotheses of the two radius bridges

`no_gluing_without_continuity`, `no_corner_transfer_without_continuity` and
`no_pointwise_derivative_at_corner` are the three headlines; §§1-2 build the witnesses.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology NNReal

set_option linter.style.longLine false
set_option linter.unusedVariables false

namespace PercLib.CriticalLRP.Orchestration.SmwywszgoM4

/-! ## 1. The half-line indicator

`stepAt c` is monotone and constant on each side of `c`, so it is absolutely continuous on every
closed window that avoids `c`.  It is not continuous at `c`, and consequently not absolutely
continuous on any window whose interior contains `c`. -/

theorem stepAt_eq_one {c x : ℝ} (h : c < x) : stepAt c x = 1 := by simp [stepAt, h]

theorem stepAt_eq_zero {c x : ℝ} (h : x ≤ c) : stepAt c x = 0 := by simp [stepAt, h]

theorem monotone_stepAt (c : ℝ) : Monotone (stepAt c) := by
  intro x y hxy
  rcases lt_or_ge c y with hy | hy
  · rw [stepAt_eq_one hy]
    rcases lt_or_ge c x with hx | hx
    · rw [stepAt_eq_one hx]
    · rw [stepAt_eq_zero hx]; norm_num
  · rw [stepAt_eq_zero hy, stepAt_eq_zero (le_trans hxy hy)]

/-- `stepAt c` does not change along a closed window that avoids `c`. -/
theorem eqOn_stepAt_Icc_of_notMem {c u v : ℝ} (huv : u ≤ v) (h : c ∉ Icc u v) :
    ∀ x ∈ Icc u v, stepAt c x = stepAt c u := by
  intro x hx
  rcases lt_or_ge v c with hv | hv
  · rw [stepAt_eq_zero (le_trans hx.2 hv.le),
      stepAt_eq_zero (le_trans (le_trans hx.1 hx.2) hv.le)]
  · have hcu : c < u := by
      rcases lt_or_ge c u with h' | h'
      · exact h'
      · exact absurd ⟨h', hv⟩ h
    rw [stepAt_eq_one (lt_of_lt_of_le hcu hx.1), stepAt_eq_one hcu]

/-- **Absolute continuity of the indicator on corner-free windows.** -/
theorem absolutelyContinuousOnInterval_stepAt_of_notMem {c u v : ℝ} (huv : u ≤ v)
    (h : c ∉ Icc u v) : AbsolutelyContinuousOnInterval (stepAt c) u v := by
  rcases lt_or_ge v c with hv | hv
  · refine ((LipschitzWith.const (0 : ℝ)).lipschitzOnWith
      (s := uIcc u v)).absolutelyContinuousOnInterval.congr ?_
    intro x hx
    rw [uIcc_of_le huv] at hx
    exact (stepAt_eq_zero (le_trans hx.2 hv.le)).symm
  · have hcu : c < u := by
      rcases lt_or_ge c u with h' | h'
      · exact h'
      · exact absurd ⟨h', hv⟩ h
    refine ((LipschitzWith.const (1 : ℝ)).lipschitzOnWith
      (s := uIcc u v)).absolutelyContinuousOnInterval.congr ?_
    intro x hx
    rw [uIcc_of_le huv] at hx
    exact (stepAt_eq_one (lt_of_lt_of_le hcu hx.1)).symm

/-- **A single-interval certificate against absolute continuity.**

For every `δ > 0` there is a one-term family of disjoint `uIoc` intervals inside `[c - 1, c + 1]`
whose total length is below `δ` but along which `stepAt c` varies by exactly `1`.  This is the
concrete obstruction behind `not_absolutelyContinuousOnInterval_stepAt`. -/
theorem exists_stepAt_family_deficit (c : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ E ∈ AbsolutelyContinuousOnInterval.disjWithin (c - 1) (c + 1),
      (∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2) < δ ∧
        (1 : ℝ) ≤ ∑ i ∈ Finset.range E.1,
          dist (stepAt c (E.2 i).1) (stepAt c (E.2 i).2) := by
  set t : ℝ := min (δ / 2) (1 / 2) with ht
  have ht0 : 0 < t := lt_min (by linarith) (by norm_num)
  have htδ : t < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have ht1 : t ≤ 1 := by
    have h := min_le_right (δ / 2) (1 / 2)
    linarith
  have hleft : (c, c + t).1 ∈ uIcc (c - 1) (c + 1) := by
    rw [uIcc_of_le (by linarith : c - 1 ≤ c + 1)]
    exact ⟨by linarith, by linarith⟩
  have hright : (c, c + t).2 ∈ uIcc (c - 1) (c + 1) := by
    rw [uIcc_of_le (by linarith : c - 1 ≤ c + 1)]
    exact ⟨by linarith, by linarith⟩
  refine ⟨(1, fun _ => (c, c + t)), ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro i hi
      rw [Finset.mem_range] at hi
      obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
      exact ⟨hleft, hright⟩
    · intro i hi j hj hij
      rw [Finset.coe_range, Set.mem_Iio] at hi hj
      exact absurd (by omega : i = j) hij
  · simp only [Finset.sum_range_one]
    rw [Real.dist_eq, show c - (c + t) = -t by ring, abs_neg, abs_of_pos ht0]
    exact htδ
  · simp only [Finset.sum_range_one]
    rw [stepAt_eq_zero (le_refl c), stepAt_eq_one (by linarith : c < c + t)]
    norm_num

/-- **The indicator is not absolutely continuous across its cut point.** -/
theorem not_absolutelyContinuousOnInterval_stepAt (c : ℝ) :
    ¬ AbsolutelyContinuousOnInterval (stepAt c) (c - 1) (c + 1) := by
  intro hac
  obtain ⟨δ, hδ, hD⟩ :=
    (absolutelyContinuousOnInterval_iff (stepAt c) (c - 1) (c + 1)).mp hac (1 / 2) (by norm_num)
  obtain ⟨E, hE, hlen, hvar⟩ := exists_stepAt_family_deficit c hδ
  have hsmall := hD E hE hlen
  linarith

/-- **The integrated identity holds on every corner-free window** for the indicator and the
zero integrand: both sides vanish. -/
theorem integral_identity_stepAt_cornerFree {c u v : ℝ} (huv : u ≤ v) (h : c ∉ Icc u v) :
    ∀ x ∈ Icc u v, ∫ t in u..x, (0 : ℝ) = stepAt c x - stepAt c u := by
  intro x hx
  rw [intervalIntegral.integral_zero, eqOn_stepAt_Icc_of_notMem huv h x hx, sub_self]

/-- **The integrated identity fails on the corner-containing window.** -/
theorem integral_identity_stepAt_fails :
    ∃ x ∈ Icc (-1 : ℝ) 1, ∫ t in (-1)..x, (0 : ℝ) ≠ stepAt 0 x - stepAt 0 (-1) := by
  refine ⟨1, by norm_num, ?_⟩
  rw [intervalIntegral.integral_zero, stepAt_eq_one (by norm_num : (0 : ℝ) < 1),
    stepAt_eq_zero (by norm_num : (-1 : ℝ) ≤ 0)]
  norm_num

/-- **Off its cut point the indicator has derivative zero.** -/
theorem hasDerivAt_stepAt_of_ne {c x : ℝ} (hx : x ≠ c) : HasDerivAt (stepAt c) 0 x := by
  rcases lt_or_gt_of_ne hx with hx' | hx'
  · have hz : stepAt c =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hx'] with y hy
      exact stepAt_eq_zero hy.le
    exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hz
  · have hz : stepAt c =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hx'] with y hy
      exact stepAt_eq_one hy
    exact (hasDerivAt_const x (1 : ℝ)).congr_of_eventuallyEq hz

/-- The indicator has derivative `0` almost everywhere. -/
theorem ae_hasDerivAt_stepAt (c : ℝ) :
    ∀ᵐ x ∂(volume : Measure ℝ), HasDerivAt (stepAt c) 0 x := by
  have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ c := by
    rw [ae_iff]
    simp
  filter_upwards [hne] with x hx
  exact hasDerivAt_stepAt_of_ne hx

/-- **An almost-everywhere derivative with an integrable majorant does not give absolute
continuity.**  The indicator is monotone, differentiable with derivative `0` almost everywhere,
and `0` is interval integrable on `[-1,1]`, yet the indicator is not absolutely continuous there.
So no radius argument may replace the corner-free absolute continuity of the moment by an
a.e.-derivative statement plus `L¹`-control of the derivative. -/
theorem ae_deriv_integrable_does_not_give_ac :
    ∃ f g : ℝ → ℝ, Monotone f ∧
      (∀ᵐ x ∂(volume : Measure ℝ), HasDerivAt f (g x) x) ∧
      IntervalIntegrable g volume (-1) 1 ∧
      ¬ AbsolutelyContinuousOnInterval f (-1) 1 := by
  refine ⟨stepAt 0, fun _ => 0, monotone_stepAt 0, ae_hasDerivAt_stepAt 0, ?_, ?_⟩
  · exact intervalIntegrable_const
  · have h := not_absolutelyContinuousOnInterval_stepAt 0
    rwa [show (0 : ℝ) - 1 = -1 by norm_num, show (0 : ℝ) + 1 = 1 by norm_num] at h

/-! ## 2. The corner profile `x ↦ x + |x|`

It is monotone, continuous and `2`-Lipschitz, hence absolutely continuous on every window, and yet
it has no derivative at its corner `0`.  So no radius wrapper may claim a derivative at an attained
corner radius, and the a.e. formulation cannot be strengthened to a pointwise one. -/

theorem monotone_cornerFun : Monotone cornerFun := by
  intro x y hxy
  simp only [cornerFun]
  rcases le_or_gt x 0 with hx | hx
  · rw [abs_of_nonpos hx]
    rcases le_or_gt y 0 with hy | hy
    · rw [abs_of_nonpos hy]; linarith
    · rw [abs_of_nonneg hy.le]; linarith
  · rcases le_or_gt y 0 with hy | hy
    · linarith
    · rw [abs_of_nonneg hx.le, abs_of_nonneg hy.le]; linarith

theorem continuous_cornerFun : Continuous cornerFun :=
  continuous_id.add continuous_abs

theorem lipschitzWith_cornerFun : LipschitzWith 2 cornerFun := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  have h1 : dist (cornerFun x) (cornerFun y) ≤ dist x y + dist |x| |y| :=
    dist_add_add_le x |x| y |y|
  have h2 : dist |x| |y| ≤ dist x y := by
    rw [Real.dist_eq, Real.dist_eq]
    exact abs_abs_sub_abs_le_abs_sub x y
  have h3 : dist (cornerFun x) (cornerFun y) ≤ dist x y + dist x y := by linarith
  have h4 : ((2 : ℝ≥0) : ℝ) * dist x y = dist x y + dist x y := by
    push_cast
    ring
  rw [h4]
  exact h3

theorem absolutelyContinuousOnInterval_cornerFun (u v : ℝ) :
    AbsolutelyContinuousOnInterval cornerFun u v :=
  lipschitzWith_cornerFun.lipschitzOnWith.absolutelyContinuousOnInterval

/-- **The corner profile has no derivative at its corner.** -/
theorem not_differentiableAt_cornerFun_zero : ¬ DifferentiableAt ℝ cornerFun 0 := by
  intro h
  have h3 : DifferentiableAt ℝ (cornerFun - fun x : ℝ => x) 0 :=
    h.sub (differentiableAt_id (x := (0 : ℝ)))
  have h4 : (cornerFun - fun x : ℝ => x) = fun x : ℝ => |x| := by
    funext x
    simp [cornerFun]
  rw [h4] at h3
  exact not_differentiableAt_abs_zero h3

theorem cornerDeriv_eq_zero {x : ℝ} (hx : x ≤ 0) : cornerDeriv x = 0 := by
  simp [cornerDeriv, hx]

theorem cornerDeriv_eq_two {x : ℝ} (hx : 0 < x) : cornerDeriv x = 2 := by
  simp [cornerDeriv, not_le.mpr hx]

/-- **Off the corner the profile is differentiable**, with derivative `cornerDeriv`. -/
theorem hasDerivAt_cornerFun_of_ne {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt cornerFun (cornerDeriv x) x := by
  rcases lt_or_gt_of_ne hx with hx' | hx'
  · have hz : cornerFun =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hx'] with y hy
      simp [cornerFun, abs_of_neg hy]
    rw [cornerDeriv_eq_zero hx'.le]
    exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hz
  · have hz : cornerFun =ᶠ[𝓝 x] fun y => 2 * y := by
      filter_upwards [Ioi_mem_nhds hx'] with y hy
      simp only [cornerFun, abs_of_pos hy]
      ring
    rw [cornerDeriv_eq_two hx']
    have h2 : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
      simpa using (hasDerivAt_id x).const_mul 2
    exact h2.congr_of_eventuallyEq hz

/-- **The a.e. derivative statement holds** for the corner profile. -/
theorem ae_hasDerivAt_cornerFun :
    ∀ᵐ x ∂(volume : Measure ℝ), HasDerivAt cornerFun (cornerDeriv x) x := by
  have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := by
    rw [ae_iff]
    simp
  filter_upwards [hne] with x hx
  exact hasDerivAt_cornerFun_of_ne hx

/-- **But the a.e. statement cannot be made pointwise** at the corner. -/
theorem not_forall_hasDerivAt_cornerFun :
    ¬ ∀ x : ℝ, HasDerivAt cornerFun (cornerDeriv x) x := fun h =>
  not_differentiableAt_cornerFun_zero (h 0).differentiableAt

/-- **The hypothesis set of the finite-set gluing lemma is consistent**: the corner profile is
monotone, continuous and absolutely continuous on every corner-free window, and also on the
corner-containing window `[-1,1]`.  So the obstruction of §1 is exactly the missing continuity. -/
theorem cornerFun_satisfies_gluing_hypotheses :
    Monotone cornerFun ∧ Continuous cornerFun ∧
      (∀ u v : ℝ, u ≤ v → (0 : ℝ) ∉ Icc u v →
        AbsolutelyContinuousOnInterval cornerFun u v) ∧
      AbsolutelyContinuousOnInterval cornerFun (-1) 1 :=
  ⟨monotone_cornerFun, continuous_cornerFun,
    fun _ _ _ _ => absolutelyContinuousOnInterval_cornerFun _ _,
    absolutelyContinuousOnInterval_cornerFun (-1) 1⟩

/-! ## 3. The three sharpness statements, in the shape of the bridges -/

/-- **Bridge 1 (absolute-continuity gluing) cannot drop continuity at the exceptional points.**

There are a monotone `f` and a finite `C` such that `f` is absolutely continuous on every closed
window inside `[-1,1]` that avoids `C`, and yet `f` is not absolutely continuous on `[-1,1]`.  So
the continuity hypothesis of the gluing lemma is load-bearing: monotonicity plus corner-free
absolute continuity does not give absolute continuity. -/
theorem no_gluing_without_continuity :
    ∃ (f : ℝ → ℝ) (C : Set ℝ), C.Finite ∧ Monotone f ∧
      (∀ u v : ℝ, -1 ≤ u → u < v → v ≤ 1 → (∀ c ∈ C, c ∉ Icc u v) →
        AbsolutelyContinuousOnInterval f u v) ∧
      ¬ AbsolutelyContinuousOnInterval f (-1) 1 := by
  refine ⟨stepAt 0, {0}, Set.finite_singleton 0, monotone_stepAt 0, ?_, ?_⟩
  · intro u v _ huv _ hC
    exact absolutelyContinuousOnInterval_stepAt_of_notMem huv.le (hC 0 rfl)
  · have h := not_absolutelyContinuousOnInterval_stepAt 0
    rwa [show (0 : ℝ) - 1 = -1 by norm_num, show (0 : ℝ) + 1 = 1 by norm_num] at h

/-- **Bridge 2 (corner transfer of the integrated identity) cannot drop continuity at the corner.**

There are `f`, `g` and a finite `C` such that the integrated identity `∫_u^x g = f x - f u` holds
on every closed window inside `[-1,1]` avoiding `C`, and yet fails on `[-1,1]`.  So the corner
transfer does not follow from the corner-free identity alone; it needs the extra continuity of `f`
at the corner radius. -/
theorem no_corner_transfer_without_continuity :
    ∃ (f g : ℝ → ℝ) (C : Set ℝ), C.Finite ∧
      (∀ u v x : ℝ, -1 ≤ u → u < v → v ≤ 1 → (∀ c ∈ C, c ∉ Icc u v) →
        x ∈ Icc u v → ∫ t in u..x, g t = f x - f u) ∧
      ¬ ∀ x ∈ Icc (-1 : ℝ) 1, ∫ t in (-1)..x, g t = f x - f (-1) := by
  refine ⟨stepAt 0, fun _ => 0, {0}, Set.finite_singleton 0, ?_, ?_⟩
  · intro u v x _ huv _ hC hx
    exact integral_identity_stepAt_cornerFree huv.le (hC 0 rfl) x hx
  · intro h
    obtain ⟨x, hx, hne⟩ := integral_identity_stepAt_fails
    exact hne (h x hx)

/-- **No wrapper may claim a derivative at an attained corner radius.**

There are a monotone continuous `f`, a `g` and a finite `C` such that `f` has derivative `g x` at
every `x ∉ C` and `g` is the a.e. derivative of `f`, and yet `f` has no derivative at one point of
`C`.  So the `∀ᵐ`-formulation of the radius derivative is sharp: it cannot be strengthened to a
pointwise statement at attained corner radii, even under full absolute continuity of `f`. -/
theorem no_pointwise_derivative_at_corner :
    ∃ (f g : ℝ → ℝ) (C : Set ℝ), C.Finite ∧ Monotone f ∧ Continuous f ∧
      (∀ x : ℝ, x ∉ C → HasDerivAt f (g x) x) ∧
      (∀ᵐ x ∂(volume : Measure ℝ), HasDerivAt f (g x) x) ∧
      ¬ ∀ x : ℝ, HasDerivAt f (g x) x := by
  refine ⟨cornerFun, cornerDeriv, {0}, Set.finite_singleton 0, monotone_cornerFun,
    continuous_cornerFun, ?_, ae_hasDerivAt_cornerFun, not_forall_hasDerivAt_cornerFun⟩
  intro x hx
  exact hasDerivAt_cornerFun_of_ne (by simpa using hx)

/-! ### The same three facts as no-go statements

The witnesses above are stated in the logically natural form below: the universally quantified
implication with the continuity / corner-free restriction removed is *false*. -/

/-- **No-go form of bridge 1.**  The finite-set gluing implication is false without continuity of
`f` at the exceptional points — even when `f` is monotone and absolutely continuous on every closed
window avoiding them (with the stronger *closed*-window avoidance hypothesis). -/
theorem gluing_without_continuity_false :
    ¬ ∀ (f : ℝ → ℝ) (C : Set ℝ), C.Finite → Monotone f →
      (∀ u v : ℝ, -1 ≤ u → u < v → v ≤ 1 → (∀ c ∈ C, c ∉ Icc u v) →
        AbsolutelyContinuousOnInterval f u v) →
      AbsolutelyContinuousOnInterval f (-1) 1 := by
  intro h
  obtain ⟨f, C, hC, hmono, hgap, hnot⟩ := no_gluing_without_continuity
  exact hnot (h f C hC hmono hgap)

/-- **No-go form of bridge 2.**  Corner transfer of the integrated identity is false without
continuity of `f` at the corner: the identity on all corner-free windows does not force it on the
corner-containing one. -/
theorem corner_transfer_without_continuity_false :
    ¬ ∀ (f g : ℝ → ℝ) (C : Set ℝ), C.Finite →
      (∀ u v x : ℝ, -1 ≤ u → u < v → v ≤ 1 → (∀ c ∈ C, c ∉ Icc u v) →
        x ∈ Icc u v → ∫ t in u..x, g t = f x - f u) →
      ∀ x ∈ Icc (-1 : ℝ) 1, ∫ t in (-1)..x, g t = f x - f (-1) := by
  intro h
  obtain ⟨f, g, C, hC, hgap, hnot⟩ := no_corner_transfer_without_continuity
  exact hnot (h f g C hC hgap)

/-- **No-go form of the a.e. radius derivative.**  The a.e. statement cannot be upgraded to a
pointwise one at an attained corner radius, even for a monotone continuous `f` whose a.e. derivative
is also its pointwise derivative off a finite set. -/
theorem pointwise_derivative_at_corner_false :
    ¬ ∀ (f g : ℝ → ℝ) (C : Set ℝ), C.Finite → Monotone f → Continuous f →
      (∀ x : ℝ, x ∉ C → HasDerivAt f (g x) x) →
      (∀ᵐ x ∂(volume : Measure ℝ), HasDerivAt f (g x) x) →
      ∀ x : ℝ, HasDerivAt f (g x) x := by
  intro h
  obtain ⟨f, g, C, hC, hmono, hcont, hoff, hae, hnot⟩ := no_pointwise_derivative_at_corner
  exact hnot (h f g C hC hmono hcont hoff hae)

end PercLib.CriticalLRP.Orchestration.SmwywszgoM4
