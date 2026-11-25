/-
# Interval absolute continuity from an interval-integrable derivative majorant

Direction D3 (member `m7`, swarm `smwtrtcqs`), analysis only.

The previously landed `.ultramath/smwtqkdul/m7/IntervalAC.lean` proves the mean-value inequality
with a variable majorant, and the absolute-continuity/FTC consequences, under the hypothesis that
the majorant `g` is **continuous on the closed window**.  That regularity is not what the model
provides: the only bound available on the radial derivative of the cut mass is a pointwise
inequality against a majorant built from a *measurable* log-error factor.

This file isolates how much regularity of `g` the argument really needs, and proves the sharp
alternative:

* `abs_sub_le_integral_of_derivative_majorant` — the reflexivity argument needs only that the
  *primitive* of `g` be differentiable with derivative `g u` at every interior point
  (`PrimitiveDerivativeMajorant`), plus interval integrability of `g` on the window.  No
  continuity, no boundedness, and no continuity at the endpoints.
* `abs_sub_le_integral_of_finite_exception_majorant` — allowing finitely many discontinuities of
  `g` (poles) *and* finitely many corners of `f`, by splitting the window.
* `abs_sub_le_integral_of_continuousOn_interior` (+ absolute-continuity and FTC forms) — the
  special case where `g` is continuous only on the *open* window and merely interval integrable on
  the closed one, so the endpoints may carry genuine singularities of the majorant.
* `sub_le_integral_of_absolutelyContinuous_of_ae_deriv_le` and its absolute-value form — once `f`
  is known to be absolutely continuous, the majorant can be **any** interval-integrable function
  and the derivative only needs to be dominated *almost everywhere*.  This removes the majorant's
  regularity from the hypotheses entirely; the single remaining premise is the absolute continuity
  of `f` itself.
* `abs_sub_le_integral_of_two_step` — the resulting recipe: pointwise data off a finite set
  against a majorant continuous off that set give absolute continuity of `f`; a separate a.e. bound
  against an arbitrary interval-integrable majorant then gives the quantitative incremental bound.
* `stepFun_counterexample` — a counterexample showing that the pointwise hypothesis cannot be
  weakened to an a.e. one without continuity of `f`: the step function is differentiable with
  derivative `0` at every point off the finite set `{0}`, hence a.e., and `0` is an integrable
  majorant, yet the incremental bound fails.  So both `ContinuousOn f` and the *pointwise* (not
  a.e.) nature of the derivative bound are load-bearing.
* `majorant_continuous_on_window_is_strictly_stronger` — a non-vacuous instance of the weakened
  hypotheses with a majorant that is *not* continuous on the closed window, showing that
  `abs_sub_le_integral_of_finite_exception_majorant` is strictly stronger than the landed
  continuous-majorant theorem.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import PercLib.CriticalLRP.Analysis.Cutoff.LocalAC.Defs

@[expose] public section

open MeasureTheory Set Filter
open scoped Interval Topology

namespace PercLib.CriticalLRP.LocalAC

/-! ## The corner-free mean value inequality with an integrable majorant -/

/-- **FTC-1 at an interior point of the window**, for a majorant that is only required to be
interval integrable on the whole window and continuous at that one point. -/
theorem hasDerivAt_primitive_of_continuousAt {g : ℝ → ℝ} {p q u : ℝ}
    (hgi : IntervalIntegrable g volume p q) (hu : u ∈ Ioo p q) (hcu : ContinuousAt g u) :
    HasDerivAt (fun s => ∫ t in p..s, g t) (g u) u := by
  have hpu : p ≤ u := hu.1.le
  have huq : u ≤ q := hu.2.le
  have hmem : Ι p q ∈ 𝓝 u := by
    rw [uIoc_of_le (hpu.trans huq)]
    exact mem_of_superset (Ioo_mem_nhds hu.1 hu.2) Ioo_subset_Ioc_self
  refine intervalIntegral.integral_hasDerivAt_right (b := u) ?_ ⟨Ι p q, hmem, ?_⟩ hcu
  · refine hgi.mono_set ?_
    rw [uIcc_of_le hpu, uIcc_of_le (hpu.trans huq)]
    exact Icc_subset_Icc le_rfl hu.2.le
  · exact hgi.def'.aestronglyMeasurable

/-- **Mean-value inequality with an integral majorant, weakened regularity.**

`f` continuous on the window, differentiable on its interior with `|f'| ≤ g` there; `g` only
interval integrable on the window, and its *primitive* differentiable with derivative `g` at every
interior point.  Then `|f y - f x| ≤ ∫_x^y g`.

Compared with the landed `IntervalAC.abs_sub_le_integral_of_deriv_le` the hypothesis
`ContinuousOn g (Icc a b)` is replaced by `IntervalIntegrable g` plus `PrimitiveDerivativeMajorant`,
which in particular allows `g` to blow up at the endpoints of the window. -/
theorem abs_sub_le_integral_of_derivative_majorant {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hfc : ContinuousOn f (Icc a b))
    (hgi : IntervalIntegrable g volume a b)
    (hgprim : PrimitiveDerivativeMajorant g a b)
    (hfd : DifferentiableOn ℝ f (Ioo a b))
    (hmaj : ∀ u ∈ Ioo a b, |deriv f u| ≤ g u) :
    ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y → |f y - f x| ≤ ∫ t in x..y, g t := by
  set G : ℝ → ℝ := fun s => ∫ t in a..s, g t with hG
  have hGcont : ContinuousOn G (Icc a b) := by
    have h := intervalIntegral.continuousOn_primitive_interval' (f := g) (μ := volume)
      (a := a) (b₁ := a) (b₂ := b) hgi left_mem_uIcc
    rwa [uIcc_of_le hab] at h
  have hGD : DifferentiableOn ℝ G (Ioo a b) := by
    intro u hu
    exact (hgprim u hu).differentiableAt.differentiableWithinAt
  have hderiv : ∀ u ∈ Ioo a b, HasDerivAt G (g u) u := hgprim
  have hAn : AntitoneOn (fun s => f s - G s) (Icc a b) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc a b) ?_ ?_ ?_
    · intro x hx
      exact (hfc x hx).sub (hGcont x hx)
    · rw [interior_Icc]
      intro x hx
      exact (hfd x hx).sub (hGD x hx)
    · rw [interior_Icc]
      intro u hu
      have h1 : HasDerivAt f (deriv f u) u :=
        ((hfd u hu).differentiableAt (isOpen_Ioo.mem_nhds hu)).hasDerivAt
      have h3 : HasDerivAt (fun s => f s - G s) (deriv f u - g u) u := h1.sub (hderiv u hu)
      rw [h3.deriv]
      linarith [(abs_le.mp (hmaj u hu)).2]
  have hMo : MonotoneOn (fun s => f s + G s) (Icc a b) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc a b) ?_ ?_ ?_
    · intro x hx
      exact (hfc x hx).add (hGcont x hx)
    · rw [interior_Icc]
      intro x hx
      exact (hfd x hx).add (hGD x hx)
    · rw [interior_Icc]
      intro u hu
      have h1 : HasDerivAt f (deriv f u) u :=
        ((hfd u hu).differentiableAt (isOpen_Ioo.mem_nhds hu)).hasDerivAt
      have h3 : HasDerivAt (fun s => f s + G s) (deriv f u + g u) u := h1.add (hderiv u hu)
      rw [h3.deriv]
      linarith [(abs_le.mp (hmaj u hu)).1]
  intro x hx y hy hxy
  have hsplit : (∫ t in a..y, g t) - (∫ t in a..x, g t) = ∫ t in x..y, g t := by
    have h1 : IntervalIntegrable g volume a x := hgi.mono_set (by
      rw [uIcc_of_le hx.1, uIcc_of_le hab]
      exact Icc_subset_Icc le_rfl hx.2)
    have h2 : IntervalIntegrable g volume x y := hgi.mono_set (by
      rw [uIcc_of_le hxy, uIcc_of_le hab]
      exact Icc_subset_Icc hx.1 hy.2)
    have h3 : (∫ t in a..x, g t) + (∫ t in x..y, g t) = ∫ t in a..y, g t :=
      intervalIntegral.integral_add_adjacent_intervals h1 h2
    linarith
  have hle : f y - f x ≤ (∫ t in x..y, g t) := by
    have h : f y - G y ≤ f x - G x := hAn hx hy hxy
    linarith
  have hge : f x - f y ≤ (∫ t in x..y, g t) := by
    have h : f x + G x ≤ f y + G y := hMo hx hy hxy
    linarith
  exact abs_le.mpr ⟨by linarith, hle⟩

/-- **Finite exceptional sets for both `f` and `g`.**

The cut-off profile has a corner at every radius equal to a lattice distance, and a majorant built
from a log-error factor may have finitely many discontinuities (poles) inside the window.  Both
finite sets are harmless: split the window at their points, apply the corner-free inequality on
each piece, and telescope.  No derivative and no continuity of `g` is claimed at the exceptional
radii themselves. -/
theorem abs_sub_le_integral_of_finite_exception_majorant {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hfc : ContinuousOn f (Icc a b))
    (hgi : IntervalIntegrable g volume a b)
    (D : Finset ℝ)
    (hgood : ∀ u ∈ Ioo a b, u ∉ (D : Set ℝ) →
      DifferentiableAt ℝ f u ∧ |deriv f u| ≤ g u ∧ ContinuousAt g u) :
    ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y → |f y - f x| ≤ ∫ t in x..y, g t := by
  classical
  have key : ∀ D : Finset ℝ, ∀ p ∈ Icc a b, ∀ q ∈ Icc a b, p ≤ q →
      (∀ u ∈ Ioo p q, u ∉ (D : Set ℝ) →
        DifferentiableAt ℝ f u ∧ |deriv f u| ≤ g u ∧ ContinuousAt g u) →
      |f q - f p| ≤ ∫ t in p..q, g t := by
    intro D
    induction D using Finset.induction with
    | empty =>
        intro p hp q hq hpq hloc
        have hsub : Icc p q ⊆ Icc a b := fun t ht => ⟨le_trans hp.1 ht.1, le_trans ht.2 hq.2⟩
        have hgpq : IntervalIntegrable g volume p q := hgi.mono_set (by
          rw [uIcc_of_le hpq, uIcc_of_le hab]
          exact hsub)
        have hprim : PrimitiveDerivativeMajorant g p q := by
          intro u hu
          exact hasDerivAt_primitive_of_continuousAt hgpq hu ((hloc u hu (by simp)).2.2)
        refine abs_sub_le_integral_of_derivative_majorant hpq (hfc.mono hsub) hgpq hprim ?_ ?_
          p ⟨le_rfl, hpq⟩ q ⟨hpq, le_rfl⟩ hpq
        · exact fun u hu => ((hloc u hu (by simp)).1).differentiableWithinAt
        · exact fun u hu => (hloc u hu (by simp)).2.1
    | insert c s _ ih =>
        intro p hp q hq hpq hloc
        by_cases hc : c ∈ Icc p q
        · have hsub1 : ∀ u ∈ Ioo p c, u ∉ (s : Set ℝ) →
              DifferentiableAt ℝ f u ∧ |deriv f u| ≤ g u ∧ ContinuousAt g u := by
            intro u hu hus
            exact hloc u ⟨hu.1, lt_of_lt_of_le hu.2 hc.2⟩ (by
              simp only [Finset.coe_insert, Set.mem_insert_iff, not_or]
              exact ⟨ne_of_lt hu.2, hus⟩)
          have hsub2 : ∀ u ∈ Ioo c q, u ∉ (s : Set ℝ) →
              DifferentiableAt ℝ f u ∧ |deriv f u| ≤ g u ∧ ContinuousAt g u := by
            intro u hu hus
            exact hloc u ⟨lt_of_le_of_lt hc.1 hu.1, hu.2⟩ (by
              simp only [Finset.coe_insert, Set.mem_insert_iff, not_or]
              exact ⟨ne_of_gt hu.1, hus⟩)
          have hc' : c ∈ Icc a b := ⟨le_trans hp.1 hc.1, le_trans hc.2 hq.2⟩
          have h1 : |f c - f p| ≤ (∫ t in p..c, g t) := ih p hp c hc' hc.1 hsub1
          have h2 : |f q - f c| ≤ (∫ t in c..q, g t) := ih c hc' q hq hc.2 hsub2
          have hg1 : IntervalIntegrable g volume p c := hgi.mono_set (by
            rw [uIcc_of_le hc.1, uIcc_of_le hab]
            exact fun t ht => ⟨le_trans hp.1 ht.1, le_trans ht.2 hc'.2⟩)
          have hg2 : IntervalIntegrable g volume c q := hgi.mono_set (by
            rw [uIcc_of_le hc.2, uIcc_of_le hab]
            exact fun t ht => ⟨le_trans hc'.1 ht.1, le_trans ht.2 hq.2⟩)
          have hsplit : (∫ t in p..c, g t) + (∫ t in c..q, g t) = ∫ t in p..q, g t :=
            intervalIntegral.integral_add_adjacent_intervals hg1 hg2
          have htri : |f q - f p| ≤ |f q - f c| + |f c - f p| := by
            have heq : f q - f p = (f q - f c) + (f c - f p) := by ring
            rw [heq]; exact abs_add_le _ _
          linarith
        · have hsub : ∀ u ∈ Ioo p q, u ∉ (s : Set ℝ) →
              DifferentiableAt ℝ f u ∧ |deriv f u| ≤ g u ∧ ContinuousAt g u := by
            intro u hu hus
            exact hloc u hu (by
              simp only [Finset.coe_insert, Set.mem_insert_iff, not_or]
              exact ⟨fun h => hc (h ▸ ⟨le_of_lt hu.1, le_of_lt hu.2⟩), hus⟩)
          exact ih p hp q hq hpq hsub
  intro x hx y hy hxy
  refine key D x hx y hy hxy ?_
  intro u hu huD
  exact hgood u ⟨lt_of_le_of_lt hx.1 hu.1, lt_of_lt_of_le hu.2 hy.2⟩ huD

/-! ## From the incremental bound to absolute continuity and the FTC -/

/-- **Absolute continuity from the incremental bound.**  If `|f y - f x| ≤ ∫_x^y g` for all
`x ≤ y` in the window with `g` interval integrable, then `f` is absolutely continuous: `f` is
`1`-Lipschitz for the pseudo-metric `(x,y) ↦ ∫_x^y |g|`, which is the distance induced by the
absolutely continuous primitive of `|g|`. -/
theorem absolutelyContinuousOnInterval_of_interval_bound {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hg : IntervalIntegrable g volume a b)
    (hbound : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y → |f y - f x| ≤ ∫ t in x..y, g t) :
    AbsolutelyContinuousOnInterval f a b := by
  classical
  have hmem : uIcc a b = Icc a b := uIcc_of_le hab
  have hgabs : IntervalIntegrable (fun t => |g t|) volume a b := hg.abs
  have hint : ∀ p ∈ Icc a b, ∀ q ∈ Icc a b,
      IntervalIntegrable (fun t => |g t|) volume p q := by
    intro p hp q hq
    refine hgabs.mono_set ?_
    rw [uIcc, uIcc, min_eq_left hab, max_eq_right hab]
    exact Icc_subset_Icc (le_min hp.1 hq.1) (max_le hp.2 hq.2)
  have hGac : AbsolutelyContinuousOnInterval (fun x => ∫ t in a..x, |g t|) a b :=
    hgabs.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hstep : ∀ p ∈ Icc a b, ∀ q ∈ Icc a b, p ≤ q →
      dist (f p) (f q) ≤ dist (∫ t in a..p, |g t|) (∫ t in a..q, |g t|) := by
    intro p hp q hq hpq
    have hb := hbound p hp q hq hpq
    have hnn : 0 ≤ ∫ t in p..q, g t := le_trans (abs_nonneg _) hb
    have hle : (∫ t in p..q, g t) ≤ ∫ t in p..q, |g t| := by
      rw [← abs_of_nonneg hnn]
      exact intervalIntegral.abs_integral_le_integral_abs hpq
    have hsplit : (∫ t in a..p, |g t|) + (∫ t in p..q, |g t|) = ∫ t in a..q, |g t| :=
      intervalIntegral.integral_add_adjacent_intervals (hint a ⟨le_rfl, hab⟩ p hp) (hint p hp q hq)
    have hnonneg : 0 ≤ (∫ t in a..q, |g t|) - (∫ t in a..p, |g t|) := by
      have h0 : 0 ≤ ∫ t in p..q, |g t| :=
        intervalIntegral.integral_nonneg hpq (fun t _ => abs_nonneg (g t))
      linarith
    rw [Real.dist_eq, Real.dist_eq, abs_sub_comm (f p) (f q),
      abs_sub_comm (∫ t in a..p, |g t|) (∫ t in a..q, |g t|), abs_of_nonneg hnonneg]
    linarith
  have hstep' : ∀ p ∈ Icc a b, ∀ q ∈ Icc a b,
      dist (f p) (f q) ≤ dist (∫ t in a..p, |g t|) (∫ t in a..q, |g t|) := by
    intro p hp q hq
    rcases le_total p q with hpq | hqp
    · exact hstep p hp q hq hpq
    · rw [dist_comm (f p) (f q), dist_comm (∫ t in a..p, |g t|) (∫ t in a..q, |g t|)]
      exact hstep q hq p hp hqp
  refine squeeze_zero' ?_ ?_ hGac
  · filter_upwards with E using Finset.sum_nonneg (fun i _ => dist_nonneg)
  · rw [eventually_inf_principal]
    filter_upwards with E hE
    exact Finset.sum_le_sum (fun i hi => by
      obtain ⟨h1, h2⟩ := hE.1 i hi
      rw [hmem] at h1 h2
      exact hstep' _ h1 _ h2)

/-- **Absolute continuity from pointwise data with a majorant that is only locally continuous off a
finite set.**  No continuity of `g` on the closed window, no boundedness of `g`. -/
theorem absolutelyContinuousOnInterval_of_finite_exception_majorant {f g : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hfc : ContinuousOn f (Icc a b)) (hgi : IntervalIntegrable g volume a b)
    (D : Finset ℝ)
    (hgood : ∀ u ∈ Ioo a b, u ∉ (D : Set ℝ) →
      DifferentiableAt ℝ f u ∧ |deriv f u| ≤ g u ∧ ContinuousAt g u) :
    AbsolutelyContinuousOnInterval f a b :=
  absolutelyContinuousOnInterval_of_interval_bound hab hgi
    (abs_sub_le_integral_of_finite_exception_majorant hab hfc hgi D hgood)

/-- **Fundamental theorem of calculus** for `f` across the window, under the weakened majorant
hypotheses: `∫_a^b f' = f b - f a`.  No derivative is claimed at the exceptional radii. -/
theorem intervalIntegral_deriv_eq_sub_of_finite_exception_majorant {f g : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hfc : ContinuousOn f (Icc a b)) (hgi : IntervalIntegrable g volume a b)
    (D : Finset ℝ)
    (hgood : ∀ u ∈ Ioo a b, u ∉ (D : Set ℝ) →
      DifferentiableAt ℝ f u ∧ |deriv f u| ≤ g u ∧ ContinuousAt g u) :
    ∫ t in a..b, deriv f t = f b - f a :=
  AbsolutelyContinuousOnInterval.integral_deriv_eq_sub
    (absolutelyContinuousOnInterval_of_finite_exception_majorant hab hfc hgi D hgood)

/-- Almost-everywhere differentiability of `f` in the window, under the weakened majorant
hypotheses. -/
theorem ae_differentiableAt_of_finite_exception_majorant {f g : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hfc : ContinuousOn f (Icc a b)) (hgi : IntervalIntegrable g volume a b)
    (D : Finset ℝ)
    (hgood : ∀ u ∈ Ioo a b, u ∉ (D : Set ℝ) →
      DifferentiableAt ℝ f u ∧ |deriv f u| ≤ g u ∧ ContinuousAt g u) :
    ∀ᵐ t, t ∈ Icc a b → DifferentiableAt ℝ f t := by
  have h := (absolutelyContinuousOnInterval_of_finite_exception_majorant hab hfc hgi D hgood)
    |>.ae_differentiableAt
  rwa [uIcc_of_le hab] at h

/-! ## The majorant's regularity removed entirely, at the price of absolute continuity of `f` -/

/-- **One-sided incremental bound from an a.e. derivative bound and an arbitrary interval-integrable
majorant.**

If `f` is absolutely continuous on the window and `f' ≤ g` a.e. on its interior, where `g` is only
required to be interval integrable, then `f y - f x ≤ ∫_x^y g`.  The proof is the FTC for
absolutely continuous functions plus monotonicity of the integral; no regularity of `g` enters. -/
theorem sub_le_integral_of_absolutelyContinuous_of_ae_deriv_le {f g : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hfac : AbsolutelyContinuousOnInterval f a b)
    (hgi : IntervalIntegrable g volume a b)
    (hmaj : ∀ᵐ u ∂volume, u ∈ Ioo a b → deriv f u ≤ g u) :
    ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y → f y - f x ≤ ∫ t in x..y, g t := by
  intro x hx y hy hxy
  have hsub : Icc x y ⊆ Icc a b := fun t ht => ⟨le_trans hx.1 ht.1, le_trans ht.2 hy.2⟩
  have hfxy : AbsolutelyContinuousOnInterval f x y := hfac.mono (by
    rw [uIcc_of_le hxy, uIcc_of_le hab]; exact hsub)
  have hfixy : IntervalIntegrable (deriv f) volume x y := hfxy.intervalIntegrable_deriv
  have hgxy : IntervalIntegrable g volume x y := hgi.mono_set (by
    rw [uIcc_of_le hxy, uIcc_of_le hab]; exact hsub)
  have hftc : ∫ t in x..y, deriv f t = f y - f x := hfxy.integral_deriv_eq_sub
  have hA : ∫ t in x..y, deriv f t = ∫ t in Ioo x y, deriv f t := by
    rw [intervalIntegral.integral_of_le hxy, integral_Ioc_eq_integral_Ioo]
  have hB : ∫ t in x..y, g t = ∫ t in Ioo x y, g t := by
    rw [intervalIntegral.integral_of_le hxy, integral_Ioc_eq_integral_Ioo]
  have hfi : IntegrableOn (deriv f) (Ioo x y) volume := by
    refine hfixy.def'.mono_set ?_
    rw [uIoc_of_le hxy]
    exact Ioo_subset_Ioc_self
  have hgI : IntegrableOn g (Ioo x y) volume := by
    refine hgxy.def'.mono_set ?_
    rw [uIoc_of_le hxy]
    exact Ioo_subset_Ioc_self
  have hae : ∀ᵐ u ∂(volume.restrict (Ioo x y)), deriv f u ≤ g u := by
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hmaj] with u hu hmem
    exact hu (Ioo_subset_Ioo hx.1 hy.2 hmem)
  have hmono : ∫ u in Ioo x y, deriv f u ≤ ∫ u in Ioo x y, g u :=
    setIntegral_mono_ae_restrict hfi hgI hae
  rw [← hftc, hA, hB]
  exact hmono

/-- **Incremental bound with an arbitrary interval-integrable majorant**, given absolute continuity
of `f` and the a.e. derivative bound `|f'| ≤ g`. -/
theorem abs_sub_le_integral_of_absolutelyContinuous_of_ae_abs_deriv_le {f g : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hfac : AbsolutelyContinuousOnInterval f a b)
    (hgi : IntervalIntegrable g volume a b)
    (hmaj : ∀ᵐ u ∂volume, u ∈ Ioo a b → |deriv f u| ≤ g u) :
    ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y → |f y - f x| ≤ ∫ t in x..y, g t := by
  intro x hx y hy hxy
  have hpos : ∀ᵐ u ∂volume, u ∈ Ioo a b → deriv f u ≤ g u :=
    hmaj.mono fun u hu hmem => (abs_le.mp (hu hmem)).2
  have hneg : ∀ᵐ u ∂volume, u ∈ Ioo a b → deriv (fun t => -f t) u ≤ g u := by
    refine hmaj.mono ?_
    intro u hu hmem
    have hd : deriv (fun t => -f t) u = -deriv f u := by simp
    rw [hd]
    have hle := (abs_le.mp (hu hmem)).1
    linarith
  have h1 := sub_le_integral_of_absolutelyContinuous_of_ae_deriv_le hab hfac hgi hpos x hx y hy hxy
  have h2 := sub_le_integral_of_absolutelyContinuous_of_ae_deriv_le hab hfac.neg hgi hneg
    x hx y hy hxy
  have h2'' : -f y - -f x ≤ ∫ t in x..y, g t := by simpa using h2
  have h2' : f x - f y ≤ ∫ t in x..y, g t := by linarith [h2'']
  exact abs_le.mpr ⟨by linarith, h1⟩


/-! ## Sharpness: the hypotheses cannot be weakened to almost-everywhere information

The pointwise bound `|f'| ≤ g` off a finite set is *not* replaceable by an a.e. bound, and
`f` must be continuous: the step function is differentiable with derivative `0` at every point
off the finite set `{0}` (hence a.e.), `0` is an integrable majorant, yet the incremental bound
fails.  Consequently the a.e. information available for a merely measurable log-error factor is
genuinely insufficient without an independent absolute-continuity argument for `f`. -/

theorem stepFun_zero : stepFun 0 = 0 := by simp [stepFun]

theorem stepFun_of_pos {t : ℝ} (ht : 0 < t) : stepFun t = 1 := by simp [stepFun, ht]

theorem stepFun_of_nonpos {t : ℝ} (ht : t ≤ 0) : stepFun t = 0 := by
  simp [stepFun, not_lt.mpr ht]

theorem not_continuousAt_stepFun_zero : ¬ ContinuousAt stepFun 0 := by
  intro h
  have h1 : Tendsto stepFun (𝓝[>] (0 : ℝ)) (𝓝 (stepFun 0)) := h.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto stepFun (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hev : stepFun =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => (1 : ℝ)) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact stepFun_of_pos ht
    exact tendsto_const_nhds.congr' hev.symm
  have h3 : stepFun 0 = 1 := tendsto_nhds_unique h1 h2
  rw [stepFun_zero] at h3
  exact zero_ne_one h3

/-- Off the single point `0` the step function is locally constant, hence differentiable with
derivative `0`. -/
theorem stepFun_differentiableAt_of_ne {u : ℝ} (hu : u ≠ 0) :
    DifferentiableAt ℝ stepFun u ∧ deriv stepFun u = 0 := by
  rcases lt_or_gt_of_ne hu with h | h
  · have hev : stepFun =ᶠ[𝓝 u] (fun _ => (0 : ℝ)) := by
      filter_upwards [isOpen_Iio.mem_nhds h] with t ht
      simp [stepFun, not_lt.mpr ht.le]
    have hd : HasDerivAt stepFun 0 u :=
      (hasDerivAt_const (x := u) (c := (0 : ℝ))).congr_of_eventuallyEq hev
    exact ⟨hd.differentiableAt, hd.deriv⟩
  · have hev : stepFun =ᶠ[𝓝 u] (fun _ => (1 : ℝ)) := by
      filter_upwards [isOpen_Ioi.mem_nhds h] with t ht
      exact stepFun_of_pos ht
    have hd : HasDerivAt stepFun 0 u :=
      (hasDerivAt_const (x := u) (c := (1 : ℝ))).congr_of_eventuallyEq hev
    exact ⟨hd.differentiableAt, hd.deriv⟩

/-- The step function is differentiable almost everywhere, with derivative `0` almost everywhere:
the a.e. hypothesis that a merely measurable majorant can supply. -/
theorem stepFun_ae_differentiableAt :
    ∀ᵐ u ∂(volume : Measure ℝ), DifferentiableAt ℝ stepFun u ∧ deriv stepFun u = 0 := by
  have hne : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simp
  filter_upwards [hne] with u hu
  exact stepFun_differentiableAt_of_ne hu

/-- **The overstrong formulation is false.**  `f = stepFun` is differentiable with derivative `0`
at every point off the finite set `{0}` (so in particular `|f'| ≤ g` with `g ≡ 0`, which is
continuous and integrable, holds a.e.), but the incremental bound fails, and `f` is not absolutely
continuous.  Hence neither `ContinuousOn f` nor the *pointwise* (rather than a.e.) nature of the
derivative bound can be dropped. -/
theorem stepFun_counterexample :
    (∀ u ∈ Ioo (-1 : ℝ) 1, u ∉ ({0} : Finset ℝ) →
      DifferentiableAt ℝ stepFun u ∧ |deriv stepFun u| ≤ (0 : ℝ))
    ∧ (∀ᵐ u ∂(volume : Measure ℝ),
        DifferentiableAt ℝ stepFun u ∧ deriv stepFun u = 0)
    ∧ IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume (-1) 1
    ∧ ¬ (|stepFun 1 - stepFun (-1)| ≤ ∫ _s in (-1)..1, (0 : ℝ))
    ∧ ¬ AbsolutelyContinuousOnInterval stepFun (-1) 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro u _ hu
    have hu0 : u ≠ 0 := by
      intro h; exact hu (by simp [h])
    obtain ⟨hd, hd0⟩ := stepFun_differentiableAt_of_ne hu0
    refine ⟨hd, ?_⟩
    rw [hd0]; norm_num
  · exact stepFun_ae_differentiableAt
  · simp
  · intro h
    have h1 : stepFun 1 = 1 := stepFun_of_pos one_pos
    have h2 : stepFun (-1) = 0 := stepFun_of_nonpos (by norm_num)
    rw [h1, h2] at h
    norm_num at h
  · intro hac
    have hcont : ContinuousOn stepFun (Icc (-1) 1) := by
      have h := hac.continuousOn
      rwa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at h
    exact not_continuousAt_stepFun_zero
      (hcont.continuousAt (Icc_mem_nhds (by norm_num) (by norm_num)))

/-! ## Strictness: a majorant that is not continuous on the closed window

`unitPole` is `1` except at the single interior radius `0`, where it is `0`.  It is interval
integrable on `[-1,1]` and continuous at every interior point outside `{0}`, so
`abs_sub_le_integral_of_finite_exception_majorant` applies to its primitive; but it is not
continuous on `Icc (-1) 1`, so the landed continuous-majorant theorem does not apply. -/

theorem unitPole_of_ne {t : ℝ} (ht : t ≠ 0) : unitPole t = 1 := by simp [unitPole, ht]

theorem unitPole_zero : unitPole 0 = 0 := by simp [unitPole]

theorem unitPole_continuousAt {u : ℝ} (hu : u ≠ 0) : ContinuousAt unitPole u := by
  have hmem : ({0}ᶜ : Set ℝ) ∈ 𝓝 u :=
    isOpen_compl_singleton.mem_nhds (by simpa using hu)
  have hev : unitPole =ᶠ[𝓝 u] (fun _ => (1 : ℝ)) := by
    filter_upwards [hmem] with t ht
    exact unitPole_of_ne (by simpa using ht)
  exact continuousAt_const.congr hev.symm

theorem not_continuousAt_unitPole_zero : ¬ ContinuousAt unitPole 0 := by
  intro h
  have h1 : Tendsto unitPole (𝓝[>] (0 : ℝ)) (𝓝 (unitPole 0)) := h.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto unitPole (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hev : unitPole =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => (1 : ℝ)) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact unitPole_of_ne (ne_of_gt ht)
    exact tendsto_const_nhds.congr' hev.symm
  have h3 : unitPole 0 = 1 := tendsto_nhds_unique h1 h2
  rw [unitPole_zero] at h3
  exact zero_ne_one h3

theorem unitPole_ae_eq_one : unitPole =ᵐ[volume] (fun _ : ℝ => (1 : ℝ)) := by
  have hne : ∀ᵐ u ∂(volume : Measure ℝ), u ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simp
  filter_upwards [hne] with u hu
  exact unitPole_of_ne hu

theorem unitPole_ae_eq_one_restrict :
    unitPole =ᵐ[volume.restrict (Ι (-1 : ℝ) 1)] (fun _ : ℝ => (1 : ℝ)) :=
  unitPole_ae_eq_one.filter_mono (MeasureTheory.ae_mono Measure.restrict_le_self)

theorem unitPole_intervalIntegrable : IntervalIntegrable unitPole volume (-1) 1 :=
  intervalIntegrable_congr_ae unitPole_ae_eq_one_restrict |>.mpr intervalIntegrable_const

/-- **The finite-exception majorant theorem is strictly stronger than the continuous-majorant
one.**  There are a function `f` and an interval-integrable majorant `g`, discontinuous at the
interior radius `0`, such that `f` satisfies the finite-exception derivative bound and the
incremental bound holds. -/
theorem majorant_continuous_on_window_is_strictly_stronger :
    ∃ f g : ℝ → ℝ,
      IntervalIntegrable g volume (-1) 1 ∧
      ContinuousAtOff g (-1) 1 {0} ∧
      ¬ ContinuousOn g (Icc (-1) 1) ∧
      DerivBoundOff f g (-1) 1 {0} ∧
      (∀ x ∈ Icc (-1 : ℝ) 1, ∀ y ∈ Icc (-1) 1, x ≤ y → |f y - f x| ≤ ∫ t in x..y, g t) := by
  refine ⟨fun t => ∫ s in (-1)..t, unitPole s, unitPole, unitPole_intervalIntegrable,
    ?_, ?_, ?_, ?_⟩
  · intro u _ huD
    exact unitPole_continuousAt (by intro h; exact huD (by simp [h]))
  · intro hcont
    exact not_continuousAt_unitPole_zero
      (hcont.continuousAt (Icc_mem_nhds (by norm_num) (by norm_num)))
  · intro u hu huD
    have hu0 : u ≠ 0 := by intro h; exact huD (by simp [h])
    have hd : HasDerivAt (fun t => ∫ s in (-1)..t, unitPole s) (unitPole u) u :=
      hasDerivAt_primitive_of_continuousAt unitPole_intervalIntegrable hu
        (unitPole_continuousAt hu0)
    refine ⟨hd.differentiableAt, ?_⟩
    rw [hd.deriv, unitPole_of_ne hu0]
    norm_num
  · intro x hx y hy hxy
    have hfcont : ContinuousOn (fun t => ∫ s in (-1)..t, unitPole s) (Icc (-1) 1) := by
      have h := intervalIntegral.continuousOn_primitive_interval' (f := unitPole) (μ := volume)
        (a := -1) (b₁ := -1) (b₂ := 1) unitPole_intervalIntegrable left_mem_uIcc
      rwa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at h
    exact abs_sub_le_integral_of_finite_exception_majorant (by norm_num) hfcont
      unitPole_intervalIntegrable {0}
      (fun u hu huD => by
        have hu0 : u ≠ 0 := by intro h; exact huD (by simp [h])
        have hd : HasDerivAt (fun t => ∫ s in (-1)..t, unitPole s) (unitPole u) u :=
          hasDerivAt_primitive_of_continuousAt unitPole_intervalIntegrable hu
            (unitPole_continuousAt hu0)
        exact ⟨hd.differentiableAt, by rw [hd.deriv, unitPole_of_ne hu0]; norm_num,
          unitPole_continuousAt hu0⟩)
      x hx y hy hxy

/-! ## The special case `ContinuousOn g (Ioo a b)`: singularities allowed at the endpoints -/

/-- The landed continuous-majorant theorem needs `ContinuousOn g (Icc a b)`.  If `g` is continuous
only on the *open* window and merely interval integrable on the closed one, the incremental bound
still holds: the endpoints of the window may carry genuine singularities of the majorant. -/
theorem abs_sub_le_integral_of_continuousOn_interior {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hfc : ContinuousOn f (Icc a b)) (hgi : IntervalIntegrable g volume a b)
    (hgc : ContinuousOn g (Ioo a b))
    (hfd : DifferentiableOn ℝ f (Ioo a b))
    (hmaj : ∀ u ∈ Ioo a b, |deriv f u| ≤ g u) :
    ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y → |f y - f x| ≤ ∫ t in x..y, g t := by
  refine abs_sub_le_integral_of_derivative_majorant hab hfc hgi ?_ hfd hmaj
  intro u hu
  exact hasDerivAt_primitive_of_continuousAt hgi hu (hgc.continuousAt (isOpen_Ioo.mem_nhds hu))

/-- Absolute continuity from `ContinuousOn g (Ioo a b)` plus interval integrability. -/
theorem absolutelyContinuousOnInterval_of_continuousOn_interior {f g : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hfc : ContinuousOn f (Icc a b)) (hgi : IntervalIntegrable g volume a b)
    (hgc : ContinuousOn g (Ioo a b))
    (hfd : DifferentiableOn ℝ f (Ioo a b))
    (hmaj : ∀ u ∈ Ioo a b, |deriv f u| ≤ g u) :
    AbsolutelyContinuousOnInterval f a b :=
  absolutelyContinuousOnInterval_of_interval_bound hab hgi
    (abs_sub_le_integral_of_continuousOn_interior hab hfc hgi hgc hfd hmaj)

/-- Fundamental theorem of calculus from `ContinuousOn g (Ioo a b)` plus interval integrability. -/
theorem intervalIntegral_deriv_eq_sub_of_continuousOn_interior {f g : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hfc : ContinuousOn f (Icc a b)) (hgi : IntervalIntegrable g volume a b)
    (hgc : ContinuousOn g (Ioo a b))
    (hfd : DifferentiableOn ℝ f (Ioo a b))
    (hmaj : ∀ u ∈ Ioo a b, |deriv f u| ≤ g u) :
    ∫ t in a..b, deriv f t = f b - f a :=
  AbsolutelyContinuousOnInterval.integral_deriv_eq_sub
    (absolutelyContinuousOnInterval_of_continuousOn_interior hab hfc hgi hgc hfd hmaj)

/-! ## Two-step recipe: absolute continuity from regular data, quantitative bound from wild data -/

/-- **Two-step recipe.**

Suppose `f` satisfies a pointwise derivative bound against a majorant `g₀` that is merely
continuous *off a finite set* (this is what a Russo-type formula delivers off the corner radii, for
a source-law reason), and *separately* an almost-everywhere bound `|f'| ≤ g` against an arbitrary
interval-integrable majorant `g` (this is what a merely measurable log-error factor can deliver).

Then `|f y - f x| ≤ ∫_x^y g`: the first bound is used only to obtain absolute continuity of `f`,
after which the second, much weaker, hypothesis suffices for the quantitative estimate.  In
particular no regularity whatsoever is required of the majorant that enters the final bound. -/
theorem abs_sub_le_integral_of_two_step {f g₀ g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hfc : ContinuousOn f (Icc a b)) (hg₀i : IntervalIntegrable g₀ volume a b)
    (D : Finset ℝ)
    (hgood : ∀ u ∈ Ioo a b, u ∉ (D : Set ℝ) →
      DifferentiableAt ℝ f u ∧ |deriv f u| ≤ g₀ u ∧ ContinuousAt g₀ u)
    (hgi : IntervalIntegrable g volume a b)
    (hmaj : ∀ᵐ u ∂volume, u ∈ Ioo a b → |deriv f u| ≤ g u) :
    ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y → |f y - f x| ≤ ∫ t in x..y, g t :=
  abs_sub_le_integral_of_absolutelyContinuous_of_ae_abs_deriv_le hab
    (absolutelyContinuousOnInterval_of_finite_exception_majorant hab hfc hg₀i D hgood) hgi hmaj

end PercLib.CriticalLRP.LocalAC

/-! ## Axiom audit

Every declaration above must rest only on Lean's three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`); no `sorry`, no `native_decide`, no custom axiom.
-/

set_option linter.hashCommand false
set_option linter.style.longLine false

#print axioms PercLib.CriticalLRP.LocalAC.PrimitiveDerivativeMajorant
#print axioms PercLib.CriticalLRP.LocalAC.ContinuousAtOff
#print axioms PercLib.CriticalLRP.LocalAC.DerivBoundOff
#print axioms PercLib.CriticalLRP.LocalAC.hasDerivAt_primitive_of_continuousAt
#print axioms PercLib.CriticalLRP.LocalAC.abs_sub_le_integral_of_derivative_majorant
#print axioms PercLib.CriticalLRP.LocalAC.abs_sub_le_integral_of_finite_exception_majorant
#print axioms PercLib.CriticalLRP.LocalAC.absolutelyContinuousOnInterval_of_interval_bound
#print axioms PercLib.CriticalLRP.LocalAC.absolutelyContinuousOnInterval_of_finite_exception_majorant
#print axioms PercLib.CriticalLRP.LocalAC.intervalIntegral_deriv_eq_sub_of_finite_exception_majorant
#print axioms PercLib.CriticalLRP.LocalAC.ae_differentiableAt_of_finite_exception_majorant
#print axioms PercLib.CriticalLRP.LocalAC.sub_le_integral_of_absolutelyContinuous_of_ae_deriv_le
#print axioms PercLib.CriticalLRP.LocalAC.abs_sub_le_integral_of_absolutelyContinuous_of_ae_abs_deriv_le
#print axioms PercLib.CriticalLRP.LocalAC.abs_sub_le_integral_of_continuousOn_interior
#print axioms PercLib.CriticalLRP.LocalAC.absolutelyContinuousOnInterval_of_continuousOn_interior
#print axioms PercLib.CriticalLRP.LocalAC.intervalIntegral_deriv_eq_sub_of_continuousOn_interior
#print axioms PercLib.CriticalLRP.LocalAC.abs_sub_le_integral_of_two_step
#print axioms PercLib.CriticalLRP.LocalAC.stepFun
#print axioms PercLib.CriticalLRP.LocalAC.stepFun_zero
#print axioms PercLib.CriticalLRP.LocalAC.stepFun_of_pos
#print axioms PercLib.CriticalLRP.LocalAC.stepFun_of_nonpos
#print axioms PercLib.CriticalLRP.LocalAC.not_continuousAt_stepFun_zero
#print axioms PercLib.CriticalLRP.LocalAC.stepFun_differentiableAt_of_ne
#print axioms PercLib.CriticalLRP.LocalAC.stepFun_ae_differentiableAt
#print axioms PercLib.CriticalLRP.LocalAC.stepFun_counterexample
#print axioms PercLib.CriticalLRP.LocalAC.unitPole
#print axioms PercLib.CriticalLRP.LocalAC.unitPole_of_ne
#print axioms PercLib.CriticalLRP.LocalAC.unitPole_zero
#print axioms PercLib.CriticalLRP.LocalAC.unitPole_continuousAt
#print axioms PercLib.CriticalLRP.LocalAC.not_continuousAt_unitPole_zero
#print axioms PercLib.CriticalLRP.LocalAC.unitPole_ae_eq_one
#print axioms PercLib.CriticalLRP.LocalAC.unitPole_ae_eq_one_restrict
#print axioms PercLib.CriticalLRP.LocalAC.unitPole_intervalIntegrable
#print axioms PercLib.CriticalLRP.LocalAC.majorant_continuous_on_window_is_strictly_stronger
