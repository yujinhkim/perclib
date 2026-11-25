/-
# Interval absolute continuity from a uniform derivative majorant

This file isolates the analytic step that turns the *pointwise* `r`-derivative formula of
Lemma I.4.1 (Russo's formula for the cut-off cluster-volume expectation) into an *interval*
statement: an incremental bound for the cut mass across a whole window of radii, absolute
continuity on compact radius intervals, and the fundamental-theorem-of-calculus identity.

The cut-off profile `r ↦ K(r) 1{s ≤ r}` has a corner at every radius equal to an edge length.
For a fixed bounded window `[a,b]` only finitely many distinct edge lengths occur, so the
derivative formula is available off a **finite** exceptional set.  Accordingly the main results
below are stated for a finite exceptional set `D`; no derivative is claimed at the corners.

No theorem here assumes an absolute-continuity conclusion: the incremental bound is *derived*
from the pointwise derivative bound.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import PercLib.CriticalLRP.Analysis.Cutoff.RowSum
public import PercLib.CriticalLRP.Analysis.Cutoff.IntervalAC.Defs
public import PercLib.CriticalLRP.RussoInf.Degree

/-!
# Interval absolute continuity from a uniform derivative majorant

This file isolates the analytic step that turns the *pointwise* `r`-derivative formula of
Lemma I.4.1 (Russo's formula for the cut-off cluster-volume expectation) into an *interval*
statement: an incremental bound for the cut mass across a whole window of radii, absolute
continuity on compact radius intervals, and the fundamental-theorem-of-calculus identity.

The cut-off profile `r ↦ K(r) 1{s ≤ r}` has a corner at every radius equal to an edge length.
For a fixed bounded window `[a,b]` only finitely many distinct edge lengths occur, so the
derivative formula is available off a *finite* exceptional set.  Accordingly the main results
below are stated for a finite exceptional set `D`; no derivative is claimed at the corners.
-/

set_option autoImplicit false

@[expose] public section

open MeasureTheory Set Filter
open scoped Interval Topology

namespace PercLib.CriticalLRP.IntervalAC

/-- At an interior point of an interval on which `g` is continuous, the primitive
`u ↦ ∫ t in a..u, g t` has derivative `g u`. -/
theorem hasDerivAt_primitive_of_continuousOn {g : ℝ → ℝ} {a b : ℝ}
    (hg : ContinuousOn g (Icc a b)) {u : ℝ} (hu : u ∈ Ioo a b) :
    HasDerivAt (fun s => ∫ t in a..s, g t) (g u) u := by
  have hcu : ContinuousAt g u := hg.continuousAt (Icc_mem_nhds hu.1 hu.2)
  have hint : IntervalIntegrable g volume a u :=
    (hg.mono (Icc_subset_Icc le_rfl hu.2.le)).intervalIntegrable_of_Icc hu.1.le
  refine intervalIntegral.integral_hasDerivAt_right hint ?_ hcu
  exact ⟨Ioo a b, Ioo_mem_nhds hu.1 hu.2,
    (hg.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo⟩

/-- **Mean-value inequality with an integral majorant.**

If `f` is continuous on `[a,b]`, differentiable on `(a,b)`, and `|f'| ≤ g` there with `g`
continuous, then `|f y - f x| ≤ ∫ t in x..y, g t` for all `x ≤ y` in `[a,b]`.

This is the mean value theorem in the form needed for a radially varying majorant: the
constant-`C` version (`Convex.image_sub_le_mul_sub_of_deriv_le`) does not apply, so we compare
`f ∓ ∫ g` against the sign of its derivative. -/
theorem abs_sub_le_integral_of_deriv_le {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hfc : ContinuousOn f (Icc a b)) (hgc : ContinuousOn g (Icc a b))
    (hfd : DifferentiableOn ℝ f (Ioo a b))
    (hmaj : ∀ u ∈ Ioo a b, |deriv f u| ≤ g u) :
    ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y → |f y - f x| ≤ ∫ t in x..y, g t := by
  have hgc' : ContinuousOn g (uIcc a b) := by rwa [uIcc_of_le hab]
  have hgcI : IntervalIntegrable g volume a b := hgc'.intervalIntegrable
  set G : ℝ → ℝ := fun s => ∫ t in a..s, g t with hG
  have hGcont : ContinuousOn G (Icc a b) := by
    have h := intervalIntegral.continuousOn_primitive_interval' (f := g) (μ := volume)
      (a := a) (b₁ := a) (b₂ := b) hgcI left_mem_uIcc
    rwa [uIcc_of_le hab] at h
  have hGD : DifferentiableOn ℝ G (Ioo a b) := by
    intro u hu
    exact (hasDerivAt_primitive_of_continuousOn hgc hu).differentiableAt.differentiableWithinAt
  have hderiv : ∀ u ∈ Ioo a b, HasDerivAt G (g u) u := fun u hu =>
    hasDerivAt_primitive_of_continuousOn hgc hu
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
    have h1 : IntervalIntegrable g volume a x := by
      refine (hgc.mono ?_).intervalIntegrable
      rw [uIcc_of_le hx.1]
      exact Icc_subset_Icc le_rfl hx.2
    have h2 : IntervalIntegrable g volume x y := by
      refine (hgc.mono ?_).intervalIntegrable
      rw [uIcc_of_le hxy]
      exact Icc_subset_Icc hx.1 hy.2
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


/-- **Finite exceptional set version.**  The cut-off profile has a corner at every radius equal
to an edge length, so the derivative formula of Lemma I.4.1 is only available off a finite set
`D` of radii in a bounded window.  Splitting the window at the finitely many exceptional radii
and applying the corner-free inequality on each piece gives the same incremental bound. -/
theorem abs_sub_le_integral_of_finite_exception {f g : ℝ → ℝ} {a b : ℝ}
    (hfc : ContinuousOn f (Icc a b)) (hgc : ContinuousOn g (Icc a b))
    (D : Finset ℝ)
    (hgood : ∀ u ∈ Ioo a b, u ∉ (D : Set ℝ) →
      DifferentiableAt ℝ f u ∧ |deriv f u| ≤ g u) :
    ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y → |f y - f x| ≤ ∫ t in x..y, g t := by
  classical
  have hint : ∀ p ∈ Icc a b, ∀ q ∈ Icc a b, IntervalIntegrable g volume p q := by
    intro p hp q hq
    refine (hgc.mono ?_).intervalIntegrable
    rw [uIcc]
    exact Icc_subset_Icc (le_min hp.1 hq.1) (max_le hp.2 hq.2)
  have key : ∀ D : Finset ℝ, ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y →
      (∀ u ∈ Ioo x y, u ∉ (D : Set ℝ) → DifferentiableAt ℝ f u ∧ |deriv f u| ≤ g u) →
      |f y - f x| ≤ ∫ t in x..y, g t := by
    intro D
    induction D using Finset.induction with
    | empty =>
        intro x hx y hy hxy hloc
        have hsub : Icc x y ⊆ Icc a b :=
          fun t ht => ⟨le_trans hx.1 ht.1, le_trans ht.2 hy.2⟩
        refine abs_sub_le_integral_of_deriv_le hxy (hfc.mono hsub) (hgc.mono hsub) ?_ ?_
          x ⟨le_rfl, hxy⟩ y ⟨hxy, le_rfl⟩ hxy
        · exact fun u hu => ((hloc u hu (by simp)).1).differentiableWithinAt
        · exact fun u hu => (hloc u hu (by simp)).2
    | insert c s _ ih =>
        intro x hx y hy hxy hloc
        by_cases hc : c ∈ Icc x y
        · have hsub1 : ∀ u ∈ Ioo x c, u ∉ (s : Set ℝ) →
              DifferentiableAt ℝ f u ∧ |deriv f u| ≤ g u := by
            intro u hu hus
            exact hloc u ⟨hu.1, lt_of_lt_of_le hu.2 hc.2⟩ (by
              simp only [Finset.coe_insert, Set.mem_insert_iff, not_or]
              exact ⟨ne_of_lt hu.2, hus⟩)
          have hsub2 : ∀ u ∈ Ioo c y, u ∉ (s : Set ℝ) →
              DifferentiableAt ℝ f u ∧ |deriv f u| ≤ g u := by
            intro u hu hus
            exact hloc u ⟨lt_of_le_of_lt hc.1 hu.1, hu.2⟩ (by
              simp only [Finset.coe_insert, Set.mem_insert_iff, not_or]
              exact ⟨ne_of_gt hu.1, hus⟩)
          have hc' : c ∈ Icc a b := ⟨le_trans hx.1 hc.1, le_trans hc.2 hy.2⟩
          have h1 : |f c - f x| ≤ (∫ t in x..c, g t) := ih x hx c hc' hc.1 hsub1
          have h2 : |f y - f c| ≤ (∫ t in c..y, g t) := ih c hc' y hy hc.2 hsub2
          have hsplit : (∫ t in x..c, g t) + (∫ t in c..y, g t) = ∫ t in x..y, g t :=
            intervalIntegral.integral_add_adjacent_intervals (hint x hx c hc') (hint c hc' y hy)
          have htri : |f y - f x| ≤ |f y - f c| + |f c - f x| := by
            have heq : f y - f x = (f y - f c) + (f c - f x) := by ring
            rw [heq]; exact abs_add_le _ _
          linarith
        · have hsub : ∀ u ∈ Ioo x y, u ∉ (s : Set ℝ) →
              DifferentiableAt ℝ f u ∧ |deriv f u| ≤ g u := by
            intro u hu hus
            exact hloc u hu (by
              simp only [Finset.coe_insert, Set.mem_insert_iff, not_or]
              exact ⟨fun h => hc (h ▸ ⟨le_of_lt hu.1, le_of_lt hu.2⟩), hus⟩)
          exact ih x hx y hy hxy hsub
  intro x hx y hy hxy
  refine key D x hx y hy hxy ?_
  intro u hu huD
  exact hgood u ⟨lt_of_le_of_lt hx.1 hu.1, lt_of_lt_of_le hu.2 hy.2⟩ huD


/-- **Absolute continuity from the incremental bound.**

If `|f y - f x| ≤ ∫ t in x..y, g t` for all `x ≤ y` in `[a,b]`, then `f` is absolutely
continuous on `[a,b]`: `f` is `1`-Lipschitz for the pseudo-metric `(x,y) ↦ ∫ t in x..y, |g t|`,
which is itself the distance induced by the absolutely continuous primitive of `|g|`. -/
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

/-- **Fundamental theorem of calculus across a window of cut-off radii.**

Combining the finite-exception incremental bound with the absolute-continuity transfer gives
`∫ t in a..b, deriv f t = f b - f a`: the cut mass is the integral of its own radial derivative
across the window.  No derivative is claimed at the corners. -/
theorem intervalIntegral_deriv_eq_sub_of_finite_exception {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hfc : ContinuousOn f (Icc a b)) (hgc : ContinuousOn g (Icc a b))
    (D : Finset ℝ)
    (hgood : ∀ u ∈ Ioo a b, u ∉ (D : Set ℝ) →
      DifferentiableAt ℝ f u ∧ |deriv f u| ≤ g u) :
    ∫ t in a..b, deriv f t = f b - f a := by
  have hgc' : ContinuousOn g (uIcc a b) := by rwa [uIcc_of_le hab]
  exact AbsolutelyContinuousOnInterval.integral_deriv_eq_sub
    (absolutelyContinuousOnInterval_of_interval_bound hab hgc'.intervalIntegrable
      (fun x hx y hy hxy =>
        abs_sub_le_integral_of_finite_exception hfc hgc D hgood x hx y hy hxy))

/-- **Almost-everywhere differentiability of the cut mass in its radius.**

Away from the (Lebesgue-null) set of exceptional radii the derivative exists; in particular the
radial derivative of the cut mass exists for almost every radius in the window. -/
theorem ae_differentiableAt_of_finite_exception {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hfc : ContinuousOn f (Icc a b)) (hgc : ContinuousOn g (Icc a b))
    (D : Finset ℝ)
    (hgood : ∀ u ∈ Ioo a b, u ∉ (D : Set ℝ) →
      DifferentiableAt ℝ f u ∧ |deriv f u| ≤ g u) :
    ∀ᵐ x, x ∈ Icc a b → DifferentiableAt ℝ f x := by
  have hgc' : ContinuousOn g (uIcc a b) := by rwa [uIcc_of_le hab]
  have h := (absolutelyContinuousOnInterval_of_interval_bound hab hgc'.intervalIntegrable
      (fun x hx y hy hxy =>
        abs_sub_le_integral_of_finite_exception hfc hgc D hgood x hx y hy hxy)).ae_differentiableAt
  rwa [uIcc_of_le hab] at h



end PercLib.CriticalLRP.IntervalAC


/-! ## The source model: the cut-off cluster mass `χ(r) = E_{β_c,r}|K|` -/

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- The cut-off cluster mass is nondecreasing in the cut-off radius.  Unconditional, and *not* new
at the cut-off-radius level: it is `SourceModelData.cutMoment_monotone 1` transported across
`cutMassAt_zero_eq_cutMoment`.  It is restated here by the row-sum route
(`tsum_cutTwoPointE_eq_cutMassAt` + `cutTwoPointE_mono_r`) so that this file's use of monotonicity
is self-contained. -/
theorem cutMassAt_mono {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r') (h : r ≤ r') :
    M.cutMassAt r 0 ≤ M.cutMassAt r' 0 := by
  rw [← M.tsum_cutTwoPointE_eq_cutMassAt r 0, ← M.tsum_cutTwoPointE_eq_cutMassAt r' 0]
  exact ENNReal.tsum_le_tsum fun y => M.cutTwoPointE_mono_r hr hr' h 0 y

/-- With finiteness of the cluster mass at the right endpoint, `r ↦ χ(r)` is monotone on the
window `[a,b]`. -/
theorem cutMassReal_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hfin : M.cutMassAt b 0 ≠ ⊤) :
    MonotoneOn M.cutMassReal (Icc a b) := by
  intro r hr r' hr' hrr'
  have hr0 : 0 < r := lt_of_lt_of_le ha hr.1
  have hr'0 : 0 < r' := lt_of_lt_of_le ha hr'.1
  have hb0 : 0 < b := lt_of_lt_of_le ha hab
  have hle := M.cutMassAt_mono hr'0 hb0 hr'.2
  exact ENNReal.toReal_mono (ne_top_of_le_ne_top hfin hle) (M.cutMassAt_mono hr0 hr'0 hrr')

/-- The window increment of the cut mass is nonnegative under finiteness at the right endpoint. -/
theorem cutMassReal_sub_nonneg {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hfin : M.cutMassAt b 0 ≠ ⊤) : 0 ≤ M.cutMassReal b - M.cutMassReal a :=
  sub_nonneg.mpr ((M.cutMassReal_mono ha hab hfin) ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab)

/-- **Almost-everywhere differentiability of the cut-off cluster mass, with no regularity
hypothesis**: only finiteness of the cluster mass at the right endpoint is needed, since
`r ↦ χ(r)` is monotone on the window.  (This is the a.e. existence half of Lemma I.4.1.) -/
theorem cutMassReal_ae_differentiableWithinAt {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hfin : M.cutMassAt b 0 ≠ ⊤) :
    ∀ᵐ t, t ∈ Icc a b → DifferentiableWithinAt ℝ M.cutMassReal (Icc a b) t :=
  (M.cutMassReal_mono ha hab hfin).ae_differentiableWithinAt_of_mem

/-- **The radial derivative of the cut mass is interval integrable** on any window on which the
cluster mass is finite at the right endpoint — again by monotonicity alone. -/
theorem intervalIntegrable_deriv_cutMassReal {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hfin : M.cutMassAt b 0 ≠ ⊤) :
    IntervalIntegrable (deriv M.cutMassReal) volume a b := by
  refine MonotoneOn.intervalIntegrable_deriv ?_
  rw [uIcc_of_le hab]
  exact M.cutMassReal_mono ha hab hfin

/-- **The fundamental theorem of calculus, inequality half, for the cut mass**: the integral of
the radial derivative over a window is at most the increment of the cut mass.  This needs no
differentiability at all — only monotonicity and finiteness at the right endpoint. -/
theorem integral_deriv_cutMassReal_le_sub {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hfin : M.cutMassAt b 0 ≠ ⊤) :
    ∫ t in a..b, deriv M.cutMassReal t ≤ M.cutMassReal b - M.cutMassReal a := by
  have h : MonotoneOn M.cutMassReal (Set.uIcc a b) := by
    rw [uIcc_of_le hab]; exact M.cutMassReal_mono ha hab hfin
  have hmem := MonotoneOn.intervalIntegral_deriv_mem_uIcc h
  rw [uIcc_of_le (M.cutMassReal_sub_nonneg ha hab hfin)] at hmem
  exact hmem.2

/-- The derivative of the cut mass is nonnegative in integral form: `0 ≤ ∫ χ'` over a window on
which the cut mass is finite at the right endpoint. -/
theorem integral_deriv_cutMassReal_nonneg {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hfin : M.cutMassAt b 0 ≠ ⊤) :
    0 ≤ ∫ t in a..b, deriv M.cutMassReal t := by
  have h : MonotoneOn M.cutMassReal (Set.uIcc a b) := by
    rw [uIcc_of_le hab]; exact M.cutMassReal_mono ha hab hfin
  have hmem := MonotoneOn.intervalIntegral_deriv_mem_uIcc h
  rw [uIcc_of_le (M.cutMassReal_sub_nonneg ha hab hfin)] at hmem
  exact hmem.1

/-- The `ℓ^∞` edge lengths used by the `RussoInf` machinery are natural numbers, so every radius in
`[0,b)` of the form `(edgeLen e : ℝ)` lies in the explicit finite set `{0, 1, …, ⌈b⌉}`: for the
`ℓ^∞` cut-off graph the corner set is finite *without any hypothesis*.  For the model's own cut-off,
which uses `M.S.ρ`, the corner set is `M.cornerRadii` instead; see the note there. -/
theorem edgeLen_mem_cornerSet {b r : ℝ} (hrb : r < b) {e : Sym2 M.V}
    (he : (PercLib.CriticalLRP.FiniteVolume.edgeLen (d := M.d) e : ℝ) = r) :
    r ∈ ((Finset.range (Nat.ceil b + 1)).image (fun n : ℕ => (n : ℝ)) : Set ℝ) := by
  set k := PercLib.CriticalLRP.FiniteVolume.edgeLen (d := M.d) e with hk
  have hk' : (k : ℝ) = r := by rw [hk]; exact he
  have h1 : (k : ℝ) < b := by rw [hk']; exact hrb
  have h2 : (k : ℝ) < (Nat.ceil b : ℝ) := by linarith [Nat.le_ceil b]
  have h3 : k < Nat.ceil b := by exact_mod_cast h2
  rw [Finset.mem_coe, Finset.mem_image]
  exact ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_lt h3), he⟩

/-- **Incremental bound for the cut-off cluster mass across a window of radii.**

Given continuity of `r ↦ χ(r)`, finiteness of the corner set in the window, and the pointwise Russo
bound `|χ'(r)| ≤ g(r)` at every radius which is *not* a corner radius, the cut mass changes by at
most `∫ t in x..y, g t`.  The finite-exception machinery makes the corner set harmless, and no
derivative is claimed at a corner radius. -/
theorem cutMassReal_abs_sub_le_integral {a b : ℝ}
    (hcont : ContinuousOn M.cutMassReal (Icc a b)) {g : ℝ → ℝ} (hgcont : ContinuousOn g (Icc a b))
    (hDfin : (M.cornerRadii ∩ Ioo a b).Finite)
    (hgood : ∀ u ∈ Ioo a b, u ∉ M.cornerRadii →
      DifferentiableAt ℝ M.cutMassReal u ∧ |deriv M.cutMassReal u| ≤ g u) :
    ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y →
      |M.cutMassReal y - M.cutMassReal x| ≤ ∫ t in x..y, g t :=
  PercLib.CriticalLRP.IntervalAC.abs_sub_le_integral_of_finite_exception hcont hgcont
    hDfin.toFinset
    (fun u hu huD =>
      hgood u hu (fun hmem => huD (by rw [hDfin.coe_toFinset]; exact ⟨hmem, hu⟩)))

/-- **The cut-off cluster mass is absolutely continuous in its radius** on any window where the
corner set is finite and the Russo bound holds with a continuous majorant. -/
theorem cutMassReal_absolutelyContinuousOn {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn M.cutMassReal (Icc a b)) {g : ℝ → ℝ} (hgcont : ContinuousOn g (Icc a b))
    (hDfin : (M.cornerRadii ∩ Ioo a b).Finite)
    (hgood : ∀ u ∈ Ioo a b, u ∉ M.cornerRadii →
      DifferentiableAt ℝ M.cutMassReal u ∧ |deriv M.cutMassReal u| ≤ g u) :
    AbsolutelyContinuousOnInterval M.cutMassReal a b := by
  have hgc : ContinuousOn g (uIcc a b) := by rwa [uIcc_of_le hab]
  exact PercLib.CriticalLRP.IntervalAC.absolutelyContinuousOnInterval_of_interval_bound hab
    hgc.intervalIntegrable (M.cutMassReal_abs_sub_le_integral hcont hgcont hDfin hgood)

/-- **Fundamental theorem of calculus for the cut mass across a window of radii.** -/
theorem cutMassReal_intervalIntegral_deriv {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn M.cutMassReal (Icc a b)) {g : ℝ → ℝ} (hgcont : ContinuousOn g (Icc a b))
    (hDfin : (M.cornerRadii ∩ Ioo a b).Finite)
    (hgood : ∀ u ∈ Ioo a b, u ∉ M.cornerRadii →
      DifferentiableAt ℝ M.cutMassReal u ∧ |deriv M.cutMassReal u| ≤ g u) :
    ∫ t in a..b, deriv M.cutMassReal t = M.cutMassReal b - M.cutMassReal a :=
  AbsolutelyContinuousOnInterval.integral_deriv_eq_sub
    (M.cutMassReal_absolutelyContinuousOn hab hcont hgcont hDfin hgood)

/-- **Almost-everywhere differentiability of the cut-off cluster mass in its radius**, conditional
form from absolute continuity.  `cutMassReal_ae_differentiableWithinAt` proves the same conclusion
with no regularity hypothesis at all. -/
theorem cutMassReal_ae_differentiableAt {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn M.cutMassReal (Icc a b)) {g : ℝ → ℝ} (hgcont : ContinuousOn g (Icc a b))
    (hDfin : (M.cornerRadii ∩ Ioo a b).Finite)
    (hgood : ∀ u ∈ Ioo a b, u ∉ M.cornerRadii →
      DifferentiableAt ℝ M.cutMassReal u ∧ |deriv M.cutMassReal u| ≤ g u) :
    ∀ᵐ t, t ∈ Icc a b → DifferentiableAt ℝ M.cutMassReal t := by
  have h := (M.cutMassReal_absolutelyContinuousOn hab hcont hgcont hDfin hgood).ae_differentiableAt
  rwa [uIcc_of_le hab] at h

end SourceModelData

end PercLib.CriticalLRP.Orchestration

set_option linter.hashCommand false

/-! ## Axiom audit

Every declaration above must rest only on Lean's three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`): no `sorry`, no `native_decide`, no custom axiom.
-/

open PercLib.CriticalLRP.Orchestration.SourceModelData

#print axioms PercLib.CriticalLRP.IntervalAC.hasDerivAt_primitive_of_continuousOn
#print axioms PercLib.CriticalLRP.IntervalAC.abs_sub_le_integral_of_deriv_le
#print axioms PercLib.CriticalLRP.IntervalAC.abs_sub_le_integral_of_finite_exception
#print axioms PercLib.CriticalLRP.IntervalAC.absolutelyContinuousOnInterval_of_interval_bound
#print axioms PercLib.CriticalLRP.IntervalAC.intervalIntegral_deriv_eq_sub_of_finite_exception
#print axioms PercLib.CriticalLRP.IntervalAC.ae_differentiableAt_of_finite_exception
#print axioms cutMassAt_mono
#print axioms cutMassReal_mono
#print axioms cutMassReal_sub_nonneg
#print axioms cutMassReal_ae_differentiableWithinAt
#print axioms intervalIntegrable_deriv_cutMassReal
#print axioms integral_deriv_cutMassReal_le_sub
#print axioms integral_deriv_cutMassReal_nonneg
#print axioms edgeLen_mem_cornerSet
#print axioms cutMassReal_abs_sub_le_integral
#print axioms cutMassReal_absolutelyContinuousOn
#print axioms cutMassReal_intervalIntegral_deriv
#print axioms cutMassReal_ae_differentiableAt
