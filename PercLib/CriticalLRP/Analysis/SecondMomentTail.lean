/-
Integrated and independently rebuilt from accepted Ultramath `smwyvlg99`, member `m1`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Swarm `smwyvlg99`, member `m1`, direction `d1`.

# Absolute continuity and a.e. radius derivative of the `p = 2` cutoff moment

This file supplies the two radius-regularity inputs `hac` and `hae` of the `p = 2` case of
Hutchcroft's Lemma I.4.1 from the *integrated* radius identity

`∫ t in a..x, M.rhsScalarTwo t = M.cutMomentReal 2 x - M.cutMomentReal 2 a`   (`x ∈ [a,b]`),

which is the landed output of the monotone-convergence / dominated-convergence exchanges
(`SecondMoment.Integrated.Main.integral_rhsScalarTwo_eq_sub_of_window`,
`SecondMoment.Integrated.RadiusFTC.integral_rhsScalarTwo_eq_sub_of_window_majorant`).

The two analytic facts used are Mathlib's primitive theory for interval integrals:

* `IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral` — the primitive of an
  interval-integrable function is absolutely continuous on the interval;
* `IntervalIntegrable.ae_hasDerivAt_integral` — the interval version of the Lebesgue
  differentiation theorem: the derivative of that primitive is the integrand a.e.

Consequently the step from the integrated identity to `hac`/`hae` needs no pointwise majorant of
the flux, no continuity of the flux at any radius, no corner-free window and no window-index
monotonicity: `L¹`-control of `M.rhsScalarTwo` on the window plus the integrated identity suffice.
(The *landed* producers of the integrated identity do take an off-corner window
`M.IsOffCornerWindow a b`, because the finite-window Russo identity needs differentiability of the
edge probability at every radius of the window; that is an input of the flux side, not of the
AC/differentiation step.)  In particular `hac` and `hae` on a window are *strictly weaker* inputs
than the landed conditional pointwise derivative
`SourceModelData.hasDerivAt_cutMomentReal_two_*`, which needs the off-corner continuity of the RHS
at the radius.

Conversely, `integral_eq_sub_of_absolutelyContinuousOnInterval_of_ae_hasDerivAt` shows that
`hac` together with the a.e. derivative recovers the integrated identity, so the two forms are
equivalent inputs and the identity is the exact remaining obligation.

No `sorry`, no `admit`, no `native_decide`, no custom axiom.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Integrated.RadiusFTC
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Integrated.Assembly
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.WindowMajorant.Main
public import PercLib.CriticalLRP.Analysis.SecondMomentCase1
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# `hac` and `hae` of the `p = 2` radius picture, from the integrated identity
-/

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration.Smwyvlg99M1

/-! ## 1. Abstract core: an integral representation gives AC and the a.e. derivative -/

/-- **Absolute continuity from an integral representation.**  If `f` is, on `uIcc a b`, the sum
of a constant and the primitive from `a` of an interval-integrable `g`, then `f` is absolutely
continuous on `uIcc a b`.

No continuity, boundedness or sign condition on `g` is used: only its interval integrability.
-/
theorem absolutelyContinuousOnInterval_of_eq_add_integral {f g : ℝ → ℝ} {a b : ℝ}
    (hint : IntervalIntegrable g volume a b)
    (h : ∀ x ∈ Set.uIcc a b, f x = f a + ∫ t in a..x, g t) :
    AbsolutelyContinuousOnInterval f a b := by
  have hF : AbsolutelyContinuousOnInterval (fun x => ∫ t in a..x, g t) a b :=
    hint.absolutelyContinuousOnInterval_intervalIntegral left_mem_uIcc
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => f a) a b :=
    (LipschitzWith.const (f a)).lipschitzOnWith.absolutelyContinuousOnInterval
  refine (hc.add hF).congr ?_
  intro x hx
  exact (h x hx).symm

/-- **The a.e. radius derivative from an integral representation.**  If `f` is, on `uIcc a b`,
the sum of a constant and the primitive from `a` of an interval-integrable `g`, then for almost
every radius `x` of `(a,b)` the function `f` has derivative `g x` at `x`.

This is the interval Lebesgue differentiation theorem applied to the primitive, transferred to
`f` along the local identity.  It gives the derivative at almost every radius *without* knowing
whether `g` is continuous at any particular radius.
-/
theorem ae_hasDerivAt_of_eq_add_integral {f g : ℝ → ℝ} {a b : ℝ}
    (hint : IntervalIntegrable g volume a b)
    (h : ∀ x ∈ Set.uIcc a b, f x = f a + ∫ t in a..x, g t) :
    ∀ᵐ x ∂volume, x ∈ Set.Ioo a b → HasDerivAt f (g x) x := by
  filter_upwards [hint.ae_hasDerivAt_integral] with x hx hxIoo
  have hxU : x ∈ Set.uIcc a b := Icc_subset_uIcc (Ioo_subset_Icc_self hxIoo)
  have h1 : HasDerivAt (fun y => f a + ∫ t in a..y, g t) (g x) x :=
    (hx hxU a left_mem_uIcc).const_add (f a)
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hxIoo.1 hxIoo.2] with y hy
  exact h y (Icc_subset_uIcc (Ioo_subset_Icc_self hy))

/-- **The a.e. derivative, written as an a.e. equality of `deriv`.**  A function that has
derivative `g x` at almost every radius of `(a,b)` has `deriv` equal to `g` almost everywhere
with respect to the restriction of Lebesgue measure to `(a,b)`. -/
theorem deriv_ae_eq_of_ae_hasDerivAt {f g : ℝ → ℝ} {a b : ℝ}
    (h : ∀ᵐ x ∂volume, x ∈ Set.Ioo a b → HasDerivAt f (g x) x) :
    deriv f =ᵐ[volume.restrict (Set.Ioo a b)] g := by
  filter_upwards [ae_restrict_iff' measurableSet_Ioo |>.mpr h] with x hx
  exact hx.deriv

/-- **`hac` plus the a.e. derivative gives back the integrated identity.**  An absolutely
continuous function whose a.e. radius derivative is `g` satisfies the fundamental theorem of
calculus with integrand `g`:

`∫ t in a..b, g t = f b - f a`.

Together with `absolutelyContinuousOnInterval_of_eq_add_integral` and
`ae_hasDerivAt_of_eq_add_integral` this shows that `hac`+`hae` and the integrated identity are
equivalent inputs on a radius window, so the integrated identity is the exact remaining
obligation and `hac`/`hae` add no further strength.
-/
theorem integral_eq_sub_of_absolutelyContinuousOnInterval_of_ae_hasDerivAt {f g : ℝ → ℝ}
    {a b : ℝ} (hab : a ≤ b) (hac : AbsolutelyContinuousOnInterval f a b)
    (h : ∀ᵐ x ∂volume, x ∈ Set.Ioo a b → HasDerivAt f (g x) x) :
    ∫ x in a..b, g x = f b - f a := by
  rw [← hac.integral_deriv_eq_sub]
  refine intervalIntegral.integral_congr_ae ?_
  have hb : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ b := by
    rw [ae_iff]
    simp
  filter_upwards [h, hb] with x hx hxb hxu
  rw [uIoc_of_le hab] at hxu
  exact (hx ⟨hxu.1, lt_of_le_of_ne hxu.2 hxb⟩).deriv.symm


/-! ## 2. The source model: `hac` and `hae` from the integrated radius identity -/

/-! ## 2. The source model: `hac` and `hae` from the integrated radius identity -/

variable (M : SourceModelData)

/-- **`hac` at `p = 2` from the integrated identity.**  On a radius window on which the actual
second cutoff moment is the primitive of `M.rhsScalarTwo`, the function `r ↦ (M.cutMoment 2 r).toReal`
is absolutely continuous.

The only analytic input is interval integrability of `M.rhsScalarTwo` on the window; in contrast
the landed conditional statement `SourceModelData.cutMomentReal_absolutelyContinuousOn_two` needs
the pointwise off-corner derivative together with a *continuous* majorant of it. -/
theorem absolutelyContinuousOnInterval_cutMomentReal_two {a b : ℝ} (hab : a ≤ b)
    (hint : IntervalIntegrable (fun t => M.rhsScalarTwo t) volume a b)
    (hid : ∀ x ∈ Set.Icc a b,
      ∫ t in a..x, M.rhsScalarTwo t = M.cutMomentReal 2 x - M.cutMomentReal 2 a) :
    AbsolutelyContinuousOnInterval (fun r => M.cutMomentReal 2 r) a b := by
  refine absolutelyContinuousOnInterval_of_eq_add_integral hint ?_
  intro x hx
  rw [Set.uIcc_of_le hab] at hx
  rw [hid x hx]
  ring

/-- **`hae` at `p = 2` from the integrated identity.**  On a radius window on which the actual
second cutoff moment is the primitive of `M.rhsScalarTwo`, for almost every radius of the window
the moment has derivative `M.rhsScalarTwo r`. -/
theorem ae_hasDerivAt_cutMomentReal_two {a b : ℝ} (hab : a ≤ b)
    (hint : IntervalIntegrable (fun t => M.rhsScalarTwo t) volume a b)
    (hid : ∀ x ∈ Set.Icc a b,
      ∫ t in a..x, M.rhsScalarTwo t = M.cutMomentReal 2 x - M.cutMomentReal 2 a) :
    ∀ᵐ r ∂volume,
      r ∈ Set.Ioo a b →
        HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r) r := by
  refine ae_hasDerivAt_of_eq_add_integral hint ?_
  intro x hx
  rw [Set.uIcc_of_le hab] at hx
  rw [hid x hx]
  ring

/-- **The a.e. radius derivative as an a.e. equality of `deriv`.** -/
theorem deriv_ae_eq_rhsScalarTwo {a b : ℝ} (hab : a ≤ b)
    (hint : IntervalIntegrable (fun t => M.rhsScalarTwo t) volume a b)
    (hid : ∀ x ∈ Set.Icc a b,
      ∫ t in a..x, M.rhsScalarTwo t = M.cutMomentReal 2 x - M.cutMomentReal 2 a) :
    deriv (fun r => M.cutMomentReal 2 r) =ᵐ[volume.restrict (Set.Ioo a b)]
      fun t => M.rhsScalarTwo t :=
  deriv_ae_eq_of_ae_hasDerivAt (ae_hasDerivAt_cutMomentReal_two M hab hint hid)

/-! ## 3. Instantiation from the landed integrated identity with a flux majorant

`SourceModelData.integral_rhsScalarTwo_eq_sub_of_window_majorant` produces the integrated identity
from a uniform-in-window majorant `G` of the flux, i.e. *without* the window-index monotonicity
`hfluxMono` that the pointwise derivative routes need.  Composing it with §2 gives `hac`/`hae`
under exactly those weaker flux inputs. -/

/-- **`hac` without window-flux monotonicity**, from a uniform-in-window majorant of the flux. -/
theorem absolutelyContinuousOnInterval_cutMomentReal_two_of_window_majorant {a b : ℝ}
    (hwin : M.IsOffCornerWindow a b) (S : ℕ → Finset (Sym2 M.V)) {G : ℝ → ℝ}
    (hfluxMaj : ∀ n, ∀ t ∈ Set.Ioc a b, M.windowFlux (S n) t ≤ G t)
    (hG : IntegrableOn G (Set.Ioc a b) volume)
    (hfluxConv : ∀ t, Tendsto (fun n => M.windowFlux (S n) t) atTop (𝓝 (M.rhsScalarTwo t)))
    (hmoment : ∀ x ∈ Set.Icc a b,
      Tendsto (fun n => M.windowMoment (S n) x - M.windowMoment (S n) a) atTop
        (𝓝 (M.cutMomentReal 2 x - M.cutMomentReal 2 a)))
    (hrhsInt : IntervalIntegrable (fun t => M.rhsScalarTwo t) volume a b) :
    AbsolutelyContinuousOnInterval (fun r => M.cutMomentReal 2 r) a b :=
  absolutelyContinuousOnInterval_cutMomentReal_two M hwin.2.1 hrhsInt
    (M.integral_rhsScalarTwo_eq_sub_of_window_majorant hwin S hfluxMaj hG hfluxConv hmoment)

/-- **`hae` without window-flux monotonicity**, from a uniform-in-window majorant of the flux. -/
theorem ae_hasDerivAt_cutMomentReal_two_of_window_majorant {a b : ℝ}
    (hwin : M.IsOffCornerWindow a b) (S : ℕ → Finset (Sym2 M.V)) {G : ℝ → ℝ}
    (hfluxMaj : ∀ n, ∀ t ∈ Set.Ioc a b, M.windowFlux (S n) t ≤ G t)
    (hG : IntegrableOn G (Set.Ioc a b) volume)
    (hfluxConv : ∀ t, Tendsto (fun n => M.windowFlux (S n) t) atTop (𝓝 (M.rhsScalarTwo t)))
    (hmoment : ∀ x ∈ Set.Icc a b,
      Tendsto (fun n => M.windowMoment (S n) x - M.windowMoment (S n) a) atTop
        (𝓝 (M.cutMomentReal 2 x - M.cutMomentReal 2 a)))
    (hrhsInt : IntervalIntegrable (fun t => M.rhsScalarTwo t) volume a b) :
    ∀ᵐ r ∂volume,
      r ∈ Set.Ioo a b →
        HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r) r :=
  ae_hasDerivAt_cutMomentReal_two M hwin.2.1 hrhsInt
    (M.integral_rhsScalarTwo_eq_sub_of_window_majorant hwin S hfluxMaj hG hfluxConv hmoment)


/-! ## 4. Tail assembly: `hac` and `hae` with the moment and integrability inputs discharged -/

/-- **The `p = 2` radius picture on a positive off-corner tail, from a uniform flux majorant.**

On an off-corner window `[a,b]` of the positive tail (`0 < a`), assume

* a monotone, edge-exhausting window family `S`;
* a finite second cutoff moment at the right endpoint `b` (all finiteness on the window follows);
* a bound `C` on `|M.coeffRHS|` on the window (the kernel-coefficient input; see §6);
* a uniform-in-window majorant `G` of the finite-window fluxes, integrable on `(a,b]`;
* pointwise-in-radius convergence of the window fluxes to `M.rhsScalarTwo`.

Then

* the actual second cutoff moment `r ↦ (M.cutMoment 2 r).toReal` is absolutely continuous on
  `[a,b]`;
* for almost every radius of `(a,b)` it has derivative `M.rhsScalarTwo r`;
* its `deriv` agrees with `M.rhsScalarTwo` almost everywhere on `(a,b)`;
* the integrated identity holds on the window;
* `M.rhsScalarTwo` is interval integrable on the window.

Neither the window-index monotonicity `hfluxMono` of the flux nor any continuity of
`M.rhsScalarTwo` at any radius is an input: the only analytic inputs are `L¹`-control of the
flux (`hG`) and of `M.rhsScalarTwo` (`hC` with the fourth moment).  This is strictly weaker
than the hypothesis set of `SourceModelData.hasDerivAt_cutMomentReal_two_of_window_majorant`,
which additionally needs `hrhsCont` at the radius. -/
theorem ac_and_ae_hasDerivAt_cutMomentReal_two_of_window_majorant {a b : ℝ}
    (hwin : M.IsOffCornerWindow a b) (S : ℕ → Finset (Sym2 M.V))
    (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ k, e ∈ S k)
    (h2b : M.cutMoment 2 b ≠ ⊤)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ r ∈ Set.Icc a b, |M.coeffRHS r| ≤ C)
    {G : ℝ → ℝ} (hfluxMaj : ∀ n, ∀ t ∈ Set.Ioc a b, M.windowFlux (S n) t ≤ G t)
    (hG : IntegrableOn G (Set.Ioc a b) volume)
    (hfluxConv : ∀ t, Tendsto (fun n => M.windowFlux (S n) t) atTop (𝓝 (M.rhsScalarTwo t))) :
    AbsolutelyContinuousOnInterval (fun r => M.cutMomentReal 2 r) a b ∧
      (∀ᵐ r ∂volume, r ∈ Set.Ioo a b →
        HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r) r) ∧
      (deriv (fun r => M.cutMomentReal 2 r) =ᵐ[volume.restrict (Set.Ioo a b)]
        fun t => M.rhsScalarTwo t) ∧
      (∀ x ∈ Set.Icc a b,
        ∫ t in a..x, M.rhsScalarTwo t = M.cutMomentReal 2 x - M.cutMomentReal 2 a) ∧
      IntervalIntegrable (fun t => M.rhsScalarTwo t) volume a b := by
  have hab : a ≤ b := hwin.2.1
  have hfin : ∀ x ∈ Set.Icc a b, M.cutMoment 2 x ≠ ⊤ :=
    fun x hx => M.cutMoment_ne_top_of_le hx.2 2 h2b
  have hmoment : ∀ x ∈ Set.Icc a b,
      Tendsto (fun n => M.windowMoment (S n) x - M.windowMoment (S n) a) atTop
        (𝓝 (M.cutMomentReal 2 x - M.cutMomentReal 2 a)) :=
    fun x hx => M.tendsto_windowMoment_sub S hSmono hS (hfin x hx)
      (hfin a ⟨le_refl a, hab⟩)
  have hmeas : Measurable fun t => M.rhsScalarTwo t := by
    have hlim : (fun t => M.rhsScalarTwo t)
        = fun t => liminf (fun n => M.windowFlux (S n) t) atTop := by
      funext t
      exact (hfluxConv t).liminf_eq.symm
    rw [hlim]
    exact Measurable.liminf fun n => M.measurable_windowFlux (S n)
  have hrhsInt : IntervalIntegrable (fun t => M.rhsScalarTwo t) volume a b :=
    M.intervalIntegrable_rhsScalarTwo_of_coeffBound hab hmeas hC0 hC
      (PercLib.CriticalLRP.CaseOne.cutMoment_four_ne_top_of_two M h2b)
  have hid := M.integral_rhsScalarTwo_eq_sub_of_window_majorant hwin S hfluxMaj hG hfluxConv
    hmoment
  exact ⟨absolutelyContinuousOnInterval_cutMomentReal_two M hab hrhsInt hid,
    ae_hasDerivAt_cutMomentReal_two M hab hrhsInt hid,
    deriv_ae_eq_rhsScalarTwo M hab hrhsInt hid, hid, hrhsInt⟩

/-! ## 5. Consequences of the absolute continuity, and the converse direction

Absolute continuity of the moment on a radius window is exactly the regularity needed to
integrate over the radius: it gives continuity, bounded variation and interval integrability of
`deriv`.  Conversely, `hac` together with the a.e. derivative recovers the integrated identity,
so no radius-regularity input beyond the identity is being introduced anywhere. -/

/-- **Continuity of the second cutoff moment from its absolute continuity.** -/
theorem continuousOn_cutMomentReal_two {a b : ℝ}
    (hac : AbsolutelyContinuousOnInterval (fun r => M.cutMomentReal 2 r) a b) (hab : a ≤ b) :
    ContinuousOn (fun r => M.cutMomentReal 2 r) (Set.Icc a b) := by
  have h := hac.continuousOn
  rwa [Set.uIcc_of_le hab] at h

/-- **Bounded variation of the second cutoff moment from its absolute continuity.** -/
theorem boundedVariationOn_cutMomentReal_two {a b : ℝ}
    (hac : AbsolutelyContinuousOnInterval (fun r => M.cutMomentReal 2 r) a b) (hab : a ≤ b) :
    BoundedVariationOn (fun r => M.cutMomentReal 2 r) (Set.Icc a b) := by
  have h := hac.boundedVariationOn
  rwa [Set.uIcc_of_le hab] at h

/-- **`deriv` of the second cutoff moment is interval integrable on the window.** -/
theorem intervalIntegrable_deriv_cutMomentReal_two {a b : ℝ}
    (hac : AbsolutelyContinuousOnInterval (fun r => M.cutMomentReal 2 r) a b) :
    IntervalIntegrable (deriv (fun r => M.cutMomentReal 2 r)) volume a b :=
  hac.intervalIntegrable_deriv

/-- **The converse: `hac` plus the a.e. derivative gives the integrated identity.**  On a radius
window, absolute continuity of the second cutoff moment together with the a.e. radius derivative
`M.rhsScalarTwo` implies the integrated identity with that right-hand side.

Combined with §2 this makes the integrated identity and the pair (`hac`, `hae`) equivalent inputs,
so the integrated identity is the exact remaining obligation of the `p = 2` radius picture. -/
theorem integral_rhsScalarTwo_eq_sub_of_absolutelyContinuousOnInterval {a b : ℝ} (hab : a ≤ b)
    (hac : AbsolutelyContinuousOnInterval (fun r => M.cutMomentReal 2 r) a b)
    (hae : ∀ᵐ r ∂volume,
      r ∈ Set.Ioo a b →
        HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r) r) :
    ∀ x ∈ Set.Icc a b,
      ∫ t in a..x, M.rhsScalarTwo t = M.cutMomentReal 2 x - M.cutMomentReal 2 a := by
  intro x hx
  have hacx : AbsolutelyContinuousOnInterval (fun r => M.cutMomentReal 2 r) a x :=
    hac.mono (uIcc_subset_uIcc left_mem_uIcc (Icc_subset_uIcc hx))
  have haex : ∀ᵐ r ∂volume,
      r ∈ Set.Ioo a x →
        HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r) r :=
    hae.mono fun r hr hra => hr (Set.Ioo_subset_Ioo_right hx.2 hra)
  exact integral_eq_sub_of_absolutelyContinuousOnInterval_of_ae_hasDerivAt hx.1 hacx haex

/-! ## 6. Audit of the coefficient input

`M.coeffRHS r = β_c (-(deriv M.K r))`.  Two facts about the coefficient bound
`|M.coeffRHS r| ≤ C` used in §4:

* it *is* supplied by continuity of `deriv M.K` on the compact window — a genuine C¹ hypothesis
  on the kernel's radial derivative, not mere differentiability;
* it is **not** supplied by the model's `K_diff : DifferentiableOn ℝ K (Set.Ioi 0)` alone:
  `DifferentiableOn` does not assert continuity of `deriv K`, so `deriv K` may be unbounded on a
  compact subinterval of `(0,∞)`.  `K_eq_integral` bounds only the *tail integral* of `|K'|`, and
  `exists_error` gives the pointwise size `|deriv K r| = (1 + δ r) r^{-d-α-1}` with `δ → 0` at
  infinity, which does not bound `δ` (hence `|K'|`) on a compact window near `0`.
  So the coefficient bound is an honest additional input at this level of generality. -/

/-- **The coefficient bound from a continuous kernel derivative on the window.**  Continuity of
`r ↦ deriv M.K r` on the compact window bounds `|M.coeffRHS|` there by
`β_c · sup |K'|`. -/
theorem exists_coeffRHS_bound_of_continuousOn_deriv {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn (fun r => deriv M.K r) (Set.Icc a b)) :
    ∃ C, 0 ≤ C ∧ ∀ r ∈ Set.Icc a b, |M.coeffRHS r| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := a) (b := b)).exists_bound_of_continuousOn hcont
  have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hC a (left_mem_Icc.mpr hab))
  refine ⟨(M.betaCrit : ℝ) * C, mul_nonneg M.betaCrit.coe_nonneg hCnn, fun r hr => ?_⟩
  rw [SourceModelData.coeffRHS, abs_mul, abs_neg, abs_of_nonneg M.betaCrit.coe_nonneg]
  refine mul_le_mul_of_nonneg_left ?_ M.betaCrit.coe_nonneg
  rw [← Real.norm_eq_abs]
  exact hC r hr

/-- **Continuity of the coefficient from continuity of the kernel derivative.**  On the interior
of a window, C¹-regularity of the radial kernel makes `M.coeffRHS` continuous, which is the
coefficient input of the landed off-sphere continuity theorems
(`SourceModelData.continuousAt_rhsScalarTwo_of_no_sphere`). -/
theorem continuousAt_coeffRHS_of_continuousOn_deriv {a b r : ℝ}
    (hcont : ContinuousOn (fun r => deriv M.K r) (Set.Icc a b)) (hr : r ∈ Set.Ioo a b) :
    ContinuousAt M.coeffRHS r := by
  have h : ContinuousAt (fun r => deriv M.K r) r :=
    hcont.continuousAt (Icc_mem_nhds hr.1 hr.2)
  exact continuousAt_const.mul h.neg

/-! ## 7. Fully assembled tail theorem: the uniform majorant is itself landed

`WindowMajorant.Main.windowFlux_le_windowMajorant_of_cutMoment_four_le` and
`WindowMajorant.Main.intervalIntegrable_windowMajorant` supply the two halves of
`hfluxMaj`/`hG` with `G = M.windowMajorant C b = 2 * (M.rhsScalarTwo · + 3 C (M.cutMoment 4 b).toReal)`.
Discharging them leaves only the fixed-radius convergence `hfluxConv`, the coefficient bound `hC`
and finiteness of the second cutoff moment at the right endpoint. -/

/-- **The `p = 2` radius picture on a positive off-corner tail, assembled.**

Inputs: an off-corner window `[a,b]` of the positive tail, a monotone edge-exhausting window family,
finiteness of the *second* cutoff moment at `b`, a bound on `|M.coeffRHS|` on the window, and
pointwise-in-radius convergence of the window fluxes to `M.rhsScalarTwo`.

Outputs: absolute continuity of `r ↦ (M.cutMoment 2 r).toReal` on `[a,b]`; the a.e. radius
derivative `M.rhsScalarTwo`; the a.e. equality `deriv = M.rhsScalarTwo`; the integrated identity on
the window; and interval integrability of `M.rhsScalarTwo`.

Compared to the landed pointwise interface `SourceModelData.hasDerivAt_cutMomentReal_two_of_majorant`
the hypotheses `hmeas`, `hmoment`, `hrhsCont` and `h4 : ∀ t ∈ Icc a b, cutMoment 4 t ≠ ⊤` are gone:
`hmeas` is produced as a `liminf` from `hfluxConv`, `hmoment` from the window-moment convergence
along the exhausting family, `h4` from `cutMoment_four_ne_top_of_two` at `b`, and `hrhsCont` is not
needed at all because the conclusion is a.e. in the radius. -/
theorem ac_and_ae_hasDerivAt_cutMomentReal_two_assembled {a b : ℝ}
    (hwin : M.IsOffCornerWindow a b) (S : ℕ → Finset (Sym2 M.V))
    (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ k, e ∈ S k)
    (h2b : M.cutMoment 2 b ≠ ⊤)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ r ∈ Set.Icc a b, |M.coeffRHS r| ≤ C)
    (hfluxConv : ∀ t, Tendsto (fun n => M.windowFlux (S n) t) atTop (𝓝 (M.rhsScalarTwo t))) :
    AbsolutelyContinuousOnInterval (fun r => M.cutMomentReal 2 r) a b ∧
      (∀ᵐ r ∂volume, r ∈ Set.Ioo a b →
        HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r) r) ∧
      (deriv (fun r => M.cutMomentReal 2 r) =ᵐ[volume.restrict (Set.Ioo a b)]
        fun t => M.rhsScalarTwo t) ∧
      (∀ x ∈ Set.Icc a b,
        ∫ t in a..x, M.rhsScalarTwo t = M.cutMomentReal 2 x - M.cutMomentReal 2 a) ∧
      IntervalIntegrable (fun t => M.rhsScalarTwo t) volume a b := by
  have ha : 0 < a := hwin.1
  have hab : a ≤ b := hwin.2.1
  have h4b : M.cutMoment 4 b ≠ ⊤ :=
    PercLib.CriticalLRP.CaseOne.cutMoment_four_ne_top_of_two M h2b
  have hmeas : Measurable fun t => M.rhsScalarTwo t := by
    have hlim : (fun t => M.rhsScalarTwo t)
        = fun t => liminf (fun n => M.windowFlux (S n) t) atTop := by
      funext t
      exact (hfluxConv t).liminf_eq.symm
    rw [hlim]
    exact Measurable.liminf fun n => M.measurable_windowFlux (S n)
  have hfluxMaj : ∀ n, ∀ t ∈ Set.Ioc a b,
      M.windowFlux (S n) t ≤ M.windowMajorant C b t :=
    M.windowFlux_le_windowMajorant_of_cutMoment_four_le ha hab h4b hC0 hC S
  have hG : IntegrableOn (M.windowMajorant C b) (Set.Ioc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp
      (M.intervalIntegrable_windowMajorant hab hmeas hC0 hC h4b)
  exact ac_and_ae_hasDerivAt_cutMomentReal_two_of_window_majorant M hwin S hSmono hS h2b hC0 hC
    hfluxMaj hG hfluxConv

/-- **The coefficient bound on a positive tail is *derivable* from the model's own sharpness
assumption.**  `M.exists_error` gives a log-error function `δ` with
`|deriv M.K r| = (1 + δ r) r^{-d-α-1}` for `r > 0` and `δ r → 0` as `r → ∞`.  Hence for every
radius beyond the point where `|δ| ≤ 1`, the derivative decays with the actual power law and

`|M.coeffRHS r| ≤ β_c · 2 · a^{-d-α-1}`  for every `r ∈ [a, b]`,  `0 < a`,  `a ≤ b`.

So the coefficient bound `hC` of §4/§7 is not an independent regularity hypothesis on a positive
tail: it is forced by the sharpness input that already defines the model.  What is genuinely extra
there is only `ContinuousAt M.coeffRHS r` at a single radius, which is what the landed off-corner
continuity theorem consumes; the a.e. conclusions of §4 need no continuity at all. -/
theorem exists_coeffRHS_bound_of_deriv_decay :
    ∃ R : ℝ, ∀ a b : ℝ, R ≤ a → 0 < a → a ≤ b →
      ∃ C, 0 ≤ C ∧ ∀ r ∈ Set.Icc a b, |M.coeffRHS r| ≤ C := by
  obtain ⟨δ, hδ, hlog⟩ := M.exists_error
  have hδtend : Tendsto δ atTop (𝓝 0) := hlog.2
  have hev : ∀ᶠ r in atTop, |δ r| < 1 := by
    have h := hδtend.eventually (Metric.ball_mem_nhds (0 : ℝ) one_pos)
    simpa [Real.dist_eq, abs_sub_comm] using h
  obtain ⟨R, hR⟩ := eventually_atTop.mp hev
  refine ⟨R, fun a b hRa ha0 hab => ⟨(M.betaCrit : ℝ) * (2 * a ^ (-(M.d : ℝ) - M.α - 1)),
    mul_nonneg M.betaCrit.coe_nonneg (by positivity), fun r hr => ?_⟩⟩
  have hr0 : 0 < r := lt_of_lt_of_le ha0 hr.1
  have he : -(M.d : ℝ) - M.α - 1 ≤ 0 := by
    have hd1 : (1 : ℝ) ≤ (M.d : ℝ) := by exact_mod_cast M.hd
    have := M.hα
    linarith
  have hδr : |δ r| ≤ 1 := le_of_lt (hR r (le_trans hRa hr.1))
  have hδub : δ r ≤ 1 := (abs_le.mp hδr).2
  have h1 : 1 + δ r ≤ 2 := by linarith
  have hKr : |deriv M.K r| = (1 + δ r) * r ^ (-(M.d : ℝ) - M.α - 1) := hδ r hr0
  have hpow : r ^ (-(M.d : ℝ) - M.α - 1) ≤ a ^ (-(M.d : ℝ) - M.α - 1) :=
    Real.rpow_le_rpow_of_nonpos ha0 hr.1 he
  have hpow0 : 0 ≤ r ^ (-(M.d : ℝ) - M.α - 1) :=
    le_of_lt (Real.rpow_pos_of_pos hr0 _)
  calc |M.coeffRHS r| = (M.betaCrit : ℝ) * |deriv M.K r| := by
        rw [SourceModelData.coeffRHS, abs_mul, abs_of_nonneg M.betaCrit.coe_nonneg, abs_neg]
    _ = (M.betaCrit : ℝ) * ((1 + δ r) * r ^ (-(M.d : ℝ) - M.α - 1)) := by rw [hKr]
    _ ≤ (M.betaCrit : ℝ) * (2 * a ^ (-(M.d : ℝ) - M.α - 1)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul h1 hpow hpow0 (by norm_num : (0 : ℝ) ≤ 2))
          M.betaCrit.coe_nonneg

/-- **The `p = 2` radius picture on the positive tail, with the coefficient bound discharged.**

There is a radius `R` such that for every off-corner window `[a,b]` of the positive tail beyond `R`
(`R ≤ a`, so `0 < a` and every radius of the window is off-corner), every monotone edge-exhausting
window family, and every radius with finite second cutoff moment at `b`, the fixed-radius
convergence of the window fluxes alone gives:

`r ↦ (M.cutMoment 2 r).toReal` is absolutely continuous on `[a,b]`; its radius derivative is
`M.rhsScalarTwo` almost everywhere on `(a,b)`; `deriv` agrees with `M.rhsScalarTwo` a.e.;
the integrated identity holds on the window; and `M.rhsScalarTwo` is interval integrable.

The coefficient bound is *not* a hypothesis here: it is derived from the model's sharpness field
`exists_error` by `exists_coeffRHS_bound_of_deriv_decay`. -/
theorem ac_and_ae_hasDerivAt_cutMomentReal_two_tail :
    ∃ R : ℝ, ∀ {a b : ℝ}, R ≤ a → M.IsOffCornerWindow a b →
      ∀ (S : ℕ → Finset (Sym2 M.V)), Monotone S → (∀ e : Sym2 M.V, ∃ k, e ∈ S k) →
      M.cutMoment 2 b ≠ ⊤ →
      (∀ t, Tendsto (fun n => M.windowFlux (S n) t) atTop (𝓝 (M.rhsScalarTwo t))) →
      AbsolutelyContinuousOnInterval (fun r => M.cutMomentReal 2 r) a b ∧
        (∀ᵐ r ∂volume, r ∈ Set.Ioo a b →
          HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r) r) ∧
        (deriv (fun r => M.cutMomentReal 2 r) =ᵐ[volume.restrict (Set.Ioo a b)]
          fun t => M.rhsScalarTwo t) ∧
        (∀ x ∈ Set.Icc a b,
          ∫ t in a..x, M.rhsScalarTwo t = M.cutMomentReal 2 x - M.cutMomentReal 2 a) ∧
        IntervalIntegrable (fun t => M.rhsScalarTwo t) volume a b := by
  obtain ⟨R, hR⟩ := exists_coeffRHS_bound_of_deriv_decay M
  refine ⟨R, fun {a b} hRa hwin S hSmono hS h2b hfluxConv => ?_⟩
  obtain ⟨C, hC0, hC⟩ := hR a b hRa hwin.1 hwin.2.1
  exact ac_and_ae_hasDerivAt_cutMomentReal_two_assembled M hwin S hSmono hS h2b hC0 hC hfluxConv

/-- **The radius picture from the integrated identity, packaged.**  A single interface for the
conclusions of §4: given interval integrability of `M.rhsScalarTwo` and the integrated identity on
`[a,b]`, all of absolute continuity, the a.e. radius derivative, the a.e. `deriv` equality and the
identity itself hold. -/
theorem ac_and_ae_hasDerivAt_cutMomentReal_two_of_identity {a b : ℝ} (hab : a ≤ b)
    (hint : IntervalIntegrable (fun t => M.rhsScalarTwo t) volume a b)
    (hid : ∀ x ∈ Set.Icc a b,
      ∫ t in a..x, M.rhsScalarTwo t = M.cutMomentReal 2 x - M.cutMomentReal 2 a) :
    AbsolutelyContinuousOnInterval (fun r => M.cutMomentReal 2 r) a b ∧
      (∀ᵐ r ∂volume, r ∈ Set.Ioo a b →
        HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r) r) ∧
      (deriv (fun r => M.cutMomentReal 2 r) =ᵐ[volume.restrict (Set.Ioo a b)]
        fun t => M.rhsScalarTwo t) ∧
      (∀ x ∈ Set.Icc a b,
        ∫ t in a..x, M.rhsScalarTwo t = M.cutMomentReal 2 x - M.cutMomentReal 2 a) ∧
      IntervalIntegrable (fun t => M.rhsScalarTwo t) volume a b :=
  ⟨absolutelyContinuousOnInterval_cutMomentReal_two M hab hint hid,
    ae_hasDerivAt_cutMomentReal_two M hab hint hid,
    deriv_ae_eq_rhsScalarTwo M hab hint hid, hid, hint⟩

/-- **The same radius picture along the monotone-window flux route.**  Here the integrated identity
is the landed `integral_rhsScalarTwo_eq_sub_of_window_noMomMono`, whose flux input is
window-index monotonicity `hfluxMono` rather than a uniform majorant.  Both routes therefore feed
the same `hac`/`hae` interface; whichever of the two flux inputs is closed first suffices. -/
theorem ac_and_ae_hasDerivAt_cutMomentReal_two_of_window_mono {a b : ℝ}
    (hwin : M.IsOffCornerWindow a b) (S : ℕ → Finset (Sym2 M.V))
    (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ k, e ∈ S k)
    (h2b : M.cutMoment 2 b ≠ ⊤)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ r ∈ Set.Icc a b, |M.coeffRHS r| ≤ C)
    (hfluxMono : ∀ n t, M.windowFlux (S n) t ≤ M.windowFlux (S (n + 1)) t)
    (hfluxConv : ∀ t, Tendsto (fun n => M.windowFlux (S n) t) atTop (𝓝 (M.rhsScalarTwo t))) :
    AbsolutelyContinuousOnInterval (fun r => M.cutMomentReal 2 r) a b ∧
      (∀ᵐ r ∂volume, r ∈ Set.Ioo a b →
        HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r) r) ∧
      (deriv (fun r => M.cutMomentReal 2 r) =ᵐ[volume.restrict (Set.Ioo a b)]
        fun t => M.rhsScalarTwo t) ∧
      (∀ x ∈ Set.Icc a b,
        ∫ t in a..x, M.rhsScalarTwo t = M.cutMomentReal 2 x - M.cutMomentReal 2 a) ∧
      IntervalIntegrable (fun t => M.rhsScalarTwo t) volume a b := by
  have hab : a ≤ b := hwin.2.1
  have hfin : ∀ x ∈ Set.Icc a b, M.cutMoment 2 x ≠ ⊤ :=
    fun x hx => M.cutMoment_ne_top_of_le hx.2 2 h2b
  have hmoment : ∀ x ∈ Set.Icc a b,
      Tendsto (fun n => M.windowMoment (S n) x - M.windowMoment (S n) a) atTop
        (𝓝 (M.cutMomentReal 2 x - M.cutMomentReal 2 a)) :=
    fun x hx => M.tendsto_windowMoment_sub S hSmono hS (hfin x hx)
      (hfin a ⟨le_refl a, hab⟩)
  have hmomnn : ∀ x ∈ Set.Icc a b, ∀ n,
      0 ≤ M.windowMoment (S n) x - M.windowMoment (S n) a :=
    fun x hx n => M.windowMoment_sub_nonneg (S n) hwin hx (hfin x hx)
  have hmeas : Measurable fun t => M.rhsScalarTwo t := by
    have hlim : (fun t => M.rhsScalarTwo t)
        = fun t => liminf (fun n => M.windowFlux (S n) t) atTop := by
      funext t
      exact (hfluxConv t).liminf_eq.symm
    rw [hlim]
    exact Measurable.liminf fun n => M.measurable_windowFlux (S n)
  have hrhsInt : IntervalIntegrable (fun t => M.rhsScalarTwo t) volume a b :=
    M.intervalIntegrable_rhsScalarTwo_of_coeffBound hab hmeas hC0 hC
      (PercLib.CriticalLRP.CaseOne.cutMoment_four_ne_top_of_two M h2b)
  refine ac_and_ae_hasDerivAt_cutMomentReal_two_of_identity M hab hrhsInt ?_
  exact M.integral_rhsScalarTwo_eq_sub_of_window_noMomMono hwin S
    (fun n => M.measurable_windowFlux (S n)) (fun n t => M.windowFlux_nonneg (S n) t)
    hfluxMono (fun n => M.intervalIntegrable_windowFlux (S n) hwin) hfluxConv hmomnn hmoment

/-! ## 8. Non-vacuity: positive off-corner windows exist in every positive radius interval

`M.IsOffCornerWindow a b` asks that *every* radius of `[a,b]` fail to be a `ρ`-distance of two
distinct vertices.  Since the corner set is locally finite (`finite_cornerRadii_inter_Ioo`) and
therefore has open dense complement, every nondegenerate positive radius interval contains a
nondegenerate off-corner subwindow.  So the tail hypothesis of §7 is satisfiable at arbitrarily
large radii, and no statement above is vacuous. -/

/-- **Every positive radius interval contains a nondegenerate off-corner window.** -/
theorem exists_offCornerWindow {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ a' b' : ℝ, a < a' ∧ a' < b' ∧ b' < b ∧ M.IsOffCornerWindow a' b' := by
  have hfin : (M.cornerRadii ∩ Set.Ioo a b).Finite := M.finite_cornerRadii_inter_Ioo a b
  have hne : ((Set.Ioo a b) \ (M.cornerRadii ∩ Set.Ioo a b)).Nonempty :=
    (Set.Ioo_infinite hab).sdiff hfin |>.nonempty
  obtain ⟨x, hxIoo, hxS⟩ := hne
  have hxmem : x ∈ (M.cornerRadii ∩ Set.Ioo a b)ᶜ ∩ Set.Ioo a b := ⟨hxS, hxIoo⟩
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.mp (hfin.isClosed.isOpen_compl.inter isOpen_Ioo) x hxmem
  have hlo : x - ε / 2 ∈ (M.cornerRadii ∩ Set.Ioo a b)ᶜ ∩ Set.Ioo a b := by
    refine hball (Metric.mem_ball.mpr ?_)
    rw [Real.dist_eq, show x - ε / 2 - x = -(ε / 2) by ring, abs_neg, abs_of_pos (by linarith)]
    linarith
  have hhi : x + ε / 2 ∈ (M.cornerRadii ∩ Set.Ioo a b)ᶜ ∩ Set.Ioo a b := by
    refine hball (Metric.mem_ball.mpr ?_)
    rw [Real.dist_eq, show x + ε / 2 - x = ε / 2 by ring, abs_of_pos (by linarith)]
    linarith
  refine ⟨x - ε / 2, x + ε / 2, hlo.2.1, by linarith, hhi.2.2, ?_⟩
  refine ⟨lt_trans ha hlo.2.1, by linarith, fun r hr => ?_⟩
  have hrball : dist r x < ε := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hr.1, hr.2]
  have hrmem : r ∈ (M.cornerRadii ∩ Set.Ioo a b)ᶜ ∩ Set.Ioo a b :=
    hball (Metric.mem_ball.mpr hrball)
  exact fun hrc => hrmem.1 ⟨hrc, hrmem.2⟩

/-- **The tail theorem stated for the actual second cutoff moment `(M.cutMoment 2 r).toReal`.**

`M.cutMomentReal 2` is an abbreviation for exactly this function, so this is the form in which
`hac` and `hae` of the `p = 2` radius picture are consumed downstream
(`SecondMomentError.Normalized`). -/
theorem ac_and_ae_hasDerivAt_cutMoment_toReal_two_tail :
    ∃ R : ℝ, ∀ {a b : ℝ}, R ≤ a → M.IsOffCornerWindow a b →
      ∀ (S : ℕ → Finset (Sym2 M.V)), Monotone S → (∀ e : Sym2 M.V, ∃ k, e ∈ S k) →
      M.cutMoment 2 b ≠ ⊤ →
      (∀ t, Tendsto (fun n => M.windowFlux (S n) t) atTop (𝓝 (M.rhsScalarTwo t))) →
      AbsolutelyContinuousOnInterval (fun r => (M.cutMoment 2 r).toReal) a b ∧
        (∀ᵐ r ∂volume, r ∈ Set.Ioo a b →
          HasDerivAt (fun r => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo r) r) := by
  obtain ⟨R, hR⟩ := ac_and_ae_hasDerivAt_cutMomentReal_two_tail M
  exact ⟨R, fun hRa hwin S hSmono hS h2b hfluxConv =>
    ⟨(hR hRa hwin S hSmono hS h2b hfluxConv).1,
      (hR hRa hwin S hSmono hS h2b hfluxConv).2.1⟩⟩

/-! ## 10. The exact consumer shape of `hac` and `hae`

`SourceModelData.regularlyVarying_two` (and its Case-1/Case-3 companions) consume

`hac : ∀ R, r₀ ≤ R → AbsolutelyContinuousOnInterval (fun r => (M.cutMoment 2 r).toReal) r₀ R`
`hae : ∀ᵐ t ∂(volume.restrict (Set.Ici r₀)), HasDerivAt (fun r => (M.cutMoment 2 r).toReal)
        (M.rhsScalarTwo t) t`.

Both are delivered below from the single remaining flux input: the integrated identity on every
radius window `[r₀, R]` (including windows that contain corner radii). -/

/-- **The consumer shape of `hac`.**  If the integrated identity with `M.rhsScalarTwo` holds on
every radius window `[r₀, R]`, then the actual second cutoff moment is absolutely continuous on
each of them. -/
theorem absolutelyContinuousOnInterval_toReal_two_of_forall_identity {r₀ : ℝ}
    (hint : ∀ R : ℝ, r₀ ≤ R → IntervalIntegrable (fun t => M.rhsScalarTwo t) volume r₀ R)
    (hid : ∀ R : ℝ, r₀ ≤ R → ∀ x ∈ Set.Icc r₀ R,
      ∫ t in r₀..x, M.rhsScalarTwo t = M.cutMomentReal 2 x - M.cutMomentReal 2 r₀) :
    ∀ R : ℝ, r₀ ≤ R →
      AbsolutelyContinuousOnInterval (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R :=
  fun R hR => absolutelyContinuousOnInterval_cutMomentReal_two M hR (hint R hR) (hid R hR)

/-- **The consumer shape of `hae`.**  From the same input, almost every radius of the whole tail
`[r₀, ∞)` is a differentiability point of the actual second cutoff moment, with derivative
`M.rhsScalarTwo`.  The passage from the per-window a.e. statements to the tail is a countable union
over the windows `[r₀, r₀ + n]` (the single radius `r₀` is null). -/
theorem ae_hasDerivAt_toReal_two_of_forall_identity {r₀ : ℝ}
    (hint : ∀ R : ℝ, r₀ ≤ R → IntervalIntegrable (fun t => M.rhsScalarTwo t) volume r₀ R)
    (hid : ∀ R : ℝ, r₀ ≤ R → ∀ x ∈ Set.Icc r₀ R,
      ∫ t in r₀..x, M.rhsScalarTwo t = M.cutMomentReal 2 x - M.cutMomentReal 2 r₀) :
    ∀ᵐ t ∂(volume.restrict (Set.Ici r₀)),
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t := by
  have hall : ∀ n : ℕ, ∀ᵐ t ∂volume,
      t ∈ Set.Ioo r₀ (r₀ + n) →
        HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t := by
    intro n
    have hn : r₀ ≤ r₀ + (n : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg n)
    exact ae_hasDerivAt_cutMomentReal_two M hn (hint _ hn) (hid _ hn)
  have hu : ∀ᵐ t ∂volume, ∀ n : ℕ, t ∈ Set.Ioo r₀ (r₀ + n) →
      HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t :=
    MeasureTheory.ae_all_iff.mpr hall
  rw [ae_restrict_iff' measurableSet_Ici]
  have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ r₀ := by
    rw [ae_iff]
    simp
  filter_upwards [hu, hne] with t ht htr hmem
  have hlt : r₀ < t := lt_of_le_of_ne hmem (Ne.symm htr)
  obtain ⟨n, hn⟩ := exists_nat_gt (t - r₀)
  exact ht n ⟨hlt, by linarith⟩

end PercLib.CriticalLRP.Orchestration.Smwyvlg99M1

/-! ## 9. The exact downstream shape and the corner-transfer interface

At the time this module was written two bridges were left for successor files; both are now
addressed by `SecondMomentAllWindowAe` and the `SecondMomentPrimitiveConsistency`/
`SecondMomentCornerIdentity` pair. The description below records that interface, not an assertion
that those later results remain missing.

The consumers in this repository (`SourceModelData.regularlyVarying_two`,
`SourceModelData.regularlyVarying_two_of_caseOne` in
`Analysis/SecondMomentError/Normalized.lean` and `Analysis/SecondMomentCase1.lean`) take

```
(hac : ∀ R : ℝ, r₀ ≤ R → AbsolutelyContinuousOnInterval (fun r : ℝ => (M.cutMoment 2 r).toReal) r₀ R)
(hmf : Measurable fun r : ℝ => (M.cutMoment 2 r).toReal)
(hmR : Measurable M.rhsScalarTwo)
(hae : ∀ᵐ t ∂(volume.restrict (Set.Ici r₀)),
        HasDerivAt (fun r : ℝ => (M.cutMoment 2 r).toReal) (M.rhsScalarTwo t) t)
```

What §7 delivers is the *per-window* form: for every off-corner window `[a,b]` (`0 < a`,
`a ≤ b`, no radius of `[a,b]` attained by the norm) with finite second moment at `b` and the
fixed-radius convergence, `AbsolutelyContinuousOnInterval` on `[a,b]` and the a.e. derivative on
`(a,b)`.  Hence `hac` in the consumer's form holds as soon as `M.IsOffCornerWindow r₀ R`.

For a window that *contains* corner radii, nothing is missing on the AC/differentiation side:
§10 delivers the consumer's `hac` and `hae` verbatim from the integrated identity on every window
`[r₀,R]`.  To *produce* that identity on windows containing corner radii from the corner-free ones,
two pure real-analysis routes suffice, with no probabilistic content:

1. **Gluing across finitely many corner radii.**  `M.cutMomentReal 2` is monotone
   (`SourceModelData.cutMoment_monotone`) and continuous
   (`SourceModelData.continuousOn_cutMomentReal`), and `M.cornerRadii ∩ [a,b]` is finite
   (`SourceModelData.finite_cornerRadii_inter_Ioo`).  The suggested analytic gluing lemma was:

   `f monotone on [a,b] → ContinuousOn f (Icc a b) → (∀ u v, a ≤ u → u < v → v ≤ b →
      (Icc u v ∩ C = ∅) → AbsolutelyContinuousOnInterval f u v) → (C.Finite) →
      AbsolutelyContinuousOnInterval f a b`.

   Proof shape: `absolutelyContinuousOnInterval_iff`, split each testing interval at the finitely
   many points of `C`, shrink by `η` into the corner-free gaps (where AC with constants `δ_gap` is
   available), take `δ = min_gap δ_gap`, and let `η → 0` using monotonicity and continuity.
2. **Countable transfer to `volume.restrict (Ici r₀)`.**  Almost every radius of `(r₀,∞)` is
   off-corner (`SourceModelData.ae_notMem_cornerRadii`), and each off-corner radius lies in an
   off-corner window (`exists_offCornerWindow`).  Covering `(r₀,∞) \ M.cornerRadii` by countably
   many off-corner windows with rational endpoints and taking a countable union of the a.e.
   statements gives the consumer's `hae`.

`SecondMomentAllWindowAe` proves the second bridge directly.  The
`SecondMomentPrimitiveConsistency`/`SecondMomentCornerIdentity` package takes a slightly stronger
but simpler route: it transfers the primitive identity itself across the finite corner set, using
continuity of the moment minus its interval primitive, and then derives AC from the identity.  This
avoids needing a separate AC-gluing lemma.  `OffCornerIdentity` supplies the corner-free inputs from
second-moment finiteness.  No derivative at attained radii is claimed by either route.
-/

/-! ## Axiom audit -/

namespace PercLib.CriticalLRP.Orchestration.Smwyvlg99M1

#print axioms absolutelyContinuousOnInterval_of_eq_add_integral
#print axioms ae_hasDerivAt_of_eq_add_integral
#print axioms deriv_ae_eq_of_ae_hasDerivAt
#print axioms integral_eq_sub_of_absolutelyContinuousOnInterval_of_ae_hasDerivAt
#print axioms absolutelyContinuousOnInterval_cutMomentReal_two
#print axioms ae_hasDerivAt_cutMomentReal_two
#print axioms deriv_ae_eq_rhsScalarTwo
#print axioms absolutelyContinuousOnInterval_cutMomentReal_two_of_window_majorant
#print axioms ae_hasDerivAt_cutMomentReal_two_of_window_majorant
#print axioms ac_and_ae_hasDerivAt_cutMomentReal_two_of_window_majorant
#print axioms continuousOn_cutMomentReal_two
#print axioms boundedVariationOn_cutMomentReal_two
#print axioms intervalIntegrable_deriv_cutMomentReal_two
#print axioms integral_rhsScalarTwo_eq_sub_of_absolutelyContinuousOnInterval
#print axioms exists_coeffRHS_bound_of_continuousOn_deriv
#print axioms continuousAt_coeffRHS_of_continuousOn_deriv
#print axioms ac_and_ae_hasDerivAt_cutMomentReal_two_assembled
#print axioms exists_coeffRHS_bound_of_deriv_decay
#print axioms exists_offCornerWindow
#print axioms ac_and_ae_hasDerivAt_cutMoment_toReal_two_tail
#print axioms absolutelyContinuousOnInterval_toReal_two_of_forall_identity
#print axioms ae_hasDerivAt_toReal_two_of_forall_identity
#print axioms ac_and_ae_hasDerivAt_cutMomentReal_two_tail
#print axioms ac_and_ae_hasDerivAt_cutMomentReal_two_of_identity
#print axioms ac_and_ae_hasDerivAt_cutMomentReal_two_of_window_mono

end PercLib.CriticalLRP.Orchestration.Smwyvlg99M1
