/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The `p = 2` off-corner derivative identity in *integrated* form

Swarm `smwv9oxuv`, member `m3`, direction `d3` (audit + reduction; no finite box, no flux API).

The swarm target is, at a non-corner radius `r`,

`HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r) r`   (`T`)

with `M.rhsScalarTwo r = M.coeffRHS r * (M.p2RHS r).toReal` the accepted `p = 2` right-hand side
of Hutchcroft, *Critical long-range percolation I*, Lemma I.4.1.  **Nothing here proves `(T)`, and
no right-hand-side identity alone can prove it**: `(T)` is a statement about the radius variable of
the infinite-volume cutoff law and needs an interchange.

What this file does is prove that `(T)` — hence the whole "differentiate under the infinite
vertex/edge sum" obligation — is *equivalent* to a statement of a different shape, and that the
two shapes are not interchangeable for free:

* `integral_rhsScalarTwo_eq_sub` (FTC, forward): if `(T)` holds at *every* interior point of a
  radius window `[a,b]`, the moment is continuous there and `rhsScalarTwo` is interval
  integrable, then the **integrated identity**
  `∫ t in a..b, rhsScalarTwo t = cutMomentReal 2 b - cutMomentReal 2 a`
  holds.  So the integrated identity is *no stronger* than the pointwise one.

* `hasDerivAt_of_eventually_eq_add_integral` (FTC, backward): conversely, the integrated identity
  in a neighbourhood of `r`, together with continuity of `rhsScalarTwo` at `r`, gives `(T)` at
  `r`.  Consequently `(T)` follows at *every* continuity point of the RHS from the integrated
  identity alone: the pointwise derivative is not an extra input once the RHS is continuous.

The reduction is the point of the file.  A pointwise interchange needs a *summable majorant of
the `p = 2` pivotal flux*, which is exactly what the landed `p = 1` chain spent its effort on
(`OffCorner/RadiusSummedFlux`, `OffCorner/EdgeMajorant`) and which the accepted `p = 2` packet
does **not** provide.  The integrated identity needs only `L¹`-shaped control on a bounded radius
window, which is what monotone convergence of finite windows *does* give (each finite-window
Russo derivative is unconditional, `Deriv.hasDerivAt_integral_cutFun_cutLaw`, and the windows are
increasing).  So the acquisition order is: integrated identity first, pointwise derivative after.

The two hypotheses that the integrated identity still needs are named, not assumed away:
continuity of `M.rhsScalarTwo` at the radius (so that `(T)` follows there) and interval
integrability of `M.rhsScalarTwo` on the window.  The quantitative statements below show what the
integrated identity is worth even without the continuity input: the moment is Lipschitz on any
window on which the RHS is bounded, with the explicit constant `sup rhsScalarTwo`.

No `sorry`, `admit`, `native_decide` or custom axiom.  Axiom audit at the end of the file.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Finiteness
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.RadiusMoments

/-!
# Fundamental-theorem-of-calculus reductions for the second cutoff moment

An integrated off-corner identity and local continuity give the pointwise derivative.
The separate consequences for moment increments and Lipschitz bounds are also included.
-/

set_option autoImplicit false
set_option linter.hashCommand false

/-!
# Integrated form of the `p = 2` off-corner radius derivative

Section 1: the two fundamental-theorem-of-calculus directions in abstract form.  Section 2: the
same at the source model and at the actual `p = 2` right-hand side `M.rhsScalarTwo`.  Section 3:
the quantitative consequences (Lipschitz bound and its integral form).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set

namespace PercLib.CriticalLRP.Orchestration

/-! ## 1. The two directions of the fundamental theorem of calculus -/

/-- **FTC, forward direction (abstract).**  A pointwise derivative identity at every interior
point of a window, together with continuity of the function on the window and interval
integrability of the derivative, gives the integrated identity.  This is the direction that
shows the integrated form is not a weakening of the pointwise form. -/
theorem integral_eq_sub_of_forall_hasDerivAt {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hderiv : ∀ u ∈ Set.Ioo a b, HasDerivAt f (g u) u)
    (hint : IntervalIntegrable g volume a b) :
    ∫ t in a..b, g t = f b - f a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont hderiv hint

/-- **FTC, backward direction (abstract).**  If `g` is continuous at `r` and `f` agrees near `r`
with `f r + ∫_r^x g`, then `f` has derivative `g r` at `r`.

This is the direction that matters for the swarm target: the *integrated* identity in a
neighbourhood of `r` — which is what a monotone-convergence interchange of finite windows
produces — already implies the pointwise derivative at every point where `g` is continuous.  No
pointwise majorant of the flux enters. -/
theorem hasDerivAt_of_eventually_eq_add_integral {f g : ℝ → ℝ} {r : ℝ}
    (hg : ContinuousAt g r) (hmeas : StronglyMeasurableAtFilter g (𝓝 r) volume)
    (h : f =ᶠ[𝓝 r] fun x => f r + ∫ t in r..x, g t) :
    HasDerivAt f (g r) r := by
  have hint : IntervalIntegrable g volume r r := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le le_rfl]
    exact MeasureTheory.IntegrableOn.of_measure_zero (by simp)
  have hprim : HasDerivAt (fun x => ∫ t in r..x, g t) (g r) r :=
    intervalIntegral.integral_hasDerivAt_right hint hmeas hg
  exact (hprim.const_add (f r)).congr_of_eventuallyEq h

/-- **FTC, backward direction, local-continuity form.**  Local continuity of `g` on an open set
supplies the strong-measurability input of the previous lemma, so the only hypothesis on `g` is
continuity on a neighbourhood of the radius. -/
theorem hasDerivAt_of_eventually_eq_add_integral_of_isOpen {f g : ℝ → ℝ} {r : ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hrU : r ∈ U) (hg : ContinuousOn g U)
    (h : f =ᶠ[𝓝 r] fun x => f r + ∫ t in r..x, g t) :
    HasDerivAt f (g r) r :=
  hasDerivAt_of_eventually_eq_add_integral (hg.continuousAt (hU.mem_nhds hrU))
    (hg.stronglyMeasurableAtFilter hU r hrU) h

/-! ## 2. The same at the source model and at the accepted `p = 2` right-hand side -/

namespace SourceModelData

variable (M : SourceModelData)

/-- **The `p = 2` off-corner derivative from the integrated identity.**  If the accepted `p = 2`
right-hand side `M.rhsScalarTwo` is continuous at the radius and the second cutoff moment is,
near that radius, the primitive of `M.rhsScalarTwo`, then the exact off-corner `p = 2` identity of
Lemma I.4.1 holds there, with the accepted RHS.

The hypotheses are exactly what an integrated (monotone-convergence, `L¹`) interchange produces;
they do not mention any pivotal flux, any finite box or any majorant of a flux. -/
theorem hasDerivAt_cutMomentReal_two_of_window_integral {r : ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hrU : r ∈ U)
    (hcont : ContinuousOn (fun t => M.rhsScalarTwo t) U)
    (hwin : (fun x => M.cutMomentReal 2 x) =ᶠ[𝓝 r]
      fun x => M.cutMomentReal 2 r + ∫ t in r..x, M.rhsScalarTwo t) :
    HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r) r :=
  hasDerivAt_of_eventually_eq_add_integral_of_isOpen hU hrU hcont hwin

/-- **The integrated `p = 2` identity on a window.**  If the off-corner `p = 2` identity holds at
every interior point of `[a,b]`, the second cutoff moment is continuous on `[a,b]` and the RHS is
interval integrable, then the moment difference is the integral of the accepted RHS.  Together
with `hasDerivAt_cutMomentReal_two_of_window_integral` this makes the pointwise and integrated
forms equivalent inputs for the target. -/
theorem integral_rhsScalarTwo_eq_sub {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn (fun r => M.cutMomentReal 2 r) (Set.Icc a b))
    (hderiv : ∀ u ∈ Set.Ioo a b,
      HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo u) u)
    (hint : IntervalIntegrable (fun t => M.rhsScalarTwo t) volume a b) :
    ∫ t in a..b, M.rhsScalarTwo t = M.cutMomentReal 2 b - M.cutMomentReal 2 a :=
  integral_eq_sub_of_forall_hasDerivAt hab hcont hderiv hint

/-! ## 3. Quantitative consequences of the integrated identity -/

/-- **Integral form of the Lipschitz bound.**  The integrated identity on a window bounds the
increment of the second cutoff moment by the `L¹` norm of the accepted `p = 2` right-hand side on
that window.  No derivative at any point of the window is used. -/
theorem abs_sub_le_integral_abs_rhsScalarTwo {a b : ℝ} (hab : a ≤ b)
    (hwin : ∀ x ∈ Set.Icc a b,
      M.cutMomentReal 2 x = M.cutMomentReal 2 a + ∫ t in a..x, M.rhsScalarTwo t) :
    |M.cutMomentReal 2 b - M.cutMomentReal 2 a| ≤ ∫ t in a..b, |M.rhsScalarTwo t| := by
  have hsub : M.cutMomentReal 2 b - M.cutMomentReal 2 a = ∫ t in a..b, M.rhsScalarTwo t := by
    rw [hwin b (right_mem_Icc.mpr hab), hwin a (left_mem_Icc.mpr hab),
      intervalIntegral.integral_same, add_zero]
    ring
  rw [hsub]
  exact intervalIntegral.abs_integral_le_integral_abs hab

/-- **Explicit-constant form.**  If additionally `0 ≤ rhsScalarTwo ≤ C` on the window, then the
second cutoff moment is `C`-Lipschitz there:

`|cutMomentReal 2 b - cutMomentReal 2 a| ≤ C * (b - a)`.

This is the quantitative payload of the integrated identity: an unconditional-in-`r` growth
bound for the `p = 2` cutoff moment on any radius window on which the accepted RHS is bounded,
obtained without differentiating the moment anywhere. -/
theorem abs_sub_le_mul_of_bound {a b C : ℝ} (hab : a ≤ b)
    (hwin : ∀ x ∈ Set.Icc a b,
      M.cutMomentReal 2 x = M.cutMomentReal 2 a + ∫ t in a..x, M.rhsScalarTwo t)
    (hint : IntervalIntegrable (fun t => M.rhsScalarTwo t) volume a b)
    (hnonneg : ∀ t ∈ Set.Icc a b, 0 ≤ M.rhsScalarTwo t)
    (hbound : ∀ t ∈ Set.Icc a b, M.rhsScalarTwo t ≤ C) :
    |M.cutMomentReal 2 b - M.cutMomentReal 2 a| ≤ C * (b - a) := by
  have hC0 : 0 ≤ C := le_trans (hnonneg a (left_mem_Icc.mpr hab)) (hbound a (left_mem_Icc.mpr hab))
  have hle : ∀ t ∈ Set.Icc a b, |M.rhsScalarTwo t| ≤ C := by
    intro t ht
    rw [abs_of_nonneg (hnonneg t ht)]
    exact hbound t ht
  calc |M.cutMomentReal 2 b - M.cutMomentReal 2 a|
      ≤ ∫ t in a..b, |M.rhsScalarTwo t| :=
        M.abs_sub_le_integral_abs_rhsScalarTwo hab hwin
    _ ≤ ∫ t in a..b, C :=
        intervalIntegral.integral_mono_on hab hint.abs intervalIntegrable_const hle
    _ = C * (b - a) := by
        rw [intervalIntegral.integral_const, smul_eq_mul, mul_comm]

end SourceModelData

end PercLib.CriticalLRP.Orchestration

end

#print axioms PercLib.CriticalLRP.Orchestration.hasDerivAt_of_eventually_eq_add_integral
#print axioms
  PercLib.CriticalLRP.Orchestration.hasDerivAt_of_eventually_eq_add_integral_of_isOpen
#print axioms PercLib.CriticalLRP.Orchestration.integral_eq_sub_of_forall_hasDerivAt
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.hasDerivAt_cutMomentReal_two_of_window_integral
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.integral_rhsScalarTwo_eq_sub
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.abs_sub_le_integral_abs_rhsScalarTwo
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.abs_sub_le_mul_of_bound
