/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Swarm `smwvdggcc`, member `m1`, direction `d3`.

Integration donor: `.ultramath/smwvdggcc/m1`; independently checked at `0b87f45527ec4090b7f9189ab48f7ade24cac41e`.

# The integrated `p = 2` radius identity

This file proves the *integrated* form of the `p = 2` off-corner derivative,

`∫ t in a..b, M.rhsScalarTwo t = M.cutMomentReal 2 b - M.cutMomentReal 2 a`,

for a closed radius window `[a, b]` on which no radius is attained (`IsOffCornerWindow`), and
deduces from it the pointwise derivative

`HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r0) r0`

at every off-sphere radius `r0`.  The method is an exchange of the radius integral with the
window limit, *not* a pointwise uniform exchange of the flux: every object that is passed to the
radius limit is nonnegative, so the limit is monotone convergence (`lintegral_iSup`) and no
dominated or summable majorant of the pivotal flux is needed.

## The three layers

1. `intervalIntegral_eq_of_monotone_window` (abstract, no model): monotone convergence of
   interval integrals.  If `F n` are nonnegative measurable functions with interval integrals
   `p n`, increasing to `Flim` pointwise, then `∫ t in a..b, Flim t = L` for `L = lim p n`.

2. `integral_windowFlux_eq_sub` (model, finite window): the finite-window identity
   `∫ t in a..b, windowFlux S t = windowMoment S b - windowMoment S a`.  It is the fundamental
   theorem of calculus applied to the *unconditional* finite Russo identity
   `hasDerivAt_integral_cutFun_cutLaw`; the only input beyond the model is interval
   integrability of the finite flux on the window.

3. `integral_rhsScalarTwo_eq_sub` and `hasDerivAt_cutMomentReal_two`: layers 1 and 2 combined
   with the monotone convergence of window moments to `M.cutMomentReal 2` and of window fluxes
   to `M.rhsScalarTwo` (`tsum_cutEdgeDeriv_mul_pivotalFlux_eq_rhsScalarTwo`).

Every hypothesis of layers 2 and 3 is a statement about a *finite* window or an explicitly named
monotonicity/convergence, and each is listed in the docstring of the theorem that consumes it.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Integrated.Defs
public import Mathlib

/-!
# The integrated `p = 2` radius identity
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

namespace PercLib.CriticalLRP.Orchestration

/-! ## 1. Monotone convergence of interval integrals -/

/-- **Monotone convergence for interval integrals.**  Let `F n` be nonnegative measurable real
functions on the window `[a, b]` with finite interval integrals `p n`, increasing pointwise to
`Flim`, and let `p n` increase to `L`.  Then the interval integral of `Flim` is `L`.

This is the analytic core of the integrated radius identity: it converts a pointwise-in-`r`
limit of finite-window fluxes into the integral of the limit, requiring nothing but
nonnegativity and *finite* window integrals.  No uniform bound in the window index and no
dominated convergence hypothesis appears. -/
theorem intervalIntegral_eq_of_monotone_window {F : ℕ → ℝ → ℝ} {Flim : ℝ → ℝ} {p : ℕ → ℝ}
    {L a b : ℝ} (hab : a ≤ b) (hmeas : ∀ n, Measurable (F n))
    (hnn : ∀ n t, 0 ≤ F n t) (hmono : ∀ n t, F n t ≤ F (n + 1) t)
    (hint : ∀ n, IntervalIntegrable (F n) volume a b)
    (hconv : ∀ t, Tendsto (fun n => F n t) atTop (𝓝 (Flim t)))
    (hstep : ∀ n, ∫ t in a..b, F n t = p n)
    (hpmono : Monotone p) (hpnn : ∀ n, 0 ≤ p n)
    (hL : Tendsto p atTop (𝓝 L)) :
    ∫ t in a..b, Flim t = L := by
  have hmono_t : ∀ t, Monotone fun n => F n t :=
    fun t => monotone_nat_of_le_succ fun n => hmono n t
  have hLnn : 0 ≤ L :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hL (Eventually.of_forall hpnn)
  have hFlim_meas : Measurable Flim := by
    have hlim : Flim = fun t => liminf (fun n => F n t) atTop := by
      funext t
      exact (hconv t).liminf_eq.symm
    rw [hlim]
    exact Measurable.liminf hmeas
  -- the `ℝ≥0∞` integral of each window flux
  have hln : ∀ n, ∫⁻ t in Ioc a b, ENNReal.ofReal (F n t) = ENNReal.ofReal (p n) := by
    intro n
    have hIntOn : IntegrableOn (F n) (Ioc a b) volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp (hint n)
    have h1 : ENNReal.ofReal (∫ t in Ioc a b, F n t)
        = ∫⁻ t in Ioc a b, ENNReal.ofReal (F n t) :=
      MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntOn (Eventually.of_forall (hnn n))
    rw [← h1, ← intervalIntegral.integral_of_le hab, hstep n]
  -- monotone convergence of those `ℝ≥0∞` integrals
  have hconv_ae : ∀ᵐ t ∂(volume.restrict (Ioc a b)),
      Tendsto (fun n => ENNReal.ofReal (F n t)) atTop (𝓝 (ENNReal.ofReal (Flim t))) :=
    Eventually.of_forall fun t =>
      (ENNReal.continuous_ofReal.tendsto (Flim t)).comp (hconv t)
  have hmeas' : ∀ n, AEMeasurable (fun t => ENNReal.ofReal (F n t))
      (volume.restrict (Ioc a b)) :=
    fun n => (ENNReal.measurable_ofReal.comp (hmeas n)).aemeasurable
  have hmono' : ∀ᵐ t ∂(volume.restrict (Ioc a b)),
      Monotone fun n => ENNReal.ofReal (F n t) :=
    Eventually.of_forall fun t =>
      monotone_nat_of_le_succ fun n => ENNReal.ofReal_le_ofReal (hmono n t)
  have hcm : Tendsto (fun n => ∫⁻ t in Ioc a b, ENNReal.ofReal (F n t)) atTop
      (𝓝 (∫⁻ t in Ioc a b, ENNReal.ofReal (Flim t))) :=
    lintegral_tendsto_of_tendsto_of_monotone hmeas' hmono' hconv_ae
  have hlim : Tendsto (fun n => ∫⁻ t in Ioc a b, ENNReal.ofReal (F n t)) atTop
      (𝓝 (ENNReal.ofReal L)) := by
    have hEq : (fun n => ∫⁻ t in Ioc a b, ENNReal.ofReal (F n t))
        = fun n => ENNReal.ofReal (p n) := funext hln
    rw [hEq]
    exact (ENNReal.continuous_ofReal.tendsto L).comp hL
  have hkey : ∫⁻ t in Ioc a b, ENNReal.ofReal (Flim t) = ENNReal.ofReal L :=
    tendsto_nhds_unique hcm hlim
  have hFlim_nn : ∀ᵐ t ∂(volume.restrict (Ioc a b)), 0 ≤ Flim t :=
    Eventually.of_forall fun t =>
      le_of_tendsto_of_tendsto tendsto_const_nhds (hconv t)
        (Eventually.of_forall fun n => hnn n t)
  rw [intervalIntegral.integral_of_le hab,
    integral_eq_lintegral_of_nonneg_ae hFlim_nn hFlim_meas.aestronglyMeasurable, hkey,
    ENNReal.toReal_ofReal hLnn]


/-! ## 2. The finite-window identity -/

namespace SourceModelData

variable (M : SourceModelData)

/-- **The finite-window radius derivative.**  At every off-corner radius the window moment is
differentiable in the radius with derivative the finite pivotal sum `windowFlux`.

This is the landed unconditional finite Russo identity `hasDerivAt_integral_cutFun_cutLaw` read
through the definitions `windowMoment`/`windowFlux`; nothing is exchanged and no moment
hypothesis enters. -/
theorem hasDerivAt_windowMoment (S : Finset (Sym2 M.V)) {r : ℝ}
    (hoff : r ∉ M.cornerRadii) (hr : 0 < r) :
    HasDerivAt (M.windowMoment S) (M.windowFlux S r) r := by
  change HasDerivAt (fun r' => ∫ ω, cutFun S M.clusterVolSqReal ω ∂(M.cutLaw r'))
    (∑ e ∈ S, M.cutEdgeDeriv r e * pivotalFlux (M.cutLaw r)
      (cutFun S M.clusterVolSqReal) e) r
  exact M.hasDerivAt_integral_cutFun_cutLaw S M.clusterVolSqReal hoff
    (M.K_diff.differentiableAt (isOpen_Ioi.mem_nhds hr))

/-- **The fundamental theorem of calculus for one finite window.**  On an off-corner window the
window moment is the primitive of the window flux.

The only input beyond the model data and the window predicate is interval integrability of the
finite window flux on the window; the derivative at every interior point is
`hasDerivAt_windowMoment`, which is unconditional. -/
theorem integral_windowFlux_eq_sub (S : Finset (Sym2 M.V)) {a b : ℝ}
    (hwin : M.IsOffCornerWindow a b)
    (hint : IntervalIntegrable (M.windowFlux S) volume a b) :
    ∫ t in a..b, M.windowFlux S t = M.windowMoment S b - M.windowMoment S a := by
  obtain ⟨ha, hab, hoff⟩ := hwin
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab ?_ ?_ hint
  · exact continuousOn_of_forall_continuousAt fun x hx =>
      (M.hasDerivAt_windowMoment S (hoff x hx) (lt_of_lt_of_le ha hx.1)).continuousAt
  · intro x hx
    exact M.hasDerivAt_windowMoment S (hoff x (Ioo_subset_Icc_self hx)) (lt_trans ha hx.1)

/-- **The integrated `p = 2` radius identity on a window, from a fixed base point.**

For a monotone family `S n` of edge windows, if

* the window fluxes are nonnegative and measurable in the radius and increase with `n`,
* each window flux is interval integrable on the window,
* the window fluxes converge pointwise in the radius to `M.rhsScalarTwo`,
* the window moments are monotone in `n`, their increments from `a` are nonnegative, and
  converge to the increments of `M.cutMomentReal 2`,

then for every `x` in the window the moment increment from `a` is the radius integral of
`M.rhsScalarTwo`.  This is monotone convergence of the finite-window identities of
`integral_windowFlux_eq_sub`; no majorant of the infinite pivotal flux is used. -/
theorem integral_rhsScalarTwo_eq_sub_of_window {a b : ℝ} (hwin : M.IsOffCornerWindow a b)
    (S : ℕ → Finset (Sym2 M.V))
    (hmeas : ∀ n, Measurable (M.windowFlux (S n)))
    (hnn : ∀ n t, 0 ≤ M.windowFlux (S n) t)
    (hmono : ∀ n t, M.windowFlux (S n) t ≤ M.windowFlux (S (n + 1)) t)
    (hint : ∀ n, IntervalIntegrable (M.windowFlux (S n)) volume a b)
    (hconv : ∀ t, Tendsto (fun n => M.windowFlux (S n) t) atTop (𝓝 (M.rhsScalarTwo t)))
    (hmommono : ∀ x ∈ Set.Icc a b,
      Monotone fun n => M.windowMoment (S n) x - M.windowMoment (S n) a)
    (hmomnn : ∀ x ∈ Set.Icc a b, ∀ n, 0 ≤ M.windowMoment (S n) x - M.windowMoment (S n) a)
    (hmoment : ∀ x ∈ Set.Icc a b,
      Tendsto (fun n => M.windowMoment (S n) x - M.windowMoment (S n) a) atTop
        (𝓝 (M.cutMomentReal 2 x - M.cutMomentReal 2 a))) :
    ∀ x ∈ Set.Icc a b,
      ∫ t in a..x, M.rhsScalarTwo t = M.cutMomentReal 2 x - M.cutMomentReal 2 a := by
  obtain ⟨ha, hab, hoff⟩ := hwin
  intro x hx
  have hwin' : M.IsOffCornerWindow a x :=
    ⟨ha, hx.1, fun r hr => hoff r (Set.Icc_subset_Icc_right hx.2 hr)⟩
  have hintx : ∀ n, IntervalIntegrable (M.windowFlux (S n)) volume a x := by
    intro n
    have hOn : IntegrableOn (M.windowFlux (S n)) (Set.Ioc a b) volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp (hint n)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hx.1).mpr
      (hOn.mono_set (Set.Ioc_subset_Ioc le_rfl hx.2))
  refine intervalIntegral_eq_of_monotone_window (F := fun n => M.windowFlux (S n))
    (Flim := fun t => M.rhsScalarTwo t)
    (p := fun n => M.windowMoment (S n) x - M.windowMoment (S n) a)
    (L := M.cutMomentReal 2 x - M.cutMomentReal 2 a) hx.1 hmeas hnn hmono
    hintx hconv ?_ (hmommono x hx) (hmomnn x hx) (hmoment x hx)
  intro n
  exact M.integral_windowFlux_eq_sub (S n) hwin' (hintx n)

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## 3. From the integrated identity to the pointwise derivative -/

namespace PercLib.CriticalLRP.Orchestration

/-- **The integrated identity from a fixed base point gives the derivative.**  If `f` is, near
`r0`, the primitive of `g` started at `a`, and `g` is continuous at `r0` and interval integrable
on `[a, r0]`, then `f` has derivative `g r0` at `r0`.

This is the form in which the integrated `p = 2` radius identity is consumed: the base point `a`
is the left end of the off-corner window, which is fixed, while the right end varies. -/
theorem hasDerivAt_of_integral_from_base {f g : ℝ → ℝ} {a r0 : ℝ}
    (hint : IntervalIntegrable g volume a r0) (hmeas : Measurable g) (hcont : ContinuousAt g r0)
    (hbase : ∀ᶠ x in 𝓝 r0, ∫ t in a..x, g t = f x - f a) :
    HasDerivAt f (g r0) r0 := by
  have hF : HasDerivAt (fun x => ∫ t in a..x, g t) (g r0) r0 :=
    intervalIntegral.integral_hasDerivAt_right hint hmeas.aestronglyMeasurable.stronglyMeasurableAtFilter hcont
  have hcongr : (fun x => f a + ∫ t in a..x, g t) =ᶠ[𝓝 r0] f := by
    filter_upwards [hbase] with x hx
    linarith
  exact (hF.const_add (f a)).congr_of_eventuallyEq hcongr.symm

/-! ## 4. The off-corner `p = 2` radius derivative -/

namespace SourceModelData

variable (M : SourceModelData)

/-- **The `p = 2` off-corner radius derivative, from the integrated identity.**

Fix an off-corner window `[a, b]` containing `r0` in its interior and a monotone family `S n` of
edge windows.  Suppose

* `hfluxMeas`, `hfluxNN`, `hfluxMono`, `hfluxConv` — the window fluxes are measurable in the
  radius, nonnegative, increase with the window, and converge pointwise in the radius to the
  accepted `p = 2` right-hand side `M.rhsScalarTwo`;
* `hfluxInt` — each window flux is interval integrable on `[a, b]`;
* `hmomMono`, `hmomNN`, `hmomConv` — the window moments are monotone in the window, increase in
  the radius, and converge to `M.cutMomentReal 2` together with their increments from `a`;
* `hrhsCont` — `M.rhsScalarTwo` is continuous at `r0` (landed off the sphere, see the audit);
  measurability of `M.rhsScalarTwo` is *not* assumed: it is derived from `hfluxMeas` and
  `hfluxConv` through `Measurable.liminf`;
* `hrhsInt` — `M.rhsScalarTwo` is interval integrable on `[a, r0]`.

Then `HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r0) r0`.

The proof is the integrated identity `integral_rhsScalarTwo_eq_sub_of_window` (monotone
convergence of the finite-window identities) followed by `hasDerivAt_of_integral_from_base`.
No pointwise uniform bound on the infinite pivotal flux is used at any stage: the flux enters
only through the pointwise-in-`r` convergence `hfluxConv` and the finite-window integrals
`hfluxInt`. -/
theorem hasDerivAt_cutMomentReal_two {a b r0 : ℝ} (hwin : M.IsOffCornerWindow a b)
    (S : ℕ → Finset (Sym2 M.V))
    (har : a < r0) (hrb : r0 < b)
    (hfluxMeas : ∀ n, Measurable (M.windowFlux (S n)))
    (hfluxNN : ∀ n t, 0 ≤ M.windowFlux (S n) t)
    (hfluxMono : ∀ n t, M.windowFlux (S n) t ≤ M.windowFlux (S (n + 1)) t)
    (hfluxInt : ∀ n, IntervalIntegrable (M.windowFlux (S n)) volume a b)
    (hfluxConv : ∀ t, Tendsto (fun n => M.windowFlux (S n) t) atTop (𝓝 (M.rhsScalarTwo t)))
    (hmomMono : ∀ x ∈ Set.Icc a b,
      Monotone fun n => M.windowMoment (S n) x - M.windowMoment (S n) a)
    (hmomNN : ∀ x ∈ Set.Icc a b, ∀ n, 0 ≤ M.windowMoment (S n) x - M.windowMoment (S n) a)
    (hmomConv : ∀ x ∈ Set.Icc a b,
      Tendsto (fun n => M.windowMoment (S n) x - M.windowMoment (S n) a) atTop
        (𝓝 (M.cutMomentReal 2 x - M.cutMomentReal 2 a)))
    (hrhsCont : ContinuousAt (fun t => M.rhsScalarTwo t) r0)
    (hrhsInt : IntervalIntegrable (fun t => M.rhsScalarTwo t) volume a r0) :
    HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r0) r0 := by
  have hbase := M.integral_rhsScalarTwo_eq_sub_of_window hwin S hfluxMeas hfluxNN hfluxMono
    hfluxInt hfluxConv hmomMono hmomNN hmomConv
  have hrhsMeas : Measurable fun t => M.rhsScalarTwo t := by
    have hlim : (fun t => M.rhsScalarTwo t)
        = fun t => liminf (fun n => M.windowFlux (S n) t) atTop := by
      funext t
      exact (hfluxConv t).liminf_eq.symm
    rw [hlim]
    exact Measurable.liminf hfluxMeas
  refine hasDerivAt_of_integral_from_base hrhsInt hrhsMeas hrhsCont ?_
  filter_upwards [isOpen_Ioo.mem_nhds (show r0 ∈ Set.Ioo a b from ⟨har, hrb⟩)] with x hx
  exact hbase x (Set.Ioo_subset_Icc_self hx)

end SourceModelData

end PercLib.CriticalLRP.Orchestration

end

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.Orchestration.intervalIntegral_eq_of_monotone_window
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.hasDerivAt_windowMoment
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.integral_windowFlux_eq_sub
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.integral_rhsScalarTwo_eq_sub_of_window
#print axioms PercLib.CriticalLRP.Orchestration.hasDerivAt_of_integral_from_base
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.hasDerivAt_cutMomentReal_two
