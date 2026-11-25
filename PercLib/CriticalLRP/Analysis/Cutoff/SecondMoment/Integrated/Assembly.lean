/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Swarm `smwveg8a1`, member `m1`, direction `d4`.

Integration donor: `.ultramath/smwveg8a1/m1`; independently checked at `6edf7ce1b15eba496fa5d59c040124a47dcf987e`.

# The integrated `p = 2` radius identity without moment monotonicity

The landed `SourceModelData.hasDerivAt_cutMomentReal_two` takes, among its ten inputs, three
statements about the window moments: `hmomMono` (the increments increase with the window),
`hmomNN` (they are nonnegative) and `hmomConv` (they converge to the increments of
`M.cutMomentReal 2`).

This file shows that **`hmomMono` is not needed**.  In the landed analytic core
`intervalIntegral_eq_of_monotone_window`, the monotone convergence is that of the *fluxes* in the
window index (`hmono : F n t ≤ F (n + 1) t`), which gives
`∫⁻ ofReal (F n) → ∫⁻ ofReal Flim` directly; the monotonicity `Monotone p` of the moment
increments bound to those integrals by `hstep` is never used.  The only place nonnegativity of
`p` enters is `0 ≤ L`, supplied by `hmomNN`.

Consequently:

* `intervalIntegral_eq_of_monotone_window'` — the analytic core with `hpmono` dropped;
* `integral_rhsScalarTwo_eq_sub_of_window_noMomMono` — the integrated identity with `hmommono` dropped;
* `hasDerivAt_cutMomentReal_two_noMomMono` — the pointwise derivative with `hmomMono` dropped;
* `hasDerivAt_cutMomentReal_two_of_finite` — the pointwise derivative with **all three** moment
  inputs discharged from the single genuine finite-window input
  `∀ x ∈ Icc a b, M.cutMoment 2 x ≠ ⊤` (finiteness of the second cutoff moment on the window).

The remaining hypotheses are exactly the flux inputs (`hfluxMeas`, `hfluxNN`, `hfluxMono`,
`hfluxInt`, `hfluxConv`, the subject of directions A--C), the off-sphere continuity `hrhsCont`
(landed, see `continuousAt_rhsScalarTwo_of_no_sphere`) and the interval integrability `hrhsInt`
of `M.rhsScalarTwo`.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Integrated.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Regularity.Left.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Integrated.Moment

/-!
# Removing the moment-monotonicity input
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

/-! ## 1. The analytic core, without monotonicity of the moment increments -/

/-- **Monotone convergence for interval integrals, without monotonicity of the integrals.**

Identical to the landed `intervalIntegral_eq_of_monotone_window`, but with the hypothesis
`Monotone p` removed.  The proof shows it is not used: the convergence
`∫⁻ ofReal (F n) → ∫⁻ ofReal Flim` is the monotone convergence of the nonnegative integrands in
the window index, and `p n` only records the value of the finite-window integral (`hstep`), so
`p n → L` identifies the limit without any monotonicity of `p`. -/
theorem intervalIntegral_eq_of_monotone_window' {F : ℕ → ℝ → ℝ} {Flim : ℝ → ℝ} {p : ℕ → ℝ}
    {L a b : ℝ} (hab : a ≤ b) (hmeas : ∀ n, Measurable (F n))
    (hnn : ∀ n t, 0 ≤ F n t) (hmono : ∀ n t, F n t ≤ F (n + 1) t)
    (hint : ∀ n, IntervalIntegrable (F n) volume a b)
    (hconv : ∀ t, Tendsto (fun n => F n t) atTop (𝓝 (Flim t)))
    (hstep : ∀ n, ∫ t in a..b, F n t = p n)
    (hpnn : ∀ n, 0 ≤ p n)
    (hL : Tendsto p atTop (𝓝 L)) :
    ∫ t in a..b, Flim t = L := by
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

namespace SourceModelData

variable (M : SourceModelData)

/-! ## 2. The integrated identity without moment monotonicity -/

/-- **The integrated `p = 2` radius identity on a window, from a fixed base point**, with the
moment monotonicity hypothesis `hmommono` of
`SourceModelData.integral_rhsScalarTwo_eq_sub_of_window` removed. -/
theorem integral_rhsScalarTwo_eq_sub_of_window_noMomMono {a b : ℝ} (hwin : M.IsOffCornerWindow a b)
    (S : ℕ → Finset (Sym2 M.V))
    (hmeas : ∀ n, Measurable (M.windowFlux (S n)))
    (hnn : ∀ n t, 0 ≤ M.windowFlux (S n) t)
    (hmono : ∀ n t, M.windowFlux (S n) t ≤ M.windowFlux (S (n + 1)) t)
    (hint : ∀ n, IntervalIntegrable (M.windowFlux (S n)) volume a b)
    (hconv : ∀ t, Tendsto (fun n => M.windowFlux (S n) t) atTop (𝓝 (M.rhsScalarTwo t)))
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
  refine intervalIntegral_eq_of_monotone_window' (F := fun n => M.windowFlux (S n))
    (Flim := fun t => M.rhsScalarTwo t)
    (p := fun n => M.windowMoment (S n) x - M.windowMoment (S n) a)
    (L := M.cutMomentReal 2 x - M.cutMomentReal 2 a) hx.1 hmeas hnn hmono
    hintx hconv ?_ (hmomnn x hx) (hmoment x hx)
  intro n
  exact M.integral_windowFlux_eq_sub (S n) hwin' (hintx n)

/-! ## 3. The pointwise derivative without moment monotonicity -/

/-- **The `p = 2` off-corner radius derivative**, with `hmomMono` removed from the hypotheses of
`SourceModelData.hasDerivAt_cutMomentReal_two`. -/
theorem hasDerivAt_cutMomentReal_two_noMomMono {a b r0 : ℝ} (hwin : M.IsOffCornerWindow a b)
    (S : ℕ → Finset (Sym2 M.V))
    (har : a < r0) (hrb : r0 < b)
    (hfluxMeas : ∀ n, Measurable (M.windowFlux (S n)))
    (hfluxNN : ∀ n t, 0 ≤ M.windowFlux (S n) t)
    (hfluxMono : ∀ n t, M.windowFlux (S n) t ≤ M.windowFlux (S (n + 1)) t)
    (hfluxInt : ∀ n, IntervalIntegrable (M.windowFlux (S n)) volume a b)
    (hfluxConv : ∀ t, Tendsto (fun n => M.windowFlux (S n) t) atTop (𝓝 (M.rhsScalarTwo t)))
    (hmomNN : ∀ x ∈ Set.Icc a b, ∀ n, 0 ≤ M.windowMoment (S n) x - M.windowMoment (S n) a)
    (hmomConv : ∀ x ∈ Set.Icc a b,
      Tendsto (fun n => M.windowMoment (S n) x - M.windowMoment (S n) a) atTop
        (𝓝 (M.cutMomentReal 2 x - M.cutMomentReal 2 a)))
    (hrhsCont : ContinuousAt (fun t => M.rhsScalarTwo t) r0)
    (hrhsInt : IntervalIntegrable (fun t => M.rhsScalarTwo t) volume a r0) :
    HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r0) r0 := by
  have hbase := M.integral_rhsScalarTwo_eq_sub_of_window_noMomMono hwin S hfluxMeas hfluxNN hfluxMono
    hfluxInt hfluxConv hmomNN hmomConv
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

/-! ## 4. All three moment inputs discharged -/

/-- **The `p = 2` off-corner radius derivative, with all three moment inputs discharged.**

`hmomMono` is not needed (Sections 1--3); `hmomNN` and `hmomConv` are supplied by
`windowMoment_sub_nonneg` and `tendsto_windowMoment_sub` from the single genuine finite-window
input of direction D, finiteness of the second cutoff moment on `[a, b]`.

The remaining hypotheses are exactly the flux inputs (`hfluxMeas`, `hfluxNN`, `hfluxMono`,
`hfluxInt`, `hfluxConv`), the off-sphere continuity `hrhsCont` and the interval integrability
`hrhsInt` of `M.rhsScalarTwo`. -/
theorem hasDerivAt_cutMomentReal_two_of_finite {a b r0 : ℝ} (hwin : M.IsOffCornerWindow a b)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 M.V, ∃ k, e ∈ S k)
    (har : a < r0) (hrb : r0 < b)
    (hfin : ∀ x ∈ Set.Icc a b, M.cutMoment 2 x ≠ ⊤)
    (hfluxMeas : ∀ n, Measurable (M.windowFlux (S n)))
    (hfluxNN : ∀ n t, 0 ≤ M.windowFlux (S n) t)
    (hfluxMono : ∀ n t, M.windowFlux (S n) t ≤ M.windowFlux (S (n + 1)) t)
    (hfluxInt : ∀ n, IntervalIntegrable (M.windowFlux (S n)) volume a b)
    (hfluxConv : ∀ t, Tendsto (fun n => M.windowFlux (S n) t) atTop (𝓝 (M.rhsScalarTwo t)))
    (hrhsCont : ContinuousAt (fun t => M.rhsScalarTwo t) r0)
    (hrhsInt : IntervalIntegrable (fun t => M.rhsScalarTwo t) volume a r0) :
    HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r0) r0 :=
  M.hasDerivAt_cutMomentReal_two_noMomMono hwin S har hrb hfluxMeas hfluxNN hfluxMono hfluxInt hfluxConv
    (fun x hx n => M.windowMoment_sub_nonneg (S n) hwin hx (hfin x hx))
    (fun x hx => M.tendsto_windowMoment_sub S hSmono hS (hfin x hx)
      (hfin a ⟨le_refl a, le_trans hx.1 hx.2⟩))
    hrhsCont hrhsInt

/-- **`hrhsCont` from the landed off-sphere fourth-moment theorem.**  The exact hypotheses the
landed continuity statement consumes: the radius is positive and off the sphere
(`∀ y, ρ y ≠ r0`), the fourth cutoff moment is finite at some strictly larger radius, and
`M.coeffRHS` is continuous at `r0`. -/
theorem continuousAt_rhsScalarTwo_of_no_sphere' {r0 r1 : ℝ} (hr0 : 0 < r0) (hr1 : r0 < r1)
    (h4 : M.cutMoment 4 r1 ≠ ⊤) (h : ∀ y : M.V, M.S.ρ (toVec y) ≠ r0)
    (hcoef : ContinuousAt M.coeffRHS r0) :
    ContinuousAt (fun t => M.rhsScalarTwo t) r0 :=
  M.continuousAt_rhsScalarTwo_of_no_sphere r0 hr0 hr1 h4 h hcoef

/-! ## 5. Interval integrability of `M.rhsScalarTwo` from a coefficient bound -/

/-- **`hrhsInt` from a bound on the scalar coefficient.**

`M.rhsScalarTwo r = M.coeffRHS r * (M.p2RHS r).toReal`.  On a compact radius window
`[a, r0]` the `p = 2` excluded mass obeys the landed bound
`M.p2RHS r ≤ 6 |B_r| M₄(r)` (`p2RhsMass_le_fourth`), and both factors are monotone in the
radius (`Set.ncard_mono` for the ball, `cutMoment_monotone` for the fourth moment), so
`M.p2RHS` is bounded on the window by the single value at `r0`, provided the fourth cutoff
moment there is finite.  Hence `M.rhsScalarTwo` is interval integrable as soon as
`M.coeffRHS` is bounded on the window.  Boundedness of `β_c (-K')` on a compact window is the
genuine remaining analytic input; it is not derivable from `K_eq_integral`, which bounds only
the *tail integral* of `|K'|`, not its pointwise values. -/
theorem intervalIntegrable_rhsScalarTwo_of_coeffBound {a r0 C : ℝ} (har : a ≤ r0)
    (hmeas : Measurable fun t => M.rhsScalarTwo t)
    (hC0 : 0 ≤ C) (hC : ∀ r ∈ Set.Icc a r0, |M.coeffRHS r| ≤ C)
    (h4 : M.cutMoment 4 r0 ≠ ⊤) :
    IntervalIntegrable (fun t => M.rhsScalarTwo t) volume a r0 := by
  set D : ℝ≥0∞ := 6 * ((M.ball r0).ncard : ℝ≥0∞) * M.cutMoment 4 r0 with hD
  have hDne : D ≠ ⊤ := by
    rw [hD]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) (by simp)) h4
  have hDreal : D.toReal = 6 * ((M.ball r0).ncard : ℝ) * (M.cutMoment 4 r0).toReal := by
    rw [hD, ENNReal.toReal_mul, ENNReal.toReal_mul]
    simp
  have hbound : ∀ r ∈ Set.Icc a r0, ‖M.rhsScalarTwo r‖ ≤ C * D.toReal := by
    intro r hr
    have hball : M.ball r ⊆ M.ball r0 := fun y hy => le_trans hy hr.2
    have hcard : ((M.ball r).ncard : ℝ≥0∞) ≤ ((M.ball r0).ncard : ℝ≥0∞) := by
      exact_mod_cast Set.ncard_le_ncard hball
        (PercLib.CriticalLRP.BallAverage.ball_finite M r0)
    have hmom : M.cutMoment 4 r ≤ M.cutMoment 4 r0 := M.cutMoment_monotone 4 hr.2
    have hp2 : M.p2RHS r ≤ D := by
      rw [hD]
      calc M.p2RHS r
          ≤ 6 * (((M.ball r).ncard : ℝ≥0∞) * M.cutMoment 4 r) :=
            M.p2RhsMass_le_fourth r
        _ ≤ 6 * (((M.ball r0).ncard : ℝ≥0∞) * M.cutMoment 4 r0) :=
            mul_le_mul_of_nonneg_left (mul_le_mul' hcard hmom)
              (by positivity : (0 : ℝ≥0∞) ≤ 6)
        _ = 6 * ((M.ball r0).ncard : ℝ≥0∞) * M.cutMoment 4 r0 :=
            (mul_assoc _ _ _).symm
    have hp2' : (M.p2RHS r).toReal ≤ D.toReal := ENNReal.toReal_mono hDne hp2
    have hp2'' : (M.p2RHS r).toReal
        ≤ 6 * ((M.ball r0).ncard : ℝ) * (M.cutMoment 4 r0).toReal := by
      rw [← hDreal]
      exact hp2'
    have hmul : |M.coeffRHS r| * (M.p2RHS r).toReal
        ≤ C * (6 * ((M.ball r0).ncard : ℝ) * (M.cutMoment 4 r0).toReal) :=
      mul_le_mul (hC r hr) hp2'' (by positivity) hC0
    calc ‖M.rhsScalarTwo r‖ = |M.coeffRHS r| * (M.p2RHS r).toReal := by
          rw [SourceModelData.rhsScalarTwo, Real.norm_eq_abs, abs_mul,
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ (M.p2RHS r).toReal)]
      _ ≤ C * (6 * ((M.ball r0).ncard : ℝ) * (M.cutMoment 4 r0).toReal) := hmul
      _ = C * D.toReal := by rw [hDreal]
  refine IntervalIntegrable.mono_fun' (f := fun t => M.rhsScalarTwo t)
    (g := fun _ : ℝ => C * D.toReal) (intervalIntegrable_const)
    hmeas.aestronglyMeasurable ?_
  refine (MeasureTheory.ae_restrict_mem measurableSet_uIoc).mono fun r hr => ?_
  rw [Set.uIoc_of_le har] at hr
  obtain ⟨hr1, hr2⟩ := hr
  exact hbound r ⟨le_of_lt hr1, hr2⟩

/-! ## 6. The final assembly -/

/-- **The `p = 2` off-corner radius derivative**, with all three moment inputs discharged and
`hrhsInt` derived from a bound on the scalar coefficient.  The hypotheses are exactly: the
off-corner window, an exhaustive monotone window family, the flux inputs, the off-sphere
continuity of `M.rhsScalarTwo`, finiteness of the second and fourth cutoff moments on the
window, and a bound on `β_c (-K')` on the window. -/
theorem hasDerivAt_cutMomentReal_two_of_finite_of_coeffBound {a b r0 : ℝ}
    (hwin : M.IsOffCornerWindow a b) (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 M.V, ∃ k, e ∈ S k)
    (har : a < r0) (hrb : r0 < b)
    (hfin : ∀ x ∈ Set.Icc a b, M.cutMoment 2 x ≠ ⊤)
    (h4 : M.cutMoment 4 r0 ≠ ⊤) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ r ∈ Set.Icc a r0, |M.coeffRHS r| ≤ C)
    (hfluxMeas : ∀ n, Measurable (M.windowFlux (S n)))
    (hfluxNN : ∀ n t, 0 ≤ M.windowFlux (S n) t)
    (hfluxMono : ∀ n t, M.windowFlux (S n) t ≤ M.windowFlux (S (n + 1)) t)
    (hfluxInt : ∀ n, IntervalIntegrable (M.windowFlux (S n)) volume a b)
    (hfluxConv : ∀ t, Tendsto (fun n => M.windowFlux (S n) t) atTop (𝓝 (M.rhsScalarTwo t)))
    (hrhsCont : ContinuousAt (fun t => M.rhsScalarTwo t) r0) :
    HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r0) r0 := by
  have hrhsMeas : Measurable fun t => M.rhsScalarTwo t := by
    have hlim : (fun t => M.rhsScalarTwo t)
        = fun t => liminf (fun n => M.windowFlux (S n) t) atTop := by
      funext t
      exact (hfluxConv t).liminf_eq.symm
    rw [hlim]
    exact Measurable.liminf hfluxMeas
  exact M.hasDerivAt_cutMomentReal_two_of_finite hwin S hSmono hS har hrb hfin hfluxMeas
    hfluxNN hfluxMono hfluxInt hfluxConv hrhsCont
    (M.intervalIntegrable_rhsScalarTwo_of_coeffBound har.le hrhsMeas hC0 hC h4)

/-- **Fully assembled form.**  The `p = 2` off-corner derivative with the remaining hypotheses
stated entirely in the vocabulary of the model: the off-corner window, an exhaustive monotone
window family, the flux inputs, finiteness of the second cutoff moment on the window and of the
fourth at some strictly larger radius, the off-sphere condition at `r0`, continuity of
`M.coeffRHS` at `r0`, and a bound on `M.coeffRHS` on the window. -/
theorem hasDerivAt_cutMomentReal_two_assembled {a b r0 r1 : ℝ}
    (hwin : M.IsOffCornerWindow a b) (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 M.V, ∃ k, e ∈ S k)
    (har : a < r0) (hrb : r0 < b)
    (hfin : ∀ x ∈ Set.Icc a b, M.cutMoment 2 x ≠ ⊤)
    (hr1 : r0 < r1) (h4 : M.cutMoment 4 r1 ≠ ⊤)
    (hsphere : ∀ y : M.V, M.S.ρ (toVec y) ≠ r0)
    (hcoefcont : ContinuousAt M.coeffRHS r0)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ r ∈ Set.Icc a r0, |M.coeffRHS r| ≤ C)
    (hfluxMeas : ∀ n, Measurable (M.windowFlux (S n)))
    (hfluxNN : ∀ n t, 0 ≤ M.windowFlux (S n) t)
    (hfluxMono : ∀ n t, M.windowFlux (S n) t ≤ M.windowFlux (S (n + 1)) t)
    (hfluxInt : ∀ n, IntervalIntegrable (M.windowFlux (S n)) volume a b)
    (hfluxConv : ∀ t, Tendsto (fun n => M.windowFlux (S n) t) atTop (𝓝 (M.rhsScalarTwo t))) :
    HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r0) r0 := by
  have hr0 : 0 < r0 := lt_trans hwin.1 har
  have h4r0 : M.cutMoment 4 r0 ≠ ⊤ :=
    ne_top_of_le_ne_top h4 (M.cutMoment_monotone 4 hr1.le)
  exact M.hasDerivAt_cutMomentReal_two_of_finite_of_coeffBound hwin S hSmono hS har hrb hfin
    h4r0 hC0 hC hfluxMeas hfluxNN hfluxMono hfluxInt hfluxConv
    (M.continuousAt_rhsScalarTwo_of_no_sphere' hr0 hr1 h4 hsphere hcoefcont)

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.Orchestration.intervalIntegral_eq_of_monotone_window'
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.integral_rhsScalarTwo_eq_sub_of_window_noMomMono
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.hasDerivAt_cutMomentReal_two_noMomMono
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.hasDerivAt_cutMomentReal_two_of_finite
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.continuousAt_rhsScalarTwo_of_no_sphere'
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.intervalIntegrable_rhsScalarTwo_of_coeffBound
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.hasDerivAt_cutMomentReal_two_of_finite_of_coeffBound
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.hasDerivAt_cutMomentReal_two_assembled
