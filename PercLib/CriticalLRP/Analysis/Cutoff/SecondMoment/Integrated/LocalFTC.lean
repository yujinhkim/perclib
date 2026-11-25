/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Swarm `smwvi25ua`, member `m2`, direction `d2` (the non-majorant half).

# The off-corner `p = 2` radius derivative from a positive-radius flux majorant

The landed chain
`hasDerivAt_cutMomentReal_two_of_finite` -> `hasDerivAt_cutMomentReal_two_integrated` ->
`hasDerivAt_cutMomentReal_two_sourceModelWitness_powerLaw` produces the off-corner radius
derivative

`HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r0) r0`

from the window-index monotonicity `hfluxMono` of the finite window fluxes plus a *globally*
phrased flux convergence `hfluxConv : ∀ t, Tendsto (fun n => M.windowFlux (S n) t) atTop
(𝓝 (M.rhsScalarTwo t))`.  This file removes both, and constructs no majorant: the majorant is an
explicit input, so that the two halves of the remaining gap (the pointwise flux bound and the
radius derivative) can be checked separately.

## What is proved here

* `aeStronglyMeasurable_rhsScalarTwo_restrict` — the accepted right-hand side is a.e. strongly
  measurable on any radius interval `(a, b]` with `a > 0`, as the `liminf` of the (measurable)
  window fluxes.  This is the *replacement for global measurability*: the landed
  `hasDerivAt_of_integral_from_base` wants `Measurable M.rhsScalarTwo` on the whole line, which
  was only ever obtained from a flux convergence at *all* radii, including nonpositive ones where
  the fixed-radius estimate carries no information;
* `intervalIntegrable_rhsScalarTwo_of_coeffBound_ae` — the landed
  `intervalIntegrable_rhsScalarTwo_of_coeffBound` with `Measurable` weakened to a.e. strong
  measurability on the interval actually integrated over; the analysis (the `p = 2` excluded mass
  bound `M.p2RHS r ≤ 6 |B_r| M₄(r)` and the monotonicity of the ball and of the fourth moment) is
  the landed one;
* `intervalIntegrable_candidateMajorant` — the *integrability* half of the candidate majorant
  `t ↦ 2 * (M.rhsScalarTwo t + 3 C (M.cutMoment 4 b)ᵗᵒᴿᵉᵃˡ)` of direction (A), from the coefficient
  bound alone, so that (A) is left with the pointwise inequality only;
* `hasDerivAt_of_integral_from_base_ae` — the fixed-base fundamental theorem of calculus with
  `Measurable g` replaced by a.e. strong measurability on one radius interval;
* `intervalIntegral_eq_of_majorant_window_pos`, `integral_rhsScalarTwo_eq_sub_of_window_majorant_pos`,
  `hasDerivAt_cutMomentReal_two_of_window_majorant_pos` — the monotone-free exchange and the radius
  derivative of `RadiusFTC.lean`, with the flux convergence required **only on the radius window
  `(a, b]`** that is actually integrated over;
* `hasDerivAt_cutMomentReal_two_of_local_majorant` — the generic assembly: *every* input is
  radius-local (finiteness of the fourth cutoff moment only at the right endpoint `b`, the
  coefficient bound on `[a, b]`, and the flux convergence on `(a, b]`);
* `hasDerivAt_cutMomentReal_two_of_cutMoment_four_majorant` — the same with the flux convergence
  *derived*, from a fourth cutoff moment finite on the window's radius interval `(a, b]` only
  (`tendsto_windowFlux_of_cutMoment_four`
  at each radius), so the statement is fully radius-local;
* `hasDerivAt_cutMomentReal_two_of_isWindowMajorant` — the same in the vocabulary of the landed
  `IsWindowMajorantOn`, i.e. the exact shape of a compiled majorant statement;
* `hasDerivAt_cutMomentReal_two_of_sSup_majorant` — the same with the *canonical* majorant
  `t ↦ ⨆ n, ‖M.windowFlux (S n) t‖`: no envelope has to be chosen, only its interval integrability
  and the pointwise boundedness of the family in the window index;
* `hasDerivAt_cutMomentReal_two_of_global_cutMoment_four_majorant` — its corollary from the source's
  global `∀ t > 0, M.cutMoment 4 t ≠ ⊤`;
* the witness versions in the paper's own scale, where the coefficient bound is the explicit power
  law `powLawCoeffBound β_c d α a` and the derivative is
  `powLawCoeff β_c d α r0 * (M.p2RHS r0).toReal`;
* `hasDerivAt_cutMomentReal_two_sourceModelWitness_box_majorant` — the fully instantiated version on
  the canonical box windows `boxEdges d n` and the off-corner window `[1/2, 1]`, where the
  off-sphere condition is discharged by `sourceModelWitness_sphere_ne`;
* `hasDerivAt_cutMomentReal_two_sourceModelWitness_box_noMoments_majorant` and
  `hasDerivAt_cutMomentReal_two_sourceModelWitness_box_sSup_majorant` — the same with **no moment
  hypothesis at all**: below radius `2` every cutoff moment of the witness is `1`
  (`cutMoment_sourceModelWitness_eq_one`);
* §7: `exists_nat_eq_norm_toVec`, `cornerRadii_sourceModelWitness_eq_even` — the `ρ`-lengths of the
  witness are **twice a natural number** (the norm of the witness is the sup norm, so it is integral
  on integral vectors).  Consequently `isOffCornerWindow_sourceModelWitness_of_no_even` and
  `sourceModelWitness_sphere_ne_of_no_even` discharge the off-corner and off-sphere conditions at
  *every* radius avoiding `2ℕ`, not only below `2`; and
  `hasDerivAt_cutMomentReal_two_sourceModelWitness_three_and_seven` is the derivative at the
  concrete nondegenerate off-sphere radius `r0 = 37/10` on the off-corner window `[7/2, 39/10]`
  (above the radius where the witness cut kernel vanishes).

The box instances on `[1/2, 1]` land in the *degenerate* region `r < 2`, where the cut kernel of the
witness vanishes identically: `M.cutLaw r` is the point mass at the empty configuration, the origin
is isolated, `M.cutMoment p r = 1` and `M.p2RHS r = 0`, so the derivative value asserted there is
`0` and the statement is a consistency check rather than new mathematics.  The substantive content
of this file is in the arbitrary-window statements, which do reach nondegenerate radii (their
`h4`-input is a genuine hypothesis about the fourth moment above radius `2`).

## What is not proved here

The uniform-in-window bound `hfluxMaj` and the interval integrability of its majorant are inputs
of every statement below: no majorant is constructed.  Consequently nothing here is a radius
derivative at an arbitrary radius without that input.  In particular, the statements below are
**not** unconditional off-corner derivatives; the remaining hypothesis is stated exactly, and in
the local forms it is the only hypothesis not confined to the radius window itself.

`hfluxMono` (window-index monotonicity of the finite window fluxes) appears nowhere: the exchange is
dominated convergence in the window index, driven by `hfluxMaj`.  No finite box replaces the model,
no two-sided claim is made at an attained radius, and no moment is converted from `⊤`.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Integrated.Assembly
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Integrated.RadiusFTC
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.FluxConv.Envelope.Summable
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.SourceWitness.Main

/-!
# The off-corner radius derivative with a positive-radius flux majorant as input
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

namespace SourceModelData

variable (M : SourceModelData)

/-! ## 1. A.e. strong measurability on a positive radius interval -/

/-- **`M.rhsScalarTwo` is a.e. strongly measurable on `(a, b]` for `0 < a`.**

On the radius window `(a, b]` the window fluxes converge to `M.rhsScalarTwo`, so there it is the
`liminf` of the measurable window fluxes.  This is the restricted form of
`measurable_rhsScalarTwo_of_tendsto_windowFlux`, and it is what the fixed-base FTC actually needs.

The caveat is real: the landed route obtains *global* measurability by taking the `liminf` at every
radius, which requires the fixed-radius flux convergence at nonpositive radii as well.  Nothing is
known there, and the statements of this file never ask for it: `hfluxConv` ranges over `(a, b]`
only. -/
theorem aeStronglyMeasurable_rhsScalarTwo_restrict {a b : ℝ}
    (S : ℕ → Finset (Sym2 M.V))
    (hfluxConv : ∀ t ∈ Set.Ioc a b,
      Tendsto (fun n => M.windowFlux (S n) t) atTop (𝓝 (M.rhsScalarTwo t))) :
    AEStronglyMeasurable (fun t => M.rhsScalarTwo t) (volume.restrict (Set.Ioc a b)) := by
  have hlim : (fun t => M.rhsScalarTwo t) =ᵐ[volume.restrict (Set.Ioc a b)]
      fun t => liminf (fun n => M.windowFlux (S n) t) atTop := by
    refine (ae_restrict_mem measurableSet_Ioc).mono fun t ht => ?_
    exact (hfluxConv t ht).liminf_eq.symm
  exact (Measurable.aestronglyMeasurable
    (Measurable.liminf fun n => M.measurable_windowFlux (S n))).congr hlim.symm

/-! ## 2. Interval integrability from the coefficient bound, with restricted measurability -/

/-- **`hrhsInt` from a bound on the scalar coefficient, with a.e. measurability on the interval.**

This is `intervalIntegrable_rhsScalarTwo_of_coeffBound` with the input `Measurable fun t =>
M.rhsScalarTwo t` on the whole line weakened to a.e. strong measurability on `(a, r0]`, which is
all that `IntervalIntegrable.mono_fun'` consumes.  The estimate is unchanged: on the compact window
`M.p2RHS r ≤ 6 |B_{r0}| M₄(r0)` by `p2RhsMass_le_fourth`, monotonicity of the ball and of the
fourth moment at finite `M₄(r0)`, so `M.rhsScalarTwo = β_c(-K') · (p2RHS)ᵗᵒᴿᵉᵃˡ` is dominated by
the constant `C · 6 |B_{r0}| M₄(r0)ᵗᵒᴿᵉᵃˡ`.

`hC` is a pointwise bound on the *coefficient* only; it is not derivable from `K_eq_integral`,
which controls the tail integral of `|K'|` and not its pointwise values. -/
theorem intervalIntegrable_rhsScalarTwo_of_coeffBound_ae {a r0 C : ℝ} (har : a ≤ r0)
    (hmeas : AEStronglyMeasurable (fun t => M.rhsScalarTwo t)
      (volume.restrict (Set.uIoc a r0)))
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
    (g := fun _ : ℝ => C * D.toReal) (intervalIntegrable_const) hmeas ?_
  refine (MeasureTheory.ae_restrict_mem measurableSet_uIoc).mono fun r hr => ?_
  rw [Set.uIoc_of_le har] at hr
  obtain ⟨hr1, hr2⟩ := hr
  exact hbound r ⟨le_of_lt hr1, hr2⟩

/-- **Interval integrability of the natural candidate majorant.**

Direction (A) of the swarm proposes the radius majorant
`G t = 2 * (M.rhsScalarTwo t + 3 * C * (M.cutMoment 4 b).toReal)` for the finite window fluxes on
`(a, b]`, with `C` a pointwise bound on `|M.coeffRHS|`.  Both terms of `G` are interval integrable
as soon as `C` bounds the coefficient and the fourth moment at `b` is finite: the constant term is
`intervalIntegrable_const`, and the `M.rhsScalarTwo` term is
`intervalIntegrable_rhsScalarTwo_of_coeffBound_ae` above.

So the *interval integrability* half of (A)'s target is discharged here; what remains of (A) is
purely the pointwise inequality `M.windowFlux (S n) t ≤ G t`, which is not a statement about
integrability and is not touched in this file. -/
theorem intervalIntegrable_candidateMajorant {a b C : ℝ} (hab : a ≤ b)
    (hmeas : AEStronglyMeasurable (fun t => M.rhsScalarTwo t)
      (volume.restrict (Set.uIoc a b)))
    (hC0 : 0 ≤ C) (hC : ∀ r ∈ Set.Icc a b, |M.coeffRHS r| ≤ C)
    (h4 : M.cutMoment 4 b ≠ ⊤) :
    IntervalIntegrable (fun t => 2 * (M.rhsScalarTwo t + 3 * C * (M.cutMoment 4 b).toReal))
      volume a b := by
  have h : IntervalIntegrable (fun t => M.rhsScalarTwo t) volume a b :=
    M.intervalIntegrable_rhsScalarTwo_of_coeffBound_ae hab hmeas hC0 hC h4
  have hconst : IntervalIntegrable (fun _ : ℝ => 3 * C * (M.cutMoment 4 b).toReal)
      volume a b := intervalIntegrable_const
  exact (h.add hconst).const_mul 2

/-! ## 3. The fixed-base FTC with restricted measurability -/

/-- **The fundamental theorem of calculus from a fixed base, with a.e. measurability.**

`hasDerivAt_of_integral_from_base` asks for `Measurable g` on the whole line.  Only a radius
interval around the differentiation point is ever used: `∫ t in a..x, g t` for `x` near `r0`, and
`r0 ∈ (a, b)` makes `(a, b]` a neighbourhood of `r0`.  A.e. strong measurability on `(a, b]`
therefore suffices for the `StronglyMeasurableAtFilter g (𝓝 r0)` input of the interval FTC. -/
theorem hasDerivAt_of_integral_from_base_ae {f g : ℝ → ℝ} {a b r0 : ℝ}
    (har : a < r0) (hrb : r0 < b)
    (hint : IntervalIntegrable g volume a r0)
    (hAE : AEStronglyMeasurable g (volume.restrict (Set.Ioc a b)))
    (hcont : ContinuousAt g r0)
    (hbase : ∀ᶠ x in 𝓝 r0, ∫ t in a..x, g t = f x - f a) :
    HasDerivAt f (g r0) r0 := by
  have hmem : Set.Ioc a b ∈ 𝓝 r0 :=
    mem_of_superset (isOpen_Ioo.mem_nhds (show r0 ∈ Set.Ioo a b from ⟨har, hrb⟩))
      Set.Ioo_subset_Ioc_self
  have hF : HasDerivAt (fun x => ∫ t in a..x, g t) (g r0) r0 :=
    intervalIntegral.integral_hasDerivAt_right hint ⟨Set.Ioc a b, hmem, hAE⟩ hcont
  have hcongr : (fun x => f a + ∫ t in a..x, g t) =ᶠ[𝓝 r0] f := by
    filter_upwards [hbase] with x hx
    linarith
  exact (hF.const_add (f a)).congr_of_eventuallyEq hcongr.symm

/-! ## 4. The monotone-free exchange at positive radii only -/

/-- **Dominated convergence for interval integrals, with convergence only on the window.**

`intervalIntegral_eq_of_majorant_window` of `Exchange.lean` asks for `∀ t, Tendsto (fun n => F n t)
atTop (𝓝 (Flim t))`.  The dominated-convergence exchange only evaluates the convergence on `uIoc a b`,
so a convergence hypothesis on `(a, b]` alone suffices.  Everything else is unchanged: one-sided
majorant, no window-index monotonicity, no monotone convergence. -/
theorem intervalIntegral_eq_of_majorant_window_pos {F : ℕ → ℝ → ℝ} {Flim : ℝ → ℝ}
    {p : ℕ → ℝ} {G : ℝ → ℝ} {L a b : ℝ} (hab : a ≤ b)
    (hnn : ∀ n t, 0 ≤ F n t)
    (hmeas : ∀ n, AEStronglyMeasurable (F n) (volume.restrict (Set.uIoc a b)))
    (hmaj : IsWindowMajorantOn F G (Set.Ioc a b))
    (hG : IntervalIntegrable G volume a b)
    (hconv : ∀ t ∈ Set.Ioc a b, Tendsto (fun n => F n t) atTop (𝓝 (Flim t)))
    (hstep : ∀ n, ∫ t in a..b, F n t = p n)
    (hL : Tendsto p atTop (𝓝 L)) :
    ∫ t in a..b, Flim t = L := by
  refine intervalIntegral_eq_of_dominated_window hmeas ?_ hG ?_ hstep hL
  · intro n
    refine Eventually.of_forall fun t ht => ?_
    rw [Set.uIoc_of_le hab] at ht
    exact hmaj.norm_le hnn ht
  · refine Eventually.of_forall fun t ht => ?_
    rw [Set.uIoc_of_le hab] at ht
    exact hconv t ht

/-- **The integrated `p = 2` radius identity from a window-local majorant.**  The counterpart of
`integral_rhsScalarTwo_eq_sub_of_window_majorant` with the flux convergence required only at
positive radii. -/
theorem integral_rhsScalarTwo_eq_sub_of_window_majorant_pos {a b : ℝ}
    (hwin : M.IsOffCornerWindow a b) (S : ℕ → Finset (Sym2 M.V))
    {G : ℝ → ℝ} (hfluxMaj : ∀ n, ∀ t ∈ Set.Ioc a b, M.windowFlux (S n) t ≤ G t)
    (hG : IntegrableOn G (Set.Ioc a b) volume)
    (hfluxConv : ∀ t ∈ Set.Ioc a b,
      Tendsto (fun n => M.windowFlux (S n) t) atTop (𝓝 (M.rhsScalarTwo t)))
    (hmoment : ∀ x ∈ Set.Icc a b,
      Tendsto (fun n => M.windowMoment (S n) x - M.windowMoment (S n) a) atTop
        (𝓝 (M.cutMomentReal 2 x - M.cutMomentReal 2 a))) :
    ∀ x ∈ Set.Icc a b,
      ∫ t in a..x, M.rhsScalarTwo t = M.cutMomentReal 2 x - M.cutMomentReal 2 a := by
  obtain ⟨ha, hab, hoff⟩ := hwin
  intro x hx
  have hwin' : M.IsOffCornerWindow a x :=
    ⟨ha, hx.1, fun r hr => hoff r (Set.Icc_subset_Icc_right hx.2 hr)⟩
  have hGx : IntervalIntegrable G volume a x :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hx.1).mpr
      (hG.mono_set (Set.Ioc_subset_Ioc le_rfl hx.2))
  refine intervalIntegral_eq_of_majorant_window_pos (F := fun n => M.windowFlux (S n))
    (Flim := fun t => M.rhsScalarTwo t)
    (p := fun n => M.windowMoment (S n) x - M.windowMoment (S n) a)
    (G := G) (L := M.cutMomentReal 2 x - M.cutMomentReal 2 a) hx.1
    (fun n t => M.windowFlux_nonneg (S n) t)
    (fun n => (M.measurable_windowFlux (S n)).aestronglyMeasurable) ?_ hGx
    (fun t ht => hfluxConv t (Set.Ioc_subset_Ioc le_rfl hx.2 ht))
    (fun n => M.integral_windowFlux_eq_sub (S n) hwin'
      (M.intervalIntegrable_windowFlux (S n) hwin')) (hmoment x hx)
  intro n t ht
  exact hfluxMaj n t (Set.Ioc_subset_Ioc le_rfl hx.2 ht)

/-- **The off-corner radius derivative from a uniform-in-window majorant, with a window-local
flux convergence.**  The counterpart of `hasDerivAt_cutMomentReal_two_of_window_majorant` with the
flux convergence required only on `(a, b]` and the measurability of `M.rhsScalarTwo` obtained on the
window rather than globally. -/
theorem hasDerivAt_cutMomentReal_two_of_window_majorant_pos {a b r0 : ℝ}
    (hwin : M.IsOffCornerWindow a b) (S : ℕ → Finset (Sym2 M.V))
    (har : a < r0) (hrb : r0 < b)
    {G : ℝ → ℝ} (hfluxMaj : ∀ n, ∀ t ∈ Set.Ioc a b, M.windowFlux (S n) t ≤ G t)
    (hG : IntervalIntegrable G volume a b)
    (hfluxConv : ∀ t ∈ Set.Ioc a b,
      Tendsto (fun n => M.windowFlux (S n) t) atTop (𝓝 (M.rhsScalarTwo t)))
    (hmoment : ∀ x ∈ Set.Icc a b,
      Tendsto (fun n => M.windowMoment (S n) x - M.windowMoment (S n) a) atTop
        (𝓝 (M.cutMomentReal 2 x - M.cutMomentReal 2 a)))
    (hrhsCont : ContinuousAt (fun t => M.rhsScalarTwo t) r0)
    (hrhsInt : IntervalIntegrable (fun t => M.rhsScalarTwo t) volume a b) :
    HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r0) r0 := by
  have ha : 0 < a := hwin.1
  have hab : a ≤ b := hwin.2.1
  have hOn : IntegrableOn (fun t => M.rhsScalarTwo t) (Set.Ioc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hrhsInt
  have hGon : IntegrableOn G (Set.Ioc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hG
  have hbase := M.integral_rhsScalarTwo_eq_sub_of_window_majorant_pos hwin S hfluxMaj hGon
    hfluxConv hmoment
  have hAE : AEStronglyMeasurable (fun t => M.rhsScalarTwo t)
      (volume.restrict (Set.Ioc a b)) :=
    M.aeStronglyMeasurable_rhsScalarTwo_restrict S hfluxConv
  have hint : IntervalIntegrable (fun t => M.rhsScalarTwo t) volume a r0 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (le_of_lt har)).mpr
      (hOn.mono_set (Set.Ioc_subset_Ioc le_rfl (le_of_lt hrb)))
  refine hasDerivAt_of_integral_from_base_ae (f := fun r => M.cutMomentReal 2 r)
    (g := fun t => M.rhsScalarTwo t) har hrb hint hAE hrhsCont ?_
  filter_upwards [isOpen_Ioo.mem_nhds (show r0 ∈ Set.Ioo a b from ⟨har, hrb⟩)] with x hx
  exact hbase x (Set.Ioo_subset_Icc_self hx)

/-! ## 5. The generic assembly

Everything is radius-local: the fourth cutoff moment is required finite at the right endpoint `b`
of the window only, the coefficient bound on `[a, b]` only, and the flux convergence on `(a, b]`
only, i.e. exactly where the dominated-convergence exchange evaluates it.  The majorant is the one
input this file does not construct; §6 shows how the flux convergence is obtained when the fourth
moment is finite at *every* positive radius, which is the only non-local input that then remains.
-/

/-- **The off-corner `p = 2` radius derivative, from a local majorant and a window-local flux
convergence.**

Inputs, and where each one comes from:

* `hwin : M.IsOffCornerWindow a b` — the radius window is positive and contains no `ρ`-length of an
  edge, so the finite-window Russo identity integrates over it;
* `har`, `hrb` — `r0` is interior to the window (`r0 < b` is what makes the window a neighbourhood
  of `r0`, so that a.e. strong measurability on `(a, b]` suffices for the FTC);
* `h4 : M.cutMoment 4 b ≠ ⊤` — the *only* moment finiteness used.  The second cutoff moment at
  every point of `[a, b]` and at `a` is derived from it by `cutMoment_two_le_cutMoment_four` and
  `cutMoment_monotone`, which is what `tendsto_windowMoment_sub` consumes;
* `hC0`, `hC` — a pointwise bound on `|M.coeffRHS|` on `[a, b]`; it is *not* derived from
  `K_eq_integral` (a tail integral of `|K'|` gives no pointwise bound) and it is an explicit
  hypothesis here;
* `hcoef` — continuity of `M.coeffRHS` at `r0`, for the off-sphere RHS continuity;
* `hsphere` — `r0` is not the `ρ`-length of any edge, for the off-sphere RHS continuity;
* `hfluxMaj`, `hG` — the uniform-in-window majorant and its interval integrability.  **These are
  the remaining gap**: this file constructs no majorant, so the statement below is not an
  unconditional radius derivative;
* `hfluxConv` — the fixed-radius insertion convergence, on the window `(a, b]` only. -/
theorem hasDerivAt_cutMomentReal_two_of_local_majorant {a b r0 : ℝ}
    (hwin : M.IsOffCornerWindow a b) (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 M.V, ∃ k, e ∈ S k)
    (har : a < r0) (hrb : r0 < b)
    (h4 : M.cutMoment 4 b ≠ ⊤)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ r ∈ Set.Icc a b, |M.coeffRHS r| ≤ C)
    (hcoef : ContinuousAt M.coeffRHS r0)
    (hsphere : ∀ y : M.V, M.S.ρ (toVec y) ≠ r0)
    {G : ℝ → ℝ} (hfluxMaj : ∀ n, ∀ t ∈ Set.Ioc a b, M.windowFlux (S n) t ≤ G t)
    (hG : IntervalIntegrable G volume a b)
    (hfluxConv : ∀ t ∈ Set.Ioc a b,
      Tendsto (fun n => M.windowFlux (S n) t) atTop (𝓝 (M.rhsScalarTwo t))) :
    HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r0) r0 := by
  have ha : 0 < a := hwin.1
  have hab : a ≤ b := hwin.2.1
  have hr0 : 0 < r0 := lt_trans ha har
  have h2 : ∀ x ∈ Set.Icc a b, M.cutMoment 2 x ≠ ⊤ := by
    intro x hx
    exact ne_top_of_le_ne_top h4
      (le_trans (M.cutMoment_two_le_cutMoment_four x) (M.cutMoment_monotone 4 hx.2))
  have hmom : ∀ x ∈ Set.Icc a b,
      Tendsto (fun n => M.windowMoment (S n) x - M.windowMoment (S n) a) atTop
        (𝓝 (M.cutMomentReal 2 x - M.cutMomentReal 2 a)) :=
    fun x hx => M.tendsto_windowMoment_sub S hSmono hS (h2 x hx)
      (h2 a ⟨le_rfl, le_trans hx.1 hx.2⟩)
  have hcont : ContinuousAt (fun t => M.rhsScalarTwo t) r0 :=
    M.continuousAt_rhsScalarTwo_of_no_sphere r0 hr0 hrb h4 hsphere hcoef
  have hAE : AEStronglyMeasurable (fun t => M.rhsScalarTwo t)
      (volume.restrict (Set.uIoc a b)) := by
    rw [Set.uIoc_of_le hab]
    exact M.aeStronglyMeasurable_rhsScalarTwo_restrict S hfluxConv
  have hint : IntervalIntegrable (fun t => M.rhsScalarTwo t) volume a b :=
    M.intervalIntegrable_rhsScalarTwo_of_coeffBound_ae hab hAE hC0 hC h4
  exact M.hasDerivAt_cutMomentReal_two_of_window_majorant_pos hwin S har hrb hfluxMaj hG
    hfluxConv hmom hcont hint

/-- **The same, with the flux convergence derived from a fourth cutoff moment that is finite on
the radius interval `(a, b]`.**

This is the fully radius-local form.  The fixed-radius insertion theorem
`tendsto_windowFlux_of_cutMoment_four` needs the fourth moment only at the *one* radius it is
evaluated at, so the hypothesis `h4` is required on `(a, b]` and nowhere else.  In
particular finiteness at `b` alone is *not* what is used for the radii `t < b`: `M.cutLaw t` is a
different measure, and `h4` says so, pointwise.

What is *not* claimed: no finite-box substitution, no two-sided statement at an attained radius,
and no `toReal` of an infinite moment. -/
theorem hasDerivAt_cutMomentReal_two_of_cutMoment_four_majorant {a b r0 : ℝ}
    (hwin : M.IsOffCornerWindow a b) (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 M.V, ∃ k, e ∈ S k)
    (har : a < r0) (hrb : r0 < b)
    (h4 : ∀ t : ℝ, t ∈ Set.Ioc a b → M.cutMoment 4 t ≠ ⊤)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ r ∈ Set.Icc a b, |M.coeffRHS r| ≤ C)
    (hcoef : ContinuousAt M.coeffRHS r0)
    (hsphere : ∀ y : M.V, M.S.ρ (toVec y) ≠ r0)
    {G : ℝ → ℝ} (hfluxMaj : ∀ n, ∀ t ∈ Set.Ioc a b, M.windowFlux (S n) t ≤ G t)
    (hG : IntervalIntegrable G volume a b) :
    HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r0) r0 :=
  M.hasDerivAt_cutMomentReal_two_of_local_majorant hwin S hSmono hS har hrb
    (h4 b ⟨lt_trans har hrb, le_rfl⟩) hC0 hC hcoef hsphere hfluxMaj hG
    (fun t ht => M.tendsto_windowFlux_of_cutMoment_four t (lt_trans hwin.1 ht.1) (h4 t ht)
      S hSmono hS)

/-- **The same from the source's global positive-radius hypothesis** `∀ t > 0, M.cutMoment 4 t ≠ ⊤`.

This is the form in which the hypothesis is available in the paper (a finite fourth moment at every
radius), packaged by `hfluxConv_of_cutMoment_four`; it is the corollary with the global shape, not a
stronger statement. -/
theorem hasDerivAt_cutMomentReal_two_of_global_cutMoment_four_majorant {a b r0 : ℝ}
    (hwin : M.IsOffCornerWindow a b) (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 M.V, ∃ k, e ∈ S k)
    (har : a < r0) (hrb : r0 < b)
    (h4 : ∀ t : ℝ, 0 < t → M.cutMoment 4 t ≠ ⊤)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ r ∈ Set.Icc a b, |M.coeffRHS r| ≤ C)
    (hcoef : ContinuousAt M.coeffRHS r0)
    (hsphere : ∀ y : M.V, M.S.ρ (toVec y) ≠ r0)
    {G : ℝ → ℝ} (hfluxMaj : ∀ n, ∀ t ∈ Set.Ioc a b, M.windowFlux (S n) t ≤ G t)
    (hG : IntervalIntegrable G volume a b) :
    HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r0) r0 :=
  M.hasDerivAt_cutMomentReal_two_of_cutMoment_four_majorant hwin S hSmono hS har hrb
    (fun t ht => h4 t (lt_trans hwin.1 ht.1)) hC0 hC hcoef hsphere hfluxMaj hG

/-- **The local assembly in the vocabulary of `IsWindowMajorantOn`.**

Direction (A) of the swarm states its target as `IsWindowMajorantOn (fun n => M.windowFlux (S n)) G
(Set.Ioc a b)`, the landed name for the pointwise bound; this wrapper is that exact shape, so a
compiled `IsWindowMajorantOn` statement can be fed in without unfolding it. -/
theorem hasDerivAt_cutMomentReal_two_of_isWindowMajorant {a b r0 : ℝ}
    (hwin : M.IsOffCornerWindow a b) (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 M.V, ∃ k, e ∈ S k)
    (har : a < r0) (hrb : r0 < b)
    (h4 : ∀ t : ℝ, t ∈ Set.Ioc a b → M.cutMoment 4 t ≠ ⊤)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ r ∈ Set.Icc a b, |M.coeffRHS r| ≤ C)
    (hcoef : ContinuousAt M.coeffRHS r0)
    (hsphere : ∀ y : M.V, M.S.ρ (toVec y) ≠ r0)
    {G : ℝ → ℝ} (hmaj : IsWindowMajorantOn (fun n => M.windowFlux (S n)) G (Set.Ioc a b))
    (hG : IntervalIntegrable G volume a b) :
    HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r0) r0 :=
  M.hasDerivAt_cutMomentReal_two_of_cutMoment_four_majorant hwin S hSmono hS har hrb h4 hC0 hC
    hcoef hsphere hmaj hG

/-- **The local assembly with the *canonical* majorant `t ↦ ⨆ n, ‖M.windowFlux (S n) t‖`.**

This is the weakest of the majorant hypotheses available: no explicit envelope has to be produced,
only the pointwise boundedness of the window family in the window index and the interval
integrability of the pointwise supremum.  Any explicit majorant `G` of
`hasDerivAt_cutMomentReal_two_of_isWindowMajorant` implies these two hypotheses, so nothing is lost;
what is gained is that the residual input is now canonical, i.e. it does not depend on a choice of
constants in a candidate envelope. -/
theorem hasDerivAt_cutMomentReal_two_of_sSup_majorant {a b r0 : ℝ}
    (hwin : M.IsOffCornerWindow a b) (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 M.V, ∃ k, e ∈ S k)
    (har : a < r0) (hrb : r0 < b)
    (h4 : ∀ t : ℝ, t ∈ Set.Ioc a b → M.cutMoment 4 t ≠ ⊤)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ r ∈ Set.Icc a b, |M.coeffRHS r| ≤ C)
    (hcoef : ContinuousAt M.coeffRHS r0)
    (hsphere : ∀ y : M.V, M.S.ρ (toVec y) ≠ r0)
    (hbdd : ∀ t, BddAbove (Set.range fun n => ‖M.windowFlux (S n) t‖))
    (hsup : IntervalIntegrable (fun t => sSup (Set.range fun n => ‖M.windowFlux (S n) t‖))
      volume a b) :
    HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r0) r0 := by
  refine M.hasDerivAt_cutMomentReal_two_of_cutMoment_four_majorant hwin S hSmono hS har hrb h4
    hC0 hC hcoef hsphere (G := fun t => sSup (Set.range fun n => ‖M.windowFlux (S n) t‖)) ?_ hsup
  intro n t _
  have h1 : ‖M.windowFlux (S n) t‖ ≤ sSup (Set.range fun n => ‖M.windowFlux (S n) t‖) :=
    le_csSup (hbdd t) (Set.mem_range_self n)
  rwa [Real.norm_eq_abs, abs_of_nonneg (M.windowFlux_nonneg (S n) t)] at h1

end SourceModelData

namespace Witness

open PercLib.CriticalLRP.Orchestration
open PercLib.CriticalLRP.Orchestration.SourceModelData

/-! ## 6. The witness model, in the paper's own scale

At `sourceModelWitness d hd α hα` the coefficient is the literal power law
`β_c r^{-d-α-1}`, its modulus is decreasing, and the bound on `[a, ∞)` is the exact value at `a`.
Both coefficient inputs `hC0`, `hC` and the continuity `hcoef` are therefore discharged outright,
and the conclusion is stated in the paper's scale
`powLawCoeff β_c d α r0 * (p2RHS r0).toReal`. -/

/-- **The witness off-corner radius derivative, with a local majorant and a positive-radius flux
convergence.**

The coefficient inputs are discharged: `C = powLawCoeffBound β_c d α a = |β_c| a^{-d-α-1}`,
`hC` is `abs_coeffRHS_sourceModelWitness_le`, `hcoef` is
`continuousAt_coeffRHS_sourceModelWitness`.  The remaining inputs are the off-corner window, the
options `hfluxMaj`/`hG` and `hfluxConv`, the off-sphere condition, the finite fourth moment at `b`,
and the geometry.

This statement covers *arbitrary positive off-sphere radii* `r0` — the window `[a, b]` is arbitrary
with `0 < a < r0 < b` and `hsphere` is an explicit hypothesis.  It is not unconditional: `hfluxMaj`
and `hG` are not constructed here. -/
theorem hasDerivAt_cutMomentReal_two_sourceModelWitness_local_majorant
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {a b r0 : ℝ}
    (hwin : (sourceModelWitness d hd α hα).IsOffCornerWindow a b)
    (S : ℕ → Finset (Sym2 (sourceModelWitness d hd α hα).V)) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 (sourceModelWitness d hd α hα).V, ∃ k, e ∈ S k)
    (har : a < r0) (hrb : r0 < b)
    (h4b : (sourceModelWitness d hd α hα).cutMoment 4 b ≠ ⊤)
    (hsphere : ∀ y : (sourceModelWitness d hd α hα).V,
      (sourceModelWitness d hd α hα).S.ρ (toVec y) ≠ r0)
    {G : ℝ → ℝ}
    (hfluxMaj : ∀ n, ∀ t ∈ Set.Ioc a b,
      (sourceModelWitness d hd α hα).windowFlux (S n) t ≤ G t)
    (hG : IntervalIntegrable G volume a b)
    (hfluxConv : ∀ t ∈ Set.Ioc a b,
      Tendsto (fun n => (sourceModelWitness d hd α hα).windowFlux (S n) t) atTop
        (𝓝 ((sourceModelWitness d hd α hα).rhsScalarTwo t))) :
    HasDerivAt (fun r => (sourceModelWitness d hd α hα).cutMomentReal 2 r)
      (powLawCoeff ((sourceModelWitness d hd α hα).betaCrit : ℝ) d α r0
        * ((sourceModelWitness d hd α hα).p2RHS r0).toReal) r0 := by
  have ha : 0 < a := hwin.1
  have hr0 : 0 < r0 := lt_trans ha har
  have h := (sourceModelWitness d hd α hα).hasDerivAt_cutMomentReal_two_of_local_majorant
    (a := a) (b := b) (r0 := r0) hwin S hSmono hS har hrb h4b
    (powLawCoeffBound_nonneg (d := d) (α := α)
      (β := ((sourceModelWitness d hd α hα).betaCrit : ℝ)) ha)
    (fun _ hr => abs_coeffRHS_sourceModelWitness_le d hd α hα ha hr.1)
    (continuousAt_coeffRHS_sourceModelWitness d hd α hα hr0) hsphere hfluxMaj hG hfluxConv
  rwa [rhsScalarTwo_sourceModelWitness_eq d hd α hα hr0] at h

/-- **The same at the witness model, with the flux convergence derived from a fourth cutoff moment
finite on `(a, b]`.**  The hypotheses that range beyond the radius window are `h4` on `(a, b]` and
`hsphere`; nothing is asked of the fourth moment above `b`. -/
theorem hasDerivAt_cutMomentReal_two_sourceModelWitness_majorant
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {a b r0 : ℝ}
    (hwin : (sourceModelWitness d hd α hα).IsOffCornerWindow a b)
    (S : ℕ → Finset (Sym2 (sourceModelWitness d hd α hα).V)) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 (sourceModelWitness d hd α hα).V, ∃ k, e ∈ S k)
    (har : a < r0) (hrb : r0 < b)
    (h4 : ∀ t : ℝ, t ∈ Set.Ioc a b →
      (sourceModelWitness d hd α hα).cutMoment 4 t ≠ ⊤)
    (hsphere : ∀ y : (sourceModelWitness d hd α hα).V,
      (sourceModelWitness d hd α hα).S.ρ (toVec y) ≠ r0)
    {G : ℝ → ℝ}
    (hfluxMaj : ∀ n, ∀ t ∈ Set.Ioc a b,
      (sourceModelWitness d hd α hα).windowFlux (S n) t ≤ G t)
    (hG : IntervalIntegrable G volume a b) :
    HasDerivAt (fun r => (sourceModelWitness d hd α hα).cutMomentReal 2 r)
      (powLawCoeff ((sourceModelWitness d hd α hα).betaCrit : ℝ) d α r0
        * ((sourceModelWitness d hd α hα).p2RHS r0).toReal) r0 :=
  hasDerivAt_cutMomentReal_two_sourceModelWitness_local_majorant d hd α hα hwin S hSmono hS
    har hrb (h4 b ⟨lt_trans har hrb, le_rfl⟩) hsphere hfluxMaj hG
    (fun t ht =>
      (sourceModelWitness d hd α hα).tendsto_windowFlux_of_cutMoment_four t
        (lt_trans hwin.1 ht.1) (h4 t ht) S hSmono hS)

/-- **The witness derivative from the source's global positive-radius fourth moment.**  The
`∀ t > 0` form of the previous theorem, in the paper's own hypothesis shape. -/
theorem hasDerivAt_cutMomentReal_two_sourceModelWitness_global_majorant
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {a b r0 : ℝ}
    (hwin : (sourceModelWitness d hd α hα).IsOffCornerWindow a b)
    (S : ℕ → Finset (Sym2 (sourceModelWitness d hd α hα).V)) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 (sourceModelWitness d hd α hα).V, ∃ k, e ∈ S k)
    (har : a < r0) (hrb : r0 < b)
    (h4 : ∀ t : ℝ, 0 < t → (sourceModelWitness d hd α hα).cutMoment 4 t ≠ ⊤)
    (hsphere : ∀ y : (sourceModelWitness d hd α hα).V,
      (sourceModelWitness d hd α hα).S.ρ (toVec y) ≠ r0)
    {G : ℝ → ℝ}
    (hfluxMaj : ∀ n, ∀ t ∈ Set.Ioc a b,
      (sourceModelWitness d hd α hα).windowFlux (S n) t ≤ G t)
    (hG : IntervalIntegrable G volume a b) :
    HasDerivAt (fun r => (sourceModelWitness d hd α hα).cutMomentReal 2 r)
      (powLawCoeff ((sourceModelWitness d hd α hα).betaCrit : ℝ) d α r0
        * ((sourceModelWitness d hd α hα).p2RHS r0).toReal) r0 :=
  hasDerivAt_cutMomentReal_two_sourceModelWitness_majorant d hd α hα hwin S hSmono hS har hrb
    (fun t ht => h4 t (lt_trans hwin.1 ht.1)) hsphere hfluxMaj hG

/-- **The witness derivative on the canonical box windows and the off-corner window `[1/2, 1]`.**

Both geometric inputs are discharged (`isOffCornerWindow_sourceModelWitness`,
`sourceModelWitness_sphere_ne`) and the window family is the explicit `boxEdges d n`, so the
hypotheses that appear are exactly: `0 < r0 < 2` through `1/2 < r0 < 1`, the positive-radius fourth
moment `h4`, and the majorant `hfluxMaj`/`hG`.  No majorant is constructed. -/
theorem hasDerivAt_cutMomentReal_two_sourceModelWitness_box_majorant
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {r0 : ℝ}
    (hr0lo : 1 / 2 < r0) (hr0hi : r0 < 1)
    (h4 : ∀ t : ℝ, t ∈ Set.Ioc (1 / 2 : ℝ) 1 →
      (sourceModelWitness d hd α hα).cutMoment 4 t ≠ ⊤)
    {G : ℝ → ℝ}
    (hfluxMaj : ∀ n, ∀ t ∈ Set.Ioc (1 / 2) 1,
      (sourceModelWitness d hd α hα).windowFlux (boxEdges d n) t ≤ G t)
    (hG : IntervalIntegrable G volume (1 / 2) 1) :
    HasDerivAt (fun r => (sourceModelWitness d hd α hα).cutMomentReal 2 r)
      (powLawCoeff ((sourceModelWitness d hd α hα).betaCrit : ℝ) d α r0
        * ((sourceModelWitness d hd α hα).p2RHS r0).toReal) r0 :=
  hasDerivAt_cutMomentReal_two_sourceModelWitness_majorant d hd α hα
    (isOffCornerWindow_sourceModelWitness d hd α hα) (boxEdges d) (boxEdges_mono d)
    (exists_mem_boxEdges d) hr0lo hr0hi h4
    (sourceModelWitness_sphere_ne d hd α hα (lt_trans (by norm_num) hr0lo)
      (lt_trans hr0hi (by norm_num)))
    hfluxMaj hG


/-- **The witness derivative on `[1/2, 1]` with no moment hypothesis whatsoever.**

Below radius `2` every cutoff moment of the witness is `1`
(`cutMoment_sourceModelWitness_eq_one`), so the fourth moment on `(0, 1]` is finite for free and the
moment input of `hasDerivAt_cutMomentReal_two_sourceModelWitness_box_majorant` disappears.  What is
left is exactly: `1/2 < r0 < 1`, a uniform-in-window majorant of the box-window fluxes on `(1/2, 1]`
and its interval integrability.  This is the sharpest statement in this file; it is still not
unconditional, because no majorant is constructed here. -/
theorem hasDerivAt_cutMomentReal_two_sourceModelWitness_box_noMoments_majorant
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {r0 : ℝ}
    (hr0lo : 1 / 2 < r0) (hr0hi : r0 < 1)
    {G : ℝ → ℝ}
    (hfluxMaj : ∀ n, ∀ t ∈ Set.Ioc (1 / 2) 1,
      (sourceModelWitness d hd α hα).windowFlux (boxEdges d n) t ≤ G t)
    (hG : IntervalIntegrable G volume (1 / 2) 1) :
    HasDerivAt (fun r => (sourceModelWitness d hd α hα).cutMomentReal 2 r)
      (powLawCoeff ((sourceModelWitness d hd α hα).betaCrit : ℝ) d α r0
        * ((sourceModelWitness d hd α hα).p2RHS r0).toReal) r0 :=
  hasDerivAt_cutMomentReal_two_sourceModelWitness_box_majorant d hd α hα hr0lo hr0hi
    (fun t ht =>
      cutMoment_four_sourceModelWitness d hd α hα (lt_of_le_of_lt ht.2 (show (1 : ℝ) < 2 by norm_num)))
    hfluxMaj hG


/-- **The box version with the canonical majorant, and no moment hypothesis.**  The residual input
is `t ↦ ⨆ n, ‖windowFlux (boxEdges d n) t‖` being interval integrable on `(1/2, 1]`; no envelope and
no moment appears. -/
theorem hasDerivAt_cutMomentReal_two_sourceModelWitness_box_sSup_majorant
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) {r0 : ℝ}
    (hr0lo : 1 / 2 < r0) (hr0hi : r0 < 1)
    (hbdd : ∀ t,
      BddAbove (Set.range fun n => ‖(sourceModelWitness d hd α hα).windowFlux (boxEdges d n) t‖))
    (hsup : IntervalIntegrable
      (fun t => sSup (Set.range fun n =>
        ‖(sourceModelWitness d hd α hα).windowFlux (boxEdges d n) t‖)) volume (1 / 2) 1) :
    HasDerivAt (fun r => (sourceModelWitness d hd α hα).cutMomentReal 2 r)
      (powLawCoeff ((sourceModelWitness d hd α hα).betaCrit : ℝ) d α r0
        * ((sourceModelWitness d hd α hα).p2RHS r0).toReal) r0 := by
  have h := (sourceModelWitness d hd α hα).hasDerivAt_cutMomentReal_two_of_sSup_majorant
    (isOffCornerWindow_sourceModelWitness d hd α hα) (boxEdges d) (boxEdges_mono d)
    (exists_mem_boxEdges d) hr0lo hr0hi
    (fun t ht =>
      cutMoment_four_sourceModelWitness d hd α hα (lt_of_le_of_lt ht.2 (show (1 : ℝ) < 2 by norm_num)))
    (powLawCoeffBound_nonneg (d := d) (α := α)
      (β := ((sourceModelWitness d hd α hα).betaCrit : ℝ)) (by norm_num : (0 : ℝ) < 1 / 2))
    (fun _ hr => abs_coeffRHS_sourceModelWitness_le d hd α hα (by norm_num : (0 : ℝ) < 1 / 2) hr.1)
    (continuousAt_coeffRHS_sourceModelWitness d hd α hα (lt_trans (by norm_num) hr0lo))
    (sourceModelWitness_sphere_ne d hd α hα (lt_trans (by norm_num) hr0lo)
      (lt_trans hr0hi (by norm_num)))
    hbdd hsup
  rwa [rhsScalarTwo_sourceModelWitness_eq d hd α hα (lt_trans (by norm_num) hr0lo)] at h


/-! ## 7. The `rho`-lengths of the witness are twice a natural number

The witness norm is the *sup* norm (`Pi.norm_def`), so on integral vectors it takes integral values:
`‖toVec z‖ = sup_i |z i|` is a natural number.  Hence every `ρ`-length `2‖toVec (x - y)‖` is twice a
natural number, and the corner set and the sphere set of the witness are contained in `2ℕ`.  This is
what makes the off-corner and off-sphere hypotheses *dischargeable* at radii above `2`, not only
below it (`sourceModelWitness_sphere_ne` covers `r0 < 2` only, via `‖z‖ = 0 ∨ 1 ≤ ‖z‖`). -/

/-- The `ℝ≥0`-norm of an integer cast is its `natAbs`. -/
theorem nnnorm_intCast_eq_natAbs (n : ℤ) : ‖((n : ℤ) : ℝ)‖₊ = (n.natAbs : ℝ≥0) := by
  rw [← NNReal.coe_inj]
  push_cast
  simp [Real.norm_eq_abs, Int.cast_abs]

/-- **The norm of a witness lattice vector is a natural number.**  The norm on `Fin d → ℝ` is the
sup norm, and its value is the `natAbs` of a maximising coordinate. -/
theorem exists_nat_eq_norm_toVec {d : ℕ} (hd : 1 ≤ d) (z : Fin d → ℤ) :
    ∃ k : ℕ, ‖toVec z‖ = (k : ℝ) := by
  have hne : (Finset.univ : Finset (Fin d)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, hd⟩⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin d)) hne
    (fun i => ‖toVec z i‖₊)
  have hA : ‖toVec z i‖₊ = ((z i).natAbs : ℝ≥0) := by
    simp only [toVec]
    exact nnnorm_intCast_eq_natAbs (z i)
  refine ⟨(z i).natAbs, ?_⟩
  rw [Pi.norm_def, hi, hA]
  simp

/-- **Every corner radius of the witness is twice a natural number.** -/
theorem cornerRadii_sourceModelWitness_eq_even (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    {r : ℝ} (hr : r ∈ (sourceModelWitness d hd α hα).cornerRadii) :
    ∃ k : ℕ, r = 2 * (k : ℝ) := by
  obtain ⟨x, y, -, hdist⟩ := hr
  obtain ⟨k, hk⟩ := exists_nat_eq_norm_toVec hd (x - y)
  refine ⟨k, ?_⟩
  rw [SourceNormData.dist] at hdist
  have hdist' : 2 * ‖toVec (x - y)‖ = r := hdist
  exact hdist'.symm.trans (congrArg (fun t => 2 * t) hk)

/-- **The witness has no corner radius in a window free of even natural numbers.** -/
theorem isOffCornerWindow_sourceModelWitness_of_no_even (d : ℕ) (hd : 1 ≤ d) (α : ℝ)
    (hα : 0 < α) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (h : ∀ k : ℕ, 2 * (k : ℝ) ∉ Set.Icc a b) :
    (sourceModelWitness d hd α hα).IsOffCornerWindow a b := by
  refine ⟨ha, hab, ?_⟩
  intro r hr hcorner
  obtain ⟨k, hk⟩ := cornerRadii_sourceModelWitness_eq_even d hd α hα hcorner
  exact h k (hk ▸ hr)

/-- **No `rho`-length of the witness equals a non-even radius.**  This is the off-sphere condition at
*every* positive radius avoiding `2ℕ`, in contrast with `sourceModelWitness_sphere_ne`, which covers
`r0 < 2` only. -/
theorem sourceModelWitness_sphere_ne_of_no_even (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    {r0 : ℝ} (h : ∀ k : ℕ, r0 ≠ 2 * (k : ℝ)) :
    ∀ y : (sourceModelWitness d hd α hα).V,
      (sourceModelWitness d hd α hα).S.ρ (toVec y) ≠ r0 := by
  intro y hy
  obtain ⟨k, hk⟩ := exists_nat_eq_norm_toVec hd y
  refine h k ?_
  have hval : (sourceModelWitness d hd α hα).S.ρ (toVec y) = 2 * ‖toVec y‖ := rfl
  rw [hval] at hy
  exact hy.symm.trans (congrArg (fun t => 2 * t) hk)

/-! ### A concrete nondegenerate radius: the window `[7/2, 39/10]` and `r0 = 37/10`

The interval `(2, 4)` contains the single even natural `2 * 2 = 4` at its right end, so
`[7/2, 39/10] ⊂ (2, 4)` is off corner and `37/10` is off sphere.  Unlike the `[1/2, 1]` instances of
§6, this window is *above* the radius below which the witness cut kernel vanishes: at `r0 = 37/10`
the cut law is not the point mass at the empty configuration and `M.p2RHS r0` is not obviously `0`. -/

/-- `[7/2, 39/10]` is an off-corner window of the witness. -/
theorem isOffCornerWindow_sourceModelWitness_seven_halves (d : ℕ) (hd : 1 ≤ d) (α : ℝ)
    (hα : 0 < α) :
    (sourceModelWitness d hd α hα).IsOffCornerWindow (7 / 2) (39 / 10) := by
  refine isOffCornerWindow_sourceModelWitness_of_no_even d hd α hα (by norm_num) (by norm_num) ?_
  intro k hk
  have hk2 : (k : ℝ) < 2 := by linarith [hk.2]
  have hk1 : k ≤ 1 := by
    have hk' : k < 2 := by exact_mod_cast hk2
    omega
  have hle : ((k : ℝ)) ≤ 1 := by exact_mod_cast hk1
  linarith [hk.1]

/-- `37/10` is not a `rho`-length of the witness. -/
theorem sourceModelWitness_sphere_ne_seven_tenths (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α) :
    ∀ y : (sourceModelWitness d hd α hα).V,
      (sourceModelWitness d hd α hα).S.ρ (toVec y) ≠ (37 / 10 : ℝ) := by
  refine sourceModelWitness_sphere_ne_of_no_even d hd α hα ?_
  intro k hk
  have hk2 : (k : ℝ) < 2 := by linarith
  have hk1 : (1 : ℝ) < (k : ℝ) := by linarith
  have hk' : k < 2 := by exact_mod_cast hk2
  have hk'' : 1 < k := by exact_mod_cast hk1
  have : k = 1 := by omega
  rw [this] at hk
  norm_num at hk

/-- **The witness radius derivative at the concrete nondegenerate off-sphere radius `37/10`**, in
the paper's scale, conditional on exactly two inputs: finiteness of the fourth cutoff moment on
`(0, 39/10]`, and the uniform-in-window majorant on `(7/2, 39/10]` with its interval integrability.
The geometry, the off-sphere condition, the coefficient bound, the coefficient continuity, the
second-moment convergence and the right-hand side's integrability are all discharged. -/
theorem hasDerivAt_cutMomentReal_two_sourceModelWitness_three_and_seven
    (d : ℕ) (hd : 1 ≤ d) (α : ℝ) (hα : 0 < α)
    (h4 : ∀ t : ℝ, t ∈ Set.Ioc (7 / 2 : ℝ) (39 / 10) →
      (sourceModelWitness d hd α hα).cutMoment 4 t ≠ ⊤)
    {G : ℝ → ℝ}
    (hfluxMaj : ∀ n, ∀ t ∈ Set.Ioc (7 / 2) (39 / 10),
      (sourceModelWitness d hd α hα).windowFlux (boxEdges d n) t ≤ G t)
    (hG : IntervalIntegrable G volume (7 / 2) (39 / 10)) :
    HasDerivAt (fun r => (sourceModelWitness d hd α hα).cutMomentReal 2 r)
      (powLawCoeff ((sourceModelWitness d hd α hα).betaCrit : ℝ) d α (37 / 10)
        * ((sourceModelWitness d hd α hα).p2RHS (37 / 10)).toReal) (37 / 10) :=
  hasDerivAt_cutMomentReal_two_sourceModelWitness_majorant d hd α hα
    (isOffCornerWindow_sourceModelWitness_seven_halves d hd α hα) (boxEdges d) (boxEdges_mono d)
    (exists_mem_boxEdges d) (by norm_num) (by norm_num) h4
    (sourceModelWitness_sphere_ne_seven_tenths d hd α hα) hfluxMaj hG

end Witness

end PercLib.CriticalLRP.Orchestration

end

/-! ## Axiom audit -/

#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.aeStronglyMeasurable_rhsScalarTwo_restrict
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.intervalIntegrable_rhsScalarTwo_of_coeffBound_ae
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.intervalIntegrable_candidateMajorant
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.hasDerivAt_of_integral_from_base_ae
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.intervalIntegral_eq_of_majorant_window_pos
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.integral_rhsScalarTwo_eq_sub_of_window_majorant_pos
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.hasDerivAt_cutMomentReal_two_of_window_majorant_pos
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.hasDerivAt_cutMomentReal_two_of_local_majorant
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.hasDerivAt_cutMomentReal_two_of_isWindowMajorant
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.hasDerivAt_cutMomentReal_two_of_sSup_majorant
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.hasDerivAt_cutMomentReal_two_of_cutMoment_four_majorant
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.hasDerivAt_cutMomentReal_two_of_global_cutMoment_four_majorant
#print axioms
  PercLib.CriticalLRP.Orchestration.Witness.hasDerivAt_cutMomentReal_two_sourceModelWitness_local_majorant
#print axioms
  PercLib.CriticalLRP.Orchestration.Witness.hasDerivAt_cutMomentReal_two_sourceModelWitness_majorant
#print axioms
  PercLib.CriticalLRP.Orchestration.Witness.hasDerivAt_cutMomentReal_two_sourceModelWitness_global_majorant
#print axioms
  PercLib.CriticalLRP.Orchestration.Witness.hasDerivAt_cutMomentReal_two_sourceModelWitness_box_majorant
#print axioms
  PercLib.CriticalLRP.Orchestration.Witness.hasDerivAt_cutMomentReal_two_sourceModelWitness_box_noMoments_majorant
#print axioms
  PercLib.CriticalLRP.Orchestration.Witness.hasDerivAt_cutMomentReal_two_sourceModelWitness_box_sSup_majorant
#print axioms
  PercLib.CriticalLRP.Orchestration.Witness.cornerRadii_sourceModelWitness_eq_even
#print axioms
  PercLib.CriticalLRP.Orchestration.Witness.isOffCornerWindow_sourceModelWitness_seven_halves
#print axioms
  PercLib.CriticalLRP.Orchestration.Witness.sourceModelWitness_sphere_ne_seven_tenths
#print axioms
  PercLib.CriticalLRP.Orchestration.Witness.hasDerivAt_cutMomentReal_two_sourceModelWitness_three_and_seven
