/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Finite-window bounds and local radius integrability of the `p = 2` window flux

Integration donor: `.ultramath/smwveg8a1/m2/WindowFluxBound.lean`, checked at `14f1272cadd0c43418e4222458c61961f09ce20c`.

Swarm `smwveg8a1`, member `m2`, direction (B): the input `hfluxInt` of
`SourceModelData.hasDerivAt_cutMomentReal_two`, for the *exact* definition

  `M.windowFlux S r = ∑ e ∈ S, M.cutEdgeDeriv r e *
      pivotalFlux (M.cutLaw r) (cutFun S M.clusterVolSqReal) e`.

The content is genuinely finite-window:

* `clusterVol_cutConfig_le` — inside a finite edge window `S` the cluster of the origin is contained
  in the finite vertex set `insert 0 (edgeVertices S)`, so its volume is at most
  `(insert 0 (edgeVertices S)).card`.  No moment or sharpness assumption is used.
* `cutFun_clusterVolSqReal_le` / `abs_pivotalFlux_cutFun_clusterVolSq_le` — hence the squared
  volume functional of the window is bounded by the *constant* `A_S ^ 2`, and so is the pivotal
  flux of every edge, uniformly in the radius.
* `abs_cutEdgeDeriv_le_deriv` — the edge derivative weight is dominated by
  `β_c |K'(r)|`, which is the source's own derivative weight.
* `intervalIntegrable_deriv_K` — `K'` is interval integrable on a compact radius interval in
  `(0, ∞)`, from antitonicity of `K` alone (`MonotoneOn.intervalIntegrable_deriv`).
* `intervalIntegrable_windowFlux` — `hfluxInt` for every finite `S` and every off-corner window.

No `sorry`, no `admit`, no auxiliary axioms.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Integrated.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.RadiusMoments

/-!
# Finite-window bounds and local radius integrability
-/

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.hashCommand false

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

@[expose] public section

noncomputable section

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-! ## 1. Finite-window cluster containment and the volume bound -/

/-- **The window cluster is contained in the vertices of the window.**  For a finite edge window
`S`, the cluster of the origin computed inside `S` only uses edges of `S`; every vertex of that
cluster other than the origin is therefore an endpoint of an edge of `S`. -/
theorem cluster_cutConfig_subset (S : Finset (Sym2 M.V)) (ω : Config M.V) :
    cluster (cutConfig S ω) (0 : M.V) ⊆ ((insert (0 : M.V) (edgeVertices S) : Finset M.V) :
      Set M.V) := by
  refine cluster_subset_of_leaving_closed (A := insert (0 : M.V) (edgeVertices S)) (by simp) ?_
  intro e _heA heout heS
  refine heout (fun v hv => ?_)
  exact Finset.mem_insert_of_mem (mem_edgeVertices heS.2 hv)

/-- **Finite-window volume bound.**  The cluster volume of the origin inside a finite edge window
`S` is at most the number of its vertices, plus one for the origin. -/
theorem clusterVol_cutConfig_le_toReal (S : Finset (Sym2 M.V)) (ω : Config M.V) :
    (clusterVol (cutConfig S ω) (0 : M.V)).toReal ≤
      ((insert (0 : M.V) (edgeVertices S)).card : ℝ) := by
  rcases Set.finite_or_infinite (cluster (cutConfig S ω) (0 : M.V)) with hfin | hinf
  · have hvol : (clusterVol (cutConfig S ω) (0 : M.V)).toReal =
        ((cluster (cutConfig S ω) (0 : M.V)).ncard : ℝ) := by
      rw [clusterVol_eq_encard, encard_coe_eq_ncard_coe hfin]
      simp
    rw [hvol]
    have hle : (cluster (cutConfig S ω) (0 : M.V)).ncard ≤
        (((insert (0 : M.V) (edgeVertices S) : Finset M.V)) : Set M.V).ncard :=
      Set.ncard_le_ncard (M.cluster_cutConfig_subset S ω)
    rw [Set.ncard_coe_finset] at hle
    exact_mod_cast hle
  · have htop : clusterVol (cutConfig S ω) (0 : M.V) = ⊤ := by
      rw [clusterVol_eq_encard, Set.encard_eq_top_iff.mpr hinf]
      rfl
    rw [htop]
    simp

/-- **The window squared cluster volume is bounded by a constant.**  The bound depends only on the
finite window `S`, uniformly in the configuration. -/
theorem cutFun_clusterVolSqReal_le (S : Finset (Sym2 M.V)) (ω : Config M.V) :
    cutFun S M.clusterVolSqReal ω ≤
      ((insert (0 : M.V) (edgeVertices S)).card : ℝ) ^ 2 := by
  have hle := M.clusterVol_cutConfig_le_toReal S ω
  have hy : (0 : ℝ) ≤ (clusterVol (cutConfig S ω) (0 : M.V)).toReal := ENNReal.toReal_nonneg
  simpa only [cutFun, clusterVolSqReal, SecondMomentExchange.volSq] using
    pow_le_pow_left₀ hy hle 2

/-- Nonnegativity of the window squared cluster volume (as a function of the configuration). -/
theorem cutFun_clusterVolSqReal_nonneg (S : Finset (Sym2 M.V)) (ω : Config M.V) :
    0 ≤ cutFun S M.clusterVolSqReal ω := by
  simp only [cutFun, clusterVolSqReal, SecondMomentExchange.volSq]
  positivity

/-! ## 2. The pivotal flux of the window functional is uniformly bounded -/

/-- **Uniform-in-radius bound on the pivotal flux of the finite-window squared volume.**  The flip
difference of a functional which takes values in `[0, A]` is at most `A` in absolute value, and the
candidate law is a probability measure. -/
theorem abs_pivotalFlux_cutFun_clusterVolSq_le (S : Finset (Sym2 M.V)) (e : Sym2 M.V)
    (r : ℝ) :
    |pivotalFlux (M.cutLaw r) (cutFun S M.clusterVolSqReal) e| ≤
      2 * ((insert (0 : M.V) (edgeVertices S)).card : ℝ) ^ 2 := by
  have hflip : ∀ ω : Config M.V,
      |flipDiff (cutFun S M.clusterVolSqReal) e ω| ≤
        2 * ((insert (0 : M.V) (edgeVertices S)).card : ℝ) ^ 2 := by
    intro ω
    have h₁ := M.cutFun_clusterVolSqReal_le S (forceOn ({e} : Set (Sym2 M.V))
      ({e} : Config M.V) ω)
    have h₂ := M.cutFun_clusterVolSqReal_le S (forceOn ({e} : Set (Sym2 M.V))
      (∅ : Config M.V) ω)
    have h₀ := M.cutFun_clusterVolSqReal_nonneg S (forceOn ({e} : Set (Sym2 M.V))
      (∅ : Config M.V) ω)
    have h₀' := M.cutFun_clusterVolSqReal_nonneg S (forceOn ({e} : Set (Sym2 M.V))
      ({e} : Config M.V) ω)
    have hA : (0 : ℝ) ≤ ((insert (0 : M.V) (edgeVertices S)).card : ℝ) ^ 2 := by positivity
    simp only [flipDiff]
    rw [abs_le]
    constructor <;> linarith
  calc |pivotalFlux (M.cutLaw r) (cutFun S M.clusterVolSqReal) e|
      = ‖∫ ω, flipDiff (cutFun S M.clusterVolSqReal) e ω ∂(M.cutLaw r)‖ := rfl
    _ ≤ 2 * ((insert (0 : M.V) (edgeVertices S)).card : ℝ) ^ 2 := by
        have h := norm_integral_le_of_norm_le_const (μ := M.cutLaw r)
          (f := fun ω => flipDiff (cutFun S M.clusterVolSqReal) e ω)
          (C := 2 * ((insert (0 : M.V) (edgeVertices S)).card : ℝ) ^ 2)
          (Eventually.of_forall fun ω => by
            simpa only [Real.norm_eq_abs] using hflip ω)
        simpa [MeasureTheory.Measure.real, measure_univ] using h

/-! ## 3. The edge derivative weight is dominated by `β_c |K'|` -/

/-- **The cut-off edge derivative is bounded by the source derivative weight.**  The exponential
factor of `cutEdgeDeriv` is at most one, since the cut-off profile of an antitone nonnegative kernel
is nonnegative; the bound therefore holds at every radius. -/
theorem abs_cutEdgeDeriv_le_deriv (e : Sym2 M.V) (r : ℝ) :
    |M.cutEdgeDeriv r e| ≤ (M.betaCrit : ℝ) * |deriv M.K r| := by
  induction e using Sym2.ind with
  | h x y =>
    rw [M.cutEdgeDeriv_mk]
    by_cases hxy : x = y
    · rw [ite_eq_left hxy]
      simp only [abs_zero]
      positivity
    · rw [ite_eq_right hxy]
      by_cases hd : M.S.dist x y ≤ r
      · rw [ite_eq_left hd]
        have hβ : (0 : ℝ) ≤ (M.betaCrit : ℝ) := by positivity
        have hprof : 0 ≤ FiniteVolume.cutoffProfile M.K r (M.S.dist x y) :=
          cutoffProfile_nonneg_on M.K_antitone (M.S.dist_pos hxy)
        have hexp1 : Real.exp (-((M.betaCrit : ℝ) *
            FiniteVolume.cutoffProfile M.K r (M.S.dist x y))) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          nlinarith [mul_nonneg hβ hprof]
        have hexp0 : (0 : ℝ) ≤ Real.exp (-((M.betaCrit : ℝ) *
            FiniteVolume.cutoffProfile M.K r (M.S.dist x y))) := (Real.exp_pos _).le
        have hnonneg : (0 : ℝ) ≤ (M.betaCrit : ℝ) * |deriv M.K r| := by positivity
        calc |(M.betaCrit : ℝ) * -deriv M.K r * Real.exp (-((M.betaCrit : ℝ) *
              FiniteVolume.cutoffProfile M.K r (M.S.dist x y)))|
            = (M.betaCrit : ℝ) * |deriv M.K r| * Real.exp (-((M.betaCrit : ℝ) *
                FiniteVolume.cutoffProfile M.K r (M.S.dist x y))) := by
              rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hβ,
                abs_of_pos (Real.exp_pos _)]
          _ ≤ (M.betaCrit : ℝ) * |deriv M.K r| * 1 :=
              mul_le_mul_of_nonneg_left hexp1 hnonneg
          _ = (M.betaCrit : ℝ) * |deriv M.K r| := by ring
      · rw [ite_eq_right hd]
        simp only [abs_zero]
        positivity

/-! ## 4. The source derivative is locally interval integrable -/

/-- **`K'` is interval integrable on every compact radius interval in `(0, ∞)`.**  This is not an
extra analytic assumption: `K` is antitone on `(0, ∞)`, so `-K` is monotone there and Mathlib's
`MonotoneOn.intervalIntegrable_deriv` applies. -/
theorem intervalIntegrable_deriv_K {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun r => deriv M.K r) volume a b := by
  have hmono : MonotoneOn (fun r => -M.K r) (uIcc a b) :=
    M.K_antitone.neg.mono (by
      rw [uIcc_of_le hab]
      intro x hx
      exact lt_of_lt_of_le ha hx.1)
  have h := hmono.intervalIntegrable_deriv
  have h' : IntervalIntegrable (fun r => -deriv M.K r) volume a b := by
    simpa [deriv_neg] using h
  have h'' : IntervalIntegrable (fun r => -(-deriv M.K r)) volume a b := h'.neg
  simpa using h''

/-! ## 5. `hfluxInt`: interval integrability of the window flux -/

/-- **Pointwise bound on the window flux.**  On a positive radius the window flux is dominated by a
constant (depending only on the finite window `S`) times `|K'|`: the pivotal flux of the window
squared volume is uniformly bounded by `2 |V_S|²`, and the edge weight by `β_c |K'|`. -/
theorem abs_windowFlux_le (S : Finset (Sym2 M.V)) (r : ℝ) :
    |M.windowFlux S r| ≤
      ((S.card : ℝ) * ((M.betaCrit : ℝ) * (2 * ((insert (0 : M.V) (edgeVertices S)).card :
        ℝ) ^ 2))) * |deriv M.K r| := by
  set A : ℝ := ((insert (0 : M.V) (edgeVertices S)).card : ℝ) ^ 2 with hAdef
  have hterm : ∀ e ∈ S, ‖M.cutEdgeDeriv r e *
      pivotalFlux (M.cutLaw r) (cutFun S M.clusterVolSqReal) e‖ ≤
      ((M.betaCrit : ℝ) * (2 * A)) * |deriv M.K r| := by
    intro e _
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 := M.abs_cutEdgeDeriv_le_deriv e r
    have h2 := M.abs_pivotalFlux_cutFun_clusterVolSq_le S e r
    have h3 : (0 : ℝ) ≤ 2 * A := by rw [hAdef]; positivity
    calc |M.cutEdgeDeriv r e| *
          |pivotalFlux (M.cutLaw r) (cutFun S M.clusterVolSqReal) e|
        ≤ ((M.betaCrit : ℝ) * |deriv M.K r|) * (2 * A) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = ((M.betaCrit : ℝ) * (2 * A)) * |deriv M.K r| := by ring
  have hcard : (0 : ℝ) ≤ (S.card : ℝ) := by positivity
  calc |M.windowFlux S r|
      = |∑ e ∈ S, M.cutEdgeDeriv r e *
          pivotalFlux (M.cutLaw r) (cutFun S M.clusterVolSqReal) e| := rfl
    _ ≤ ∑ e ∈ S, ‖M.cutEdgeDeriv r e *
          pivotalFlux (M.cutLaw r) (cutFun S M.clusterVolSqReal) e‖ :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ S, ((M.betaCrit : ℝ) * (2 * A)) * |deriv M.K r| :=
        Finset.sum_le_sum hterm
    _ = ((S.card : ℝ) * ((M.betaCrit : ℝ) * (2 * A))) * |deriv M.K r| := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

/-- **`hfluxInt` for the exact window flux.**  For every finite edge window `S` and every off-corner
radius window `[a, b]`, the window flux `r ↦ M.windowFlux S r` is interval integrable.

This is the input `hfluxInt` of `SourceModelData.hasDerivAt_cutMomentReal_two`.  The two ingredients
are genuinely finite-window: the authorised domination `|pivotalFlux| ≤ 2 |V_S|²` of the squared
volume functional of the window, and local integrability of the source derivative `K'`, which comes
from antitonicity of `K` on `(0, ∞)` (no extra analytic hypothesis).  Measurability in the radius is
not assumed: on an off-corner window the window flux *is* the radius derivative of the window
moment (`hasDerivAt_windowMoment`). -/
theorem intervalIntegrable_windowFlux (S : Finset (Sym2 M.V)) {a b : ℝ}
    (hwin : M.IsOffCornerWindow a b) :
    IntervalIntegrable (M.windowFlux S) volume a b := by
  obtain ⟨ha, hab, hoff⟩ := hwin
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  -- the window flux agrees with the derivative of the window moment on the window
  have hderivmem : ∀ r ∈ Ioc a b, deriv (M.windowMoment S) r = M.windowFlux S r := by
    intro r hr
    have hrpos : 0 < r := lt_trans ha hr.1
    have hoff' : r ∉ M.cornerRadii := hoff r ⟨hr.1.le, hr.2⟩
    exact (M.hasDerivAt_windowMoment S hoff' hrpos).deriv
  have hmeas : AEStronglyMeasurable (M.windowFlux S) (volume.restrict (Ioc a b)) := by
    refine (measurable_deriv (M.windowMoment S)).aestronglyMeasurable.congr ?_
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
    exact Eventually.of_forall hderivmem
  -- the dominating function
  have hintK : IntegrableOn (fun r => |deriv M.K r|) (Ioc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp
      ((M.intervalIntegrable_deriv_K ha hab).abs)
  have hIntDom : Integrable (fun r => ((S.card : ℝ) * ((M.betaCrit : ℝ) *
      (2 * ((insert (0 : M.V) (edgeVertices S)).card : ℝ) ^ 2))) * |deriv M.K r|)
      (volume.restrict (Ioc a b)) := hintK.const_mul _
  refine hIntDom.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  simpa only [Real.norm_eq_abs] using M.abs_windowFlux_le S r

/-- **`hfluxInt` in the measurability-conditional form.**  If the window flux is measurable in the
radius (the direction-`(A)` input `hfluxMeas`), then interval integrability holds on *every* compact
radius interval inside `(0, ∞)`, with no off-corner hypothesis: only the finite-window domination
`|windowFlux| ≤ C_S |K'|` and local integrability of `K'` are used. -/
theorem intervalIntegrable_windowFlux_of_measurable (S : Finset (Sym2 M.V))
    (hmeas : Measurable (M.windowFlux S)) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (M.windowFlux S) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  have hintK : IntegrableOn (fun r => |deriv M.K r|) (Ioc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp
      ((M.intervalIntegrable_deriv_K ha hab).abs)
  have hIntDom : Integrable (fun r => ((S.card : ℝ) * ((M.betaCrit : ℝ) *
      (2 * ((insert (0 : M.V) (edgeVertices S)).card : ℝ) ^ 2))) * |deriv M.K r|)
      (volume.restrict (Ioc a b)) := hintK.const_mul _
  refine hIntDom.mono' hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r _
  simpa only [Real.norm_eq_abs] using M.abs_windowFlux_le S r


/-- **`hfluxInt` as an input of `hasDerivAt_cutMomentReal_two`.**  For a monotone family of finite
edge windows the interval integrability holds window by window. -/
theorem intervalIntegrable_windowFlux_family (S : ℕ → Finset (Sym2 M.V)) {a b : ℝ}
    (hwin : M.IsOffCornerWindow a b) :
    ∀ n, IntervalIntegrable (M.windowFlux (S n)) volume a b :=
  fun n => M.intervalIntegrable_windowFlux (S n) hwin

/-! ## 6. Assembly: the pointwise derivative with `hfluxInt` discharged -/

/-- **The `p = 2` off-corner radius derivative, with `hfluxInt` discharged.**

This is `SourceModelData.hasDerivAt_cutMomentReal_two` with the interval-integrability input for the
window flux removed from the hypothesis list: it is supplied by `intervalIntegrable_windowFlux` for
*every* finite window, hence in particular for any window family.  The remaining hypotheses are the
ones genuine to the monotone-convergence exchange (measurability, nonnegativity and monotonicity of
the window fluxes in the window, pointwise convergence to `rhsScalarTwo`, the window-moment
increments, and local continuity/integrability of `rhsScalarTwo`). -/
theorem hasDerivAt_cutMomentReal_two_of_fluxInt {a b r0 : ℝ} (hwin : M.IsOffCornerWindow a b)
    (S : ℕ → Finset (Sym2 M.V)) (har : a < r0) (hrb : r0 < b)
    (hfluxMeas : ∀ n, Measurable (M.windowFlux (S n)))
    (hfluxNN : ∀ n t, 0 ≤ M.windowFlux (S n) t)
    (hfluxMono : ∀ n t, M.windowFlux (S n) t ≤ M.windowFlux (S (n + 1)) t)
    (hfluxConv : ∀ t, Tendsto (fun n => M.windowFlux (S n) t) atTop (𝓝 (M.rhsScalarTwo t)))
    (hmomMono : ∀ x ∈ Set.Icc a b,
      Monotone fun n => M.windowMoment (S n) x - M.windowMoment (S n) a)
    (hmomNN : ∀ x ∈ Set.Icc a b, ∀ n, 0 ≤ M.windowMoment (S n) x - M.windowMoment (S n) a)
    (hmomConv : ∀ x ∈ Set.Icc a b,
      Tendsto (fun n => M.windowMoment (S n) x - M.windowMoment (S n) a) atTop
        (𝓝 (M.cutMomentReal 2 x - M.cutMomentReal 2 a)))
    (hrhsCont : ContinuousAt (fun t => M.rhsScalarTwo t) r0)
    (hrhsInt : IntervalIntegrable (fun t => M.rhsScalarTwo t) volume a r0) :
    HasDerivAt (fun r => M.cutMomentReal 2 r) (M.rhsScalarTwo r0) r0 :=
  M.hasDerivAt_cutMomentReal_two hwin S har hrb hfluxMeas hfluxNN hfluxMono
    (M.intervalIntegrable_windowFlux_family S hwin) hfluxConv hmomMono hmomNN hmomConv
    hrhsCont hrhsInt

/-! ## 7. Unconditional finite-window identities

With `hfluxInt` discharged, the landed finite-window layers lose their interval-integrability
hypotheses. -/

/-- **The unconditional finite-window FTC identity.**  On an off-corner window the window moment is
the primitive of the window flux, for *every* finite edge window; no integrability hypothesis is
needed any more. -/
theorem integral_windowFlux_eq_sub' (S : Finset (Sym2 M.V)) {a b : ℝ}
    (hwin : M.IsOffCornerWindow a b) :
    ∫ t in a..b, M.windowFlux S t = M.windowMoment S b - M.windowMoment S a :=
  M.integral_windowFlux_eq_sub S hwin (M.intervalIntegrable_windowFlux S hwin)

/-- **The integrated `p = 2` radius identity, with `hfluxInt` discharged.**  This is
`integral_rhsScalarTwo_eq_sub_of_window` with the interval integrability of every window flux
removed from the hypotheses. -/
theorem integral_rhsScalarTwo_eq_sub_of_window' {a b : ℝ} (hwin : M.IsOffCornerWindow a b)
    (S : ℕ → Finset (Sym2 M.V))
    (hmeas : ∀ n, Measurable (M.windowFlux (S n)))
    (hnn : ∀ n t, 0 ≤ M.windowFlux (S n) t)
    (hmono : ∀ n t, M.windowFlux (S n) t ≤ M.windowFlux (S (n + 1)) t)
    (hconv : ∀ t, Tendsto (fun n => M.windowFlux (S n) t) atTop (𝓝 (M.rhsScalarTwo t)))
    (hmommono : ∀ x ∈ Set.Icc a b,
      Monotone fun n => M.windowMoment (S n) x - M.windowMoment (S n) a)
    (hmomnn : ∀ x ∈ Set.Icc a b, ∀ n, 0 ≤ M.windowMoment (S n) x - M.windowMoment (S n) a)
    (hmoment : ∀ x ∈ Set.Icc a b,
      Tendsto (fun n => M.windowMoment (S n) x - M.windowMoment (S n) a) atTop
        (𝓝 (M.cutMomentReal 2 x - M.cutMomentReal 2 a))) :
    ∀ x ∈ Set.Icc a b,
      ∫ t in a..x, M.rhsScalarTwo t = M.cutMomentReal 2 x - M.cutMomentReal 2 a :=
  M.integral_rhsScalarTwo_eq_sub_of_window hwin S hmeas hnn hmono
    (M.intervalIntegrable_windowFlux_family S hwin) hconv hmommono hmomnn hmoment

/-! ## 8. `hfluxInt` on any positive-radius interval

The off-corner hypothesis in section 5 was used only to read the window flux as the radius derivative
of the window moment.  Since the set of corner radii is null (`ae_notMem_cornerRadii`), that
identification holds almost everywhere, which is all that interval integrability needs; and at
nonpositive radii the window flux vanishes identically. -/

/-- The cut-off edge derivative weight vanishes at nonpositive radii: every edge has positive
length, and loop edges have zero kernel. -/
theorem cutEdgeDeriv_eq_zero_of_nonpos {r : ℝ} (hr : r ≤ 0) (e : Sym2 M.V) :
    M.cutEdgeDeriv r e = 0 := by
  induction e using Sym2.ind with
  | h x y =>
    rw [M.cutEdgeDeriv_mk]
    by_cases hxy : x = y
    · rw [ite_eq_left hxy]
    · rw [ite_eq_right hxy, ite_eq_right (by
        intro hd
        have := M.S.dist_pos hxy
        linarith)]

/-- The window flux vanishes at nonpositive radii. -/
theorem windowFlux_eq_zero_of_nonpos (S : Finset (Sym2 M.V)) {r : ℝ} (hr : r ≤ 0) :
    M.windowFlux S r = 0 := by
  simp only [windowFlux]
  exact Finset.sum_eq_zero fun e _ => by
    rw [M.cutEdgeDeriv_eq_zero_of_nonpos hr e, zero_mul]

/-- **The window flux is almost everywhere strongly measurable in the radius**, for every finite
window, with no off-corner hypothesis: it agrees almost everywhere with the everywhere-defined
measurable function `r ↦ if 0 < r then deriv (M.windowMoment S) r else 0`. -/
theorem aestronglyMeasurable_windowFlux (S : Finset (Sym2 M.V)) :
    AEStronglyMeasurable (M.windowFlux S) (volume : Measure ℝ) := by
  have hmeas : Measurable fun r : ℝ => if 0 < r then deriv (M.windowMoment S) r else 0 :=
    (measurable_deriv (M.windowMoment S)).ite measurableSet_Ioi measurable_const
  refine hmeas.aestronglyMeasurable.congr ?_
  filter_upwards [M.ae_notMem_cornerRadii] with r hr
  by_cases hr0 : 0 < r
  · rw [ite_eq_left hr0]
    exact (M.hasDerivAt_windowMoment S hr hr0).deriv
  · rw [ite_eq_right hr0]
    exact (M.windowFlux_eq_zero_of_nonpos S (le_of_not_gt hr0)).symm

/-- **`hfluxInt` on any compact radius interval inside `(0, ∞)`.**  No off-corner hypothesis is
needed: the window flux is almost everywhere the derivative of the window moment. -/
theorem intervalIntegrable_windowFlux_of_pos (S : Finset (Sym2 M.V)) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (M.windowFlux S) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  have hintK : IntegrableOn (fun r => |deriv M.K r|) (Ioc a b) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp
      ((M.intervalIntegrable_deriv_K ha hab).abs)
  have hIntDom : Integrable (fun r => ((S.card : ℝ) * ((M.betaCrit : ℝ) *
      (2 * ((insert (0 : M.V) (edgeVertices S)).card : ℝ) ^ 2))) * |deriv M.K r|)
      (volume.restrict (Ioc a b)) := hintK.const_mul _
  refine hIntDom.mono' ((M.aestronglyMeasurable_windowFlux S).restrict) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r _
  simpa only [Real.norm_eq_abs] using M.abs_windowFlux_le S r

/-- **`hfluxInt` as an input of `hasDerivAt_cutMomentReal_two`, without the off-corner hypothesis.** -/
theorem intervalIntegrable_windowFlux_family_of_pos (S : ℕ → Finset (Sym2 M.V)) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    ∀ n, IntervalIntegrable (M.windowFlux (S n)) volume a b :=
  fun n => M.intervalIntegrable_windowFlux_of_pos (S n) ha hab

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cluster_cutConfig_subset
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.clusterVol_cutConfig_le_toReal
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutFun_clusterVolSqReal_le
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutFun_clusterVolSqReal_nonneg
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.abs_pivotalFlux_cutFun_clusterVolSq_le
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.abs_cutEdgeDeriv_le_deriv
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.intervalIntegrable_deriv_K
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.abs_windowFlux_le
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.intervalIntegrable_windowFlux
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.intervalIntegrable_windowFlux_of_measurable
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.intervalIntegrable_windowFlux_family
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.integral_windowFlux_eq_sub'
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.integral_rhsScalarTwo_eq_sub_of_window'
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutEdgeDeriv_eq_zero_of_nonpos
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.windowFlux_eq_zero_of_nonpos
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.aestronglyMeasurable_windowFlux
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.intervalIntegrable_windowFlux_of_pos
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.intervalIntegrable_windowFlux_family_of_pos
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.hasDerivAt_cutMomentReal_two_of_fluxInt
