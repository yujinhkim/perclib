/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Swarm `smwveg8a1`, member `m4`, direction (A).

Integration donor: `.ultramath/smwveg8a1/m4/Main.lean`, independently checked at `cfb27572ee02f0e8dbc751b822b50389b54f2df5`.

# Measurability in the radius and nonnegativity of the finite-window flux

The landed reduction `SourceModelData.hasDerivAt_cutMomentReal_two` (and its
`hfluxInt`-discharged form `hasDerivAt_cutMomentReal_two_of_fluxInt` of
`Integrated/FluxBounds`) consumes, for a monotone family `S n` of finite edge windows, the two
inputs about the **exact** finite pivotal sum

`M.windowFlux (S n) t = ∑ e ∈ S n, M.cutEdgeDeriv t e * pivotalFlux (M.cutLaw t)
  (cutFun (S n) M.clusterVolSqReal) e`

that are discharged here, for *every* finite window `S` and *every* radius `t`:

* `hfluxMeas : ∀ n, Measurable (M.windowFlux (S n))` — `measurable_windowFlux`;
* `hfluxNN : ∀ n t, 0 ≤ M.windowFlux (S n) t` — `windowFlux_nonneg`.

No moment hypothesis, no off-corner hypothesis, no domination input and no sign assumption on
`M.K` off `(0,∞)` is used.  The third flux input, `hfluxInt`, is already discharged for every
finite window in `Integrated/FluxBounds` (`intervalIntegrable_windowFlux`); section 5 assembles the
target with `hfluxMeas`, `hfluxNN` and `hfluxInt` all removed from the hypothesis list.

## 1-2. Window clusters, nonnegativity

* Each window cluster volume is finite: the cluster computed inside a finite edge window lies in
  the finite vertex set `insert 0 (edgeVertices S)` (`cluster_cutConfig_subset`, landed in
  `FluxBounds`), so `clusterVol (cutConfig S ω) 0 ≠ ⊤` (`clusterVol_cutConfig_ne_top`).  This is
  what makes the `ℝ≥0∞ → ℝ` conversion of `clusterVolSqReal` order preserving on window
  configurations: the unrestricted `volSq` is *not* monotone, since an infinite cluster has
  `toReal = 0`.  The finiteness of the window cluster is therefore essential content, not
  bookkeeping.
* Hence `cutFun S clusterVolSqReal` is monotone in the configuration
  (`monotone_cutFun_clusterVolSqReal`), so opening an edge can only increase it: every per-edge
  flip is pointwise nonnegative (`flipDiff_cutFun_clusterVolSqReal_nonneg`), and so is every
  pivotal flux (`pivotalFlux_cutFun_clusterVolSqReal_nonneg`).
* The edge weight `M.cutEdgeDeriv t e` is nonnegative for `0 < t`
  (`cutEdgeDeriv_nonneg (neg_deriv_K_nonneg ht)`) and vanishes for `t ≤ 0`
  (`cutEdgeDeriv_eq_zero_of_nonpos`, landed in `FluxBounds`).  This is how the `∀ t` of `hfluxNN`
  is met at nonpositive radii without any sign hypothesis on `M.K` off `(0,∞)`.

## 3. The monotonicity that *is* order-theoretic: the window moment

`windowMoment_mono`: enlarging the window can only increase the window moment, for every radius.
This does **not** follow from `cutFun_mono`, whose hypothesis is monotonicity of the *unrestricted*
`volSq` (false at infinite clusters); the proof uses the finiteness of the larger window cluster
(`cutFun_clusterVolSqReal_mono_window`).  Integrability of both window functionals is supplied by
the landed finite-window bound `cutFun_clusterVolSqReal_le`.

## 4. Measurability in the radius

`M.cutLaw refl = edgeMeasure (M.cutProb refl)`, and the pivotal flux of a *window* functional is a
finite Bernoulli expectation over the window (`integral_edgeMeasure_cylinder`,
`pivotalFlux_cutFun_eq_expectation`): the flip of an edge of the window depends only on the states
of the edges of the window.  The expectation is an explicit finite sum of products of the values
`(M.cutProb refl e : unitInterval)` and `1 - (M.cutProb refl e : unitInterval)`
(`measurable_expectation`), hence measurable in the radius because each edge probability is
monotone in the radius (`monotone_cutProb_coe`).  Summing over the finite window against the
measurable weights `cutEdgeDeriv` (`measurable_cutEdgeDeriv`) gives `Measurable (M.windowFlux S)`.

Everywhere measurability is strictly stronger than the almost-everywhere strong measurability
`aestronglyMeasurable_windowFlux` of `FluxBounds`, and it is the form `hfluxMeas` asks for.

## 5. What is *not* proved here: `hfluxMono`

`hfluxMono` (`M.windowFlux S ≤ M.windowFlux T` for `S ⊆ T`) is not a consequence of `cutFun_mono`:
the per-edge flip of a window functional is not monotone in the window.  The exact-rational
computation in `counterexample.md` (script `hfluxMono_counterexample.py`) exhibits nested windows
`S ⊂ T` in the sup-norm witness geometry, all four edges of equal length, where the window pivotal
sum strictly *decreases* as soon as the common open probability exceeds
`q₀ = 0.673522733799661…` (the root of `12q³ + 6q² − 8q − 1` in `(0,1)`).  So `hfluxMono` is not
derivable from the order structure: it needs quantitative bounds on the cut probabilities of a
*specific* window family.  See `counterexample.md` for exactly what this does and does not refute.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.Integrated.FluxBounds
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.RadiusMeasurability.Main

/-!
# Measurability and nonnegativity of the finite-window flux
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.hashCommand false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

variable {V : Type*} [Countable V]

/-! ## 1. Window cluster volumes are finite, and the window functional is monotone -/

/-- **A window cluster volume is finite.**  The cluster computed inside a finite edge window lies in
a finite vertex set.  This is what makes `clusterVolSqReal` order preserving on window
configurations, even though the unrestricted `volSq` is not. -/
theorem clusterVol_ne_top_of_finite {ω : Config V} {x : V} (hfin : (cluster ω x).Finite) :
    clusterVol ω x ≠ ⊤ := by
  rw [clusterVol_eq_encard, encard_coe_eq_ncard_coe hfin]
  exact ENNReal.natCast_ne_top _

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- **A window cluster volume is finite, in the source model.** -/
theorem clusterVol_cutConfig_ne_top (S : Finset (Sym2 M.V)) (ω : Config M.V) :
    clusterVol (cutConfig S ω) (0 : M.V) ≠ ⊤ := by
  refine PercLib.CriticalLRP.clusterVol_ne_top_of_finite (ω := cutConfig S ω) (x := 0) ?_
  exact (Finset.finite_toSet (insert (0 : M.V) (edgeVertices S))).subset
    (M.cluster_cutConfig_subset S ω)

/-! ## 2. Monotonicity of the window functional and nonnegativity of the flips -/

/-- The window functional is monotone in the configuration: a window cluster is finite, so the
`ℝ≥0∞ → ℝ` conversion in `clusterVolSqReal` is order preserving there. -/
theorem monotone_cutFun_clusterVolSqReal (S : Finset (Sym2 M.V)) :
    Monotone (cutFun S M.clusterVolSqReal) := by
  intro ω ω' h
  have hcut : ∀ e, e ∈ cutConfig S ω → e ∈ cutConfig S ω' := fun e he => ⟨h he.1, he.2⟩
  have hle : clusterVol (cutConfig S ω) (0 : M.V) ≤ clusterVol (cutConfig S ω') (0 : M.V) :=
    clusterVol_mono hcut 0
  have hne : clusterVol (cutConfig S ω') (0 : M.V) ≠ ⊤ := M.clusterVol_cutConfig_ne_top S ω'
  have h2 : (clusterVol (cutConfig S ω) (0 : M.V)).toReal
      ≤ (clusterVol (cutConfig S ω') (0 : M.V)).toReal :=
    ENNReal.toReal_mono hne hle
  exact pow_le_pow_left₀ ENNReal.toReal_nonneg h2 2

/-- Opening an edge can only increase a window functional of the squared cluster volume. -/
theorem flipDiff_cutFun_clusterVolSqReal_nonneg (S : Finset (Sym2 M.V)) (e : Sym2 M.V)
    (ω : Config M.V) :
    0 ≤ flipDiff (cutFun S M.clusterVolSqReal) e ω := by
  have hsub : forceOn {e} (∅ : Config M.V) ω ⊆ forceOn {e} ({e} : Config M.V) ω := by
    intro e' he'
    simp only [forceOn, Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff, Set.mem_singleton_iff,
      Set.mem_empty_iff_false, false_and, or_false] at he' ⊢
    tauto
  exact sub_nonneg.mpr (M.monotone_cutFun_clusterVolSqReal S hsub)

/-- **Every finite-window pivotal flux is nonnegative.** -/
theorem pivotalFlux_cutFun_clusterVolSqReal_nonneg (S : Finset (Sym2 M.V)) (r : ℝ)
    (e : Sym2 M.V) :
    0 ≤ pivotalFlux (M.cutLaw r) (cutFun S M.clusterVolSqReal) e := by
  rw [pivotalFlux]
  exact integral_nonneg fun ω => M.flipDiff_cutFun_clusterVolSqReal_nonneg S e ω

/-- **`hfluxNN` for every finite window.**  The exact window flux is nonnegative at every radius:
at nonpositive radii every edge weight vanishes, and at positive radii both factors are
nonnegative. -/
theorem windowFlux_nonneg (S : Finset (Sym2 M.V)) (t : ℝ) : 0 ≤ M.windowFlux S t := by
  rcases le_or_gt t 0 with ht | ht
  · rw [M.windowFlux_eq_zero_of_nonpos S ht]
  · exact Finset.sum_nonneg fun e _ =>
      mul_nonneg (M.cutEdgeDeriv_nonneg (M.neg_deriv_K_nonneg ht) e)
        (M.pivotalFlux_cutFun_clusterVolSqReal_nonneg S t e)

/-! ## 3. The window moment is monotone in the window

The monotonicity that *is* a formal consequence of the definitions is the one for the **moment**,
not for the flux: the window functional increases when the window is enlarged (`cutFun_mono`) and
so does its expectation.  Both window functionals are integrable by the landed finite-window bound
`cutFun_clusterVolSqReal_le`. -/

/-- Measurability of the squared cluster volume as a function of the configuration. -/
theorem measurable_clusterVolSqReal : Measurable M.clusterVolSqReal := by
  have h : Measurable fun ω : Config M.V => (clusterVol ω (0 : M.V)).toReal :=
    (measurable_clusterVol (0 : M.V)).ennreal_toReal
  exact h.pow_const 2

/-- The window functional is integrable under the cut-off law: it is measurable and bounded by the
landed finite-window constant. -/
theorem integrable_cutFun_clusterVolSqReal (S : Finset (Sym2 M.V)) (r : ℝ) :
    Integrable (cutFun S M.clusterVolSqReal) (M.cutLaw r) := by
  refine Integrable.of_bound (measurable_cutFun M.measurable_clusterVolSqReal).aestronglyMeasurable
    (((insert (0 : M.V) (edgeVertices S)).card : ℝ) ^ 2) (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (M.cutFun_clusterVolSqReal_nonneg S ω)]
  exact M.cutFun_clusterVolSqReal_le S ω

/-- **The window functional increases with the window.**  Note that this does *not* follow from
`cutFun_mono`, whose hypothesis is monotonicity of the unrestricted functional: the unrestricted
`volSq` is not monotone (an infinite cluster has `toReal = 0`).  It follows directly from the
finiteness of the *larger* window cluster. -/
theorem cutFun_clusterVolSqReal_mono_window {S T : Finset (Sym2 M.V)} (hST : S ⊆ T) :
    cutFun S M.clusterVolSqReal ≤ cutFun T M.clusterVolSqReal := by
  intro ω
  have hle : clusterVol (cutConfig S ω) (0 : M.V) ≤ clusterVol (cutConfig T ω) (0 : M.V) :=
    clusterVol_mono (cutConfig_mono_S hST ω) 0
  have hne : clusterVol (cutConfig T ω) (0 : M.V) ≠ ⊤ := M.clusterVol_cutConfig_ne_top T ω
  have h2 : (clusterVol (cutConfig S ω) (0 : M.V)).toReal
      ≤ (clusterVol (cutConfig T ω) (0 : M.V)).toReal :=
    ENNReal.toReal_mono hne hle
  exact pow_le_pow_left₀ ENNReal.toReal_nonneg h2 2

/-- **The window moment is monotone in the window.**  Enlarging a finite edge window can only
increase the expectation of the squared cluster volume of the origin. -/
theorem windowMoment_mono {S T : Finset (Sym2 M.V)} (hST : S ⊆ T) (r : ℝ) :
    M.windowMoment S r ≤ M.windowMoment T r :=
  integral_mono (M.integrable_cutFun_clusterVolSqReal S r)
    (M.integrable_cutFun_clusterVolSqReal T r)
    (M.cutFun_clusterVolSqReal_mono_window hST)

end SourceModelData

end PercLib.CriticalLRP.Orchestration

namespace PercLib.CriticalLRP

/-! ## 4. Measurability in the radius

The pivotal flux of a window functional is a finite Bernoulli expectation over the window: the
flip of an edge only depends on the states of the edges of the window, so the infinite-volume
integral collapses to the finite product law (`integral_edgeMeasure_cylinder`,
`pivotalFlux_cutFun_eq_expectation`).  The expectation is an explicit finite sum of products of the
edge probabilities `(M.cutProb refl e : unitInterval)`, so measurability in the radius is the
measurability of those probabilities, which is monotonicity (`monotone_cutProb_coe`). -/

/-- **Measurability of the finite Bernoulli law weights in the edge probabilities.** -/
theorem measurable_configurationLaw {E : Type*} [Fintype E] [DecidableEq E]
    {p : ℝ → E → ℝ} (hp : ∀ e, Measurable fun r => p r e) (s : Configuration E) :
    Measurable fun r => configurationLaw (p r) s := by
  classical
  unfold configurationLaw
  refine Finset.measurable_prod _ fun e _ => ?_
  by_cases h : e ∈ s
  · have hfun : (fun r => (if e ∈ s then p r e else 1 - p r e)) = fun r => p r e := by
      funext r
      rw [ite_eq_left h]
    rw [hfun]
    exact hp e
  · have hfun : (fun r => (if e ∈ s then p r e else 1 - p r e)) = fun r => 1 - p r e := by
      funext r
      rw [ite_eq_right h]
    rw [hfun]
    exact measurable_const.sub (hp e)

/-- **Measurability of a finite-product expectation in the edge probabilities.** -/
theorem measurable_expectation {E : Type*} [Fintype E] [DecidableEq E]
    (X : Configuration E → ℝ) {p : ℝ → E → ℝ} (hp : ∀ e, Measurable fun r => p r e) :
    Measurable fun r => expectation (p r) X := by
  classical
  unfold expectation
  exact Finset.measurable_sum _ fun s _ =>
    (measurable_configurationLaw hp s).mul measurable_const

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- **The pivotal flux of a window functional is a finite Bernoulli expectation.**  The flip of the
edge `e ∈ S` depends only on the states of the edges of the window `S`, so the integral over the
infinite product law is the expectation over the finite product law on `S`
(`integral_edgeMeasure_cylinder`).  This is the form of `pivotalFlux_cutFun` which makes the radius
dependence transparent: the configuration dependence sits in the fixed function
`c ↦ cutConfig S (forceOn {e} η (restrConfig S c))`, and the only radius dependence is in the edge
probabilities. -/
theorem pivotalFlux_cutFun_eq_expectation (S : Finset (Sym2 M.V)) (g : Config M.V → ℝ)
    {e : Sym2 M.V} (he : e ∈ S) (r : ℝ) :
    pivotalFlux (M.cutLaw r) (cutFun S g) e
      = expectation (fun i : S => ((M.cutProb r i : unitInterval) : ℝ))
          (fun c : Configuration S =>
            g (cutConfig S (forceOn ({e} : Set (Sym2 M.V)) ({e} : Config M.V)
                (restrConfig S fun i => i ∈ c)))
            - g (cutConfig S (forceOn ({e} : Set (Sym2 M.V)) (∅ : Config M.V)
                (restrConfig S fun i => i ∈ c)))) := by
  classical
  set Φ : (↥S → Prop) → ℝ := fun y =>
    g (cutConfig S (forceOn ({e} : Set (Sym2 M.V)) ({e} : Config M.V) (restrConfig S y)))
    - g (cutConfig S (forceOn ({e} : Set (Sym2 M.V)) (∅ : Config M.V) (restrConfig S y)))
    with hΦ
  have hidem : ∀ ω : Config M.V, cutConfig S (cutConfig S ω) = cutConfig S ω := by
    intro ω
    simp only [cutConfig, Set.inter_assoc, Set.inter_self]
  have hflip : ∀ ω : Config M.V, flipDiff (cutFun S g) e ω = Φ (S.restrict ω) := by
    intro ω
    simp only [flipDiff, cutFun_apply, restrConfig_restrict, hΦ,
      cutConfig_forceOn_of_mem S he, hidem]
  rw [M.cutLaw_eq_edgeMeasure r, pivotalFlux]
  simp only [hflip]
  simpa only [hΦ] using integral_edgeMeasure_cylinder (M.cutProb r) S Φ

/-- **Measurability in the radius of a window pivotal flux**, for an arbitrary window functional
`g` on configurations.  No hypothesis on `g` is needed: the configuration dependence is frozen in
the finite sum and the only radius dependence is through the edge probabilities. -/
theorem measurable_pivotalFlux_cutFun (S : Finset (Sym2 M.V)) (g : Config M.V → ℝ)
    (e : Sym2 M.V) (he : e ∈ S) :
    Measurable fun r => pivotalFlux (M.cutLaw r) (cutFun S g) e := by
  have hpt : ∀ r, pivotalFlux (M.cutLaw r) (cutFun S g) e
      = expectation (fun i : S => ((M.cutProb r i : unitInterval) : ℝ))
          (fun c : Configuration S =>
            g (cutConfig S (forceOn ({e} : Set (Sym2 M.V)) ({e} : Config M.V)
                (restrConfig S fun i => i ∈ c)))
            - g (cutConfig S (forceOn ({e} : Set (Sym2 M.V)) (∅ : Config M.V)
                (restrConfig S fun i => i ∈ c)))) :=
    fun r => M.pivotalFlux_cutFun_eq_expectation S g he r
  rw [funext hpt]
  exact measurable_expectation (E := S) _
    (fun i => (M.monotone_cutProb_coe i).measurable)

/-- **Measurability in the radius of a window pivotal flux for the exact window functional**
`cutFun S clusterVolSqReal`. -/
theorem measurable_pivotalFlux_cutFun_clusterVolSqReal (S : Finset (Sym2 M.V)) (e : Sym2 M.V)
    (he : e ∈ S) :
    Measurable fun r => pivotalFlux (M.cutLaw r) (cutFun S M.clusterVolSqReal) e :=
  M.measurable_pivotalFlux_cutFun S M.clusterVolSqReal e he

/-- **`hfluxMeas` for every finite window.**  The exact window flux is measurable in the radius, as
a finite sum of measurable products: measurable edge weights times measurable pivotal fluxes. -/
theorem measurable_windowFlux (S : Finset (Sym2 M.V)) : Measurable (M.windowFlux S) := by
  unfold SourceModelData.windowFlux
  exact Finset.measurable_sum _ fun e he =>
    (M.measurable_cutEdgeDeriv e).mul
      (M.measurable_pivotalFlux_cutFun_clusterVolSqReal S e he)

/-! ## 5. Assembly: `hfluxMeas`, `hfluxNN` and `hfluxInt` all discharged -/

/-- **The `p = 2` off-corner radius derivative, with every flux-side input that is a statement
about one finite window discharged.**

Compared with `SourceModelData.hasDerivAt_cutMomentReal_two`, the hypotheses

* `hfluxMeas` — measurability in the radius: `measurable_windowFlux`;
* `hfluxNN` — nonnegativity at every radius: `windowFlux_nonneg`;
* `hfluxInt` — interval integrability on the off-corner window: landed
  `intervalIntegrable_windowFlux` in `Integrated/FluxBounds`,

are gone, for *every* finite window family.  What remains is exactly the monotone-convergence
content: monotonicity of the window fluxes in the window (`hfluxMono`), their pointwise convergence
to `M.rhsScalarTwo` (`hfluxConv`), the three window-moment inputs, and local continuity and
integrability of `M.rhsScalarTwo`. -/
theorem hasDerivAt_cutMomentReal_two_of_window_flux {a b r0 : ℝ}
    (hwin : M.IsOffCornerWindow a b) (S : ℕ → Finset (Sym2 M.V)) (har : a < r0) (hrb : r0 < b)
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
  M.hasDerivAt_cutMomentReal_two_of_fluxInt hwin S har hrb
    (fun n => M.measurable_windowFlux (S n))
    (fun n t => M.windowFlux_nonneg (S n) t)
    hfluxMono hfluxConv hmomMono hmomNN hmomConv hrhsCont hrhsInt

end SourceModelData

end PercLib.CriticalLRP.Orchestration

end

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.clusterVol_ne_top_of_finite
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.clusterVol_cutConfig_ne_top
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.monotone_cutFun_clusterVolSqReal
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.flipDiff_cutFun_clusterVolSqReal_nonneg
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.pivotalFlux_cutFun_clusterVolSqReal_nonneg
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.windowFlux_nonneg
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.measurable_clusterVolSqReal
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.integrable_cutFun_clusterVolSqReal
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutFun_clusterVolSqReal_mono_window
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.windowMoment_mono
#print axioms PercLib.CriticalLRP.measurable_configurationLaw
#print axioms PercLib.CriticalLRP.measurable_expectation
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.pivotalFlux_cutFun_eq_expectation
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.measurable_pivotalFlux_cutFun
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.measurable_pivotalFlux_cutFun_clusterVolSqReal
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.measurable_windowFlux
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.hasDerivAt_cutMomentReal_two_of_window_flux
