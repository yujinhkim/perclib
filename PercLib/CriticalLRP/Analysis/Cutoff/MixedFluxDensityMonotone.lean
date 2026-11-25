/-
# Monotonicity of the mixed cutoff flux density in the cutoff radius

For the source model data of Hutchcroft, *Critical long-range percolation I*
(arXiv:2508.18807v1), the range-truncated law `P_{β_c,r}` has edge-open probability
`cutProb r`, and its truncated kernel `cutKernel r` increases pointwise in `r`
(landed `SourceModelData.cutKernel_mono_r`).  Consequently

* `cutLaw r` stochastically dominates `cutLaw r'` for `r' ≤ r` (`cutLaw_mono_apply`), and
* the mixed density `b ↦ E_b[|K_0| 1{y ∈ K_0}]` increases with the radius: for positive
  radii `r ≤ b` and a finite first cutoff moment at `b`,

  `mixedFluxDensity r y ≤ mixedFluxDensity b y`   (`mixedFluxDensity_mono`),

  more generally `mixedFluxDensity · y` is monotone on `(0, b]`
  (`monotoneOn_mixedFluxDensity`).

The integral is handled by writing `|K_v| 1{y ∈ K_v}` pointwise as the `tsum` over `x` of
the joint cluster indicators `1{x ∈ K_v} 1{y ∈ K_v}`
(`clusterVol_mul_indicator_eq_tsum`); each summand is the probability of the increasing
measurable event `{x ∈ K_v} ∩ {y ∈ K_v}`, so the stochastic domination applies termwise
(`lintegral_clusterVol_mul_indicator_eq_tsum`,
`lintegral_clusterVol_mul_indicator_mono`).  Only the **first** cutoff moment is needed for
the `toReal` transfer.

The last two theorems are the consumer-side reduction: a per-radius bound
`|flux(y,r)| ≤ 2 E_r[|K_0| 1{y ∈ K_0}]` valid for `r ∈ I ⊆ (0, b]` upgrades to the
radius-uniform summable majorant `y ↦ 2 E_b[|K_0| 1{y ∈ K_0}]`, which is exactly the
`hmix` input of the landed `exists_summable_perY_fluxMajorant` and of
`hasDerivAt_cutMassReal_of_mixedMoment`.  That reduction does not assume any incident-edge
transport constant: the majorant is the model's own mixed density at the fixed radius `b`,
which the landed `summable_mixedFluxDensity` shows summable in `y` from `E_b|K_0|² < ∞`
(and `mixedFluxDensity_le_cutMoment_two` shows it is dominated by that moment).

No `sorry`, no `admit`, no `native_decide`, no custom axioms.  No new definitions.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.Resampling

/-!
Monotonicity in the cutoff radius of the mixed two-point/cluster density.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

namespace PercLib.CriticalLRP.Orchestration

/-! ## 1. The mixed density as a sum of joint cluster events

These statements are about the countable-graph configuration space and hold for every
root vertex `v`; the model instantiation takes `v = 0`. -/

section General

variable {V : Type*} [Countable V]

/-- Product of two cluster indicators is the indicator of the intersection of the events. -/
theorem ite_mul_ite_eq_indicator_inter (s t : Set (Config V)) (ω : Config V) :
    (if ω ∈ s then (1 : ℝ≥0∞) else 0) * (if ω ∈ t then (1 : ℝ≥0∞) else 0)
      = (s ∩ t).indicator (fun _ => (1 : ℝ≥0∞)) ω := by
  by_cases hs : ω ∈ s <;> by_cases ht : ω ∈ t <;>
    simp [hs, ht, Set.indicator_of_mem, Set.indicator_of_notMem]

/-- **The mixed density integrand is a `tsum` of joint cluster indicators.** -/
theorem clusterVol_mul_indicator_eq_tsum (ω : Config V) (v y : V) :
    clusterVol ω v * (if y ∈ cluster ω v then (1 : ℝ≥0∞) else 0)
      = ∑' x : V, (if x ∈ cluster ω v then (1 : ℝ≥0∞) else 0) *
          (if y ∈ cluster ω v then (1 : ℝ≥0∞) else 0) := by
  have hrewrite : (∑' w : V, (cluster ω v).indicator (fun _ => (1 : ℝ≥0∞)) w)
      = ∑' w : V, (if w ∈ cluster ω v then (1 : ℝ≥0∞) else 0) :=
    tsum_congr fun w => by rw [Set.indicator_apply]
  rw [clusterVol_eq_tsum, hrewrite]
  exact ENNReal.tsum_mul_right.symm

/-- **The mixed density is the `x`-sum of the joint cluster-event probabilities.** -/
theorem lintegral_clusterVol_mul_indicator_eq_tsum (p : Sym2 V → unitInterval) (v y : V) :
    (∫⁻ ω : Config V, clusterVol ω v *
        (if y ∈ cluster ω v then (1 : ℝ≥0∞) else 0) ∂edgeMeasure p)
      = ∑' x : V, (edgeMeasure p)
          ({ω : Config V | x ∈ cluster ω v} ∩ {ω : Config V | y ∈ cluster ω v}) := by
  have hmeas : ∀ x : V, AEMeasurable (fun ω : Config V =>
      (if x ∈ cluster ω v then (1 : ℝ≥0∞) else 0) *
        (if y ∈ cluster ω v then (1 : ℝ≥0∞) else 0)) (edgeMeasure p) := by
    intro x
    exact (((Measurable.ite (measurableSet_cluster_mem v x) measurable_const
      measurable_const)).mul
        (Measurable.ite (measurableSet_cluster_mem v y) measurable_const
          measurable_const)).aemeasurable
  have hterm : ∀ x : V,
      (∫⁻ ω : Config V, (if x ∈ cluster ω v then (1 : ℝ≥0∞) else 0) *
            (if y ∈ cluster ω v then (1 : ℝ≥0∞) else 0) ∂edgeMeasure p)
        = (edgeMeasure p) ({ω : Config V | x ∈ cluster ω v}
            ∩ {ω : Config V | y ∈ cluster ω v}) := by
    intro x
    rw [show (∫⁻ ω : Config V, (if x ∈ cluster ω v then (1 : ℝ≥0∞) else 0) *
            (if y ∈ cluster ω v then (1 : ℝ≥0∞) else 0) ∂edgeMeasure p)
        = ∫⁻ ω : Config V,
            ({ω : Config V | x ∈ cluster ω v}
              ∩ {ω : Config V | y ∈ cluster ω v}).indicator
              (fun _ => (1 : ℝ≥0∞)) ω ∂edgeMeasure p from
      lintegral_congr fun ω =>
        ite_mul_ite_eq_indicator_inter {ω : Config V | x ∈ cluster ω v}
          {ω : Config V | y ∈ cluster ω v} ω]
    rw [lintegral_indicator_const
      ((measurableSet_cluster_mem v x).inter (measurableSet_cluster_mem v y)) 1, one_mul]
  calc (∫⁻ ω : Config V, clusterVol ω v *
        (if y ∈ cluster ω v then (1 : ℝ≥0∞) else 0) ∂edgeMeasure p)
      = ∫⁻ ω : Config V, ∑' x : V,
          (if x ∈ cluster ω v then (1 : ℝ≥0∞) else 0) *
            (if y ∈ cluster ω v then (1 : ℝ≥0∞) else 0) ∂edgeMeasure p :=
        lintegral_congr fun ω => clusterVol_mul_indicator_eq_tsum ω v y
    _ = ∑' x : V, ∫⁻ ω : Config V,
          (if x ∈ cluster ω v then (1 : ℝ≥0∞) else 0) *
            (if y ∈ cluster ω v then (1 : ℝ≥0∞) else 0) ∂edgeMeasure p :=
        lintegral_tsum hmeas
    _ = ∑' x : V, (edgeMeasure p)
          ({ω : Config V | x ∈ cluster ω v} ∩ {ω : Config V | y ∈ cluster ω v}) :=
        tsum_congr hterm

/-- **The mixed density is monotone in the edge probabilities.** -/
theorem lintegral_clusterVol_mul_indicator_mono {p q : Sym2 V → unitInterval}
    (hpq : ∀ e, p e ≤ q e) (v y : V) :
    (∫⁻ ω : Config V, clusterVol ω v *
        (if y ∈ cluster ω v then (1 : ℝ≥0∞) else 0) ∂edgeMeasure p)
      ≤ (∫⁻ ω : Config V, clusterVol ω v *
        (if y ∈ cluster ω v then (1 : ℝ≥0∞) else 0) ∂edgeMeasure q) := by
  rw [lintegral_clusterVol_mul_indicator_eq_tsum p v y,
    lintegral_clusterVol_mul_indicator_eq_tsum q v y]
  exact ENNReal.tsum_le_tsum fun x => edgeMeasure_mono_of_le hpq
    ((measurableSet_cluster_mem v x).inter (measurableSet_cluster_mem v y))
    ((isIncreasing_cluster_mem v x).inter (isIncreasing_cluster_mem v y))

end General
/-! ## 2. Stochastic monotonicity of the truncated law in the radius -/

namespace SourceModelData

variable (M : SourceModelData)

/-- **Stochastic monotonicity of the truncated law in the radius.** For `0 < r ≤ b` the
probability of every increasing measurable event is at least as large under `cutLaw b`. -/
theorem cutLaw_mono_apply {r b : ℝ} (hr : 0 < r) (hrb : r ≤ b) {A : Set (Config M.V)}
    (hA : MeasurableSet A) (hinc : IsIncreasing A) :
    M.cutLaw r A ≤ M.cutLaw b A := by
  have hb : 0 < b := lt_of_lt_of_le hr hrb
  have h1 : M.cutLaw r = edgeMeasure (M.cutProb r) := rfl
  have h2 : M.cutLaw b = edgeMeasure (M.cutProb b) := rfl
  rw [h1, h2]
  exact edgeMeasure_mono_of_le (fun e => M.cutProb_mono hr hb hrb e) hA hinc

/-- **The mixed density is monotone in the cutoff radius**, in `ℝ≥0∞` form. -/
theorem lintegral_mixedFlux_mono_cutLaw {r b : ℝ} (hr : 0 < r) (hrb : r ≤ b) (y : M.V) :
    (∫⁻ ω : Config M.V, clusterVol ω (0 : M.V) *
        (if y ∈ cluster ω (0 : M.V) then (1 : ℝ≥0∞) else 0) ∂(M.cutLaw r))
      ≤ (∫⁻ ω : Config M.V, clusterVol ω (0 : M.V) *
        (if y ∈ cluster ω (0 : M.V) then (1 : ℝ≥0∞) else 0) ∂(M.cutLaw b)) := by
  have hb : 0 < b := lt_of_lt_of_le hr hrb
  have h1 : M.cutLaw r = edgeMeasure (M.cutProb r) := rfl
  have h2 : M.cutLaw b = edgeMeasure (M.cutProb b) := rfl
  rw [h1, h2]
  exact lintegral_clusterVol_mul_indicator_mono (fun e => M.cutProb_mono hr hb hrb e) 0 y

/-- **Monotonicity of the mixed flux density in the cutoff radius.** For positive radii
`r ≤ b`, a finite first cutoff moment at `b` gives
`mixedFluxDensity r y ≤ mixedFluxDensity b y`. -/
theorem mixedFluxDensity_mono {r b : ℝ} (hr : 0 < r) (hrb : r ≤ b)
    (h1 : M.cutMoment 1 b ≠ ⊤) (y : M.V) :
    M.mixedFluxDensity r y ≤ M.mixedFluxDensity b y := by
  have key := M.lintegral_mixedFlux_mono_cutLaw hr hrb y
  have hmass : M.cutMassAt b (0 : M.V) ≠ ⊤ := by
    rwa [show M.cutMassAt b (0 : M.V) = M.cutMoment 1 b from by
      simp [SourceModelData.cutMassAt, SourceModelData.cutMoment]]
  have hne : (∫⁻ ω : Config M.V, clusterVol ω (0 : M.V) *
      (if y ∈ cluster ω (0 : M.V) then (1 : ℝ≥0∞) else 0) ∂(M.cutLaw b)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hmass ?_
    refine lintegral_mono fun ω => ?_
    have hind : (if y ∈ cluster ω (0 : M.V) then (1 : ℝ≥0∞) else 0) ≤ 1 := by
      by_cases hy : y ∈ cluster ω (0 : M.V)
      · rw [ite_eq_left hy]
      · rw [ite_eq_right hy]; exact zero_le_one
    calc clusterVol ω (0 : M.V) * (if y ∈ cluster ω (0 : M.V) then (1 : ℝ≥0∞) else 0)
        ≤ clusterVol ω (0 : M.V) * 1 := mul_le_mul_right hind _
      _ = clusterVol ω (0 : M.V) := mul_one _
  have hfin := ENNReal.toReal_mono hne key
  simpa [SourceModelData.mixedFluxDensity] using hfin

/-- **Monotonicity on an interval.** Given a finite first moment at the right endpoint,
the mixed density is monotone on `(0, b]`. -/
theorem monotoneOn_mixedFluxDensity {b : ℝ} (h1 : M.cutMoment 1 b ≠ ⊤) (y : M.V) :
    MonotoneOn (fun r : ℝ => M.mixedFluxDensity r y) (Set.Ioc 0 b) := by
  intro r hr r' hr' hrr'
  have hr0 : 0 < r := hr.1
  have hr'0 : 0 < r' := lt_of_lt_of_le hr0 hrr'
  have hb : 0 < b := lt_of_lt_of_le hr'0 hr'.2
  have hmono : M.cutMoment 1 r' ≤ M.cutMoment 1 b := by
    simpa [SourceModelData.cutMoment, SourceModelData.cutMassAt] using
      M.cutMassAt_mono (r := r') (r' := b) hr'0 hb hr'.2
  exact M.mixedFluxDensity_mono hr0 hrr' (ne_top_of_le_ne_top h1 hmono) y

/-- The first cutoff moment is at most the second: cluster volumes are at least one. -/
theorem cutMoment_one_le_two (b : ℝ) : M.cutMoment 1 b ≤ M.cutMoment 2 b := by
  refine lintegral_mono fun ω => ?_
  have h1 : (1 : ℝ≥0∞) ≤ clusterVol ω (0 : M.V) := by
    rw [clusterVol_eq_tsum]
    have h := ENNReal.le_tsum
      (f := fun w : M.V => (cluster ω (0 : M.V)).indicator (fun _ => (1 : ℝ≥0∞)) w) (0 : M.V)
    rwa [Set.indicator_of_mem (cluster_mem_self ω (0 : M.V))] at h
  calc (clusterVol ω (0 : M.V)) ^ 1 = clusterVol ω (0 : M.V) * 1 := by rw [pow_one, mul_one]
    _ ≤ clusterVol ω (0 : M.V) * clusterVol ω (0 : M.V) := mul_le_mul_right h1 _
    _ = (clusterVol ω (0 : M.V)) ^ 2 := by rw [pow_two]

/-- A finite second cutoff moment gives a finite first cutoff moment. -/
theorem cutMoment_one_ne_top_of_two {b : ℝ} (h2 : M.cutMoment 2 b ≠ ⊤) :
    M.cutMoment 1 b ≠ ⊤ :=
  ne_top_of_le_ne_top h2 (M.cutMoment_one_le_two b)

/-- **The mixed density is dominated by the full quadratic moment**: the per-vertex
majorant `2 · mixedFluxDensity b y` is finite and summable under `E_b|K_0|² < ∞`. -/
theorem mixedFluxDensity_le_cutMoment_two {b : ℝ} (h2 : M.cutMoment 2 b ≠ ⊤) (y : M.V) :
    M.mixedFluxDensity b y ≤ (M.cutMoment 2 b).toReal := by
  have key : (∫⁻ ω : Config M.V, clusterVol ω (0 : M.V) *
      (if y ∈ cluster ω (0 : M.V) then (1 : ℝ≥0∞) else 0) ∂(M.cutLaw b))
      ≤ M.cutMoment 2 b := by
    refine lintegral_mono fun ω => ?_
    have hind : (if y ∈ cluster ω (0 : M.V) then (1 : ℝ≥0∞) else 0)
        ≤ clusterVol ω (0 : M.V) := by
      by_cases hy : y ∈ cluster ω (0 : M.V)
      · rw [ite_eq_left hy]
        rw [clusterVol_eq_tsum]
        have h := ENNReal.le_tsum
          (f := fun w : M.V => (cluster ω (0 : M.V)).indicator (fun _ => (1 : ℝ≥0∞)) w) y
        rwa [Set.indicator_of_mem hy] at h
      · rw [ite_eq_right hy]; exact bot_le
    calc clusterVol ω (0 : M.V) * (if y ∈ cluster ω (0 : M.V) then (1 : ℝ≥0∞) else 0)
        ≤ clusterVol ω (0 : M.V) * clusterVol ω (0 : M.V) := mul_le_mul_right hind _
      _ = (clusterVol ω (0 : M.V)) ^ 2 := by rw [pow_two]
  have hfin := ENNReal.toReal_mono h2 key
  simpa [SourceModelData.mixedFluxDensity] using hfin

/-! ## 3. Radius-uniform summable majorant from a per-radius bound -/
/-- **The `hmix` input of `exists_summable_perY_fluxMajorant` from a per-radius bound.**
If the two-point flux at radius `r` is bounded by `2` times the mixed density *at that
same radius* for all `r` in a window `I ⊆ (0, b]`, then it is bounded by `2` times the
mixed density at the fixed radius `b`. -/
theorem mixedFlux_le_mixedFluxDensity_right {I : Set ℝ} {b : ℝ}
    (hIpos : ∀ r ∈ I, 0 < r) (hIb : ∀ r ∈ I, r ≤ b) (h1 : M.cutMoment 1 b ≠ ⊤)
    (hloc : ∀ (y : M.V) (r : ℝ), r ∈ I →
      |sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r|
        ≤ 2 * M.mixedFluxDensity r y) :
    ∀ (y : M.V) (r : ℝ), r ∈ I →
      |sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r|
        ≤ 2 * M.mixedFluxDensity b y := by
  intro y r hr
  refine le_trans (hloc y r hr) ?_
  have hmono := M.mixedFluxDensity_mono (hIpos r hr) (hIb r hr) h1 y
  linarith

/-- **The `hmix` input with a radius-dependent scalar factor.** Same as
`mixedFlux_le_mixedFluxDensity_right`, but the factor in front of the mixed density may
depend on the radius as long as it is bounded by its value at `b` on the window.  This is
the form in which a per-radius incident-transport constant `D_std(r)` composes with the
monotonicity of the density. -/
theorem mixedFlux_le_mul_mixedFluxDensity_right {C : ℝ → ℝ} {I : Set ℝ} {b : ℝ}
    (hIpos : ∀ r ∈ I, 0 < r) (hIb : ∀ r ∈ I, r ≤ b) (h1 : M.cutMoment 1 b ≠ ⊤)
    (hCmono : ∀ r ∈ I, C r ≤ C b) (hCb : 0 ≤ C b)
    (hloc : ∀ (y : M.V) (r : ℝ), r ∈ I →
      |sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r|
        ≤ C r * M.mixedFluxDensity r y) :
    ∀ (y : M.V) (r : ℝ), r ∈ I →
      |sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r|
        ≤ C b * M.mixedFluxDensity b y := by
  intro y r hr
  have hDr : 0 ≤ M.mixedFluxDensity r y := ENNReal.toReal_nonneg
  have hDmono := M.mixedFluxDensity_mono (hIpos r hr) (hIb r hr) h1 y
  calc |sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r|
      ≤ C r * M.mixedFluxDensity r y := hloc y r hr
    _ ≤ C b * M.mixedFluxDensity b y := mul_le_mul (hCmono r hr) hDmono hDr hCb

/-- **Radius-uniform summable per-vertex majorant for the two-point flux from a
per-radius mixed-density bound.** The majorant is `y ↦ 2 E_b[|K_0| 1{y ∈ K_0}]`; it is
summable in `y` by the landed `summable_mixedFluxDensity` from the full quadratic moment
at the single radius `b`. -/
theorem exists_summable_perY_fluxMajorant_of_perRadius {I : Set ℝ} {b : ℝ}
    (hIpos : ∀ r ∈ I, 0 < r) (hIb : ∀ r ∈ I, r ≤ b) (h1 : M.cutMoment 1 b ≠ ⊤)
    (hloc : ∀ (y : M.V) (r : ℝ), r ∈ I →
      |sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r|
        ≤ 2 * M.mixedFluxDensity r y)
    (h2 : M.cutMoment 2 b ≠ ⊤) :
    ∃ u : M.V → ℝ, Summable u ∧ ∀ (y : M.V) (r : ℝ), r ∈ I →
      |sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r| ≤ u y :=
  M.exists_summable_perY_fluxMajorant
    (M.mixedFlux_le_mixedFluxDensity_right hIpos hIb h1 hloc) h2

/-- **The model-level off-corner mass derivative from a per-radius mixed-density bound.**

This is `hasDerivAt_cutMassReal_of_mixedMoment` with the radius-uniform majorant hypothesis
`hmix` (a bound by the mixed density at the fixed right endpoint `bb`) replaced by a bound
by the mixed density *at each radius* `r ∈ (a, bb)`.  The passage from the local bound to
the uniform majorant is `mixedFlux_le_mixedFluxDensity_right`, i.e. the monotonicity of
`mixedFluxDensity` in the radius; the extra positivity hypothesis is `0 ≤ a`, so that the
window consists of positive radii. -/
theorem hasDerivAt_cutMassReal_of_perRadiusBound
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {a bb : ℝ} {r0 : ℝ} (ha : 0 ≤ a) (hr0 : r0 ∈ Set.Ioo a bb)
    (hoff : ∀ r ∈ Set.Ioo a bb, r ∉ M.cornerRadii)
    (hKd : ∀ r ∈ Set.Ioo a bb, DifferentiableAt ℝ M.K r)
    (hdom : ∀ r ∈ Set.Ioo a bb, Summable fun e : Sym2 M.V =>
      |M.cutEdgeDeriv r e| * (2 * (M.cutLaw r).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)}))
    (hboundint : ∀ y : M.V, ∀ a' ∈ Set.Ioo a bb, ∀ b' ∈ Set.Ioo a bb,
      IntervalIntegrable
        (sMomentWeight (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) volume a' b')
    (hmeasK : ∀ y : M.V, ∀ k : ℕ, AEStronglyMeasurable (windowFluxOf (0 : M.V)
      (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) {y}) S M.cutProb M.cutEdgeDeriv k) volume)
    (hmeasinf : ∀ y : M.V, ∀ r ∈ Set.Ioo a bb, StronglyMeasurableAtFilter
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) (𝓝 r) volume)
    (hcontinf : ∀ y : M.V, ∀ r ∈ Set.Ioo a bb, ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hfin : ∀ r ∈ Set.Ioo a bb, M.cutMassAt r 0 ≠ ⊤)
    (h2 : M.cutMoment 2 bb ≠ ⊤)
    (hloc : ∀ (y : M.V) (r : ℝ), r ∈ Set.Ioo a bb →
      |sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r|
        ≤ 2 * M.mixedFluxDensity r y) :
    HasDerivAt M.cutMassReal
      (∑' y : M.V,
        sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r0) r0 :=
  M.hasDerivAt_cutMassReal_of_mixedMoment S hSmono hS hr0 hoff hKd hdom hboundint hmeasK
    hmeasinf hcontinf hfin h2
    (M.mixedFlux_le_mixedFluxDensity_right (I := Set.Ioo a bb) (b := bb)
      (fun _ hr => lt_of_le_of_lt ha hr.1) (fun _ hr => le_of_lt hr.2)
      (M.cutMoment_one_ne_top_of_two h2) hloc)

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

set_option linter.hashCommand false
set_option linter.style.longLine false

#print axioms PercLib.CriticalLRP.Orchestration.ite_mul_ite_eq_indicator_inter
#print axioms PercLib.CriticalLRP.Orchestration.clusterVol_mul_indicator_eq_tsum
#print axioms PercLib.CriticalLRP.Orchestration.lintegral_clusterVol_mul_indicator_eq_tsum
#print axioms PercLib.CriticalLRP.Orchestration.lintegral_clusterVol_mul_indicator_mono
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutLaw_mono_apply
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.lintegral_mixedFlux_mono_cutLaw
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.mixedFluxDensity_mono
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.monotoneOn_mixedFluxDensity
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMoment_one_le_two
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutMoment_one_ne_top_of_two
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.mixedFluxDensity_le_cutMoment_two
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.mixedFlux_le_mixedFluxDensity_right
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.mixedFlux_le_mul_mixedFluxDensity_right
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_summable_perY_fluxMajorant_of_perRadius
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.hasDerivAt_cutMassReal_of_perRadiusBound
