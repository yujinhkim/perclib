/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.RadiusHorizon.Defs
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.RadiusEnvelope
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.RadiusFrozenCylinder
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Uniform-in-radius failure of monotone horizon approximation, and one-sided continuity

Swarm `smwv2c2lw`, member `m1`.

The cutoff law `r ↦ cutLaw r` has continuous per-edge probabilities and, because `K` is
antitone, stochastically increasing edge probabilities.  For an increasing event `A` generated
by finite witnesses (`CylinderOpen A`) this file proves:

* every horizon mass `r ↦ (cutLaw r).real (horizon A S)` is continuous at every `r₀ > 0`
  (a cylinder expectation, `continuousAt_integral_cutLaw_cylinder`);
* the horizon masses increase to `(cutLaw r).real A`;
* hence `r ↦ (cutLaw r).real A` is **lower semicontinuous** everywhere, and since it is also
  nondecreasing in `r` it is **left-continuous**: the `𝓝[<] r₀` limit exists and equals the
  value.  No moment or escape estimate is used, and no uniformity in `r` is assumed.

The second half is the exact delimitation of the remaining gap.  `continuousAt_iff_uniform_tail`
is a Dini-type equivalence: for a monotone sequence of continuous functions increasing to `F`,
continuity of `F` at `r₀` is *equivalent* to a locally uniform tail bound
`∀ ε > 0, ∃ N δ > 0, ∀ r, |r - r₀| < δ → F r - u N r ≤ ε`.  Consequently no argument which
only uses pointwise (in `r`) monotone convergence of the horizon masses can give two-sided
continuity; a genuinely uniform estimate is required.  The two-sided statements (excluded mass,
`hGcont`, `hcontinf`) therefore remain open, and the right-hand limit at `r₀` is exactly where
the missing uniformity has to be spent.
-/

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.hashCommand false

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

variable {V : Type*} [Countable V]

/-! ## 1. The positive cylinders and the horizon truncation -/

theorem isIncreasing_posCyl (F : Finset (Sym2 V)) : IsIncreasing (posCyl F) :=
  fun _ _ hab ha _ he => hab (ha he)

theorem measurableSet_posCyl (F : Finset (Sym2 V)) : MeasurableSet (posCyl F) := by
  have h : posCyl F = {ω : Config V | ∀ e ∈ F, e ∈ ω} := by
    ext ω; simp [posCyl, Set.subset_def]
  rw [h]
  exact measurableSet_allOpen F

theorem mem_posCyl' {F : Finset (Sym2 V)} {ω : Config V} :
    ω ∈ posCyl F ↔ ∀ e ∈ F, e ∈ ω := by
  simp [posCyl, Set.subset_def]

theorem cylinderOpen_isIncreasing {A : Set (Config V)} (hA : CylinderOpen A) :
    IsIncreasing A := by
  intro ω ω' hsub hω
  obtain ⟨F, hF, hFA⟩ := hA ω hω
  exact hFA (fun e he => hsub (hF he))

theorem horizon_subset (A : Set (Config V)) (S : Finset (Sym2 V)) : horizon A S ⊆ A := by
  intro ω hω
  simp only [horizon, Set.mem_iUnion, exists_prop] at hω
  obtain ⟨F, -, hFA, hmem⟩ := hω
  exact hFA hmem

theorem horizon_mono {S S' : Finset (Sym2 V)} (h : S ⊆ S') (A : Set (Config V)) :
    horizon A S ⊆ horizon A S' := by
  intro ω hω
  simp only [horizon, Set.mem_iUnion, exists_prop] at hω ⊢
  obtain ⟨F, hF, hFA, hmem⟩ := hω
  exact ⟨F, Finset.mem_powerset.mpr (Finset.Subset.trans (Finset.mem_powerset.mp hF) h), hFA, hmem⟩

theorem mem_horizon_iff {A : Set (Config V)} {S : Finset (Sym2 V)} {ω : Config V} :
    ω ∈ horizon A S ↔ ∃ F : Finset (Sym2 V), F ⊆ S ∧ posCyl F ⊆ A ∧ ω ∈ posCyl F := by
  simp only [horizon, Set.mem_iUnion, exists_prop, Finset.mem_powerset]

theorem subset_horizon_of_witness {A : Set (Config V)} {S F : Finset (Sym2 V)}
    (hFS : F ⊆ S) (hFA : posCyl F ⊆ A) : posCyl F ⊆ horizon A S := by
  intro ω hω
  exact mem_horizon_iff.mpr ⟨F, hFS, hFA, hω⟩

theorem iUnion_horizon_eq {A : Set (Config V)} (S : ℕ → Finset (Sym2 V))
    (hScof : ∀ F : Finset (Sym2 V), ∃ N, F ⊆ S N) (hA : CylinderOpen A) :
    (⋃ N, horizon A (S N)) = A := by
  refine Set.Subset.antisymm (Set.iUnion_subset fun N => horizon_subset A (S N)) ?_
  intro ω hω
  obtain ⟨F, hF, hFA⟩ := hA ω hω
  obtain ⟨N, hN⟩ := hScof F
  exact Set.mem_iUnion.mpr ⟨N, subset_horizon_of_witness hN hFA hF⟩

theorem measurableSet_horizon (A : Set (Config V)) (S : Finset (Sym2 V)) :
    MeasurableSet (horizon A S) := by
  classical
  have h : horizon A S = ⋃ F ∈ S.powerset.filter (fun F => posCyl F ⊆ A), posCyl F := by
    ext ω
    simp only [mem_horizon_iff, Set.mem_iUnion, exists_prop, Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨F, hFS, hFA, hω⟩
      exact ⟨F, ⟨hFS, hFA⟩, hω⟩
    · rintro ⟨F, ⟨hFS, hFA⟩, hω⟩
      exact ⟨F, hFS, hFA, hω⟩
  rw [h]
  exact MeasurableSet.biUnion (Finset.finite_toSet _).countable
    (fun F _ => measurableSet_posCyl F)

/-! ## 2. The pattern on a finite window -/

theorem mem_patternConf {S : Finset (Sym2 V)} {c : ↥S → Prop} {e : Sym2 V} :
    e ∈ patternConf S c ↔ ∃ h : e ∈ S, c ⟨e, h⟩ := Iff.rfl

theorem patternConf_restrict (S : Finset (Sym2 V)) {ω : Config V} {e : Sym2 V} (he : e ∈ S) :
    e ∈ patternConf S (S.restrict ω) ↔ e ∈ ω := by
  rw [mem_patternConf]
  constructor
  · rintro ⟨h, hc⟩
    exact hc
  · intro h
    exact ⟨he, h⟩

theorem horizon_determined {A : Set (Config V)} (S : Finset (Sym2 V)) {ω ω' : Config V}
    (h : ∀ e ∈ S, (e ∈ ω ↔ e ∈ ω')) : (ω ∈ horizon A S ↔ ω' ∈ horizon A S) := by
  rw [mem_horizon_iff, mem_horizon_iff]
  constructor
  · rintro ⟨F, hFS, hFA, hFω⟩
    exact ⟨F, hFS, hFA, fun e he => (h e (hFS he)).mp (mem_posCyl'.mp hFω e he)⟩
  · rintro ⟨F, hFS, hFA, hFω⟩
    exact ⟨F, hFS, hFA, fun e he => (h e (hFS he)).mpr (mem_posCyl'.mp hFω e he)⟩

theorem horizon_indicator_eq (A : Set (Config V)) (S : Finset (Sym2 V)) (ω : Config V) :
    (horizon A S).indicator (1 : Config V → ℝ) ω
      = horizonObs A S (fun e : ↥S => (e : Sym2 V) ∈ ω) := by
  classical
  have hdet : (ω ∈ horizon A S ↔ patternConf S (fun e : ↥S => (e : Sym2 V) ∈ ω) ∈ horizon A S) :=
    horizon_determined S fun e he => (patternConf_restrict S he).symm
  rw [horizonObs, Set.indicator_apply, Set.indicator_apply, Pi.one_apply, Pi.one_apply]
  by_cases h : ω ∈ horizon A S
  · simp [h, hdet.mp h]
  · have h' : patternConf S (fun e : ↥S => (e : Sym2 V) ∈ ω) ∉ horizon A S := fun hh => h (hdet.mpr hh)
    simp [h, h']


/-! ## 3. The horizon mass of a cylinder-open event is continuous in the radius -/

namespace Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- **Horizon masses are continuous in the cutoff radius.**  The horizon truncation depends on
the finitely many edges in `S` only, so its mass is a cylinder expectation; cylinder expectations
are continuous in a continuously varying family of edge probabilities
(`continuousAt_integral_cutLaw_cylinder`), and `r ↦ (cutProb r e : ℝ)` is continuous at every
positive radius. -/
theorem continuousAt_real_horizon (A : Set (Config M.V)) (S : Finset (Sym2 M.V))
    {r0 : ℝ} (hr0 : 0 < r0) :
    ContinuousAt (fun r => (M.cutLaw r).real (horizon A S)) r0 := by
  have hcont : ContinuousAt
      (fun r => ∫ ω, horizonObs A S (fun e : ↥S => (e : Sym2 M.V) ∈ ω) ∂(M.cutLaw r)) r0 :=
    M.continuousAt_integral_cutLaw_cylinder S (horizonObs A S) hr0
  refine hcont.congr (Filter.Eventually.of_forall fun r => ?_)
  change (∫ ω, horizonObs A S (fun e : ↥S => (e : Sym2 M.V) ∈ ω) ∂(M.cutLaw r))
    = (M.cutLaw r).real (horizon A S)
  rw [← integral_indicator_one (μ := M.cutLaw r) (measurableSet_horizon A S)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω => (horizon_indicator_eq A S ω).symm)

/-- **Horizon masses increase to the mass of the event.**  Continuity from below for the finite
measure `cutLaw r` along the monotone family `N ↦ horizon A (S N)`, whose union is `A`. -/
theorem tendsto_real_horizon {A : Set (Config M.V)} (S : ℕ → Finset (Sym2 M.V)) (hS : Monotone S)
    (hA : (⋃ N, horizon A (S N)) = A) (r : ℝ) :
    Tendsto (fun N => (M.cutLaw r).real (horizon A (S N))) atTop (𝓝 ((M.cutLaw r).real A)) := by
  have hmono : Monotone fun N => horizon A (S N) := fun n m hnm => horizon_mono (hS hnm) A
  have h2 := tendsto_measure_iUnion_atTop (μ := M.cutLaw r)
    (s := fun N => horizon A (S N)) hmono
  rw [hA] at h2
  have h1 : Tendsto (fun N => (M.cutLaw r) (horizon A (S N))) atTop (𝓝 ((M.cutLaw r) A)) :=
    Tendsto.congr (fun N => rfl) h2
  have h3 : Tendsto (fun N => ((M.cutLaw r) (horizon A (S N))).toReal) atTop
      (𝓝 (((M.cutLaw r) A).toReal)) :=
    (ENNReal.tendsto_toReal_iff (fun N => measure_ne_top _ _)
      (measure_ne_top (M.cutLaw r) A)).mpr h1
  simpa only [measureReal_def] using h3

/-- **The cutoff law is stochastically increasing in the radius**, in `real` form. -/
theorem real_cutLaw_mono_radius {A : Set (Config M.V)} (hA : MeasurableSet A)
    (hAinc : IsIncreasing A) {r r' : ℝ} (hr : 0 < r) (hr' : 0 < r') (h : r ≤ r') :
    (M.cutLaw r).real A ≤ (M.cutLaw r').real A := by
  have hle : (PercLib.CriticalLRP.edgeMeasure (M.cutProb r)) A
      ≤ (PercLib.CriticalLRP.edgeMeasure (M.cutProb r')) A :=
    PercLib.CriticalLRP.edgeMeasure_mono_of_le (fun e => M.cutProb_mono hr hr' h e) hA hAinc
  rw [PercLib.CriticalLRP.E1Sign.cutLaw_eq M r, PercLib.CriticalLRP.E1Sign.cutLaw_eq M r']
  exact ENNReal.toReal_mono (measure_ne_top _ _) hle

/-- The mass of the horizon truncation is at most the mass of the event. -/
theorem real_horizon_le (A : Set (Config M.V)) (S : Finset (Sym2 M.V)) (r : ℝ) :
    (M.cutLaw r).real (horizon A S) ≤ (M.cutLaw r).real A := by
  rw [measureReal_def, measureReal_def]
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (horizon_subset A S))

/-- The tail of the horizon approximation at `r₀`, made explicit. -/
theorem exists_horizon_tail_lt {A : Set (Config M.V)} (S : ℕ → Finset (Sym2 M.V))
    (hS : Monotone S) (hA : (⋃ N, horizon A (S N)) = A) {r : ℝ} {ε : ℝ} (hε : 0 < ε) :
    ∃ N, (M.cutLaw r).real A - (M.cutLaw r).real (horizon A (S N)) ≤ ε := by
  have hlim := M.tendsto_real_horizon S hS hA r
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hlim) ε hε
  refine ⟨N, ?_⟩
  have hdist : |(M.cutLaw r).real (horizon A (S N)) - (M.cutLaw r).real A| < ε := by
    simpa only [Real.dist_eq] using hN N le_rfl
  rw [abs_lt] at hdist
  linarith [hdist.1]

/-- **Lower semicontinuity of the event mass in the cutoff radius.**  The mass is the supremum of
the continuous horizon masses, so it cannot drop.  No monotonicity in the radius, no moment
estimate and no uniformity in the radius is used. -/
theorem lowerSemicontinuous_real_cutLaw {A : Set (Config M.V)} (_hA : MeasurableSet A)
    (hAopen : CylinderOpen A) (S : ℕ → Finset (Sym2 M.V)) (hS : Monotone S)
    (hScof : ∀ F : Finset (Sym2 M.V), ∃ N, F ⊆ S N) {r0 : ℝ} (hr0 : 0 < r0) :
    ∀ ε > 0, ∀ᶠ r in 𝓝 r0, (M.cutLaw r0).real A - ε ≤ (M.cutLaw r).real A := by
  intro ε hε
  have hUnion : (⋃ N, horizon A (S N)) = A := iUnion_horizon_eq S hScof hAopen
  obtain ⟨N, hN⟩ := M.exists_horizon_tail_lt S hS hUnion (r := r0) (ε := ε / 2) (by linarith)
  have hcont := M.continuousAt_real_horizon A (S N) hr0
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ, hδ, hspec⟩ := hcont (ε / 2) (by linarith)
  filter_upwards [Metric.ball_mem_nhds r0 hδ] with r hr
  have h2 : |(M.cutLaw r).real (horizon A (S N)) - (M.cutLaw r0).real (horizon A (S N))|
      < ε / 2 := by
    have := hspec (Metric.mem_ball.mp hr)
    simpa only [Real.dist_eq] using this
  rw [abs_lt] at h2
  have h1 := M.real_horizon_le A (S N) r
  linarith [h2.2]

/-- **Left continuity of the event mass in the cutoff radius.**  The mass is lower semicontinuous
and nondecreasing in `r`, hence its limit from the left exists and equals the value.  This is
unconditional: nothing about the right-hand limit is asserted, and that is exactly where the
uniform tail estimate is missing. -/
theorem tendsto_nhdsLT_real_cutLaw {A : Set (Config M.V)} (hA : MeasurableSet A)
    (hAinc : IsIncreasing A) (hAopen : CylinderOpen A) (S : ℕ → Finset (Sym2 M.V))
    (hS : Monotone S) (hScof : ∀ F : Finset (Sym2 M.V), ∃ N, F ⊆ S N)
    {r0 : ℝ} (hr0 : 0 < r0) :
    Tendsto (fun r => (M.cutLaw r).real A) (𝓝[<] r0) (𝓝 ((M.cutLaw r0).real A)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  have hUnion : (⋃ N, horizon A (S N)) = A := iUnion_horizon_eq S hScof hAopen
  obtain ⟨N, hN⟩ := M.exists_horizon_tail_lt S hS hUnion (r := r0) (ε := ε / 2) (by linarith)
  have hcont := M.continuousAt_real_horizon A (S N) hr0
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ, hδ, hspec⟩ := hcont (ε / 2) (by linarith)
  refine ⟨min δ (r0 / 2), lt_min hδ (by linarith), fun r hrI hdist => ?_⟩
  have hrlt : r < r0 := hrI
  have hrδ : dist r r0 < δ := lt_of_lt_of_le hdist (min_le_left _ _)
  have hrpos : 0 < r := by
    have h1 : dist r r0 < r0 / 2 := lt_of_lt_of_le hdist (min_le_right _ _)
    rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hrlt)] at h1
    linarith
  have hmono : (M.cutLaw r).real A ≤ (M.cutLaw r0).real A :=
    M.real_cutLaw_mono_radius hA hAinc hrpos hr0 hrlt.le
  have hu : (M.cutLaw r).real (horizon A (S N)) ≤ (M.cutLaw r).real A :=
    M.real_horizon_le A (S N) r
  have hspec' : |(M.cutLaw r).real (horizon A (S N))
      - (M.cutLaw r0).real (horizon A (S N))| < ε / 2 := by
    have := hspec hrδ
    simpa only [Real.dist_eq] using this
  rw [abs_lt] at hspec'
  rw [Real.dist_eq, abs_of_nonpos (by linarith : (M.cutLaw r).real A - (M.cutLaw r0).real A ≤ 0)]
  linarith [hspec'.1, hN, hu, hmono]

end SourceModelData

end Orchestration

/-! ## 4. The Dini-type characterization: continuity is equivalent to a uniform tail bound -/

/-- **Dini-type characterization for monotone approximations by continuous functions.**

Let `u : ℕ → ℝ → ℝ` be a pointwise nondecreasing sequence of functions continuous at `r₀`, with
`u n r ≤ F r` and `u n r → F r` for every `r`.  Then `F` is continuous at `r₀` *if and only if*
the tail `F r - u N r` is small uniformly in `r` near `r₀`.

The `→` direction is the content: continuity of the limit forces the uniform tail, so no argument
which only knows pointwise (in `r`) convergence of the horizon masses can prove continuity of the
limit.  The `←` direction is the standard three-`ε` splitting. -/
theorem continuousAt_iff_uniform_tail {u : ℕ → ℝ → ℝ} {F : ℝ → ℝ} {r0 : ℝ}
    (hmono : Monotone u) (hle : ∀ n r, u n r ≤ F r)
    (htend : ∀ r, Tendsto (fun n => u n r) atTop (𝓝 (F r)))
    (hcont : ∀ n, ContinuousAt (u n) r0) :
    ContinuousAt F r0 ↔
      ∀ ε > 0, ∃ N δ, 0 < δ ∧ ∀ r, |r - r0| < δ → F r - u N r ≤ ε := by
  constructor
  · -- continuity of the limit forces the uniform tail
    intro hF ε hε
    obtain ⟨N, hN⟩ : ∃ N, F r0 - u N r0 ≤ ε / 2 := by
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp (htend r0)) (ε / 2) (by linarith)
      refine ⟨N, ?_⟩
      have hdist : |u N r0 - F r0| < ε / 2 := by simpa only [Real.dist_eq] using hN N le_rfl
      rw [abs_lt] at hdist
      linarith [hdist.1]
    rw [Metric.continuousAt_iff] at hF
    obtain ⟨δ₁, hδ₁, hspec₁⟩ := hF (ε / 4) (by linarith)
    obtain ⟨δ₂, hδ₂, hspec₂⟩ := (Metric.continuousAt_iff.mp (hcont N)) (ε / 4) (by linarith)
    refine ⟨N, min δ₁ δ₂, lt_min hδ₁ hδ₂, fun r hr => ?_⟩
    have h1 : dist (F r) (F r0) < ε / 4 := hspec₁ (lt_of_lt_of_le hr (min_le_left _ _))
    have h2 : dist (u N r) (u N r0) < ε / 4 := hspec₂ (lt_of_lt_of_le hr (min_le_right _ _))
    rw [Real.dist_eq, abs_lt] at h1 h2
    linarith [h1.2, h2.1]
  · -- a uniform tail bound gives continuity
    intro h
    rw [Metric.continuousAt_iff]
    intro ε hε
    obtain ⟨N, δ, hδ, hspec⟩ := h (ε / 3) (by linarith)
    have hN0 : F r0 - u N r0 ≤ ε / 3 := by
      have := hspec r0 (by rw [sub_self, abs_zero]; exact hδ)
      linarith
    obtain ⟨δ', hδ', hspec'⟩ := (Metric.continuousAt_iff.mp (hcont N)) (ε / 3) (by linarith)
    refine ⟨min δ δ', lt_min hδ hδ', fun r hr => ?_⟩
    have h1 : F r - u N r ≤ ε / 3 := hspec r (lt_of_lt_of_le hr (min_le_left _ _))
    have h2 : dist (u N r) (u N r0) < ε / 3 := hspec' (lt_of_lt_of_le hr (min_le_right _ _))
    rw [Real.dist_eq, abs_lt] at h2 ⊢
    constructor <;> linarith [h1, h2.1, h2.2, hN0, hle N r, hle N r0]

/-! ## 5. The connectivity event: left continuity and the exact remaining obligation -/

/-- A cofinal monotone family of finite windows on an enumerable edge set. -/
theorem exists_cofinal_window {W : Type*} (e : ℕ → W) (he : Function.Surjective e) :
    ∃ S : ℕ → Finset W, Monotone S ∧ ∀ F : Finset W, ∃ N, F ⊆ S N := by
  classical
  have hchoice : ∀ a : W, ∃ n, e n = a := fun a => he a
  choose i hi using hchoice
  refine ⟨fun N => (Finset.range N).image e, fun n m hnm => Finset.image_subset_image
    (Finset.range_subset_range.mpr hnm), fun F => ?_⟩
  refine ⟨F.sup i + 1, fun a ha => Finset.mem_image.mpr
    ⟨i a, Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := i) ha)), hi a⟩⟩

/-- **The connection event is generated by finite witnesses.**  The edges of a connecting walk
certify it, and any configuration containing them connects as well. -/
theorem cylinderOpen_connects (x y : V) :
    CylinderOpen {ω : Config V | Connects ω x y} := by
  classical
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω
  rw [← pathConnects_iff] at hω
  obtain ⟨p, hp⟩ := hω
  refine ⟨p.edges.toFinset, ?_, ?_⟩
  · intro e he
    exact hp e (by simpa using he)
  · intro ω' hω'
    simp only [Set.mem_ofPred_eq]
    rw [← pathConnects_iff]
    exact ⟨p, fun e he => mem_posCyl'.mp hω' e (by simpa using he)⟩

namespace Orchestration

variable (M : SourceModelData)

/-- **Left continuity of the two-point function in the cutoff radius**, unconditionally. -/
theorem tendsto_nhdsLT_cutLaw_connects (e : ℕ → Sym2 M.V) (he : Function.Surjective e) {x y : M.V}
    {r0 : ℝ} (hr0 : 0 < r0) :
    Tendsto (fun r => (M.cutLaw r).real {ω | Connects ω x y}) (𝓝[<] r0)
      (𝓝 ((M.cutLaw r0).real {ω | Connects ω x y})) := by
  obtain ⟨S, hS, hScof⟩ := exists_cofinal_window e he
  exact M.tendsto_nhdsLT_real_cutLaw (measurableSet_connects x y) (isIncreasing_connects x y)
    (cylinderOpen_connects x y) S hS hScof hr0


/-- **The two-point mass cannot drop: one-sided lower semicontinuity at every positive radius.**
This is the only information available on the right of `r₀`; the matching upper bound is the
uniform tail of `continuousAt_cutLaw_connects_iff_uniform_horizon`. -/
theorem lowerSemicontinuous_cutLaw_connects {x y : M.V} (e₀ : ℕ → Sym2 M.V)
    (he₀ : Function.Surjective e₀) {r0 : ℝ} (hr0 : 0 < r0) :
    ∀ ε > 0, ∀ᶠ r in 𝓝 r0,
      (M.cutLaw r0).real {ω | Connects ω x y} - ε ≤ (M.cutLaw r).real {ω | Connects ω x y} := by
  obtain ⟨S, hS, hScof⟩ := exists_cofinal_window e₀ he₀
  exact M.lowerSemicontinuous_real_cutLaw (measurableSet_connects x y)
    (cylinderOpen_connects x y) S hS hScof hr0

/-- **The exact remaining obligation for the two-point function.**  Continuity at `r₀` holds if
and only if the horizon tail of the connection probability is small uniformly for radii near
`r₀`.  The right-hand side is the uniform estimate that is not available; it is *equivalent* to
the conclusion, not merely sufficient. -/
theorem continuousAt_cutLaw_connects_iff_uniform_horizon {x y : M.V}
    (S : ℕ → Finset (Sym2 M.V)) (hS : Monotone S)
    (hScof : ∀ F : Finset (Sym2 M.V), ∃ N, F ⊆ S N) {r0 : ℝ} (hr0 : 0 < r0) :
    ContinuousAt (fun r => (M.cutLaw r).real {ω | Connects ω x y}) r0 ↔
      ∀ ε > 0, ∃ N δ, 0 < δ ∧ ∀ r, |r - r0| < δ →
        (M.cutLaw r).real {ω | Connects ω x y}
          - (M.cutLaw r).real (horizon {ω | Connects ω x y} (S N)) ≤ ε := by
  refine continuousAt_iff_uniform_tail
    (u := fun N r => (M.cutLaw r).real (horizon {ω | Connects ω x y} (S N)))
    (F := fun r => (M.cutLaw r).real {ω | Connects ω x y}) ?_ ?_ ?_ ?_
  · intro n m hnm r
    change (M.cutLaw r).real (horizon {ω | Connects ω x y} (S n))
      ≤ (M.cutLaw r).real (horizon {ω | Connects ω x y} (S m))
    rw [measureReal_def, measureReal_def]
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (horizon_mono (hS hnm) _))
  · intro n r
    exact M.real_horizon_le _ (S n) r
  · intro r
    exact M.tendsto_real_horizon S hS (iUnion_horizon_eq S hScof (cylinderOpen_connects x y)) r
  · intro n
    exact M.continuousAt_real_horizon _ (S n) hr0

end Orchestration


/-! ## 6. Application: the forced-event masses and the fixed-edge singleton pivotal flux -/

variable {V : Type*} [Countable V]

/-- The cluster-membership event is generated by finite witnesses. -/
theorem cylinderOpen_cluster_mem (x y : V) :
    CylinderOpen {σ : Config V | y ∈ cluster σ x} := by
  have h : {σ : Config V | y ∈ cluster σ x} = {σ : Config V | Connects σ x y} := by
    ext σ
    exact mem_cluster_iff
  rw [h]
  exact cylinderOpen_connects x y

/-- **Forcing a set of edges open or closed preserves finite witnesses.**  If `E` is generated by
positive cylinders then so is the event that the configuration with the finite edge set `S`
forced to `η` lies in `E`: the witness is the original witness with the edges of `S` deleted,
since those are supplied by the forcing. -/
theorem cylinderOpen_preimage_forceOn {E : Set (Config V)} (hE : CylinderOpen E)
    (S : Finset (Sym2 V)) (η : Config V) :
    CylinderOpen (forceOn (↑S : Set (Sym2 V)) η ⁻¹' E) := by
  classical
  intro ω hω
  obtain ⟨F, hF, hFE⟩ := hE (forceOn (↑S : Set (Sym2 V)) η ω) hω
  have hdel : ∀ a ∈ F, a ∉ S → a ∈ ω := by
    intro a haF haS
    have hmem : a ∈ forceOn (↑S : Set (Sym2 V)) η ω := hF (Finset.mem_coe.mpr haF)
    rw [forceOn, Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff, Finset.mem_coe] at hmem
    rcases hmem with ⟨haω, -⟩ | ⟨-, haS'⟩
    · exact haω
    · exact absurd haS' haS
  have hmemη : ∀ a ∈ F, a ∈ S → a ∈ η := by
    intro a haF haS
    have hmem : a ∈ forceOn (↑S : Set (Sym2 V)) η ω := hF (Finset.mem_coe.mpr haF)
    rw [forceOn, Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff, Finset.mem_coe] at hmem
    rcases hmem with ⟨-, haS'⟩ | ⟨haη, -⟩
    · exact absurd haS haS'
    · exact haη
  refine ⟨F \ S, ?_, ?_⟩
  · intro a ha
    rw [Finset.mem_coe, Finset.mem_sdiff] at ha
    exact hdel a ha.1 ha.2
  · intro ω' hω'
    apply hFE
    intro a haF
    rw [forceOn, Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff, Finset.mem_coe]
    by_cases haS : a ∈ S
    · exact Or.inr ⟨hmemη a haF haS, haS⟩
    · have hmem : a ∈ (↑(F \ S) : Set (Sym2 V)) := by
        rw [Finset.mem_coe, Finset.mem_sdiff]
        exact ⟨haF, haS⟩
      exact Or.inl ⟨hω' hmem, haS⟩

namespace Orchestration

namespace SourceModelData

variable (M : SourceModelData)

theorem cylinderOpen_rawOpenEvent (e : Sym2 M.V) {E : Set (Config M.V)} (hE : CylinderOpen E) :
    CylinderOpen (M.rawOpenEvent e E) := by
  simpa only [SourceModelData.rawOpenEvent, Finset.coe_singleton] using
    cylinderOpen_preimage_forceOn hE {e} {e}

theorem cylinderOpen_rawClosedEvent (e : Sym2 M.V) {E : Set (Config M.V)} (hE : CylinderOpen E) :
    CylinderOpen (M.rawClosedEvent e E) := by
  simpa only [SourceModelData.rawClosedEvent, Finset.coe_singleton] using
    cylinderOpen_preimage_forceOn hE {e} (∅ : Config M.V)

/-- **The singleton pivotal flux is a difference of two forced-event masses.** -/
theorem pivotalFlux_singleton_eq_forced (y : M.V) (e : Sym2 M.V) (r : ℝ) :
    pivotalFlux (M.cutLaw r)
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e
      = (M.cutLaw r).real (M.rawOpenEvent e {σ | y ∈ cluster σ (0 : M.V)})
        - (M.cutLaw r).real (M.rawClosedEvent e {σ | y ∈ cluster σ (0 : M.V)}) := by
  have hflip : pivotalFlux (M.cutLaw r)
      (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e
      = ∫ ω, flipDiff (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e ω
          ∂(M.cutLaw r) := rfl
  rw [hflip, M.sMomentTrunc_singleton_as_indicator y]
  exact M.integral_flipDiff_indicator (M.cutLaw r) e (measurableSet_cluster_mem (0 : M.V) y)

/-- **Left continuity of the forced-open connection mass in the cutoff radius.** -/
theorem tendsto_nhdsLT_real_rawOpenEvent (y : M.V) (e : Sym2 M.V) (e₀ : ℕ → Sym2 M.V)
    (he₀ : Function.Surjective e₀) {r0 : ℝ} (hr0 : 0 < r0) :
    Tendsto (fun r => (M.cutLaw r).real (M.rawOpenEvent e {σ | y ∈ cluster σ (0 : M.V)}))
      (𝓝[<] r0) (𝓝 ((M.cutLaw r0).real (M.rawOpenEvent e {σ | y ∈ cluster σ (0 : M.V)}))) := by
  obtain ⟨S, hS, hScof⟩ := exists_cofinal_window e₀ he₀
  exact M.tendsto_nhdsLT_real_cutLaw
    (M.measurableSet_rawOpenEvent e (measurableSet_cluster_mem (0 : M.V) y))
    (M.isIncreasing_rawOpenEvent e (isIncreasing_cluster_mem (0 : M.V) y))
    (M.cylinderOpen_rawOpenEvent e (cylinderOpen_cluster_mem (0 : M.V) y)) S hS hScof hr0

/-- **Left continuity of the forced-closed connection mass in the cutoff radius.** -/
theorem tendsto_nhdsLT_real_rawClosedEvent (y : M.V) (e : Sym2 M.V) (e₀ : ℕ → Sym2 M.V)
    (he₀ : Function.Surjective e₀) {r0 : ℝ} (hr0 : 0 < r0) :
    Tendsto (fun r => (M.cutLaw r).real (M.rawClosedEvent e {σ | y ∈ cluster σ (0 : M.V)}))
      (𝓝[<] r0) (𝓝 ((M.cutLaw r0).real (M.rawClosedEvent e {σ | y ∈ cluster σ (0 : M.V)}))) := by
  obtain ⟨S, hS, hScof⟩ := exists_cofinal_window e₀ he₀
  exact M.tendsto_nhdsLT_real_cutLaw
    (M.measurableSet_rawClosedEvent e (measurableSet_cluster_mem (0 : M.V) y))
    (M.isIncreasing_rawClosedEvent e (isIncreasing_cluster_mem (0 : M.V) y))
    (M.cylinderOpen_rawClosedEvent e (cylinderOpen_cluster_mem (0 : M.V) y)) S hS hScof hr0

/-- **Left continuity of the fixed-edge singleton pivotal flux in the cutoff radius.**
Unconditional in the radius and in the moments: both forced-event masses are left-continuous, so
their difference is.  This is one side of the `hcontinf` input; the right-hand limit, and with it
the interchange of the pivotal sum with differentiation, is not asserted. -/
theorem tendsto_nhdsLT_real_pivotalFlux_singleton (y : M.V) (e : Sym2 M.V)
    (e₀ : ℕ → Sym2 M.V) (he₀ : Function.Surjective e₀) {r0 : ℝ} (hr0 : 0 < r0) :
    Tendsto (fun r => pivotalFlux (M.cutLaw r)
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e)
      (𝓝[<] r0) (𝓝 (pivotalFlux (M.cutLaw r0)
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e)) := by
  have hopen := M.tendsto_nhdsLT_real_rawOpenEvent y e e₀ he₀ hr0
  have hclosed := M.tendsto_nhdsLT_real_rawClosedEvent y e e₀ he₀ hr0
  have hsub := hopen.sub hclosed
  rw [show (M.cutLaw r0).real (M.rawOpenEvent e {σ | y ∈ cluster σ (0 : M.V)})
        - (M.cutLaw r0).real (M.rawClosedEvent e {σ | y ∈ cluster σ (0 : M.V)})
      = pivotalFlux (M.cutLaw r0)
          (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e from
    (M.pivotalFlux_singleton_eq_forced y e r0).symm] at hsub
  exact Tendsto.congr (fun r => (M.pivotalFlux_singleton_eq_forced y e r).symm) hsub

end SourceModelData

end Orchestration


/-! ## 7. The frozen uniform cylinder approximation is equivalent to the continuity it is used for

`RadiusFrozenCylinder.continuousAt_toReal_lintegral_of_cylinder_approx` transfers a *uniform in
the radius* cylinder approximation of a moment to continuity of that moment.  The converse holds
as well, for a degenerate reason: on the empty edge window every function is a constant, so
continuity at `r₀` is itself an approximation by the constant cylinder observable.  Hence the
frozen approximation hypothesis `hcyl` of `continuousAt_exclScalar_of_cylinderApprox` and
`hGcont_of_cylinderApprox` is *equivalent* to the continuity of the frozen-window moment: it is
not a weaker sufficient condition, and no argument which only has pointwise convergence of
truncations can supply it. -/

namespace Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- **Cylinder approximation is equivalent to continuity**, for any nonnegative integrand. -/
theorem cylinderApprox_iff_continuousAt (F : Config M.V → ℝ≥0∞) {r0 : ℝ} (hr0 : 0 < r0) :
    (∀ ε > 0, ∃ (S : Finset (Sym2 M.V)) (g : (↥S → Prop) → ℝ), 0 ≤ g ∧ ∃ δ > 0,
      ∀ r, |r - r0| < δ →
        |(∫⁻ ω, F ω ∂(M.cutLaw r)).toReal
          - (∫⁻ ω, ENNReal.ofReal (g (S.restrict ω)) ∂(M.cutLaw r)).toReal| ≤ ε)
      ↔ ContinuousAt (fun r => (∫⁻ ω, F ω ∂(M.cutLaw r)).toReal) r0 := by
  constructor
  · intro h
    exact M.continuousAt_toReal_lintegral_of_cylinder_approx F hr0 h
  · intro hF ε hε
    classical
    set c : ℝ := (∫⁻ ω, F ω ∂(M.cutLaw r0)).toReal with hc
    have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
    refine ⟨∅, fun _ => c, fun _ => hc0, ?_⟩
    have hcylval : ∀ r : ℝ,
        (∫⁻ ω, ENNReal.ofReal ((fun _ => c) ((∅ : Finset (Sym2 M.V)).restrict ω))
          ∂(M.cutLaw r)).toReal = c := by
      intro r
      have hprob : IsProbabilityMeasure (M.cutLaw r) := by
        rw [PercLib.CriticalLRP.E1Sign.cutLaw_eq M r]
        infer_instance
      have h1 : (∫⁻ ω, ENNReal.ofReal ((fun _ => c) ((∅ : Finset (Sym2 M.V)).restrict ω))
          ∂(M.cutLaw r)) = ENNReal.ofReal c := by
        rw [lintegral_const, measure_univ, mul_one]
      rw [h1, ENNReal.toReal_ofReal hc0]
    have hcont := hF
    rw [Metric.continuousAt_iff] at hcont
    obtain ⟨δ, hδ, hspec⟩ := hcont (ε / 2) (by linarith)
    refine ⟨δ, hδ, fun r hr => ?_⟩
    have h2 : |(∫⁻ ω, F ω ∂(M.cutLaw r)).toReal - c| < ε / 2 := by
      have := hspec hr
      rwa [Real.dist_eq] at this
    rw [hcylval r]
    linarith [abs_lt.mp h2]

/-- **The frozen uniform cylinder approximation for the excluded mass is equivalent to continuity
of the excluded-mass scalar.**  Composing `cylinderApprox_iff_continuousAt` with the landed
identification `continuousAt_exclScalar_iff_frozenWindow`: the hypothesis `hcyl` consumed by
`continuousAt_exclScalar_of_cylinderApprox` and `hGcont_of_cylinderApprox` is neither weaker nor
stronger than the continuity it is used to prove. -/
theorem cylinderApprox_exclScalar_iff_continuousAt {r0 : ℝ} (hr0 : 0 < r0)
    (hoff : r0 ∉ M.attainedRadii) :
    (∀ ε > 0, ∃ (S : Finset (Sym2 M.V)) (g : (↥S → Prop) → ℝ), 0 ≤ g ∧ ∃ δ > 0,
      ∀ r, |r - r0| < δ →
        |(∫⁻ ω, clusterVol ω (0 : M.V) * ∑ y ∈ E1Sign.ballF M r0,
            ((cluster ω (0 : M.V))ᶜ).indicator (fun _ => (1 : ℝ≥0∞)) y * clusterVol ω y
              ∂(M.cutLaw r)).toReal
          - (∫⁻ ω, ENNReal.ofReal (g (S.restrict ω)) ∂(M.cutLaw r)).toReal| ≤ ε)
      ↔ ContinuousAt M.exclScalar r0 := by
  rw [M.continuousAt_exclScalar_iff_frozenWindow hr0 hoff]
  exact M.cylinderApprox_iff_continuousAt _ hr0

end SourceModelData

end Orchestration

/-! ## 8. The touching event -/

variable {V : Type*} [Countable V]

/-- **The touching event is generated by finite witnesses.** -/
theorem cylinderOpen_touchSet (o : V) (e : Sym2 V) :
    CylinderOpen {ω : Config V | e ∈ touchSet ω o} := by
  intro ω hω
  obtain ⟨v, hve, hv⟩ := mem_touchSet.mp hω
  obtain ⟨F, hF, hFA⟩ := cylinderOpen_cluster_mem o v ω hv
  exact ⟨F, hF, fun ω' hω' => mem_touchSet.mpr ⟨v, hve, hFA hω'⟩⟩

namespace Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- **Left continuity of the touching mass in the cutoff radius.**  The landed
`monotoneOn_cutLaw_touchSet` gives monotonicity in the radius; with the finite-witness structure
this becomes a genuine one-sided limit, with no moment or escape input. -/
theorem tendsto_nhdsLT_real_touchSet (o : M.V) (e : Sym2 M.V) (e₀ : ℕ → Sym2 M.V)
    (he₀ : Function.Surjective e₀) {r0 : ℝ} (hr0 : 0 < r0) :
    Tendsto (fun r => (M.cutLaw r).real {ω | e ∈ touchSet ω o}) (𝓝[<] r0)
      (𝓝 ((M.cutLaw r0).real {ω | e ∈ touchSet ω o})) := by
  obtain ⟨S, hS, hScof⟩ := exists_cofinal_window e₀ he₀
  exact M.tendsto_nhdsLT_real_cutLaw (measurableSet_touchSet_mem e)
    (isIncreasing_touchSet_mem o e) (cylinderOpen_touchSet o e) S hS hScof hr0

end SourceModelData

end Orchestration


/-! ## 9. Monotone double limits do not commute: a counterexample at a positive radius

The Dini-type characterization of §4 has a matching counterexample: continuity of every horizon
function, monotonicity in the horizon index *and* monotonicity in the parameter, together with
pointwise convergence, do not make the limit continuous — here at the positive radius `1`.  This
is the precise reason why the escape/moment input cannot be replaced by the monotone structure of
the horizon approximation alone. -/
theorem exists_monotone_continuous_tendsto_not_continuousAt :
    ∃ (u : ℕ → ℝ → ℝ) (F : ℝ → ℝ), (∀ n, Continuous (u n)) ∧ Monotone u ∧
      (∀ n, Monotone (u n)) ∧
      (∀ r, Tendsto (fun n => u n r) atTop (𝓝 (F r))) ∧ ¬ ContinuousAt F 1 := by
  have key : ∀ x : ℝ, 0 < x →
      Tendsto (fun k : ℕ => 1 - Real.exp (-((k : ℝ) * x))) atTop (𝓝 1) := by
    intro x hx
    have hk : Tendsto (fun k : ℕ => (k : ℝ) * x) atTop atTop :=
      Tendsto.atTop_mul_const hx tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun k : ℕ => Real.exp (-((k : ℝ) * x))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hk)
    have h3 : Tendsto (fun k : ℕ => 1 - Real.exp (-((k : ℝ) * x))) atTop (𝓝 (1 - 0)) :=
      tendsto_const_nhds.sub h2
    simpa using h3
  refine ⟨fun n r => 1 - Real.exp (-((n : ℝ) * max (r - 1) 0)),
    fun r => if 1 < r then 1 else 0, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    have h : Continuous fun r : ℝ => -((n : ℝ) * max (r - 1) 0) := by fun_prop
    exact continuous_const.sub (Real.continuous_exp.comp h)
  · intro n m hnm r
    have h0 : 0 ≤ max (r - 1) 0 := le_max_right _ _
    have hle : (n : ℝ) * max (r - 1) 0 ≤ (m : ℝ) * max (r - 1) 0 := by
      have hnm' : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
      exact mul_le_mul_of_nonneg_right hnm' h0
    have hexp : Real.exp (-((m : ℝ) * max (r - 1) 0)) ≤
        Real.exp (-((n : ℝ) * max (r - 1) 0)) :=
      Real.exp_le_exp.mpr (by linarith)
    change 1 - Real.exp (-((n : ℝ) * max (r - 1) 0)) ≤
      1 - Real.exp (-((m : ℝ) * max (r - 1) 0))
    linarith
  · intro n r r' hrr'
    have hmax : max (r - 1) 0 ≤ max (r' - 1) 0 := max_le_max (by linarith) le_rfl
    have hle : (n : ℝ) * max (r - 1) 0 ≤ (n : ℝ) * max (r' - 1) 0 :=
      mul_le_mul_of_nonneg_left hmax (by positivity)
    have hexp : Real.exp (-((n : ℝ) * max (r' - 1) 0)) ≤
        Real.exp (-((n : ℝ) * max (r - 1) 0)) :=
      Real.exp_le_exp.mpr (by linarith)
    change 1 - Real.exp (-((n : ℝ) * max (r - 1) 0)) ≤
      1 - Real.exp (-((n : ℝ) * max (r' - 1) 0))
    linarith
  · intro r
    by_cases hr : 1 < r
    · have hx : 0 < max (r - 1) 0 := lt_of_lt_of_le (by linarith) (le_max_left _ _)
      have hFr : (if 1 < r then (1 : ℝ) else 0) = 1 := by simp [hr]
      simpa [hFr] using key (max (r - 1) 0) hx
    · have hx : max (r - 1) 0 = 0 := max_eq_right (by linarith)
      have hFr : (if 1 < r then (1 : ℝ) else 0) = 0 := by simp [hr]
      simp only [hFr, hx, mul_zero, neg_zero, Real.exp_zero, sub_self]
      exact tendsto_const_nhds
  · intro hcont
    have ht : Tendsto (fun r => if 1 < r then (1 : ℝ) else 0) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
      have h := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1 : ℝ)))
      simpa using h
    have heq : (fun r => if 1 < r then (1 : ℝ) else 0) =ᶠ[𝓝[>] (1 : ℝ)] fun _ => 1 := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      have hr' : (1 : ℝ) < r := hr
      simp [hr']
    have h1 : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[>] (1 : ℝ)) (𝓝 0) :=
      Tendsto.congr' heq ht
    have h2 := tendsto_nhds_unique (tendsto_const_nhds (x := (1 : ℝ))) h1
    norm_num at h2

end PercLib.CriticalLRP

/-! ## Axiom audit -/

open PercLib.CriticalLRP

#print axioms posCyl

#print axioms CylinderOpen

#print axioms horizon

#print axioms patternConf

#print axioms horizonObs

#print axioms isIncreasing_posCyl

#print axioms measurableSet_posCyl

#print axioms mem_posCyl'

#print axioms cylinderOpen_isIncreasing

#print axioms horizon_subset

#print axioms horizon_mono

#print axioms mem_horizon_iff

#print axioms subset_horizon_of_witness

#print axioms iUnion_horizon_eq

#print axioms measurableSet_horizon

#print axioms mem_patternConf

#print axioms patternConf_restrict

#print axioms horizon_determined

#print axioms horizon_indicator_eq

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.continuousAt_real_horizon

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_real_horizon

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.real_cutLaw_mono_radius

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.real_horizon_le

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_horizon_tail_lt

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.lowerSemicontinuous_real_cutLaw

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_nhdsLT_real_cutLaw

#print axioms continuousAt_iff_uniform_tail

#print axioms exists_cofinal_window

#print axioms cylinderOpen_connects

#print axioms PercLib.CriticalLRP.Orchestration.tendsto_nhdsLT_cutLaw_connects

#print axioms PercLib.CriticalLRP.Orchestration.continuousAt_cutLaw_connects_iff_uniform_horizon

#print axioms PercLib.CriticalLRP.Orchestration.lowerSemicontinuous_cutLaw_connects

#print axioms cylinderOpen_connects

#print axioms cylinderOpen_cluster_mem

#print axioms PercLib.CriticalLRP.cylinderOpen_preimage_forceOn

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cylinderOpen_rawOpenEvent

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cylinderOpen_rawClosedEvent

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.pivotalFlux_singleton_eq_forced

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_nhdsLT_real_rawOpenEvent

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_nhdsLT_real_rawClosedEvent

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_nhdsLT_real_pivotalFlux_singleton

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cylinderApprox_iff_continuousAt

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cylinderApprox_exclScalar_iff_continuousAt

#print axioms PercLib.CriticalLRP.cylinderOpen_touchSet

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_nhdsLT_real_touchSet

#print axioms PercLib.CriticalLRP.exists_monotone_continuous_tendsto_not_continuousAt
