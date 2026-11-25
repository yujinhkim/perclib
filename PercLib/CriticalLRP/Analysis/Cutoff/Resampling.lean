/-
# Open-coordinate resampling and cutoff-flux localisation

Independently reviewed intermediate packet from swarm `smwtvrwnn` member `m6`, direction D1A.

This proves the open-coordinate law mixture, forced-preimage bounds, local pivotal sign/support,
a standardized per-edge estimate with the explicit `1/q_e` factor, and summability of the mixed
cluster density from a finite second cutoff moment.  It does not prove the finite incident-edge
transport, density monotonicity in the radius, a summable radius-uniform per-vertex majorant, or
an unconditional cutoff-mass derivative.  Older mixed-density conditional consumers are retained
only with their domination hypotheses visible.
-/

module

public import PercLib.CriticalLRP.Analysis.Cutoff.Resampling.Defs

/-!
Resampling and per-edge flux estimates at the actual normalized cutoff law.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-! ## 1. The two-point pivotal difference: sign and support -/

/-- Forcing the single edge `e` open contains the configuration with `e` closed. -/
theorem forceOn_singleton_empty_subset (e : Sym2 M.V) (ω : Config M.V) :
    forceOn ({e} : Set (Sym2 M.V)) (∅ : Config M.V) ω
      ⊆ forceOn ({e} : Set (Sym2 M.V)) ({e} : Config M.V) ω := by
  intro a ha
  simp only [forceOn, Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff, Set.mem_singleton_iff,
    Set.mem_empty_iff_false, false_and, or_false] at ha ⊢
  exact Or.inl ha

/-- The cluster of `0` grows when the single edge `e` is forced open. -/
theorem cluster_forceOn_singleton_empty_subset (e : Sym2 M.V) (ω : Config M.V) (o : M.V) :
    cluster (forceOn ({e} : Set (Sym2 M.V)) (∅ : Config M.V) ω) o
      ⊆ cluster (forceOn ({e} : Set (Sym2 M.V)) ({e} : Config M.V) ω) o :=
  cluster_mono (forceOn_singleton_empty_subset (M := M) e ω) o

/-- The singleton two-point functional is the cluster indicator of `y`. -/
theorem sMomentTrunc_singleton_eq (y : M.V) (ω : Config M.V) :
    sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V) ω
      = (cluster ω (0 : M.V)).indicator (fun _ => (1 : ℝ)) y := by
  simp [sMomentTrunc]

/-- The pivotal difference of the singleton two-point functional, in closed form. -/
theorem flipDiff_sMomentTrunc_singleton (y : M.V) (e : Sym2 M.V) (ω : Config M.V) :
    flipDiff (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e ω
      = (cluster (forceOn ({e} : Set (Sym2 M.V)) ({e} : Config M.V) ω) (0 : M.V)).indicator
          (fun _ => (1 : ℝ)) y
        - (cluster (forceOn ({e} : Set (Sym2 M.V)) (∅ : Config M.V) ω) (0 : M.V)).indicator
          (fun _ => (1 : ℝ)) y := by
  simp [flipDiff, sMomentTrunc]

/-- The pivotal difference of the two-point functional is nonnegative: forcing one edge
open only enlarges the cluster of `0`. -/
theorem flipDiff_sMomentTrunc_singleton_nonneg (y : M.V) (e : Sym2 M.V) (ω : Config M.V) :
    0 ≤ flipDiff (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e ω := by
  classical
  have hsub := cluster_forceOn_singleton_empty_subset (M := M) e ω (0 : M.V)
  rw [flipDiff_sMomentTrunc_singleton]
  simp only [Set.indicator_apply]
  by_cases h1 : y ∈ cluster (forceOn ({e} : Set (Sym2 M.V)) ({e} : Config M.V) ω) (0 : M.V)
  · by_cases h2 : y ∈ cluster (forceOn ({e} : Set (Sym2 M.V)) (∅ : Config M.V) ω) (0 : M.V)
    · rw [ite_eq_left h1, ite_eq_left h2]; norm_num
    · rw [ite_eq_left h1, ite_eq_right h2]; norm_num
  · have h2 : y ∉ cluster (forceOn ({e} : Set (Sym2 M.V)) (∅ : Config M.V) ω) (0 : M.V) :=
      fun hh => h1 (hsub hh)
    rw [ite_eq_right h1, ite_eq_right h2]; norm_num

/-- The pivotal difference of the two-point functional is dominated by the indicator of
`y` belonging to the cluster of `0` *after* `e` is forced open, times the indicator that
`e` touches the cluster of `0`. -/
theorem flipDiff_sMomentTrunc_singleton_le (y : M.V) (e : Sym2 M.V) (ω : Config M.V) :
    flipDiff (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e ω
      ≤ (cluster (forceOn ({e} : Set (Sym2 M.V)) ({e} : Config M.V) ω) (0 : M.V)).indicator
          (fun _ => (1 : ℝ)) y
        * (touchSet ω (0 : M.V)).indicator (fun _ => (1 : ℝ)) e := by
  classical
  have hsub := cluster_forceOn_singleton_empty_subset (M := M) e ω (0 : M.V)
  by_cases ht : e ∈ touchSet ω (0 : M.V)
  · rw [Set.indicator_of_mem ht, mul_one, flipDiff_sMomentTrunc_singleton]
    simp only [Set.indicator_apply]
    by_cases h1 : y ∈ cluster (forceOn ({e} : Set (Sym2 M.V)) ({e} : Config M.V) ω) (0 : M.V)
    · by_cases h2 : y ∈ cluster (forceOn ({e} : Set (Sym2 M.V)) (∅ : Config M.V) ω) (0 : M.V)
      · rw [ite_eq_left h1, ite_eq_left h2]; norm_num
      · rw [ite_eq_left h1, ite_eq_right h2]; norm_num
    · have h2 : y ∉ cluster (forceOn ({e} : Set (Sym2 M.V)) (∅ : Config M.V) ω) (0 : M.V) :=
        fun hh => h1 (hsub hh)
      rw [ite_eq_right h1, ite_eq_right h2]; norm_num
  · rw [Set.indicator_of_notMem ht, mul_zero,
      flipDiff_eq_zero (sMomentTrunc_dep (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) ht]


/-! ## 2. The mixed two-point/cluster density at a larger cutoff -/

/-- The cluster volume is the `y`-sum of the cluster indicators. -/
theorem tsum_cluster_indicator (ω : Config M.V) :
    (∑' y : M.V, (if y ∈ cluster ω (0 : M.V) then (1 : ℝ≥0∞) else 0))
      = clusterVol ω (0 : M.V) := by
  rw [clusterVol_eq_tsum]
  exact tsum_congr fun w => by rw [Set.indicator_apply]

/-- The mixed densities are summable, with `∑'_y E_b[|K_0| 1{y ∈ K_0}] = E_b|K_0|²`. -/
theorem summable_mixedFluxDensity {b : ℝ} (h2 : M.cutMoment 2 b ≠ ⊤) :
    Summable fun y : M.V => M.mixedFluxDensity b y := by
  have hmeas : ∀ y : M.V, AEMeasurable (fun ω : Config M.V => clusterVol ω (0 : M.V) *
      (if y ∈ cluster ω (0 : M.V) then (1 : ℝ≥0∞) else 0)) (M.cutLaw b) := by
    intro y
    refine Measurable.aemeasurable ?_
    exact (measurable_clusterVol (0 : M.V)).mul
      (Measurable.ite (measurableSet_cluster_mem (0 : M.V) y) measurable_const
        measurable_const)
  have hpt : ∀ ω : Config M.V, (∑' y : M.V, clusterVol ω (0 : M.V) *
      (if y ∈ cluster ω (0 : M.V) then (1 : ℝ≥0∞) else 0)) = (clusterVol ω (0 : M.V)) ^ 2 := by
    intro ω
    rw [ENNReal.tsum_mul_left, tsum_cluster_indicator, pow_two]
  have htot : (∑' y : M.V, ∫⁻ ω : Config M.V, clusterVol ω (0 : M.V) *
      (if y ∈ cluster ω (0 : M.V) then (1 : ℝ≥0∞) else 0) ∂(M.cutLaw b))
      = M.cutMoment 2 b := by
    rw [← lintegral_tsum hmeas]
    refine lintegral_congr fun ω => ?_
    exact hpt ω
  have hne : (∑' y : M.V, ∫⁻ ω : Config M.V, clusterVol ω (0 : M.V) *
      (if y ∈ cluster ω (0 : M.V) then (1 : ℝ≥0∞) else 0) ∂(M.cutLaw b)) ≠ ⊤ := by
    rw [htot]; exact h2
  exact ENNReal.summable_toReal hne

/-- **A summable per-vertex majorant for the two-point flux, uniform on a parameter set,
from a mixed two-point domination input and finiteness of the full quadratic moment at one
larger cutoff.**

The dominated quantity is the flux of the singleton spatial moment
`1{y ∈ K_0}`, i.e. the derivative of `r ↦ M.cutTwoPoint r 0 y`, whose majorant hypothesis
`hub` is the residual input of `hasDerivAt_cutMassReal_of_summableMajorant`.

The majorant is `y ↦ 2 E_b[|K_0| 1{y ∈ K_0}]`, which is summable in `y` by
`summable_mixedFluxDensity` as soon as the *full quadratic* moment `E_b|K_0|²` at the larger
cutoff `b` is finite.  In particular the total first-moment bound `2 D χ` is not used and
cannot be used: it has no `y`-dependence. -/
theorem exists_summable_perY_fluxMajorant {I : Set ℝ} {b : ℝ}
    (hmix : ∀ (y : M.V) (r : ℝ), r ∈ I →
      |sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r|
        ≤ 2 * M.mixedFluxDensity b y)
    (h2 : M.cutMoment 2 b ≠ ⊤) :
    ∃ u : M.V → ℝ, Summable u ∧ ∀ (y : M.V) (r : ℝ), r ∈ I →
      |sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r| ≤ u y := by
  refine ⟨fun y => 2 * M.mixedFluxDensity b y, ?_, fun y r hr => hmix y r hr⟩
  exact (M.summable_mixedFluxDensity h2).mul_left 2


/-- **The model-level off-corner mass derivative, with `hub` replaced by the mixed moment
input.**

Identical to `hasDerivAt_cutMassReal_of_summableMajorant`, except that the summable
radius-uniform per-vertex majorant `u`/`hu`/`hub` is replaced by

* `h2` — finiteness of the *full quadratic* cutoff moment `E_bb|K_0|²` at the right endpoint,
* `hmix` — the mixed two-point domination of the per-vertex flux by `2 E_bb[|K_0| 1{y ∈ K_0}]`.

Both are visible, quantitative inputs about the actual cut law at a single radius `bb`; no
statement is restated as a hypothesis. -/
theorem hasDerivAt_cutMassReal_of_mixedMoment
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {a bb : ℝ} {r0 : ℝ} (hr0 : r0 ∈ Set.Ioo a bb)
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
    (hmix : ∀ (y : M.V) (r : ℝ), r ∈ Set.Ioo a bb →
      |sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r|
        ≤ 2 * M.mixedFluxDensity bb y) :
    HasDerivAt M.cutMassReal
      (∑' y : M.V,
        sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r0) r0 := by
  obtain ⟨u, hu, hub⟩ := M.exists_summable_perY_fluxMajorant (I := Set.Ioo a bb) hmix h2
  exact M.hasDerivAt_cutMassReal_of_summableMajorant S hSmono hS hr0 hoff hKd hdom hboundint
    hmeasK hmeasinf hcontinf hfin u hu hub


/-! ## 3. Localisation: where the `y`-dependence of the flux lives -/

/-- Product of two indicator functions is the indicator of the intersection. -/
theorem indicator_mul_indicator_one (s t : Set (Config M.V)) (ω : Config M.V) :
    s.indicator (fun _ => (1 : ℝ)) ω * t.indicator (fun _ => (1 : ℝ)) ω
      = (s ∩ t).indicator (fun _ => (1 : ℝ)) ω := by
  by_cases hs : ω ∈ s <;> by_cases ht : ω ∈ t <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, hs, ht]

/-- **The two-point pivot is bounded by the probability of the coupled event**: `y` is in the
cluster of `0` after `e` is forced open, and `e` touches the cluster of `0`. -/
theorem pivotalFlux_sMomentTrunc_singleton_le_real {r : ℝ} (y : M.V) (e : Sym2 M.V) :
    pivotalFlux (M.cutLaw r) (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e
      ≤ (M.cutLaw r).real
          ({ω : Config M.V | y ∈ cluster (forceOn ({e} : Set (Sym2 M.V)) ({e} : Config M.V) ω)
              (0 : M.V)} ∩ {ω : Config M.V | e ∈ touchSet ω (0 : M.V)}) := by
  have hA : MeasurableSet {ω : Config M.V | y ∈ cluster (forceOn ({e} : Set (Sym2 M.V))
      ({e} : Config M.V) ω) (0 : M.V)} :=
    (measurableSet_cluster_mem (0 : M.V) y).preimage
      (measurable_forceOn ({e} : Set (Sym2 M.V)) ({e} : Config M.V))
  have hB : MeasurableSet {ω : Config M.V | e ∈ touchSet ω (0 : M.V)} :=
    measurableSet_touchSet_mem e
  have hpt : ∀ ω : Config M.V,
      flipDiff (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e ω
        ≤ ({ω : Config M.V | y ∈ cluster (forceOn ({e} : Set (Sym2 M.V)) ({e} : Config M.V) ω)
            (0 : M.V)} ∩ {ω : Config M.V | e ∈ touchSet ω (0 : M.V)}).indicator
              (fun _ => (1 : ℝ)) ω := by
    intro ω
    rw [← indicator_mul_indicator_one]
    exact flipDiff_sMomentTrunc_singleton_le (M := M) y e ω
  rw [pivotalFlux]
  exact (integral_mono_of_nonneg
      (Eventually.of_forall fun ω => flipDiff_sMomentTrunc_singleton_nonneg (M := M) y e ω)
      ((integrable_const (1 : ℝ)).indicator (hA.inter hB))
      (Eventually.of_forall hpt)).trans_eq (integral_indicator_one (hA.inter hB))

/-- **Exact localisation of the `y`-dependence of the two-point flux.**

The flux of `1{y ∈ K_0}` through the singleton `{y}` is bounded by the sum over edges of the
edge weight times the probability of the *coupled* event "`y` is in the cluster of `0` after `e`
is forced open **and** `e` touches the cluster of `0`".  The `y`-dependence therefore enters
through the cluster of `0` at the forced-open configuration, not at the underlying one.

Rewriting it as a two-point function is the standardisation step: forcing a single edge open
reweights the law by the factor `1/q_e(r)`, so the bound produced by this localisation is
`P(y ∈ K_0 after forcing e open) ≤ P_r(y ∈ K_0)/q_e(r)`, and the theorem below requires no
such reweighting.  All inputs here are unconditional (edge-weight positivity and absolute
summability of the edge series). -/
theorem abs_sMomentInfFlux_le_localised {r : ℝ} (y : M.V)
    (hpos : ∀ e : Sym2 M.V, 0 ≤ M.cutEdgeDeriv r e)
    (hdom : Summable fun e : Sym2 M.V => |M.cutEdgeDeriv r e| *
      (2 * (M.cutLaw r).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)})) :
    |sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ)) M.cutProb
        M.cutEdgeDeriv r|
      ≤ ∑' e : Sym2 M.V, M.cutEdgeDeriv r e *
          (M.cutLaw r).real
            ({ω : Config M.V | y ∈ cluster (forceOn ({e} : Set (Sym2 M.V))
                ({e} : Config M.V) ω) (0 : M.V)} ∩
              {ω : Config M.V | e ∈ touchSet ω (0 : M.V)}) := by
  have hflux : sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ)) M.cutProb
      M.cutEdgeDeriv r
      = ∑' e : Sym2 M.V, M.cutEdgeDeriv r e *
          pivotalFlux (M.cutLaw r)
            (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e := by
    simp only [sMomentInfFlux, infFluxOf]
    rw [M.cutLaw_eq_edgeMeasure r]
  have hterm : ∀ e : Sym2 M.V,
      |M.cutEdgeDeriv r e * pivotalFlux (M.cutLaw r)
          (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e|
        ≤ M.cutEdgeDeriv r e * (M.cutLaw r).real
            ({ω : Config M.V | y ∈ cluster (forceOn ({e} : Set (Sym2 M.V))
                ({e} : Config M.V) ω) (0 : M.V)} ∩
              {ω : Config M.V | e ∈ touchSet ω (0 : M.V)}) := by
    intro e
    have hnonneg : 0 ≤ pivotalFlux (M.cutLaw r)
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e := by
      rw [pivotalFlux]
      exact integral_nonneg fun ω => flipDiff_sMomentTrunc_singleton_nonneg (M := M) y e ω
    rw [abs_mul, abs_of_nonneg (hpos e), abs_of_nonneg hnonneg]
    exact mul_le_mul_of_nonneg_left
      (pivotalFlux_sMomentTrunc_singleton_le_real (M := M) y e) (hpos e)
  have hrhs : Summable fun e : Sym2 M.V => M.cutEdgeDeriv r e * (M.cutLaw r).real
      ({ω : Config M.V | y ∈ cluster (forceOn ({e} : Set (Sym2 M.V))
          ({e} : Config M.V) ω) (0 : M.V)} ∩
        {ω : Config M.V | e ∈ touchSet ω (0 : M.V)}) := by
    refine Summable.of_nonneg_of_le
      (fun e => mul_nonneg (hpos e) ENNReal.toReal_nonneg) (fun e => ?_) hdom
    have hsub : (M.cutLaw r).real
        ({ω : Config M.V | y ∈ cluster (forceOn ({e} : Set (Sym2 M.V))
            ({e} : Config M.V) ω) (0 : M.V)} ∩
          {ω : Config M.V | e ∈ touchSet ω (0 : M.V)})
        ≤ (M.cutLaw r).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)} :=
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono Set.inter_subset_right)
    have hb : (0 : ℝ) ≤ (M.cutLaw r).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)} :=
      ENNReal.toReal_nonneg
    calc M.cutEdgeDeriv r e * (M.cutLaw r).real
          ({ω : Config M.V | y ∈ cluster (forceOn ({e} : Set (Sym2 M.V))
              ({e} : Config M.V) ω) (0 : M.V)} ∩
            {ω : Config M.V | e ∈ touchSet ω (0 : M.V)})
        ≤ M.cutEdgeDeriv r e * (M.cutLaw r).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)} :=
          mul_le_mul_of_nonneg_left hsub (hpos e)
      _ ≤ |M.cutEdgeDeriv r e| *
            (2 * (M.cutLaw r).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)}) := by
          rw [abs_of_nonneg (hpos e)]
          exact mul_le_mul_of_nonneg_left (by linarith) (hpos e)
  have habs : Summable fun e : Sym2 M.V =>
      |M.cutEdgeDeriv r e * pivotalFlux (M.cutLaw r)
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e| :=
    Summable.of_nonneg_of_le (fun e => abs_nonneg _) hterm hrhs
  have habs' : Summable fun e : Sym2 M.V =>
      ‖M.cutEdgeDeriv r e * pivotalFlux (M.cutLaw r)
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e‖ := by
    simpa only [Real.norm_eq_abs] using habs
  rw [hflux]
  refine (norm_tsum_le_tsum_norm habs').trans ?_
  simpa only [Real.norm_eq_abs] using habs.tsum_le_tsum hterm hrhs


/-! ## 4. No `y`-free majorant is summable on the infinite vertex set -/

/-- The vertex set `Fin d → ℤ` of the source model is infinite. -/
theorem infinite_vertex : Infinite M.V := by
  have hd : 0 < M.d := M.hd
  let i0 : Fin M.d := ⟨0, hd⟩
  let emb : ℕ → M.V := fun n i => if i = i0 then (n : ℤ) else 0
  have hinj : Function.Injective emb := by
    intro m n h
    have h0 := congrFun h i0
    simpa [emb, i0] using h0
  exact Infinite.of_injective emb hinj

/-- A function on an infinite type which is bounded below by a positive constant is not
summable.  Consequently a majorant that is uniform not only in the radius but also in `y` can
never satisfy `Summable u`. -/
theorem not_summable_of_const_le' {α : Type*} [Infinite α] {u : α → ℝ} {c : ℝ} (hc : 0 < c)
    (hu : ∀ y : α, c ≤ u y) : ¬ Summable u := by
  classical
  intro hsum
  let emb : ℕ ↪ α := Infinite.natEmbedding α
  have hle : ∀ n : ℕ, (n : ℝ) * c ≤ ∑' y : α, u y := by
    intro n
    have hsum' : (∑ y ∈ (Finset.range n).image emb, u y)
        = ∑ i ∈ Finset.range n, u (emb i) :=
      Finset.sum_image (fun x _ y _ h => emb.injective h)
    have hlower : (n : ℝ) * c ≤ ∑ y ∈ (Finset.range n).image emb, u y := by
      rw [hsum']
      calc (n : ℝ) * c = ∑ _i ∈ Finset.range n, c := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ ≤ ∑ i ∈ Finset.range n, u (emb i) :=
              Finset.sum_le_sum (fun i _ => hu (emb i))
    exact hlower.trans (hsum.sum_le_tsum _ (fun i _ => le_trans hc.le (hu i)))
  obtain ⟨n, hn⟩ := exists_nat_gt ((∑' y : α, u y) / c)
  have hn' : (∑' y : α, u y) < (n : ℝ) * c := by
    rw [div_lt_iff₀ hc] at hn
    linarith
  have := hle n
  linarith

/-- The vertex-set form of `not_summable_of_const_le'`. -/
theorem not_summable_of_const_le {u : M.V → ℝ} {c : ℝ} (hc : 0 < c)
    (hu : ∀ y : M.V, c ≤ u y) : ¬ Summable u :=
  @not_summable_of_const_le' M.V M.infinite_vertex u c hc hu

/-- The pinned per-vertex dominator of `tsum_abs_weight_touch_le` is independent of `y` when
specialised to the singleton `{y}` with unit weight: it only sees `∑_{x ∈ {y}} |1| = 1`. -/
theorem sMomentWeight_singleton_indep (π : ℝ → Sym2 M.V → unitInterval)
    (c : ℝ → Sym2 M.V → ℝ) (r : ℝ) (y y' : M.V) :
    sMomentWeight (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ)) π c r
      = sMomentWeight (0 : M.V) ({y'} : Finset M.V) (fun _ => (1 : ℝ)) π c r := by
  simp [sMomentWeight]

/-- A positive constant majorant on the infinite vertex set is not summable; hence the total
pivotal mass `2 D χ`, which carries no `y`-dependence, cannot be the sought-for `u`. -/
theorem not_summable_const_of_pos {C : ℝ} (hC : 0 < C) :
    ¬ Summable fun _ : M.V => C :=
  not_summable_of_const_le (M := M) hC (fun _ => le_rfl)

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## 5. The per-radius total-mass bound does not give a uniform majorant -/

/-- **A monotone family with convergent `y`-series at every radius but no summable
`r`-uniform majorant.**

`g y r = 1{r ≥ 1 - 1/(y+1)}` is nonnegative, monotone in `r`, bounded by `1`, and summable in
`y` at every radius `r < 1` (only finitely many `y` contribute, because `1 - 1/(y+1) ↑ 1`),
but every `y` contributes at `r = 1`, so there is no summable majorant uniform in `r`.

Hence "the `y`-series converges at each radius" together with monotonicity in the radius does
not produce the radius-uniform majorant `hub`: the uniformity on the parameter window is a
genuinely separate input, and it is exactly what the mixed-moment domination supplies. -/
theorem no_uniform_majorant_of_per_radius_mass :
    ∃ g : ℕ → ℝ → ℝ,
      (∀ y r, 0 ≤ g y r) ∧
      (∀ y, Monotone (g y)) ∧
      (∀ r : ℝ, r < 1 → Summable fun y => g y r) ∧
      (∀ y r, g y r ≤ 1) ∧
      (∀ y, g y 1 = 1) ∧
      ¬ ∃ u : ℕ → ℝ, Summable u ∧ ∀ y r, g y r ≤ u y := by
  classical
  set g : ℕ → ℝ → ℝ := fun y r => if 1 - 1 / ((y : ℝ) + 1) ≤ r then (1 : ℝ) else 0 with hg
  have hnonneg : ∀ y r, 0 ≤ g y r := by
    intro y r
    simp only [hg]
    split_ifs <;> norm_num
  have hmono : ∀ y, Monotone (g y) := by
    intro y r r' hrr
    simp only [hg]
    by_cases h : 1 - 1 / ((y : ℝ) + 1) ≤ r
    · rw [ite_eq_left h, ite_eq_left (le_trans h hrr)]
    · rw [ite_eq_right h]
      split_ifs <;> norm_num
  have hsum : ∀ r : ℝ, r < 1 → Summable fun y => g y r := by
    intro r hr
    have hpos : (0 : ℝ) < 1 - r := by linarith
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / (1 - r))
    refine summable_of_ne_finset_zero (s := Finset.range N) (fun y hy => ?_)
    have hyN : (N : ℝ) ≤ (y : ℝ) := by
      have hNy : N ≤ y := by simpa only [Finset.mem_range, not_lt] using hy
      exact_mod_cast hNy
    have hlt : 1 / ((y : ℝ) + 1) < 1 - r := by
      have h2 : 1 / (1 - r) < (y : ℝ) + 1 := lt_of_lt_of_le hN (by linarith)
      rw [div_lt_iff₀ hpos] at h2
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (y : ℝ) + 1)]
      simpa [mul_comm] using h2
    simp only [hg]
    exact ite_eq_right (by linarith : ¬ (1 - 1 / ((y : ℝ) + 1) ≤ r))
  have hle1 : ∀ y r, g y r ≤ 1 := by
    intro y r
    simp only [hg]
    split_ifs <;> norm_num
  have hone : ∀ y, g y 1 = 1 := by
    intro y
    simp only [hg]
    exact ite_eq_left (by
      have h2 : (0 : ℝ) < 1 / ((y : ℝ) + 1) := by positivity
      linarith)
  refine ⟨g, hnonneg, hmono, hsum, hle1, hone, ?_⟩
  rintro ⟨u, hu, hbound⟩
  have h1 : ∀ y : ℕ, (1 : ℝ) ≤ u y := by
    intro y
    have hb := hbound y 1
    rwa [hone y] at hb
  exact PercLib.CriticalLRP.Orchestration.SourceModelData.not_summable_of_const_le'
    (α := ℕ) one_pos h1 hu

/-! ## 6. The open-coordinate resampling identity

`edgeMeasure π` is the image of `edgeMeasure π × edgeMeasure π` under `forceOn {e}`
(`edgeMeasure_map_forceOn`).  Reading the `e`-coordinate from the source copy and the others from
the base copy makes the inner integral a two-valued sum, which gives the **mixture identity**

  `μ(F) = q_e · μ(F after forcing e open) + (1-q_e) · μ(F after forcing e closed)`,

`q_e = μ{e open}`.  Consequences: `μ(F after forcing e open) ≤ μ(F)/q_e`, which is the
standardisation that converts the pivotal flux of the two-point function into the two-point
function.  The factor `1/q_e` cannot be dropped, since forcing `e` open raises connectivity.
-/

namespace PercLib.CriticalLRP

variable {V : Type*} [Countable V]

/-- The state of `e` in `forceOn {e} η ω` is read from `η`, the other coordinates from `ω`. -/
theorem mem_forceOn_singleton (e : Sym2 V) (η ω : Config V) (e' : Sym2 V) :
    (e' ∈ forceOn ({e} : Set (Sym2 V)) η ω) ↔ (e' = e → e' ∈ η) ∧ (e' ≠ e → e' ∈ ω) := by
  change forceOn ({e} : Set (Sym2 V)) η ω e' ↔ (e' = e → e' ∈ η) ∧ (e' ≠ e → e' ∈ ω)
  rw [forceOn_apply]
  simp only [Set.mem_singleton_iff]
  tauto

/-- `forceOn {e} ω η` is `η` with the state of `e` taken from `ω`. -/
theorem forceOn_singleton_eq_ite (e : Sym2 V) (η ω : Config V) :
    forceOn ({e} : Set (Sym2 V)) ω η
      = if e ∈ ω then forceOn ({e} : Set (Sym2 V)) ({e} : Config V) η
        else forceOn ({e} : Set (Sym2 V)) (∅ : Config V) η := by
  ext e'
  by_cases he : e ∈ ω
  · rw [ite_eq_left he]
    by_cases h : e' = e
    · rw [h, mem_forceOn_singleton, mem_forceOn_singleton]
      simp [he]
    · rw [mem_forceOn_singleton, mem_forceOn_singleton]
      simp [h]
  · rw [ite_eq_right he]
    by_cases h : e' = e
    · rw [h, mem_forceOn_singleton, mem_forceOn_singleton]
      simp [he]
    · rw [mem_forceOn_singleton, mem_forceOn_singleton]
      simp [h]

/-- A function of a single open coordinate takes exactly two values. -/
theorem lintegral_ite_mem (π : Sym2 V → unitInterval) (e : Sym2 V) (a b : ℝ≥0∞) :
    ∫⁻ ω, (if e ∈ ω then a else b) ∂(edgeMeasure π)
      = a * (edgeMeasure π) {ω : Config V | e ∈ ω}
        + b * (edgeMeasure π) {ω : Config V | e ∉ ω} := by
  classical
  have hA : MeasurableSet {ω : Config V | e ∈ ω} := measurableSet_mem e
  have hpt : ∀ ω : Config V, (if e ∈ ω then a else b)
      = a * ({ω : Config V | e ∈ ω}.indicator (fun _ => (1 : ℝ≥0∞)) ω)
        + b * ({ω : Config V | e ∉ ω}.indicator (fun _ => (1 : ℝ≥0∞)) ω) := by
    intro ω
    by_cases he : e ∈ ω <;> simp [he]
  simp_rw [hpt]
  have hf : Measurable fun ω : Config V =>
      a * ({ω : Config V | e ∈ ω}.indicator (fun _ => (1 : ℝ≥0∞)) ω) :=
    Measurable.const_mul (measurable_const.indicator hA) a
  rw [lintegral_add_left hf,
    lintegral_const_mul a (measurable_const.indicator hA),
    lintegral_const_mul b (measurable_const.indicator (s := {ω : Config V | e ∉ ω}) hA.compl),
    lintegral_indicator_const hA, lintegral_indicator_const
      (s := {ω : Config V | e ∉ ω}) hA.compl]
  simp

end PercLib.CriticalLRP

/-! ### The mixture identity -/

namespace PercLib.CriticalLRP

variable {V : Type*} [Countable V]

/-- **Mixture identity for the single-edge resampling.** -/
theorem lintegral_forceOn_mix (π : Sym2 V → unitInterval) (e : Sym2 V)
    {F : Config V → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ ω, F ω ∂(edgeMeasure π)
      = (∫⁻ ω, F (forceOn ({e} : Set (Sym2 V)) ({e} : Config V) ω) ∂(edgeMeasure π))
          * (edgeMeasure π) {ω : Config V | e ∈ ω}
        + (∫⁻ ω, F (forceOn ({e} : Set (Sym2 V)) (∅ : Config V) ω) ∂(edgeMeasure π))
          * (edgeMeasure π) {ω : Config V | e ∉ ω} := by
  classical
  have hm : edgeMeasure π
      = ((edgeMeasure π).prod (edgeMeasure π)).map
          (fun p : Config V × Config V => forceOn ({e} : Set (Sym2 V)) p.1 p.2) :=
    (edgeMeasure_map_forceOn π {e}).symm
  have hmeas : Measurable fun p : Config V × Config V =>
      forceOn ({e} : Set (Sym2 V)) p.1 p.2 := measurable_forceOn_pair {e}
  have hcomp : Measurable fun p : Config V × Config V =>
      F (forceOn ({e} : Set (Sym2 V)) p.1 p.2) := hF.comp hmeas
  have hstep : ∀ η : Config V,
      (∫⁻ ω, F (forceOn ({e} : Set (Sym2 V)) ω η) ∂(edgeMeasure π))
        = F (forceOn ({e} : Set (Sym2 V)) ({e} : Config V) η)
            * (edgeMeasure π) {ω : Config V | e ∈ ω}
          + F (forceOn ({e} : Set (Sym2 V)) (∅ : Config V) η)
            * (edgeMeasure π) {ω : Config V | e ∉ ω} := by
    intro η
    have hpt : ∀ ω : Config V, F (forceOn ({e} : Set (Sym2 V)) ω η)
        = if e ∈ ω then F (forceOn ({e} : Set (Sym2 V)) ({e} : Config V) η)
          else F (forceOn ({e} : Set (Sym2 V)) (∅ : Config V) η) := by
      intro ω
      rw [forceOn_singleton_eq_ite]
      by_cases he : e ∈ ω
      · rw [ite_eq_left he, ite_eq_left he]
      · rw [ite_eq_right he, ite_eq_right he]
    rw [show (∫⁻ ω, F (forceOn ({e} : Set (Sym2 V)) ω η) ∂(edgeMeasure π))
        = ∫⁻ ω, (if e ∈ ω then F (forceOn ({e} : Set (Sym2 V)) ({e} : Config V) η)
            else F (forceOn ({e} : Set (Sym2 V)) (∅ : Config V) η)) ∂(edgeMeasure π) from
      lintegral_congr fun ω => hpt ω]
    exact lintegral_ite_mem (V := V) π e _ _
  calc ∫⁻ ω, F ω ∂(edgeMeasure π)
      = ∫⁻ p : Config V × Config V, F (forceOn ({e} : Set (Sym2 V)) p.1 p.2)
          ∂(((edgeMeasure π).prod (edgeMeasure π))) := by
        conv_lhs => rw [hm]
        exact lintegral_map hF hmeas
    _ = ∫⁻ η, ∫⁻ ω, F (forceOn ({e} : Set (Sym2 V)) ω η)
          ∂(edgeMeasure π) ∂(edgeMeasure π) := by
        rw [lintegral_prod_symm _ hcomp.aemeasurable]
    _ = ∫⁻ η, (F (forceOn ({e} : Set (Sym2 V)) ({e} : Config V) η)
            * (edgeMeasure π) {ω : Config V | e ∈ ω}
          + F (forceOn ({e} : Set (Sym2 V)) (∅ : Config V) η)
            * (edgeMeasure π) {ω : Config V | e ∉ ω}) ∂(edgeMeasure π) :=
        lintegral_congr fun η => hstep η
    _ = (∫⁻ ω, F (forceOn ({e} : Set (Sym2 V)) ({e} : Config V) ω) ∂(edgeMeasure π))
          * (edgeMeasure π) {ω : Config V | e ∈ ω}
        + (∫⁻ ω, F (forceOn ({e} : Set (Sym2 V)) (∅ : Config V) ω) ∂(edgeMeasure π))
          * (edgeMeasure π) {ω : Config V | e ∉ ω} := by
        rw [lintegral_add_left (f := fun η : Config V => F (forceOn ({e} : Set (Sym2 V))
            ({e} : Config V) η) * (edgeMeasure π) {ω : Config V | e ∈ ω})
          (g := fun η : Config V => F (forceOn ({e} : Set (Sym2 V)) (∅ : Config V) η)
            * (edgeMeasure π) {ω : Config V | e ∉ ω})
          ((hF.comp (measurable_forceOn _ _)).mul_const _),
          lintegral_mul_const (f := fun ω : Config V =>
            F (forceOn ({e} : Set (Sym2 V)) ({e} : Config V) ω)) _
            (hF.comp (measurable_forceOn _ _)),
          lintegral_mul_const (f := fun ω : Config V =>
            F (forceOn ({e} : Set (Sym2 V)) (∅ : Config V) ω)) _
            (hF.comp (measurable_forceOn _ _))]

/-- The indicator of `S` composed with the resampling map is the indicator of the preimage. -/
theorem indicator_comp_forceOn (e : Sym2 V) (S : Set (Config V)) (σ : Config V) :
    (fun ω : Config V => S.indicator (fun _ => (1 : ℝ≥0∞))
        (forceOn ({e} : Set (Sym2 V)) σ ω))
      = ((forceOn ({e} : Set (Sym2 V)) σ) ⁻¹' S).indicator (fun _ => (1 : ℝ≥0∞)) := by
  funext ω
  by_cases h : forceOn ({e} : Set (Sym2 V)) σ ω ∈ S
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (Set.mem_preimage.mpr h)]
  · rw [Set.indicator_of_notMem h,
      Set.indicator_of_notMem (fun hh => h (Set.mem_preimage.mp hh))]

/-- **The standardised bound**: the probability of an event after forcing `e` open, weighted by
`q_e = μ{e open}`, is at most its probability under `μ`. -/
theorem measure_preimage_forceOn_le_div (π : Sym2 V → unitInterval) (e : Sym2 V)
    {S : Set (Config V)} (hS : MeasurableSet S) :
    (edgeMeasure π) ((forceOn ({e} : Set (Sym2 V)) ({e} : Config V)) ⁻¹' S)
        * (edgeMeasure π) {ω : Config V | e ∈ ω} ≤ (edgeMeasure π) S := by
  have hmix := lintegral_forceOn_mix (V := V) π e
    (F := S.indicator (fun _ => (1 : ℝ≥0∞))) (measurable_const.indicator hS)
  have h₁ : (∫⁻ ω, S.indicator (fun _ => (1 : ℝ≥0∞))
        (forceOn ({e} : Set (Sym2 V)) ({e} : Config V) ω) ∂(edgeMeasure π))
      = (edgeMeasure π) ((forceOn ({e} : Set (Sym2 V)) ({e} : Config V)) ⁻¹' S) := by
    rw [indicator_comp_forceOn (V := V) e S ({e} : Config V),
      lintegral_indicator_const (hS.preimage (measurable_forceOn _ _)), one_mul]
  have h₀ : (∫⁻ ω, S.indicator (fun _ => (1 : ℝ≥0∞))
        (forceOn ({e} : Set (Sym2 V)) (∅ : Config V) ω) ∂(edgeMeasure π))
      = (edgeMeasure π) ((forceOn ({e} : Set (Sym2 V)) (∅ : Config V)) ⁻¹' S) := by
    rw [indicator_comp_forceOn (V := V) e S (∅ : Config V),
      lintegral_indicator_const (hS.preimage (measurable_forceOn _ _)), one_mul]
  rw [lintegral_indicator_const hS, one_mul, h₁, h₀] at hmix
  rw [hmix]
  exact le_add_right le_rfl

end PercLib.CriticalLRP

/-! ## 7. The standardised weight and the per-edge two-point bound -/

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

theorem openProb_le_one (r : ℝ) (e : Sym2 M.V) : M.openProb r e ≤ 1 := by
  rw [openProb]
  calc (M.cutLaw r).real {ω : Config M.V | e ∈ ω}
      ≤ (M.cutLaw r).real Set.univ :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.subset_univ _))
    _ = 1 := by rw [Measure.real, measure_univ, ENNReal.toReal_one]

/-- Real form of the standardised resampling bound. -/
theorem openProb_mul_real_preimage_le {r : ℝ} (e : Sym2 M.V) {S : Set (Config M.V)}
    (hS : MeasurableSet S) :
    M.openProb r e
        * (M.cutLaw r).real ((forceOn ({e} : Set (Sym2 M.V)) ({e} : Config M.V)) ⁻¹' S)
      ≤ (M.cutLaw r).real S := by
  have h := measure_preimage_forceOn_le_div (V := M.V) (M.cutProb r) e hS
  rw [← M.cutLaw_eq_edgeMeasure r] at h
  calc M.openProb r e
        * (M.cutLaw r).real ((forceOn ({e} : Set (Sym2 M.V)) ({e} : Config M.V)) ⁻¹' S)
      = (((M.cutLaw r) ((forceOn ({e} : Set (Sym2 M.V)) ({e} : Config M.V)) ⁻¹' S))
          * ((M.cutLaw r) {ω : Config M.V | e ∈ ω})).toReal := by
        rw [ENNReal.toReal_mul, mul_comm]
        rfl
    _ ≤ ((M.cutLaw r) S).toReal := ENNReal.toReal_mono (measure_ne_top _ _) h
    _ = (M.cutLaw r).real S := rfl

/-- **Per-edge standardisation of the two-point pivotal flux**: the cut-off edge weight times the
pivotal flux of `1{y ∈ K_0}` is at most the standardised weight `c_r(e)/q_e(r)` times the
probability of the coupled event `{y ∈ K_0} ∩ {e touches K_0}`. -/
theorem cutEdgeDeriv_mul_pivotalFlux_le {r : ℝ} {y : M.V} {e : Sym2 M.V}
    (hpos : 0 ≤ M.cutEdgeDeriv r e) (hq : 0 < M.openProb r e) :
    M.cutEdgeDeriv r e
        * pivotalFlux (M.cutLaw r) (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e
      ≤ M.stdEdgeWeight r e * (M.cutLaw r).real
          ({ω : Config M.V | y ∈ cluster ω (0 : M.V)}
            ∩ {ω : Config M.V | e ∈ touchSet ω (0 : M.V)}) := by
  classical
  set S : Set (Config M.V) := {ω : Config M.V | y ∈ cluster ω (0 : M.V)}
    ∩ {ω : Config M.V | e ∈ touchSet ω (0 : M.V)} with hSdef
  have hS : MeasurableSet S :=
    (measurableSet_cluster_mem (0 : M.V) y).inter (measurableSet_touchSet_mem e)
  have hpre : MeasurableSet ((forceOn ({e} : Set (Sym2 M.V)) ({e} : Config M.V)) ⁻¹' S) :=
    hS.preimage (measurable_forceOn _ _)
  have hsupport : ∀ ω : Config M.V,
      flipDiff (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e ω
        ≤ ((forceOn ({e} : Set (Sym2 M.V)) ({e} : Config M.V)) ⁻¹' S).indicator
            (fun _ => (1 : ℝ)) ω := by
    intro ω
    have h := flipDiff_sMomentTrunc_singleton_le (M := M) y e ω
    have hsub : touchSet ω (0 : M.V)
        ⊆ touchSet (forceOn ({e} : Set (Sym2 M.V)) ({e} : Config M.V) ω) (0 : M.V) := by
      intro e' he'
      obtain ⟨v, hv, hcv⟩ := mem_touchSet.mp he'
      have hbase : ∀ e' : Sym2 M.V, e' ∈ ω →
          e' ∈ forceOn ({e} : Set (Sym2 M.V)) ({e} : Config M.V) ω := by
        intro e' he'
        simp only [forceOn, Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff, Set.mem_singleton_iff]
        by_cases h : e' = e
        · exact Or.inr ⟨h, h⟩
        · exact Or.inl ⟨he', h⟩
      exact mem_touchSet.mpr ⟨v, hv, cluster_mono hbase (0 : M.V) hcv⟩
    have hnn : (0 : ℝ) ≤ ((forceOn ({e} : Set (Sym2 M.V)) ({e} : Config M.V)) ⁻¹' S).indicator
        (fun _ => (1 : ℝ)) ω := Set.indicator_nonneg (fun _ => by norm_num) ω
    by_cases hy : y ∈ cluster (forceOn ({e} : Set (Sym2 M.V)) ({e} : Config M.V) ω) (0 : M.V)
    · by_cases ht : e ∈ touchSet ω (0 : M.V)
      · have hmem : ω ∈ (forceOn ({e} : Set (Sym2 M.V)) ({e} : Config M.V)) ⁻¹' S := by
          rw [Set.mem_preimage, hSdef, Set.mem_inter_iff]
          exact ⟨hy, hsub ht⟩
        rw [Set.indicator_of_mem hmem]
        rw [Set.indicator_of_mem hy, Set.indicator_of_mem ht, mul_one] at h
        linarith
      · rw [Set.indicator_of_notMem ht, mul_zero] at h
        linarith
    · rw [Set.indicator_of_notMem hy, zero_mul] at h
      linarith
  have hpiv_nodiv : pivotalFlux (M.cutLaw r)
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e
      ≤ (M.cutLaw r).real ((forceOn ({e} : Set (Sym2 M.V)) ({e} : Config M.V)) ⁻¹' S) := by
    rw [pivotalFlux]
    calc ∫ ω, flipDiff (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e ω
          ∂(M.cutLaw r)
        ≤ ∫ ω, ((forceOn ({e} : Set (Sym2 M.V)) ({e} : Config M.V)) ⁻¹' S).indicator
            (fun _ => (1 : ℝ)) ω ∂(M.cutLaw r) :=
          integral_mono_of_nonneg
            (Eventually.of_forall fun ω => flipDiff_sMomentTrunc_singleton_nonneg (M := M) y e ω)
            ((integrable_const (1 : ℝ)).indicator hpre) (Eventually.of_forall hsupport)
      _ = (M.cutLaw r).real ((forceOn ({e} : Set (Sym2 M.V)) ({e} : Config M.V)) ⁻¹' S) :=
          integral_indicator_one hpre
  have hq_piv : M.openProb r e * pivotalFlux (M.cutLaw r)
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e
      ≤ (M.cutLaw r).real S := by
    have h1 : M.openProb r e * pivotalFlux (M.cutLaw r)
          (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e
        ≤ M.openProb r e * (M.cutLaw r).real
            ((forceOn ({e} : Set (Sym2 M.V)) ({e} : Config M.V)) ⁻¹' S) :=
      mul_le_mul_of_nonneg_left hpiv_nodiv ENNReal.toReal_nonneg
    have h2 := openProb_mul_real_preimage_le (M := M) (r := r) e hS
    linarith
  have hpiv' : pivotalFlux (M.cutLaw r)
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e
      ≤ (M.cutLaw r).real S / M.openProb r e := by
    rw [le_div_iff₀ hq,
      mul_comm (pivotalFlux (M.cutLaw r)
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e) (M.openProb r e)]
    exact hq_piv
  calc M.cutEdgeDeriv r e
        * pivotalFlux (M.cutLaw r) (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e
      ≤ M.cutEdgeDeriv r e * ((M.cutLaw r).real S / M.openProb r e) :=
        mul_le_mul_of_nonneg_left hpiv' hpos
    _ = M.stdEdgeWeight r e * (M.cutLaw r).real S := by
        rw [stdEdgeWeight]; ring

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## 8. Axiom audit

The `#print axioms` commands below are part of this file so that a single compile audits every
result.  Only `propext`, `Classical.choice` and `Quot.sound` may appear. -/

set_option linter.hashCommand false
set_option linter.style.longLine false

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.forceOn_singleton_empty_subset
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cluster_forceOn_singleton_empty_subset
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.sMomentTrunc_singleton_eq
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.flipDiff_sMomentTrunc_singleton
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.flipDiff_sMomentTrunc_singleton_nonneg
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.flipDiff_sMomentTrunc_singleton_le
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tsum_cluster_indicator
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.summable_mixedFluxDensity
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.exists_summable_perY_fluxMajorant
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.hasDerivAt_cutMassReal_of_mixedMoment
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.indicator_mul_indicator_one
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.pivotalFlux_sMomentTrunc_singleton_le_real
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.abs_sMomentInfFlux_le_localised
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.infinite_vertex
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.not_summable_of_const_le'
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.not_summable_of_const_le
#print axioms no_uniform_majorant_of_per_radius_mass
#print axioms PercLib.CriticalLRP.mem_forceOn_singleton
#print axioms PercLib.CriticalLRP.forceOn_singleton_eq_ite
#print axioms PercLib.CriticalLRP.lintegral_ite_mem
#print axioms PercLib.CriticalLRP.lintegral_forceOn_mix
#print axioms PercLib.CriticalLRP.indicator_comp_forceOn
#print axioms PercLib.CriticalLRP.measure_preimage_forceOn_le_div
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.openProb
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.stdEdgeWeight
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.openProb_le_one
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.openProb_mul_real_preimage_le
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.cutEdgeDeriv_mul_pivotalFlux_le

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.sMomentWeight_singleton_indep
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.not_summable_const_of_pos
