/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Infinite-volume (`r`-)derivative exchange for the *spatial* cluster moment

Swarm `smwh9j4uh`, member `m3`, direction (G): countable / infinite-volume spatial-moment
derivative exchange.

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.5.8 (TeX `lem:gyration_derivative2`, lines 2749--2885 of
`.scratch/i52/source/Zd_renormalizationHD.tex`), first display of the proof:

  `d/dr E_r[∑_{x∈K}⟨x,u⟩²] = β_c|J'(r)| · E_r[∑_{x∈K} ∑_{y∈B_r(x)} 1(y∉K) ∑_{z∈K_y} ⟨z,u⟩²]`

The repository already has the *finite-graph* derivative identity for the spatial moment
(`VolumeMoments/SpatialPivot`, `VolumeMoments/QuadraticMerge`, general finite graph) and the
infinite-volume pivot/flux exchange for the *cluster cardinality* (`RussoInf/Exchange`,
`cappedClusterVol`).  What neither has is the infinite-volume exchange for the spatially
weighted cluster moment `∑_{x ∈ K_o} q x`, which is the object that Lemma I.5.8 differentiates.

What this file proves (sorry-free, no new axioms):

1. `sMomentTrunc` — the truncated spatial moment `∑_{x ∈ K_o ∩ A} q x` on a finite vertex set
   `A` (the paper's `∑_{x∈K∩B_r}` in the case `A = B_r`), with nonnegativity, the sup bound,
   measurability, dependence on `K_o` only, monotonicity in `A`, and the identification with
   the filtered sum over `K_o ∩ A`.

2. `tendsto_sMomentTrunc_cutConfig`, `tendsto_integral_sMomentTrunc` — along any edge-exhausting
   window sequence, the truncated spatial moment of the truncated configuration converges
   pointwise (hence in expectation) to that of the full configuration.  Since `q` is unbounded,
   the domination is by the *finite* constant `∑_{x ∈ A}|q x|`, which is what makes the quadratic
   weight admissible (contrast: `Exchange` dominates `cappedClusterVol` by its cap `m`).

3. `tendsto_integral_cutFun_of_bound` and `hasDerivAt_integral_clusterFun` — the exchange theorem
   for a **general** bounded, measurable, cluster-dependent functional `g`, generalising
   `hasDerivAt_integral_cappedClusterVol` from the capped cluster volume to an arbitrary such `g`.

4. `hasDerivAt_integral_sMomentTrunc`, `hasDerivAt_integral_sMomentTrunc_of_sharpness`,
   `hasDerivAt_integral_sMomentTrunc_cutoff` — the infinite-volume Russo formula for the
   truncated spatial moment: the `r`-derivative of `r ↦ ∫ sMomentTrunc q o A ∂P_r` is the
   infinite pivotal flux of `sMomentTrunc q o A`.  In `_of_sharpness` the flux domination is
   *discharged* from the paper's two inputs (per-vertex degree bound `D`, and finite expected
   cluster volume), and in `_cutoff` also the degree bound and the edge-probability derivatives
   are discharged for the cut-off long-range model, leaving only the local-uniform-convergence
   input, away from the (countable) edge-length set.

5. Section `AlmostEverywhere` — the *off-edge-length vs. a.e.* distinction: the set of edge
   lengths is countable hence Lebesgue-null, and a derivative identity proved at every point off
   that set holds almost everywhere.  This is recorded separately because the finite-graph
   identity requires `∀ e, len e ≠ r` and the paper never states it with that exclusion.

6. Section `InfiniteVolumeSpatialMoment` — the passage from the truncated moments to the
   *genuine* infinite-volume spatial moment `∑_{x ∈ K_o} q x`: `spatialMomentENN` is the
   `ℝ≥0∞`-valued `tsum` over the cluster of `o`, `iSup_sMomentTruncENN` shows the truncations
   increase to it, `lintegral_spatialMomentENN` is monotone convergence for its integral, and
   `lintegral_sMomentTruncENN_eq` identifies the truncation integrals with the real expectations
   that the derivative formula of item 4 differentiates.  `tendsto_sMomentTrunc_of_finite` shows
   that on the event that `K_o` is finite the truncations converge to the honest finite sum
   `∑_{x ∈ K_o} q x` — that is the step at which a.s. finiteness of the cluster enters, and it is
   the only place where it does.

## A negative observation (relevant to the rejected source step)

One is tempted to justify the paper's "enlarge the covariance sums first" by monotonicity of the
truncated pivotal flux in the truncation set: `A ⊆ B ⟹ pivotalFlux (sMomentTrunc q o A) ≤
pivotalFlux (sMomentTrunc q o B)`.  That implication does **not** follow from
`sMomentTrunc_mono`: the flip difference is `f(K_o ∪ K_x) - f(K_o)`, and the two monotonicities
`A_on ≤ B_on`, `A_off ≤ B_off` do not compare their differences (they give opposite signs for the
two terms).  The correct enlargement keeps the factor `1(y ∉ K)` and adjoins the mass of `K_y`
*outside* `K`, which is a statement about the flip structure, not about monotonicity of the
truncated flux.  No monotonicity of the truncated pivotal flux is claimed in this file.

## Not claimed

The local-uniform-convergence input `hunif` (the window fluxes converge to the infinite pivotal
flux, locally uniformly in the parameter) is *not* proved here; it is the same obligation that
`RussoInf/Exchange` already isolates for the cardinality, and discharging it needs the
insertion-tolerance / sharpness mechanism used in the paper (including the corrected additive
I.4.12 estimate already available elsewhere in this repository) is not applied here to discharge it.
What is new here is that for the spatial moment the *flux domination* half of that input is
proved (`summable_abs_weight_touch` applied to `abs_sMomentTrunc_le`), and that the truncation to
the full infinite-volume spatial moment is proved by monotone convergence rather than assumed.
-/
module

public import PercLib.CriticalLRP.RussoInf.Exchange
public import PercLib.CriticalLRP.RussoInf.FluxMain

set_option autoImplicit true

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

@[expose] public section

open MeasureTheory Measure Filter Finset
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-! ## 1. The truncated spatial moment of the cluster of `o` -/

/-- The spatially weighted cluster moment of `o`, truncated to a finite vertex set `A`:
`∑_{x ∈ K_o ∩ A} q x`.  With `q x = ⟨x,u⟩²` and `A = B_r` this is the paper's
`∑_{x∈K∩B_r}⟨x,u⟩²`.  Written with `Set.indicator` (not `if`) so that no `Decidable`
instance enters the definition. -/
noncomputable def sMomentTrunc (q : V → ℝ) (o : V) (A : Finset V) (ω : Config V) : ℝ :=
  ∑ x ∈ A, (cluster ω o).indicator q x

/-- The truncated spatial moment is nonnegative for a nonnegative weight. -/
theorem sMomentTrunc_nonneg {q : V → ℝ} (hq : ∀ x, 0 ≤ q x) (o : V) (A : Finset V)
    (ω : Config V) : 0 ≤ sMomentTrunc q o A ω := by
  rw [sMomentTrunc]
  exact Finset.sum_nonneg fun x _ => by
    by_cases h : x ∈ cluster ω o
    · rw [Set.indicator_of_mem h]; exact hq x
    · rw [Set.indicator_of_notMem h]

/-- **The sup bound for the truncated spatial moment.**  This is the bound that replaces the cap
`m` of `cappedClusterVol`: the spatial weight is unbounded on the cluster, but its truncation to
the finite set `A` is bounded by the finite constant `∑_{x ∈ A}|q x|`. -/
theorem abs_sMomentTrunc_le (q : V → ℝ) (o : V) (A : Finset V) (ω : Config V) :
    |sMomentTrunc q o A ω| ≤ ∑ x ∈ A, |q x| := by
  refine (Finset.abs_sum_le_sum_abs (fun x => (cluster ω o).indicator q x) A).trans ?_
  refine Finset.sum_le_sum fun x _ => ?_
  by_cases h : x ∈ cluster ω o
  · rw [Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h, abs_zero]
    exact abs_nonneg (q x)

theorem measurable_sMomentTrunc (q : V → ℝ) (o : V) (A : Finset V) :
    Measurable (sMomentTrunc q o A) := by
  refine Finset.measurable_sum A fun x _ => ?_
  exact Measurable.indicator measurable_const (measurableSet_cluster_mem o x)

/-- The truncated spatial moment is a functional of the cluster of `o`. -/
theorem sMomentTrunc_dep (q : V → ℝ) (o : V) (A : Finset V) :
    ∀ ω η : Config V, cluster ω o = cluster η o →
      sMomentTrunc q o A ω = sMomentTrunc q o A η := by
  intro ω η h
  unfold sMomentTrunc
  rw [h]

/-- The truncated spatial moment is monotone in the truncation set for a nonnegative weight. -/
theorem sMomentTrunc_mono {q : V → ℝ} (hq : ∀ x, 0 ≤ q x) (o : V) {A B : Finset V}
    (hAB : A ⊆ B) (ω : Config V) : sMomentTrunc q o A ω ≤ sMomentTrunc q o B ω := by
  refine Finset.sum_le_sum_of_subset_of_nonneg hAB fun x _ _ => ?_
  by_cases h : x ∈ cluster ω o
  · rw [Set.indicator_of_mem h]; exact hq x
  · rw [Set.indicator_of_notMem h]

/-- The truncated spatial moment is the spatial moment of `K_o ∩ A`, in the form in which the
paper writes it. -/
theorem sMomentTrunc_eq_sum_filter (q : V → ℝ) (o : V) (A : Finset V) (ω : Config V) :
    sMomentTrunc q o A ω = ∑ x ∈ A.filter (fun x => x ∈ cluster ω o), q x := by
  rw [sMomentTrunc, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : x ∈ cluster ω o
  · rw [Set.indicator_of_mem h, ite_eq_left h]
  · rw [Set.indicator_of_notMem h, ite_eq_right h]

/-! ## 2. Edge-exhausting windows: the truncated spatial moment of the truncated configuration -/

/-- Along an edge-exhausting window sequence, the truncated spatial moment of the truncated
configuration equals that of the full configuration eventually. -/
theorem eventually_sMomentTrunc_cutConfig (S : ℕ → Finset (Sym2 V)) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 V, ∃ n, e ∈ S n) (q : V → ℝ) (o : V) (A : Finset V) (ω : Config V) :
    ∀ᶠ k in atTop, sMomentTrunc q o A (cutConfig (S k) ω) = sMomentTrunc q o A ω := by
  have hev : ∀ᶠ k in atTop, ∀ x ∈ A,
      (cluster (cutConfig (S k) ω) o).indicator q x = (cluster ω o).indicator q x := by
    rw [eventually_all_finset]
    intro x _
    by_cases hx : x ∈ cluster ω o
    · filter_upwards [eventually_mem_cluster_cutConfig S hSmono hS ω hx] with k hk
      rw [Set.indicator_of_mem hk, Set.indicator_of_mem hx]
    · filter_upwards with k
      have hnot : x ∉ cluster (cutConfig (S k) ω) o := fun hc =>
        hx (cluster_mono (ω := cutConfig (S k) ω) (ω' := ω) (fun e he => he.1) o hc)
      rw [Set.indicator_of_notMem hnot, Set.indicator_of_notMem hx]
  filter_upwards [hev] with k hk
  exact Finset.sum_congr rfl fun x hx => hk x hx

/-- **Pointwise convergence of the truncated spatial moments.** -/
theorem tendsto_sMomentTrunc_cutConfig (S : ℕ → Finset (Sym2 V)) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 V, ∃ n, e ∈ S n) (q : V → ℝ) (o : V) (A : Finset V) (ω : Config V) :
    Tendsto (fun k => sMomentTrunc q o A (cutConfig (S k) ω)) atTop
      (𝓝 (sMomentTrunc q o A ω)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_sMomentTrunc_cutConfig S hSmono hS q o A ω] with k hk
  exact hk.symm

/-- **Window expectations of the truncated spatial moment converge to the infinite-volume
expectation.**  Dominated convergence with the finite bound `∑_{x ∈ A}|q x|`. -/
theorem tendsto_integral_sMomentTrunc (S : ℕ → Finset (Sym2 V)) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 V, ∃ n, e ∈ S n) (q : V → ℝ) (o : V) (A : Finset V)
    (μ : Measure (Config V)) [IsProbabilityMeasure μ] :
    Tendsto (fun k => ∫ ω : Config V, sMomentTrunc q o A (cutConfig (S k) ω) ∂μ) atTop
      (𝓝 (∫ ω : Config V, sMomentTrunc q o A ω ∂μ)) := by
  refine tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun k ω => sMomentTrunc q o A (cutConfig (S k) ω))
    (f := fun ω => sMomentTrunc q o A ω) (bound := fun _ => ∑ x ∈ A, |q x|)
    (fun k => ((measurable_sMomentTrunc q o A).comp (measurable_cutConfig (S k))).aestronglyMeasurable)
    (integrable_const _) ?_ ?_
  · intro k
    filter_upwards with ω
    rw [Real.norm_eq_abs]
    exact abs_sMomentTrunc_le q o A _
  · exact Eventually.of_forall fun ω =>
      tendsto_sMomentTrunc_cutConfig S hSmono hS q o A ω

/-! ## 3. The infinite-volume Russo exchange for a general bounded cluster functional -/

/-- **Window expectations converge to the infinite-volume expectation** for an arbitrary
bounded, measurable functional satisfying the pointwise window convergence.  (Generalises
`tendsto_integral_cutFun`, which is stated for `cappedClusterVol` only.) -/
theorem tendsto_integral_cutFun_of_bound (S : ℕ → Finset (Sym2 V))
    {g : Config V → ℝ} {m : ℝ} (hbound : ∀ ω, |g ω| ≤ m) (hmeas : Measurable g)
    (hcont : ∀ ω : Config V, Tendsto (fun n => cutFun (S n) g ω) atTop (𝓝 (g ω)))
    (μ : Measure (Config V)) [IsProbabilityMeasure μ] :
    Tendsto (fun k => ∫ ω : Config V, cutFun (S k) g ω ∂μ) atTop
      (𝓝 (∫ ω : Config V, g ω ∂μ)) := by
  refine tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun k ω => cutFun (S k) g ω) (f := fun ω => g ω) (bound := fun _ => m)
    (fun k => (measurable_cutFun hmeas).aestronglyMeasurable)
    (integrable_const _) ?_ ?_
  · intro k
    filter_upwards with ω
    rw [Real.norm_eq_abs]
    exact hbound _
  · exact Eventually.of_forall hcont

/-- **Infinite-volume Russo exchange for a bounded cluster functional (reduced form).**

For a family of independent edge laws with parameter derivatives `c`, windows `S k` exhausting
the edge set, and a bounded measurable functional `g` of the cluster of `o`, the expectation of
`g` has derivative `Φ r₀` at `r₀`, provided the flux weights are summable and the window fluxes
converge to `Φ` locally uniformly near `r₀`.  All other inputs are discharged from the
finite-window Russo identity (`hasDerivAt_integral_cutFun`), the pointwise convergence of the
window expectations and the pointwise convergence of the window fluxes
(`tendsto_windowFlux`). -/
theorem hasDerivAt_integral_clusterFun (o : V)
    (S : ℕ → Finset (Sym2 V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 V, ∃ n, e ∈ S n)
    (π : ℝ → Sym2 V → unitInterval) (c : ℝ → Sym2 V → ℝ)
    {g : Config V → ℝ} {m : ℝ} (hbound : ∀ ω, |g ω| ≤ m) (hmeas : Measurable g)
    (hdep : ∀ ω η : Config V, cluster ω o = cluster η o → g ω = g η)
    (hcont : ∀ ω : Config V, Tendsto (fun n => cutFun (S n) g ω) atTop (𝓝 (g ω)))
    {I : Set ℝ} (hI : IsOpen I) {r0 : ℝ} (hr0 : r0 ∈ I)
    (hderiv : ∀ e : Sym2 V, ∀ r ∈ I,
      HasDerivAt (fun r' => ((π r' e : unitInterval) : ℝ)) (c r e) r)
    (hdom : ∀ r ∈ I, Summable fun e : Sym2 V =>
      |c r e| * (2 * max m 0 * (edgeMeasure (π r)).real {ω : Config V | e ∈ touchSet ω o}))
    (Φ : ℝ → ℝ)
    (hunif : TendstoLocallyUniformlyOn
      (fun k r => ∑ e ∈ S k, c r e *
        pivotalFlux (edgeMeasure (π r)) (cutFun (S k) g) e) Φ atTop I) :
    HasDerivAt (fun r => ∫ ω : Config V, g ω ∂(edgeMeasure (π r))) (Φ r0) r0 := by
  classical
  refine hasDerivAt_integral_of_windowFlux S (fun r => edgeMeasure (π r)) c hI ?_ ?_ hunif hr0
  · intro k r hr
    have h := hasDerivAt_integral_cutFun π (c r) (S k) g (fun e => hderiv e r hr)
    have hsum : (∑ e : S k, c r (e : Sym2 V) *
          pivotalFlux (edgeMeasure (π r)) (cutFun (S k) g) (e : Sym2 V))
        = ∑ e ∈ S k, c r e * pivotalFlux (edgeMeasure (π r)) (cutFun (S k) g) e :=
      Finset.sum_coe_sort (S k) (fun e => c r e *
        pivotalFlux (edgeMeasure (π r)) (cutFun (S k) g) e)
    exact h.congr_deriv hsum
  · intro r _
    exact tendsto_integral_cutFun_of_bound S hbound hmeas hcont (edgeMeasure (π r))

/-- **Infinite-volume Russo for the truncated spatial moment (reduced form).**

The `r`-derivative of `r ↦ ∫ sMomentTrunc q o A ∂P_r` is the infinite pivotal flux `Φ r₀`,
under the flux-domination hypothesis and local uniform convergence of the window fluxes. -/
theorem hasDerivAt_integral_sMomentTrunc
    (o : V) (A : Finset V) (q : V → ℝ)
    (S : ℕ → Finset (Sym2 V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 V, ∃ n, e ∈ S n)
    (π : ℝ → Sym2 V → unitInterval) (c : ℝ → Sym2 V → ℝ)
    {I : Set ℝ} (hI : IsOpen I) {r0 : ℝ} (hr0 : r0 ∈ I)
    (hderiv : ∀ e : Sym2 V, ∀ r ∈ I,
      HasDerivAt (fun r' => ((π r' e : unitInterval) : ℝ)) (c r e) r)
    (hdom : ∀ r ∈ I, Summable fun e : Sym2 V =>
      |c r e| * (2 * (∑ x ∈ A, |q x|) *
        (edgeMeasure (π r)).real {ω : Config V | e ∈ touchSet ω o}))
    (Φ : ℝ → ℝ)
    (hunif : TendstoLocallyUniformlyOn
      (fun k r => ∑ e ∈ S k, c r e *
        pivotalFlux (edgeMeasure (π r)) (cutFun (S k) (sMomentTrunc q o A)) e) Φ atTop I) :
    HasDerivAt (fun r => ∫ ω : Config V, sMomentTrunc q o A ω ∂(edgeMeasure (π r)))
      (Φ r0) r0 := by
  have hA : 0 ≤ ∑ x ∈ A, |q x| := Finset.sum_nonneg fun x _ => abs_nonneg (q x)
  refine hasDerivAt_integral_clusterFun o S hSmono hS π c
    (m := ∑ x ∈ A, |q x|) (abs_sMomentTrunc_le q o A) (measurable_sMomentTrunc q o A)
    (sMomentTrunc_dep q o A) (fun ω => ?_) hI hr0 hderiv ?_ Φ hunif
  · simpa only [cutFun] using tendsto_sMomentTrunc_cutConfig S hSmono hS q o A ω
  · intro r hr
    refine (hdom r hr).congr fun e => ?_
    rw [max_eq_left hA]

/-- **Infinite-volume Russo for the truncated spatial moment, from the paper's two inputs.**

The flux-domination hypothesis of `hasDerivAt_integral_sMomentTrunc` is discharged from the
per-vertex degree bound `hdeg` on the derivative weights and finiteness of the expected cluster
volume `hvol` (the sharpness input), via `summable_abs_weight_touch` and the sup bound
`abs_sMomentTrunc_le`.  The total flux mass is at most `2 (∑_{x∈A}|q x|) · D · E|K_o|`. -/
theorem hasDerivAt_integral_sMomentTrunc_of_sharpness
    (o : V) (A : Finset V) (q : V → ℝ)
    (S : ℕ → Finset (Sym2 V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 V, ∃ n, e ∈ S n)
    (π : ℝ → Sym2 V → unitInterval) (c : ℝ → Sym2 V → ℝ) (D : ℝ → ℝ)
    {I : Set ℝ} (hI : IsOpen I) {r0 : ℝ} (hr0 : r0 ∈ I)
    (hderiv : ∀ e : Sym2 V, ∀ r ∈ I,
      HasDerivAt (fun r' => ((π r' e : unitInterval) : ℝ)) (c r e) r)
    (hD : ∀ r ∈ I, 0 ≤ D r)
    (hdeg : ∀ r ∈ I, ∀ x : V, ∀ u : Finset (Sym2 V),
      ∑ e ∈ u, |c r e| * (if x ∈ e then (1 : ℝ) else 0) ≤ D r)
    (hvol : ∀ r ∈ I, ∫⁻ ω : Config V, clusterVol ω o ∂(edgeMeasure (π r)) ≠ ⊤)
    (Φ : ℝ → ℝ)
    (hunif : TendstoLocallyUniformlyOn
      (fun k r => ∑ e ∈ S k, c r e *
        pivotalFlux (edgeMeasure (π r)) (cutFun (S k) (sMomentTrunc q o A)) e) Φ atTop I) :
    HasDerivAt (fun r => ∫ ω : Config V, sMomentTrunc q o A ω ∂(edgeMeasure (π r)))
      (Φ r0) r0 := by
  have hA : 0 ≤ ∑ x ∈ A, |q x| := Finset.sum_nonneg fun x _ => abs_nonneg (q x)
  refine hasDerivAt_integral_sMomentTrunc o A q S hSmono hS π c hI hr0 hderiv
    (fun r hr => ?_) Φ hunif
  have hsum := summable_abs_weight_touch (o := o) (edgeMeasure (π r)) (c r) (hD r hr)
    (hdeg r hr) (hvol r hr)
  refine (hsum.mul_left (2 * (∑ x ∈ A, |q x|))).congr fun e => ?_
  ring

/-! ## 4. Instantiation at the cut-off long-range model on `ℤ^d` -/

variable {d : ℕ}

/-- **Infinite-volume Russo for the truncated spatial moment of the cut-off model.**

For the cut-off long-range model on `ℤ^d` with profile `K` and derivative scale `K'`
(`d/dr K = -K'`), away from edge lengths (`hne`), the `r`-derivative of
`r ↦ ∫ sMomentTrunc q o A ∂P_r` is the infinite pivotal flux `Φ r₀`.

Every input except the local uniform convergence `hunif` is discharged: the edge-probability
derivatives (`CutoffFlux.cutoffEdgeDeriv_hasDerivAt`), the per-vertex degree bound of the cut-off
graph (`CutoffFlux.cutoff_edgeDeriv_degree`), and the flux domination (from `hvol`, the
finiteness of the expected cluster volume). -/
theorem hasDerivAt_integral_sMomentTrunc_cutoff
    (o : Fin d → ℤ) (A : Finset (Fin d → ℤ)) (q : (Fin d → ℤ) → ℝ)
    (S : ℕ → Finset (Sym2 (Fin d → ℤ))) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 (Fin d → ℤ), ∃ n, e ∈ S n)
    {β K' : ℝ} (hβ : 0 ≤ β) (hK' : 0 ≤ K') {K : ℝ → ℝ}
    (hprof : ∀ (r : ℝ) (e : Sym2 (Fin d → ℤ)),
      0 ≤ FiniteVolume.cutoffProfile K r (FiniteVolume.edgeLen e))
    {I : Set ℝ} (hI : IsOpen I) {r0 : ℝ} (hr0 : r0 ∈ I)
    (hderivK : ∀ r ∈ I, HasDerivAt K (-K') r)
    (hne : ∀ r ∈ I, ∀ e : Sym2 (Fin d → ℤ), FiniteVolume.edgeLen e ≠ r)
    (hvol : ∀ r ∈ I, ∫⁻ ω : Config (Fin d → ℤ), clusterVol ω o
      ∂(edgeMeasure (cutoffPiFamily (d := d) β K hβ hprof r)) ≠ ⊤)
    (Φ : ℝ → ℝ)
    (hunif : TendstoLocallyUniformlyOn
      (fun k r => ∑ e ∈ S k, CutoffFlux.cutoffEdgeDeriv K β K' r e *
        pivotalFlux (edgeMeasure (cutoffPiFamily (d := d) β K hβ hprof r))
          (cutFun (S k) (sMomentTrunc (V := Fin d → ℤ) q o A)) e) Φ atTop I) :
    HasDerivAt (fun r => ∫ ω : Config (Fin d → ℤ), sMomentTrunc (V := Fin d → ℤ) q o A ω
      ∂(edgeMeasure (cutoffPiFamily (d := d) β K hβ hprof r))) (Φ r0) r0 := by
  classical
  refine hasDerivAt_integral_sMomentTrunc_of_sharpness (V := Fin d → ℤ) o A q S hSmono hS
    (cutoffPiFamily (d := d) β K hβ hprof) (fun r e => CutoffFlux.cutoffEdgeDeriv K β K' r e)
    (fun r => β * K' * ((2 * ⌈r⌉₊ + 1) ^ d : ℕ)) hI hr0 ?_ ?_ ?_ hvol Φ hunif
  · intro e r hr
    have h := CutoffFlux.cutoffEdgeDeriv_hasDerivAt (K := K) (β := β) (K' := K') (r := r)
      (e := e) (hne r hr e) (hderivK r hr)
    simpa only [cutoffPiFamily_coe] using h
  · intro r _
    positivity
  · intro r _ x u
    have h := CutoffFlux.cutoff_edgeDeriv_degree (d := d) (K := K) (β := β) (K' := K') (r := r)
      hβ hK' (fun e => longRangeEdgeProbability_nonneg hβ (hprof r e))
      (fun e => longRangeEdgeProbability_le_one hβ (hprof r e)) x u
    refine (le_of_eq ?_).trans h
    refine Finset.sum_congr rfl fun e _ => ?_
    exact congrArg (fun t => |CutoffFlux.cutoffEdgeDeriv K β K' r e| * t)
      (CutoffFlux.ite_inst_irrel _ _ (1 : ℝ) 0)

/-! ## 5. Off-edge-length versus almost everywhere -/

/-- The set of edge lengths in `ℤ^d`, regarded as a set of real parameters, is countable. -/
theorem countable_range_edgeLen (d : ℕ) :
    (Set.range (fun e : Sym2 (Fin d → ℤ) => (FiniteVolume.edgeLen e : ℝ))).Countable :=
  Set.countable_range _

/-- The set of edge lengths is Lebesgue-null.  This is exactly the exceptional set on which the
cut-off edge probability `q_e(r) = 1 - exp(-β J_r(e))` fails to have the derivative
`cutoffEdgeDeriv`: the finite-graph identity needs `∀ e, |e| ≠ r`, and the paper only ever needs
the a.e. statement. -/
theorem volume_range_edgeLen (d : ℕ) :
    volume (Set.range (fun e : Sym2 (Fin d → ℤ) => (FiniteVolume.edgeLen e : ℝ))) = 0 :=
  (countable_range_edgeLen d).measure_zero volume

/-- **Off a countable parameter set implies almost everywhere.** -/
theorem ae_of_forall_notMem_countable {C : Set ℝ} (hC : C.Countable) {P : ℝ → Prop}
    (h : ∀ r, r ∉ C → P r) : ∀ᵐ r ∂(volume : Measure ℝ), P r := by
  rw [ae_iff]
  refine measure_mono_null ?_ (hC.measure_zero volume)
  intro r hr
  simp only [Set.mem_ofPred_eq] at hr
  by_contra hrc
  exact hr (h r hrc)

/-- **Almost-everywhere derivative identity.**  A family of derivative identities that holds at
every parameter outside a countable set (in the application, the edge lengths) holds for almost
every parameter. -/
theorem ae_hasDerivAt_of_notMem_countable {C : Set ℝ} (hC : C.Countable)
    {E D : ℝ → ℝ} (h : ∀ r, r ∉ C → HasDerivAt E (D r) r) :
    ∀ᵐ r ∂(volume : Measure ℝ), HasDerivAt E (D r) r :=
  ae_of_forall_notMem_countable hC h

/-- **Off-edge-length implies almost everywhere, on a parameter set**: if the identity holds at
every point of `I` that is not an edge length, then it holds at almost every point of `I` — the
only points of `I` it can fail at are the edge lengths, a countable hence null set.  This is the
precise form of the `∀ e, |e| ≠ r` / `∀ᵐ r` distinction: the off-edge-length hypothesis of the
exchange is strictly stronger than the a.e. statement the paper only needs. -/
theorem ae_hasDerivAt_of_off_edgeLen {C : Set ℝ} (hC : C.Countable) {E D : ℝ → ℝ} {I : Set ℝ}
    (h : ∀ r ∈ I, r ∉ C → HasDerivAt E (D r) r) :
    ∀ᵐ r ∂(volume : Measure ℝ), r ∈ I → HasDerivAt E (D r) r := by
  rw [ae_iff]
  refine measure_mono_null ?_ (hC.measure_zero volume)
  intro r hr
  simp only [Set.mem_ofPred_eq, not_imp] at hr
  by_contra hrc
  exact hr.2 (h r hr.1 hrc)

/-- **The truncated spatial moment of the cut-off model is differentiable almost everywhere**,
with derivative the infinite pivotal flux, on any open parameter set `I` all of whose points are
off the edge-length set.  (This is the `∀ᵐ r` form of
`hasDerivAt_integral_sMomentTrunc_cutoff`, whose hypotheses hold at every off-edge-length `r`.) -/
theorem ae_hasDerivAt_integral_sMomentTrunc_cutoff
    (o : Fin d → ℤ) (A : Finset (Fin d → ℤ)) (q : (Fin d → ℤ) → ℝ)
    (S : ℕ → Finset (Sym2 (Fin d → ℤ))) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 (Fin d → ℤ), ∃ n, e ∈ S n)
    {β K' : ℝ} (hβ : 0 ≤ β) (hK' : 0 ≤ K') {K : ℝ → ℝ}
    (hprof : ∀ (r : ℝ) (e : Sym2 (Fin d → ℤ)),
      0 ≤ FiniteVolume.cutoffProfile K r (FiniteVolume.edgeLen e))
    {I : Set ℝ} (hI : IsOpen I)
    (hIoff : ∀ r ∈ I, r ∉ Set.range (fun e : Sym2 (Fin d → ℤ) => (FiniteVolume.edgeLen e : ℝ)))
    (hderivK : ∀ r ∈ I, HasDerivAt K (-K') r)
    (hvol : ∀ r ∈ I, ∫⁻ ω : Config (Fin d → ℤ), clusterVol ω o
      ∂(edgeMeasure (cutoffPiFamily (d := d) β K hβ hprof r)) ≠ ⊤)
    (Φ : ℝ → ℝ)
    (hunif : TendstoLocallyUniformlyOn
      (fun k r => ∑ e ∈ S k, CutoffFlux.cutoffEdgeDeriv K β K' r e *
        pivotalFlux (edgeMeasure (cutoffPiFamily (d := d) β K hβ hprof r))
          (cutFun (S k) (sMomentTrunc (V := Fin d → ℤ) q o A)) e) Φ atTop I) :
    ∀ᵐ r ∂(volume : Measure ℝ), r ∈ I →
      HasDerivAt (fun r' => ∫ ω : Config (Fin d → ℤ),
        sMomentTrunc (V := Fin d → ℤ) q o A ω
        ∂(edgeMeasure (cutoffPiFamily (d := d) β K hβ hprof r'))) (Φ r) r :=
  ae_hasDerivAt_of_off_edgeLen (countable_range_edgeLen d) fun r hr _ =>
    hasDerivAt_integral_sMomentTrunc_cutoff o A q S hSmono hS hβ hK' hprof hI hr
      hderivK (fun r' hr' e hc => hIoff r' hr' ⟨e, hc⟩) hvol Φ hunif

/-! ## 6. The genuine infinite-volume spatial moment and monotone convergence -/

section InfiniteVolumeSpatialMoment

/-- The genuine infinite-volume spatially weighted cluster moment of `o`, as an `ℝ≥0∞` sum over
the whole (possibly infinite) cluster.  With `q x = ⟨x,u⟩²` this is the object whose expectation
Lemma I.5.8 differentiates. -/
noncomputable def spatialMomentENN (q : V → ℝ) (o : V) (ω : Config V) : ℝ≥0∞ :=
  ∑' x : V, (cluster ω o).indicator (fun x => ENNReal.ofReal (q x)) x

/-- The truncation of `spatialMomentENN` to a finite vertex set `A`, in `ℝ≥0∞`. -/
noncomputable def sMomentTruncENN (q : V → ℝ) (o : V) (A : Finset V) (ω : Config V) : ℝ≥0∞ :=
  ∑ x ∈ A, (cluster ω o).indicator (fun x => ENNReal.ofReal (q x)) x

theorem measurable_sMomentTruncENN (q : V → ℝ) (o : V) (A : Finset V) :
    Measurable (sMomentTruncENN q o A) := by
  refine Finset.measurable_sum A fun x _ => ?_
  exact Measurable.indicator measurable_const (measurableSet_cluster_mem o x)

/-- The `ℝ≥0∞` truncation is the `ENNReal.ofReal` of the real truncation. -/
theorem ofReal_sMomentTrunc {q : V → ℝ} (hq : ∀ x, 0 ≤ q x) (o : V) (A : Finset V)
    (ω : Config V) :
    ENNReal.ofReal (sMomentTrunc q o A ω) = sMomentTruncENN q o A ω := by
  rw [sMomentTrunc, sMomentTruncENN, ENNReal.ofReal_sum_of_nonneg]
  · refine Finset.sum_congr rfl fun x _ => ?_
    by_cases h : x ∈ cluster ω o
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, ENNReal.ofReal_zero]
  · intro x _
    by_cases h : x ∈ cluster ω o
    · rw [Set.indicator_of_mem h]; exact hq x
    · rw [Set.indicator_of_notMem h]

/-- Along an edge-exhausting (more precisely, vertex-exhausting) sequence of finite vertex sets,
some member contains any prescribed finite set. -/
theorem exists_finset_subset_of_exhausting {A : ℕ → Finset V} (hAmono : Monotone A)
    (hA : ∀ x : V, ∃ k, x ∈ A k) (s : Finset V) : ∃ k, s ⊆ A k := by
  classical
  choose k hk using hA
  refine ⟨s.sup k, fun x hx => ?_⟩
  exact hAmono (Finset.le_sup (f := k) hx) (hk x)

/-- The `ℝ≥0∞` truncations are monotone in the truncation set. -/
theorem monotone_sMomentTruncENN {A : ℕ → Finset V} (hAmono : Monotone A) (q : V → ℝ) (o : V)
    (ω : Config V) : Monotone fun k => sMomentTruncENN q o (A k) ω := by
  intro m n hmn
  refine Finset.sum_le_sum_of_subset_of_nonneg (hAmono hmn) ?_
  intro x _ _
  exact zero_le

/-- **The truncations increase to the genuine infinite-volume spatial moment.** -/
theorem iSup_sMomentTruncENN {A : ℕ → Finset V} (hAmono : Monotone A)
    (hA : ∀ x : V, ∃ k, x ∈ A k) (q : V → ℝ) (o : V) (ω : Config V) :
    (⨆ k, sMomentTruncENN q o (A k) ω) = spatialMomentENN q o ω := by
  refine le_antisymm (iSup_le fun k => ENNReal.sum_le_tsum (A k)) ?_
  rw [spatialMomentENN, ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  obtain ⟨k, hk⟩ := exists_finset_subset_of_exhausting hAmono hA s
  refine le_iSup_of_le k (Finset.sum_le_sum_of_subset_of_nonneg hk ?_)
  intro x _ _
  exact zero_le

/-- **Monotone convergence for the infinite-volume spatial moment**: the integral of the genuine
spatial moment is the supremum of the integrals of its finite truncations. -/
theorem lintegral_spatialMomentENN {A : ℕ → Finset V} (hAmono : Monotone A)
    (hA : ∀ x : V, ∃ k, x ∈ A k) (q : V → ℝ) (o : V) (μ : Measure (Config V)) :
    ∫⁻ ω, spatialMomentENN q o ω ∂μ
      = ⨆ k, ∫⁻ ω, sMomentTruncENN q o (A k) ω ∂μ := by
  have hfun : spatialMomentENN q o
      = fun ω => ⨆ k, sMomentTruncENN q o (A k) ω := by
    funext ω
    exact (iSup_sMomentTruncENN hAmono hA q o ω).symm
  rw [hfun, lintegral_iSup (fun k => measurable_sMomentTruncENN q o (A k))
    (fun m n hmn ω => monotone_sMomentTruncENN hAmono q o ω hmn)]

/-- Boundedness gives integrability of the real truncation. -/
theorem integrable_sMomentTrunc (q : V → ℝ) (o : V) (A : Finset V)
    (μ : Measure (Config V)) [IsFiniteMeasure μ] : Integrable (sMomentTrunc q o A) μ := by
  refine Integrable.of_bound (measurable_sMomentTrunc q o A).aestronglyMeasurable
    (∑ x ∈ A, |q x|) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs]
  exact abs_sMomentTrunc_le q o A ω

/-- **The `ℝ≥0∞` truncation integral is the real expectation**, for a nonnegative weight.  This is
the bridge from the derivative formula of Section 4 (stated for the real expectation
`∫ sMomentTrunc q o A`) to the `ℝ≥0∞`-valued infinite-volume spatial moment. -/
theorem lintegral_sMomentTruncENN_eq {q : V → ℝ} (hq : ∀ x, 0 ≤ q x) (o : V) (A : Finset V)
    (μ : Measure (Config V)) [IsFiniteMeasure μ] :
    ∫⁻ ω, sMomentTruncENN q o A ω ∂μ
      = ENNReal.ofReal (∫ ω, sMomentTrunc q o A ω ∂μ) := by
  have hfun : (fun ω => sMomentTruncENN q o A ω)
      = fun ω => ENNReal.ofReal (sMomentTrunc q o A ω) := by
    funext ω
    exact (ofReal_sMomentTrunc hq o A ω).symm
  rw [hfun, ← ofReal_integral_eq_lintegral_ofReal (f := sMomentTrunc q o A)
    (integrable_sMomentTrunc q o A μ)
    (Eventually.of_forall fun ω => sMomentTrunc_nonneg hq o A ω)]

/-- **The expectation of the genuine infinite-volume spatial moment is the supremum of the
truncated-model expectations.**  This is the exact sense in which the finite-window expectations
converge to the infinite-volume spatial moment: no derivative is exchanged here, only the
monotone limit of the observed quantities. -/
theorem lintegral_spatialMomentENN_eq_iSup {A : ℕ → Finset V} (hAmono : Monotone A)
    (hA : ∀ x : V, ∃ k, x ∈ A k) {q : V → ℝ} (hq : ∀ x, 0 ≤ q x) (o : V)
    (μ : Measure (Config V)) [IsFiniteMeasure μ] :
    ∫⁻ ω, spatialMomentENN q o ω ∂μ
      = ⨆ k, ENNReal.ofReal (∫ ω, sMomentTrunc q o (A k) ω ∂μ) := by
  rw [lintegral_spatialMomentENN hAmono hA q o μ]
  exact iSup_congr fun k => lintegral_sMomentTruncENN_eq hq o (A k) μ

/-- **On the event that the cluster of `o` is finite, the truncations converge to the honest
finite sum `∑_{x ∈ K_o} q x`.**  This is the only place where finiteness of the cluster is used,
and it is what makes `spatialMomentENN` the paper's `∑_{x∈K}⟨x,u⟩²`. -/
theorem tendsto_sMomentTrunc_of_finite {A : ℕ → Finset V} (hAmono : Monotone A)
    (hA : ∀ x : V, ∃ k, x ∈ A k) (q : V → ℝ) (o : V) {ω : Config V}
    (hfin : (cluster ω o).Finite) :
    Tendsto (fun k => sMomentTrunc q o (A k) ω) atTop (𝓝 (∑ x ∈ hfin.toFinset, q x)) := by
  have hev : ∀ᶠ k in atTop, sMomentTrunc q o (A k) ω = ∑ x ∈ hfin.toFinset, q x := by
    obtain ⟨K, hK⟩ := exists_finset_subset_of_exhausting hAmono hA hfin.toFinset
    refine eventually_atTop.mpr ⟨K, fun n hn => ?_⟩
    have h1 : ∑ x ∈ hfin.toFinset, (cluster ω o).indicator q x
        = sMomentTrunc q o (A n) ω :=
      Finset.sum_subset (hK.trans (hAmono hn)) fun x _ hxnot => by
        by_cases hc : x ∈ cluster ω o
        · exact absurd (hfin.mem_toFinset.mpr hc) hxnot
        · exact Set.indicator_of_notMem hc q
    rw [← h1]
    exact Finset.sum_congr rfl fun x hx => Set.indicator_of_mem (hfin.mem_toFinset.mp hx) q
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hev] with k hk
  exact hk.symm

end InfiniteVolumeSpatialMoment

/-! ## 7. The total pivotal flux of the truncated spatial moment, and the quadratic weight -/

/-- **The pivotal flux of the truncated spatial moment is absolutely summable, with total mass at
most `2 (∑_{x∈A}|q x|) · D · E|K_o|`.**

This is the quantitative half of the paper's "finite pivotal flux" input for Lemma I.5.8: the
spatial weight is unbounded on the cluster, but truncating it to `A` replaces the cap `m` of the
cluster-volume case by the finite constant `∑_{x∈A}|q x|`. -/
theorem tsum_abs_pivotalFlux_sMomentTrunc_le (o : V) (A : Finset V) (q : V → ℝ)
    (μ : Measure (Config V)) [IsProbabilityMeasure μ] {c : Sym2 V → ℝ} {D : ℝ} (hD : 0 ≤ D)
    (hdeg : ∀ x : V, ∀ u : Finset (Sym2 V),
      ∑ e ∈ u, |c e| * (if x ∈ e then (1 : ℝ) else 0) ≤ D)
    (hvol : ∫⁻ ω : Config V, clusterVol ω o ∂μ ≠ ⊤) :
    ∑' e : Sym2 V, |c e * pivotalFlux μ (sMomentTrunc q o A) e|
      ≤ 2 * (∑ x ∈ A, |q x|) * D * (∫⁻ ω : Config V, clusterVol ω o ∂μ).toReal :=
  tsum_abs_pivotalFlux_le (o := o) μ c (D := D) (m := ∑ x ∈ A, |q x|)
    (Finset.sum_nonneg fun x _ => abs_nonneg (q x)) hD hdeg
    (abs_sMomentTrunc_le q o A) (measurable_sMomentTrunc q o A) (sMomentTrunc_dep q o A) hvol

/-! ### The quadratic weight `x ↦ ⟨x,u⟩²` -/

/-- The quadratic weight of Lemma I.5.8: `x ↦ ⟨x,u⟩²` for `x ∈ ℤ^d` and `u ∈ ℝ^d`. -/
noncomputable def quadWeight {d : ℕ} (u : Fin d → ℝ) (x : Fin d → ℤ) : ℝ :=
  (∑ i, (x i : ℝ) * u i) ^ 2

theorem quadWeight_nonneg {d : ℕ} (u : Fin d → ℝ) (x : Fin d → ℤ) : 0 ≤ quadWeight u x :=
  sq_nonneg _

/-- **The size of the quadratic weight on a ball.**  If every coordinate of `x` is at most `r` in
absolute value then `⟨x,u⟩² ≤ ‖u‖₁² r²`, which is the `‖u‖²₂ r²` factor of Lemma I.5.8. -/
theorem quadWeight_le {d : ℕ} (u : Fin d → ℝ) {r : ℝ} (hr : 0 ≤ r) {x : Fin d → ℤ}
    (hx : ∀ i, |(x i : ℝ)| ≤ r) :
    quadWeight u x ≤ (∑ i, |u i|) ^ 2 * r ^ 2 := by
  have habs : |∑ i, (x i : ℝ) * u i| ≤ r * ∑ i, |u i| := by
    refine (Finset.abs_sum_le_sum_abs (fun i => (x i : ℝ) * u i) Finset.univ).trans ?_
    calc ∑ i, |(x i : ℝ) * u i| = ∑ i, |(x i : ℝ)| * |u i| :=
          Finset.sum_congr rfl fun i _ => abs_mul _ _
      _ ≤ ∑ i, r * |u i| :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hx i) (abs_nonneg (u i))
      _ = r * ∑ i, |u i| := (Finset.mul_sum Finset.univ (fun i => |u i|) r).symm
  have hsq : |∑ i, (x i : ℝ) * u i| ^ 2 ≤ (r * ∑ i, |u i|) ^ 2 := by
    have h := mul_self_le_mul_self (abs_nonneg (∑ i, (x i : ℝ) * u i)) habs
    simpa [sq] using h
  rw [quadWeight, ← sq_abs]
  calc |∑ i, (x i : ℝ) * u i| ^ 2 ≤ (r * ∑ i, |u i|) ^ 2 := hsq
    _ = (∑ i, |u i|) ^ 2 * r ^ 2 := by ring

/-- **The sup bound of the truncated quadratic moment on a ball**: at most
`#(A ∩ B_r) · ‖u‖₁² r²`. -/
theorem sum_quadWeight_le {d : ℕ} (u : Fin d → ℝ) {r : ℝ} (hr : 0 ≤ r)
    (A : Finset (Fin d → ℤ)) (hA : ∀ x ∈ A, ∀ i, |(x i : ℝ)| ≤ r) :
    ∑ x ∈ A, |quadWeight u x| ≤ (A.card : ℝ) * ((∑ i, |u i|) ^ 2 * r ^ 2) := by
  calc ∑ x ∈ A, |quadWeight u x| ≤ ∑ _x ∈ A, ((∑ i, |u i|) ^ 2 * r ^ 2) := by
        refine Finset.sum_le_sum fun x hx => ?_
        rw [abs_of_nonneg (quadWeight_nonneg u x)]
        exact quadWeight_le u hr (hA x hx)
    _ = (A.card : ℝ) * ((∑ i, |u i|) ^ 2 * r ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- **The total pivotal flux of the truncated quadratic moment on a ball**: at most
`2 #(A ∩ B_r) ‖u‖₁² r² · D · E|K_o|`.  This is the quantitative input that the proof of
Lemma I.5.8 uses to control the pivotal-flux sums of the spatial moment. -/
theorem tsum_abs_pivotalFlux_quadWeight_le {d : ℕ} (u : Fin d → ℝ) {r : ℝ} (hr : 0 ≤ r)
    (o : Fin d → ℤ) (A : Finset (Fin d → ℤ)) (hA : ∀ x ∈ A, ∀ i, |(x i : ℝ)| ≤ r)
    (μ : Measure (Config (Fin d → ℤ))) [IsProbabilityMeasure μ]
    {c : Sym2 (Fin d → ℤ) → ℝ} {D : ℝ} (hD : 0 ≤ D)
    (hdeg : ∀ x : Fin d → ℤ, ∀ s : Finset (Sym2 (Fin d → ℤ)),
      ∑ e ∈ s, |c e| * (if x ∈ e then (1 : ℝ) else 0) ≤ D)
    (hvol : ∫⁻ ω : Config (Fin d → ℤ), clusterVol ω o ∂μ ≠ ⊤) :
    ∑' e : Sym2 (Fin d → ℤ), |c e * pivotalFlux μ (sMomentTrunc (quadWeight u) o A) e|
      ≤ 2 * ((A.card : ℝ) * ((∑ i, |u i|) ^ 2 * r ^ 2)) * D *
        (∫⁻ ω : Config (Fin d → ℤ), clusterVol ω o ∂μ).toReal := by
  refine (tsum_abs_pivotalFlux_sMomentTrunc_le (o := o) A (quadWeight u) μ hD ?_ hvol).trans ?_
  · intro x s
    refine (le_of_eq ?_).trans (hdeg x s)
    refine Finset.sum_congr rfl fun e _ => ?_
    exact congrArg (fun t => |c e| * t) (CutoffFlux.ite_inst_irrel _ _ (1 : ℝ) 0)
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  refine mul_le_mul_of_nonneg_right ?_ hD
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  exact sum_quadWeight_le u hr A hA

end PercLib.CriticalLRP

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.abs_sMomentTrunc_le
#print axioms PercLib.CriticalLRP.eventually_sMomentTrunc_cutConfig
#print axioms PercLib.CriticalLRP.tendsto_integral_sMomentTrunc
#print axioms PercLib.CriticalLRP.hasDerivAt_integral_clusterFun
#print axioms PercLib.CriticalLRP.hasDerivAt_integral_sMomentTrunc
#print axioms PercLib.CriticalLRP.hasDerivAt_integral_sMomentTrunc_of_sharpness
#print axioms PercLib.CriticalLRP.hasDerivAt_integral_sMomentTrunc_cutoff
#print axioms PercLib.CriticalLRP.volume_range_edgeLen
#print axioms PercLib.CriticalLRP.ae_hasDerivAt_integral_sMomentTrunc_cutoff
#print axioms PercLib.CriticalLRP.iSup_sMomentTruncENN
#print axioms PercLib.CriticalLRP.lintegral_spatialMomentENN_eq_iSup
#print axioms PercLib.CriticalLRP.tendsto_sMomentTrunc_of_finite
#print axioms PercLib.CriticalLRP.tsum_abs_pivotalFlux_sMomentTrunc_le
#print axioms PercLib.CriticalLRP.quadWeight_le
#print axioms PercLib.CriticalLRP.sum_quadWeight_le
#print axioms PercLib.CriticalLRP.tsum_abs_pivotalFlux_quadWeight_le
#print axioms PercLib.CriticalLRP.ae_hasDerivAt_of_off_edgeLen
#print axioms PercLib.CriticalLRP.lintegral_sMomentTruncENN_eq
#print axioms PercLib.CriticalLRP.ofReal_sMomentTrunc
