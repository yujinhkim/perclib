/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# The truncated spatial moment: a dominator replaces `hunif`

Swarm `smwhc77id`, member `m3`, direction (F): eliminate / weaken the locally-uniform-convergence
hypothesis `hunif` of the infinite-volume Russo exchange for the *spatially weighted* cluster
moment.

## Where `hunif` appears

`CriticalPercLib.CriticalLRP/RussoInf/SpatialExchange.lean` proves the infinite-volume Russo
formula for the truncated spatial moment `sMomentTrunc q o A = ∑_{x ∈ K_o ∩ A} q x`
(source: Hutchcroft, arXiv:2508.18807v1, Lemma I.5.8, TeX `lem:gyration_derivative2`), in the
four conditional forms

* `hasDerivAt_integral_sMomentTrunc`
* `hasDerivAt_integral_sMomentTrunc_of_sharpness`
* `hasDerivAt_integral_sMomentTrunc_cutoff`
* `ae_hasDerivAt_integral_sMomentTrunc_cutoff`

and each of them carries the hypothesis

  `hunif : TendstoLocallyUniformlyOn (fun k r => ∑_{e ∈ S k} c_r(e) · pivot_r(cutFun (S k) g) e) Φ atTop I`

i.e. *local uniform convergence in the parameter of the whole sequence of window pivotal fluxes*.
`RussoInf/DominatedFlux.lean` and `RussoInf/RussoDominated.lean` already replace this hypothesis for
the capped cluster volume `cappedClusterVol` — a functional of the cluster *cardinality* — by a
dominator plus continuity of the limiting flux at one point.  What was missing is the same
replacement for the spatially weighted moment.

## What this file proves

1. `windowFluxOf`, `infFluxOf`, `pivotalWeightOf` — the window pivotal flux, the infinite pivotal
   flux and the *total pivotal weight*, for an **arbitrary** cluster functional `g` bounded by `m`
   (not just `cappedClusterVol`; `windowFluxOf_eq_windowPivotalFlux` shows the definitions
   specialise to `windowPivotalFlux`).

2. `norm_windowFluxOf_le` — **every** window flux, at **every** parameter, is bounded by the total
   pivotal weight.  This is the pointwise half; it uses the single-edge locality bound
   `abs_pivotalFlux_cutFun_le` and summability of the pivotal weights, and it involves no
   uniformity in the window index.

3. `hasDerivAt_integral_clusterFun_of_dominated` — the exchange theorem for a general bounded
   cluster functional with `hunif` **removed**: replaced by

   * `hboundint : IntervalIntegrable (pivotalWeightOf o m π c)` on each parameter interval inside
     `I` (local integrability in the parameter of the total pivotal weight — a *bound*, not a
     convergence statement), and
   * measurability in the parameter of the window fluxes (`hmeasK`), strong measurability of the
     limit flux at `r0` (`hmeasinf`) and its **continuity at the single point** `r0`
     (`hcontinf`).

   Uniformity in `k` is never used: the finite-window identities are integrated against one
   dominating function (`RussoDominated.integral_eq_sub_of_tendsto_hasDerivAt`,
   `RussoDominated.hasDerivAt_of_tendsto_hasDerivAt`).

4. `intervalIntegral_infFluxOf_eq_sub` — the *integrated* form: no continuity of the limit flux at
   all, only local integrability of the total pivotal weight.  The increment of the infinite-volume
   expectation is the integral of the infinite pivotal flux.

5. `hasDerivAt_integral_sMomentTrunc_of_dominated` — the specialisation to `sMomentTrunc`, i.e. the
   `hunif`-free analogue of `hasDerivAt_integral_sMomentTrunc`.  Every non-`hunif` hypothesis of
   that theorem (`hderiv`, `hdom`, the integrand's bound/measurability/cluster dependence and the
   pointwise convergence of window expectations) is reused verbatim; only `hunif` is replaced.

6. `tsum_abs_weight_touch_le` — the *explicit* total pivotal mass: `∑'_e |c e| · P(e touches K_o) ≤ D · E|K_o|`.
   `sMomentWeight` (the total pivotal weight of the truncated spatial moment) and
   `sMomentWeight_le_of_sharpness` — the model bound
   `sMomentWeight ≤ 2 (∑_{x∈A}|q x|) · D · E|K_o|`, so the dominator is an explicit scalar function
   of the parameter and not an abstract `bound`.

7. `hasDerivAt_integral_clusterFun_of_uniformBound` — the same exchange with a *constant* dominator
   `B`, so no integrability hypothesis in the parameter is needed.

8. `hasDerivAt_integral_sMomentTrunc_of_uniformMass` — the sharpest spatial-moment form: the flux
   domination `hdom` is discharged from the per-vertex degree bound and finite expected cluster
   volume, the total pivotal mass bound is the explicit scalar above, and the single remaining
   quantitative input is `2 (∑_{x∈A}|q x|) D_r E_r|K_o| ≤ B` on `I` — the paper's uniform
   total-pivotal-mass bound.

9. `continuousAt_infFlux_of_hunif`, `continuousAt_sMomentInfFlux_of_hunif` — the continuity input of
   the `_of_dominated` theorems is *implied* by `hunif` whenever the window fluxes are continuous in
   the parameter (`TendstoLocallyUniformlyOn.continuousOn`).  So the replacement changes the
   *direction* of the quantitative input (a pointwise bound instead of convergence in the window
   index), it does not add a convergence requirement.

10. `hasDerivAt_integral_sMomentTrunc_of_sharpness_dominated`,
    `hasDerivAt_integral_sMomentTrunc_cutoff_of_uniformMass`,
    `ae_hasDerivAt_integral_sMomentTrunc_cutoff_of_uniformMass` — the `hunif`-free counterparts of
    `hasDerivAt_integral_sMomentTrunc_of_sharpness`, `..._cutoff` and
    `ae_hasDerivAt_integral_sMomentTrunc_cutoff` respectively, including the off-edge-length /
    almost-everywhere passage at the cut-off long-range model.

## What is *not* claimed

* No differentiability statement in `r` of the *genuine* infinite-volume spatial moment
  `spatialMomentENN` is proved here (nor is it claimed in `SpatialExchange`); the object
  differentiated is the truncated moment `sMomentTrunc q o A`, i.e. the paper's
  `∑_{x ∈ K ∩ B_r}`.
* `hvol` (finiteness of the expected cluster volume) is *not* eliminated: it is the sharpness input
  that makes the pivotal weights summable.  It is used, not assumed away.
* `hmeasK` (measurability in the parameter of the window fluxes) is assumed, exactly as in
  `RussoDominated`; in the concrete cut-off model it follows from continuity of `r ↦ (π r e)` and
  of the edge law, which this file does not formalise.
* The uniform total-pivotal-mass bound `hmass` is *not* derived from the model: it is a scalar
  inequality about `D_r` and `E_r|K_o|` that must be supplied (it is the form in which the paper's
  sharpness argument is used).  What *is* proved is that its left-hand side is exactly the total
  pivotal weight dominating every window flux (`sMomentWeight_le_of_sharpness`).
* `hunif` is not proved from the other hypotheses, nor are the other hypotheses proved from
  `hunif`: the two are independent inputs, and what is proved is that `hunif` is not *needed* (and
  that its continuity consequence is implied by it).
* No claim is made about, or use of, the separate printed factor-`1/2` discrepancy in the `T3`
  bound, nor about `BC`/`DF`/`hgap`.
-/
module

public import PercLib.CriticalLRP.RussoInf.SpatialExchange
public import PercLib.CriticalLRP.RussoInf.RussoDominated

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

@[expose] public section

open MeasureTheory Measure Filter Finset
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-! ## 1. Window flux, infinite flux and total pivotal weight for a general cluster functional -/

/-- The pivotal flux of the `k`-th window of a cluster functional `g`, as a function of the
parameter: `∑_{e ∈ S k} c_r(e) · pivot_r(cutFun (S k) g) e`. -/
noncomputable def windowFluxOf (o : V) (g : Config V → ℝ) (S : ℕ → Finset (Sym2 V))
    (π : ℝ → Sym2 V → unitInterval) (c : ℝ → Sym2 V → ℝ) (k : ℕ) (r : ℝ) : ℝ :=
  ∑ e ∈ S k, c r e * pivotalFlux (edgeMeasure (π r)) (cutFun (S k) g) e

/-- The infinite pivotal flux of a cluster functional `g`: `∑'_e c_r(e) · pivot_r(g) e`. -/
noncomputable def infFluxOf (g : Config V → ℝ) (π : ℝ → Sym2 V → unitInterval)
    (c : ℝ → Sym2 V → ℝ) (r : ℝ) : ℝ :=
  ∑' e : Sym2 V, c r e * pivotalFlux (edgeMeasure (π r)) g e

/-- **The total pivotal weight** of a functional bounded by `m`: the sum over all edges of the
single-edge pivotal weight.  This is the function whose *local integrability in the parameter*
replaces `hunif`. -/
noncomputable def pivotalWeightOf (o : V) (m : ℝ) (π : ℝ → Sym2 V → unitInterval)
    (c : ℝ → Sym2 V → ℝ) (r : ℝ) : ℝ :=
  ∑' e : Sym2 V,
    |c r e| * (2 * max m 0 * (edgeMeasure (π r)).real {ω : Config V | e ∈ touchSet ω o})

/-- The generic window flux specialises to `windowPivotalFlux` for the capped
cluster volume: the definitions are the same term. -/
theorem windowFluxOf_eq_windowPivotalFlux (o : V) (p : ℕ) (n' m' : ℝ)
    (S : ℕ → Finset (Sym2 V)) (π : ℝ → Sym2 V → unitInterval) (c : ℝ → Sym2 V → ℝ)
    (k : ℕ) (r : ℝ) :
    windowFluxOf o (cappedClusterVol o p n' m') S π c k r
      = windowPivotalFlux o p n' m' S π c k r := rfl

/-- The generic infinite flux specialises to `infPivotalFlux` for the capped cluster
volume. -/
theorem infFluxOf_eq_infPivotalFlux (o : V) (p : ℕ) (n' m' : ℝ)
    (π : ℝ → Sym2 V → unitInterval) (c : ℝ → Sym2 V → ℝ) (r : ℝ) :
    infFluxOf (cappedClusterVol o p n' m') π c r
      = infPivotalFlux o p n' m' π c r := rfl

/-! ## 2. Every window flux is dominated by the total pivotal weight -/

/-- **The pointwise domination half.**  For a functional `g` bounded by `m` and depending only on
the cluster of `o`, each window pivotal flux is bounded, at every parameter, by the total pivotal
weight.  No uniformity in the window index `k` is involved: the same function majorises all `k`. -/
theorem norm_windowFluxOf_le (o : V) {g : Config V → ℝ} {m : ℝ} (hm : 0 ≤ m)
    (hbound : ∀ ω, |g ω| ≤ m) (hmeas : Measurable g)
    (hdep : ∀ ω η : Config V, cluster ω o = cluster η o → g ω = g η)
    (S : ℕ → Finset (Sym2 V)) (π : ℝ → Sym2 V → unitInterval) (c : ℝ → Sym2 V → ℝ) (r : ℝ)
    (hdom : Summable fun e : Sym2 V =>
      |c r e| * (2 * max m 0 * (edgeMeasure (π r)).real {ω : Config V | e ∈ touchSet ω o}))
    (k : ℕ) :
    ‖windowFluxOf o g S π c k r‖ ≤ pivotalWeightOf o m π c r := by
  classical
  have hm' : (0 : ℝ) ≤ max m 0 := le_max_right _ _
  have hbound' : ∀ ω : Config V, |g ω| ≤ max m 0 :=
    fun ω => (hbound ω).trans (le_max_left m 0)
  have hweight : ∀ e : Sym2 V,
      0 ≤ |c r e| * (2 * max m 0 *
        (edgeMeasure (π r)).real {ω : Config V | e ∈ touchSet ω o}) := fun e =>
    mul_nonneg (abs_nonneg _) (mul_nonneg (by positivity) measureReal_nonneg)
  have h1 : ‖windowFluxOf o g S π c k r‖
      ≤ ∑ e ∈ S k, |c r e| * (2 * max m 0 *
          (edgeMeasure (π r)).real {ω : Config V | e ∈ touchSet ω o}) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
    intro e _
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    exact abs_pivotalFlux_cutFun_le (o := o) (edgeMeasure (π r)) hm'
      hbound' hmeas hdep e
  exact h1.trans (Summable.sum_le_tsum (S k) (fun e _ => hweight e) hdom)

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-! ## 3. The exchange theorem with `hunif` replaced by a dominator -/

/-- **Infinite-volume Russo exchange for a bounded cluster functional, without `hunif`.**

Let `g` be bounded by `m`, measurable, and determined by the cluster of `o`; let `S k` be an
edge-exhausting window sequence, `π` a family of independent edge laws with parameter derivatives
`c`.  Then the expectation of `g` has derivative at `r0` equal to the infinite pivotal flux
`∑'_e c_{r0}(e) · pivot_{r0}(g) e`, provided

* `hdom` : the pivotal weights are summable at every parameter of `I` (the sharpness input),
* `hboundint` : the total pivotal weight `pivotalWeightOf o m π c` is interval integrable on the
  parameter intervals inside `I`,
* `hmeasK` : measurability in the parameter of the window fluxes,
* `hmeasinf`, `hcontinf` : strong measurability at `r0` and **continuity at `r0`** of the limit
  flux,
* `hderiv` : the per-edge derivative of the model.

Compared with `hasDerivAt_integral_of_windowFlux` (equivalently
`hasDerivAt_integral_clusterFun`), the local-uniform-convergence hypothesis `hunif` is gone: the
finite-window identities are integrated against the single function `pivotalWeightOf o m π c`
(`norm_windowFluxOf_le` bounds every window flux by it) and the fundamental theorem of calculus is
applied in its dominated form, `RussoDominated.hasDerivAt_of_tendsto_hasDerivAt`.  Uniformity in
the window index is nowhere used. -/
theorem hasDerivAt_integral_clusterFun_of_dominated
    (o : V) (S : ℕ → Finset (Sym2 V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 V, ∃ n, e ∈ S n)
    (π : ℝ → Sym2 V → unitInterval) (c : ℝ → Sym2 V → ℝ)
    {g : Config V → ℝ} {m : ℝ} (hm : 0 ≤ m) (hbound : ∀ ω, |g ω| ≤ m) (hmeas : Measurable g)
    (hdep : ∀ ω η : Config V, cluster ω o = cluster η o → g ω = g η)
    (hcont : ∀ ω : Config V, Tendsto (fun n => cutFun (S n) g ω) atTop (𝓝 (g ω)))
    {I : Set ℝ} (hI : IsOpen I) {r0 : ℝ} (hr0 : r0 ∈ I)
    (hderiv : ∀ e : Sym2 V, ∀ r ∈ I,
      HasDerivAt (fun r' => ((π r' e : unitInterval) : ℝ)) (c r e) r)
    (hdom : ∀ r ∈ I, Summable fun e : Sym2 V =>
      |c r e| * (2 * max m 0 * (edgeMeasure (π r)).real {ω : Config V | e ∈ touchSet ω o}))
    (hboundint : ∀ a ∈ I, ∀ b ∈ I, IntervalIntegrable (pivotalWeightOf o m π c) volume a b)
    (hmeasK : ∀ k, AEStronglyMeasurable (windowFluxOf o g S π c k) volume)
    (hmeasinf : StronglyMeasurableAtFilter (infFluxOf g π c) (𝓝 r0) volume)
    (hcontinf : ContinuousAt (infFluxOf g π c) r0) :
    HasDerivAt (fun r => ∫ ω : Config V, g ω ∂(edgeMeasure (π r))) (infFluxOf g π c r0) r0 := by
  classical
  have hbound' : ∀ ω : Config V, |g ω| ≤ max m 0 :=
    fun ω => (hbound ω).trans (le_max_left m 0)
  refine RussoDominated.hasDerivAt_of_tendsto_hasDerivAt
    (f := fun k r => ∫ ω : Config V, cutFun (S k) g ω ∂(edgeMeasure (π r)))
    (f' := windowFluxOf o g S π c)
    (g := fun r => ∫ ω : Config V, g ω ∂(edgeMeasure (π r)))
    (g' := infFluxOf g π c) (bound := pivotalWeightOf o m π c)
    hI ?_ hmeasK ?_ hboundint ?_ ?_ hmeasinf hcontinf hr0
  · -- the finite-window Russo identity, in window-flux form
    intro k r hr
    have h := hasDerivAt_integral_cutFun π (c r) (S k) g (fun e => hderiv e r hr)
    have hsum : (∑ e : S k, c r (e : Sym2 V) * pivotalFlux (edgeMeasure (π r))
          (cutFun (S k) g) (e : Sym2 V))
        = windowFluxOf o g S π c k r :=
      Finset.sum_coe_sort (S k) (fun e => c r e * pivotalFlux (edgeMeasure (π r))
        (cutFun (S k) g) e)
    exact h.congr_deriv hsum
  · -- every window flux is dominated by the total pivotal weight
    intro k r hr
    exact norm_windowFluxOf_le o hm hbound hmeas hdep S π c r (hdom r hr) k
  · -- window expectations converge to the infinite-volume expectation
    intro r _
    exact tendsto_integral_cutFun_of_bound S hbound hmeas hcont (edgeMeasure (π r))
  · -- window fluxes converge pointwise to the infinite pivotal series
    intro r hr
    simpa only [windowFluxOf, infFluxOf] using
      tendsto_windowFlux (edgeMeasure (π r)) S (le_max_right m 0) hbound' hmeas hdep hcont
        (c r) (hdom r hr)

/-- **The integrated form of the exchange, with no continuity hypothesis.**

For an interval `[a,b] ⊆ I` on which the total pivotal weight is interval integrable, the increment
of the infinite-volume expectation of `g` is the integral in the parameter of the infinite pivotal
flux.  Nothing about convergence of the window fluxes — locally uniform or otherwise — is assumed,
and neither is continuity of the limit flux. -/
theorem intervalIntegral_infFluxOf_eq_sub
    (o : V) (S : ℕ → Finset (Sym2 V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 V, ∃ n, e ∈ S n)
    (π : ℝ → Sym2 V → unitInterval) (c : ℝ → Sym2 V → ℝ)
    {g : Config V → ℝ} {m : ℝ} (hm : 0 ≤ m) (hbound : ∀ ω, |g ω| ≤ m) (hmeas : Measurable g)
    (hdep : ∀ ω η : Config V, cluster ω o = cluster η o → g ω = g η)
    (hcont : ∀ ω : Config V, Tendsto (fun n => cutFun (S n) g ω) atTop (𝓝 (g ω)))
    {I : Set ℝ} {a b : ℝ} (hsub : Set.uIcc a b ⊆ I)
    (hderiv : ∀ e : Sym2 V, ∀ r ∈ I,
      HasDerivAt (fun r' => ((π r' e : unitInterval) : ℝ)) (c r e) r)
    (hdom : ∀ r ∈ I, Summable fun e : Sym2 V =>
      |c r e| * (2 * max m 0 * (edgeMeasure (π r)).real {ω : Config V | e ∈ touchSet ω o}))
    (hboundint : IntervalIntegrable (pivotalWeightOf o m π c) volume a b)
    (hmeasK : ∀ k, AEStronglyMeasurable (windowFluxOf o g S π c k) volume) :
    ∫ r in a..b, infFluxOf g π c r
      = (∫ ω : Config V, g ω ∂(edgeMeasure (π b)))
        - (∫ ω : Config V, g ω ∂(edgeMeasure (π a))) := by
  classical
  have hbound' : ∀ ω : Config V, |g ω| ≤ max m 0 :=
    fun ω => (hbound ω).trans (le_max_left m 0)
  refine RussoDominated.integral_eq_sub_of_tendsto_hasDerivAt
    (f := fun k r => ∫ ω : Config V, cutFun (S k) g ω ∂(edgeMeasure (π r)))
    (f' := windowFluxOf o g S π c)
    (g := fun r => ∫ ω : Config V, g ω ∂(edgeMeasure (π r)))
    (g' := infFluxOf g π c) (bound := pivotalWeightOf o m π c)
    hsub ?_ hmeasK ?_ hboundint ?_ ?_
  · intro k r hr
    have h := hasDerivAt_integral_cutFun π (c r) (S k) g (fun e => hderiv e r hr)
    have hsum : (∑ e : S k, c r (e : Sym2 V) * pivotalFlux (edgeMeasure (π r))
          (cutFun (S k) g) (e : Sym2 V))
        = windowFluxOf o g S π c k r :=
      Finset.sum_coe_sort (S k) (fun e => c r e * pivotalFlux (edgeMeasure (π r))
        (cutFun (S k) g) e)
    exact h.congr_deriv hsum
  · intro k r hr
    exact norm_windowFluxOf_le o hm hbound hmeas hdep S π c r (hdom r hr) k
  · intro r _
    exact tendsto_integral_cutFun_of_bound S hbound hmeas hcont (edgeMeasure (π r))
  · intro r hr
    simpa only [windowFluxOf, infFluxOf] using
      tendsto_windowFlux (edgeMeasure (π r)) S (le_max_right m 0) hbound' hmeas hdep hcont
        (c r) (hdom r hr)

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-! ## 4. The total pivotal mass as an explicit scalar function of the parameter -/

/-- **The total pivotal mass, bounded explicitly.**  Under the per-vertex degree bound `D` on the
edge weights and finiteness of the expected cluster volume, the pivotal *weight* series
`∑'_e |c e| · P(e touches K_o)` is bounded by `D · E|K_o|`.

This is the quantitative content that `RussoInf/DominatedFlux` and `RussoInf/RussoDominated` leave
implicit: it turns the abstract dominator into an explicit scalar function of the parameter, so that
the hypotheses of the `_of_dominated` theorems become *scalar* inequalities rather than statements
about abstract majorants.  The estimate is the one proved inside `summable_abs_weight_touch`, whose
conclusion only records summability; here the bound itself is exported. -/
theorem tsum_abs_weight_touch_le {o : V} (μ : Measure (Config V)) [IsProbabilityMeasure μ]
    (c : Sym2 V → ℝ) {D : ℝ} (hD : 0 ≤ D)
    (hdeg : ∀ x : V, ∀ u : Finset (Sym2 V),
      ∑ e ∈ u, |c e| * (if x ∈ e then (1 : ℝ) else 0) ≤ D)
    (hvol : ∫⁻ ω, clusterVol ω o ∂μ ≠ ⊤) :
    ∑' e : Sym2 V, |c e| * μ.real {ω : Config V | e ∈ touchSet ω o}
      ≤ D * (∫⁻ ω, clusterVol ω o ∂μ).toReal := by
  classical
  refine Real.tsum_le_of_sum_le (fun e => mul_nonneg (abs_nonneg _) measureReal_nonneg)
    (fun u => ?_)
  -- integrability of the single-edge weight
  have hind : ∀ e : Sym2 V, Integrable (fun ω : Config V =>
      |c e| * (if e ∈ touchSet ω o then (1 : ℝ) else 0)) μ := by
    intro e
    refine Integrable.const_mul (Integrable.of_bound (Measurable.aestronglyMeasurable ?_) 1 ?_) _
    · exact measurable_touchInd e
    · filter_upwards with ω
      rw [Real.norm_eq_abs]
      by_cases h : e ∈ touchSet ω o <;> simp [h]
  have hswap : ∑ e ∈ u, |c e| * μ.real {ω : Config V | e ∈ touchSet ω o}
      = ∫ ω, (∑ e ∈ u, |c e| * (if e ∈ touchSet ω o then (1 : ℝ) else 0)) ∂μ := by
    have hterm : ∀ e : Sym2 V, |c e| * μ.real {ω : Config V | e ∈ touchSet ω o}
        = ∫ ω, |c e| * (if e ∈ touchSet ω o then (1 : ℝ) else 0) ∂μ := by
      intro e
      rw [integral_const_mul, integral_touchInd μ e]
    rw [Finset.sum_congr rfl (fun e _ => hterm e)]
    exact (integral_finsetSum u (fun e _ => hind e)).symm
  have hcardFun : (fun ω : Config V =>
      (((edgeVertices u).filter (fun x => x ∈ cluster ω o)).card : ℝ))
      = fun ω => ∑ x ∈ edgeVertices u, (if x ∈ cluster ω o then (1 : ℝ) else 0) := by
    funext ω
    rw [Finset.card_filter]
    push_cast
    rfl
  have hcardInt : Integrable (fun ω : Config V =>
      D * (((edgeVertices u).filter (fun x => x ∈ cluster ω o)).card : ℝ)) μ := by
    have hmeas : Measurable fun ω : Config V =>
        (((edgeVertices u).filter (fun x => x ∈ cluster ω o)).card : ℝ) := by
      rw [hcardFun]
      exact Finset.measurable_sum _ fun x _ => measurable_clusterInd x
    refine Integrable.const_mul (Integrable.of_bound hmeas.aestronglyMeasurable
      ((edgeVertices u).card : ℝ) ?_) _
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hle : ((edgeVertices u).filter (fun x => x ∈ cluster ω o)).card
        ≤ (edgeVertices u).card := Finset.card_filter_le _ _
    exact_mod_cast hle
  have h3 : ∫ ω, (∑ e ∈ u, |c e| * (if e ∈ touchSet ω o then (1 : ℝ) else 0)) ∂μ
      ≤ ∫ ω, D * (((edgeVertices u).filter (fun x => x ∈ cluster ω o)).card : ℝ) ∂μ := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun ω =>
      Finset.sum_nonneg fun e _ => by positivity) (hcardInt) (Eventually.of_forall fun ω => ?_)
    exact sum_touchSet_weight_le (o := o) c hdeg u ω
  have h4 : ∫ ω, D * (((edgeVertices u).filter (fun x => x ∈ cluster ω o)).card : ℝ) ∂μ
      = D * ∑ x ∈ edgeVertices u, μ.real {ω : Config V | x ∈ cluster ω o} := by
    have hpt : ∀ ω : Config V,
        D * (((edgeVertices u).filter (fun x => x ∈ cluster ω o)).card : ℝ)
          = D * ∑ x ∈ edgeVertices u, (if x ∈ cluster ω o then (1 : ℝ) else 0) := by
      intro ω
      rw [congrFun hcardFun ω]
    calc ∫ ω, D * (((edgeVertices u).filter (fun x => x ∈ cluster ω o)).card : ℝ) ∂μ
        = ∫ ω, D * ∑ x ∈ edgeVertices u,
            (if x ∈ cluster ω o then (1 : ℝ) else 0) ∂μ :=
          integral_congr_ae (Eventually.of_forall hpt)
      _ = D * ∫ ω, ∑ x ∈ edgeVertices u,
            (if x ∈ cluster ω o then (1 : ℝ) else 0) ∂μ := integral_const_mul D _
      _ = D * ∑ x ∈ edgeVertices u, μ.real {ω : Config V | x ∈ cluster ω o} := by
          rw [integral_finsetSum _ (fun x _ => integrable_clusterInd μ x)]
          congr 1
          exact Finset.sum_congr rfl fun x _ => integral_clusterInd μ x
  have h5 : ∑ x ∈ edgeVertices u, μ.real {ω : Config V | x ∈ cluster ω o}
      ≤ (∫⁻ ω, clusterVol ω o ∂μ).toReal := by
    have hsplit : ∑ x ∈ edgeVertices u, μ {ω : Config V | x ∈ cluster ω o}
        ≤ ∫⁻ ω, clusterVol ω o ∂μ := by
      have hL : ∑ x ∈ edgeVertices u, μ {ω : Config V | x ∈ cluster ω o}
          = ∫⁻ ω, ∑ x ∈ edgeVertices u,
              (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ := by
        rw [lintegral_finsetSum]
        · exact Finset.sum_congr rfl fun x _ => (lintegral_clusterIndENN μ x).symm
        · intro x _
          exact measurable_clusterIndENN (o := o) x
      rw [hL]
      refine lintegral_mono fun ω => ?_
      rw [clusterVol_eq_tsum]
      exact ENNReal.sum_le_tsum (edgeVertices u)
    calc ∑ x ∈ edgeVertices u, μ.real {ω : Config V | x ∈ cluster ω o}
        = (∑ x ∈ edgeVertices u, μ {ω : Config V | x ∈ cluster ω o}).toReal := by
          rw [ENNReal.toReal_sum (fun x _ => measure_ne_top _ _)]
          rfl
      _ ≤ (∫⁻ ω, clusterVol ω o ∂μ).toReal := ENNReal.toReal_mono hvol hsplit
  calc ∑ e ∈ u, |c e| * μ.real {ω : Config V | e ∈ touchSet ω o}
      = ∫ ω, (∑ e ∈ u, |c e| * (if e ∈ touchSet ω o then (1 : ℝ) else 0)) ∂μ := hswap
    _ ≤ ∫ ω, D * (((edgeVertices u).filter (fun x => x ∈ cluster ω o)).card : ℝ) ∂μ := h3
    _ = D * ∑ x ∈ edgeVertices u, μ.real {ω : Config V | x ∈ cluster ω o} := h4
    _ ≤ D * (∫⁻ ω, clusterVol ω o ∂μ).toReal :=
        mul_le_mul_of_nonneg_left h5 hD

/-- **The total pivotal weight of the truncated spatial moment**, written as a scalar function of
the parameter: `∑'_e |c_r(e)| · 2 (∑_{x∈A}|q x|) · P_r(e ∈ touchSet · o)`.  This is the dominator
of §2, with `m` specialised to the sup bound `∑_{x∈A}|q x|` of the truncated spatial moment. -/
noncomputable def sMomentWeight (o : V) (A : Finset V) (q : V → ℝ)
    (π : ℝ → Sym2 V → unitInterval) (c : ℝ → Sym2 V → ℝ) (r : ℝ) : ℝ :=
  pivotalWeightOf o (∑ x ∈ A, |q x|) π c r

/-- The infinite pivotal flux of the truncated spatial moment. -/
noncomputable def sMomentInfFlux (o : V) (A : Finset V) (q : V → ℝ)
    (π : ℝ → Sym2 V → unitInterval) (c : ℝ → Sym2 V → ℝ) (r : ℝ) : ℝ :=
  infFluxOf (sMomentTrunc q o A) π c r

/-- **The total pivotal mass of the truncated spatial moment is `2 (∑|q|) D E|K_o|`.**

This is the explicit form of the dominator for the spatial moment: the abstract majorant
`pivotalWeightOf o m π c` equals `2 m` times the weight series bounded in
`tsum_abs_weight_touch_le`.  It is exactly the paper's total-pivotal-mass bound for
`∑_{x∈K∩B_r}⟨x,u⟩²` (with `m = ∑_{x∈A}|q x|` the truncation bound). -/
theorem sMomentWeight_le_of_sharpness {o : V} (A : Finset V) (q : V → ℝ)
    (μ : Measure (Config V)) [IsProbabilityMeasure μ] {c : Sym2 V → ℝ} {D : ℝ} (hD : 0 ≤ D)
    (hdeg : ∀ x : V, ∀ u : Finset (Sym2 V),
      ∑ e ∈ u, |c e| * (if x ∈ e then (1 : ℝ) else 0) ≤ D)
    (hvol : ∫⁻ ω : Config V, clusterVol ω o ∂μ ≠ ⊤) :
    ∑' e : Sym2 V, |c e| * (2 * max (∑ x ∈ A, |q x|) 0 *
        μ.real {ω : Config V | e ∈ touchSet ω o})
      ≤ 2 * (∑ x ∈ A, |q x|) * D * (∫⁻ ω : Config V, clusterVol ω o ∂μ).toReal := by
  classical
  have hm : (0 : ℝ) ≤ ∑ x ∈ A, |q x| := Finset.sum_nonneg fun x _ => abs_nonneg (q x)
  have hsplit : ∑' e : Sym2 V, |c e| * (2 * max (∑ x ∈ A, |q x|) 0 *
        μ.real {ω : Config V | e ∈ touchSet ω o})
      = (2 * max (∑ x ∈ A, |q x|) 0) *
        ∑' e : Sym2 V, |c e| * μ.real {ω : Config V | e ∈ touchSet ω o} := by
    rw [show (∑' e : Sym2 V, |c e| * (2 * max (∑ x ∈ A, |q x|) 0 *
          μ.real {ω : Config V | e ∈ touchSet ω o}))
        = ∑' e : Sym2 V, (2 * max (∑ x ∈ A, |q x|) 0) *
            (|c e| * μ.real {ω : Config V | e ∈ touchSet ω o}) from
      tsum_congr fun e => by ring]
    rw [tsum_mul_left]
  rw [hsplit, max_eq_left hm]
  calc 2 * (∑ x ∈ A, |q x|) *
        ∑' e : Sym2 V, |c e| * μ.real {ω : Config V | e ∈ touchSet ω o}
      ≤ 2 * (∑ x ∈ A, |q x|) * (D * (∫⁻ ω : Config V, clusterVol ω o ∂μ).toReal) :=
        mul_le_mul_of_nonneg_left (tsum_abs_weight_touch_le μ c hD hdeg hvol)
          (by positivity)
    _ = 2 * (∑ x ∈ A, |q x|) * D * (∫⁻ ω : Config V, clusterVol ω o ∂μ).toReal := by ring

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-! ## 5. The same exchange with a constant dominator -/

/-- **Exchange with a constant dominator.**  If the whole window-flux family is bounded by a single
number `B` on the parameter set `I`, then `B` is an interval-integrable dominator and no
integrability hypothesis in the parameter is needed at all.  The remaining inputs are measurability
of the window fluxes in the parameter and continuity of the limit flux at `r0`. -/
theorem hasDerivAt_integral_clusterFun_of_uniformBound
    (o : V) (S : ℕ → Finset (Sym2 V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 V, ∃ n, e ∈ S n)
    (π : ℝ → Sym2 V → unitInterval) (c : ℝ → Sym2 V → ℝ)
    {g : Config V → ℝ} {m : ℝ} (hm : 0 ≤ m) (hbound : ∀ ω, |g ω| ≤ m) (hmeas : Measurable g)
    (hdep : ∀ ω η : Config V, cluster ω o = cluster η o → g ω = g η)
    (hcont : ∀ ω : Config V, Tendsto (fun n => cutFun (S n) g ω) atTop (𝓝 (g ω)))
    {I : Set ℝ} (hI : IsOpen I) {r0 : ℝ} (hr0 : r0 ∈ I)
    (hderiv : ∀ e : Sym2 V, ∀ r ∈ I,
      HasDerivAt (fun r' => ((π r' e : unitInterval) : ℝ)) (c r e) r)
    (hdom : ∀ r ∈ I, Summable fun e : Sym2 V =>
      |c r e| * (2 * max m 0 * (edgeMeasure (π r)).real {ω : Config V | e ∈ touchSet ω o}))
    (B : ℝ) (hB : ∀ (k : ℕ) (r : ℝ), r ∈ I → ‖windowFluxOf o g S π c k r‖ ≤ B)
    (hmeasK : ∀ k, AEStronglyMeasurable (windowFluxOf o g S π c k) volume)
    (hmeasinf : StronglyMeasurableAtFilter (infFluxOf g π c) (𝓝 r0) volume)
    (hcontinf : ContinuousAt (infFluxOf g π c) r0) :
    HasDerivAt (fun r => ∫ ω : Config V, g ω ∂(edgeMeasure (π r))) (infFluxOf g π c r0) r0 := by
  classical
  have hbound' : ∀ ω : Config V, |g ω| ≤ max m 0 :=
    fun ω => (hbound ω).trans (le_max_left m 0)
  refine RussoDominated.hasDerivAt_of_tendsto_hasDerivAt
    (f := fun k r => ∫ ω : Config V, cutFun (S k) g ω ∂(edgeMeasure (π r)))
    (f' := windowFluxOf o g S π c)
    (g := fun r => ∫ ω : Config V, g ω ∂(edgeMeasure (π r)))
    (g' := infFluxOf g π c) (bound := fun _ : ℝ => B)
    hI ?_ hmeasK ?_ ?_ ?_ ?_ hmeasinf hcontinf hr0
  · intro k r hr
    have h := hasDerivAt_integral_cutFun π (c r) (S k) g (fun e => hderiv e r hr)
    have hsum : (∑ e : S k, c r (e : Sym2 V) * pivotalFlux (edgeMeasure (π r))
          (cutFun (S k) g) (e : Sym2 V))
        = windowFluxOf o g S π c k r :=
      Finset.sum_coe_sort (S k) (fun e => c r e * pivotalFlux (edgeMeasure (π r))
        (cutFun (S k) g) e)
    exact h.congr_deriv hsum
  · exact hB
  · intro a _ b _
    exact intervalIntegrable_const
  · intro r _
    exact tendsto_integral_cutFun_of_bound S hbound hmeas hcont (edgeMeasure (π r))
  · intro r hr
    simpa only [windowFluxOf, infFluxOf] using
      tendsto_windowFlux (edgeMeasure (π r)) S (le_max_right m 0) hbound' hmeas hdep hcont
        (c r) (hdom r hr)

/-! ## 6. The truncated spatial moment: `hunif`-free Russo formula -/

/-- **Infinite-volume Russo for the truncated spatial moment, from a dominator.**

This is `hasDerivAt_integral_sMomentTrunc` with the local-uniform-convergence hypothesis `hunif`
replaced by the interval integrability of the explicit total pivotal weight
`sMomentWeight o A q π c` (see `sMomentWeight_le_of_sharpness` for its value) together with
measurability in the parameter of the window fluxes and continuity of the limit flux at `r0`.

Every other hypothesis is literally the one of `hasDerivAt_integral_sMomentTrunc`: in particular
the flux-domination input `hdom` (the sharpness input) and the per-edge derivative `hderiv` are
unchanged. -/
theorem hasDerivAt_integral_sMomentTrunc_of_dominated
    (o : V) (A : Finset V) (q : V → ℝ)
    (S : ℕ → Finset (Sym2 V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 V, ∃ n, e ∈ S n)
    (π : ℝ → Sym2 V → unitInterval) (c : ℝ → Sym2 V → ℝ)
    {I : Set ℝ} (hI : IsOpen I) {r0 : ℝ} (hr0 : r0 ∈ I)
    (hderiv : ∀ e : Sym2 V, ∀ r ∈ I,
      HasDerivAt (fun r' => ((π r' e : unitInterval) : ℝ)) (c r e) r)
    (hdom : ∀ r ∈ I, Summable fun e : Sym2 V =>
      |c r e| * (2 * (∑ x ∈ A, |q x|) *
        (edgeMeasure (π r)).real {ω : Config V | e ∈ touchSet ω o}))
    (hboundint : ∀ a ∈ I, ∀ b ∈ I, IntervalIntegrable (sMomentWeight o A q π c) volume a b)
    (hmeasK : ∀ k, AEStronglyMeasurable (windowFluxOf o (sMomentTrunc q o A) S π c k) volume)
    (hmeasinf : StronglyMeasurableAtFilter (sMomentInfFlux o A q π c) (𝓝 r0) volume)
    (hcontinf : ContinuousAt (sMomentInfFlux o A q π c) r0) :
    HasDerivAt (fun r => ∫ ω : Config V, sMomentTrunc q o A ω ∂(edgeMeasure (π r)))
      (sMomentInfFlux o A q π c r0) r0 := by
  classical
  have hm : (0 : ℝ) ≤ ∑ x ∈ A, |q x| := Finset.sum_nonneg fun x _ => abs_nonneg (q x)
  refine hasDerivAt_integral_clusterFun_of_dominated (o := o) S hSmono hS π c
    (m := ∑ x ∈ A, |q x|) hm (abs_sMomentTrunc_le q o A) (measurable_sMomentTrunc q o A)
    (sMomentTrunc_dep q o A) (fun ω => ?_) hI hr0 hderiv ?_ hboundint hmeasK hmeasinf hcontinf
  · simpa only [cutFun] using tendsto_sMomentTrunc_cutConfig S hSmono hS q o A ω
  · intro r hr
    simpa only [max_eq_left hm] using hdom r hr

/-- **Infinite-volume Russo for the truncated spatial moment, from the paper's total-pivotal-mass
bound.**

The dominator `hdom` and the interval integrability of the total pivotal weight are *discharged*:
`hdom` follows from the per-vertex degree bound `hdeg` and the finiteness of the expected cluster
volume `hvol` (`summable_abs_weight_touch`), and the total pivotal mass is bounded explicitly by
`2 (∑_{x∈A}|q x|) D_r E_r|K_o|` (`sMomentWeight_le_of_sharpness`).  What remains is

* one **scalar** inequality `hmass`, the uniform-in-`r` total-pivotal-mass bound on `I`,
* measurability in `r` of the window fluxes,
* continuity of the infinite pivotal flux at the single parameter `r0`.

No statement about the sequence of window fluxes — convergence, uniformity, or otherwise — is
assumed: with a constant dominator the exchange is the dominated form of the limit-of-derivatives
theorem. -/
theorem hasDerivAt_integral_sMomentTrunc_of_uniformMass
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
    (B : ℝ)
    (hmass : ∀ r ∈ I, 2 * (∑ x ∈ A, |q x|) * D r *
      (∫⁻ ω : Config V, clusterVol ω o ∂(edgeMeasure (π r))).toReal ≤ B)
    (hmeasK : ∀ k, AEStronglyMeasurable (windowFluxOf o (sMomentTrunc q o A) S π c k) volume)
    (hmeasinf : StronglyMeasurableAtFilter (sMomentInfFlux o A q π c) (𝓝 r0) volume)
    (hcontinf : ContinuousAt (sMomentInfFlux o A q π c) r0) :
    HasDerivAt (fun r => ∫ ω : Config V, sMomentTrunc q o A ω ∂(edgeMeasure (π r)))
      (sMomentInfFlux o A q π c r0) r0 := by
  classical
  have hm : (0 : ℝ) ≤ ∑ x ∈ A, |q x| := Finset.sum_nonneg fun x _ => abs_nonneg (q x)
  have hdom : ∀ r ∈ I, Summable fun e : Sym2 V =>
      |c r e| * (2 * max (∑ x ∈ A, |q x|) 0 *
        (edgeMeasure (π r)).real {ω : Config V | e ∈ touchSet ω o}) := by
    intro r hr
    have hbase := summable_abs_weight_touch (o := o) (edgeMeasure (π r)) (c r)
      (hD r hr) (hdeg r hr) (hvol r hr)
    refine (hbase.mul_left (2 * max (∑ x ∈ A, |q x|) 0)).congr fun e => ?_
    ring
  have hB : ∀ (k : ℕ) (r : ℝ), r ∈ I → ‖windowFluxOf o (sMomentTrunc q o A) S π c k r‖ ≤ B := by
    intro k r hr
    have h1 : ‖windowFluxOf o (sMomentTrunc q o A) S π c k r‖ ≤ sMomentWeight o A q π c r :=
      norm_windowFluxOf_le (o := o) (g := sMomentTrunc q o A) (m := ∑ x ∈ A, |q x|) hm
        (abs_sMomentTrunc_le q o A) (measurable_sMomentTrunc q o A) (sMomentTrunc_dep q o A)
        S π c r (hdom r hr) k
    have h2 : sMomentWeight o A q π c r ≤
        2 * (∑ x ∈ A, |q x|) * D r *
          (∫⁻ ω : Config V, clusterVol ω o ∂(edgeMeasure (π r))).toReal :=
      sMomentWeight_le_of_sharpness A q (edgeMeasure (π r)) (hD r hr) (hdeg r hr) (hvol r hr)
    exact (h1.trans h2).trans (hmass r hr)
  exact hasDerivAt_integral_clusterFun_of_uniformBound (o := o) S hSmono hS π c
    (m := ∑ x ∈ A, |q x|) hm (abs_sMomentTrunc_le q o A) (measurable_sMomentTrunc q o A)
    (sMomentTrunc_dep q o A) (fun ω => by
      simpa only [cutFun] using tendsto_sMomentTrunc_cutConfig S hSmono hS q o A ω)
    hI hr0 hderiv hdom B hB hmeasK hmeasinf hcontinf

end PercLib.CriticalLRP

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.windowFluxOf_eq_windowPivotalFlux
#print axioms PercLib.CriticalLRP.infFluxOf_eq_infPivotalFlux
#print axioms PercLib.CriticalLRP.norm_windowFluxOf_le
#print axioms PercLib.CriticalLRP.hasDerivAt_integral_clusterFun_of_dominated
#print axioms PercLib.CriticalLRP.intervalIntegral_infFluxOf_eq_sub
#print axioms PercLib.CriticalLRP.tsum_abs_weight_touch_le
#print axioms PercLib.CriticalLRP.sMomentWeight_le_of_sharpness
#print axioms PercLib.CriticalLRP.hasDerivAt_integral_clusterFun_of_uniformBound
#print axioms PercLib.CriticalLRP.hasDerivAt_integral_sMomentTrunc_of_dominated
#print axioms PercLib.CriticalLRP.hasDerivAt_integral_sMomentTrunc_of_uniformMass

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-! ## 7. The continuity input is implied by `hunif` -/

/-- **Continuity of the limit flux is a consequence of `hunif`.**

The `_of_dominated` theorems replace `hunif` by continuity of the limit flux at the single point
`r0`.  That is not an extra assumption *in addition to* local uniform convergence: a locally uniform
limit of functions continuous in the parameter is itself continuous
(`TendstoLocallyUniformlyOn.continuousOn`).  What is genuinely new in the replacement is only the
*direction* of the quantitative input: a pointwise bound on the flux family obtained from the
model's degree bound and finite expected cluster volume, instead of convergence in the window index.
-/
theorem continuousAt_infFlux_of_hunif {o : V} {g : Config V → ℝ} (S : ℕ → Finset (Sym2 V))
    (π : ℝ → Sym2 V → unitInterval) (c : ℝ → Sym2 V → ℝ) {Φ : ℝ → ℝ}
    {I : Set ℝ} (hI : IsOpen I) {r0 : ℝ} (hr0 : r0 ∈ I)
    (hunif : TendstoLocallyUniformlyOn (fun k r => windowFluxOf o g S π c k r) Φ atTop I)
    (hcontK : ∀ k, ContinuousOn (fun r => windowFluxOf o g S π c k r) I) :
    ContinuousAt Φ r0 :=
  (hunif.continuousOn (Eventually.of_forall hcontK).frequently).continuousAt
    (hI.mem_nhds hr0)

/-- The same statement for the truncated spatial moment: under `hunif` the infinite pivotal flux
`sMomentInfFlux` is continuous at every point of the (open) parameter set, so the continuity input
of `hasDerivAt_integral_sMomentTrunc_of_dominated` holds. -/
theorem continuousAt_sMomentInfFlux_of_hunif {o : V} (A : Finset V) (q : V → ℝ)
    (S : ℕ → Finset (Sym2 V)) (π : ℝ → Sym2 V → unitInterval) (c : ℝ → Sym2 V → ℝ)
    {I : Set ℝ} (hI : IsOpen I) {r0 : ℝ} (hr0 : r0 ∈ I)
    (hunif : TendstoLocallyUniformlyOn
      (fun k r => windowFluxOf o (sMomentTrunc q o A) S π c k r) (sMomentInfFlux o A q π c) atTop I)
    (hcontK : ∀ k, ContinuousOn (fun r => windowFluxOf o (sMomentTrunc q o A) S π c k r) I) :
    ContinuousAt (sMomentInfFlux o A q π c) r0 :=
  continuousAt_infFlux_of_hunif S π c hI hr0 hunif hcontK

/-! ## 8. Instantiation at the cut-off long-range model on `ℤ^d` -/

variable {d : ℕ}

/-- **Infinite-volume Russo for the truncated spatial moment of the cut-off model, without `hunif`.**

This is `hasDerivAt_integral_sMomentTrunc_cutoff` with `hunif` removed.  Everything the repository
can discharge is discharged: the edge-probability derivatives
(`CutoffFlux.cutoffEdgeDeriv_hasDerivAt`), the per-vertex degree bound
(`CutoffFlux.cutoff_edgeDeriv_degree`), the flux domination (from `hvol`) and the total pivotal mass
bound (`sMomentWeight_le_of_sharpness`, giving the explicit bound
`2 (∑_{x∈A}|q x|) · β K' (2⌈r⌉₊+1)^d · E_r|K_o|`).  What remains is

* `hmass` : that explicit scalar function is bounded by `B` on `I` (the paper's uniform
  total-pivotal-mass bound — a bound, not a convergence),
* `hmeasK` : measurability in the parameter of the window fluxes,
* `hmeasinf`, `hcontinf` : measurability and continuity at `r0` of the limit flux — and `hcontinf`
  is implied by `hunif` whenever the window fluxes are continuous in `r`
  (`continuousAt_sMomentInfFlux_of_hunif`). -/
theorem hasDerivAt_integral_sMomentTrunc_cutoff_of_uniformMass
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
    (B : ℝ)
    (hmass : ∀ r ∈ I, 2 * (∑ x ∈ A, |q x|) *
        (β * K' * ((2 * ⌈r⌉₊ + 1) ^ d : ℕ)) *
        (∫⁻ ω : Config (Fin d → ℤ), clusterVol ω o
          ∂(edgeMeasure (cutoffPiFamily (d := d) β K hβ hprof r))).toReal ≤ B)
    (hmeasK : ∀ k, AEStronglyMeasurable (windowFluxOf o (sMomentTrunc q o A) S
      (cutoffPiFamily (d := d) β K hβ hprof)
      (fun r e => CutoffFlux.cutoffEdgeDeriv K β K' r e) k) volume)
    (hmeasinf : StronglyMeasurableAtFilter
      (sMomentInfFlux (V := Fin d → ℤ) o A q
        (cutoffPiFamily (d := d) β K hβ hprof)
        (fun r e => CutoffFlux.cutoffEdgeDeriv K β K' r e)) (𝓝 r0) volume)
    (hcontinf : ContinuousAt
      (sMomentInfFlux (V := Fin d → ℤ) o A q
        (cutoffPiFamily (d := d) β K hβ hprof)
        (fun r e => CutoffFlux.cutoffEdgeDeriv K β K' r e)) r0) :
    HasDerivAt (fun r => ∫ ω : Config (Fin d → ℤ), sMomentTrunc (V := Fin d → ℤ) q o A ω
      ∂(edgeMeasure (cutoffPiFamily (d := d) β K hβ hprof r)))
      (sMomentInfFlux (V := Fin d → ℤ) o A q
        (cutoffPiFamily (d := d) β K hβ hprof)
        (fun r e => CutoffFlux.cutoffEdgeDeriv K β K' r e) r0) r0 := by
  classical
  refine hasDerivAt_integral_sMomentTrunc_of_uniformMass (V := Fin d → ℤ) o A q S hSmono hS
    (cutoffPiFamily (d := d) β K hβ hprof)
    (fun r e => CutoffFlux.cutoffEdgeDeriv K β K' r e)
    (fun r => β * K' * ((2 * ⌈r⌉₊ + 1) ^ d : ℕ)) hI hr0 ?_ ?_ ?_ hvol B hmass
    hmeasK hmeasinf hcontinf
  · intro e r hr
    have h := CutoffFlux.cutoffEdgeDeriv_hasDerivAt (K := K) (β := β) (K' := K') (r := r)
      (e := e) (hne r hr e) (hderivK r hr)
    simpa only [cutoffPiFamily_coe] using h
  · intro r _
    positivity
  · intro r _ x u
    have h := CutoffFlux.cutoff_edgeDeriv_degree (d := d) (K := K) (β := β) (K' := K')
      (r := r) hβ hK' (fun e => longRangeEdgeProbability_nonneg hβ (hprof r e))
      (fun e => longRangeEdgeProbability_le_one hβ (hprof r e)) x u
    refine (le_of_eq ?_).trans h
    refine Finset.sum_congr rfl fun e _ => ?_
    exact congrArg (fun t => |CutoffFlux.cutoffEdgeDeriv K β K' r e| * t)
      (CutoffFlux.ite_inst_irrel _ _ (1 : ℝ) 0)

end PercLib.CriticalLRP

/-! ## Axiom audit (continued) -/

#print axioms PercLib.CriticalLRP.continuousAt_infFlux_of_hunif
#print axioms PercLib.CriticalLRP.continuousAt_sMomentInfFlux_of_hunif
#print axioms PercLib.CriticalLRP.hasDerivAt_integral_sMomentTrunc_cutoff_of_uniformMass

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-! ## 9. Discharging the flux domination from the paper's two inputs -/

/-- **Infinite-volume Russo for the truncated spatial moment, `hunif`-free and with the flux
domination discharged from the paper's two inputs.**

This is the `hunif`-free analogue of `hasDerivAt_integral_sMomentTrunc_of_sharpness`: the
summability input `hdom` is derived from the per-vertex degree bound `hdeg` and the finiteness of the
expected cluster volume `hvol` (via `summable_abs_weight_touch`), so the only remaining hypotheses
are the interval integrability of the explicit total pivotal weight `sMomentWeight`, measurability in
the parameter of the window fluxes, and measurability/continuity at `r0` of the limit flux. -/
theorem hasDerivAt_integral_sMomentTrunc_of_sharpness_dominated
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
    (hboundint : ∀ a ∈ I, ∀ b ∈ I, IntervalIntegrable (sMomentWeight o A q π c) volume a b)
    (hmeasK : ∀ k, AEStronglyMeasurable (windowFluxOf o (sMomentTrunc q o A) S π c k) volume)
    (hmeasinf : StronglyMeasurableAtFilter (sMomentInfFlux o A q π c) (𝓝 r0) volume)
    (hcontinf : ContinuousAt (sMomentInfFlux o A q π c) r0) :
    HasDerivAt (fun r => ∫ ω : Config V, sMomentTrunc q o A ω ∂(edgeMeasure (π r)))
      (sMomentInfFlux o A q π c r0) r0 := by
  classical
  refine hasDerivAt_integral_sMomentTrunc_of_dominated o A q S hSmono hS π c hI hr0 hderiv
    (fun r hr => ?_) hboundint hmeasK hmeasinf hcontinf
  have hbase := summable_abs_weight_touch (o := o) (edgeMeasure (π r)) (c r)
    (hD r hr) (hdeg r hr) (hvol r hr)
  refine (hbase.mul_left (2 * (∑ x ∈ A, |q x|))).congr fun e => ?_
  ring

/-! ## 10. The almost-everywhere form at the cut-off model -/

variable {d : ℕ}

/-- **The `hunif`-free Russo formula for the truncated spatial moment of the cut-off model, almost
everywhere in the parameter.**

The a.e. passage is orthogonal to the removal of `hunif`: off the (countable, Lebesgue-null) set of
edge lengths the cut-off edge probability is differentiable, so the exchange applies at every point
of `I` outside that set, hence almost everywhere (`ae_hasDerivAt_of_off_edgeLen`).  Note that the
continuity and mass hypotheses are now stated at every parameter of `I`, which is what the a.e.
conclusion needs; each of them is a single-function statement. -/
theorem ae_hasDerivAt_integral_sMomentTrunc_cutoff_of_uniformMass
    (o : Fin d → ℤ) (A : Finset (Fin d → ℤ)) (q : (Fin d → ℤ) → ℝ)
    (S : ℕ → Finset (Sym2 (Fin d → ℤ))) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 (Fin d → ℤ), ∃ n, e ∈ S n)
    {β K' : ℝ} (hβ : 0 ≤ β) (hK' : 0 ≤ K') {K : ℝ → ℝ}
    (hprof : ∀ (r : ℝ) (e : Sym2 (Fin d → ℤ)),
      0 ≤ FiniteVolume.cutoffProfile K r (FiniteVolume.edgeLen e))
    {I : Set ℝ} (hI : IsOpen I)
    (hIoff : ∀ r ∈ I, r ∉ Set.range (fun e : Sym2 (Fin d → ℤ) =>
      (FiniteVolume.edgeLen e : ℝ)))
    (hderivK : ∀ r ∈ I, HasDerivAt K (-K') r)
    (hvol : ∀ r ∈ I, ∫⁻ ω : Config (Fin d → ℤ), clusterVol ω o
      ∂(edgeMeasure (cutoffPiFamily (d := d) β K hβ hprof r)) ≠ ⊤)
    (B : ℝ)
    (hmass : ∀ r ∈ I, 2 * (∑ x ∈ A, |q x|) *
        (β * K' * ((2 * ⌈r⌉₊ + 1) ^ d : ℕ)) *
        (∫⁻ ω : Config (Fin d → ℤ), clusterVol ω o
          ∂(edgeMeasure (cutoffPiFamily (d := d) β K hβ hprof r))).toReal ≤ B)
    (hmeasK : ∀ k, AEStronglyMeasurable (windowFluxOf o (sMomentTrunc q o A) S
      (cutoffPiFamily (d := d) β K hβ hprof)
      (fun r e => CutoffFlux.cutoffEdgeDeriv K β K' r e) k) volume)
    (hmeasinf : ∀ r ∈ I, StronglyMeasurableAtFilter
      (sMomentInfFlux (V := Fin d → ℤ) o A q
        (cutoffPiFamily (d := d) β K hβ hprof)
        (fun r e => CutoffFlux.cutoffEdgeDeriv K β K' r e)) (𝓝 r) volume)
    (hcontinf : ∀ r ∈ I, ContinuousAt
      (sMomentInfFlux (V := Fin d → ℤ) o A q
        (cutoffPiFamily (d := d) β K hβ hprof)
        (fun r e => CutoffFlux.cutoffEdgeDeriv K β K' r e)) r) :
    ∀ᵐ r ∂(volume : Measure ℝ), r ∈ I →
      HasDerivAt (fun r' => ∫ ω : Config (Fin d → ℤ),
        sMomentTrunc (V := Fin d → ℤ) q o A ω
        ∂(edgeMeasure (cutoffPiFamily (d := d) β K hβ hprof r')))
        (sMomentInfFlux (V := Fin d → ℤ) o A q
          (cutoffPiFamily (d := d) β K hβ hprof)
          (fun r e => CutoffFlux.cutoffEdgeDeriv K β K' r e) r) r :=
  ae_hasDerivAt_of_off_edgeLen (countable_range_edgeLen d) fun r hr _ =>
    hasDerivAt_integral_sMomentTrunc_cutoff_of_uniformMass o A q S hSmono hS hβ hK' hprof
      hI hr hderivK (fun r' hr' e hc => hIoff r' hr' ⟨e, hc⟩) hvol B hmass hmeasK
      (hmeasinf r hr) (hcontinf r hr)

end PercLib.CriticalLRP

/-! ## Axiom audit (continued) -/

#print axioms PercLib.CriticalLRP.hasDerivAt_integral_sMomentTrunc_of_sharpness_dominated
#print axioms PercLib.CriticalLRP.ae_hasDerivAt_integral_sMomentTrunc_cutoff_of_uniformMass

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- **Infinite-volume Russo for the truncated spatial moment from uniform bounds on the two
sharpness quantities.**

The scalar mass hypothesis `hmass` of `hasDerivAt_integral_sMomentTrunc_of_uniformMass` is a product
of the degree constant `D_r` and the expected cluster volume `E_r|K_o|`; it therefore follows from a
bound on each factor separately, which is the form in which sharpness supplies them (finite expected
cluster volume, uniformly on the parameter set, together with the degree bound).  After this
reduction the quantitative inputs are exactly

* `hDle` : `D_r ≤ Dmax` on `I`,
* `hV` : `E_r|K_o| ≤ V` on `I` (finiteness *and* a uniform bound of the expected cluster volume),
* `hvol`, the a.e.-finiteness form of the same input, used to make the pivotal weights summable,

plus measurability in `r` of the window fluxes and continuity of the limit flux at `r0`.  No
statement about the sequence of window fluxes is assumed. -/
theorem hasDerivAt_integral_sMomentTrunc_of_uniformVolume
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
    (Dmax V₀ : ℝ) (hDle : ∀ r ∈ I, D r ≤ Dmax)
    (hV : ∀ r ∈ I, (∫⁻ ω : Config V, clusterVol ω o ∂(edgeMeasure (π r))).toReal ≤ V₀)
    (hmeasK : ∀ k, AEStronglyMeasurable (windowFluxOf o (sMomentTrunc q o A) S π c k) volume)
    (hmeasinf : StronglyMeasurableAtFilter (sMomentInfFlux o A q π c) (𝓝 r0) volume)
    (hcontinf : ContinuousAt (sMomentInfFlux o A q π c) r0) :
    HasDerivAt (fun r => ∫ ω : Config V, sMomentTrunc q o A ω ∂(edgeMeasure (π r)))
      (sMomentInfFlux o A q π c r0) r0 := by
  classical
  have hm : (0 : ℝ) ≤ ∑ x ∈ A, |q x| := Finset.sum_nonneg fun x _ => abs_nonneg (q x)
  refine hasDerivAt_integral_sMomentTrunc_of_uniformMass o A q S hSmono hS π c D hI hr0 hderiv
    hD hdeg hvol (B := 2 * (∑ x ∈ A, |q x|) * Dmax * V₀) (fun r hr => ?_) hmeasK hmeasinf
    hcontinf
  have hstep1 : 2 * (∑ x ∈ A, |q x|) * D r ≤ 2 * (∑ x ∈ A, |q x|) * Dmax :=
    mul_le_mul_of_nonneg_left (hDle r hr) (by positivity)
  have hDmax : (0 : ℝ) ≤ Dmax := (hD r hr).trans (hDle r hr)
  exact mul_le_mul hstep1 (hV r hr) ENNReal.toReal_nonneg (by positivity)

end PercLib.CriticalLRP

#print axioms PercLib.CriticalLRP.hasDerivAt_integral_sMomentTrunc_of_uniformVolume
