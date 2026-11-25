/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Infinite-volume Russo for the capped cluster volume: dominator replaces `hunif`

`CriticalPercLib.CriticalLRP/RussoInf/Exchange.lean` proves the infinite-volume Russo identity
for the capped cluster-volume functional conditionally on a hypothesis

  `hunif : TendstoLocallyUniformlyOn (fun k r => <window pivotal flux k r>) Φ atTop I`

(`hasDerivAt_integral_of_windowFlux`, `hasDerivAt_integral_cappedClusterVol`,
`hasDerivAt_integral_cappedClusterVol_of_sharpness`, `hasDerivAt_integral_cappedClusterVol_cutoff`).
Its header states the remaining gap as a uniform-in-parameter estimate on the *tails* of the window
flux, obtained in the paper from "the standard consequence of sharpness".

This file proves that `hunif` is **strictly stronger than necessary**.  The finite-window identities
`d/dr ψ_k = (window pivotal flux k)` are integrated in `r` against one *dominating* function, so
that dominated convergence plus the fundamental theorem of calculus identifies the derivative of the
limit at every point at which the limiting flux is continuous.  The uniformity in `k` of the
convergence is never used; only a bound.

Concretely, for the canonical capped cluster volume the dominator can be taken to be the *canonical
total pivotal weight*

  `fluxWeight r = ∑'_e |c r e| * (2 * max m' 0 * P_r (e ∈ touchSet · o))`,

because every window flux is bounded by it (`norm_windowPivotalFlux_le`), which is exactly the
`D · E|K_o|` bound of the paper's finite-pivotal-flux input.  Hence the hypotheses of
`hasDerivAt_integral_cappedClusterVol_of_dominated` are

* `hdom`      : summability of the pivotal weights at every parameter (the existing input),
* `hboundint` : **local integrability in the parameter of the canonical total pivotal weight**,
* `hmeas`     : measurability in the parameter of each window flux,
* `hinf`, `hcont` : strong measurability of the infinite pivotal series and its **continuity at the
  single parameter `r0`**.

Compared with `hunif` these are weaker: a locally uniform limit of continuous window fluxes supplies
all four (the bound on a compact parameter interval, measurability, and continuity of the limit), but
none of them says anything about uniformity of the convergence in the window index.  In particular
`hboundint` is a *bound*, of the type sharpness actually yields, and `hcont` is a statement about a
single function, not about a sequence of functions.

Everything else is discharged from the repository: the finite-window Russo identity
(`hasDerivAt_integral_cutFun`), pointwise convergence of the window expectations
(`tendsto_integral_cutFun`) and pointwise convergence of the window fluxes (`tendsto_windowFlux`).
-/
module

public import PercLib.CriticalLRP.RussoInf.Exchange
public import PercLib.CriticalLRP.RussoInf.CutoffFlux
public import PercLib.CriticalLRP.RussoInf.DominatedFlux

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open MeasureTheory Measure Filter Finset
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- The pivotal flux of the `k`-th window of the capped cluster-volume functional, as a function of
the parameter: `∑_{e ∈ S k} c_r(e) · pivot_r(cutFun (S k) g) e`. -/
noncomputable def windowPivotalFlux (o : V) (p : ℕ) (n' m' : ℝ) (S : ℕ → Finset (Sym2 V))
    (π : ℝ → Sym2 V → unitInterval) (c : ℝ → Sym2 V → ℝ) (k : ℕ) (r : ℝ) : ℝ :=
  ∑ e ∈ S k, c r e * pivotalFlux (edgeMeasure (π r))
    (cutFun (S k) (cappedClusterVol o p n' m')) e

/-- The infinite pivotal flux of the capped cluster-volume functional:
`∑'_e c_r(e) · pivot_r(g) e`, the derivative predicted by the infinite-volume Russo formula. -/
noncomputable def infPivotalFlux (o : V) (p : ℕ) (n' m' : ℝ)
    (π : ℝ → Sym2 V → unitInterval) (c : ℝ → Sym2 V → ℝ) (r : ℝ) : ℝ :=
  ∑' e : Sym2 V, c r e * pivotalFlux (edgeMeasure (π r)) (cappedClusterVol o p n' m') e

/-- **The canonical dominator.**  `2 · max m' 0` times the total pivotal weight of the capped
cluster-volume functional at parameter `r`.  This is the function whose *local integrability in the
parameter* replaces the local uniformity hypothesis `hunif`. -/
noncomputable def fluxWeight (o : V) (m' : ℝ)
    (π : ℝ → Sym2 V → unitInterval) (c : ℝ → Sym2 V → ℝ) (r : ℝ) : ℝ :=
  ∑' e : Sym2 V,
    |c r e| * (2 * max m' 0 * (edgeMeasure (π r)).real {ω : Config V | e ∈ touchSet ω o})

/-- Each window flux is dominated by the canonical total pivotal weight. -/
theorem norm_windowPivotalFlux_le (o : V) (p : ℕ) (n' m' : ℝ) (hm' : 0 ≤ m')
    (S : ℕ → Finset (Sym2 V)) (π : ℝ → Sym2 V → unitInterval) (c : ℝ → Sym2 V → ℝ) (r : ℝ)
    (hdom : Summable fun e : Sym2 V =>
      |c r e| * (2 * max m' 0 * (edgeMeasure (π r)).real {ω : Config V | e ∈ touchSet ω o}))
    (k : ℕ) :
    ‖windowPivotalFlux o p n' m' S π c k r‖ ≤ fluxWeight o m' π c r := by
  classical
  have hm : (0 : ℝ) ≤ max m' 0 := le_max_right _ _
  have hweight : ∀ e : Sym2 V,
      0 ≤ |c r e| * (2 * max m' 0 *
        (edgeMeasure (π r)).real {ω : Config V | e ∈ touchSet ω o}) := fun e =>
    mul_nonneg (abs_nonneg _) (mul_nonneg (by positivity) measureReal_nonneg)
  have h1 : ‖windowPivotalFlux o p n' m' S π c k r‖
      ≤ ∑ e ∈ S k, |c r e| * (2 * max m' 0 *
          (edgeMeasure (π r)).real {ω : Config V | e ∈ touchSet ω o}) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum ?_)
    intro e _
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    exact abs_pivotalFlux_cutFun_le (o := o) (edgeMeasure (π r)) hm
      (cappedClusterVol_bound o p n' m' hm') (measurable_cappedClusterVol o p n' m')
      (cappedClusterVol_dep o p n' m') e
  exact h1.trans (Summable.sum_le_tsum (S k) (fun e _ => hweight e) hdom)

/-- **Infinite-volume Russo for the capped cluster volume, from a dominator.**

The derivative of `r ↦ ∫ cappedClusterVol dP_r` at `r0` is the infinite pivotal flux
`∑'_e c_{r0}(e) · pivot_{r0}(g) e`.

The hypothesis `hunif` of `hasDerivAt_integral_cappedClusterVol` (local uniform convergence of the
window fluxes) is replaced by a dominator for the window fluxes together with continuity of the
limiting flux at `r0`.  Both are consequences of `hunif` (when the window fluxes are continuous in
the parameter), and neither is a uniform-convergence statement. -/
theorem hasDerivAt_integral_cappedClusterVol_of_dominated
    (o : V) (p : ℕ) (n' m' : ℝ) (hm' : 0 ≤ m')
    (S : ℕ → Finset (Sym2 V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 V, ∃ n, e ∈ S n)
    (π : ℝ → Sym2 V → unitInterval) (c : ℝ → Sym2 V → ℝ)
    {I : Set ℝ} (hI : IsOpen I) {r0 : ℝ} (hr0 : r0 ∈ I)
    (hderiv : ∀ e : Sym2 V, ∀ r ∈ I,
      HasDerivAt (fun r' => ((π r' e : unitInterval) : ℝ)) (c r e) r)
    (hdom : ∀ r ∈ I, Summable fun e : Sym2 V =>
      |c r e| * (2 * max m' 0 * (edgeMeasure (π r)).real {ω : Config V | e ∈ touchSet ω o}))
    (hboundint : ∀ a ∈ I, ∀ b ∈ I, IntervalIntegrable (fluxWeight o m' π c) volume a b)
    (hmeas : ∀ k, AEStronglyMeasurable (windowPivotalFlux o p n' m' S π c k) volume)
    (hinf : StronglyMeasurableAtFilter (infPivotalFlux o p n' m' π c) (𝓝 r0) volume)
    (hcont : ContinuousAt (infPivotalFlux o p n' m' π c) r0) :
    HasDerivAt (fun r => ∫ ω : Config V, cappedClusterVol o p n' m' ω ∂(edgeMeasure (π r)))
      (infPivotalFlux o p n' m' π c r0) r0 := by
  classical
  have hm0 : (0 : ℝ) ≤ max m' 0 := le_max_right _ _
  refine RussoDominated.hasDerivAt_of_tendsto_hasDerivAt
    (f := fun k r => ∫ ω : Config V, cutFun (S k) (cappedClusterVol o p n' m') ω
      ∂(edgeMeasure (π r)))
    (f' := windowPivotalFlux o p n' m' S π c)
    (g := fun r => ∫ ω : Config V, cappedClusterVol o p n' m' ω ∂(edgeMeasure (π r)))
    (g' := infPivotalFlux o p n' m' π c) (bound := fluxWeight o m' π c)
    hI ?_ hmeas ?_ hboundint ?_ ?_ hinf hcont hr0
  · -- the finite-window Russo identity, in window-flux form
    intro k r hr
    have h := hasDerivAt_integral_cutFun π (c r) (S k) (cappedClusterVol o p n' m')
      (fun e => hderiv e r hr)
    have hsum : (∑ e : S k, c r (e : Sym2 V) * pivotalFlux (edgeMeasure (π r))
          (cutFun (S k) (cappedClusterVol o p n' m')) (e : Sym2 V))
        = windowPivotalFlux o p n' m' S π c k r :=
      Finset.sum_coe_sort (S k) (fun e => c r e * pivotalFlux (edgeMeasure (π r))
        (cutFun (S k) (cappedClusterVol o p n' m')) e)
    exact h.congr_deriv hsum
  · -- the canonical dominator bounds every window flux
    intro k r hr
    exact norm_windowPivotalFlux_le o p n' m' hm' S π c r (hdom r hr) k
  · -- window expectations converge to the infinite-volume expectation
    intro r _
    exact tendsto_integral_cutFun S hSmono hS o p n' m' hm' (edgeMeasure (π r))
  · -- window fluxes converge pointwise to the infinite pivotal series
    intro r hr
    exact tendsto_windowFlux (m := max m' 0) (edgeMeasure (π r)) S hm0
      (cappedClusterVol_bound o p n' m' hm') (measurable_cappedClusterVol o p n' m')
      (cappedClusterVol_dep o p n' m')
      (fun ω => tendsto_cappedClusterVol_cutConfig S hSmono hS o p n' m' ω)
      (c r) (hdom r hr)

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- **The integrated infinite-volume Russo identity for the capped cluster volume.**

For any parameter interval `[a,b] ⊆ I` on which a locally integrable dominator for the window fluxes
is available, the *increment* of the infinite-volume expectation equals the integral of the infinite
pivotal flux with respect to the parameter:

`∫ r in a..b, (∑'_e c_r(e) pivot_r(g) e) = ψ b - ψ a`.

No continuity, and no local uniformity, of anything is required: this is the a.e./integrated form of
`hasDerivAt_integral_cappedClusterVol_of_dominated`, and it already determines `ψ` up to a constant
from the infinite pivotal flux.  (In particular `ψ` is absolutely continuous in `r` on `I` whenever
`fluxWeight` is locally integrable, with derivative the infinite pivotal flux almost everywhere.) -/
theorem intervalIntegral_infPivotalFlux_eq_sub
    (o : V) (p : ℕ) (n' m' : ℝ) (hm' : 0 ≤ m')
    (S : ℕ → Finset (Sym2 V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 V, ∃ n, e ∈ S n)
    (π : ℝ → Sym2 V → unitInterval) (c : ℝ → Sym2 V → ℝ)
    {I : Set ℝ} {a b : ℝ} (hsub : Set.uIcc a b ⊆ I)
    (hderiv : ∀ e : Sym2 V, ∀ r ∈ I,
      HasDerivAt (fun r' => ((π r' e : unitInterval) : ℝ)) (c r e) r)
    (hdom : ∀ r ∈ I, Summable fun e : Sym2 V =>
      |c r e| * (2 * max m' 0 * (edgeMeasure (π r)).real {ω : Config V | e ∈ touchSet ω o}))
    (hboundint : IntervalIntegrable (fluxWeight o m' π c) volume a b)
    (hmeas : ∀ k, AEStronglyMeasurable (windowPivotalFlux o p n' m' S π c k) volume) :
    ∫ r in a..b, infPivotalFlux o p n' m' π c r
      = (∫ ω : Config V, cappedClusterVol o p n' m' ω ∂(edgeMeasure (π b)))
        - (∫ ω : Config V, cappedClusterVol o p n' m' ω ∂(edgeMeasure (π a))) := by
  classical
  refine RussoDominated.integral_eq_sub_of_tendsto_hasDerivAt
    (f := fun k r => ∫ ω : Config V, cutFun (S k) (cappedClusterVol o p n' m') ω
      ∂(edgeMeasure (π r)))
    (f' := windowPivotalFlux o p n' m' S π c)
    (g := fun r => ∫ ω : Config V, cappedClusterVol o p n' m' ω ∂(edgeMeasure (π r)))
    (g' := infPivotalFlux o p n' m' π c) (bound := fluxWeight o m' π c)
    hsub ?_ hmeas ?_ hboundint ?_ ?_
  · intro k r hr
    have h := hasDerivAt_integral_cutFun π (c r) (S k) (cappedClusterVol o p n' m')
      (fun e => hderiv e r hr)
    have hsum : (∑ e : S k, c r (e : Sym2 V) * pivotalFlux (edgeMeasure (π r))
          (cutFun (S k) (cappedClusterVol o p n' m')) (e : Sym2 V))
        = windowPivotalFlux o p n' m' S π c k r :=
      Finset.sum_coe_sort (S k) (fun e => c r e * pivotalFlux (edgeMeasure (π r))
        (cutFun (S k) (cappedClusterVol o p n' m')) e)
    exact h.congr_deriv hsum
  · intro k r hr
    exact norm_windowPivotalFlux_le o p n' m' hm' S π c r (hdom r hr) k
  · intro r _
    exact tendsto_integral_cutFun S hSmono hS o p n' m' hm' (edgeMeasure (π r))
  · intro r hr
    simpa only [windowPivotalFlux, infPivotalFlux] using
      tendsto_windowFlux (m := max m' 0) (edgeMeasure (π r)) S (le_max_right m' 0)
        (cappedClusterVol_bound o p n' m' hm') (measurable_cappedClusterVol o p n' m')
        (cappedClusterVol_dep o p n' m')
        (fun ω => tendsto_cappedClusterVol_cutConfig S hSmono hS o p n' m' ω)
        (c r) (hdom r hr)

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- **Uniform boundedness of the paper's total pivotal mass replaces `hunif`.**

At each parameter `r` the total pivotal mass of the capped cluster-volume functional is at most
`2 sup|g| · D_r · E_{P_r}|K_o|` (`tsum_abs_pivotalFlux_le`; `hdom` is its summability, which
`summable_abs_weight_touch` supplies from the degree bound and finite expected cluster volume).

This theorem shows that the *only* additional uniformity the exchange needs is that this single
number be bounded on the parameter set: if `∑'_e |c_r(e)| · 2 max m' 0 · P_r(e ∈ touchSet · o) ≤ B`
for all `r ∈ I`, then `B` is a dominator for the whole window-flux family, and the infinite-volume
Russo formula holds at `r0` as soon as the infinite pivotal flux is measurable there and continuous
there.

Note that no uniformity in the window index appears anywhere: the bound is on the total mass, at
each parameter separately, with one constant `B` for the parameter set. -/
theorem hasDerivAt_integral_cappedClusterVol_of_uniformMass
    (o : V) (p : ℕ) (n' m' : ℝ) (hm' : 0 ≤ m')
    (S : ℕ → Finset (Sym2 V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 V, ∃ n, e ∈ S n)
    (π : ℝ → Sym2 V → unitInterval) (c : ℝ → Sym2 V → ℝ)
    {I : Set ℝ} (hI : IsOpen I) {r0 : ℝ} (hr0 : r0 ∈ I)
    (hderiv : ∀ e : Sym2 V, ∀ r ∈ I,
      HasDerivAt (fun r' => ((π r' e : unitInterval) : ℝ)) (c r e) r)
    (hdom : ∀ r ∈ I, Summable fun e : Sym2 V =>
      |c r e| * (2 * max m' 0 * (edgeMeasure (π r)).real {ω : Config V | e ∈ touchSet ω o}))
    (B : ℝ) (hmass : ∀ r ∈ I, ∑' e : Sym2 V,
      |c r e| * (2 * max m' 0 * (edgeMeasure (π r)).real {ω : Config V | e ∈ touchSet ω o}) ≤ B)
    (hmeas : ∀ k, AEStronglyMeasurable (windowPivotalFlux o p n' m' S π c k) volume)
    (hinf : StronglyMeasurableAtFilter (infPivotalFlux o p n' m' π c) (𝓝 r0) volume)
    (hcont : ContinuousAt (infPivotalFlux o p n' m' π c) r0) :
    HasDerivAt (fun r => ∫ ω : Config V, cappedClusterVol o p n' m' ω ∂(edgeMeasure (π r)))
      (infPivotalFlux o p n' m' π c r0) r0 := by
  classical
  have hm0 : (0 : ℝ) ≤ max m' 0 := le_max_right _ _
  have hWpos : ∀ (r : ℝ) (e : Sym2 V),
      0 ≤ |c r e| * (2 * max m' 0 *
        (edgeMeasure (π r)).real {ω : Config V | e ∈ touchSet ω o}) := fun r e =>
    mul_nonneg (abs_nonneg _) (mul_nonneg (by positivity) measureReal_nonneg)
  -- the total pivotal mass bounds every window flux
  have hbd : ∀ (k : ℕ) (r : ℝ), r ∈ I →
      ‖windowPivotalFlux o p n' m' S π c k r‖ ≤ B := by
    intro k r hr
    exact (norm_windowPivotalFlux_le o p n' m' hm' S π c r (hdom r hr) k).trans (hmass r hr)
  refine RussoDominated.hasDerivAt_of_tendsto_hasDerivAt
    (f := fun k r => ∫ ω : Config V, cutFun (S k) (cappedClusterVol o p n' m') ω
      ∂(edgeMeasure (π r)))
    (f' := windowPivotalFlux o p n' m' S π c)
    (g := fun r => ∫ ω : Config V, cappedClusterVol o p n' m' ω ∂(edgeMeasure (π r)))
    (g' := infPivotalFlux o p n' m' π c) (bound := fun _ : ℝ => B)
    hI ?_ hmeas ?_ ?_ ?_ ?_ ?_ hcont hr0
  · intro k r hr
    have h := hasDerivAt_integral_cutFun π (c r) (S k) (cappedClusterVol o p n' m')
      (fun e => hderiv e r hr)
    have hsum : (∑ e : S k, c r (e : Sym2 V) * pivotalFlux (edgeMeasure (π r))
          (cutFun (S k) (cappedClusterVol o p n' m')) (e : Sym2 V))
        = windowPivotalFlux o p n' m' S π c k r :=
      Finset.sum_coe_sort (S k) (fun e => c r e * pivotalFlux (edgeMeasure (π r))
        (cutFun (S k) (cappedClusterVol o p n' m')) e)
    exact h.congr_deriv hsum
  · exact hbd
  · intro a _ b _
    exact intervalIntegrable_const
  · intro r _
    exact tendsto_integral_cutFun S hSmono hS o p n' m' hm' (edgeMeasure (π r))
  · intro r hr
    simpa only [windowPivotalFlux, infPivotalFlux] using
      tendsto_windowFlux (m := max m' 0) (edgeMeasure (π r)) S (le_max_right m' 0)
        (cappedClusterVol_bound o p n' m' hm') (measurable_cappedClusterVol o p n' m')
        (cappedClusterVol_dep o p n' m')
        (fun ω => tendsto_cappedClusterVol_cutConfig S hSmono hS o p n' m' ω)
        (c r) (hdom r hr)
  · exact hinf

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- **The sharpness input isolated as a single parameter-independent majorant.**

For the capped cluster-volume functional, let `W : Sym2 V → ℝ` be a summable majorant of the
per-edge pivotal weights, *uniformly in the parameter on `I`*:

`|c r e| · 2 max m' 0 · P_r(e ∈ touchSet · o) ≤ W e`   for all `r ∈ I` and all edges `e`,

and assume the individual pivotal-flux terms are continuous in the parameter at every point of `I`.
Then the infinite-volume Russo formula holds at `r0`:

`d/dr (∫ cappedClusterVol dP_r)|_{r0} = ∑'_e c_{r0}(e) · pivot_{r0}(g) e`.

Everything quantitative here is a *bound*: `hW` is summable and `hmaj` is a uniform-in-parameter
estimate, both of the form produced by sharpness (finite expected cluster volume, uniformly on
compacts, together with the degree bound).  In particular this theorem has

* no locally uniform convergence hypothesis (`hunif`),
* no separate continuity hypothesis on the limit flux — it is *derived* from `hmaj` and
  `hcontterm` by Tannery's theorem (`tendsto_tsum_of_dominated_convergence`), and
* no integrability hypothesis on a dominator — the constant `∑' e, W e` is used.

The only remaining hypotheses are the pointwise finiteness input `hdom` (absorbed into `hmaj`), the
measurability in the parameter of the finite window fluxes (`hmeas`, supplied in concrete models by
continuity of `r ↦ c r e` and of the edge law), and the per-edge derivative `hderiv` of the model. -/
theorem hasDerivAt_integral_cappedClusterVol_of_majorant
    (o : V) (p : ℕ) (n' m' : ℝ) (hm' : 0 ≤ m')
    (S : ℕ → Finset (Sym2 V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 V, ∃ n, e ∈ S n)
    (π : ℝ → Sym2 V → unitInterval) (c : ℝ → Sym2 V → ℝ)
    {I : Set ℝ} (hI : IsOpen I) {r0 : ℝ} (hr0 : r0 ∈ I)
    (hderiv : ∀ e : Sym2 V, ∀ r ∈ I,
      HasDerivAt (fun r' => ((π r' e : unitInterval) : ℝ)) (c r e) r)
    (W : Sym2 V → ℝ) (hW : Summable W)
    (hmaj : ∀ r ∈ I, ∀ e : Sym2 V,
      |c r e| * (2 * max m' 0 * (edgeMeasure (π r)).real {ω : Config V | e ∈ touchSet ω o}) ≤ W e)
    (hcontterm : ∀ e : Sym2 V, ∀ r ∈ I, ContinuousAt (fun r' => c r' e *
      pivotalFlux (edgeMeasure (π r')) (cappedClusterVol o p n' m') e) r)
    (hmeas : ∀ k, AEStronglyMeasurable (windowPivotalFlux o p n' m' S π c k) volume) :
    HasDerivAt (fun r => ∫ ω : Config V, cappedClusterVol o p n' m' ω ∂(edgeMeasure (π r)))
      (infPivotalFlux o p n' m' π c r0) r0 := by
  classical
  have hm0 : (0 : ℝ) ≤ max m' 0 := le_max_right _ _
  have hweight_nonneg : ∀ (r : ℝ) (e : Sym2 V),
      0 ≤ |c r e| * (2 * max m' 0 *
        (edgeMeasure (π r)).real {ω : Config V | e ∈ touchSet ω o}) := fun r e =>
    mul_nonneg (abs_nonneg _) (mul_nonneg (by positivity) measureReal_nonneg)
  have hWpos : ∀ e : Sym2 V, 0 ≤ W e := fun e =>
    (hweight_nonneg r0 e).trans (hmaj r0 hr0 e)
  -- the pivotal weights are summable at every parameter in `I`
  have hdomW : ∀ r ∈ I, Summable fun e : Sym2 V =>
      |c r e| * (2 * max m' 0 * (edgeMeasure (π r)).real {ω : Config V | e ∈ touchSet ω o}) := by
    intro r hr
    exact Summable.of_nonneg_of_le (fun e => hweight_nonneg r e) (fun e => hmaj r hr e) hW
  -- every window flux is bounded by the constant `∑' e, W e`
  have hbd : ∀ (k : ℕ) (r : ℝ), r ∈ I →
      ‖windowPivotalFlux o p n' m' S π c k r‖ ≤ ∑' e : Sym2 V, W e := by
    intro k r hr
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum ?_).trans
      (Summable.sum_le_tsum (S k) (fun e _ => hWpos e) hW))
    intro e _
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul_of_nonneg_left
      (abs_pivotalFlux_cutFun_le (o := o) (edgeMeasure (π r)) hm0
        (cappedClusterVol_bound o p n' m' hm') (measurable_cappedClusterVol o p n' m')
        (cappedClusterVol_dep o p n' m') e) (abs_nonneg _)).trans (hmaj r hr e)
  -- Tannery: the infinite pivotal flux is continuous on `I`
  have hcontI : ∀ r ∈ I, ContinuousAt (infPivotalFlux o p n' m' π c) r := by
    intro r hr
    have hb : ∀ᶠ r' in 𝓝 r, ∀ e : Sym2 V,
        ‖c r' e * pivotalFlux (edgeMeasure (π r')) (cappedClusterVol o p n' m') e‖ ≤ W e := by
      filter_upwards [hI.mem_nhds hr] with r' hr'
      intro e
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul_of_nonneg_left
        (abs_pivotalFlux_le (o := o) (edgeMeasure (π r')) hm0
          (cappedClusterVol_bound o p n' m' hm') (measurable_cappedClusterVol o p n' m')
          (cappedClusterVol_dep o p n' m') e) (abs_nonneg _)).trans (hmaj r' hr' e)
    exact tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝 r) hW
      (fun e => hcontterm e r hr) hb
  refine RussoDominated.hasDerivAt_of_tendsto_hasDerivAt
    (f := fun k r => ∫ ω : Config V, cutFun (S k) (cappedClusterVol o p n' m') ω
      ∂(edgeMeasure (π r)))
    (f' := windowPivotalFlux o p n' m' S π c)
    (g := fun r => ∫ ω : Config V, cappedClusterVol o p n' m' ω ∂(edgeMeasure (π r)))
    (g' := infPivotalFlux o p n' m' π c) (bound := fun _ : ℝ => ∑' e : Sym2 V, W e)
    hI ?_ hmeas ?_ ?_ ?_ ?_ ?_ (hcontI r0 hr0) hr0
  · -- the finite-window Russo identity, in window-flux form
    intro k r hr
    have h := hasDerivAt_integral_cutFun π (c r) (S k) (cappedClusterVol o p n' m')
      (fun e => hderiv e r hr)
    have hsum : (∑ e : S k, c r (e : Sym2 V) * pivotalFlux (edgeMeasure (π r))
          (cutFun (S k) (cappedClusterVol o p n' m')) (e : Sym2 V))
        = windowPivotalFlux o p n' m' S π c k r :=
      Finset.sum_coe_sort (S k) (fun e => c r e * pivotalFlux (edgeMeasure (π r))
        (cutFun (S k) (cappedClusterVol o p n' m')) e)
    exact h.congr_deriv hsum
  · exact hbd
  · -- the constant majorant is interval integrable
    intro a _ b _
    exact intervalIntegrable_const
  · -- window expectations converge to the infinite-volume expectation
    intro r _
    exact tendsto_integral_cutFun S hSmono hS o p n' m' hm' (edgeMeasure (π r))
  · -- window fluxes converge pointwise to the infinite pivotal series
    intro r hr
    simpa only [windowPivotalFlux, infPivotalFlux] using
      tendsto_windowFlux (m := max m' 0) (edgeMeasure (π r)) S hm0
        (cappedClusterVol_bound o p n' m' hm') (measurable_cappedClusterVol o p n' m')
        (cappedClusterVol_dep o p n' m')
        (fun ω => tendsto_cappedClusterVol_cutConfig S hSmono hS o p n' m' ω)
        (c r) (hdomW r hr)
  · exact ContinuousAt.stronglyMeasurableAtFilter hI hcontI r0 hr0

end PercLib.CriticalLRP

#print axioms RussoDominated.integral_eq_sub_of_tendsto_hasDerivAt
#print axioms RussoDominated.hasDerivAt_of_tendsto_hasDerivAt
#print axioms PercLib.CriticalLRP.norm_windowPivotalFlux_le
#print axioms PercLib.CriticalLRP.hasDerivAt_integral_cappedClusterVol_of_dominated
#print axioms PercLib.CriticalLRP.intervalIntegral_infPivotalFlux_eq_sub
#print axioms PercLib.CriticalLRP.hasDerivAt_integral_cappedClusterVol_of_uniformMass
#print axioms PercLib.CriticalLRP.hasDerivAt_integral_cappedClusterVol_of_majorant
