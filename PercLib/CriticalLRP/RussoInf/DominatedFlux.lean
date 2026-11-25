/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Dominated (integrated) form of the limit-of-derivatives step in infinite-volume Russo

This file supplies the analytic core of the "sharpness" input behind infinite-volume Russo
moment differentiation, in the form that does *not* assume local uniform convergence of the
finite-window pivotal fluxes.

## The point

In `CriticalPercLib.CriticalLRP/RussoInf/Exchange.lean` the conditional theorems have a
hypothesis

  `hunif : TendstoLocallyUniformlyOn (fun k r => <window flux k r>) Φ atTop I`

(it is a hypothesis of `hasDerivAt_integral_of_windowFlux`,
`hasDerivAt_integral_cappedClusterVol`, `hasDerivAt_integral_cappedClusterVol_of_sharpness`
and `hasDerivAt_integral_cappedClusterVol_cutoff`).

`hunif` is *stronger than necessary*.  What is really used is the identity

  (★)  `∫ r in a..b, Φ r = ψ b - ψ a`

for the limit expectation `ψ r = ∫ g dμ_r`, together with regularity of `Φ` in `r`.  The
identity (★) follows from the finite-window identities `ψ_k' = (window flux k)` by

* pointwise convergence of `(window flux k)` to `Φ` in the parameter (this is already proved in
  the repository as `tendsto_windowFlux`), and
* **one** quantitative input: a *dominator* for the whole family of window fluxes, i.e. a single
  function `bound` with `‖window flux k r‖ ≤ bound r` for all `k` and all `r ∈ I`, locally
  integrable on `I`,

via dominated convergence plus the fundamental theorem of calculus.  No uniformity in `k` of the
convergence is used anywhere.

So the sharpness content is relocated from "the window fluxes converge locally uniformly" (a
statement about the whole sequence) to

  (D) a locally integrable dominator for the window fluxes, and
  (C) continuity of the limiting infinite pivotal flux `Φ`.

Both are strictly weaker than `hunif` (a locally uniform limit of continuous functions supplies
both), and both are what the paper's sharpness argument actually produces: (D) is the
finite-expected-cluster-volume bound and (C) is the absolute convergence of the infinite pivotal
series with a parameter-continuous majorant.

## What is proved here

* `integral_eq_sub_of_tendsto_hasDerivAt` — the integrated identity (★) from per-window derivative
  identities + pointwise derivative convergence + a dominator.  No locally uniform convergence.
* `hasDerivAt_of_tendsto_hasDerivAt` — hence the limit is differentiable at every continuity point
  of `Φ`, with derivative `Φ`.  In particular differentiability holds `a.e.` in the parameter
  (the set of discontinuities of a real function need not be null, but continuity of `Φ` is the
  concrete sufficient condition produced by sharpness, and the identity (★) alone already gives
  absolute continuity of `ψ` with `ψ' = Φ` a.e.).
-/
module

public import Mathlib

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace RussoDominated

/-- The closed unordered interval contains the oriented half-open interval. -/
theorem ioc_subset_uIcc (a b : ℝ) : Set.Ioc a b ⊆ Set.uIcc a b := by
  intro x hx
  rw [Set.mem_uIcc]
  exact Or.inl ⟨le_of_lt hx.1, hx.2⟩

/-! ### The integrated identity -/

/-- **Integrated limit-of-derivatives theorem.**

Let `f n` have derivative `f' n` at every point of a set `I` containing `uIcc a b`, let the
derivatives `f' n` converge pointwise on `I` to `g'` and be dominated there by a single function
`bound` which is interval integrable on `a`, `b`, and let `f n` converge pointwise on `I` to `g`.
Then `∫ x in a..b, g' x = g b - g a`.

No uniformity of the convergence of the derivatives is assumed; this is the dominated-convergence
(equivalently, Vitali-type) replacement for Mathlib's
`hasDerivAt_of_tendstoLocallyUniformlyOn`. -/
theorem integral_eq_sub_of_tendsto_hasDerivAt
    {I : Set ℝ} {f f' : ℕ → ℝ → ℝ} {g g' bound : ℝ → ℝ} {a b : ℝ}
    (hsub : Set.uIcc a b ⊆ I)
    (hderiv : ∀ n, ∀ x ∈ I, HasDerivAt (f n) (f' n x) x)
    (hmeas : ∀ n, AEStronglyMeasurable (f' n) volume)
    (hbound : ∀ n, ∀ x ∈ I, ‖f' n x‖ ≤ bound x)
    (hboundint : IntervalIntegrable bound volume a b)
    (hfg : ∀ x ∈ I, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (hfg' : ∀ x ∈ I, Tendsto (fun n => f' n x) atTop (𝓝 (g' x))) :
    ∫ x in a..b, g' x = g b - g a := by
  -- (i) the exact finite-window identities
  have key : ∀ n, ∫ x in a..b, f' n x = f n b - f n a := by
    intro n
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hderiv n x (hsub hx)) ?_
    refine ⟨?_, ?_⟩
    · refine Integrable.mono' hboundint.1 ((hmeas n).mono_measure Measure.restrict_le_self) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact hbound n x (hsub (ioc_subset_uIcc a b hx))
    · refine Integrable.mono' hboundint.2 ((hmeas n).mono_measure Measure.restrict_le_self) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact hbound n x (hsub (by rw [Set.uIcc_comm]; exact ioc_subset_uIcc b a hx))
  -- (ii) dominated convergence identifies the limit of the integrals
  have hDCT : Tendsto (fun n => ∫ x in a..b, f' n x) atTop (𝓝 (∫ x in a..b, g' x)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (μ := volume) (l := atTop) (a := a) (b := b) (f := g') (bound := bound)
      ?_ ?_ hboundint ?_
    · exact Eventually.of_forall fun n => (hmeas n).mono_measure Measure.restrict_le_self
    · exact Eventually.of_forall fun n => Eventually.of_forall fun x hx =>
        hbound n x (hsub (Set.uIoc_subset_uIcc hx))
    · exact Eventually.of_forall fun x hx => hfg' x (hsub (Set.uIoc_subset_uIcc hx))
  -- (iii) the finite-window identities converge to the increment of the limit
  have h1 : Tendsto (fun n => ∫ x in a..b, f' n x) atTop (𝓝 (g b - g a)) := by
    have hb : Tendsto (fun n => f n b - f n a) atTop (𝓝 (g b - g a)) :=
      (hfg b (hsub Set.right_mem_uIcc)).sub (hfg a (hsub Set.left_mem_uIcc))
    refine hb.congr' (Eventually.of_forall fun n => ?_)
    exact (key n).symm
  exact tendsto_nhds_unique hDCT h1

/-! ### Differentiation at continuity points of the limit flux -/

/-- **Dominated limit-of-derivatives, pointwise form.**

Under the same hypotheses as `integral_eq_sub_of_tendsto_hasDerivAt`, uniformly over the
sub-intervals of `I`, if the limiting flux `g'` is strongly measurable and continuous at `x₀`,
then `g` has derivative `g' x₀` at `x₀`.

This is the statement that replaces `hunif`: local uniform convergence of `f' n` to `g'` is not
assumed, only a dominator for `f' n` and continuity of `g'`.

Note that measurability of `f' n` and of `g'` are the only extra hypotheses compared with the
uniform-convergence theorem; in the percolation instantiation they follow from measurability in
the parameter of the edge law. -/
theorem hasDerivAt_of_tendsto_hasDerivAt
    {I : Set ℝ} (hI : IsOpen I) {f f' : ℕ → ℝ → ℝ} {g g' bound : ℝ → ℝ} {x₀ : ℝ}
    (hderiv : ∀ n, ∀ x ∈ I, HasDerivAt (f n) (f' n x) x)
    (hmeas : ∀ n, AEStronglyMeasurable (f' n) volume)
    (hbound : ∀ n, ∀ x ∈ I, ‖f' n x‖ ≤ bound x)
    (hboundint : ∀ a ∈ I, ∀ b ∈ I, IntervalIntegrable bound volume a b)
    (hfg : ∀ x ∈ I, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (hfg' : ∀ x ∈ I, Tendsto (fun n => f' n x) atTop (𝓝 (g' x)))
    (hmeasg : StronglyMeasurableAtFilter g' (𝓝 x₀) volume)
    (hcont : ContinuousAt g' x₀) (hx₀ : x₀ ∈ I) :
    HasDerivAt g (g' x₀) x₀ := by
  -- locally, `g` is the indefinite integral of `g'`
  have hident : g =ᶠ[𝓝 x₀] fun u => g x₀ + ∫ y in x₀..u, g' y := by
    obtain ⟨ρ, hρ, hρI⟩ := Metric.isOpen_iff.mp hI x₀ hx₀
    filter_upwards [Metric.ball_mem_nhds x₀ hρ] with u hu
    have hsub : Set.uIcc x₀ u ⊆ I :=
      ((convex_ball x₀ ρ).ordConnected.uIcc_subset (Metric.mem_ball_self hρ) hu).trans hρI
    have h := integral_eq_sub_of_tendsto_hasDerivAt hsub hderiv hmeas hbound
      (hboundint x₀ hx₀ u (hρI hu)) hfg hfg'
    rw [h]
    ring
  -- the indefinite integral of a continuous integrand differentiates back
  have hInt : HasDerivAt (fun u => g x₀ + ∫ y in x₀..u, g' y) (g' x₀) x₀ :=
    (intervalIntegral.integral_hasDerivAt_right (f := g') (a := x₀) (b := x₀)
      ⟨by simp, by simp⟩ hmeasg hcont).const_add (g x₀)
  exact hInt.congr_of_eventuallyEq hident

end RussoDominated
