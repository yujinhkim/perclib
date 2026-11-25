/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The edge-integrated Russo flux series of one vertex sums to the two-point increment

Swarm `smwv576pz`, member `m1`, direction A1.

`PivotalWeight/Interchange.lean` proves that the interval integral of the infinite pivotal flux
of one vertex is the edge series of the per-edge integrals (`∫_r ∑'_e = ∑'_e ∫_r`).  This file
supplies the missing evaluation of that common value: on a window meeting no corner radius, the
flux is the radius derivative of the two-point function (`hasDerivAt_cutTwoPoint_off`, landed), so
the fundamental theorem of calculus identifies it with `cutTwoPoint b 0 y - cutTwoPoint a 0 y`.

Both the derivative input and the interval integrability of the flux are explicit hypotheses; the
latter can be discharged from the interior-scale envelope by
`intervalIntegrable_sMomentInfFlux_of_envelope` when the window is the envelope window, so the
only genuinely residual hypothesis below is the continuity of the per-vertex infinite flux
(`hcontinf`), exactly as in the landed derivative statement.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.PivotalWeight.Interchange
public import PercLib.CriticalLRP.Analysis.Cutoff.Deriv

/-!
Evaluation of the edge-integrated flux series at a two-point increment.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- **Fundamental theorem of calculus for the per-vertex infinite flux.**

On a window `I` of radii that meets no corner radius, and on which `K` is differentiable and the
per-edge weight series is summable, the interval integral of the infinite pivotal flux of `y` is
the increment of the two-point function. -/
theorem intervalIntegral_sMomentInfFlux_singleton_eq_cutTwoPoint_sub (y : M.V)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {I : Set ℝ} (hI : IsOpen I) {a b : ℝ} (hsub : Set.uIcc a b ⊆ I)
    (hoff : ∀ r ∈ I, r ∉ M.cornerRadii)
    (hKd : ∀ r ∈ I, DifferentiableAt ℝ M.K r)
    (hdom : ∀ r ∈ I, Summable fun e : Sym2 M.V =>
      |M.cutEdgeDeriv r e| * (2 * (M.cutLaw r).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)}))
    (hboundint : ∀ a' ∈ I, ∀ b' ∈ I, IntervalIntegrable
      (sMomentWeight (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv) volume a' b')
    (hmeasK : ∀ k : ℕ, AEStronglyMeasurable (windowFluxOf (0 : M.V)
      (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) S M.cutProb M.cutEdgeDeriv k)
      volume)
    (hmeasinf : ∀ r ∈ I, StronglyMeasurableAtFilter
      (sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv) (𝓝 r) volume)
    (hcontinf : ∀ r ∈ I, ContinuousAt
      (sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv) r)
    (hint : IntervalIntegrable (fun r =>
      sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv r) volume a b) :
    ∫ r in a..b, sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv r
      = M.cutTwoPoint b (0 : M.V) y - M.cutTwoPoint a (0 : M.V) y := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun r => M.cutTwoPoint r (0 : M.V) y) ?_ hint
  intro r hr
  exact M.hasDerivAt_cutTwoPoint_off y S hSmono hS hI (hsub hr) hoff hKd hdom
    (fun a' ha' b' hb' => hboundint a' ha' b' hb') hmeasK (hmeasinf r (hsub hr))
    (hcontinf r (hsub hr))

/-- **The edge-integrated Russo flux series of one vertex is the two-point increment.**

This composes the edge-sum interchange (`intervalIntegral_sMomentInfFlux_eq_tsum_integral`, whose
analytic input is the interior-scale envelope at `ρ ≥ b`) with the fundamental theorem of calculus
above.  The right-hand side does not depend on the edge exhaustion `S`. -/
theorem tsum_intervalIntegral_flux_eq_cutTwoPoint_sub {a b ρ C : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hbρ : b ≤ ρ) (hCb : ∀ r ∈ Set.Icc a b, -(deriv M.K r) ≤ C) (hC0 : 0 ≤ C)
    (hKρ : deriv M.K ρ < 0) (hρ : 0 < ρ) (hvol : M.cutMoment 1 ρ ≠ ⊤) (y : M.V)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {I : Set ℝ} (hI : IsOpen I) (hsub : Set.uIcc a b ⊆ I)
    (hoff : ∀ r ∈ I, r ∉ M.cornerRadii)
    (hKd : ∀ r ∈ I, DifferentiableAt ℝ M.K r)
    (hdom : ∀ r ∈ I, Summable fun e : Sym2 M.V =>
      |M.cutEdgeDeriv r e| * (2 * (M.cutLaw r).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)}))
    (hboundint : ∀ a' ∈ I, ∀ b' ∈ I, IntervalIntegrable
      (sMomentWeight (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv) volume a' b')
    (hmeasK : ∀ k : ℕ, AEStronglyMeasurable (windowFluxOf (0 : M.V)
      (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) S M.cutProb M.cutEdgeDeriv k)
      volume)
    (hmeasinf : ∀ r ∈ I, StronglyMeasurableAtFilter
      (sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv) (𝓝 r) volume)
    (hcontinf : ∀ r ∈ I, ContinuousAt
      (sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv) r)
    (hint : IntervalIntegrable (fun r =>
      sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv r) volume a b) :
    ∑' e : Sym2 M.V, ∫ r in a..b, M.cutEdgeDeriv r e *
        pivotalFlux (M.cutLaw r)
          (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e
      = M.cutTwoPoint b (0 : M.V) y - M.cutTwoPoint a (0 : M.V) y := by
  rw [← M.intervalIntegral_sMomentInfFlux_eq_tsum_integral (a' := a) (b' := b) ha hab hbρ
    hCb hC0 hKρ hρ hvol y]
  exact M.intervalIntegral_sMomentInfFlux_singleton_eq_cutTwoPoint_sub y S hSmono hS hI hsub
    hoff hKd hdom hboundint hmeasK hmeasinf hcontinf hint

/-- **The same identity with the flux integrability discharged by the interior-scale envelope.**

Only the window regularity data (`I`, corner-free, `K` differentiable, per-edge weights summable,
per-vertex pivotal weight integrable, window-flux measurable, flux measurable and continuous) plus
the envelope at `[a,b]` remain; `IntervalIntegrable` of the signed flux series is not an extra
assumption. -/
theorem tsum_intervalIntegral_flux_eq_cutTwoPoint_sub_of_envelope {a b ρ C : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hbρ : b ≤ ρ) (hCb : ∀ r ∈ Set.Icc a b, -(deriv M.K r) ≤ C) (hC0 : 0 ≤ C)
    (hKρ : deriv M.K ρ < 0) (hρ : 0 < ρ) (hvol : M.cutMoment 1 ρ ≠ ⊤) (y : M.V)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {I : Set ℝ} (hI : IsOpen I) (hsub : Set.uIcc a b ⊆ I)
    (hoff : ∀ r ∈ I, r ∉ M.cornerRadii)
    (hKd : ∀ r ∈ I, DifferentiableAt ℝ M.K r)
    (hdom : ∀ r ∈ I, Summable fun e : Sym2 M.V =>
      |M.cutEdgeDeriv r e| * (2 * (M.cutLaw r).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)}))
    (hboundint : ∀ a' ∈ I, ∀ b' ∈ I, IntervalIntegrable
      (sMomentWeight (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv) volume a' b')
    (hmeasK : ∀ k : ℕ, AEStronglyMeasurable (windowFluxOf (0 : M.V)
      (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) S M.cutProb M.cutEdgeDeriv k)
      volume)
    (hmeasinf : ∀ r ∈ I, StronglyMeasurableAtFilter
      (sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv) (𝓝 r) volume)
    (hcontinf : ∀ r ∈ I, ContinuousAt
      (sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv) r) :
    ∑' e : Sym2 M.V, ∫ r in a..b, M.cutEdgeDeriv r e *
        pivotalFlux (M.cutLaw r)
          (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e
      = M.cutTwoPoint b (0 : M.V) y - M.cutTwoPoint a (0 : M.V) y :=
  M.tsum_intervalIntegral_flux_eq_cutTwoPoint_sub ha hab hbρ hCb hC0 hKρ hρ hvol y S hSmono hS
    hI hsub hoff hKd hdom hboundint hmeasK hmeasinf hcontinf
    (M.intervalIntegrable_sMomentInfFlux_of_envelope ha hab hbρ hCb hC0 hKρ hρ hvol y)

end SourceModelData

end PercLib.CriticalLRP.Orchestration
