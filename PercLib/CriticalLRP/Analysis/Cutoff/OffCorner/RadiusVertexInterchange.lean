/-
# Radius/vertex exchange for the cut mass: integrated Lemma I.4.1 with the
exchange hypotheses discharged

Source: Lemma I.4.1 and display (I.4.1) with `p = 1`
(`.scratch/source/paper-tex.txt`, lines 815–819) state

`d/dr E_{β,r}|K| = β |J'(r)| E_{β,r}[ ∑_{y ∈ B_r} 1(y ∉ K) |K| |K_y| ]`.

Production rewrites the derivative as the vertex sum of singleton pivotal fluxes,
`∑'_y sMomentInfFlux 0 {y} 1 r` (`OffCorner/RadiusSummedFlux.tsum_sMomentInfFlux_eq_rhsScalar`
in the off-corner closed form `β_c (-K'(r)) (exclMass r).toReal`).  The integrated form of
(I.4.1) is the identity

`∫_a^b (∑'_y flux_y r) dr = χ b - χ a`,  `χ r = M.cutMassReal r`,

which is the exact radius-versus-vertex exchange the source uses when it integrates the
derivative formula.

`Analysis/Cutoff/IntegralFluxInterchange.intervalIntegral_tsum_sMomentInfFlux_eq_sub` proves
that identity, but carries three exchange-side hypotheses beyond the model inputs:

* `hfluxnn` — nonnegativity of every per-vertex flux on `Ioc a b`;
* `hfluxint` — interval integrability in `r` of every per-vertex flux;
* `hsummable` — pointwise (in `r`) summability in `y` of the per-vertex fluxes.

All three are consequences of landed results, not independent analytic inputs:

* `hfluxnn` follows from `sMomentInfFlux_eq_toReal_tsum` (the singleton moment functional is
  increasing, so every pivotal flux and every edge weight is nonnegative, and the real tsum is
  the `toReal` of a nonnegative `ℝ≥0∞` tsum);
* `hfluxint` follows from the per-vertex radius continuity `hcontinf` alone, since `uIcc a b` is
  compact inside the window (no `hboundint`-type dominator is needed for integrability);
* `hsummable` follows from `summable_sMomentInfFlux_of_cutMoment_two` (finite *second* cutoff
  moment at an off-corner radius), not from the weighted touching bound.

The first theorem below is therefore the same integrated identity with `hfluxnn`, `hfluxint` and
`hsummable` deleted.  The remaining inputs are exactly the model hypotheses: an off-corner radius
window, a finite second cutoff moment at the right endpoint, interval integrability of the
per-vertex *pivotal weights* (`hboundint`, the input supplied for the power-law witness by
`PowerLawAC`), and per-vertex radius continuity (`hcontinf`, supplied on a window for the
power-law witness by `OffCorner/PowerLawContinuity`).

The second theorem records the precise limitation of the weighted touching bound, which is the
distinction the source's mass-transport step has to bridge: on the singleton `{y}` with unit
weight the weighted bound is *independent of `y`*
(`sMomentWeight_singleton_indep`), so a nonzero value gives a non-summable constant family.  The
weighted bound therefore cannot produce the vertex summability `hsummable`; the actual flux is
summable instead because of the second-moment domination
(`summable_sMomentInfFlux_of_cutMoment_two`).  This is a limitation of that bounding route only,
not a statement that the vertex sum fails to converge.

Nothing here re-proves the per-edge `∑'_e` interchange (the subject of A1): all edge series are
consumed through the already-landed `sMomentInfFlux` API, and the object of this file is the
outer `∑'_y` / `∫ dr` ordering.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.IntegralFluxInterchange
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.RadiusMeasurability.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.SecondMomentFlux
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.PowerLawAC
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.PowerLawContinuity
public import PercLib.CriticalLRP.Analysis.Cutoff.Resampling

/-!
# Integrated first-moment formula with radius/vertex exchanges discharged
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- **The integrated first-moment formula (I.4.1) with the radius/vertex exchange hypotheses
discharged.**

For a model `M`, a monotone vertex exhaustion `T` and edge exhaustion `S`, an off-corner radius
window `Ioo α β` with `0 < α`, and a finite second cutoff moment at the right endpoint `β`, the
radius integral of the summed singleton pivotal flux equals the increment of the cut mass.  The
per-vertex flux nonnegativity, its interval integrability in `r`, and its pointwise summability in
`y` are derived here from landed results rather than assumed.

The two genuinely analytic inputs that remain are the interval integrability of the per-vertex
pivotal *weights* `hboundint` (supplied for the power-law witness by `PowerLawAC`) and the
per-vertex radius continuity `hcontinf` (supplied on a window for the power-law witness by
`OffCorner/PowerLawContinuity`). -/
theorem intervalIntegral_tsum_sMomentInfFlux_eq_sub_of_cutMoment_two
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {α β a b : ℝ} (hα0 : 0 < α) (hαa : α < a) (hab : a ≤ b) (hbβ : b < β)
    (hoff : ∀ r ∈ Set.Ioo α β, r ∉ M.cornerRadii)
    (hKd : ∀ r ∈ Set.Ioo α β, DifferentiableAt ℝ M.K r)
    (h2β : M.cutMoment 2 β ≠ ⊤)
    (hboundint : ∀ y : M.V, ∀ a' ∈ Set.Ioo α β, ∀ b' ∈ Set.Ioo α β, IntervalIntegrable
      (sMomentWeight (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) volume a' b')
    (hcontinf : ∀ y : M.V, ∀ r ∈ Set.Ioo α β, ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r) :
    ∫ r in a..b, (∑' y : M.V,
        sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r)
      = M.cutMassReal b - M.cutMassReal a := by
  classical
  -- the interval sits strictly inside the off-corner window
  have hsub : Set.uIcc a b ⊆ Set.Ioo α β := by
    rw [Set.uIcc_of_le hab]
    exact fun r hr => ⟨lt_of_lt_of_le hαa hr.1, lt_of_le_of_lt hr.2 hbβ⟩
  have hmem : ∀ r ∈ Set.Ioc a b, r ∈ Set.Ioo α β := fun r hr =>
    ⟨lt_of_lt_of_le hαa (le_of_lt hr.1), lt_of_le_of_lt hr.2 hbβ⟩
  have hpos : ∀ r ∈ Set.Ioo α β, 0 < r := fun r hr => lt_trans hα0 hr.1
  have h2r : ∀ r ∈ Set.Ioo α β, M.cutMoment 2 r ≠ ⊤ := fun r hr =>
    M.cutMoment_ne_top_of_le (le_of_lt hr.2) 2 h2β
  have h1r : ∀ r ∈ Set.Ioo α β, M.cutMoment 1 r ≠ ⊤ := fun r hr =>
    M.cutMoment_one_ne_top_of_two (h2r r hr)
  refine M.intervalIntegral_tsum_sMomentInfFlux_eq_sub (I := Set.Ioo α β)
    T hTmono hT S hSmono hS isOpen_Ioo hab hsub (lt_trans hα0 hαa) hoff hKd
    (fun r hr => M.summable_hdom_of_cutMoment (hpos r hr) (h1r r hr))
    hboundint (fun y k => M.aeStronglyMeasurable_windowFluxOf_singleton y S k)
    (fun y r hr => M.stronglyMeasurableAtFilter_sMomentInfFlux y (le_of_lt hα0) h1r r hr)
    hcontinf
    (fun r hr => by
      have hcm : M.cutMassAt r 0 = M.cutMoment 1 r := by
        simp only [SourceModelData.cutMassAt, SourceModelData.cutMoment, pow_one]
      rw [hcm]
      exact h1r r (hsub hr))
    (fun y => ContinuousOn.intervalIntegrable (u := fun r =>
        sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ)) M.cutProb
          M.cutEdgeDeriv r) (fun r hr => (hcontinf y r (hsub hr)).continuousWithinAt))
    (fun y r hr => by
      rw [M.sMomentInfFlux_eq_toReal_tsum (hpos r (hmem r hr)) (h1r r (hmem r hr)) y]
      exact ENNReal.toReal_nonneg)
    (fun r hr => M.summable_sMomentInfFlux_of_cutMoment_two (hpos r (hmem r hr))
      (by
        rw [M.attainedRadii_eq_cornerRadii]
        exact hoff r (hmem r hr))
      (h2r r (hmem r hr)))

/-- **The weighted touching bound cannot supply vertex summability.**  On the singleton `{y}` with
unit weight, `sMomentWeight` is independent of `y`; if its value is nonzero then the family
`y ↦ sMomentWeight 0 {y} 1 r` is a nonzero constant family on the infinite vertex set and hence is
not summable.

This isolates what the source's mass-transport step has to do: the vertex sum has to be controlled
through the *actual* pivotal flux (second-moment domination), not through the weighted touching
majorant, which is uniform in `y`. -/
theorem not_summable_sMomentWeight_singleton_of_pos {r : ℝ}
    (hpos : 0 < sMomentWeight (0 : M.V) ({(0 : M.V)} : Finset M.V) (fun _ => (1 : ℝ))
      M.cutProb M.cutEdgeDeriv r) :
    ¬ Summable fun y : M.V => sMomentWeight (0 : M.V) ({y} : Finset M.V)
      (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r := by
  have heq : (fun y : M.V => sMomentWeight (0 : M.V) ({y} : Finset M.V)
      (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r)
      = fun _ => sMomentWeight (0 : M.V) ({(0 : M.V)} : Finset M.V)
          (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r := by
    funext y
    exact M.sMomentWeight_singleton_indep M.cutProb M.cutEdgeDeriv r y 0
  rw [heq]
  exact M.not_summable_const_of_pos hpos

/-- **The actual flux versus the weighted touching bound, side by side.**  Off the corner and with
a finite second cutoff moment, the singleton pivotal fluxes are summable in `y`, while a nonzero
singleton weighted touching bound is *not*: the two vertex families behave differently, so the
summability of the flux is genuinely extra information beyond the weighted bound. -/
theorem summable_sMomentInfFlux_and_not_summable_weight {r : ℝ} (hr : 0 < r)
    (hoff : r ∉ M.attainedRadii) (h2 : M.cutMoment 2 r ≠ ⊤)
    (hpos : 0 < sMomentWeight (0 : M.V) ({(0 : M.V)} : Finset M.V) (fun _ => (1 : ℝ))
      M.cutProb M.cutEdgeDeriv r) :
    Summable (fun y : M.V =>
        sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ)) M.cutProb
          M.cutEdgeDeriv r)
      ∧ ¬ Summable fun y : M.V => sMomentWeight (0 : M.V) ({y} : Finset M.V)
          (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r :=
  ⟨M.summable_sMomentInfFlux_of_cutMoment_two hr hoff h2,
    M.not_summable_sMomentWeight_singleton_of_pos hpos⟩

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.intervalIntegral_tsum_sMomentInfFlux_eq_sub_of_cutMoment_two
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.not_summable_sMomentWeight_singleton_of_pos
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.summable_sMomentInfFlux_and_not_summable_weight

namespace PercLib.CriticalLRP.Orchestration.Witness

open PercLib.CriticalLRP.Orchestration

/-- **The integrated first-moment formula for the explicit power-law witness.**  On an off-corner
radius window `Ioo a₀ b₀` of the literal model `sourceModelWitness d hd θ hθ`, with a finite second
cutoff moment at the right endpoint, the radius integral of the summed singleton pivotal flux over
any compact subinterval `[a, b] ⊂ (a₀, b₀)` is the increment of the cut mass.

Both model-level inputs of the general theorem are supplied by landed results: `hboundint` by
`PowerLawAC.sourceModelWitness_intervalIntegrable_pivotalWeight` (from the finite first moment at
`b₀`, derived from the second) and `hcontinf` by
`PowerLawContinuity.sourceModelWitness_hcontinf_of_moment_two`. -/
theorem sourceModelWitness_intervalIntegral_tsum_sMomentInfFlux_eq_sub_of_moment_two
    (d : ℕ) (hd : 1 ≤ d) (θ : ℝ) (hθ : 0 < θ)
    (T : ℕ → Finset (sourceModelWitness d hd θ hθ).V) (hTmono : Monotone T)
    (hT : ∀ y : (sourceModelWitness d hd θ hθ).V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 (sourceModelWitness d hd θ hθ).V)) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 (sourceModelWitness d hd θ hθ).V, ∃ n, e ∈ S n)
    {a₀ b₀ a b : ℝ} (ha₀ : 0 < a₀) (ha₀a : a₀ < a) (hab : a ≤ b) (hbb₀ : b < b₀)
    (hoff : ∀ r ∈ Set.Ioo a₀ b₀, r ∉ (sourceModelWitness d hd θ hθ).cornerRadii)
    (h2 : (sourceModelWitness d hd θ hθ).cutMoment 2 b₀ ≠ ⊤) :
    ∫ r in a..b, (∑' y : (sourceModelWitness d hd θ hθ).V,
        sMomentInfFlux (0 : (sourceModelWitness d hd θ hθ).V)
          ({y} : Finset (sourceModelWitness d hd θ hθ).V) (fun _ => (1 : ℝ))
          (sourceModelWitness d hd θ hθ).cutProb
          (sourceModelWitness d hd θ hθ).cutEdgeDeriv r)
      = (sourceModelWitness d hd θ hθ).cutMassReal b
        - (sourceModelWitness d hd θ hθ).cutMassReal a :=
  SourceModelData.intervalIntegral_tsum_sMomentInfFlux_eq_sub_of_cutMoment_two
    (sourceModelWitness d hd θ hθ) T hTmono hT S hSmono hS ha₀ ha₀a hab hbb₀ hoff
    (sourceModelWitness_hKd d hd θ hθ ha₀) h2
    (sourceModelWitness_intervalIntegrable_pivotalWeight d hd θ hθ ha₀
      ((sourceModelWitness d hd θ hθ).cutMoment_one_ne_top_of_two h2))
    (sourceModelWitness_hcontinf_of_moment_two d hd θ hθ ha₀ hoff h2)

/-- The explicit-model radius/vertex exchange with only a finite first cutoff moment at the
outer endpoint. The required second moment is supplied by the native cutoff-moment bound. -/
theorem sourceModelWitness_intervalIntegral_tsum_sMomentInfFlux_eq_sub_of_firstMoment
    (d : ℕ) (hd : 1 ≤ d) (θ : ℝ) (hθ : 0 < θ)
    (T : ℕ → Finset (sourceModelWitness d hd θ hθ).V) (hTmono : Monotone T)
    (hT : ∀ y : (sourceModelWitness d hd θ hθ).V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 (sourceModelWitness d hd θ hθ).V)) (hSmono : Monotone S)
    (hS : ∀ e : Sym2 (sourceModelWitness d hd θ hθ).V, ∃ n, e ∈ S n)
    {a₀ b₀ a b : ℝ} (ha₀ : 0 < a₀) (ha₀a : a₀ < a) (hab : a ≤ b) (hbb₀ : b < b₀)
    (hoff : ∀ r ∈ Set.Ioo a₀ b₀, r ∉ (sourceModelWitness d hd θ hθ).cornerRadii)
    (h1 : (sourceModelWitness d hd θ hθ).cutMoment 1 b₀ ≠ ⊤) :
    ∫ r in a..b, (∑' y : (sourceModelWitness d hd θ hθ).V,
        sMomentInfFlux (0 : (sourceModelWitness d hd θ hθ).V)
          ({y} : Finset (sourceModelWitness d hd θ hθ).V) (fun _ => (1 : ℝ))
          (sourceModelWitness d hd θ hθ).cutProb
          (sourceModelWitness d hd θ hθ).cutEdgeDeriv r)
      = (sourceModelWitness d hd θ hθ).cutMassReal b
        - (sourceModelWitness d hd θ hθ).cutMassReal a := by
  have hb₀ : 0 < b₀ := by
    calc
      0 < a₀ := ha₀
      _ < a := ha₀a
      _ ≤ b := hab
      _ < b₀ := hbb₀
  exact sourceModelWitness_intervalIntegral_tsum_sMomentInfFlux_eq_sub_of_moment_two
    d hd θ hθ T hTmono hT S hSmono hS ha₀ ha₀a hab hbb₀ hoff
    (sourceModelWitness_cutMoment_two_ne_top d hd θ hθ hb₀ h1)

end PercLib.CriticalLRP.Orchestration.Witness

#print axioms PercLib.CriticalLRP.Orchestration.Witness.sourceModelWitness_intervalIntegral_tsum_sMomentInfFlux_eq_sub_of_moment_two
#print axioms PercLib.CriticalLRP.Orchestration.Witness.sourceModelWitness_intervalIntegral_tsum_sMomentInfFlux_eq_sub_of_firstMoment
