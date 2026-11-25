/-
# The off-corner Russo derivative in terms of the literal excluded mass

Swarm `smwudd7jf`, member `m1`, direction **D1B**: assemble the off-corner cut-mass derivative
from pieces that already exist, in terms of the *literal* excluded mass `E1Sign.exclMass`, and
record exactly which input is not derivable from the landed modules.

## The three landed pieces

* `SourceModelData.hasDerivAt_cutMassReal_tsum_sMomentInfFlux`
  (`Analysis/Cutoff/IntegralFluxInterchange.lean`): the off-corner pointwise derivative
  `HasDerivAt M.cutMassReal (∑'_y flux_y r0) r0` of the cut mass, obtained by integrating the
  `y`-series first; no radius-uniform vertex majorant is used.
* `tendsto_sum_cutEdgeDeriv_mul_pivotalFlux`
  (`Analysis/Cutoff/Fibre/RussoAssembly/Main.lean`, D1C): the finite-window standardized
  excluded-flux sums converge along the cofinal diagonal `codeWindow` sequence to
  `β_c (-K'(r)) · (exclMass r).toReal`, given `exclMass r ≠ ⊤`.
* `SourceModelData.sum_cutEdgeDeriv_mul_pivotalFlux_eq_sum_pairIncr` (same file): the
  finite-window identity that makes each such sum an excluded-pair increment.

## What this file adds

The two series in the derivative theorem and in D1C are the same family of reals summed in the
two possible orders: the vertex series fixes the truncation at `A = {y}` and sums over edges, the
D1C sequence fixes an edge window and sums over a truncation.  Writing both as sums of one
function `pairFlux M r y e` of the pair `(y, e)` and comparing the orders gives

`∑'_y flux_y r = β_c (-K'(r)) · (exclMass r).toReal`,

hence the derivative value.  The comparison of the two orders is exactly what an interchange of
sums costs: it is available under the single hypothesis `habs` that the pair family is absolutely
summable at the radius in question.  Nothing here claims that `habs` holds; §4 records it as the
minimal remaining input and states the one inequality that survives without it.

## Not proved here

No absolute summability of the pair family, no radius-uniform majorant for `stdDegree`, no local
continuity of the summed flux, no large-radius moment finiteness, no uncapped `toReal`
conversion, no ODE and no corner statement.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.RussoExcluded.Defs
public import PercLib.CriticalLRP.Analysis.Cutoff.Incident.IncidentBall
public import PercLib.CriticalLRP.Analysis.Cutoff.IntegralFluxInterchange
public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.StrictDecrease
public import PercLib.CriticalLRP.Analysis.Cutoff.Resampling

/-!
# Conditional off-corner Russo derivative in excluded-mass form

The truncated pivotal flux expands into singleton vertex fluxes, giving one summand on
`M.V × Sym2 M.V`. Cofinal square windows compare the vertex-series and excluded-flux orders
under explicit summability. The actual derivative retains all regularity and moment hypotheses
of `IntegralFluxInterchange`, plus finite excluded mass and the required pair summability.
No radius-uniform majorant, uncapped moment, summability proof, or ODE is supplied here.
-/

@[expose] public section

noncomputable section

set_option linter.style.longLine false

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

attribute [local instance] Classical.propDecidable

/-! ## 1. The truncated pivotal flux is the sum of its singletons

`sMomentTrunc 1 0 A = ∑_{y ∈ A} sMomentTrunc 1 0 {y}` holds pointwise, and `flipDiff` is linear
in its argument pointwise.  What has to be paid for is the integral: each singleton pivotal
difference is an indicator difference, hence bounded by `1` in absolute value and integrable for
the probability measure `cutLaw r`. -/

/-- `flipDiff` is additive in the functional, pointwise in the configuration. -/
theorem flipDiff_finsetSum {ι : Type*} {A : Finset ι} {h : ι → Config M.V → ℝ}
    {e : Sym2 M.V} {ω : Config M.V} :
    flipDiff (fun ω => ∑ y ∈ A, h y ω) e ω = ∑ y ∈ A, flipDiff (h y) e ω := by
  simp only [flipDiff]
  rw [Finset.sum_sub_distrib]

/-- The singleton pivotal difference is an indicator difference, so it is bounded by `2`. -/
theorem abs_flipDiff_sMomentTrunc_singleton_le (y : M.V) (e : Sym2 M.V) (ω : Config M.V) :
    |flipDiff (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e ω| ≤ 2 := by
  rw [M.flipDiff_sMomentTrunc_singleton]
  by_cases h1 : y ∈ cluster (forceOn ({e} : Set (Sym2 M.V)) ({e} : Config M.V) ω) (0 : M.V) <;>
    by_cases h2 : y ∈ cluster (forceOn ({e} : Set (Sym2 M.V)) (∅ : Config M.V) ω) (0 : M.V) <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, h1, h2]

/-- The singleton pivotal difference is measurable. -/
theorem measurable_flipDiff_sMomentTrunc_singleton (y : M.V) (e : Sym2 M.V) :
    Measurable fun ω : Config M.V =>
      flipDiff (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e ω := by
  have hA : MeasurableSet {ω : Config M.V |
      y ∈ cluster (forceOn ({e} : Set (Sym2 M.V)) ({e} : Config M.V) ω) (0 : M.V)} :=
    (measurableSet_cluster_mem (0 : M.V) y).preimage
      (measurable_forceOn ({e} : Set (Sym2 M.V)) ({e} : Config M.V))
  have hB : MeasurableSet {ω : Config M.V |
      y ∈ cluster (forceOn ({e} : Set (Sym2 M.V)) (∅ : Config M.V) ω) (0 : M.V)} :=
    (measurableSet_cluster_mem (0 : M.V) y).preimage
      (measurable_forceOn ({e} : Set (Sym2 M.V)) (∅ : Config M.V))
  have h : Measurable fun ω : Config M.V =>
      (if ω ∈ {ω : Config M.V |
          y ∈ cluster (forceOn ({e} : Set (Sym2 M.V)) ({e} : Config M.V) ω) (0 : M.V)}
        then (1 : ℝ) else 0) -
      (if ω ∈ {ω : Config M.V |
          y ∈ cluster (forceOn ({e} : Set (Sym2 M.V)) (∅ : Config M.V) ω) (0 : M.V)}
        then (1 : ℝ) else 0) :=
    (Measurable.ite hA measurable_const measurable_const).sub
      (Measurable.ite hB measurable_const measurable_const)
  have hflip : (fun ω : Config M.V =>
        flipDiff (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e ω)
      = fun ω : Config M.V =>
          (if ω ∈ {ω : Config M.V |
              y ∈ cluster (forceOn ({e} : Set (Sym2 M.V)) ({e} : Config M.V) ω) (0 : M.V)}
            then (1 : ℝ) else 0) -
          (if ω ∈ {ω : Config M.V |
              y ∈ cluster (forceOn ({e} : Set (Sym2 M.V)) (∅ : Config M.V) ω) (0 : M.V)}
            then (1 : ℝ) else 0) := by
    funext ω
    rw [flipDiff_sMomentTrunc_singleton, Set.indicator_apply, Set.indicator_apply]
    simp only [Set.mem_ofPred_eq]
  rw [hflip]
  exact h

/-- The singleton pivotal difference is integrable for the cut law. -/
theorem integrable_flipDiff_sMomentTrunc_singleton (r : ℝ) (y : M.V) (e : Sym2 M.V) :
    Integrable (flipDiff (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e)
      (M.cutLaw r) :=
  Integrable.of_bound (M.measurable_flipDiff_sMomentTrunc_singleton y e).aestronglyMeasurable 2
    (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]
      exact M.abs_flipDiff_sMomentTrunc_singleton_le y e ω)

/-- **The truncated pivotal flux is the sum of the singleton ones.**  This is the only place
where an interchange has to be paid for, and it costs exactly the integrability of the bounded
singleton pivotal difference. -/
theorem pivotalFlux_sMomentTrunc_eq_sum_singleton (r : ℝ) (A : Finset M.V) (e : Sym2 M.V) :
    pivotalFlux (M.cutLaw r) (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A) e
      = ∑ y ∈ A, pivotalFlux (M.cutLaw r)
          (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e := by
  have hsplit : sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A
      = fun ω => ∑ y ∈ A,
          sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V) ω := by
    funext ω
    simp [sMomentTrunc]
  rw [pivotalFlux, hsplit]
  have hfun : (fun ω => flipDiff (fun ω => ∑ y ∈ A,
        sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V) ω) e ω)
      = fun ω => ∑ y ∈ A,
          flipDiff (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e ω :=
    funext fun ω => flipDiff_finsetSum M
  rw [hfun]
  exact integral_finsetSum A fun y _ => M.integrable_flipDiff_sMomentTrunc_singleton r y e

/-! ## 2. The two sums are the same family in the two orders -/

/-- **The finite-window standardized excluded flux is the finite truncation of the pair family.**
The left-hand side is the summand of D1C, the right-hand side is a finite partial sum of the
vertex series of the derivative theorem. -/
theorem sum_cutEdgeDeriv_mul_pivotalFlux_eq_sum_pairFlux (A X : Finset M.V) (r : ℝ) :
    ∑ e ∈ X.sym2, M.cutEdgeDeriv r e *
        pivotalFlux (M.cutLaw r) (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A) e
      = ∑ y ∈ A, ∑ e ∈ X.sym2, M.pairFlux r y e := by
  have h : ∀ e ∈ X.sym2, M.cutEdgeDeriv r e *
      pivotalFlux (M.cutLaw r) (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) A) e
      = ∑ y ∈ A, M.pairFlux r y e := by
    intro e _
    rw [M.pivotalFlux_sMomentTrunc_eq_sum_singleton, Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => rfl
  rw [Finset.sum_congr rfl h, Finset.sum_comm]

/-- The canonical square windows `codeWindow k × (codeWindow k).sym2` are cofinal in the finite
subsets of `M.V × Sym2 M.V`. -/
theorem tendsto_codeWindow_product :
    Tendsto (fun k : ℕ => codeWindow M.V k ×ˢ (codeWindow M.V k).sym2) atTop atTop := by
  refine tendsto_atTop_atTop.mpr fun S => ?_
  obtain ⟨k, hk⟩ := exists_codeWindow_subset M.V
    (S.biUnion fun p : M.V × Sym2 M.V => insert p.1 p.2.toFinset)
  refine ⟨k, fun k' hk' p hp => ?_⟩
  have hmono : codeWindow M.V k ⊆ codeWindow M.V k' := monotone_codeWindow M.V hk'
  refine Finset.mem_product.mpr ⟨?_, Finset.mem_sym2_iff.mpr fun a ha => ?_⟩
  · exact hmono (hk (Finset.mem_biUnion.mpr
      ⟨p, hp, Finset.mem_insert_self p.1 p.2.toFinset⟩))
  · exact hmono (hk (Finset.mem_biUnion.mpr
      ⟨p, hp, Finset.mem_insert_of_mem (Sym2.mem_toFinset.mpr ha)⟩))

/-- Absolute summability of the pair family makes the square windows converge to its sum. -/
theorem tendsto_sum_rect_pairFlux {r : ℝ}
    (habs : Summable fun p : M.V × Sym2 M.V => |M.pairFlux r p.1 p.2|) :
    Tendsto (fun k : ℕ => ∑ p ∈ codeWindow M.V k ×ˢ (codeWindow M.V k).sym2,
        M.pairFlux r p.1 p.2)
      atTop (𝓝 (∑' p : M.V × Sym2 M.V, M.pairFlux r p.1 p.2)) :=
  ((Summable.of_norm (by simpa [Real.norm_eq_abs] using habs)).hasSum).comp
    M.tendsto_codeWindow_product

/-! ## 3. The derivative value is the standardized excluded mass -/

/-- **The summed flux in terms of the literal excluded mass.**

Under absolute summability of the pair family at `r`, the vertex series of the cut-mass
derivative and the cofinal excluded-flux sums of D1C have the same sum, so the derivative value
`∑'_y flux_y r` equals `β_c (-K'(r)) · (exclMass r).toReal`.

`exclMass r ≠ ⊤` is required, exactly as in D1C: without it `toReal ⊤ = 0` would force a
nonnegative quantity to vanish.  The sign of `deriv K r` is *not* assumed — the identity is a
limit of an identity of finite sums, not a supremum of reals. -/
theorem tsum_sMomentInfFlux_eq_betaCrit_mul_exclMass {r : ℝ}
    (hE : E1Sign.exclMass M r ≠ ⊤)
    (habs : Summable fun p : M.V × Sym2 M.V => |M.pairFlux r p.1 p.2|) :
    (∑' y : M.V, sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv r)
      = (M.betaCrit : ℝ) * (-(deriv M.K r)) * (E1Sign.exclMass M r).toReal := by
  have hrect := M.tendsto_sum_rect_pairFlux habs
  have hD := tendsto_sum_cutEdgeDeriv_mul_pivotalFlux M r hE
  have hcongr : (fun k : ℕ => ∑ e ∈ (codeWindow M.V k).sym2, M.cutEdgeDeriv r e *
        pivotalFlux (M.cutLaw r)
          (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) (codeWindow M.V k)) e)
      = fun k : ℕ => ∑ p ∈ codeWindow M.V k ×ˢ (codeWindow M.V k).sym2,
          M.pairFlux r p.1 p.2 := by
    funext k
    rw [M.sum_cutEdgeDeriv_mul_pivotalFlux_eq_sum_pairFlux, Finset.sum_product]
  have hval : (∑' p : M.V × Sym2 M.V, M.pairFlux r p.1 p.2)
      = (M.betaCrit : ℝ) * (-(deriv M.K r)) * (E1Sign.exclMass M r).toReal :=
    tendsto_nhds_unique hrect (hcongr ▸ hD)
  have hsum : Summable fun p : M.V × Sym2 M.V => M.pairFlux r p.1 p.2 :=
    Summable.of_norm (by simpa [Real.norm_eq_abs] using habs)
  calc (∑' y : M.V, sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv r)
      = ∑' y : M.V, ∑' e : Sym2 M.V, M.pairFlux r y e :=
        tsum_congr fun y => sMomentInfFlux_eq_tsum_pairIncrFlux M {y} r
    _ = ∑' p : M.V × Sym2 M.V, M.pairFlux r p.1 p.2 :=
        (hsum.tsum_prod (f := fun p : M.V × Sym2 M.V => M.pairFlux r p.1 p.2)).symm
    _ = (M.betaCrit : ℝ) * (-(deriv M.K r)) * (E1Sign.exclMass M r).toReal := hval

/-- **The conditional actual off-corner derivative of the cut mass, with the excluded-mass
value.**

All regularity, mixed-moment, nonnegativity, pointwise summability, per-vertex interval
integrability and summed-flux continuity premises are those of the landed
`hasDerivAt_cutMassReal_tsum_sMomentInfFlux`; the only *new* input is the absolute summability
`habs` of the pair family at `r0`, together with `exclMass r0 ≠ ⊤` from D1C. -/
theorem hasDerivAt_cutMassReal_eq_betaCrit_mul_exclMass
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {α β r0 : ℝ} (hα0 : 0 < α) (hαr0 : α < r0) (hr0β : r0 < β)
    (hoff : ∀ r ∈ Set.Ioo α β, r ∉ M.cornerRadii)
    (hKd : ∀ r ∈ Set.Ioo α β, DifferentiableAt ℝ M.K r)
    (hdom : ∀ r ∈ Set.Ioo α β, Summable fun e : Sym2 M.V =>
      |M.cutEdgeDeriv r e| * (2 * (M.cutLaw r).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)}))
    (hboundint : ∀ y : M.V, ∀ a' ∈ Set.Ioo α β, ∀ b' ∈ Set.Ioo α β, IntervalIntegrable
      (sMomentWeight (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) volume a' b')
    (hmeasK : ∀ y : M.V, ∀ k : ℕ, AEStronglyMeasurable (windowFluxOf (0 : M.V)
      (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) {y}) S M.cutProb M.cutEdgeDeriv k) volume)
    (hmeasinf : ∀ y : M.V, ∀ r ∈ Set.Ioo α β, StronglyMeasurableAtFilter
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) (𝓝 r) volume)
    (hcontinf : ∀ y : M.V, ∀ r ∈ Set.Ioo α β, ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hfin : ∀ r ∈ Set.Ioo α β, M.cutMassAt r 0 ≠ ⊤)
    (hfluxnn : ∀ y : M.V, ∀ r ∈ Set.Ioo α β, 0 ≤
      sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r)
    (hsummable : ∀ r ∈ Set.Ioo α β, Summable fun y : M.V =>
      sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r)
    (hfluxintW : ∀ y : M.V, ∀ a' ∈ Set.Ioo α β, ∀ b' ∈ Set.Ioo α β, IntervalIntegrable (fun r =>
      sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r) volume a' b')
    (hGcont : ∀ r ∈ Set.Ioo α β, ContinuousAt (fun r' => ∑' y : M.V,
      sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r') r)
    (hE : E1Sign.exclMass M r0 ≠ ⊤)
    (habs : Summable fun p : M.V × Sym2 M.V => |M.pairFlux r0 p.1 p.2|) :
    HasDerivAt M.cutMassReal
      ((M.betaCrit : ℝ) * (-(deriv M.K r0)) * (E1Sign.exclMass M r0).toReal) r0 := by
  have hd := M.hasDerivAt_cutMassReal_tsum_sMomentInfFlux T hTmono hT S hSmono hS hα0 hαr0 hr0β
    hoff hKd hdom hboundint hmeasK hmeasinf hcontinf hfin hfluxnn hsummable hfluxintW hGcont
  rwa [M.tsum_sMomentInfFlux_eq_betaCrit_mul_exclMass hE habs] at hd

/-! ## 4. The one-sided bound: what survives without the interchange

The converse of §3 needs the absolute summability `habs`.  The *inequality* half needs much less:
with the source's slope sign `deriv K r ≤ 0` every `pairFlux` is nonnegative, and then each finite
rectangle sum is at most the full vertex series, so the excluded-mass value is a one-sided bound
on the summed flux.  The equality defect of §3 is therefore one-sided: nothing can exceed
`∑'_y flux_y r`. -/

/-- `pairFlux` is nonnegative under the source's slope sign. -/
theorem pairFlux_nonneg {r : ℝ} (hr : 0 < r) (y : M.V) (e : Sym2 M.V) :
    0 ≤ M.pairFlux r y e := by
  rw [SourceModelData.pairFlux, pivotalFlux]
  exact mul_nonneg (M.cutEdgeDeriv_nonneg (M.neg_deriv_K_nonneg hr) e)
    (integral_nonneg fun ω => M.flipDiff_sMomentTrunc_singleton_nonneg y e ω)

/-- **The standardized excluded mass is a lower bound for the summed flux, without any
interchange hypothesis.**

Here the per-`y` edge series is required to be summable (otherwise the `tsum` defining
`sMomentInfFlux` is the junk value `0` and the inequality is false), and the vertex series too; the
absolute summability `habs` of the *pair* family is **not** needed. -/
theorem le_tsum_sMomentInfFlux_betaCrit_mul_exclMass {r : ℝ} (hr : 0 < r)
    (hE : E1Sign.exclMass M r ≠ ⊤)
    (hinner : ∀ y : M.V, Summable fun e : Sym2 M.V => M.pairFlux r y e)
    (hsumm : Summable fun y : M.V =>
      sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv r) :
    (M.betaCrit : ℝ) * (-(deriv M.K r)) * (E1Sign.exclMass M r).toReal
      ≤ ∑' y : M.V, sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
          M.cutProb M.cutEdgeDeriv r := by
  have hnn : ∀ (y : M.V) (e : Sym2 M.V), 0 ≤ M.pairFlux r y e := fun y e =>
    M.pairFlux_nonneg hr y e
  have hD := tendsto_sum_cutEdgeDeriv_mul_pivotalFlux M r hE
  have hcongr : (fun k : ℕ => ∑ e ∈ (codeWindow M.V k).sym2, M.cutEdgeDeriv r e *
        pivotalFlux (M.cutLaw r)
          (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) (codeWindow M.V k)) e)
      = fun k : ℕ => ∑ p ∈ codeWindow M.V k ×ˢ (codeWindow M.V k).sym2,
          M.pairFlux r p.1 p.2 := by
    funext k
    rw [M.sum_cutEdgeDeriv_mul_pivotalFlux_eq_sum_pairFlux, Finset.sum_product]
  refine le_of_tendsto' (hcongr ▸ hD) fun k => ?_
  rw [Finset.sum_product]
  calc ∑ y ∈ codeWindow M.V k, ∑ e ∈ (codeWindow M.V k).sym2, M.pairFlux r y e
      ≤ ∑ y ∈ codeWindow M.V k, ∑' e : Sym2 M.V, M.pairFlux r y e :=
        Finset.sum_le_sum fun y _ => (hinner y).sum_le_tsum _ fun e _ => hnn y e
    _ = ∑ y ∈ codeWindow M.V k, sMomentInfFlux (0 : M.V) ({y} : Finset M.V)
          (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r :=
        Finset.sum_congr rfl fun y _ => (sMomentInfFlux_eq_tsum_pairIncrFlux M {y} r).symm
    _ ≤ ∑' y : M.V, sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
          M.cutProb M.cutEdgeDeriv r :=
        hsumm.sum_le_tsum _ fun y _ => tsum_nonneg fun e => hnn y e

/-- **Nonnegative per-`y` edge summability plus vertex summability give the pair summability.**

Under the source's slope sign every `pairFlux` is nonnegative, so the absolute summability `habs`
used in §3 costs no more than: each `y`-fibre of the edge series converges, and the vertex series
converges (the latter is already a hypothesis of the landed derivative theorem).  The proof bounds
every finite partial sum by a rectangle, and each rectangle by the vertex series. -/
theorem summable_abs_pairFlux_of_nonneg {r : ℝ}
    (hnn : ∀ (y : M.V) (e : Sym2 M.V), 0 ≤ M.pairFlux r y e)
    (hinner : ∀ y : M.V, Summable fun e : Sym2 M.V => M.pairFlux r y e)
    (hsumm : Summable fun y : M.V =>
      sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv r) :
    Summable fun p : M.V × Sym2 M.V => |M.pairFlux r p.1 p.2| := by
  have hfluxnn : ∀ y : M.V, 0 ≤ sMomentInfFlux (0 : M.V) ({y} : Finset M.V)
      (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r := fun y =>
    tsum_nonneg fun e => hnn y e
  refine summable_of_sum_le (f := fun p : M.V × Sym2 M.V => |M.pairFlux r p.1 p.2|)
    (c := ∑' y : M.V, sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
      M.cutProb M.cutEdgeDeriv r) (fun p => abs_nonneg _) fun s => ?_
  have hrect : ∀ p : M.V × Sym2 M.V, |M.pairFlux r p.1 p.2| = M.pairFlux r p.1 p.2 :=
    fun p => abs_of_nonneg (hnn p.1 p.2)
  rw [Finset.sum_congr rfl fun p _ => hrect p]
  calc ∑ p ∈ s, M.pairFlux r p.1 p.2
      ≤ ∑ p ∈ s.image Prod.fst ×ˢ s.image Prod.snd, M.pairFlux r p.1 p.2 :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun p hp => Finset.mem_product.mpr
            ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩)
          (fun p _ _ => hnn p.1 p.2)
    _ = ∑ y ∈ s.image Prod.fst, ∑ e ∈ s.image Prod.snd, M.pairFlux r y e :=
        Finset.sum_product _ _ _
    _ ≤ ∑ y ∈ s.image Prod.fst, ∑' e : Sym2 M.V, M.pairFlux r y e :=
        Finset.sum_le_sum fun y _ => (hinner y).sum_le_tsum _ fun e _ => hnn y e
    _ = ∑ y ∈ s.image Prod.fst, sMomentInfFlux (0 : M.V) ({y} : Finset M.V)
          (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r :=
        Finset.sum_congr rfl fun y _ => (sMomentInfFlux_eq_tsum_pairIncrFlux M {y} r).symm
    _ ≤ ∑' y : M.V, sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
          M.cutProb M.cutEdgeDeriv r :=
        hsumm.sum_le_tsum _ fun y _ => hfluxnn y

/-- **The equality is exactly the missing domination, in the nonnegative case.**

Under the source's slope sign, per-`y` edge summability and vertex summability, the summed flux
equals `β_c (-K'(r)) (exclMass r).toReal` **iff** it is at most that value: §4 gives the reverse
inequality for free.  So the only remaining content of the off-corner Russo derivative at `r` is
the one-sided domination `∑'_y flux_y r ≤ β_c (-K'(r)) (exclMass r).toReal`. -/
theorem tsum_eq_iff_le_betaCrit_mul_exclMass {r : ℝ} (hr : 0 < r)
    (hE : E1Sign.exclMass M r ≠ ⊤)
    (hinner : ∀ y : M.V, Summable fun e : Sym2 M.V => M.pairFlux r y e)
    (hsumm : Summable fun y : M.V =>
      sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv r) :
    ((∑' y : M.V, sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv r)
        = (M.betaCrit : ℝ) * (-(deriv M.K r)) * (E1Sign.exclMass M r).toReal)
      ↔ ((∑' y : M.V, sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv r)
        ≤ (M.betaCrit : ℝ) * (-(deriv M.K r)) * (E1Sign.exclMass M r).toReal) := by
  have hle := M.le_tsum_sMomentInfFlux_betaCrit_mul_exclMass hr hE hinner hsumm
  constructor
  · intro h
    rw [h]
  · intro h
    exact le_antisymm h hle

/-- **The same conditional actual derivative, with the pair summability derived rather than
assumed.**

Compared with `hasDerivAt_cutMassReal_eq_betaCrit_mul_exclMass`, the hypothesis `habs` is replaced
by per-`y` edge summability, the slope sign at `r0` being automatic from `0 < r0` — and the vertex series
summability that the derivation needs is already one of the landed theorem's hypotheses. -/
theorem hasDerivAt_cutMassReal_eq_betaCrit_mul_exclMass_of_nonneg
    (T : ℕ → Finset M.V) (hTmono : Monotone T) (hT : ∀ y : M.V, ∃ n, y ∈ T n)
    (S : ℕ → Finset (Sym2 M.V)) (hSmono : Monotone S) (hS : ∀ e : Sym2 M.V, ∃ n, e ∈ S n)
    {α β r0 : ℝ} (hα0 : 0 < α) (hαr0 : α < r0) (hr0β : r0 < β)
    (hoff : ∀ r ∈ Set.Ioo α β, r ∉ M.cornerRadii)
    (hKd : ∀ r ∈ Set.Ioo α β, DifferentiableAt ℝ M.K r)
    (hdom : ∀ r ∈ Set.Ioo α β, Summable fun e : Sym2 M.V =>
      |M.cutEdgeDeriv r e| * (2 * (M.cutLaw r).real {ω : Config M.V | e ∈ touchSet ω (0 : M.V)}))
    (hboundint : ∀ y : M.V, ∀ a' ∈ Set.Ioo α β, ∀ b' ∈ Set.Ioo α β, IntervalIntegrable
      (sMomentWeight (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) volume a' b')
    (hmeasK : ∀ y : M.V, ∀ k : ℕ, AEStronglyMeasurable (windowFluxOf (0 : M.V)
      (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) {y}) S M.cutProb M.cutEdgeDeriv k) volume)
    (hmeasinf : ∀ y : M.V, ∀ r ∈ Set.Ioo α β, StronglyMeasurableAtFilter
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) (𝓝 r) volume)
    (hcontinf : ∀ y : M.V, ∀ r ∈ Set.Ioo α β, ContinuousAt
      (sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv) r)
    (hfin : ∀ r ∈ Set.Ioo α β, M.cutMassAt r 0 ≠ ⊤)
    (hfluxnn : ∀ y : M.V, ∀ r ∈ Set.Ioo α β, 0 ≤
      sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r)
    (hsummable : ∀ r ∈ Set.Ioo α β, Summable fun y : M.V =>
      sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r)
    (hfluxintW : ∀ y : M.V, ∀ a' ∈ Set.Ioo α β, ∀ b' ∈ Set.Ioo α β, IntervalIntegrable (fun r =>
      sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r) volume a' b')
    (hGcont : ∀ r ∈ Set.Ioo α β, ContinuousAt (fun r' => ∑' y : M.V,
      sMomentInfFlux (0 : M.V) {y} (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r') r)
    (hr0 : 0 < r0)
    (hE : E1Sign.exclMass M r0 ≠ ⊤)
    (hinner : ∀ y : M.V, Summable fun e : Sym2 M.V => M.pairFlux r0 y e) :
    HasDerivAt M.cutMassReal
      ((M.betaCrit : ℝ) * (-(deriv M.K r0)) * (E1Sign.exclMass M r0).toReal) r0 :=
  M.hasDerivAt_cutMassReal_eq_betaCrit_mul_exclMass T hTmono hT S hSmono hS hα0 hαr0 hr0β
    hoff hKd hdom hboundint hmeasK hmeasinf hcontinf hfin hfluxnn hsummable hfluxintW hGcont hE
    (M.summable_abs_pairFlux_of_nonneg (fun y e => M.pairFlux_nonneg hr0 y e) hinner
      (hsummable r0 ⟨hαr0, hr0β⟩))

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

set_option linter.hashCommand false

namespace PercLib.CriticalLRP.Orchestration

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.flipDiff_finsetSum
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.abs_flipDiff_sMomentTrunc_singleton_le
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.measurable_flipDiff_sMomentTrunc_singleton
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.integrable_flipDiff_sMomentTrunc_singleton
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.pivotalFlux_sMomentTrunc_eq_sum_singleton
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.sum_cutEdgeDeriv_mul_pivotalFlux_eq_sum_pairFlux
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_codeWindow_product
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_sum_rect_pairFlux
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tsum_sMomentInfFlux_eq_betaCrit_mul_exclMass
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.hasDerivAt_cutMassReal_eq_betaCrit_mul_exclMass
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.pairFlux_nonneg
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.le_tsum_sMomentInfFlux_betaCrit_mul_exclMass
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.summable_abs_pairFlux_of_nonneg
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tsum_eq_iff_le_betaCrit_mul_exclMass
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.hasDerivAt_cutMassReal_eq_betaCrit_mul_exclMass_of_nonneg

end PercLib.CriticalLRP.Orchestration
