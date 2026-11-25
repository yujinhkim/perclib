/-
# Per-`y` edge summability of the off-corner pair flux

Swarm `smwue873v`, member `m1`.

`SourceModelData.pairFlux M r y e` is the `(y, e)`-summand of the off-corner cut-mass derivative
(`RussoExcluded/Defs`).  The residual input of `RussoExcluded/Main` is the *per-`y` edge
summability* of this family.  This file proves it, with no new hypotheses beyond the ones the
landed off-corner machinery already uses:

* `0 < r`,
* the off-corner condition `r ∉ M.attainedRadii`,
* finiteness of the mixed first moment `∫⁻ ω, |K_0(ω)| · 1{y ∈ K_0(ω)} ∂P_r` at that radius.

The route is the landed mixed incident transport (`Incident/Transport`), applied to the
standardised weight `stdEdgeWeight r`:

  `|c_r(e) · pivotal_e| ≤ stdEdgeWeight r e · P_r({y ∈ K_0} ∩ {e touches K_0})`

(`abs_pairFlux_le_stdEdgeWeight_mul_evEdge`), and the incident transport makes the right-hand side
summable in `e` from the finite mixed first moment alone
(`summable_stdEdgeWeight_mul_evEdge`), because the per-vertex incident mass of `stdEdgeWeight r` is
`< ∞` — it is at most the *fixed-radius* constant `stdDegree r` of `OffCorner/Degree`.  That
constant is not bounded in `r` (`OffCorner/UniformObstruction`), but summability is needed at one
radius at a time, so this is harmless.

Nothing here proves finiteness of any large-radius moment, no `y`-summability, no derivative, no
ODE.  The `y`-series summability `Summable fun y => sMomentInfFlux …` remains a hypothesis of the
landed statements; §5 only records how the per-`y` edge summability discharges the hypothesis
`hinner` of the landed theorems that take it explicitly, and §6 removes `hinner` from the landed
conditional derivative.

Three limits of the transport, stated so that they are not mistaken for gaps here:

* it is *per-`y`*: the bound `∑'_e |pairFlux r y e| ≤ stdDegree r · E_r[|K_0| 1{y ∈ K_0}]` does not
  sum in `y` without summability of the mixed density, which is a second-moment statement
  (`IntegralFluxInterchange.abs_sMomentInfFlux_le` records the same obstruction);
* it is *per-radius*: `stdDegree r` is finite at each fixed `r` but not bounded in `r`
  (`OffCorner/UniformObstruction`);
* it is *off-corner*: at an attained radius `r = dist x y` the edge weight `c_r(e)` is
  `β_c(-K'(r)) > 0` while `stdEdgeWeight r e = c_r(e)/q_e(r)` is Lean's `0/0 = 0`, so the per-edge
  majorant degenerates to `0 ≤ 0` there and this route gives nothing.  §3 therefore keeps
  `r ∉ M.attainedRadii`; nothing here decides the attained-radius case.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.Flux
public import PercLib.CriticalLRP.Analysis.Cutoff.RussoExcluded.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.CutoffMomentContinuity

/-!
# Per-`y` edge summability from a finite mixed first moment

The off-corner pair family is shown absolutely summable in the edge variable at every off-corner
radius where the mixed first moment of the cluster volume is finite; the `y`-series summability is
not addressed.
-/

set_option linter.style.longLine false
set_option linter.hashCommand false

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

attribute [local instance] Classical.propDecidable

/-! ## 1. The termwise standardised majorant

This is the `hterm` step of the landed `abs_sMomentInfFlux_le_mixed`, isolated: the absolute value
of the `(y, e)`-summand is at most the standardised edge weight times the probability of the
*coupled* event `{y ∈ K_0} ∩ {e touches K_0}`.  Two inputs are used: `0 < r` for nonnegativity of
the cutoff derivative weight, and `r ∉ attainedRadii` so that a vanishing open probability forces
the weight to vanish. -/

/-- **The per-edge standardised majorant of the off-corner pair flux.** -/
theorem abs_pairFlux_le_stdEdgeWeight_mul_evEdge {r : ℝ} (hr : 0 < r)
    (hoff : r ∉ M.attainedRadii) (y : M.V) (e : Sym2 M.V) :
    |M.pairFlux r y e|
      ≤ M.stdEdgeWeight r e * (M.cutLaw r).real (evEdge (o := (0 : M.V)) (y := y) e) := by
  classical
  have hpos : ∀ e : Sym2 M.V, 0 ≤ M.cutEdgeDeriv r e :=
    fun e => M.cutEdgeDeriv_nonneg (M.neg_deriv_K_nonneg hr) e
  have hq0 : ∀ e : Sym2 M.V, M.openProb r e = 0 → M.cutEdgeDeriv r e = 0 :=
    fun e hq => M.openProb_eq_zero_imp_cutEdgeDeriv_eq_zero hr hoff hq
  have hpiv : ∀ e : Sym2 M.V, 0 ≤ pivotalFlux (M.cutLaw r)
      (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e := by
    intro e
    rw [pivotalFlux]
    exact integral_nonneg fun ω => flipDiff_sMomentTrunc_singleton_nonneg (M := M) y e ω
  rw [SourceModelData.pairFlux, abs_mul, abs_of_nonneg (hpos e), abs_of_nonneg (hpiv e)]
  by_cases hq : M.openProb r e = 0
  · rw [SourceModelData.stdEdgeWeight, hq0 e hq, hq, zero_div, zero_mul, zero_mul]
  · exact M.cutEdgeDeriv_mul_pivotalFlux_le (r := r) (y := y) (e := e) (hpos e)
      (lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hq))

/-! ## 2. The standardised weight is a summable edge weighting

At a fixed radius the per-vertex incident mass of `stdEdgeWeight r` is bounded by `stdDegree r`
(`vertexWeight_stdEdgeWeight_le_stdDegree`, valid at every `r > 0`), so the incident transport
`sum_weight_mixed_le` bounds every finite sum of the coupled probabilities by
`stdDegree r · E_r[|K_0| 1{y ∈ K_0}]`.  Summability follows from `summable_of_sum_le`.

Note that no off-corner hypothesis is needed here: `stdEdgeWeight r e = c_r(e)/q_e(r)` is Lean's
`0` when `q_e(r) = 0`, which is a nonnegative value. -/

/-- **The standardised edge weighting is summable against the coupled events** from a finite mixed
first moment. -/
theorem summable_stdEdgeWeight_mul_evEdge {r : ℝ} (hr : 0 < r) (y : M.V)
    (hfin : ∫⁻ ω, clusterVol ω (0 : M.V)
      * (if y ∈ cluster ω (0 : M.V) then (1 : ℝ≥0∞) else 0) ∂(M.cutLaw r) ≠ ⊤) :
    Summable fun e : Sym2 M.V =>
      M.stdEdgeWeight r e * (M.cutLaw r).real (evEdge (o := (0 : M.V)) (y := y) e) := by
  classical
  have hpos : ∀ e : Sym2 M.V, 0 ≤ M.cutEdgeDeriv r e :=
    fun e => M.cutEdgeDeriv_nonneg (M.neg_deriv_K_nonneg hr) e
  have hD : (0 : ℝ) ≤ M.stdDegree r := M.stdDegree_nonneg hr
  have hdeg : ∀ x : M.V, ∀ u : Finset (Sym2 M.V),
      PercLib.CriticalLRP.vertexWeight (M.stdEdgeWeight r) x u ≤ M.stdDegree r :=
    fun x u => M.vertexWeight_stdEdgeWeight_le_stdDegree hr x u
  have hw : ∀ e : Sym2 M.V, 0 ≤ M.stdEdgeWeight r e := by
    intro e
    rw [SourceModelData.stdEdgeWeight]
    have hqnn : 0 ≤ M.openProb r e := measureReal_nonneg
    rcases eq_or_lt_of_le hqnn with h | h
    · rw [← h, div_zero]
    · exact div_nonneg (hpos e) h.le
  refine summable_of_sum_le (c := M.stdDegree r * (∫⁻ ω, clusterVol ω (0 : M.V)
    * (if y ∈ cluster ω (0 : M.V) then (1 : ℝ≥0∞) else 0) ∂(M.cutLaw r)).toReal)
    (fun e => mul_nonneg (hw e) measureReal_nonneg) fun u => ?_
  exact sum_weight_mixed_le (o := (0 : M.V)) (y := y) (M.cutLaw r) (M.stdEdgeWeight r)
    hD hw hdeg hfin u

/-! ## 3. The pair family is absolutely summable in the edge variable -/

/-- **Absolute per-`y` edge summability of the off-corner pair flux.** -/
theorem summable_abs_pairFlux {r : ℝ} (hr : 0 < r) (hoff : r ∉ M.attainedRadii) (y : M.V)
    (hfin : ∫⁻ ω, clusterVol ω (0 : M.V)
      * (if y ∈ cluster ω (0 : M.V) then (1 : ℝ≥0∞) else 0) ∂(M.cutLaw r) ≠ ⊤) :
    Summable fun e : Sym2 M.V => |M.pairFlux r y e| :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
    (fun e => M.abs_pairFlux_le_stdEdgeWeight_mul_evEdge hr hoff y e)
    (M.summable_stdEdgeWeight_mul_evEdge hr y hfin)

/-- **Per-`y` edge summability of the off-corner pair flux** — the residual input of
`RussoExcluded/Main`, from exactly `0 < r`, `r ∉ attainedRadii` and a finite mixed first moment. -/
theorem summable_pairFlux {r : ℝ} (hr : 0 < r) (hoff : r ∉ M.attainedRadii) (y : M.V)
    (hfin : ∫⁻ ω, clusterVol ω (0 : M.V)
      * (if y ∈ cluster ω (0 : M.V) then (1 : ℝ≥0∞) else 0) ∂(M.cutLaw r) ≠ ⊤) :
    Summable fun e : Sym2 M.V => M.pairFlux r y e :=
  Summable.of_norm
    (by simpa only [Real.norm_eq_abs] using M.summable_abs_pairFlux hr hoff y hfin)

/-- The quantitative form: the `ℓ¹` mass of the `y`-th edge series is at most the fixed-radius
degree constant times the mixed cluster density at the same radius. -/
theorem tsum_abs_pairFlux_le_stdDegree_mixed {r : ℝ} (hr : 0 < r)
    (hoff : r ∉ M.attainedRadii) (y : M.V)
    (hfin : ∫⁻ ω, clusterVol ω (0 : M.V)
      * (if y ∈ cluster ω (0 : M.V) then (1 : ℝ≥0∞) else 0) ∂(M.cutLaw r) ≠ ⊤) :
    ∑' e : Sym2 M.V, |M.pairFlux r y e| ≤ M.stdDegree r * M.mixedFluxDensity r y := by
  classical
  have hpos : ∀ e : Sym2 M.V, 0 ≤ M.cutEdgeDeriv r e :=
    fun e => M.cutEdgeDeriv_nonneg (M.neg_deriv_K_nonneg hr) e
  have hD : (0 : ℝ) ≤ M.stdDegree r := M.stdDegree_nonneg hr
  have hdeg : ∀ x : M.V, ∀ u : Finset (Sym2 M.V),
      PercLib.CriticalLRP.vertexWeight (M.stdEdgeWeight r) x u ≤ M.stdDegree r :=
    fun x u => M.vertexWeight_stdEdgeWeight_le_stdDegree hr x u
  have hw : ∀ e : Sym2 M.V, 0 ≤ M.stdEdgeWeight r e := by
    intro e
    rw [SourceModelData.stdEdgeWeight]
    have hqnn : 0 ≤ M.openProb r e := measureReal_nonneg
    rcases eq_or_lt_of_le hqnn with h | h
    · rw [← h, div_zero]
    · exact div_nonneg (hpos e) h.le
  have hmain := tsum_weight_mixed_touch_le (o := (0 : M.V)) (y := y) (M.cutLaw r)
    (M.stdEdgeWeight r) hD hw hdeg hfin
  calc ∑' e : Sym2 M.V, |M.pairFlux r y e|
      ≤ ∑' e : Sym2 M.V,
          M.stdEdgeWeight r e * (M.cutLaw r).real (evEdge (o := (0 : M.V)) (y := y) e) :=
        (M.summable_abs_pairFlux hr hoff y hfin).tsum_le_tsum
          (fun e => M.abs_pairFlux_le_stdEdgeWeight_mul_evEdge hr hoff y e)
          (M.summable_stdEdgeWeight_mul_evEdge hr y hfin)
    _ ≤ M.stdDegree r * (∫⁻ ω, clusterVol ω (0 : M.V)
          * (if y ∈ cluster ω (0 : M.V) then (1 : ℝ≥0∞) else 0) ∂(M.cutLaw r)).toReal := hmain
    _ = M.stdDegree r * M.mixedFluxDensity r y := rfl

end SourceModelData

end PercLib.CriticalLRP.Orchestration

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

attribute [local instance] Classical.propDecidable

/-! ## 4. An ordinary first cutoff moment suffices

The mixed first moment `E_r[|K_0| 1{y ∈ K_0}]` is at most the plain first cutoff moment
`E_r|K_0| = M.cutMoment 1 r`, so a finite first cutoff moment at the single radius `r` implies the
hypothesis of §3.  No other moment enters. -/

/-- The mixed first moment is dominated by the plain first cutoff moment. -/
theorem lintegral_mixed_le_cutMoment (r : ℝ) (y : M.V) :
    (∫⁻ ω, clusterVol ω (0 : M.V)
        * (if y ∈ cluster ω (0 : M.V) then (1 : ℝ≥0∞) else 0) ∂(M.cutLaw r))
      ≤ M.cutMoment 1 r := by
  rw [SourceModelData.cutMoment]
  refine lintegral_mono fun ω => ?_
  have hind : (if y ∈ cluster ω (0 : M.V) then (1 : ℝ≥0∞) else 0) ≤ 1 := by
    split <;> simp
  calc clusterVol ω (0 : M.V) * (if y ∈ cluster ω (0 : M.V) then (1 : ℝ≥0∞) else 0)
      ≤ clusterVol ω (0 : M.V) * 1 := mul_le_mul_of_nonneg_left hind zero_le
    _ = (clusterVol ω (0 : M.V)) ^ 1 := by rw [pow_one, mul_one]

/-- **Per-`y` edge summability from a finite first cutoff moment at `r`.** -/
theorem summable_pairFlux_of_cutMoment_ne_top {r : ℝ} (hr : 0 < r)
    (hoff : r ∉ M.attainedRadii) (hmass : M.cutMoment 1 r ≠ ⊤) (y : M.V) :
    Summable fun e : Sym2 M.V => M.pairFlux r y e :=
  M.summable_pairFlux hr hoff y
    (ne_top_of_le_ne_top hmass (M.lintegral_mixed_le_cutMoment r y))

/-- The same with `M.cutMassAt r 0`, the form in which the landed derivative theorems carry the
first-moment finiteness. -/
theorem summable_pairFlux_of_cutMassAt_ne_top {r : ℝ} (hr : 0 < r)
    (hoff : r ∉ M.attainedRadii) (hmass : M.cutMassAt r 0 ≠ ⊤) (y : M.V) :
    Summable fun e : Sym2 M.V => M.pairFlux r y e := by
  refine M.summable_pairFlux_of_cutMoment_ne_top hr hoff ?_ y
  rwa [M.cutMoment_one_eq_cutMassAt]

/-! ## 5. The hypothesis `hinner` of the landed `RussoExcluded/Main` theorems is redundant

`le_tsum_sMomentInfFlux_betaCrit_mul_exclMass` and `tsum_eq_iff_le_betaCrit_mul_exclMass` take
per-`y` edge summability as an explicit hypothesis `hinner`.  §3 supplies it, so the two theorems
hold with `hinner` replaced by finiteness of the mixed first moment.  The `y`-series summability
`hsumm` is *not* touched. -/

/-- **The one-sided excluded-mass bound, with per-`y` edge summability derived.** -/
theorem le_tsum_sMomentInfFlux_betaCrit_mul_exclMass_of_finite_mixed {r : ℝ} (hr : 0 < r)
    (hoff : r ∉ M.attainedRadii) (hE : E1Sign.exclMass M r ≠ ⊤)
    (hmix : ∀ y : M.V, ∫⁻ ω, clusterVol ω (0 : M.V)
      * (if y ∈ cluster ω (0 : M.V) then (1 : ℝ≥0∞) else 0) ∂(M.cutLaw r) ≠ ⊤)
    (hsumm : Summable fun y : M.V =>
      sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv r) :
    (M.betaCrit : ℝ) * (-(deriv M.K r)) * (E1Sign.exclMass M r).toReal
      ≤ ∑' y : M.V, sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
          M.cutProb M.cutEdgeDeriv r :=
  M.le_tsum_sMomentInfFlux_betaCrit_mul_exclMass hr hE
    (fun y => M.summable_pairFlux hr hoff y (hmix y)) hsumm

/-- **Equality is exactly the missing one-sided domination, with per-`y` edge summability
derived.** -/
theorem tsum_eq_iff_le_betaCrit_mul_exclMass_of_finite_mixed {r : ℝ} (hr : 0 < r)
    (hoff : r ∉ M.attainedRadii) (hE : E1Sign.exclMass M r ≠ ⊤)
    (hmix : ∀ y : M.V, ∫⁻ ω, clusterVol ω (0 : M.V)
      * (if y ∈ cluster ω (0 : M.V) then (1 : ℝ≥0∞) else 0) ∂(M.cutLaw r) ≠ ⊤)
    (hsumm : Summable fun y : M.V =>
      sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv r) :
    ((∑' y : M.V, sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv r)
        = (M.betaCrit : ℝ) * (-(deriv M.K r)) * (E1Sign.exclMass M r).toReal)
      ↔ ((∑' y : M.V, sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv r)
        ≤ (M.betaCrit : ℝ) * (-(deriv M.K r)) * (E1Sign.exclMass M r).toReal) :=
  M.tsum_eq_iff_le_betaCrit_mul_exclMass hr hE
    (fun y => M.summable_pairFlux hr hoff y (hmix y)) hsumm

/-- **The equality form with the mixed moment in place of joint absolute summability.**

`tsum_sMomentInfFlux_eq_betaCrit_mul_exclMass` assumes joint absolute summability
`Summable fun p : M.V × Sym2 M.V => |M.pairFlux r p.1 p.2|`.  By
`summable_abs_pairFlux_of_nonneg` that is per-`y` edge summability plus the vertex series
summability, and the first is §3.  So the joint hypothesis reduces to the same mixed moment plus
`hsumm`. -/
theorem tsum_sMomentInfFlux_eq_betaCrit_mul_exclMass_of_finite_mixed {r : ℝ} (hr : 0 < r)
    (hoff : r ∉ M.attainedRadii) (hE : E1Sign.exclMass M r ≠ ⊤)
    (hmix : ∀ y : M.V, ∫⁻ ω, clusterVol ω (0 : M.V)
      * (if y ∈ cluster ω (0 : M.V) then (1 : ℝ≥0∞) else 0) ∂(M.cutLaw r) ≠ ⊤)
    (hsumm : Summable fun y : M.V =>
      sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv r) :
    (∑' y : M.V, sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv r)
      = (M.betaCrit : ℝ) * (-(deriv M.K r)) * (E1Sign.exclMass M r).toReal :=
  M.tsum_sMomentInfFlux_eq_betaCrit_mul_exclMass hE
    (M.summable_abs_pairFlux_of_nonneg (fun y e => M.pairFlux_nonneg hr y e)
      (fun y => M.summable_pairFlux hr hoff y (hmix y)) hsumm)

/-! ## 6. The landed conditional off-corner derivative, with `hinner` deleted

`hasDerivAt_cutMassReal_eq_betaCrit_mul_exclMass_of_nonneg` needs `hinner` at `r0`.  Its other
hypotheses already contain `0 < r0`, `r0 ∈ Ioo α β`, the corner-free condition on `Ioo α β` and
finiteness of `M.cutMassAt r 0` there, so `hinner` follows from §4 and can be removed without
replacement: the statement below is that theorem with the hypothesis deleted. -/
theorem hasDerivAt_cutMassReal_eq_betaCrit_mul_exclMass_of_cutMass
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
    (hE : E1Sign.exclMass M r0 ≠ ⊤) :
    HasDerivAt M.cutMassReal
      ((M.betaCrit : ℝ) * (-(deriv M.K r0)) * (E1Sign.exclMass M r0).toReal) r0 := by
  have hmem : r0 ∈ Set.Ioo α β := ⟨hαr0, hr0β⟩
  have hoff' : r0 ∉ M.attainedRadii := by
    rw [SourceModelData.attainedRadii_eq_cornerRadii]
    exact hoff r0 hmem
  exact M.hasDerivAt_cutMassReal_eq_betaCrit_mul_exclMass_of_nonneg T hTmono hT S hSmono hS
    hα0 hαr0 hr0β hoff hKd hdom hboundint hmeasK hmeasinf hcontinf hfin hfluxnn hsummable
    hfluxintW hGcont hr0 hE
    (fun y => M.summable_pairFlux_of_cutMassAt_ne_top hr0 hoff' (hfin r0 hmem) y)

end SourceModelData

end PercLib.CriticalLRP.Orchestration

/-! ## Axiom audit -/

set_option linter.hashCommand false

namespace PercLib.CriticalLRP.Orchestration

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.abs_pairFlux_le_stdEdgeWeight_mul_evEdge
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.summable_stdEdgeWeight_mul_evEdge
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.summable_abs_pairFlux
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.summable_pairFlux
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tsum_abs_pairFlux_le_stdDegree_mixed
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.lintegral_mixed_le_cutMoment
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.summable_pairFlux_of_cutMoment_ne_top
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.summable_pairFlux_of_cutMassAt_ne_top
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.le_tsum_sMomentInfFlux_betaCrit_mul_exclMass_of_finite_mixed
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tsum_sMomentInfFlux_eq_betaCrit_mul_exclMass_of_finite_mixed
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.tsum_eq_iff_le_betaCrit_mul_exclMass_of_finite_mixed
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.hasDerivAt_cutMassReal_eq_betaCrit_mul_exclMass_of_cutMass

end PercLib.CriticalLRP.Orchestration
