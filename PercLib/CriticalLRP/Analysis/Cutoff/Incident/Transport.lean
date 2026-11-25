module

public import PercLib.CriticalLRP.Analysis.Cutoff.Resampling
public import PercLib.CriticalLRP.RussoInf.SpatialDominated
public import PercLib.CriticalLRP.Analysis.Cutoff.Incident.Defs

/-!
# Mixed incident-edge transport at the cutoff law

Direction (activity 4) of swarm `smwtzmkep`, member `m5`.

The landed per-edge standardisation `cutEdgeDeriv_mul_pivotalFlux_le` bounds the `e`-th pivotal
term by `stdEdgeWeight r e` times the probability of the *coupled* event
`{y ∈ K_0} ∩ {e ∈ touchSet · 0}`.  This file transports that single-edge information to the
cluster-weighted total: for a nonnegative edge weight `w` whose total mass at each vertex is
bounded by `D`, the whole edge sum of `w e · P({y ∈ K_0} ∩ {e touches K_0})` is at most
`D · E[|K_0| 1{y ∈ K_0}]`, the mixed flux density at the *same* radius.

The only inputs are the degree bound `D` of the weight, nonnegativity of the weight, and
finiteness of the mixed first moment `E[|K_0| 1{y ∈ K_0}]` at that radius.  There is no derivative,
no radius monotonicity and no untruncated-model claim.
-/

set_option linter.style.longLine false
set_option linter.hashCommand false

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- **Pointwise mixed touching-set bound.**  For a nonnegative edge weight with per-vertex mass at
most `D`, the weight of the edges of a finite set `u` that touch the cluster of `o`, restricted to
configurations on which `y` lies in that cluster, is at most `D` times the number of cluster
vertices met by `u`. -/
theorem sum_weight_touchSet_mul_clusterInd_le {o y : V} (w : Sym2 V → ℝ) {D : ℝ}
    (hw : ∀ e, 0 ≤ w e)
    (hdeg : ∀ x : V, ∀ u : Finset (Sym2 V), vertexWeight w x u ≤ D)
    (u : Finset (Sym2 V)) (ω : Config V) :
    (∑ e ∈ u, w e * (if e ∈ touchSet ω o then (1 : ℝ) else 0))
        * (if y ∈ cluster ω o then (1 : ℝ) else 0)
      ≤ D * (((edgeVertices u).filter (fun x => x ∈ cluster ω o)).card : ℝ)
        * (if y ∈ cluster ω o then (1 : ℝ) else 0) := by
  have hdeg' : ∀ x : V, ∀ u' : Finset (Sym2 V),
      ∑ e ∈ u', |w e| * (if x ∈ e then (1 : ℝ) else 0) ≤ D := by
    intro x u'
    refine le_trans (le_of_eq ?_) (hdeg x u')
    exact Finset.sum_congr rfl fun e _ => by rw [abs_of_nonneg (hw e)]
  have h := sum_touchSet_weight_le (o := o) w hdeg' u ω
  have h' : ∑ e ∈ u, w e * (if e ∈ touchSet ω o then (1 : ℝ) else 0)
      ≤ D * (((edgeVertices u).filter (fun x => x ∈ cluster ω o)).card : ℝ) := by
    refine le_trans (le_of_eq ?_) h
    exact Finset.sum_congr rfl fun e _ => by rw [abs_of_nonneg (hw e)]
  have hc : (0 : ℝ) ≤ (if y ∈ cluster ω o then (1 : ℝ) else 0) := by split <;> norm_num
  exact mul_le_mul_of_nonneg_right h' hc

/-! ## 2. The coupled events and their integral representation -/

/-! ## 3. The mixed touching-set transport -/

/-- **Finite-set mixed incident transport.** -/
theorem sum_weight_mixed_le {o y : V} (μ : Measure (Config V)) [IsProbabilityMeasure μ]
    (w : Sym2 V → ℝ) {D : ℝ} (hD : 0 ≤ D) (hw : ∀ e, 0 ≤ w e)
    (hdeg : ∀ x : V, ∀ u : Finset (Sym2 V), vertexWeight w x u ≤ D)
    (hfin : ∫⁻ ω, clusterVol ω o * (if y ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ ≠ ⊤)
    (u : Finset (Sym2 V)) :
    ∑ e ∈ u, w e * μ.real (evEdge (o := o) (y := y) e)
      ≤ D * (∫⁻ ω, clusterVol ω o * (if y ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ).toReal := by
  classical
  have hstep1 : ∑ e ∈ u, w e * μ.real (evEdge (o := o) (y := y) e)
      = ∫ ω, ∑ e ∈ u, w e * ((if y ∈ cluster ω o then (1 : ℝ) else 0)
          * (if e ∈ touchSet ω o then (1 : ℝ) else 0)) ∂μ := by
    have hterm : ∀ e : Sym2 V, w e * μ.real (evEdge (o := o) (y := y) e)
        = ∫ ω, w e * ((if y ∈ cluster ω o then (1 : ℝ) else 0)
            * (if e ∈ touchSet ω o then (1 : ℝ) else 0)) ∂μ := by
      intro e
      rw [integral_const_mul, integral_evEdge]
    rw [Finset.sum_congr rfl (fun e _ => hterm e)]
    refine (integral_finsetSum u (f := fun e ω => w e * ((if y ∈ cluster ω o then (1 : ℝ) else 0)
      * (if e ∈ touchSet ω o then (1 : ℝ) else 0))) (fun e _ => ?_)).symm
    refine Integrable.const_mul (Integrable.of_bound (μ := μ) (f := fun ω => (if y ∈ cluster ω o then (1 : ℝ) else 0)
      * (if e ∈ touchSet ω o then (1 : ℝ) else 0)) ?_ 1 ?_) _
    · exact ((measurable_clusterInd (o := o) y).mul
        (measurable_touchInd (o := o) e)).aestronglyMeasurable
    · filter_upwards with ω
      rw [Real.norm_eq_abs]
      by_cases hy : y ∈ cluster ω o <;> by_cases ht : e ∈ touchSet ω o <;> simp [hy, ht]
  have hpt : ∀ ω : Config V,
      (∑ e ∈ u, w e * ((if y ∈ cluster ω o then (1 : ℝ) else 0)
          * (if e ∈ touchSet ω o then (1 : ℝ) else 0)))
        ≤ D * (((edgeVertices u).filter (fun x => x ∈ cluster ω o)).card : ℝ)
          * (if y ∈ cluster ω o then (1 : ℝ) else 0) := by
    intro ω
    have heq : ∑ e ∈ u, w e * ((if y ∈ cluster ω o then (1 : ℝ) else 0)
        * (if e ∈ touchSet ω o then (1 : ℝ) else 0))
        = (∑ e ∈ u, w e * (if e ∈ touchSet ω o then (1 : ℝ) else 0))
          * (if y ∈ cluster ω o then (1 : ℝ) else 0) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun e _ => by ring
    rw [heq]
    exact sum_weight_touchSet_mul_clusterInd_le (o := o) (y := y) w hw hdeg u ω
  have hcardmeas : Measurable fun ω : Config V =>
      (((edgeVertices u).filter (fun x => x ∈ cluster ω o)).card : ℝ) := by
    have hfun : (fun ω : Config V =>
        (((edgeVertices u).filter (fun x => x ∈ cluster ω o)).card : ℝ))
        = fun ω => ∑ x ∈ edgeVertices u, (if x ∈ cluster ω o then (1 : ℝ) else 0) := by
      funext ω
      rw [Finset.card_filter]
      push_cast
      rfl
    rw [hfun]
    exact Finset.measurable_sum _ fun x _ => measurable_clusterInd (o := o) x
  have hdomInt : Integrable (fun ω : Config V =>
      D * (((edgeVertices u).filter (fun x => x ∈ cluster ω o)).card : ℝ)
        * (if y ∈ cluster ω o then (1 : ℝ) else 0)) μ := by
    have hbase : Integrable (fun ω : Config V =>
        D * ((((edgeVertices u).filter (fun x => x ∈ cluster ω o)).card : ℝ)
          * (if y ∈ cluster ω o then (1 : ℝ) else 0))) μ := by
      refine Integrable.const_mul (Integrable.of_bound (μ := μ) (f := fun ω : Config V =>
        (((edgeVertices u).filter (fun x => x ∈ cluster ω o)).card : ℝ)
          * (if y ∈ cluster ω o then (1 : ℝ) else 0)) ?_ ((edgeVertices u).card : ℝ) ?_) D
      · exact (hcardmeas.mul (measurable_clusterInd (o := o) y)).aestronglyMeasurable
      · filter_upwards with ω
        have hle : ((edgeVertices u).filter (fun x => x ∈ cluster ω o)).card
            ≤ (edgeVertices u).card := Finset.card_filter_le _ _
        have hind : (if y ∈ cluster ω o then (1 : ℝ) else 0) ≤ 1 := by split <;> norm_num
        have hnn : (0 : ℝ) ≤ (if y ∈ cluster ω o then (1 : ℝ) else 0) := by split <;> norm_num
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hnn)]
        calc (((edgeVertices u).filter (fun x => x ∈ cluster ω o)).card : ℝ)
              * (if y ∈ cluster ω o then (1 : ℝ) else 0)
            ≤ (((edgeVertices u).filter (fun x => x ∈ cluster ω o)).card : ℝ) * 1 :=
              mul_le_mul_of_nonneg_left hind (Nat.cast_nonneg _)
          _ ≤ ((edgeVertices u).card : ℝ) := by
              rw [mul_one]
              exact_mod_cast hle
    simpa only [mul_assoc] using hbase
  have h3 : ∫ ω, ∑ e ∈ u, w e * ((if y ∈ cluster ω o then (1 : ℝ) else 0)
        * (if e ∈ touchSet ω o then (1 : ℝ) else 0)) ∂μ
      ≤ ∫ ω, D * (((edgeVertices u).filter (fun x => x ∈ cluster ω o)).card : ℝ)
          * (if y ∈ cluster ω o then (1 : ℝ) else 0) ∂μ :=
    integral_mono_of_nonneg
      (Eventually.of_forall fun ω => Finset.sum_nonneg fun e _ => by
        have h1 : (0 : ℝ) ≤ if y ∈ cluster ω o then (1 : ℝ) else 0 := by split <;> norm_num
        have h2 : (0 : ℝ) ≤ if e ∈ touchSet ω o then (1 : ℝ) else 0 := by split <;> norm_num
        exact mul_nonneg (hw e) (mul_nonneg h1 h2))
      hdomInt (Eventually.of_forall hpt)
  have hcardEq : ∀ ω : Config V,
      D * (((edgeVertices u).filter (fun x => x ∈ cluster ω o)).card : ℝ)
          * (if y ∈ cluster ω o then (1 : ℝ) else 0)
        = D * ∑ x ∈ edgeVertices u,
            ((if x ∈ cluster ω o then (1 : ℝ) else 0) * (if y ∈ cluster ω o then (1 : ℝ) else 0)) := by
    intro ω
    have hc : (((edgeVertices u).filter (fun x => x ∈ cluster ω o)).card : ℝ)
        = ∑ x ∈ edgeVertices u, (if x ∈ cluster ω o then (1 : ℝ) else 0) := by
      rw [Finset.card_filter]
      push_cast
      rfl
    calc D * (((edgeVertices u).filter (fun x => x ∈ cluster ω o)).card : ℝ)
          * (if y ∈ cluster ω o then (1 : ℝ) else 0)
        = D * ((∑ x ∈ edgeVertices u, (if x ∈ cluster ω o then (1 : ℝ) else 0))
            * (if y ∈ cluster ω o then (1 : ℝ) else 0)) := by rw [hc]; ring
      _ = D * ∑ x ∈ edgeVertices u,
            ((if x ∈ cluster ω o then (1 : ℝ) else 0) * (if y ∈ cluster ω o then (1 : ℝ) else 0)) := by
          rw [Finset.sum_mul]
  have hIntVert : ∀ x ∈ edgeVertices u, Integrable (fun ω => (if x ∈ cluster ω o then (1 : ℝ) else 0)
      * (if y ∈ cluster ω o then (1 : ℝ) else 0)) μ := by
    intro x _
    exact Integrable.of_bound (μ := μ) (f := fun ω => (if x ∈ cluster ω o then (1 : ℝ) else 0)
      * (if y ∈ cluster ω o then (1 : ℝ) else 0))
      ((measurable_clusterInd (o := o) x).mul (measurable_clusterInd (o := o) y)).aestronglyMeasurable 1
      (by
        filter_upwards with ω
        rw [Real.norm_eq_abs]
        by_cases hx : x ∈ cluster ω o <;> by_cases hy : y ∈ cluster ω o <;> simp [hx, hy])
  have h4 : ∫ ω, D * (((edgeVertices u).filter (fun x => x ∈ cluster ω o)).card : ℝ)
        * (if y ∈ cluster ω o then (1 : ℝ) else 0) ∂μ
      = D * ∑ x ∈ edgeVertices u, μ.real (evVert (o := o) (y := y) x) := by
    rw [show (fun ω : Config V => D * (((edgeVertices u).filter (fun x => x ∈ cluster ω o)).card : ℝ)
        * (if y ∈ cluster ω o then (1 : ℝ) else 0))
        = fun ω => D * ∑ x ∈ edgeVertices u,
            ((if x ∈ cluster ω o then (1 : ℝ) else 0) * (if y ∈ cluster ω o then (1 : ℝ) else 0)) from
      funext hcardEq]
    rw [integral_const_mul, integral_finsetSum (edgeVertices u) hIntVert]
    exact congrArg (D * ·) (Finset.sum_congr rfl fun x _ => integral_evVert μ x)
  have h5 : ∑ x ∈ edgeVertices u, μ.real (evVert (o := o) (y := y) x)
      ≤ (∫⁻ ω, clusterVol ω o * (if y ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ).toReal := by
    have hsplit : ∑ x ∈ edgeVertices u, μ (evVert (o := o) (y := y) x)
        ≤ ∫⁻ ω, clusterVol ω o * (if y ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ := by
      have hL : ∑ x ∈ edgeVertices u, μ (evVert (o := o) (y := y) x)
          = ∑ x ∈ edgeVertices u, ∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0)
              * (if y ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [← lintegral_indicator_one (measurableSet_evVert (o := o) (y := y) x)]
        refine lintegral_congr fun ω => ?_
        by_cases hx : x ∈ cluster ω o <;> by_cases hy : y ∈ cluster ω o <;>
          simp [evVert, hx, hy]
      rw [hL]
      calc ∑ x ∈ edgeVertices u, ∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0)
            * (if y ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ
          ≤ ∑' x : V, ∫⁻ ω, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0)
              * (if y ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ := ENNReal.sum_le_tsum _
        _ = ∫⁻ ω, ∑' x : V, (if x ∈ cluster ω o then (1 : ℝ≥0∞) else 0)
              * (if y ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ := by
            rw [lintegral_tsum]
            intro x
            exact ((measurable_clusterIndENN (o := o) x).mul
              (measurable_clusterIndENN (o := o) y)).aemeasurable
        _ = ∫⁻ ω, clusterVol ω o * (if y ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ := by
            refine lintegral_congr fun ω => ?_
            rw [ENNReal.tsum_mul_right]
            congr 1
            simpa only [Set.indicator_apply] using
              (clusterVol_eq_tsum (V := V) ω o).symm
    have htoReal : (∑ x ∈ edgeVertices u, μ (evVert (o := o) (y := y) x)).toReal
        = ∑ x ∈ edgeVertices u, μ.real (evVert (o := o) (y := y) x) := by
      rw [ENNReal.toReal_sum (fun x _ => measure_ne_top _ _)]
      rfl
    rw [← htoReal]
    exact ENNReal.toReal_mono hfin hsplit
  calc ∑ e ∈ u, w e * μ.real (evEdge (o := o) (y := y) e)
      = ∫ ω, ∑ e ∈ u, w e * ((if y ∈ cluster ω o then (1 : ℝ) else 0)
          * (if e ∈ touchSet ω o then (1 : ℝ) else 0)) ∂μ := hstep1
    _ ≤ ∫ ω, D * (((edgeVertices u).filter (fun x => x ∈ cluster ω o)).card : ℝ)
          * (if y ∈ cluster ω o then (1 : ℝ) else 0) ∂μ := h3
    _ = D * ∑ x ∈ edgeVertices u, μ.real (evVert (o := o) (y := y) x) := h4
    _ ≤ D * (∫⁻ ω, clusterVol ω o * (if y ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ).toReal :=
        mul_le_mul_of_nonneg_left h5 hD

/-- **Mixed incident transport (tsum form).** -/
theorem tsum_weight_mixed_touch_le {o y : V} (μ : Measure (Config V)) [IsProbabilityMeasure μ]
    (w : Sym2 V → ℝ) {D : ℝ} (hD : 0 ≤ D) (hw : ∀ e, 0 ≤ w e)
    (hdeg : ∀ x : V, ∀ u : Finset (Sym2 V), vertexWeight w x u ≤ D)
    (hfin : ∫⁻ ω, clusterVol ω o * (if y ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ ≠ ⊤) :
    ∑' e : Sym2 V, w e * μ.real (evEdge (o := o) (y := y) e)
      ≤ D * (∫⁻ ω, clusterVol ω o * (if y ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ).toReal := by
  classical
  refine Real.tsum_le_of_sum_le (fun e => mul_nonneg (hw e) measureReal_nonneg) fun u => ?_
  exact sum_weight_mixed_le (o := o) (y := y) μ w hD hw hdeg hfin u

/-! ## 4. The two-point flux bound at the actual cutoff law -/

namespace Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- **The mixed per-vertex flux bound.**  At a radius where the cut-off edge derivative is
nonnegative and every edge has positive cut-off probability, the flux of the singleton two-point
moment `1{y ∈ K_0}` is dominated by `D` times the mixed cluster density `E_r[|K_0| 1{y ∈ K_0}]`,
where `D` is any per-vertex bound for the standardised edge weight. -/
theorem abs_sMomentInfFlux_le_mixed {r : ℝ} (y : M.V) {D : ℝ} (hD : 0 ≤ D)
    (hpos : ∀ e : Sym2 M.V, 0 ≤ M.cutEdgeDeriv r e)
    (hq0 : ∀ e : Sym2 M.V, M.openProb r e = 0 → M.cutEdgeDeriv r e = 0)
    (hdeg : ∀ x : M.V, ∀ u : Finset (Sym2 M.V), vertexWeight (M.stdEdgeWeight r) x u ≤ D)
    (hfin : ∫⁻ ω, clusterVol ω (0 : M.V)
      * (if y ∈ cluster ω (0 : M.V) then (1 : ℝ≥0∞) else 0) ∂(M.cutLaw r) ≠ ⊤) :
    |sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ)) M.cutProb M.cutEdgeDeriv r|
      ≤ D * M.mixedFluxDensity r y := by
  classical
  have hmem : ∀ e : Sym2 M.V, evEdge (o := (0 : M.V)) (y := y) e
      = {ω : Config M.V | y ∈ cluster ω (0 : M.V)}
        ∩ {ω : Config M.V | e ∈ touchSet ω (0 : M.V)} := fun e => rfl
  have hflux : sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ)) M.cutProb
      M.cutEdgeDeriv r
      = ∑' e : Sym2 M.V, M.cutEdgeDeriv r e *
          pivotalFlux (M.cutLaw r)
            (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e := by
    simp only [sMomentInfFlux, infFluxOf]
    rw [M.cutLaw_eq_edgeMeasure r]
  have hpiv : ∀ e : Sym2 M.V, 0 ≤ pivotalFlux (M.cutLaw r)
      (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e := by
    intro e
    rw [pivotalFlux]
    exact integral_nonneg fun ω => flipDiff_sMomentTrunc_singleton_nonneg (M := M) y e ω
  have hw : ∀ e : Sym2 M.V, 0 ≤ M.stdEdgeWeight r e := by
    intro e
    by_cases hq : M.openProb r e = 0
    · rw [SourceModelData.stdEdgeWeight, hq, hq0 e hq, zero_div]
    · exact div_nonneg (hpos e) (le_of_lt (lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hq)))
  have hterm : ∀ e : Sym2 M.V,
      |M.cutEdgeDeriv r e * pivotalFlux (M.cutLaw r)
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e|
        ≤ M.stdEdgeWeight r e * (M.cutLaw r).real (evEdge (o := (0 : M.V)) (y := y) e) := by
    intro e
    rw [abs_mul, abs_of_nonneg (hpos e), abs_of_nonneg (hpiv e)]
    by_cases hq : M.openProb r e = 0
    · rw [SourceModelData.stdEdgeWeight, hq0 e hq, hq, zero_div, zero_mul, zero_mul]
    · exact M.cutEdgeDeriv_mul_pivotalFlux_le (r := r) (y := y) (e := e) (hpos e)
        (lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hq))
  have hsumR : Summable fun e : Sym2 M.V =>
      M.stdEdgeWeight r e * (M.cutLaw r).real (evEdge (o := (0 : M.V)) (y := y) e) := by
    refine summable_of_sum_le (c := D * (∫⁻ ω, clusterVol ω (0 : M.V)
      * (if y ∈ cluster ω (0 : M.V) then (1 : ℝ≥0∞) else 0) ∂(M.cutLaw r)).toReal)
      (fun e => mul_nonneg (hw e) measureReal_nonneg) fun u => ?_
    exact sum_weight_mixed_le (o := (0 : M.V)) (y := y) (M.cutLaw r) (M.stdEdgeWeight r)
      hD hw hdeg hfin u
  have hsumabs : Summable fun e : Sym2 M.V =>
      |M.cutEdgeDeriv r e * pivotalFlux (M.cutLaw r)
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e| :=
    Summable.of_nonneg_of_le (fun e => abs_nonneg _) hterm hsumR
  have hsumabs' : Summable fun e : Sym2 M.V =>
      ‖M.cutEdgeDeriv r e * pivotalFlux (M.cutLaw r)
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e‖ := by
    simpa only [Real.norm_eq_abs] using hsumabs
  rw [hflux]
  refine (norm_tsum_le_tsum_norm hsumabs').trans ?_
  have hcomp : ∑' e : Sym2 M.V,
      |M.cutEdgeDeriv r e * pivotalFlux (M.cutLaw r)
        (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e|
      ≤ ∑' e : Sym2 M.V,
        M.stdEdgeWeight r e * (M.cutLaw r).real (evEdge (o := (0 : M.V)) (y := y) e) :=
    hsumabs.tsum_le_tsum hterm hsumR
  have hmain := tsum_weight_mixed_touch_le (o := (0 : M.V)) (y := y) (M.cutLaw r)
    (M.stdEdgeWeight r) hD hw hdeg hfin
  calc ∑' e : Sym2 M.V,
        ‖M.cutEdgeDeriv r e * pivotalFlux (M.cutLaw r)
          (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e‖
      = ∑' e : Sym2 M.V,
          |M.cutEdgeDeriv r e * pivotalFlux (M.cutLaw r)
            (sMomentTrunc (fun _ => (1 : ℝ)) (0 : M.V) ({y} : Finset M.V)) e| := by
        exact tsum_congr fun e => Real.norm_eq_abs _
    _ ≤ ∑' e : Sym2 M.V,
        M.stdEdgeWeight r e * (M.cutLaw r).real (evEdge (o := (0 : M.V)) (y := y) e) := hcomp
    _ ≤ D * (∫⁻ ω, clusterVol ω (0 : M.V)
          * (if y ∈ cluster ω (0 : M.V) then (1 : ℝ≥0∞) else 0) ∂(M.cutLaw r)).toReal := hmain
    _ = D * M.mixedFluxDensity r y := rfl

end SourceModelData

end Orchestration

end PercLib.CriticalLRP

namespace PercLib.CriticalLRP

variable {V : Type*} [Countable V]

attribute [local instance] Classical.propDecidable

/-! ## 5. Incident-sum form of the transport -/

/-- **Mixed incident transport from bounded per-vertex incident sums.** -/
theorem tsum_weight_mixed_touch_le_of_incident {o y : V} (μ : Measure (Config V))
    [IsProbabilityMeasure μ] (w : Sym2 V → ℝ) {D : ℝ} (hD : 0 ≤ D) (hw : ∀ e, 0 ≤ w e)
    (hsum : ∀ x : V, Summable fun e : Sym2 V => w e * (if x ∈ e then (1 : ℝ) else 0))
    (hinc : ∀ x : V, incidentWeight w x ≤ D)
    (hfin : ∫⁻ ω, clusterVol ω o * (if y ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ ≠ ⊤) :
    ∑' e : Sym2 V, w e * μ.real (evEdge (o := o) (y := y) e)
      ≤ D * (∫⁻ ω, clusterVol ω o * (if y ∈ cluster ω o then (1 : ℝ≥0∞) else 0) ∂μ).toReal := by
  classical
  refine tsum_weight_mixed_touch_le (o := o) (y := y) μ w hD hw (fun x u => ?_) hfin
  exact le_trans (vertexWeight_le_incidentWeight hw (hsum x) u) (hinc x)

end PercLib.CriticalLRP

/-! ## 6. Axiom audit -/

#print axioms PercLib.CriticalLRP.sum_weight_touchSet_mul_clusterInd_le
#print axioms PercLib.CriticalLRP.integral_evEdge
#print axioms PercLib.CriticalLRP.integral_evVert
#print axioms PercLib.CriticalLRP.sum_weight_mixed_le
#print axioms PercLib.CriticalLRP.tsum_weight_mixed_touch_le
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.abs_sMomentInfFlux_le_mixed
#print axioms PercLib.CriticalLRP.vertexWeight_le_incidentWeight
#print axioms PercLib.CriticalLRP.tsum_weight_mixed_touch_le_of_incident
