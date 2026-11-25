/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Finite pivotal flux for a cluster functional (main estimate)

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective
dimension*, arXiv:2508.18807v1, Lemma I.4.1 and the sharpness remark in its
proof.

`tsum_abs_pivotalFlux_le` is the quantitative statement that the pivotal (Russo)
sum of a bounded functional of the cluster of `o` is absolutely summable, with
total mass at most `2 sup|g| · D · E|K|`, where `D` bounds the total edge weight
at each vertex.  It is the "finite pivotal flux" consequence of a finite expected
cluster volume, i.e. of the sharpness input that the paper invokes when it
differentiates the cluster moments in infinite volume.
-/
module

public import PercLib.CriticalLRP.RussoInf.FluxBase

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

set_option linter.unusedSectionVars false

@[expose] public section

open MeasureTheory Measure Filter
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- **Finite pivotal flux.**  If the expected cluster volume is finite, then for any edge weight
`c` with per-vertex mass at most `D` the pivotal fluxes of a bounded measurable functional of the
cluster of `o` are absolutely summable, with total mass at most `2 sup |g| D E|K|`. -/
theorem tsum_abs_pivotalFlux_le {o : V} (μ : Measure (Config V)) [IsProbabilityMeasure μ]
    (c : Sym2 V → ℝ) {D m : ℝ} (hm : 0 ≤ m) (hD : 0 ≤ D)
    (hdeg : ∀ x : V, ∀ u : Finset (Sym2 V),
      ∑ e ∈ u, |c e| * (if x ∈ e then (1 : ℝ) else 0) ≤ D)
    {g : Config V → ℝ} (hbound : ∀ ω, |g ω| ≤ m) (hmeas : Measurable g)
    (hdep : ∀ ω η : Config V, cluster ω o = cluster η o → g ω = g η)
    (hvol : ∫⁻ ω, clusterVol ω o ∂μ ≠ ⊤) :
    ∑' e : Sym2 V, |c e * pivotalFlux μ g e|
      ≤ 2 * m * D * (∫⁻ ω, clusterVol ω o ∂μ).toReal := by
  classical
  -- the pivot of an edge is bounded by the probability that it touches the cluster
  have hflux : ∀ e : Sym2 V, |c e * pivotalFlux μ g e|
      ≤ |c e| * (2 * m * μ.real {ω : Config V | e ∈ touchSet ω o}) := by
    intro e
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_pivotalFlux_le μ hm hbound hmeas hdep e) (abs_nonneg _)
  -- integrability of the single-edge pivot weight
  have hind : ∀ e : Sym2 V, Integrable (fun ω : Config V =>
      |c e| * (if e ∈ touchSet ω o then (1 : ℝ) else 0)) μ := by
    intro e
    refine Integrable.const_mul (Integrable.of_bound (Measurable.aestronglyMeasurable ?_) 1 ?_) _
    · exact measurable_touchInd e
    · filter_upwards with ω
      rw [Real.norm_eq_abs]
      by_cases h : e ∈ touchSet ω o <;> simp [h]
  -- the cluster cardinality among the endpoints of `u`, as a finite sum of indicators
  have hcardFun : ∀ u : Finset (Sym2 V), (fun ω : Config V =>
      (((edgeVertices u).filter (fun x => x ∈ cluster ω o)).card : ℝ))
      = fun ω => ∑ x ∈ edgeVertices u, (if x ∈ cluster ω o then (1 : ℝ) else 0) := by
    intro u
    funext ω
    rw [Finset.card_filter]
    push_cast
    rfl
  have hcardInt : ∀ u : Finset (Sym2 V), Integrable (fun ω : Config V =>
      D * (((edgeVertices u).filter (fun x => x ∈ cluster ω o)).card : ℝ)) μ := by
    intro u
    have hmeas : Measurable fun ω : Config V =>
        (((edgeVertices u).filter (fun x => x ∈ cluster ω o)).card : ℝ) := by
      rw [hcardFun u]
      exact Finset.measurable_sum _ fun x _ => measurable_clusterInd x
    refine Integrable.const_mul (Integrable.of_bound hmeas.aestronglyMeasurable
      ((edgeVertices u).card : ℝ) ?_) _
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hle : ((edgeVertices u).filter (fun x => x ∈ cluster ω o)).card
        ≤ (edgeVertices u).card := Finset.card_filter_le _ _
    exact_mod_cast hle
  -- the finite-sum estimate
  have hstep : ∀ u : Finset (Sym2 V), ∑ e ∈ u, |c e * pivotalFlux μ g e|
      ≤ 2 * m * D * (∫⁻ ω, clusterVol ω o ∂μ).toReal := by
    intro u
    -- (1) bound each summand
    have h1 : ∑ e ∈ u, |c e * pivotalFlux μ g e|
        ≤ ∑ e ∈ u, |c e| * (2 * m * μ.real {ω : Config V | e ∈ touchSet ω o}) :=
      Finset.sum_le_sum fun e _ => hflux e
    -- (2) the sum of probabilities is the integral of the finite sum of indicators
    have h2 : ∑ e ∈ u, |c e| * (2 * m * μ.real {ω : Config V | e ∈ touchSet ω o})
        = 2 * m * ∫ ω, (∑ e ∈ u, |c e| *
            (if e ∈ touchSet ω o then (1 : ℝ) else 0)) ∂μ := by
      have hterm : ∀ e : Sym2 V, |c e| * (2 * m * μ.real {ω : Config V | e ∈ touchSet ω o})
          = 2 * m * ∫ ω, |c e| * (if e ∈ touchSet ω o then (1 : ℝ) else 0) ∂μ := by
        intro e
        rw [integral_const_mul, integral_touchInd μ e]
        ring
      rw [Finset.sum_congr rfl (fun e _ => hterm e), ← Finset.mul_sum]
      congr 1
      exact (integral_finsetSum _ (fun e _ => hind e)).symm
    -- (3) pointwise bound by the degree constant times the cluster cardinality
    have h3 : ∫ ω, (∑ e ∈ u, |c e| * (if e ∈ touchSet ω o then (1 : ℝ) else 0)) ∂μ
        ≤ ∫ ω, D * (((edgeVertices u).filter (fun x => x ∈ cluster ω o)).card : ℝ) ∂μ := by
      refine integral_mono_of_nonneg (Eventually.of_forall fun ω =>
        Finset.sum_nonneg fun e _ => by positivity) (hcardInt u)
        (Eventually.of_forall fun ω => ?_)
      exact sum_touchSet_weight_le (o := o) c hdeg u ω
    -- (4) evaluate the integral of the cluster cardinality
    have h4 : ∫ ω, D * (((edgeVertices u).filter (fun x => x ∈ cluster ω o)).card : ℝ) ∂μ
        = D * ∑ x ∈ edgeVertices u, μ.real {ω : Config V | x ∈ cluster ω o} := by
      have hfun : (fun ω : Config V =>
          D * (((edgeVertices u).filter (fun x => x ∈ cluster ω o)).card : ℝ))
          = fun ω => D * ∑ x ∈ edgeVertices u,
              (if x ∈ cluster ω o then (1 : ℝ) else 0) := by
        funext ω
        rw [show (((edgeVertices u).filter (fun x => x ∈ cluster ω o)).card : ℝ)
            = ∑ x ∈ edgeVertices u, (if x ∈ cluster ω o then (1 : ℝ) else 0) from by
          rw [Finset.card_filter]
          push_cast
          rfl]
      rw [hfun, integral_const_mul]
      congr 1
      rw [integral_finsetSum _ (fun x _ => integrable_clusterInd μ x)]
      exact Finset.sum_congr rfl fun x _ => integral_clusterInd μ x
    -- (5) bound the sum of probabilities by the expected cluster volume
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
    -- assemble
    have hmid1 : ∑ e ∈ u, |c e * pivotalFlux μ g e|
        ≤ 2 * m * (D * (∫⁻ ω, clusterVol ω o ∂μ).toReal) := by
      calc ∑ e ∈ u, |c e * pivotalFlux μ g e|
          ≤ ∑ e ∈ u, |c e| * (2 * m * μ.real {ω : Config V | e ∈ touchSet ω o}) := h1
        _ = 2 * m * ∫ ω, (∑ e ∈ u, |c e| *
              (if e ∈ touchSet ω o then (1 : ℝ) else 0)) ∂μ := h2
        _ ≤ 2 * m * ∫ ω, D *
              (((edgeVertices u).filter (fun x => x ∈ cluster ω o)).card : ℝ) ∂μ :=
            mul_le_mul_of_nonneg_left h3 (by positivity)
        _ = 2 * m * (D * ∑ x ∈ edgeVertices u, μ.real {ω : Config V | x ∈ cluster ω o}) := by
            rw [h4]
        _ ≤ 2 * m * (D * (∫⁻ ω, clusterVol ω o ∂μ).toReal) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h5 hD) (by positivity)
    calc ∑ e ∈ u, |c e * pivotalFlux μ g e|
        ≤ 2 * m * (D * (∫⁻ ω, clusterVol ω o ∂μ).toReal) := hmid1
      _ = 2 * m * D * (∫⁻ ω, clusterVol ω o ∂μ).toReal := by ring
  exact Real.tsum_le_of_sum_le (fun e => abs_nonneg _) hstep

end PercLib.CriticalLRP
