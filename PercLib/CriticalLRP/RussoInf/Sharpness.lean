/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Finite-window sharpness bounds for capped cluster functionals

The per-vertex derivative-weight bound and finite expected cluster volume bound
the mass of each capped cluster pivotal flux, independently of the finite window.
This isolates the sharpness input for dominated passage to infinite-volume Russo
formulas; it neither asserts sharpness for a concrete model nor supplies model
regularity or a locally uniform limit.
-/
module

public import PercLib.CriticalLRP.RussoInf.Exchange
public import PercLib.CriticalLRP.RussoInf.FluxMain

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

/-- **Finite form of the pivotal weight estimate.**  For any finite edge set `u`, the total weight
`∑_{e ∈ u} |c e| P(e touches K_o)` is at most `D · E|K_o|`, independently of `u`.
This is the finite-partial-sum statement proved inside `summable_abs_weight_touch`. -/
theorem sum_abs_weight_touch_le {o : V} (μ : Measure (Config V)) [IsProbabilityMeasure μ]
    (c : Sym2 V → ℝ) {D : ℝ} (hD : 0 ≤ D)
    (hdeg : ∀ x : V, ∀ u : Finset (Sym2 V),
      ∑ e ∈ u, |c e| * (if x ∈ e then (1 : ℝ) else 0) ≤ D)
    (hvol : ∫⁻ ω, clusterVol ω o ∂μ ≠ ⊤) (u : Finset (Sym2 V)) :
    ∑ e ∈ u, |c e| * μ.real {ω : Config V | e ∈ touchSet ω o}
      ≤ D * (∫⁻ ω, clusterVol ω o ∂μ).toReal := by
  classical
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
      Finset.sum_nonneg fun e _ => by positivity) hcardInt (Eventually.of_forall fun ω => ?_)
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

/-- **The uniform-in-window pivotal flux bound.**  For every finite edge set `S`, the pivotal flux
of the window functional `cutFun S g` for a bounded measurable functional `g` of the cluster of `o`
is bounded by `2 m D E|K_o|`, with a right-hand side that does not depend on `S`.

This is the finite-window form of the "finite pivotal flux" input of the proof of Lemma I.4.1: the
sharpness of the phase transition enters only through `hvol`, the finiteness of the expected cluster
volume, and the graph only through the per-vertex degree bound `D` on the derivative weights. -/
theorem abs_sum_pivotalFlux_cutFun_le {o : V} (μ : Measure (Config V)) [IsProbabilityMeasure μ]
    (S : Finset (Sym2 V)) (c : Sym2 V → ℝ) {D m : ℝ} (hm : 0 ≤ m) (hD : 0 ≤ D)
    (hdeg : ∀ x : V, ∀ u : Finset (Sym2 V),
      ∑ e ∈ u, |c e| * (if x ∈ e then (1 : ℝ) else 0) ≤ D)
    {g : Config V → ℝ} (hbound : ∀ ω, |g ω| ≤ m) (hmeas : Measurable g)
    (hdep : ∀ ω η : Config V, cluster ω o = cluster η o → g ω = g η)
    (hvol : ∫⁻ ω, clusterVol ω o ∂μ ≠ ⊤) :
    |∑ e ∈ S, c e * pivotalFlux μ (cutFun S g) e|
      ≤ 2 * m * D * (∫⁻ ω, clusterVol ω o ∂μ).toReal := by
  classical
  have hterm : ∀ e ∈ S, |c e * pivotalFlux μ (cutFun S g) e|
      ≤ |c e| * (2 * m * μ.real {ω : Config V | e ∈ touchSet ω o}) := by
    intro e _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_pivotalFlux_cutFun_le μ hm hbound hmeas hdep e)
      (abs_nonneg _)
  have hsplit : ∑ e ∈ S, |c e| * (2 * m * μ.real {ω : Config V | e ∈ touchSet ω o})
      = 2 * m * ∑ e ∈ S, |c e| * μ.real {ω : Config V | e ∈ touchSet ω o} := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by ring
  calc |∑ e ∈ S, c e * pivotalFlux μ (cutFun S g) e|
      ≤ ∑ e ∈ S, |c e * pivotalFlux μ (cutFun S g) e| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e ∈ S, |c e| * (2 * m * μ.real {ω : Config V | e ∈ touchSet ω o}) :=
        Finset.sum_le_sum hterm
    _ = 2 * m * ∑ e ∈ S, |c e| * μ.real {ω : Config V | e ∈ touchSet ω o} := hsplit
    _ ≤ 2 * m * (D * (∫⁻ ω, clusterVol ω o ∂μ).toReal) :=
        mul_le_mul_of_nonneg_left (sum_abs_weight_touch_le μ c hD hdeg hvol S)
          (by positivity)
    _ = 2 * m * D * (∫⁻ ω, clusterVol ω o ∂μ).toReal := by ring

end PercLib.CriticalLRP
