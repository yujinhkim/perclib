/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Real cluster-volume laws and the ghost-field identities

This module transports the canonical ghost-field probabilities to ordinary real
Laplace and exponentially weighted integrals under the law of the cluster volume.
Finite clusters are required almost everywhere, exactly as in the project's
existing real avoidance-integral formula. In particular, the convention
`e^{-h ∞}=0` is not confused with the value zero of `\top.toReal`.
-/
module

public import PercLib.CriticalLRP.Analysis.MGFAssembly
public import PercLib.CriticalLRP.CountableProduct.GhostRestoration

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval Filter Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

open PercLib.CriticalLRP.Analysis.I32

variable {V : Type*} [Countable V]

/-- The law of the real cardinality projection of the cluster. This is a genuine
probability law even before moment finiteness is imposed. -/
noncomputable def volumeLaw (π : Sym2 V → unitInterval) (o : V) : Measure ℝ :=
  (edgeMeasure π).map (fun ω => (clusterVol ω o).toReal)

instance isProbabilityMeasure_volumeLaw (π : Sym2 V → unitInterval) (o : V) :
    IsProbabilityMeasure (volumeLaw π o) := by
  unfold volumeLaw
  have hm : Measurable (fun ω : Config V => (clusterVol ω o).toReal) :=
    ENNReal.measurable_toReal.comp (measurable_clusterVol o)
  exact (Measure.isProbabilityMeasure_map_iff hm.aemeasurable).2 inferInstance

/-- The cluster-volume law is carried by nonnegative real numbers. -/
theorem volumeLaw_Iio_zero (π : Sym2 V → unitInterval) (o : V) :
    volumeLaw π o (Iio 0) = 0 := by
  have hm : Measurable (fun ω : Config V => (clusterVol ω o).toReal) :=
    ENNReal.measurable_toReal.comp (measurable_clusterVol o)
  rw [volumeLaw, Measure.map_apply hm measurableSet_Iio]
  have he : (fun ω : Config V => (clusterVol ω o).toReal) ⁻¹' Iio 0 = ∅ := by
    ext ω
    simp [ENNReal.toReal_nonneg]
  rw [he, measure_empty]

/-- The real Laplace defect of `volumeLaw` is the ghost-hit probability. -/
theorem lapDefect_volumeLaw_eq_ghostHits (π : Sym2 V → unitInterval) (h : ℝ≥0)
    (hh : 0 < h) (o : V) (hfin : ∀ᵐ ω ∂(edgeMeasure π), clusterVol ω o ≠ ⊤) :
    lapDefect (volumeLaw π o) (h : ℝ) = (ghostHits π h o).toReal := by
  have hm : Measurable (fun ω : Config V => (clusterVol ω o).toReal) :=
    ENNReal.measurable_toReal.comp (measurable_clusterVol o)
  have he : Measurable (fun x : ℝ => 1 - Real.exp (-(h : ℝ) * x)) := by fun_prop
  have hmap : lapDefect (volumeLaw π o) (h : ℝ) =
      ∫ ω, (1 - Real.exp (-(h : ℝ) * (clusterVol ω o).toReal)) ∂edgeMeasure π := by
    rw [lapDefect, volumeLaw]
    simpa using (integral_map (μ := edgeMeasure π) hm.aemeasurable he.aestronglyMeasurable)
  have hexpm : Measurable (fun ω : Config V =>
      Real.exp (-(h : ℝ) * (clusterVol ω o).toReal)) := by fun_prop
  have hexp_le : ∀ ω : Config V, Real.exp (-(h : ℝ) * (clusterVol ω o).toReal) ≤ 1 := by
    intro ω
    rw [Real.exp_le_one_iff]
    have hnonneg : 0 ≤ (h : ℝ) * (clusterVol ω o).toReal :=
      mul_nonneg h.2 ENNReal.toReal_nonneg
    linarith
  have hint : Integrable (fun ω : Config V =>
      Real.exp (-(h : ℝ) * (clusterVol ω o).toReal)) (edgeMeasure π) := by
    refine Integrable.of_bound hexpm.aestronglyMeasurable 1 ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),]
    exact hexp_le ω
  have hsum : ghostHits π h o + ∫⁻ ω, ghostMass h ω o ∂edgeMeasure π = 1 :=
    edgeMeasure_prod_ghost_hits_add π h o
  have hhitne : ghostHits π h o ≠ ⊤ := by
    unfold ghostHits
    exact measure_ne_top _ _
  have havoidne : (∫⁻ ω, ghostMass h ω o ∂edgeMeasure π) ≠ ⊤ := by
    rw [← edgeMeasure_prod_ghost_absent]
    exact measure_ne_top _ _
  have hreal := congrArg ENNReal.toReal hsum
  rw [ENNReal.toReal_add hhitne havoidne, ENNReal.toReal_one] at hreal
  have havoid := edgeMeasure_prod_ghost_absent_real π h hh o hfin
  have hexp_real : (∫⁻ ω, ghostMass h ω o ∂edgeMeasure π).toReal =
      ∫ ω, Real.exp (-(h : ℝ) * (clusterVol ω o).toReal) ∂edgeMeasure π := by
    rw [← edgeMeasure_prod_ghost_absent, havoid]
    exact ENNReal.toReal_ofReal (integral_nonneg fun _ => (Real.exp_pos _).le)
  rw [hmap]
  have hsub : ∫ ω, (1 - Real.exp (-(h : ℝ) * (clusterVol ω o).toReal)) ∂edgeMeasure π =
      1 - ∫ ω, Real.exp (-(h : ℝ) * (clusterVol ω o).toReal) ∂edgeMeasure π := by
    rw [integral_sub (integrable_const 1) hint]
    simp only [integral_const, smul_eq_mul, Measure.real, measure_univ, ENNReal.toReal_one, one_mul]
  rw [hsub]
  linarith

/-- The exponentially weighted moment of `volumeLaw` is the real value of the ghost
weighted mass. Moment integrability and finite clusters make the real conversion valid. -/
theorem integral_weighted_volumeLaw_eq_weightedGhostMass (π : Sym2 V → unitInterval)
    (h : ℝ≥0) (hh : 0 < h) (o : V)
    (hfin : ∀ᵐ ω ∂(edgeMeasure π), clusterVol ω o ≠ ⊤)
    (hint : Integrable (fun ω : Config V =>
      (clusterVol ω o).toReal * Real.exp (-(h : ℝ) * (clusterVol ω o).toReal))
      (edgeMeasure π)) :
    (∫ x, x * Real.exp (-(h : ℝ) * x) ∂volumeLaw π o) =
      (weightedGhostMass π h o).toReal := by
  have hm : Measurable (fun ω : Config V => (clusterVol ω o).toReal) :=
    ENNReal.measurable_toReal.comp (measurable_clusterVol o)
  have hf : Measurable fun ω : Config V => (clusterVol ω o).toReal *
      Real.exp (-(h : ℝ) * (clusterVol ω o).toReal) := by fun_prop
  have hp : Measurable fun x : ℝ => x * Real.exp (-(h : ℝ) * x) := by fun_prop
  rw [volumeLaw]
  have hmapped := integral_map (μ := edgeMeasure π) hm.aemeasurable hp.aestronglyMeasurable
  rw [hmapped]
  have hof := ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun ω =>
      mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le)
  have hform : ENNReal.ofReal (∫ ω, (clusterVol ω o).toReal *
      Real.exp (-(h : ℝ) * (clusterVol ω o).toReal) ∂edgeMeasure π)
      = weightedGhostMass π h o := by
    rw [hof, weightedGhostMass]
    refine lintegral_congr_ae ?_
    filter_upwards [hfin] with ω hω
    rw [ghostMass_eq_exp h hh, ite_eq_right hω]
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg]
    congr 1
    exact ENNReal.ofReal_toReal hω
  have hret := congrArg ENNReal.toReal hform
  simpa only [ENNReal.toReal_ofReal (integral_nonneg_of_ae
    (Filter.Eventually.of_forall fun _ =>
      mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le))] using hret

/-- Finite-valued form of the weighted volume/ghost identity. This is often more useful
than taking `toReal`, because it also verifies finiteness of the ghost correction. -/
theorem weightedGhostMass_eq_ofReal (π : Sym2 V → unitInterval)
    (h : ℝ≥0) (hh : 0 < h) (o : V)
    (hfin : ∀ᵐ ω ∂(edgeMeasure π), clusterVol ω o ≠ ⊤)
    (hint : Integrable (fun ω : Config V =>
      (clusterVol ω o).toReal * Real.exp (-(h : ℝ) * (clusterVol ω o).toReal))
      (edgeMeasure π)) :
    weightedGhostMass π h o = ENNReal.ofReal (∫ ω, (clusterVol ω o).toReal *
      Real.exp (-(h : ℝ) * (clusterVol ω o).toReal) ∂edgeMeasure π) := by
  have hm : Measurable (fun ω : Config V => (clusterVol ω o).toReal) :=
    ENNReal.measurable_toReal.comp (measurable_clusterVol o)
  have hp : Measurable fun x : ℝ => x * Real.exp (-(h : ℝ) * x) := by fun_prop
  rw [weightedGhostMass]
  have hof := ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun ω =>
      mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le)
  rw [hof]
  refine lintegral_congr_ae ?_
  filter_upwards [hfin] with ω hω
  rw [ghostMass_eq_exp h hh, ite_eq_right hω]
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  congr 1
  exact (ENNReal.ofReal_toReal hω).symm

#print axioms PercLib.CriticalLRP.weightedGhostMass_eq_ofReal
#print axioms PercLib.CriticalLRP.lapDefect_volumeLaw_eq_ghostHits
#print axioms PercLib.CriticalLRP.integral_weighted_volumeLaw_eq_weightedGhostMass

end PercLib.CriticalLRP
