/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# Weighted ghost moments as countable sums over finite cluster shapes

The `|K|` multiplicity and the ghost avoidance factor are both evaluated on each
finite cluster shape. An infinite cluster contributes zero at positive ghost
intensity. Tonelli's theorem then converts the integral into a countable sum.
-/
module

public import PercLib.CriticalLRP.CountableProduct.GhostCoupling
public import PercLib.CriticalLRP.CountableProduct.Compatibility

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open MeasureTheory Measure ProbabilityTheory unitInterval Filter
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP

variable {V : Type*} [Countable V]

noncomputable def ghostShapeWeight (h : ℝ≥0) (o : V) (K : Finset V) :
    Config V → ℝ≥0∞ :=
  {ω : Config V | cluster ω o = (K : Set V)}.indicator
    (fun _ => (K.card : ℝ≥0∞) * ghostW h ^ K.card)

theorem measurable_ghostShapeWeight (h : ℝ≥0) (o : V) (K : Finset V) :
    Measurable (ghostShapeWeight h o K) := by
  exact Measurable.indicator measurable_const (measurableSet_cluster_eq_finset o K)

/-- Pointwise finite-cluster decomposition of the weighted ghost integrand. -/
theorem tsum_ghostShapeWeight {h : ℝ≥0} (hh : 0 < h) (o : V) (ω : Config V) :
    ∑' K : Finset V, ghostShapeWeight h o K ω = clusterVol ω o * ghostMass h ω o := by
  classical
  by_cases hfin : (cluster ω o).Finite
  · let K : Finset V := hfin.toFinset
    have hK : cluster ω o = (K : Set V) := hfin.coe_toFinset.symm
    have hcard : (cluster ω o).ncard = K.card := Set.ncard_eq_toFinset_card _ hfin
    rw [tsum_eq_single K]
    · rw [show ghostShapeWeight h o K ω = (K.card : ℝ≥0∞) * ghostW h ^ K.card by
          simp [ghostShapeWeight, hK]]
      rw [ghostMass_of_finite h ω o hfin, clusterVol_eq_encard,
        encard_coe_eq_ncard_coe hfin, hcard]
    · intro K' hne
      by_cases heq : cluster ω o = (K' : Set V)
      · have hKK : K' = K := by
          apply Finset.ext
          intro v
          change v ∈ (K' : Set V) ↔ v ∈ (K : Set V)
          rw [← heq, hK]
        subst K'
        exact (hne rfl).elim
      · simp [ghostShapeWeight, heq]
  · have hterms : ∀ K : Finset V, ghostShapeWeight h o K ω = 0 := by
      intro K
      have hne : cluster ω o ≠ (K : Set V) := by
        intro heq
        rw [heq] at hfin
        exact hfin (Finset.finite_toSet K)
      simp [ghostShapeWeight, hne]
    rw [show (∑' K : Finset V, ghostShapeWeight h o K ω) = 0 from
      tsum_congr hterms |>.trans tsum_zero]
    rw [ghostMass_of_infinite hh ω o hfin, mul_zero]

/-- Integration of the shape weight gives its probability mass. -/
theorem lintegral_ghostShapeWeight (h : ℝ≥0) (ρ : Sym2 V → unitInterval)
    (o : V) (K : Finset V) :
    ∫⁻ ω, ghostShapeWeight h o K ω ∂edgeMeasure ρ =
      (K.card : ℝ≥0∞) * edgeMeasure ρ {ω : Config V | cluster ω o = (K : Set V)}
        * ghostW h ^ K.card := by
  unfold ghostShapeWeight
  rw [lintegral_indicator (measurableSet_cluster_eq_finset o K), setLIntegral_const]
  ac_rfl

/-- **Weighted ghost mass equals the countable sum of weighted finite cluster shapes.**
The factor `K.card` is explicit, and no contribution from an infinite cluster is lost. -/
theorem weightedGhostMass_eq_tsum_shapes (ρ : Sym2 V → unitInterval)
    {h : ℝ≥0} (hh : 0 < h) (o : V) :
    weightedGhostMass ρ h o =
      ∑' K : Finset V, (K.card : ℝ≥0∞)
        * edgeMeasure ρ {ω : Config V | cluster ω o = (K : Set V)}
        * ghostW h ^ K.card := by
  unfold weightedGhostMass
  have hpt : ∀ ω : Config V,
      clusterVol ω o * ghostMass h ω o = ∑' K : Finset V, ghostShapeWeight h o K ω := by
    intro ω
    rw [tsum_ghostShapeWeight hh o ω]
  simp_rw [hpt]
  rw [lintegral_tsum (fun K => (measurable_ghostShapeWeight h o K).aemeasurable)]
  exact tsum_congr (lintegral_ghostShapeWeight h ρ o)

/-- Concrete regression: on the empty edge law this is one cluster of cardinality one. -/
theorem weightedShapeSum_regression (h : ℝ≥0) (hh : 0 < h) (o : Fin 3) :
    weightedGhostMass (fun _ => (0 : unitInterval)) h o =
      ∑' K : Finset (Fin 3), (K.card : ℝ≥0∞)
        * edgeMeasure (fun _ => (0 : unitInterval))
          {ω : Config (Fin 3) | cluster ω o = (K : Set (Fin 3))}
        * ghostW h ^ K.card := by
  exact weightedGhostMass_eq_tsum_shapes (fun _ => (0 : unitInterval)) hh o

/-- The sum preserves the exact single-cluster value on `Fin 3`. -/
theorem weightedShapeSum_regression_value (h : ℝ≥0) (hh : 0 < h) (o : Fin 3) :
    (∑' K : Finset (Fin 3), (K.card : ℝ≥0∞)
        * edgeMeasure (fun _ => (0 : unitInterval))
          {ω : Config (Fin 3) | cluster ω o = (K : Set (Fin 3))}
        * ghostW h ^ K.card) = ghostW h :=
  (weightedShapeSum_regression h hh o).symm.trans (show
      weightedGhostMass (fun _ => (0 : unitInterval)) h o = ghostW h from by
    have hm : ghostMass h (∅ : Config (Fin 3)) o = ghostW h := by
      have hfin : (cluster (∅ : Config (Fin 3)) o).Finite := by
        rw [cluster_empty]
        exact Set.finite_singleton o
      rw [ghostMass_of_finite h ∅ o hfin, cluster_empty, Set.ncard_singleton, pow_one]
    unfold weightedGhostMass
    rw [edgeMeasure_zero, lintegral_dirac, clusterVol_eq_encard, cluster_empty,
      Set.encard_singleton, hm]
    simp)

#print axioms PercLib.CriticalLRP.tsum_ghostShapeWeight
#print axioms PercLib.CriticalLRP.weightedGhostMass_eq_tsum_shapes
#print axioms PercLib.CriticalLRP.weightedShapeSum_regression
#print axioms PercLib.CriticalLRP.weightedShapeSum_regression_value

end PercLib.CriticalLRP
