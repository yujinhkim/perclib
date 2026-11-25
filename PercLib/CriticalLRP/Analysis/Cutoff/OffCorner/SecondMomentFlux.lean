module

public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.PairFluxSummable
public import PercLib.CriticalLRP.Analysis.Cutoff.FluxODE

/-!
# Finite second cutoff moments supply summable off-corner vertex flux

Finite mixed mass, finite excluded mass, and absolute vertex-series summability follow at a fixed
off-corner radius from a finite second cutoff moment. No moment existence or uniform radius
bound is asserted.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

attribute [local instance] Classical.propDecidable

/-- The mixed first mass is dominated by the second cutoff moment. -/
theorem lintegral_mixed_le_cutMoment_two (r : ℝ) (y : M.V) :
    (∫⁻ ω, clusterVol ω (0 : M.V)
      * (if y ∈ cluster ω (0 : M.V) then (1 : ℝ≥0∞) else 0) ∂(M.cutLaw r))
      ≤ M.cutMoment 2 r := by
  rw [SourceModelData.cutMoment]
  refine lintegral_mono fun ω => ?_
  have hvol : (1 : ℝ≥0∞) ≤ clusterVol ω (0 : M.V) := by
    rw [clusterVol_eq_tsum]
    have h := ENNReal.le_tsum
      (f := fun w : M.V => (cluster ω (0 : M.V)).indicator (fun _ => (1 : ℝ≥0∞)) w) (0 : M.V)
    rwa [Set.indicator_of_mem (cluster_mem_self ω (0 : M.V))] at h
  by_cases hy : y ∈ cluster ω (0 : M.V)
  · simp only [hy, ite_true, pow_two]
    exact mul_le_mul_right hvol _
  · simp [hy]

/-- At an off-corner radius, a finite second cutoff moment makes every mixed first mass finite. -/
theorem mixed_ne_top_of_cutMoment_two {r : ℝ} (h2 : M.cutMoment 2 r ≠ ⊤) (y : M.V) :
    (∫⁻ ω, clusterVol ω (0 : M.V)
      * (if y ∈ cluster ω (0 : M.V) then (1 : ℝ≥0∞) else 0) ∂(M.cutLaw r)) ≠ ⊤ :=
  ne_top_of_le_ne_top h2 (M.lintegral_mixed_le_cutMoment_two r y)

/-- The vertex flux is absolutely summable from a finite second cutoff moment. -/
theorem summable_abs_sMomentInfFlux_of_cutMoment_two {r : ℝ} (hr : 0 < r)
    (hoff : r ∉ M.attainedRadii) (h2 : M.cutMoment 2 r ≠ ⊤) :
    Summable fun y : M.V => |sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv r| :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
    (fun y => M.abs_sMomentInfFlux_le_stdDegree_mixed hr hoff y (M.mixed_ne_top_of_cutMoment_two h2 y))
    ((M.summable_mixedFluxDensity h2).mul_left (M.stdDegree r))

/-- A finite second cutoff moment supplies the vertex-series summability needed by the
conditional derivative theorem. The first moment used for each edge series follows in turn. -/
theorem summable_sMomentInfFlux_of_cutMoment_two {r : ℝ} (hr : 0 < r)
    (hoff : r ∉ M.attainedRadii) (h2 : M.cutMoment 2 r ≠ ⊤) :
    Summable fun y : M.V => sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv r :=
  Summable.of_norm (by simpa only [Real.norm_eq_abs] using
    M.summable_abs_sMomentInfFlux_of_cutMoment_two hr hoff h2)

/-- The excluded mass is finite from the same second cutoff moment. -/
theorem exclMass_ne_top_of_cutMoment_two {r : ℝ} (h2 : M.cutMoment 2 r ≠ ⊤) :
    E1Sign.exclMass M r ≠ ⊤ := by
  have hp : E1Sign.pairMass M r ≠ ⊤ := E1Sign.pairMass_ne_top M r h2
  rw [E1Sign.pairMass_eq M r] at hp
  exact (ENNReal.add_ne_top.1 hp).2

/-- The per-vertex edge summability also follows from the second moment, through the first. -/
theorem summable_pairFlux_of_cutMoment_two {r : ℝ} (hr : 0 < r)
    (hoff : r ∉ M.attainedRadii) (h2 : M.cutMoment 2 r ≠ ⊤) (y : M.V) :
    Summable fun e : Sym2 M.V => M.pairFlux r y e :=
  M.summable_pairFlux_of_cutMoment_ne_top hr hoff (M.cutMoment_one_ne_top_of_two h2) y

/-- The summed vertex flux equals the standardized excluded mass using the second moment as a
shared source of all three summability/finiteness inputs. No uniform radius majorant is used. -/
theorem tsum_sMomentInfFlux_eq_betaCrit_mul_exclMass_of_cutMoment_two {r : ℝ} (hr : 0 < r)
    (hoff : r ∉ M.attainedRadii) (h2 : M.cutMoment 2 r ≠ ⊤) :
    (∑' y : M.V, sMomentInfFlux (0 : M.V) ({y} : Finset M.V) (fun _ => (1 : ℝ))
        M.cutProb M.cutEdgeDeriv r)
      = (M.betaCrit : ℝ) * (-(deriv M.K r)) * (E1Sign.exclMass M r).toReal :=
  M.tsum_sMomentInfFlux_eq_betaCrit_mul_exclMass_of_finite_mixed hr hoff
    (M.exclMass_ne_top_of_cutMoment_two h2) (M.mixed_ne_top_of_cutMoment_two h2)
    (M.summable_sMomentInfFlux_of_cutMoment_two hr hoff h2)

end SourceModelData
end PercLib.CriticalLRP.Orchestration

namespace PercLib.CriticalLRP.Orchestration.SourceModelData

#print axioms lintegral_mixed_le_cutMoment_two
#print axioms mixed_ne_top_of_cutMoment_two
#print axioms summable_abs_sMomentInfFlux_of_cutMoment_two
#print axioms summable_sMomentInfFlux_of_cutMoment_two
#print axioms exclMass_ne_top_of_cutMoment_two
#print axioms summable_pairFlux_of_cutMoment_two
#print axioms tsum_sMomentInfFlux_eq_betaCrit_mul_exclMass_of_cutMoment_two

end PercLib.CriticalLRP.Orchestration.SourceModelData
