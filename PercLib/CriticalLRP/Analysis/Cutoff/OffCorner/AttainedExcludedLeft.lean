/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.OffCorner.PairMassRegularity.Main

/-!
# The left limit of excluded mass at attained or off-corner radii

The closed excluded-window identity determines a strict-window left limit. Two existing
independent left limits give the pair mass in the strict ball and the connected mass in
that ball. The excluded mass has their difference as its left limit, at attained as well
as off-corner radii, from finite second and third cutoff moments at that radius.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.hashCommand false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- The strict-window pair mass is bounded by the closed-window pair mass at the same
radius. This only compares balls at fixed parameters, so no off-sphere condition is used. -/
theorem pairMassLt_le_pairMass {r : ℝ} :
    M.pairMassLt r ≤ E1Sign.pairMass M r := by
  rw [M.pairMass_eq_lintegral_pairMarkFun, SourceModelData.pairMassLt]
  refine lintegral_mono fun u => ?_
  simp only [SourceModelData.pairMarkFunLt, SourceModelData.pairMarkFun]
  refine mul_le_mul' le_rfl ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg (fun y hy => M.mem_ballF_rho.mpr
    (le_of_lt (M.mem_ballFLt.mp hy))) (fun _ _ _ => zero_le)

/-- The exact left limit of excluded mass at an arbitrary positive radius. The target uses
the strict-window pair and connected masses, rather than their closed counterparts at the
endpoint. No empty-sphere assumption is required. -/
theorem tendsto_exclScalar_nhdsLT_of_finite_moments {r0 : ℝ} (hr0 : 0 < r0)
    (h2 : M.cutMoment 2 r0 ≠ ⊤) (h3 : M.cutMoment 3 r0 ≠ ⊤) :
    Tendsto M.exclScalar (𝓝[<] r0)
      (𝓝 ((M.pairMassLt r0).toReal - (M.connMassLt r0).toReal)) := by
  have hpairFin : E1Sign.pairMass M r0 ≠ ⊤ := E1Sign.pairMass_ne_top M r0 h2
  have hpairLtFin : M.pairMassLt r0 ≠ ⊤ :=
    ne_top_of_le_ne_top hpairFin (M.pairMassLt_le_pairMass (r := r0))
  have hpair := M.tendsto_pairMassReal_nhdsLT r0 hr0 hpairLtFin
  have hconnFin : M.connMassLt r0 ≠ ⊤ :=
    ne_top_of_le_ne_top h3 (M.connMassLt_le_cutMoment_three r0)
  have hconn := M.tendsto_connMassReal_nhdsLT r0 hr0 hconnFin
  have hlim := hpair.sub hconn
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (M.exclScalar_eq_pairMassReal_sub_connMassReal_of_le (le_of_lt hr) h2).symm

end SourceModelData

end PercLib.CriticalLRP.Orchestration

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.pairMassLt_le_pairMass
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.tendsto_exclScalar_nhdsLT_of_finite_moments
