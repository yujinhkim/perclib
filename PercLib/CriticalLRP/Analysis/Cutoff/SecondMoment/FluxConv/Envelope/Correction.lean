/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Swarm `smwvhhc1v`, member `m2`, direction (B).

# The cubic connection correction of the unexcluded `p = 2` ghost sum

The unexcluded pair weight of the verified base overcounts the paper's `p = 2` weight exactly on
the configurations where the *second* connection holds.  Concretely, at the origin,

`unexclPairWeight o b c = 1(b≠c) 1(0↔b) 1(|c-b| ≤ r) (2|K_b||K_c| + |K_c|²)`

whereas the paper weight carries the exclusion `1(b↮c)`, and on `0↔b`, `b↔c` one has
`|K_b| = |K_c| = |K_0|`, so the unexcluded weight takes the constant value `3|K_0|²` while the
paper weight vanishes.  The comparison itself (`unexclPairWeight ≤ p2Weight + correction`) is the
content of direction (A); this file proves the *summation* of the correction, which is independent
of that comparison:

`∑_b ∑_c 3|K_0|² 1(0↔b) 1(b↔c) = 3|K_0|² ∑_b 1(0↔b) |K_b| = 3|K_0|² |K_0|² = 3|K_0|⁴`,

using the two landed connection identities `tsum_connects_indicator` (with the orientation of `b`
and `c` interchanged by symmetry of `Connects`) and `tsum_clusterVol_mul_connects`.  Nothing here
is a moment hypothesis: the identity is `ℝ≥0∞`-valued and unconditional.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.SecondMoment.FluxConv.Envelope.Reindex

/-!
# Summation of the cubic connection correction
-/

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unreachableTactic false

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal Topology BigOperators

namespace PercLib.CriticalLRP

namespace Orchestration

namespace SourceModelData

variable (M : SourceModelData)

attribute [local instance] Classical.propDecidable

/-! ## 1. The connection indicator is symmetric in its two vertices -/

/-- The connection indicator at a vertex, with the vertex written *second*, is the one of
`tsum_connects_indicator` (which fixes the vertex in the second slot). -/
theorem connects_indicator_swap_set (a b : M.V) :
    {ω' : Config M.V | Connects ω' a b} = {ω' : Config M.V | Connects ω' b a} := by
  ext ω'
  exact ⟨fun h => connects_symm h, fun h => connects_symm h⟩

/-- **`∑_c 1(b ↔ c) = |K_b|`**: the cluster volume as the sum of the connection indicators of
the vertex `b`, in the orientation needed below. -/
theorem tsum_connects_indicator_of (ω : Config M.V) (b : M.V) :
    (∑' c : M.V, configIndicator {ω' : Config M.V | Connects ω' b c} ω) = clusterVol ω b := by
  rw [← tsum_connects_indicator ω b]
  exact tsum_congr fun c => by rw [connects_indicator_swap_set M b c]

/-! ## 2. The inner sum of the correction -/

/-- The inner `c`-sum of the cubic correction at a fixed `b`: the second connection indicator
contributes the cluster volume `|K_b|`. -/
theorem tsum_connCorr_inner (ω : Config M.V) (b : M.V) :
    (∑' c : M.V, 3 * clusterVol ω (0 : M.V) ^ 2 *
        configIndicator {ω' : Config M.V | Connects ω' (0 : M.V) b} ω *
          configIndicator {ω' : Config M.V | Connects ω' b c} ω)
      = 3 * clusterVol ω (0 : M.V) ^ 2 *
          configIndicator {ω' : Config M.V | Connects ω' (0 : M.V) b} ω * clusterVol ω b := by
  rw [ENNReal.tsum_mul_left]
  exact congrArg _ (tsum_connects_indicator_of M ω b)

/-! ## 3. The cubic connection correction is at most `3 |K_0|⁴` -/

/-- **The summed cubic connection correction.**  The total deficit of the unexcluded weight over
the paper weight is at most `3 |K_0|⁴`, uniformly in the configuration. -/
theorem tsum_tsum_connCorr_le (ω : Config M.V) :
    (∑' b : M.V, ∑' c : M.V, 3 * clusterVol ω (0 : M.V) ^ 2 *
        configIndicator {ω' : Config M.V | Connects ω' (0 : M.V) b} ω *
          configIndicator {ω' : Config M.V | Connects ω' b c} ω)
      ≤ 3 * clusterVol ω (0 : M.V) ^ 4 := by
  have hstep : ∀ b : M.V,
      (∑' c : M.V, 3 * clusterVol ω (0 : M.V) ^ 2 *
          configIndicator {ω' : Config M.V | Connects ω' (0 : M.V) b} ω *
            configIndicator {ω' : Config M.V | Connects ω' b c} ω)
        = 3 * clusterVol ω (0 : M.V) ^ 2 *
            (clusterVol ω b *
              configIndicator {ω' : Config M.V | Connects ω' b (0 : M.V)} ω) := by
    intro b
    rw [tsum_connCorr_inner M ω b]
    rw [connects_indicator_swap_set M (0 : M.V) b]
    ring
  have hmain : (∑' b : M.V, ∑' c : M.V, 3 * clusterVol ω (0 : M.V) ^ 2 *
        configIndicator {ω' : Config M.V | Connects ω' (0 : M.V) b} ω *
          configIndicator {ω' : Config M.V | Connects ω' b c} ω)
      = 3 * clusterVol ω (0 : M.V) ^ 4 := by
    calc (∑' b : M.V, ∑' c : M.V, 3 * clusterVol ω (0 : M.V) ^ 2 *
          configIndicator {ω' : Config M.V | Connects ω' (0 : M.V) b} ω *
            configIndicator {ω' : Config M.V | Connects ω' b c} ω)
        = ∑' b : M.V, 3 * clusterVol ω (0 : M.V) ^ 2 *
            (clusterVol ω b *
              configIndicator {ω' : Config M.V | Connects ω' b (0 : M.V)} ω) :=
          tsum_congr hstep
      _ = 3 * clusterVol ω (0 : M.V) ^ 2 *
            (∑' b : M.V, clusterVol ω b *
              configIndicator {ω' : Config M.V | Connects ω' b (0 : M.V)} ω) :=
          ENNReal.tsum_mul_left
      _ = 3 * clusterVol ω (0 : M.V) ^ 2 * clusterVol ω (0 : M.V) ^ 2 := by
          rw [PivotFlux.tsum_clusterVol_mul_connects M ω]
      _ = 3 * clusterVol ω (0 : M.V) ^ 4 := by
          ring
  exact le_of_eq hmain

end SourceModelData

end Orchestration

end PercLib.CriticalLRP

end

/-! ## Axiom audit -/

namespace PercLib.CriticalLRP.Orchestration.SourceModelData

#print axioms connects_indicator_swap_set
#print axioms tsum_connects_indicator_of
#print axioms tsum_connCorr_inner
#print axioms tsum_tsum_connCorr_le

end PercLib.CriticalLRP.Orchestration.SourceModelData
