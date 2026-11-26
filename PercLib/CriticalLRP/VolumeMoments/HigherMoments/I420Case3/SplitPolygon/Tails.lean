/- Integrated from `.scratch/case3-split-draft/Tails.lean` at production base
`637558828ebcb855d2104f1d334e9a69c2d1368f`. -/

module

public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.SplitPolygon.Model

/-! # Power-rescaled triangle-tail limits -/

@[expose] public section

noncomputable section

open Filter Topology
open scoped ENNReal

set_option linter.unusedSectionVars false

namespace PercLib.CriticalLRP

namespace I420Case3

open Orchestration

/-- Power-time rescaling preserves convergence to zero of the open-triangle tail.
Decay of the unrescaled tail is an explicit hypothesis; finiteness of the triangle
alone is not used to derive it. -/
theorem tendsto_nablaTail_rpow (M : SourceModelData) {c : ℝ} (hc : 0 < c)
    (hTail : Tendsto (fun r => (M.nablaTail r).toReal) atTop (𝓝 0)) :
    Tendsto (fun r : ℝ => (M.nablaTail (r ^ c)).toReal) atTop (𝓝 0) :=
  hTail.comp (tendsto_rpow_atTop hc)

/-- The power-rescaled tail hypotheses of the canonical near/far assembler,
packaged from the one unrescaled limit. -/
theorem power_nablaTail_limits (M : SourceModelData)
    (hTail : Tendsto (fun r => (M.nablaTail r).toReal) atTop (𝓝 0)) :
    ∀ c : ℝ, 0 < c → Tendsto (fun r : ℝ => (M.nablaTail (r ^ c)).toReal) atTop (𝓝 0) :=
  fun _ hc => tendsto_nablaTail_rpow M hc hTail

end I420Case3

end PercLib.CriticalLRP
