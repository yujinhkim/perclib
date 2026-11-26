/- Integrated from independently verified `.ultramath/smwxyesaw/m2/Defs.lean`
at production base `6eb8b0b660d7d9049a9fc25c7424bf10dbd723f6`. -/
module

/-
Local definitions for the Case-3 `hD` / first-moment scope audit (member `m2`, swarm
`smwxyesaw`).  Production files and the other members' files are not modified.
-/
public import PercLib.CriticalLRP.Analysis.Cutoff.FluxODE

/-! # Local defect used by the Case-3 scope wrappers -/

@[expose] public section

noncomputable section

open PercLib.CriticalLRP Orchestration

namespace PercLib.CriticalLRP

namespace I420Case3

/-- The multiplicative error of the first-moment ODE `(I.4.6)` at the model, built from
the standardized defect `PivotFlux.cutE0` and the truncated-law defect
`PivotFlux.cutE1`: this is the function `h` of
`VolumeMoments.FirstMoment.first_moment_asymptotic` for the cutoff mass. -/
def cutError (M : SourceModelData) (t : ℝ) : ℝ :=
  1 - (1 - PivotFlux.cutE0 M t) * (1 - PivotFlux.cutE1 M t)

end I420Case3

end PercLib.CriticalLRP
