/-
Ultramath swarm `smwzqts7r`, member `m7`, direction `d1` (G).
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwzqts7r`, member m7.
Production review base `e2b5cf635f5a2ffb1c7f203271de1c0a7ef3ad2b`;
reviewed scratch source `.scratch/review-smwzqts7r/m7/src/M7Defs.lean`.
-/
module

public import PercLib.CriticalLRP.MomentMonotonicity.SourceModelCutoffLimit

/-!
# New definitions for direction G: the cutoff mean at an arbitrary temperature

Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, Proposition I.4.2 and
the display on p. 35 ("Since `E_{β_c}|K| = ∞`"), plus the sharpness input on p. 6.

Production's `SourceModelData.cutMoment p r` is the cutoff moment **at `β_c` only**.  The
three-way residual studied in `InterfaceResidual.lean` compares the critical cutoff means
with the *subcritical* ones, so the temperature has to be an explicit parameter.  The
definition below is production's `cutMoment` with `M.betaCrit` replaced by an arbitrary
`β : ℝ≥0`; it agrees definitionally with `cutMoment` at `β = M.betaCrit`
(`cutMomentAt_betaCrit`), and it is *not* the uncut mean.

No theorem conclusion is asserted in this file.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- The `p`-th cutoff moment of the root cluster **at temperature `β`**:
`E_{β,r}|K_0|^p`, i.e. production's `cutMoment` with `M.betaCrit` replaced by `β`. -/
def cutMomentAt (β : ℝ≥0) (p : ℕ) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, clusterVol ω (0 : M.V) ^ p
    ∂(longRangeMeasure (M.cutKernel r) (M.cutKernel_nonneg r) β)

/-- At `β = M.betaCrit` the parametrised cutoff moment is production's `cutMoment`. -/
theorem cutMomentAt_betaCrit (p : ℕ) (r : ℝ) :
    M.cutMomentAt M.betaCrit p r = M.cutMoment p r := rfl

end SourceModelData

end PercLib.CriticalLRP.Orchestration
