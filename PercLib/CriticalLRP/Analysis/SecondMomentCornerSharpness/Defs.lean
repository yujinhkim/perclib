/-
Accepted and independently rebuilt from Ultramath `smwywszgo`, member `m4`.

Sharpness of the corner hypotheses in the two radius bridges of the `p = 2` cutoff moment.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Swarm `smwywszgo`, member `m4`, direction `d10`.

The original landed radius picture (`Analysis/SecondMomentTail.lean`, §9) named two bridges between
the corner-free (off-corner window) results and the consumer's `hac`/`hae`:

1. gluing `AbsolutelyContinuousOnInterval` across finitely many corner radii, using continuity of
   the moment at those radii (direction `d9` of this swarm);
2. transferring the integrated identity across a corner radius, using continuity of the moment
   and of the interval primitive (direction `d2` of this swarm).

Both bridges carry a *continuity* hypothesis, and both restrict differentiability statements to
radii that are not corner radii.  This file provides the machine-checked witnesses showing that
neither restriction can be dropped: a monotone right half-line indicator is absolutely continuous
on every closed subwindow avoiding the cut point and yet is not absolutely continuous across it,
and `x ↦ x + |x|` is monotone, continuous and globally absolutely continuous while having no
derivative at its corner.  These remain sharpness statements after the successor corner-transfer
proofs: they specify which hypotheses cannot be dropped.  No positive percolation theorem is
proved here.

No `sorry`, no `admit`, no `native_decide`, no custom axiom.
-/
module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# Definitions for the corner-hypothesis sharpness witnesses
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace PercLib.CriticalLRP.Orchestration.SmwywszgoM4

/-- The right half-line indicator with cut point `c`: `1` above `c`, `0` at and below `c`.

It is monotone, bounded, and constant on each side of `c`; in particular it is absolutely
continuous on every closed interval avoiding `c` but not across `c`. -/
def stepAt (c : ℝ) : ℝ → ℝ := fun x => if c < x then 1 else 0

/-- The corner profile `x ↦ x + |x|`: `0` on the negative half-line and `2 x` on the positive one.

It is monotone, continuous and `2`-Lipschitz (hence absolutely continuous on every interval), but
it has no derivative at `0`. -/
def cornerFun : ℝ → ℝ := fun x => x + |x|

/-- The off-corner derivative of `cornerFun`: `0` below the corner and `2` above it. -/
def cornerDeriv : ℝ → ℝ := fun x => if x ≤ 0 then 0 else 2

end PercLib.CriticalLRP.Orchestration.SmwywszgoM4
