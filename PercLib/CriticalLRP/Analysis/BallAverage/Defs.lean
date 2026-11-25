/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Open-triangle tail and normalized lattice-ball sums

Accepted from independent submission `smwp648b3` direction D3.  These are the
configured source-model definitions: the open-triangle convolution at
`M.betaCrit`, its far-distance supremum, and its sum over a source-normalized
ball.  No alternative norm or finite-box probability law is introduced.
-/
module

public import PercLib.CriticalLRP.Orchestration.Defs

set_option autoImplicit true

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PercLib.CriticalLRP.BallAverage

open PercLib.CriticalLRP.Orchestration

/-- **`∇_{β_c}(0,x)`**: the open triangle diagram at the origin, as the three-fold
convolution of the two-point function,
`Σ_y Σ_z P(0↔y) P(y↔z) P(z↔x)` (paper, section I.4).  It is `ℝ≥0∞`-valued;
under the triangle condition it is finite for every `x`
(`all_le_nablaSup_ne_top`). -/
noncomputable def openTriangleNabla (M : SourceModelData) (x : M.V) : ℝ≥0∞ :=
  ∑' y : M.V, ∑' z : M.V,
    ENNReal.ofReal (M.twoPoint M.betaCrit 0 y) * ENNReal.ofReal (M.twoPoint M.betaCrit y z) *
      ENNReal.ofReal (M.twoPoint M.betaCrit z x)

/-- **`∇_r = sup_{‖x‖ ≥ r} f x`** (paper, section I.4), for an arbitrary weight `f`
on the lattice; the configured case is `f = openTriangleNabla M`. -/
noncomputable def nablaSup (M : SourceModelData) (f : M.V → ℝ≥0∞) (r : ℝ) : ℝ≥0∞ :=
  ⨆ (x : M.V) (_ : r ≤ M.S.ρ (toVec x)), f x

/-- **`Σ_{x ∈ B_r} f x`**, the unnormalized lattice-ball sum of the weight `f`. -/
noncomputable def ballSum (M : SourceModelData) (f : M.V → ℝ≥0∞) (r : ℝ) : ℝ≥0∞ :=
  ∑' x : M.V, (M.ball r).indicator f x

end PercLib.CriticalLRP.BallAverage
