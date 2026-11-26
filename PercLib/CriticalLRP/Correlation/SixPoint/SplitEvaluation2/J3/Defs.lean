/-
Swarm `smwxk27m7`, member `m1`, direction `d2` (`J3-EVENT-BRIDGE`).

Definitions for the `p = 5`, `k = 2` event-level bridge at split position `j = 3`.

At `j = 3` the sixth arm lands on comb arm `3` (`b₃ — w`), so the split tree is the
mirror of `j = 0` across `u ↔ w`, and the production socket diagram
`slots.slotProd2 π 3 i₁ i₂ b0 b1 b2 b3 b4 t` reads

  `jointP π b0 b1 i₁ * (jointP π b4 i₂ i₁ * (tau π b2 i₁ * (tau π b3 i₂ * tau π t i₂)))`

(star set `{u, w}`: the star at `u` has leaves `b₀, b₁, v` and the star at `w` has leaves
`b₄, c, v`; the residual edges are `b₂ — v`, `b₃ — c`, `t — c`).  Everything below is stated
for that diagram, so `i₁` is the shared spine target `v` and `i₂` the landing point `c`.

The only definition here is the bookkeeping permutation used to move the five terminal sums
plus the two free-vertex sums into the peel order of the accepted socket evaluation
`SplitEval2.RootSocket.slotU2_three_tsum` / `slotV2_three_tsum`.  It carries no mathematical
content: seven nested extended sums are reordered with `ENNReal.tsum_comm`, i.e. by
`SixPoint.TwoJointEval.tsum_seven_perm`.
-/
module

public import PercLib.CriticalLRP.Correlation.SixPoint.SplitEvaluation2.RootSocket.Main
public import PercLib.CriticalLRP.Correlation.SixPoint.SplitPattern.Regroup
public import PercLib.CriticalLRP.Correlation.SixPoint.K2Mass.Defs

/-!
# `j = 3` event bridge: definitions

The single permutation used by the reordering step.
-/

open Set MeasureTheory
open scoped ENNReal BigOperators

@[expose] public section

namespace PercLib.CriticalLRP.SixPoint.SplitEval2.J3

variable {V : Type*}

/-- **The seven-index socket permutation for `j = 3`.**
Position `i` of the vertex tuple `X = ![y, z, w, q, r, c, v]` in the order in which
`shapeTotal` sums them (five terminals outer, then the two free vertices `c`, `v`) is
`X (permSocket3 i)`; the tuple `(X (permSocket3 i))ᵢ` is the peel order
`(i₁, b1, b2, b4, i₂, t, b3) = (v, y, z, q, c, r, w)` of the accepted socket evaluations
`slotU2_three_tsum` / `slotV2_three_tsum`. -/
def permSocket3 : Equiv.Perm (Fin 7) where
  toFun := ![6, 0, 1, 3, 5, 4, 2]
  invFun := ![1, 2, 6, 3, 5, 4, 0]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

end PercLib.CriticalLRP.SixPoint.SplitEval2.J3
