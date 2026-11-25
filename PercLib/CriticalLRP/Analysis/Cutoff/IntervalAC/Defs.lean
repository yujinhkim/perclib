/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Real cutoff mass and its corner radii

Definitions at the actual normalized source norm. Generic finite-exception
absolute-continuity and monotone integral inequalities are in
`Analysis/Cutoff/IntervalAC.lean`.

Reviewed from the partial Ultramath `smwtqkdul` direction d4, member `m7`.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.RowSum
public import PercLib.CriticalLRP.Analysis.Cutoff.Monotone

/-! # Real cutoff mass and corner radii -/

@[expose] public section

namespace PercLib.CriticalLRP.Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-- The cut-off cluster mass of Definition I.1.5, `χ(r) = E_{β_c,r}|K|`, as a real number. -/
noncomputable def cutMassReal (r : ℝ) : ℝ := (M.cutMassAt r 0).toReal

/-- Radii at which the cut-off edge probability `1 − exp(−β_c J_r(x,y))` has a corner: the distances
`M.S.dist x y = M.S.ρ (x − y)` realised by the model's own norm, for distinct vertices.

Caution: the model's cut-off uses `M.S.ρ`, an arbitrary norm normalized by `unitBall_volume = 1`;
it is *not* the `ℓ^∞` length `FiniteVolume.edgeLen` used by the `RussoInf` machinery unless
`M.S.ρ = ‖·‖_∞`.  The finiteness of `cornerRadii ∩ [a,b]` is therefore a statement about `M.S.ρ`
(equivalence of norms on `ℝ^d`), not about `edgeLen`. -/
def cornerRadii : Set ℝ := {r : ℝ | ∃ x y : M.V, x ≠ y ∧ M.S.dist x y = r}


end SourceModelData

end PercLib.CriticalLRP.Orchestration
