/- Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Swarm `smwu4e7s3`, member `m1`, direction `d1`: definitions of the repaired (shifted-log) Case 3
source-norm input and its explicit conversion constants.
-/
module

public import PercLib.CriticalLRP.Orchestration.Defs
public import PercLib.CriticalLRP.Analysis.LatticeConvolution.NormShell.Defs
public import PercLib.CriticalLRP.Analysis.OpenTriangle.Case3Profile.Defs

/-!
# Constants of the repaired (shifted-log) Case 3 source-norm transport

Definitions only: the repaired source hypothesis `Case3ShiftedBound`/`HDCase3Shifted` and the
explicit conversion constants `logShiftAux`, `logShiftConst`, `logUpperConst`, `case3SupConst`,
`case3SrcConst`.  The proofs are in `Case3SourceNorm.Main`, which imports this module.

The hypothesis modelled here is the *repaired* shape `(log (1 + ρ))⁻¹`, not the printed v1
`(log ρ)⁻¹` of `Orchestration.HD`; the printed predicate is untouched by this module.
-/

set_option autoImplicit false

@[expose] public section

open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP.Orchestration.HD.Case3

open CriticalLRPConv

/-- **The shifted-log (repaired) Case 3 source hypothesis, radius form.**

`Case3ShiftedBound M C` is `∀ x ≠ y, τ_{β_c}(x,y) ≤ C (log (1 + ρ))⁻¹ ρ ^ (-6 + 2)` at the model's
normalized norm `ρ = M.S.ρ (toVec (x - y))`.  This is `log (1 + ρ)` where the printed source has
`log ρ`; it is the repair document in `docs/CRITICAL_LRP_CASE3_PROFILE.md`, *not* the printed
hypothesis, and it is not claimed to be equivalent to it. -/
def Case3ShiftedBound (M : SourceModelData) (C : ℝ) : Prop :=
  ∀ x y : M.V, x ≠ y →
    M.twoPoint M.betaCrit x y
      ≤ C * (Real.log (1 + M.S.ρ (toVec (x - y))))⁻¹
          * (M.S.ρ (toVec (x - y))) ^ (-(6 : ℝ) + 2)

/-- The repaired third disjunct of `Orchestration.HD`: `d = 6`, `α = 2`, and the shifted-log
domination at the normalized source norm.  This is deliberately a *new named predicate*; the
printed `HD M` is untouched. -/
def HDCase3Shifted (M : SourceModelData) : Prop :=
  M.d = 6 ∧ M.α = 2 ∧ ∃ C : ℝ, 0 < C ∧ Case3ShiftedBound M C

/-- Cost of the logarithmic comparison in the second regime (`s ≥ 2/c`), `log (1/s) / log 2 + 3`
written with a common denominator. -/
noncomputable def logShiftAux (c : ℝ) : ℝ :=
  (Real.log (1 / c) + 3 * Real.log 2) / Real.log 2

/-- **The explicit logarithmic comparison constant**: for `0 < c ≤ 1` and `s ≥ 1`,
`log (1 + s) ≤ logShiftConst c * log (1 + c * s)`. -/
noncomputable def logShiftConst (c : ℝ) : ℝ :=
  Real.log (1 + 2 / c) / Real.log (1 + c) + logShiftAux c

/-- The **output-side** logarithmic comparison constant, at the upper norm comparison
`S.ρ ≤ srcUpperConst S ‖·‖`: for `‖y‖ ≥ 1`,
`log (1 + S.dist 0 y) ≤ logUpperConst S * log (1 + ‖y‖)`. -/
noncomputable def logUpperConst {d : ℕ} (S : SourceNormData d) : ℝ :=
  1 + Real.log (srcUpperConst S) / Real.log 2

/-- The sup-norm conversion constant of the repaired Case 3 input:
`C * logShiftConst c * c ^ (-4)` with `c = srcLowerUnit S`. -/
noncomputable def case3SupConst (c C : ℝ) : ℝ := C * logShiftConst c * c ^ (-(4 : ℝ))

/-- The Case 3 constant carried by the *source-model* statement, at the model's normalized norm.
Both factors are conversion costs that are actually spent:
the input logarithm/norm conversion `case3SupConst` (lower comparison `srcLowerUnit S`) and the
output logarithm comparison `logUpperConst S ^ 2` (upper comparison `srcUpperConst S`; the square
because the tail profile is `(log (1 + ·)) ^ (-2)`). -/
noncomputable def case3SrcConst {d : ℕ} (S : SourceNormData d) (C : ℝ) : ℝ :=
  case3Conv3ConstShell (case3SupConst (srcLowerUnit S) C) * (logUpperConst S) ^ 2


end PercLib.CriticalLRP.Orchestration.HD.Case3
