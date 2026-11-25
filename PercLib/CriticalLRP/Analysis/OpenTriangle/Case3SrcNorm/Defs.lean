/-
Literal printed Case 3: normalized-source norm constants.

Split from the reviewed `smwu4e7s3/m2/Case3SrcNorm.lean` artifact. The source's raw logarithm
is retained. The proofs are in `Case3SrcNorm.Main`.
-/
module

public import PercLib.CriticalLRP.Analysis.OpenTriangle.Case3Literal.Main
public import PercLib.CriticalLRP.Analysis.LatticeConvolution.NormShell

/-!
# Constants for the literal printed source-norm Case 3 transfer

`case3SrcThreshold` controls the large sup-norm shells where the raw logarithm is safely positive;
`case3SrcConst` also covers the remaining bounded shells by the probability upper bound.
`case3SrcOutConst` includes the output logarithmic norm comparison. No shifted logarithm or
non-vacuity hypothesis is introduced.
-/

@[expose] public section

set_option autoImplicit false

namespace PercLib.CriticalLRP.Orchestration

open CriticalLRPConv

/-- The sup-norm threshold `T = max 2 (4 / srcLowerUnit S)`: above it, `srcLowerUnit S * ‖z‖ ≥ 4`,
so `log (srcLowerUnit S * ‖z‖) ≥ log 4 > 0`. -/
noncomputable def case3SrcThreshold {d : ℕ} (S : SourceNormData d) : ℝ :=
  max 2 (4 / srcLowerUnit S)

/-- The transfer constant of the literal printed HD(3).

The first branch is the genuine transfer `C c^e (1 + (-log c)/log 4)`; the second branch
`(T^e)⁻¹ log T` is what the bounded region `2 ≤ ‖z‖ ≤ T` needs from `τ ≤ 1`.  The `+ 1` makes the
constant positive.  Both branches are explicit; no norm-dependent quantity is dropped. -/
noncomputable def case3SrcConst (d : ℕ) (C : ℝ) (S : SourceNormData d) : ℝ :=
  max (C * (srcLowerUnit S) ^ (-(d : ℝ) + 2) *
        (1 + (-(Real.log (srcLowerUnit S))) / Real.log 4))
      ((case3SrcThreshold S ^ (-(d : ℝ) + 2))⁻¹ * Real.log (case3SrcThreshold S)) + 1


/-- The output constant: the landed Case 3 supershell constant at the transferred input constant,
times the square of the `log (1 + S.ρ)`-versus-`log (1 + ‖·‖)` comparison constant. -/
noncomputable def case3SrcOutConst (d : ℕ) (C : ℝ) (S : SourceNormData d) : ℝ :=
  HD.Case3.case3Conv3ConstShell (case3SrcConst d C S) * srcLogConstUpper S ^ (2 : ℝ)


end PercLib.CriticalLRP.Orchestration
