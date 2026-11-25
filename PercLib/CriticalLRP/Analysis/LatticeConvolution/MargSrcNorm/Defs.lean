/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
-/
module

public import PercLib.CriticalLRP.Analysis.LatticeConvolution.MargConv.Main
public import PercLib.CriticalLRP.Analysis.LatticeConvolution.SrcNormConv.Transfer

/-!
# The marginal (`a + b = d`) convolution constant in an arbitrary normalized source norm

Definition layer for the source-norm transfer of the frozen marginal assembly
`CriticalLRPConv.conv_tsum_le_marg` (`MargConv.Main`).  The strict-regime transfer of
`SrcNormConv.Transfer` pays the transfer constants of `NormShell`
(`srcLowerUnit`, `srcLogConst` on the hypothesis side, `srcUpperConst`,
`srcLogConstUpper` on the target side) and returns the target profile
`⟨S.ρ x⟩^{-(d-a-b)} Λ(S.ρ x)^{-(â+b̂)}`.  In the marginal case `a + b = d` the power
exponent vanishes and the target profile becomes the pure logarithmic
`Λ(S.ρ x)^{1-(â+b̂)} = Wt 0 (â+b̂-1) (S.ρ x)`, so the transfer constants are the same
except that the target-side logarithmic exponent drops from `â+b̂` to `â+b̂-1`.

The constants are assembled here; the transfer theorems are in `MargSrcNorm.Main`.
-/

set_option autoImplicit false

@[expose] public section

namespace SrcNormConv

open PercLib.CriticalLRP.Orchestration
open CriticalLRPConv

variable {d : ℕ}

/-- The transfer constant of the marginal source-norm assembly.  It is the strict-regime
constant `srcTransferConst` with the target-side logarithmic exponent lowered from `â+b̂`
to `â+b̂-1`: the hypothesis side pays `srcLowerUnit^{-(d-a)} srcLogConst^{â}` and
`srcLowerUnit^{-(d-b)} srcLogConst^{b̂}`, the target side pays
`srcLogConstUpper^{â+b̂-1}` (and one factor `srcUpperConst^0 = 1`). -/
noncomputable def srcMargTransferConst (S : SourceNormData d) (a b ah bh : ℝ) : ℝ :=
  (CriticalLRPConv.srcLowerUnit S ^ (-((d : ℝ) - a)) * CriticalLRPConv.srcLogConst S ^ ah) *
    (CriticalLRPConv.srcLowerUnit S ^ (-((d : ℝ) - b)) * CriticalLRPConv.srcLogConst S ^ bh) *
      CriticalLRPConv.srcLogConstUpper S ^ (ah + bh - 1)

/-- The marginal target profile in the source norm: `Wt 0 (â+b̂-1) (S.ρ x)`, i.e.
`Λ(S.ρ x)^{1-(â+b̂)}`. -/
noncomputable def srcMargTarget (S : SourceNormData d) (ah bh : ℝ) (x : Fin d → ℤ) : ℝ :=
  CriticalLRPConv.Wt 0 (ah + bh - 1) (S.ρ (toVec x))

/-- The marginal target profile written with the model source distance `S.dist 0 x`
instead of `S.ρ (toVec x)`; the two agree by `dist_zero_eq_srcNorm`. -/
noncomputable def srcMargTargetDist (S : SourceNormData d) (ah bh : ℝ) (x : Fin d → ℤ) : ℝ :=
  CriticalLRPConv.Wt 0 (ah + bh - 1) (SourceNormData.dist S 0 x)

/-- The full constant of the marginal source-norm assembly: the transfer constant times the
frozen sup-norm assembly constant `margConst`. -/
noncomputable def srcMargConst (S : SourceNormData d) (a b ah bh : ℝ) : ℝ :=
  srcMargTransferConst S a b ah bh * CriticalLRPConv.margConst d a b ah bh

end SrcNormConv

/-! ## Axiom audit of the definition layer -/

set_option linter.hashCommand false

#print axioms SrcNormConv.srcMargTransferConst
#print axioms SrcNormConv.srcMargTarget
#print axioms SrcNormConv.srcMargTargetDist
#print axioms SrcNormConv.srcMargConst
