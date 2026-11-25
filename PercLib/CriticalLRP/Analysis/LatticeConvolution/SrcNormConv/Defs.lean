/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
-/
module

public import PercLib.CriticalLRP.Analysis.LatticeConvolution.ConvAssembly.Main
public import PercLib.CriticalLRP.Analysis.LatticeConvolution.NormShell

/-!
# The strict convolution assembly in an arbitrary normalized source norm

Definition layer: the `S.ρ`-radius regions `A1`/`A2`/`A3`, the product majorant, the
region constants and the target profile, all stated for an arbitrary normalized
`SourceNormData S` instead of the lattice supremum norm.
-/

set_option autoImplicit false

@[expose] public section

namespace SrcNormConv

open PercLib.CriticalLRP.Orchestration

variable {d : ℕ}

/-- The `S.ρ`-radius of a lattice point, i.e. the source distance `S.dist 0 y`. -/
noncomputable def srcRadius (S : SourceNormData d) (y : Fin d → ℤ) : ℝ := S.ρ (toVec y)

/-- The source radius is the source distance from the origin. -/
theorem srcRadius_eq_dist (S : SourceNormData d) (y : Fin d → ℤ) :
    srcRadius S y = S.dist 0 y :=
  (CriticalLRPConv.dist_zero_eq_srcNorm S y).symm

/-- The source radius is nonnegative. -/
theorem srcRadius_nonneg (S : SourceNormData d) (y : Fin d → ℤ) : 0 ≤ srcRadius S y :=
  CriticalLRPConv.src_nonneg S (toVec y)

/-- The `A1` region in the source norm: the ball of `S.ρ`-radius `S.ρ x / 2`. -/
def srcConvReg1 (S : SourceNormData d) (x y : Fin d → ℤ) : Prop :=
  srcRadius S y ≤ srcRadius S x / 2

/-- The `A2` region in the source norm: the ball of `S.ρ`-radius `S.ρ x / 2` around `x`. -/
def srcConvReg2 (S : SourceNormData d) (x y : Fin d → ℤ) : Prop :=
  srcRadius S (x - y) ≤ srcRadius S x / 2

/-- The `A3` region in the source norm: outside both half-balls. -/
def srcConvReg3 (S : SourceNormData d) (x y : Fin d → ℤ) : Prop :=
  ¬ srcConvReg1 S x y ∧ ¬ srcConvReg2 S x y

/-- The product majorant `Wt (d-a) â (S.ρ y) · Wt (d-b) b̂ (S.ρ (x-y))` in the source norm. -/
noncomputable def srcConvMajorant (S : SourceNormData d) (a b ah bh : ℝ)
    (x y : Fin d → ℤ) : ℝ :=
  CriticalLRPConv.Wt ((d : ℝ) - a) ah (srcRadius S y) *
    CriticalLRPConv.Wt ((d : ℝ) - b) bh (srcRadius S (x - y))

/-- The transferred ball-shell factor of `NormShell`, `2^a (K_count (1 + κ coreConst))`. -/
noncomputable def srcBallShellConst (S : SourceNormData d) (a c : ℝ) : ℝ :=
  (2 : ℝ) ^ a * (CriticalLRPConv.srcCountConst S *
    (1 + ((d : ℝ) - a + 2 * (c + 1)) * CriticalLRPConv.coreConst a c))

/-- The `A1` contribution constant in the source norm. -/
noncomputable def srcConvReg1Const (S : SourceNormData d) (a b ah bh : ℝ) : ℝ :=
  (2 : ℝ) ^ (((d : ℝ) - b) + bh) * (srcBallShellConst (d := d) S a ah * (2 : ℝ) ^ ah)

/-- The `A2` contribution constant in the source norm. -/
noncomputable def srcConvReg2Const (S : SourceNormData d) (a b ah bh : ℝ) : ℝ :=
  (2 : ℝ) ^ (((d : ℝ) - a) + ah) * (srcBallShellConst (d := d) S b bh * (2 : ℝ) ^ bh)

/-- The norm-dependent factor of the pure power tail estimate in the source norm. -/
noncomputable def srcPowTailConst (S : SourceNormData d) (γ : ℝ) : ℝ :=
  CriticalLRPConv.srcLowerUnit S ^ (-((d : ℝ) + γ)) * CriticalLRPConv.tailShellConst d γ *
    CriticalLRPConv.srcUpperConst S ^ γ

/-- The `A3` contribution constant of one far half, in the source norm. -/
noncomputable def srcConvReg3aConst (S : SourceNormData d) (a b ah bh : ℝ) : ℝ :=
  (2 : ℝ) ^ ah * (2 : ℝ) ^ bh *
    ((2 : ℝ) ^ ((d : ℝ) - a - b) * srcPowTailConst (d := d) S ((d : ℝ) - a - b))

/-- The `A3` contribution constant in the source norm (both far halves). -/
noncomputable def srcConvReg3Const (S : SourceNormData d) (a b ah bh : ℝ) : ℝ :=
  srcConvReg3aConst (d := d) S a b ah bh + srcConvReg3aConst (d := d) S a b ah bh

/-- The total (region-summed) constant of the source-norm convolution assembly. -/
noncomputable def srcConvConst (S : SourceNormData d) (a b ah bh : ℝ) : ℝ :=
  srcConvReg1Const (d := d) S a b ah bh + srcConvReg2Const (d := d) S a b ah bh +
    srcConvReg3Const (d := d) S a b ah bh

/-- The target profile `⟨A⟩^{-(d-a-b)} Λ(A)^{-(â+b̂)}` of the source-norm assembly. -/
noncomputable def srcConvTarget (S : SourceNormData d) (a b ah bh : ℝ)
    (x : Fin d → ℤ) : ℝ :=
  CriticalLRPConv.Wt ((d : ℝ) - a - b) (ah + bh) (srcRadius S x)

/-! ## §2 Unfolding lemmas in terms of `S.ρ (toVec ·)` -/

/-- The `A1` region, unfolded to the explicit source-norm inequality. -/
theorem srcConvReg1_iff (S : SourceNormData d) (x y : Fin d → ℤ) :
    srcConvReg1 S x y ↔ S.ρ (toVec y) ≤ S.ρ (toVec x) / 2 := Iff.rfl

/-- The `A2` region, unfolded to the explicit source-norm inequality. -/
theorem srcConvReg2_iff (S : SourceNormData d) (x y : Fin d → ℤ) :
    srcConvReg2 S x y ↔ S.ρ (toVec (x - y)) ≤ S.ρ (toVec x) / 2 := Iff.rfl

/-- The product majorant, unfolded to the explicit source-norm weights. -/
theorem srcConvMajorant_eq (S : SourceNormData d) (a b ah bh : ℝ) (x y : Fin d → ℤ) :
    srcConvMajorant S a b ah bh x y =
      CriticalLRPConv.Wt ((d : ℝ) - a) ah (S.ρ (toVec y)) *
        CriticalLRPConv.Wt ((d : ℝ) - b) bh (S.ρ (toVec (x - y))) := rfl

/-- The target profile, unfolded to the explicit source-norm weight. -/
theorem srcConvTarget_eq (S : SourceNormData d) (a b ah bh : ℝ) (x : Fin d → ℤ) :
    srcConvTarget S a b ah bh x =
      CriticalLRPConv.Wt ((d : ℝ) - a - b) (ah + bh) (S.ρ (toVec x)) := rfl

end SrcNormConv
