
module

public import PercLib.CriticalLRP.Analysis.KernelOperator.Model
public import PercLib.CriticalLRP.Analysis.KernelOperator.CutoffDefs
public import PercLib.CriticalLRP.Analysis.KernelOperator.SchurComp

/-!
The O1 discharge at the actual cutoff two-point kernel.

Swarm `smwttizjk`, member `m2`, direction D6A.

`cutTwoPoint_schurKernel` shows that at the range-truncated law the two-point matrix is a Schur
kernel with constant `χ(r) = M.cutMassAt r 0` (finiteness of the expected cluster volume).  The
abstract closure `schurKernel_kernelComp` then makes the *two-step* connection kernel
`kernelComp κ κ` and the *three-step* kernel `kernelCube κ` Schur kernels at the same law, with
constants `χ²` and `χ³`, and identifies the third iterate of the kernel operator with the cube
kernel — with no further hypothesis beyond `M.cutMassAt r 0 ≠ ⊤`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace PercLib.CriticalLRP.KernelOperator

open PercLib.CriticalLRP.Orchestration

variable (M : SourceModelData)

/-- **The cutoff two-point kernel is a Schur kernel**, restated for `cutKernel`. -/
theorem cutKernel_schurKernel (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) :
    SchurKernel (cutKernel M r) (M.cutMassAt r 0).toReal :=
  cutTwoPoint_schurKernel M r hχ

/-- **O1 at the actual truncated law: the two-step connection kernel is a Schur kernel with
constant `χ(r)²`.**  This is the hypothesis `h2` of `kernelApply_three_eq`, derived here from
finiteness of the truncated cluster mass alone. -/
theorem cutKernel_comp_schurKernel (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) :
    SchurKernel (kernelComp (cutKernel M r) (cutKernel M r))
      ((M.cutMassAt r 0).toReal * (M.cutMassAt r 0).toReal) :=
  schurKernel_kernelComp (cutKernel_schurKernel M r hχ)

/-- **The three-step connection kernel at the truncated law is a Schur kernel with constant
`χ(r)³`.** -/
theorem cutKernel_cube_schurKernel (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) :
    SchurKernel (kernelCube (cutKernel M r))
      ((M.cutMassAt r 0).toReal * ((M.cutMassAt r 0).toReal * (M.cutMassAt r 0).toReal)) :=
  schurKernel_kernelCube (cutKernel_schurKernel M r hχ)

/-- **The three-fold iterate of the truncated two-point operator acts by the cube kernel.**  No
Schur hypothesis on the two-step kernel is assumed: it is supplied by
`cutKernel_comp_schurKernel` from finite truncated cluster mass. -/
theorem cutKernel_apply_three_eq (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) {g : M.V → ℝ}
    (hg : Summable fun z => g z ^ 2) (x : M.V) :
    kernelApply (cutKernel M r) (kernelApply (cutKernel M r) (kernelApply (cutKernel M r) g)) x
      = ∑' z, kernelCube (cutKernel M r) x z * g z :=
  kernelApply_three_eq_of_schurKernel (cutKernel_schurKernel M r hχ) hg x

/-- **The cube kernel operator at the truncated law is bounded on `ℓ²` with norm at most
`χ(r)³`.** -/
theorem cutKernel_cube_tsum_sq_le (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) (g : M.V → ℝ)
    (hg : Summable fun z => g z ^ 2) :
    Summable (fun x => kernelApply (kernelCube (cutKernel M r)) g x ^ 2) ∧
      ∑' x, kernelApply (kernelCube (cutKernel M r)) g x ^ 2
        ≤ (M.cutMassAt r 0).toReal * ((M.cutMassAt r 0).toReal * (M.cutMassAt r 0).toReal)
          * ((M.cutMassAt r 0).toReal * ((M.cutMassAt r 0).toReal * (M.cutMassAt r 0).toReal))
          * ∑' y, g y ^ 2 :=
  kernelCube_tsum_sq_le (cutKernel_schurKernel M r hχ) g hg

end PercLib.CriticalLRP.KernelOperator
