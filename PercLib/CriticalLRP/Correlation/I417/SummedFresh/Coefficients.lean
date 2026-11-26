/-
Coefficient cross-checks for direction `(B) UNRESTRICTED-FIBRE EVALUATION`
(swarm `smwxtabcx`, member `m2`).

The fresh polynomial of `Main` uses production's coefficients `I417FreshDepth.genCoeff q ℓ`.  The
accepted `q = 4` artifact of this repository (`I417FreshFour.Eval.freshFourProfile`) records the row
`6 χ⁴T⁴ + 12 χ⁵T³ + 15 χ⁶T² + 15 χ⁷T`, i.e. `C_1, …, C_4 = 15, 15, 12, 6`; the depth bookkeeping of
`Fresh/Depth/Defs.lean` records `(1,1)`, `(3,3,2)`, `(15,15,12,6)`, `(105,105,90,60,24)` for
`q = 2, 3, 4, 5`.  The evaluations below re-check the first three rows by kernel reduction, so the
coefficients of `freshProfileSum` are the accepted ones and the depth range really is `[1,q]`.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.SummedFresh.Main

/-! Kernel-reduction checks for the profile coefficients. -/

set_option linter.hashCommand false

open PercLib.CriticalLRP

/-! ## `q = 2`:  `C_1 = C_2 = 1`, so the bound is `χ³ T(w,y) + χ² T²(w,y)` -/

example : I417FreshDepth.genCoeff 2 1 = 1 := by decide
example : I417FreshDepth.genCoeff 2 2 = 1 := by decide
example : I417FreshDepth.genCoeff 2 0 = 0 := by decide
example : I417FreshDepth.genCoeff 2 3 = 0 := by decide

/-! ## `q = 3`:  `C = (3, 3, 2)` -/

example : I417FreshDepth.genCoeff 3 1 = 3 := by decide
example : I417FreshDepth.genCoeff 3 2 = 3 := by decide
example : I417FreshDepth.genCoeff 3 3 = 2 := by decide

/-! ## `q = 4`:  `C = (15, 15, 12, 6)`, the accepted `q = 4` profile -/

example : I417FreshDepth.genCoeff 4 1 = 15 := by decide
example : I417FreshDepth.genCoeff 4 2 = 15 := by decide
example : I417FreshDepth.genCoeff 4 3 = 12 := by decide
example : I417FreshDepth.genCoeff 4 4 = 6 := by decide

/-! ## `q = 1` -/

example : I417FreshDepth.genCoeff 1 1 = 1 :=
  PercLib.CriticalLRP.I417SummedFresh.genCoeff_one_one
example : I417FreshDepth.genCoeff 1 0 = 0 := by decide
