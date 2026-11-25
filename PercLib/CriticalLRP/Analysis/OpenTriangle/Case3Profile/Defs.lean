/-
Direction B: the log-corrected Case 3 threefold convolution profile at `d = 6`.

Definitions only: the explicit conversion and assembly constants.  The proofs are in
`Case3Profile.Main`, which imports this module.

Source shape of the Case 3 HD input (PDF p. 9, as recorded in
`docs/CRITICAL_LRP_HD_CONVOLUTION_PLAN.md`): `d = 6`, `α = 2` and

  `P_βc(x ↔ y) ≼ (log ‖x-y‖)^(-1) ‖x-y‖^(-d+2)`   for `x ≠ y`.
-/
module

public import PercLib.CriticalLRP.Analysis.LatticeConvolution.MargConv.Defs

/-!
# Constants of the Case 3 logarithmic profile (`d = 6`)

Every constant is a closed real expression in the dimension `d`, the Case 3 domination
constant `C` and the frozen convolution constants `convConst`, `margConst` of
`CriticalLRPConv`.  No model input and no property of a two-point function is used here.
-/

set_option autoImplicit false
set_option linter.hashCommand false

@[expose] public section

namespace PercLib.CriticalLRP.Orchestration.HD.Case3

open CriticalLRPConv

/-! ## §1 The conversion constants -/

/-- Conversion constant of the Case 3 input when the logarithm is read in the paper's
frozen convention `Λ x = log (2 + ‖x‖)` (i.e. the source's `log ‖x-y‖` with the standard
near-origin regularisation).  The `2^(d-2)` is the shift `1 + ‖x‖ ≤ 2‖x‖` on a nonzero
lattice point; the `+ 1` covers the excluded origin `x = 0`, where `t 0 = 1`. -/
noncomputable def case3LamConst (d : ℕ) (C : ℝ) : ℝ := C * (2 : ℝ) ^ ((d : ℝ) - 2) + 1

/-- Conversion constant of the Case 3 input under the *literal* reading `(log ‖x‖)^(-1)`.
On a nonzero lattice point `‖x‖ ≥ 1`, so the only extra cost against `case3LamConst` is the
comparison `log (2+r) ≤ 3 log r` valid for `r ≥ 2`; the point `‖x‖ = 1` contributes nothing
because `Real.log 1 = 0` and `0⁻¹ = 0` in Lean's real logarithm convention. -/
noncomputable def case3LogConst (d : ℕ) (C : ℝ) : ℝ := C * (3 * (2 : ℝ) ^ ((d : ℝ) - 2)) + 1

/-- The constant of the first (strict) Case 3 convolution. -/
noncomputable def case3Conv2Const (d : ℕ) (C : ℝ) : ℝ :=
  case3LogConst d C * case3LogConst d C * convConst d 2 2 1 1

/-- The constant of the second (marginal) Case 3 convolution at `d = 6`. -/
noncomputable def case3Conv3Const (C : ℝ) : ℝ :=
  case3Conv2Const 6 C * case3LogConst 6 C * margConst 6 4 2 2 1

/-! ## §2 Companions: the `d > 6` profile and the frozen-logarithm chain -/

/-- The constant of the `d > 6` Case 3 companion. -/
noncomputable def case3Conv3ConstHigh (d : ℕ) (C : ℝ) : ℝ :=
  case3Conv2Const d C * case3LogConst d C * convConst d 4 2 2 1

/-- The constant of the frozen-logarithm Case 3 chain. -/
noncomputable def case3LamConv2Const (d : ℕ) (C : ℝ) : ℝ :=
  case3LamConst d C * case3LamConst d C * convConst d 2 2 1 1

/-- The end-to-end constant of the frozen-logarithm Case 3 chain at `d = 6`. -/
noncomputable def case3Conv3ConstLam (C : ℝ) : ℝ :=
  case3LamConv2Const 6 C * case3LamConst 6 C * margConst 6 4 2 2 1

/-! ## §3 The source-shaped (`t ≤ 1`) constants -/

/-- The conversion constant of the source-shaped Case 3 input: `t ≤ 1` everywhere and the
decay hypothesis only off the unit shell (`‖x‖ ≥ 2`).  The `max` covers the unit shell, where
`Wt (d-2) 1 1 = 2^(-(d-2)) (log 3)^(-1) > 1`; the origin is free because
`Wt (d-2) 1 0 = (log 2)^(-1) > 1`. -/
noncomputable def case3ShellConst (d : ℕ) (C : ℝ) : ℝ :=
  max (C * (3 * (2 : ℝ) ^ ((d : ℝ) - 2))) ((2 : ℝ) ^ ((d : ℝ) - 2) * Real.log 3) + 1

/-- The end-to-end constant of the source-shaped Case 3 chain at `d = 6`. -/
noncomputable def case3Conv3ConstShell (C : ℝ) : ℝ :=
  case3ShellConst 6 C * case3ShellConst 6 C * convConst 6 2 2 1 1 * case3ShellConst 6 C *
    margConst 6 4 2 2 1

end PercLib.CriticalLRP.Orchestration.HD.Case3
