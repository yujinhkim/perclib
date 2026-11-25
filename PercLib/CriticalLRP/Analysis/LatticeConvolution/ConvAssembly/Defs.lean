module

public import PercLib.CriticalLRP.Analysis.LatticeConvolution.BallShell
public import PercLib.CriticalLRP.Analysis.LatticeConvolution.TailShell

/-!
# Generic convolution assembly: constants and the `A1`/`A2`/`A3` regions

For `a, b > 0` with `a + b < d`, the two-point convolution
`Σ' y, f y * g (x - y)` of kernels decaying like
`⟨·⟩^{-(d-a)} Λ^{-â}` and `⟨·⟩^{-(d-b)} Λ^{-b̂}` is controlled by
`⟨x⟩^{-(d-a-b)} Λ^{-(â+b̂)}`.  This file only fixes the notations: the explicit
`x`-independent constant and the region split of the proof of Lemma I.4.3.
No model input (kernel, cutoff, percolation measure) is used.
-/

set_option autoImplicit false

@[expose] public section

namespace CriticalLRPConv

/-- The explicit `S`-independent constant of the weighted ball-shell estimate on `ℤ^d`,
specialised from `ball_shell_bound_latticeInt`. -/
noncomputable def ballShellConst (d : ℕ) (a c : ℝ) : ℝ :=
  (2 : ℝ) ^ a * ((2 : ℝ) ^ (d : ℝ) * (1 + ((d : ℝ) - a + 2 * (c + 1)) * coreConst a c))

/-- The `A1` region: the ball of radius `‖x‖/2` around the origin. -/
def convReg1 {d : ℕ} (x : Fin d → ℤ) (y : Fin d → ℤ) : Prop := ‖y‖ ≤ ‖x‖ / 2

/-- The `A2` region: the ball of radius `‖x‖/2` around `x`. -/
def convReg2 {d : ℕ} (x : Fin d → ℤ) (y : Fin d → ℤ) : Prop := ‖x - y‖ ≤ ‖x‖ / 2

/-- The `A3` region: outside both half-balls. -/
def convReg3 {d : ℕ} (x : Fin d → ℤ) (y : Fin d → ℤ) : Prop :=
  ¬ convReg1 x y ∧ ¬ convReg2 x y

/-- The product majorant `Wt (d-a) â ‖y‖ · Wt (d-b) b̂ ‖x-y‖`. -/
noncomputable def convMajorant {d : ℕ} (a b ah bh : ℝ) (x y : Fin d → ℤ) : ℝ :=
  Wt ((d : ℝ) - a) ah ‖y‖ * Wt ((d : ℝ) - b) bh ‖(x - y : Fin d → ℤ)‖

/-- The `A1` contribution constant (product form, so that region bounds combine by `ring`). -/
noncomputable def convReg1Const (d : ℕ) (a b ah bh : ℝ) : ℝ :=
  (2 : ℝ) ^ (((d : ℝ) - b) + bh) * (2 : ℝ) ^ ah * ballShellConst d a ah

/-- The `A2` contribution constant. -/
noncomputable def convReg2Const (d : ℕ) (a b ah bh : ℝ) : ℝ :=
  (2 : ℝ) ^ (((d : ℝ) - a) + ah) * (2 : ℝ) ^ bh * ballShellConst d b bh

/-- The `A3` contribution constant. -/
noncomputable def convReg3Const (d : ℕ) (a b ah bh : ℝ) : ℝ :=
  (2 : ℝ) ^ ah * (2 : ℝ) ^ bh *
    (2 * ((2 : ℝ) ^ ((d : ℝ) - a - b) * tailShellConst d ((d : ℝ) - a - b)))

/-- The total (region-summed) constant of the convolution assembly. -/
noncomputable def convConst (d : ℕ) (a b ah bh : ℝ) : ℝ :=
  convReg1Const d a b ah bh + convReg2Const d a b ah bh + convReg3Const d a b ah bh

/-- The target profile `⟨A⟩^{-(d-a-b)} Λ(A)^{-(â+b̂)}` at a real radius `A`. -/
noncomputable def convTargetR (d : ℕ) (a b ah bh A : ℝ) : ℝ :=
  Wt ((d : ℝ) - a - b) (ah + bh) A

/-- The target profile `⟨‖x‖⟩^{-(d-a-b)} Λ(‖x‖)^{-(â+b̂)}`. -/
noncomputable def convTarget {d : ℕ} (a b ah bh : ℝ) (x : Fin d → ℤ) : ℝ :=
  convTargetR d a b ah bh ‖x‖

lemma convTarget_eq {d : ℕ} (a b ah bh : ℝ) (x : Fin d → ℤ) :
    convTarget a b ah bh x = convTargetR d a b ah bh ‖x‖ := rfl

end CriticalLRPConv
