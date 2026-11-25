/-
# Power–log profiles and constants for weighted ball shells

Accepted from swarm `smwtvrwnn` member `m1`, direction D7B.
-/
module

public import PercLib.CriticalLRP.Analysis.LatticeConvolution

/-!
The one-dimensional target and shell profiles, together with the explicit threshold and constant
used by the finite discrete power–log estimate.  All are independent of the outer lattice radius.
-/

set_option autoImplicit false

@[expose] public section

namespace CriticalLRPConv

/-- `S a c M = (1 + M)^a (log (2 + M))^{-c}`: the target profile at radius `M`. -/
noncomputable def Sfun (a c : ℝ) (M : ℕ) : ℝ :=
  (1 + (M : ℝ)) ^ a * LamR (M : ℝ) ^ (-c)

/-- `T a c M = (1 + M)^{a-1} (log (2 + M))^{-c}`: the shell weight at radius `M`. -/
noncomputable def Tfun (a c : ℝ) (M : ℕ) : ℝ :=
  (1 + (M : ℝ)) ^ (a - 1) * LamR (M : ℝ) ^ (-c)

/-- The threshold `⌈exp (4c/a)⌉` at which the logarithmic profile dominates `4c/a`. -/
noncomputable def coreThresh (a c : ℝ) : ℕ := ⌈Real.exp (4 * c / a)⌉₊

/-- The explicit constant of the one-dimensional core bound. -/
noncomputable def coreConst (a c : ℝ) : ℝ :=
  max (4 / a) ((coreThresh a c : ℝ) * (max 1 (((coreThresh a c : ℕ) : ℝ) ^ (a - 1))) *
    LamR ((0 : ℕ) : ℝ) ^ (-c) * LamR ((coreThresh a c : ℕ) : ℝ) ^ c) + 1

end CriticalLRPConv
