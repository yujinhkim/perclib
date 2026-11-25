/-
# Explicit constants for weighted lattice tail shells

Accepted from swarm `smwtvrwnn` member `m5`, direction D7A.
-/
module

public import PercLib.CriticalLRP.Analysis.LatticeConvolution

/-!
Constants used by the finite and infinite weighted-tail estimates.  They depend on the lattice
dimension and decay exponents, never on the outer radius.
-/

set_option autoImplicit false

@[expose] public section

namespace CriticalLRPConv

/-- The explicit `S`-independent constant of the weighted tail-shell estimate. -/
noncomputable def tailShellConst (d : ℕ) (γ : ℝ) : ℝ :=
  2 * (d : ℝ) * 3 ^ (d - 1) * 2 ^ (1 + 2 * γ) / γ

/-- The explicit constant of the pure-logarithmic (`γ = 0`, `c > 1`) tail estimate. -/
noncomputable def tailShellConstLog (d : ℕ) (c : ℝ) : ℝ :=
  2 * (d : ℝ) * 3 ^ (d - 1) * (8 * 2 ^ c / (c - 1))

end CriticalLRPConv
