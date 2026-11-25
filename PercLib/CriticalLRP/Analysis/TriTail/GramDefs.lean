/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Gram coordinates for the triangle-tail reduction

Generic Hilbert-basis coordinates and the constant-kernel counterexample
object. Operator identities and triangle-tail applications are in
`Analysis/TriTailGram.lean`.

Reviewed from Ultramath `smwtqkdul`, member `m3`, `C3Gram.lean`.
-/
module

public import PercLib.CriticalLRP.Analysis.TriTailSqrt

/-! # Gram coordinates and counterexample kernels -/

@[expose] public section

open scoped ENNReal Topology RealInnerProductSpace

namespace PercLib.CriticalLRP.TriTail

section Abstract

variable {d : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The `ℓ²` coordinates of a vector along a Hilbert basis of a real Hilbert space. This is the
candidate `ξ = S 1_0` of Kozma (2011), §2. -/
noncomputable def gramCoord (b : HilbertBasis (Fin d → ℤ) ℝ H) (Ξ : H) :
    (Fin d → ℤ) → ℝ :=
  fun y => ⟪b y, Ξ⟫

end Abstract

section Negative

variable {d : ℕ}

/-- The constant kernel on `ℤ^d`, whose `(0,x)` entry is `1` for every `x` (so it certainly does
not decay). -/
def constantKernel (d : ℕ) : (Fin d → ℤ) → (Fin d → ℤ) → ℝ := fun _ _ => 1

end Negative

end PercLib.CriticalLRP.TriTail
