/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Open triangles and their configured tails

Accepted from independent submission `smwp648b3` direction D2.  The closed
`≥` and strict `>` tails are deliberately separate source objects.
-/
module

public import PercLib.CriticalLRP.Correlation.I411.DiagramAssembly
public import PercLib.CriticalLRP.Tightness.LemmaI26Averaging
public import PercLib.Percolation.Bond.ConnectionKernel
public import PercLib.CriticalLRP.BK.CanonicalBridge
public import PercLib.CriticalLRP.CountableProduct.LRPTailBounds

@[expose] public section

open scoped ENNReal
open Filter

namespace PercLib.CriticalLRP.TriTail

variable {d : ℕ} {J : Sym2 (Fin d → ℤ) → ℝ}

/-- **The open triangle** `∇_β` of §I.4.1 at the configured kernel:
`∇_β(x,y) = ∑_{u,v} τ(x,u) τ(u,v) τ(v,y)`. The source's special case is `x = 0`. -/
noncomputable def openTriangle (J : Sym2 (Fin d → ℤ) → ℝ) (hJ : ∀ e, 0 ≤ J e) (β : NNReal)
    (x y : Fin d → ℤ) : ℝ≥0∞ :=
  ∑' u, ∑' v, twoPointFunction J hJ β x u * twoPointFunction J hJ β u v *
    twoPointFunction J hJ β v y

/-- **The triangle diagram** `∇_β = ∇_β(0,0)`: the diagonal value of the open triangle. -/
noncomputable def openTriangleSelf (J : Sym2 (Fin d → ℤ) → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (β : NNReal) (x : Fin d → ℤ) : ℝ≥0∞ :=
  openTriangle J hJ β x x

/-- **The open-triangle tail** of §I.4.1: `∇_r = sup_{‖x‖ ≥ r} ∇_{β_c}(0,x)`, where `‖·‖` is the
lattice sup-norm `FiniteVolume.linfNorm` (so `latticeDist 0 x = ‖x‖_∞` as a real number). -/
noncomputable def openTriangleTail (J : Sym2 (Fin d → ℤ) → ℝ) (hJ : ∀ e, 0 ≤ J e) (β : NNReal)
    (r : ℝ) : ℝ≥0∞ :=
  ⨆ x, ⨆ (_ : r ≤ FiniteVolume.latticeDist 0 x), openTriangle J hJ β 0 x

/-- The same tail with the *strict* condition `‖x‖ > r`, i.e. exactly `w ∉ B(v,r)` when `B` is the
closed ball: Kozma's formulation of the open triangle condition. -/
noncomputable def openTriangleTailOpen (J : Sym2 (Fin d → ℤ) → ℝ) (hJ : ∀ e, 0 ≤ J e)
    (β : NNReal) (r : ℝ) : ℝ≥0∞ :=
  ⨆ x, ⨆ (_ : r < FiniteVolume.latticeDist 0 x), openTriangle J hJ β 0 x

end PercLib.CriticalLRP.TriTail
