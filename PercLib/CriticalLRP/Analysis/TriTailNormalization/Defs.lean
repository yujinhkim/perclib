module

public import PercLib.CriticalLRP.Orchestration.Defs

/-! # Definitions for explicit-triangle normalization -/

@[expose] public section

open scoped ENNReal

noncomputable section

namespace PercLib.CriticalLRP.TriTail

variable {d : ℕ}

noncomputable def openTriangleKernel (τ : (Fin d → ℤ) → (Fin d → ℤ) → ℝ≥0∞)
    (x y : Fin d → ℤ) : ℝ≥0∞ :=
  ∑' u, ∑' v, τ x u * τ u v * τ v y

noncomputable def gramKernel (f : (Fin d → ℤ) → ℝ) : (Fin d → ℤ) → (Fin d → ℤ) → ℝ≥0∞ :=
  fun u v => ∑' z, ENNReal.ofReal (f z) * ENNReal.ofReal (f (z + v - u))

def deltaProfile (d : ℕ) : (Fin d → ℤ) → ℝ := fun z => if z = 0 then (1 : ℝ) else 0

noncomputable def conv (H K : (Fin d → ℤ) → ℝ≥0∞) : (Fin d → ℤ) → ℝ≥0∞ :=
  fun w => ∑' z, H z * K (w - z)

noncomputable def refl (H : (Fin d → ℤ) → ℝ≥0∞) : (Fin d → ℤ) → ℝ≥0∞ :=
  fun w => H (-w)

end PercLib.CriticalLRP.TriTail
