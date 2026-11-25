module

public import PercLib.CriticalLRP.Analysis.LatticeConvolution.ConvAssembly.Defs

/-!
# Generic convolution assembly (`a + b < d`): elementary profile inequalities
-/

set_option autoImplicit false

@[expose] public section

namespace CriticalLRPConv

open PercLib.CriticalLRP.FiniteVolume (linfNorm)

/-! ## §1 The lattice sup norm versus `linfNorm` -/

/-- The real sup norm of a lattice point is its integer-valued sup norm. -/
lemma coe_norm_eq_linfNorm {d : ℕ} (z : Fin d → ℤ) : (‖z‖ : ℝ) = (linfNorm z : ℝ) := by
  refine le_antisymm ?_ ?_
  · rw [pi_norm_le_iff_of_nonneg (Nat.cast_nonneg (linfNorm z))]
    intro i
    rw [← PercLib.Models.LongRange.natCast_natAbs_eq_norm]
    exact_mod_cast (PercLib.CriticalLRP.FiniteVolume.linfNorm_le_iff.mp le_rfl i)
  · have h : linfNorm z ≤ ⌊‖z‖⌋₊ := by
      rw [PercLib.CriticalLRP.FiniteVolume.linfNorm_le_iff]
      intro i
      rw [Nat.le_floor_iff (norm_nonneg z), PercLib.Models.LongRange.natCast_natAbs_eq_norm]
      exact norm_le_pi_norm z i
    calc (linfNorm z : ℝ) ≤ ((⌊‖z‖⌋₊ : ℕ) : ℝ) := by exact_mod_cast h
      _ = ‖z‖ := PercLib.Models.LongRange.natCast_floor_norm z

end CriticalLRPConv
