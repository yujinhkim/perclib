/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# A normalized flat norm used as a coefficient counterexample

Independently authored during audit `smwp648b3`.  The flattened box has volume
one but contains a nonzero lattice point at distance `1/2`.  Consequently any
cutoff domination proof at a general source norm must not assume that every such
distance is at least one.
-/
module

public import PercLib.CriticalLRP.Orchestration.Defs

set_option autoImplicit false
set_option linter.unusedSimpArgs false

@[expose] public section

open MeasureTheory Set

namespace PercLib.CriticalLRP.Orchestration.Flat

noncomputable def flatC : Fin 2 → ℝ := ![2, 1 / 8]

/-- The Minkowski functional of `[-2,2] × [-1/8,1/8]`, written directly as
`max(|v₀|/2, 8|v₁|)`. -/
noncomputable def flatNorm (v : Fin 2 → ℝ) : ℝ := max (|v 0| / 2) (8 * |v 1|)

theorem flatNorm_zero : flatNorm 0 = 0 := by
  simp [flatNorm]

/-- Unit ball of `flatNorm` is the flat box. -/
theorem flatNorm_unitBall :
    {v : Fin 2 → ℝ | flatNorm v ≤ 1} =
      Set.pi Set.univ (fun i => Set.Icc (-(flatC i)) (flatC i)) := by
  ext v
  simp only [flatNorm, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc,
    flatC, Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor
  · intro h
    have h0 : |v 0| / 2 ≤ 1 := le_trans (le_max_left _ _) h
    have h1 : 8 * |v 1| ≤ 1 := le_trans (le_max_right _ _) h
    have h0' : |v 0| ≤ 2 := by linarith
    have h1' : |v 1| ≤ 1 / 8 := by linarith
    exact ⟨⟨by linarith [neg_abs_le (v 0)], by linarith [le_abs_self (v 0)]⟩,
      ⟨by linarith [neg_abs_le (v 1)], by linarith [le_abs_self (v 1)]⟩⟩
  · intro h
    obtain ⟨⟨h00, h01⟩, h10, h11⟩ := h
    have h0 : |v 0| ≤ 2 := abs_le.mpr ⟨h00, h01⟩
    have h1 : |v 1| ≤ 1 / 8 := abs_le.mpr ⟨h10, h11⟩
    exact max_le (by linarith) (by linarith)

/-- **The flat normalized norm is an admissible `SourceNormData`.** -/
noncomputable def flatSourceNorm : SourceNormData 2 where
  ρ := flatNorm
  ρ_zero := flatNorm_zero
  ρ_pos := by
    intro v hv
    simp only [flatNorm]
    rcases eq_or_ne (v 0) 0 with h0 | h0
    · have h1 : v 1 ≠ 0 := by
        intro h1
        exact hv (by funext i; fin_cases i <;> simp [h0, h1])
      have hpos : 0 < 8 * |v 1| := by
        have : 0 < |v 1| := abs_pos.mpr h1
        linarith
      exact lt_of_lt_of_le hpos (le_max_right _ _)
    · have hpos : 0 < |v 0| / 2 := by
        have : 0 < |v 0| := abs_pos.mpr h0
        linarith
      exact lt_of_lt_of_le hpos (le_max_left _ _)
  ρ_neg := by
    intro v
    simp [flatNorm, abs_neg]
  ρ_add_le := by
    intro v w
    have h0 : |(v + w) 0| ≤ |v 0| + |w 0| := by
      simpa using abs_add_le (v 0) (w 0)
    have h1 : |(v + w) 1| ≤ |v 1| + |w 1| := by
      simpa using abs_add_le (v 1) (w 1)
    refine max_le ?_ ?_
    · have hv : |v 0| / 2 ≤ flatNorm v := le_max_left _ _
      have hw : |w 0| / 2 ≤ flatNorm w := le_max_left _ _
      have : |(v + w) 0| / 2 ≤ (|v 0| + |w 0|) / 2 := by linarith
      linarith
    · have hv : 8 * |v 1| ≤ flatNorm v := le_max_right _ _
      have hw : 8 * |w 1| ≤ flatNorm w := le_max_right _ _
      have : 8 * |(v + w) 1| ≤ 8 * (|v 1| + |w 1|) := by linarith
      linarith
  ρ_smul := by
    intro c v
    simp only [flatNorm, Pi.smul_apply, smul_eq_mul, abs_mul]
    rw [show |c| * |v 0| / 2 = |c| * (|v 0| / 2) by ring,
      show 8 * (|c| * |v 1|) = |c| * (8 * |v 1|) by ring,
      ← mul_max_of_nonneg (a := |c|) (|v 0| / 2) (8 * |v 1|) (abs_nonneg c)]
  ρ_continuous := by
    unfold flatNorm
    exact ((continuous_apply 0).abs.div_const 2).max
      (continuous_const.mul (continuous_apply 1).abs)
  unitBall_volume := by
    rw [flatNorm_unitBall, MeasureTheory.volume_pi_pi]
    simp only [Real.volume_Icc, flatC, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2 - -2)]
    norm_num

/-- The lattice point `e₁ = (1,0)` in the flat norm. -/
def e1 : Fin 2 → ℤ := ![1, 0]

end PercLib.CriticalLRP.Orchestration.Flat
