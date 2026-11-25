/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Non-vacuity and the general-norm coefficient caveat

The witnesses come from independent audit `smwp648b3`.  The normalized source
model is inhabited.  Separately, a flat normalized norm proves that
`1 - K r / K 1` is a raw sup-norm formula, not a valid general-source-norm
formula.  The general comparison is therefore proved through
`SourceModelData.cutKernel_le_kernel`, not through this coefficient.
-/
module

public import PercLib.CriticalLRP.Orchestration.ModelWitness.Defs
public import PercLib.CriticalLRP.Orchestration.FlatNorm.Defs

set_option autoImplicit false
set_option linter.unusedSimpArgs false

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PercLib.CriticalLRP.Orchestration.Witness

/-- The normalized source-norm vocabulary is inhabited in every dimension. -/
theorem sourceNormData_nonempty (d : ℕ) : Nonempty (SourceNormData d) :=
  ⟨sourceNormWitness d⟩

/-- A concrete inhabitant with `d = 1`, `α = 1`, source-normalized unit ball,
and the exact power-law derivative (zero logarithmic error). -/
theorem sourceModelData_nonempty : Nonempty SourceModelData :=
  ⟨sourceModelWitness 1 le_rfl 1 zero_lt_one⟩

#print axioms PercLib.CriticalLRP.Orchestration.Witness.sourceNormWitness
#print axioms PercLib.CriticalLRP.Orchestration.Witness.sourceModelWitness
#print axioms PercLib.CriticalLRP.Orchestration.Witness.sourceModelWitness_K_two_lt_one
#print axioms PercLib.CriticalLRP.Orchestration.Witness.sourceNormData_nonempty
#print axioms PercLib.CriticalLRP.Orchestration.Witness.sourceModelData_nonempty

end PercLib.CriticalLRP.Orchestration.Witness

namespace PercLib.CriticalLRP.Orchestration.Flat

/-- **An admissible source norm can put a nonzero lattice point at distance `1/2`.** -/
theorem flat_dist_e1 : flatSourceNorm.dist 0 e1 = 1 / 2 := by
  simp only [SourceNormData.dist, flatSourceNorm, flatNorm, e1, toVec, Pi.sub_apply, Pi.zero_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Int.cast_one, Int.cast_zero, abs_one, abs_zero,
    mul_zero, sub_zero, max_eq_left]
  norm_num

/-- At `r = 1` and the source-normalized kernel `K s = s^{-3}/3` (`d = 2`, `α = 1`), the
pointwise domination with the coefficient `1 - K r/K 1` is **false** at the lattice point
`e₁` of distance `1/2`: the left side is `8/3 - 1/3 = 7/3 > 0` while the coefficient is
`1 - K 1/K 1 = 0`. -/
theorem flat_coefficient_bound_false :
    ¬ ((fun r : ℝ => r ^ (-(2 : ℝ) - 1) / ((2 : ℝ) + 1)) (1 / 2)
        - (fun r : ℝ => r ^ (-(2 : ℝ) - 1) / ((2 : ℝ) + 1)) 1
      ≤ (1 - (fun r : ℝ => r ^ (-(2 : ℝ) - 1) / ((2 : ℝ) + 1)) 1
            / (fun r : ℝ => r ^ (-(2 : ℝ) - 1) / ((2 : ℝ) + 1)) 1)
        * (fun r : ℝ => r ^ (-(2 : ℝ) - 1) / ((2 : ℝ) + 1)) (1 / 2)) := by
  intro h
  norm_num [Real.rpow_neg] at h

/-- The minimum-positive-lattice-distance coefficient at this point,
`ε(1) = K 1/K(1/2) = 1/8`, gives `(1 - 1/8)·K(1/2) = K(1/2) - K 1`.
This accords with the source's `K r/K(t₀)` ratio when `t₀ = 1/2`; it is not a
`K r/K(0⁺)` ratio, which is degenerate for the power law. -/
theorem flat_source_epsilon_works :
    (1 - (fun r : ℝ => r ^ (-(2 : ℝ) - 1) / ((2 : ℝ) + 1)) 1
          / (fun r : ℝ => r ^ (-(2 : ℝ) - 1) / ((2 : ℝ) + 1)) (1 / 2))
        * (fun r : ℝ => r ^ (-(2 : ℝ) - 1) / ((2 : ℝ) + 1)) (1 / 2)
      = (fun r : ℝ => r ^ (-(2 : ℝ) - 1) / ((2 : ℝ) + 1)) (1 / 2)
        - (fun r : ℝ => r ^ (-(2 : ℝ) - 1) / ((2 : ℝ) + 1)) 1 := by
  norm_num [Real.rpow_neg]


#print axioms PercLib.CriticalLRP.Orchestration.Flat.flatSourceNorm
#print axioms PercLib.CriticalLRP.Orchestration.Flat.flat_dist_e1
#print axioms PercLib.CriticalLRP.Orchestration.Flat.flat_coefficient_bound_false
#print axioms PercLib.CriticalLRP.Orchestration.Flat.flat_source_epsilon_works

end PercLib.CriticalLRP.Orchestration.Flat
