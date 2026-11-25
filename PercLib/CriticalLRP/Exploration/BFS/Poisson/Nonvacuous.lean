/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Non-vacuity of the row-sum hypothesis and of the one-step conclusion.

Direction 1 (swarm `smwpbvro2`, member m1).  The whole package is conditional on
`UniformRowBound p M` with a real budget `M`.  These are the crude sanity checks that the
hypothesis is satisfiable — including in the intended high-temperature range `M < 1` — so that
the exponential bound `exp ((t-1) M)` is not vacuous and the factor is not accidentally `0`.
-/
module

public import PercLib.CriticalLRP.Exploration.BFS.Poisson.Assemble
public import PercLib.Probability.Exploration.Envelope

set_option autoImplicit false

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Percolation.Bond Finset
open PercLib.Probability
open PercLib.Probability.AdaptedReveal
open scoped ENNReal BigOperators

namespace PercLib.CriticalLRP.Exploration.BFS

variable {V : Type*}

/-- The identically-zero intensity field satisfies every nonnegative row-sum budget; in
particular `UniformRowBound` is satisfiable with `0 < M < 1`. -/
theorem uniformRowBound_zero {M : ℝ} (hM : 0 ≤ M) :
    UniformRowBound (fun _ : Sym2 V => (0 : unitInterval)) M := by
  intro x t _
  have hterm : ∀ y : V, (((fun _ : Sym2 V => (0 : unitInterval)) (s(x, y))) : ℝ) = 0 :=
    fun y => rfl
  rw [Finset.sum_congr rfl (fun y _ => hterm y)]
  simpa using hM

/-- The budget `exp ((t-1) M)` in the one-step estimate is strictly positive, so the state
weight `(exp ((t-1) M)) ^ |T|` never vanishes. -/
theorem ofReal_exp_budget_pos (t : ℝ≥0∞) (M : ℝ) (n : ℕ) :
    0 < (ENNReal.ofReal (Real.exp ((t.toReal - 1) * M))) ^ n := by
  rw [← ofReal_exp_card_mul]
  exact ENNReal.ofReal_pos.mpr (Real.exp_pos _)

/-- The `p = 1` endpoint: the one-coordinate factor is exactly `t`, so the finite product over
`S` of the factor at `p ≡ 1` is `t ^ |S|` and the exponential bound is attained only through
`∑_{e ∈ S} p_e = |S|`. -/
theorem prod_pgfFactor_one (t : ℝ≥0∞) (S : Finset (Sym2 V)) :
    ∏ _e ∈ S, (t * (unitInterval.toNNReal (1 : unitInterval) : ℝ≥0∞)
        + (1 - (unitInterval.toNNReal (1 : unitInterval) : ℝ≥0∞))) = t ^ S.card := by
  have h1 : (unitInterval.toNNReal (1 : unitInterval) : ℝ≥0∞) = 1 := by
    rw [ExplorationPoisson.coe_toNNReal_ennreal]
    simp
  rw [Finset.prod_congr rfl (fun e _ => by rw [h1, mul_one, tsub_self, add_zero]),
    Finset.prod_const]

end PercLib.CriticalLRP.Exploration.BFS
