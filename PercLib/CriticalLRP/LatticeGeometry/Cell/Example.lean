/-
# A concrete normalized norm for Lemma I.4.6

Twice the canonical coordinate supremum norm has the cube `[-1/2,1/2]^d` as
its unit ball, whose Lebesgue volume is one. This gives a non-vacuous model in
every dimension, independent of any unproved normalization claim.
-/
module

public import PercLib.CriticalLRP.LatticeGeometry.Cell.Asymptotic

set_option autoImplicit false

@[expose] public section

namespace PercLib.CriticalLRP.LatticeGeometry

open Filter MeasureTheory

open scoped Asymptotics ENNReal Topology

/-- Twice the canonical sup norm has unit-volume unit ball. -/
theorem volume_two_mul_normBall_one (d : ℕ) :
    volume {x : Fin d → ℝ | 2 * ‖x‖ ≤ 1} = 1 := by
  have hset : {x : Fin d → ℝ | 2 * ‖x‖ ≤ 1} =
      Metric.closedBall (0 : Fin d → ℝ) (1 / 2) := by
    ext x
    rw [Set.mem_ofPred_eq, Metric.mem_closedBall, dist_zero_right]
    constructor <;> intro h <;> linarith
  rw [hset, Real.volume_pi_closedBall (0 : Fin d → ℝ) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  simp

/-- **Lemma I.4.6 at `rho = 2 * ‖x‖`.** This is an explicit non-vacuous
normalized norm instance in every dimension. -/
theorem lemma_I_4_6_two_mul_norm (d : ℕ) :
    (fun r : ℝ =>
      (Set.ncard {z : Fin d → ℤ | 2 * ‖(fun j => (z j : ℝ))‖ ≤ r} : ℝ) - r ^ d) =O[atTop]
      (fun r => r ^ (d - 1)) := by
  apply lemma_I_4_6 (ρ := fun x : Fin d → ℝ => 2 * ‖x‖)
  · intro x y
    calc
      2 * ‖x + y‖ ≤ 2 * (‖x‖ + ‖y‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le x y) (by norm_num)
      _ = 2 * ‖x‖ + 2 * ‖y‖ := by ring
  · intro x
    rw [norm_neg]
  · exact continuous_const.mul continuous_norm
  · intro c x
    rw [norm_smul, Real.norm_eq_abs]
    ring
  · exact volume_two_mul_normBall_one d

end PercLib.CriticalLRP.LatticeGeometry
