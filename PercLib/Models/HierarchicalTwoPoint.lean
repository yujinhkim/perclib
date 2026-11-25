/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

New for this project (issue 214, Q-43, item 3). No upstream proof is copied.
-/
module

public import PercLib.Models.Hierarchical
public import PercLib.Percolation.Bond.ConvolutionBound

/-!
# The two-point function on the hierarchical lattice at small intensity

On `ℕ →₀ (Fin d → ZMod L)` with the radial kernel `J s(x, y) = C r^{h(y - x)}`, `r ≤ 1`, where
`h(z) = z.support.sup Nat.succ` is the level, the ultrametric inequality for `h` gives the
convolution bound `∑_z J(x, z) J(z, y) ≤ 2 M J(x, y)` for `x ≠ y`, where
`M = ∑_{z ≠ 0} C r^{h(z)}`. With the convolution bound of `ConvolutionBound.lean`,
`τ_β(x, y) ≤ β J(x, y) (1 - 2βM)⁻¹ (1 - βM)⁻¹`: at small `β` the two-point function decays like
the kernel. The ultrametric inequality is proved inline here (the general geometry is Q-40).
This is a subcritical bound and says nothing at criticality.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal
open Classical
open PercLib.Percolation.Bond

namespace PercLib.Models

variable {d L : ℕ} [NeZero L]

/-- **Two-point bound on the hierarchical lattice.** -/
theorem tau_intensity_le_hierarchical (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0) (C r : ℝ≥0)
    (hJ : ∀ x y, J s(x, y) = C * r ^ ((y - x).support.sup Nat.succ)) (hr : r ≤ 1) (β : ℝ≥0)
    {x y : ℕ →₀ (Fin d → ZMod L)} (hxy : x ≠ y) :
    tau (intensityProfile J β) x y ≤
      (β : ℝ≥0∞) * J s(x, y) *
        ((1 - 2 * (β : ℝ≥0∞) * ∑' z : ℕ →₀ (Fin d → ZMod L),
            (if z = 0 then 0 else ((C * r ^ (z.support.sup Nat.succ) : ℝ≥0) : ℝ≥0∞)))⁻¹ *
          (1 - (β : ℝ≥0∞) * ∑' z : ℕ →₀ (Fin d → ZMod L),
            (if z = 0 then 0 else ((C * r ^ (z.support.sup Nat.succ) : ℝ≥0) : ℝ≥0∞)))⁻¹) := by
  set k : (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0∞ := fun z =>
    ((C * r ^ (z.support.sup Nat.succ) : ℝ≥0) : ℝ≥0∞) with hk
  set M := ∑' z : ℕ →₀ (Fin d → ZMod L), (if z = 0 then 0 else k z) with hM
  set a : (ℕ →₀ (Fin d → ZMod L)) → (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0∞ :=
    fun v w => (β : ℝ≥0∞) * k (w - v) with ha
  -- The level is an ultrametric norm.
  have hadd : ∀ u w : ℕ →₀ (Fin d → ZMod L),
      (u + w).support.sup Nat.succ ≤ max (u.support.sup Nat.succ) (w.support.sup Nat.succ) := by
    intro u w
    rw [← Finset.sup_union]
    exact Finset.sup_mono Finsupp.support_add
  have hultra : ∀ u v w : ℕ →₀ (Fin d → ZMod L), (w - u).support.sup Nat.succ ≤
      max ((v - u).support.sup Nat.succ) ((w - v).support.sup Nat.succ) := by
    intro u v w
    have : (v - u) + (w - v) = w - u := by abel
    rw [← this]
    exact hadd _ _
  have hsymm : ∀ u v : ℕ →₀ (Fin d → ZMod L),
      (v - u).support.sup Nat.succ = (u - v).support.sup Nat.succ := fun u v => by
    rw [← neg_sub u v, Finsupp.support_neg]
  -- Row and column sums.
  have hrow_eq : ∀ v, ∑' w, offDiagonal a v w = (β : ℝ≥0∞) * M := by
    intro v
    rw [← (Equiv.addLeft v).tsum_eq, hM, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun z => ?_
    simp only [Equiv.coe_addLeft, offDiagonal_apply, ha, add_eq_left, add_sub_cancel_left,
      mul_ite, mul_zero]
  have hcol_eq : ∀ v, ∑' w, offDiagonal a w v = (β : ℝ≥0∞) * M := by
    intro v
    rw [← hrow_eq v]
    refine tsum_congr fun w => ?_
    simp only [offDiagonal_apply, ha, hk, hsymm w v, eq_comm]
  -- The convolution bound, termwise.
  have hterm : ∀ x y z, offDiagonal a x z * offDiagonal a z y ≤
      a x y * (offDiagonal a z y + offDiagonal a x z) := by
    intro x y z
    by_cases hzx : z = x
    · simp [hzx, offDiagonal_apply]
    by_cases hzy : z = y
    · simp [hzy, offDiagonal_apply]
    have e1 : offDiagonal a x z = a x z := by simp [offDiagonal_apply, hzx]
    have e2 : offDiagonal a z y = a z y := by simp [offDiagonal_apply, Ne.symm hzy]
    rw [e1, e2, mul_add]
    by_cases hlev : (y - x).support.sup Nat.succ ≤ (z - x).support.sup Nat.succ
    · have hp : r ^ (z - x).support.sup Nat.succ ≤ r ^ (y - x).support.sup Nat.succ :=
        pow_le_pow_of_le_one (by positivity) hr hlev
      have hk' : k (z - x) ≤ k (y - x) := by
        simp only [hk]
        exact_mod_cast mul_le_mul_of_nonneg_left hp (by positivity)
      refine le_add_right ?_
      simp only [ha]
      gcongr
    · refine le_add_left (le_of_eq ?_)
      have h1 := hultra x z y
      have h2 := hultra z x y
      rw [hsymm z x] at h2
      have heq : (y - z).support.sup Nat.succ = (y - x).support.sup Nat.succ := by
        rw [not_le] at hlev
        apply le_antisymm
        · exact h2.trans (max_le hlev.le le_rfl)
        · rcases le_max_iff.1 h1 with h | h
          · exact absurd h (not_le.2 hlev)
          · exact h
      simp only [ha, hk, heq]
      ring
  have hconv : ∀ u w, u ≠ w → ∑' z, offDiagonal a u z * offDiagonal a z w ≤
      (2 * (β : ℝ≥0∞) * M) * a u w := by
    intro u w _
    calc ∑' z, offDiagonal a u z * offDiagonal a z w
        ≤ ∑' z, a u w * (offDiagonal a z w + offDiagonal a u z) :=
          ENNReal.tsum_le_tsum fun z => hterm u w z
      _ = a u w * ((β : ℝ≥0∞) * M + (β : ℝ≥0∞) * M) := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_add, hcol_eq, hrow_eq]
      _ = (2 * (β : ℝ≥0∞) * M) * a u w := by ring
  have hqa : ∀ v w, v ≠ w →
      (unitInterval.toNNReal (intensityProfile J β s(v, w)) : ℝ≥0∞) ≤ a v w := by
    intro v w _
    have := intensityProfile_toNNReal_le J β s(v, w)
    rw [hJ] at this
    simp only [ha, hk]
    exact_mod_cast this
  have hτ := tau_le_of_convolution (intensityProfile J β) a ((β : ℝ≥0∞) * M) (2 * (β : ℝ≥0∞) * M)
    hqa (fun v => (hrow_eq v).le) (fun u w huw => (hconv u w huw).trans_eq (by ring)) hxy
  refine hτ.trans_eq ?_
  simp only [ha, hk, hJ]

/-! ### Non-vacuity -/

omit [NeZero L] in
/-- `d = 1`, `L = 2`, the radial kernel `4^(-level)` (`C = 1`, `r = 1/4 ≤ 1`). -/
example (x y : ℕ →₀ (Fin 1 → ZMod 2)) (hxy : x ≠ y) (β : ℝ≥0) :
    ∃ J : Sym2 (ℕ →₀ (Fin 1 → ZMod 2)) → ℝ≥0, J s(x, y) ≠ 0 ∧
      tau (intensityProfile J β) x y ≤
        (β : ℝ≥0∞) * J s(x, y) *
          ((1 - 2 * (β : ℝ≥0∞) * ∑' z : ℕ →₀ (Fin 1 → ZMod 2),
              (if z = 0 then 0 else ((1 * (1 / 4) ^ (z.support.sup Nat.succ) : ℝ≥0) : ℝ≥0∞)))⁻¹ *
            (1 - (β : ℝ≥0∞) * ∑' z : ℕ →₀ (Fin 1 → ZMod 2),
              (if z = 0 then 0 else ((1 * (1 / 4) ^ (z.support.sup Nat.succ) : ℝ≥0) : ℝ≥0∞)))⁻¹) := by
  obtain ⟨J, hJ⟩ := exists_hierarchical_kernel (d := 1) (L := 2) 1 (1 / 4)
  refine ⟨J, by rw [hJ]; positivity, tau_intensity_le_hierarchical J 1 (1 / 4) hJ
    (NNReal.coe_le_coe.1 (by norm_num)) β hxy⟩

end PercLib.Models

end
