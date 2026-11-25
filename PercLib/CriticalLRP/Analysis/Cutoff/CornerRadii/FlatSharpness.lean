/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
-/
module

public import PercLib.CriticalLRP.Analysis.Cutoff.CornerRadii
public import PercLib.CriticalLRP.Orchestration.FlatNorm.Defs

/-!
# Sharpness of local finiteness of the corner set

The landed flat normalized norm `Flat.flatSourceNorm` (a genuine `SourceNormData 2` whose unit
ball is the box `[-2,2] × [-1/8,1/8]`) puts a nonzero lattice point at distance `1/2`.  This
file draws the two consequences that delimit the attained-radius theorem:

* the corner set of an admissible norm is **not** globally finite in general: for the flat norm
  every half-integer `m/2` with `m ≥ 1` is attained, so the corner set is infinite;
* consequently `finite_attainedRadii_inter_Icc` (local finiteness in a bounded window, with the
  degree-`d` count bound) is the strongest global statement available, and no argument may
  assume a separation `M.S.dist x 0 ≥ 1` or a finite global corner set.

Both are stated for the actual `SourceNormData` instance, so they are counterexamples in the
sense of the campaign: an admissible norm, not a hypothetical one.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Asymptotics

namespace PercLib.CriticalLRP.Orchestration

/-- The flat normalized norm puts the nonzero lattice vector `e₁ = (1,0)` at distance `1/2`:
the norm does not separate lattice points from the origin. -/
theorem flat_dist_e1 : Flat.flatSourceNorm.dist Flat.e1 0 = 1 / 2 := by
  change Flat.flatNorm (toVec Flat.e1) = 1 / 2
  simp [Flat.flatNorm, Flat.e1, toVec]

/-- Moreover `1/2` is an attained radius of the flat norm, so the corner set contains a radius
below any positive separation threshold. -/
theorem flat_half_mem_attainedRadii : (1 / 2 : ℝ) ∈ Flat.flatSourceNorm.attainedRadii :=
  ⟨Flat.e1, by simp [Flat.e1], flat_dist_e1⟩

/-- Scaling the vector `e₁` by a natural number scales the flat radius by the same factor. -/
theorem flat_dist_nsmul_e1 (m : ℕ) :
    Flat.flatSourceNorm.dist (m • Flat.e1) 0 = (m : ℝ) / 2 := by
  have htv : toVec ((m : ℕ) • Flat.e1) = (m : ℝ) • toVec Flat.e1 := by
    funext i
    simp [toVec]
  have hbase : Flat.flatSourceNorm.ρ (toVec Flat.e1) = 1 / 2 := flat_dist_e1
  rw [SourceNormData.dist_zero_right, htv,
    Flat.flatSourceNorm.ρ_smul (m : ℝ) (toVec Flat.e1), hbase, abs_of_nonneg (Nat.cast_nonneg m)]
  ring

/-- Every half-integer `m/2` with `m ≥ 1` is an attained radius of the flat norm. -/
theorem flat_nat_half_mem_attainedRadii (m : ℕ) (hm : 1 ≤ m) :
    ((m : ℝ) / 2) ∈ Flat.flatSourceNorm.attainedRadii := by
  refine ⟨m • Flat.e1, ?_, flat_dist_nsmul_e1 m⟩
  intro hc
  have h0 : (m : ℤ) = 0 := by
    simpa [Flat.e1] using congrFun hc (0 : Fin 2)
  have hm0 : (m : ℤ) ≠ 0 := by
    have hne : m ≠ 0 := Nat.one_le_iff_ne_zero.mp hm
    exact_mod_cast hne
  exact hm0 h0

/-- **Global finiteness fails.** The corner set of the flat normalized norm is infinite, so the
local statement `finite_attainedRadii_inter_Icc` cannot be strengthened to a global one. -/
theorem flat_attainedRadii_infinite : Flat.flatSourceNorm.attainedRadii.Infinite := by
  have hinj : Function.Injective (fun m : ℕ => ((m + 1 : ℕ) : ℝ) / 2) := by
    intro a b hab
    simp only at hab
    have hcast : ((a + 1 : ℕ) : ℝ) = ((b + 1 : ℕ) : ℝ) := by linarith
    exact Nat.succ.inj (Nat.cast_injective hcast)
  refine (Set.infinite_range_of_injective hinj).mono ?_
  rintro r ⟨m, rfl⟩
  exact flat_nat_half_mem_attainedRadii (m + 1) (by omega)

/-- The corner set of the flat norm is unbounded: it is not merely infinite but accumulates only
at infinity, exactly as local finiteness allows. -/
theorem flat_attainedRadii_unbounded : ∀ R : ℝ, ∃ r ∈ Flat.flatSourceNorm.attainedRadii, R < r := by
  intro R
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * R)
  refine ⟨((m + 1 : ℕ) : ℝ) / 2, flat_nat_half_mem_attainedRadii (m + 1) (by omega), ?_⟩
  push_cast
  linarith

end PercLib.CriticalLRP.Orchestration
