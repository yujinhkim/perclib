/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Attained cutoff radii of a normalized source norm (candidate definitions)

For a normalized source norm `S` on `Fin d → ℤ`, a real number `r` is called an *attained
radius* when `r = S.dist x 0` for some nonzero lattice point `x`.  These are precisely the
radii at which a radial cutoff profile `s ↦ cutoffProfile K r s` may jump, so any off-corner
statement about a cutoff mass, a cutoff kernel or a cutoff moment has to quantify over the
complement of this set.

The set is attached to the norm (`SourceNormData.attainedRadii`) and re-exported for the
source model (`SourceModelData.attainedRadii`).

Nothing in this file asserts that the set is finite or locally finite; that, together with a
cardinality bound, is proved in `CornerRadii/Finiteness.lean`.
-/
module

public import PercLib.CriticalLRP.Analysis.BallRatioLogError
public import PercLib.CriticalLRP.Analysis.Cutoff.IntervalAC.Defs

/-!
# Attained cutoff radii of a normalized source norm (candidate definitions)

For a normalized source norm `S` on `Fin d → ℤ`, a real number `r` is called an *attained
radius* when `r = S.dist x 0` for some nonzero lattice point `x`.  These are precisely the
radii at which a radial cutoff profile `s ↦ cutoffProfile K r s` may jump, so any off-corner
statement about a cutoff mass, a cutoff kernel or a cutoff moment has to quantify over the
complement of this set.

The set is attached to the norm (`SourceNormData.attainedRadii`) and re-exported for the
source model (`SourceModelData.attainedRadii`).

Nothing in this file asserts that the set is finite or locally finite; that, together with a
cardinality bound, is proved in `CornerRadii/Finiteness.lean`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace PercLib.CriticalLRP.Orchestration

/-- The radii attained by the norm at nonzero lattice vectors: `r` is attained when
`r = S.dist x 0` for some `x ≠ 0`. -/
def SourceNormData.attainedRadii {d : ℕ} (S : SourceNormData d) : Set ℝ :=
  {r : ℝ | ∃ x : Fin d → ℤ, x ≠ 0 ∧ S.dist x 0 = r}

/-- The radii attained by the source model's normalized norm. -/
def SourceModelData.attainedRadii (M : SourceModelData) : Set ℝ := M.S.attainedRadii

theorem SourceNormData.mem_attainedRadii {d : ℕ} {S : SourceNormData d} {r : ℝ} :
    r ∈ S.attainedRadii ↔ ∃ x : Fin d → ℤ, x ≠ 0 ∧ S.dist x 0 = r :=
  Iff.rfl

theorem SourceModelData.mem_attainedRadii {M : SourceModelData} {r : ℝ} :
    r ∈ M.attainedRadii ↔ ∃ x : M.V, x ≠ 0 ∧ M.S.dist x 0 = r :=
  Iff.rfl

/-- The radius of a lattice vector is the distance from the origin to that vector.  This is
the bridge between `M.S.dist x 0` and the lattice balls `M.ball r`. -/
theorem SourceNormData.dist_zero_right {d : ℕ} (S : SourceNormData d) (x : Fin d → ℤ) :
    S.dist x 0 = S.ρ (toVec x) := by
  simp [SourceNormData.dist]

/-- Lattice distances are shift-invariant: the distance from `x` to `y` is the radius of the
lattice vector `y - x`. -/
theorem SourceNormData.dist_eq_dist_shift {d : ℕ} (S : SourceNormData d)
    (x y : Fin d → ℤ) : S.dist x y = S.dist (y - x) 0 := by
  rw [SourceNormData.dist, SourceNormData.dist, sub_zero]
  have h : toVec (x - y) = -toVec (y - x) := toVec_sub_eq_neg y x
  rw [h, S.ρ_neg]

theorem SourceModelData.dist_eq_dist_shift (M : SourceModelData) (x y : M.V) :
    M.S.dist x y = M.S.dist (y - x) 0 :=
  M.S.dist_eq_dist_shift x y

/-- Every pairwise distance of two distinct lattice points is an attained radius. -/
theorem SourceNormData.mem_attainedRadii_of_dist {d : ℕ} (S : SourceNormData d) {x y : Fin d → ℤ}
    (h : x ≠ y) : S.dist x y ∈ S.attainedRadii := by
  refine ⟨y - x, ?_, (S.dist_eq_dist_shift x y).symm⟩
  intro hc
  exact h (sub_eq_zero.mp hc).symm

/-- The two readings of "radius attained on a nonzero lattice point" agree: between distinct
lattice points of the lattice and from the origin to a nonzero lattice vector. -/
theorem SourceNormData.attainedRadii_eq_pairwiseDist {d : ℕ} (S : SourceNormData d) :
    S.attainedRadii = {r : ℝ | ∃ x y : Fin d → ℤ, x ≠ y ∧ S.dist x y = r} := by
  ext r
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, 0, hx, rfl⟩
  · rintro ⟨x, y, hxy, rfl⟩
    rw [S.dist_comm]
    exact S.mem_attainedRadii_of_dist hxy.symm

/-- The normalized attained radii are exactly the pairwise corner radii used by
`Analysis.Cutoff.IntervalAC`. -/
theorem SourceModelData.attainedRadii_eq_cornerRadii (M : SourceModelData) :
    M.attainedRadii = M.cornerRadii := by
  change M.S.attainedRadii = M.cornerRadii
  rw [M.S.attainedRadii_eq_pairwiseDist]
  rfl

/-- Attained radii are strictly positive. -/
theorem SourceNormData.attainedRadii_pos {d : ℕ} {S : SourceNormData d} {r : ℝ}
    (hr : r ∈ S.attainedRadii) : 0 < r := by
  obtain ⟨x, hx, rfl⟩ := hr
  exact S.dist_pos hx

theorem SourceModelData.attainedRadii_pos {M : SourceModelData} {r : ℝ}
    (hr : r ∈ M.attainedRadii) : 0 < r :=
  M.S.attainedRadii_pos hr

/-- The origin is not an attained radius: the norm vanishes there. -/
theorem SourceNormData.zero_notMem_attainedRadii {d : ℕ} (S : SourceNormData d) :
    (0 : ℝ) ∉ S.attainedRadii :=
  fun h => (S.attainedRadii_pos h).ne' rfl

theorem SourceModelData.zero_notMem_attainedRadii (M : SourceModelData) :
    (0 : ℝ) ∉ M.attainedRadii :=
  M.S.zero_notMem_attainedRadii

end PercLib.CriticalLRP.Orchestration
