/-
Accepted from Ultramath `smwzg77c3`, member `m1`, independently rebuilt.
Production integration based on commit `81c6038182e9a883ffcd3d870aed7cd4829649d4`.
Original direction `d1`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The `q = 0`, `p = 3` tree-diagram atlas: reductions and evaluated constants

Each shape of `Defs.lean` is a product of seven kernel factors (the `2p + 2q + 1 = 7` edges of
Lemma I.4.17) summed over its three labels and three internal vertices.  `peel_labels` performs the
label summation (`χ` per label), `chain_two/three/four` identify the tree-path sum with the
`ℓ`-fold kernel power, and `atlas_le` assembles the four shape evaluations into

  `atlas ≤ 3χ⁵k² + 6χ⁴k³ + 6χ³k⁴`.

`starMoment_le_three_term` transfers this to the source object `I417Gen.starMoment` (the `q = 0`
moment gap of Lemma I.4.17 at `p = 3`) given the four-label tree-graph input, and
the two-term form of the printed lemma needs, on top of this, the `ℓ = 2` absorption
`χ k² ≤ c k³`, which the printed proof supplies only for `q ≥ 1` via its marked path.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.QZeroAtlas.Defs

/-! # Reductions and evaluated constants for the `q = 0` atlas -/

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.QZeroAtlas

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-! ## Summing out the three labels -/

/-- Summing out the three labels: each label carries exactly one kernel factor, so the sum is at
most `χ³` times the remaining (label-free) factor. -/
theorem peel_labels (D : KernelData V) (a1 a2 a3 : V) (C : ℝ≥0∞) :
    (∑' x1, ∑' x2, ∑' x3, D.k a3 x3 * (D.k a2 x2 * (D.k a1 x1 * C)))
      ≤ D.χ * (D.χ * (D.χ * C)) := by
  have s3 : ∀ x1 x2, (∑' x3, D.k a3 x3 * (D.k a2 x2 * (D.k a1 x1 * C)))
      ≤ D.χ * (D.k a2 x2 * (D.k a1 x1 * C)) := by
    intro x1 x2
    rw [ENNReal.tsum_mul_right]
    exact mul_le_mul_left (D.row a3) _
  have s2 : ∀ x1, (∑' x2, ∑' x3, D.k a3 x3 * (D.k a2 x2 * (D.k a1 x1 * C)))
      ≤ D.χ * (D.χ * (D.k a1 x1 * C)) := by
    intro x1
    calc (∑' x2, ∑' x3, D.k a3 x3 * (D.k a2 x2 * (D.k a1 x1 * C)))
        ≤ ∑' x2, D.χ * (D.k a2 x2 * (D.k a1 x1 * C)) := ENNReal.tsum_le_tsum (s3 x1)
      _ = D.χ * ((∑' x2, D.k a2 x2) * (D.k a1 x1 * C)) := by
            rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
      _ ≤ D.χ * (D.χ * (D.k a1 x1 * C)) :=
            mul_le_mul_right (mul_le_mul_left (D.row a2) (D.k a1 x1 * C)) D.χ
  calc (∑' x1, ∑' x2, ∑' x3, D.k a3 x3 * (D.k a2 x2 * (D.k a1 x1 * C)))
      ≤ ∑' x1, D.χ * (D.χ * (D.k a1 x1 * C)) := ENNReal.tsum_le_tsum s2
    _ = D.χ * (D.χ * ((∑' x1, D.k a1 x1) * C)) := by
        simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
    _ ≤ D.χ * (D.χ * (D.χ * C)) :=
        mul_le_mul_right (mul_le_mul_right (mul_le_mul_left (D.row a1) C) D.χ) D.χ

/-! ## The chain sums -/

/-- The `2`-step chain sum is the twofold kernel power. -/
theorem chain_two (D : KernelData V) (v y : V) :
    (∑' w1, D.k v w1 * D.k w1 y) = kpow D.k 2 v y := (kpow_two D.k v y).symm

/-- The `3`-step chain sum is the threefold kernel power. -/
theorem chain_three (D : KernelData V) (v y : V) :
    (∑' w1, ∑' w2, D.k v w1 * (D.k w1 w2 * D.k w2 y)) = kpow D.k 3 v y := by
  rw [kpow_three]
  refine tsum_congr fun w1 => ?_
  rw [kpow_two (k := D.k) w1 y, ← ENNReal.tsum_mul_left]

/-- The `4`-step chain sum is the fourfold kernel power. -/
theorem chain_four (D : KernelData V) (v y : V) :
    (∑' w1, ∑' w2, ∑' w3, D.k v w1 * (D.k w1 w2 * (D.k w2 w3 * D.k w3 y)))
      = kpow D.k 4 v y := by
  rw [kpow_four]
  refine tsum_congr fun w1 => ?_
  rw [kpow_three (k := D.k) w1 y, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun w2 => ?_
  rw [kpow_two (k := D.k) w2 y, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]

/-! ## The four shape bounds and the assembly

The four shape evaluations

  `shapeFour ≤ χ³ k⁴`, `shapeThreeA ≤ χ⁴ k³`, `shapeThreeB ≤ χ⁴ k³`, `shapeTwo ≤ χ⁵ k²`

are the same computation (`peel_labels`, then one kernel row sum per off-path vertex or label, then
`chain_*` for the tree path).  They enter the assembly as the explicit hypotheses `h4`, `h3A`,
`h3B`, `h2`, so that the residual of this file is exactly named. -/

/-- The atlas is bounded by the three-term weight `3χ⁵k² + 6χ⁴k³ + 6χ³k⁴`, from the four shape
bounds. -/
theorem atlas_le (D : KernelData V) (v y : V)
    (h2 : shapeTwo D v y ≤ D.χ * (D.χ * (D.χ * (D.χ * (D.χ * kpow D.k 2 v y)))))
    (h3A : shapeThreeA D v y ≤ D.χ * (D.χ * (D.χ * (D.χ * kpow D.k 3 v y))))
    (h3B : shapeThreeB D v y ≤ D.χ * (D.χ * (D.χ * (D.χ * kpow D.k 3 v y))))
    (h4 : shapeFour D v y ≤ D.χ * (D.χ * (D.χ * kpow D.k 4 v y))) :
    atlas D v y ≤ 3 * (D.χ * (D.χ * (D.χ * (D.χ * (D.χ * kpow D.k 2 v y)))))
      + 6 * (D.χ * (D.χ * (D.χ * (D.χ * kpow D.k 3 v y))))
      + 6 * (D.χ * (D.χ * (D.χ * kpow D.k 4 v y))) := by
  have hsum : (3 * shapeTwo D v y + 3 * shapeThreeA D v y + 3 * shapeThreeB D v y
      + 6 * shapeFour D v y)
      ≤ 3 * (D.χ * (D.χ * (D.χ * (D.χ * (D.χ * kpow D.k 2 v y)))))
        + 3 * (D.χ * (D.χ * (D.χ * (D.χ * kpow D.k 3 v y))))
        + 3 * (D.χ * (D.χ * (D.χ * (D.χ * kpow D.k 3 v y))))
        + 6 * (D.χ * (D.χ * (D.χ * kpow D.k 4 v y))) := by
    refine add_le_add (add_le_add (add_le_add ?_ ?_) ?_) ?_
    · exact mul_le_mul_right h2 3
    · exact mul_le_mul_right h3A 3
    · exact mul_le_mul_right h3B 3
    · exact mul_le_mul_right h4 6
  exact hsum.trans (le_of_eq (by ring))

/-- **The honest `q = 0`, `p = 3` star bound.**  `I417Gen.starMoment π v y 3 = E[|K_v|³ 1(v ↔ y)]`
is bounded by the evaluated atlas, given the four-label tree-graph input `hatlas` (the `q = 0`
instance of (I.2.2), i.e. the sum over the fifteen `atlasDiagrams`). -/
theorem starMoment_le_three_term (π : Sym2 V → unitInterval) (D : KernelData V) (v y : V)
    (hatlas : I417Gen.starMoment π v y 3 ≤ atlas D v y)
    (h2 : shapeTwo D v y ≤ D.χ * (D.χ * (D.χ * (D.χ * (D.χ * kpow D.k 2 v y)))))
    (h3A : shapeThreeA D v y ≤ D.χ * (D.χ * (D.χ * (D.χ * kpow D.k 3 v y))))
    (h3B : shapeThreeB D v y ≤ D.χ * (D.χ * (D.χ * (D.χ * kpow D.k 3 v y))))
    (h4 : shapeFour D v y ≤ D.χ * (D.χ * (D.χ * kpow D.k 4 v y))) :
    I417Gen.starMoment π v y 3 ≤
      3 * (D.χ * (D.χ * (D.χ * (D.χ * (D.χ * kpow D.k 2 v y)))))
      + 6 * (D.χ * (D.χ * (D.χ * (D.χ * kpow D.k 3 v y))))
      + 6 * (D.χ * (D.χ * (D.χ * kpow D.k 4 v y))) :=
  hatlas.trans (atlas_le D v y h2 h3A h3B h4)

/-! ## Machine-checked combinatorics of the fifteen diagrams -/

/-- The atlas has fifteen members. -/
theorem atlasDiagrams_length : atlasDiagrams.length = 15 := by decide

/-- Every diagram of the atlas has seven edges (the `2p + 2q + 1 = 7` of Lemma I.4.17 at
`p = 3`, `q = 0`). -/
theorem atlasDiagrams_edges : (atlasDiagrams.map List.length).all (· = 7) = true := by decide

/-- `y` is not adjacent to the root in any of the fifteen diagrams (the tree path from `x` to `y`
has length at least two). -/
theorem atlasDiagrams_path_ge_two : (atlasDiagrams.map pathLen).all (fun l => 2 ≤ l) = true := by
  decide

/-- The path lengths of the fifteen diagrams take only the values `2, 3, 4`. -/
theorem atlasDiagrams_path_values :
    (atlasDiagrams.map pathLen).all (fun l => l = 2 ∨ l = 3 ∨ l = 4) = true := by decide

/-- The `ℓ = 2` class has three members. -/
theorem atlasDiagrams_count_two : (atlasDiagrams.map pathLen).count 2 = 3 := by decide

/-- The `ℓ = 3` class has six members. -/
theorem atlasDiagrams_count_three : (atlasDiagrams.map pathLen).count 3 = 6 := by decide

/-- The `ℓ = 4` class has six members. -/
theorem atlasDiagrams_count_four : (atlasDiagrams.map pathLen).count 4 = 6 := by decide

end PercLib.CriticalLRP.QZeroAtlas


set_option linter.hashCommand false in
-- Audit: no axioms beyond the three standard ones.
#print axioms PercLib.CriticalLRP.QZeroAtlas.peel_labels
#print axioms PercLib.CriticalLRP.QZeroAtlas.chain_four
#print axioms PercLib.CriticalLRP.QZeroAtlas.atlas_le
#print axioms PercLib.CriticalLRP.QZeroAtlas.starMoment_le_three_term
#print axioms PercLib.CriticalLRP.QZeroAtlas.atlasDiagrams_count_two
#print axioms PercLib.CriticalLRP.QZeroAtlas.atlasDiagrams_count_three
#print axioms PercLib.CriticalLRP.QZeroAtlas.atlasDiagrams_count_four
