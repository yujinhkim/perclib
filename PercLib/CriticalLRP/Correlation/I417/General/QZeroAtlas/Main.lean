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

/-- Summing out three labels, each carrying one kernel factor, in right-nested form. -/
theorem peel_labels' (D : KernelData V) (a1 a2 a3 : V) (C : ℝ≥0∞) :
    (∑' x1, ∑' x2, ∑' x3, D.k a1 x1 * (D.k a2 x2 * (D.k a3 x3 * C)))
      ≤ D.χ * (D.χ * (D.χ * C)) := by
  have h3 : ∀ x1 x2, (∑' x3, D.k a1 x1 * (D.k a2 x2 * (D.k a3 x3 * C)))
      ≤ D.k a1 x1 * (D.k a2 x2 * (D.χ * C)) := by
    intro x1 x2
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
    exact mul_le_mul_right (mul_le_mul_right (mul_le_mul_left (D.row a3) C) (D.k a2 x2))
      (D.k a1 x1)
  have h2 : ∀ x1, (∑' x2, ∑' x3, D.k a1 x1 * (D.k a2 x2 * (D.k a3 x3 * C)))
      ≤ D.k a1 x1 * (D.χ * (D.χ * C)) := by
    intro x1
    refine le_trans (ENNReal.tsum_le_tsum (h3 x1)) ?_
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
    exact mul_le_mul_right (mul_le_mul_left (D.row a2) (D.χ * C)) (D.k a1 x1)
  refine le_trans (ENNReal.tsum_le_tsum h2) ?_
  rw [ENNReal.tsum_mul_right]
  exact mul_le_mul_left (D.row a1) (D.χ * (D.χ * C))

/-- One off-path vertex attached to `a`, with a constant factor on the left. -/
theorem tsum_mul_k_le (D : KernelData V) (a : V) (g : ℝ≥0∞) :
    (∑' x, g * D.k a x) ≤ g * D.χ := by
  rw [ENNReal.tsum_mul_left]
  exact mul_le_mul_right (D.row a) g

/-- One off-path vertex attached to `a`, in a middle position. -/
theorem tsum_mul_k_mul_le (D : KernelData V) (a : V) (g h : ℝ≥0∞) :
    (∑' x, (g * D.k a x) * h) ≤ (g * D.χ) * h := by
  rw [ENNReal.tsum_mul_right]
  exact mul_le_mul_left (tsum_mul_k_le D a g) h

/-- A two-step chain with a leading constant is the twofold kernel power. -/
theorem tsum_mul_chain_two (D : KernelData V) (a b : V) (g : ℝ≥0∞) :
    (∑' x, g * (D.k a x * D.k x b)) = g * kpow D.k 2 a b := by
  rw [ENNReal.tsum_mul_left, kpow_two]

/-- A three-step chain with a leading constant is the threefold kernel power. -/
theorem tsum_mul_chain_three (D : KernelData V) (a b : V) (g : ℝ≥0∞) :
    (∑' x, g * (D.k a x * kpow D.k 2 x b)) = g * kpow D.k 3 a b := by
  rw [ENNReal.tsum_mul_left, kpow_three]

/-! ## Sharpness: the shape evaluations are equalities for a regular kernel

In the source, `T` is the two-point function of a transitive weighted graph, so the row mass
`∑_z T(x,z)` is the *same* number `E|K| = χ` for every `x`: the hypothesis `hreg` below.  Under it
every peel of the proofs above is an equality, so the four shape evaluations and the whole
three-term atlas are **identities**: `atlas D v y = 3χ⁵T² + 6χ⁴T³ + 6χ³T⁴` exactly.  In
particular the `ℓ = 2` term `3χ⁵ T²` is genuinely present in the atlas with coefficient `3` and is
not an artefact of an inequality; this is what makes the two-term range `3 ≤ ℓ` of the printed
lemma a *separate* input (the absorption `χ k² ≤ c k³`), as m1 recorded. -/

/-- Exact row peel. -/
theorem tsum_mul_k_eq (D : KernelData V) (hreg : ∀ a, (∑' z, D.k a z) = D.χ) (a : V) (g : ℝ≥0∞) :
    (∑' x, g * D.k a x) = g * D.χ := by
  rw [ENNReal.tsum_mul_left, hreg a]

/-- Exact row peel in a middle position. -/
theorem tsum_mul_k_mul_eq (D : KernelData V) (hreg : ∀ a, (∑' z, D.k a z) = D.χ) (a : V)
    (g h : ℝ≥0∞) : (∑' x, (g * D.k a x) * h) = (g * D.χ) * h := by
  rw [ENNReal.tsum_mul_right, tsum_mul_k_eq D hreg a g]

/-- Exact label summation. -/
theorem peel_labels_eq (D : KernelData V) (hreg : ∀ a, (∑' z, D.k a z) = D.χ)
    (a1 a2 a3 : V) (C : ℝ≥0∞) :
    (∑' x1, ∑' x2, ∑' x3, D.k a1 x1 * (D.k a2 x2 * (D.k a3 x3 * C)))
      = D.χ * (D.χ * (D.χ * C)) := by
  have h3 : ∀ x1 x2, (∑' x3, D.k a1 x1 * (D.k a2 x2 * (D.k a3 x3 * C)))
      = D.k a1 x1 * (D.k a2 x2 * (D.χ * C)) := by
    intro x1 x2
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hreg a3]
  have h2 : ∀ x1, (∑' x2, ∑' x3, D.k a1 x1 * (D.k a2 x2 * (D.k a3 x3 * C)))
      = D.k a1 x1 * (D.χ * (D.χ * C)) := by
    intro x1
    rw [show (∑' x2, ∑' x3, D.k a1 x1 * (D.k a2 x2 * (D.k a3 x3 * C)))
        = (∑' x2, D.k a1 x1 * (D.k a2 x2 * (D.χ * C))) from tsum_congr (h3 x1)]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, hreg a2]
  rw [show (∑' x1, ∑' x2, ∑' x3, D.k a1 x1 * (D.k a2 x2 * (D.k a3 x3 * C)))
      = (∑' x1, D.k a1 x1 * (D.χ * (D.χ * C))) from tsum_congr h2]
  rw [ENNReal.tsum_mul_right, hreg a1]

/-- **Sharpness of the `ℓ = 2` evaluation**: for a kernel whose row sums all equal `χ` (the
transitive-graph situation of the source, where `T(x, ·)` has constant mass `E|K|`), the three
off-path row sums of `shapeTwo` are exact, so `shapeTwo = χ⁵ k²` with no loss. -/
theorem shapeTwo_eq_of_regular (D : KernelData V) (hreg : ∀ a, (∑' z, D.k a z) = D.χ) (v y : V) :
    shapeTwo D v y = D.χ * (D.χ * (D.χ * (D.χ * (D.χ * kpow D.k 2 v y)))) := by
  have hlabel : shapeTwo D v y =
      ∑' w1, ∑' w2, ∑' w3,
        D.χ * (D.χ * (D.χ * (D.k v w1 * D.k w1 w2 * D.k w1 y * D.k w2 w3))) := by
    unfold shapeTwo
    refine tsum_congr fun w1 => tsum_congr fun w2 => tsum_congr fun w3 => ?_
    refine Eq.trans ?_ (peel_labels_eq D hreg w2 w3 w3
        (D.k v w1 * D.k w1 w2 * D.k w1 y * D.k w2 w3))
    exact tsum_congr fun x1 => tsum_congr fun x2 => tsum_congr fun x3 => by ring
  have hpull :
      (∑' w1, ∑' w2, ∑' w3,
        D.χ * (D.χ * (D.χ * (D.k v w1 * D.k w1 w2 * D.k w1 y * D.k w2 w3))))
      = D.χ * (D.χ * (D.χ * (∑' w1, ∑' w2, ∑' w3,
          D.k v w1 * D.k w1 w2 * D.k w1 y * D.k w2 w3))) := by
    simp only [ENNReal.tsum_mul_left]
  have hR :
      (∑' w1, ∑' w2, ∑' w3, D.k v w1 * D.k w1 w2 * D.k w1 y * D.k w2 w3)
        = D.χ * (D.χ * kpow D.k 2 v y) := by
    calc (∑' w1, ∑' w2, ∑' w3, D.k v w1 * D.k w1 w2 * D.k w1 y * D.k w2 w3)
        = (∑' w1, ∑' w2, ∑' w3,
            (D.k v w1 * D.k w1 y * D.k w1 w2) * D.k w2 w3) := by
          refine tsum_congr fun w1 => tsum_congr fun w2 => tsum_congr fun w3 => ?_
          ring
      _ = (∑' w1, ∑' w2, (D.k v w1 * D.k w1 y * D.k w1 w2) * D.χ) := by
          refine tsum_congr fun w1 => tsum_congr fun w2 => ?_
          exact tsum_mul_k_eq D hreg w2 (D.k v w1 * D.k w1 y * D.k w1 w2)
      _ = (∑' w1, ∑' w2, ((D.k v w1 * D.k w1 y) * D.k w1 w2) * D.χ) := by
          refine tsum_congr fun w1 => tsum_congr fun w2 => ?_
          ring
      _ = (∑' w1, ((D.k v w1 * D.k w1 y) * D.χ) * D.χ) := by
          refine tsum_congr fun w1 => ?_
          exact tsum_mul_k_mul_eq D hreg w1 (D.k v w1 * D.k w1 y) D.χ
      _ = (∑' w1, (D.χ * D.χ) * (D.k v w1 * D.k w1 y)) := by
          refine tsum_congr fun w1 => ?_
          ring
      _ = (D.χ * D.χ) * kpow D.k 2 v y := tsum_mul_chain_two D v y (D.χ * D.χ)
      _ = D.χ * (D.χ * kpow D.k 2 v y) := by ring
  calc shapeTwo D v y
      = ∑' w1, ∑' w2, ∑' w3,
          D.χ * (D.χ * (D.χ * (D.k v w1 * D.k w1 w2 * D.k w1 y * D.k w2 w3))) := hlabel
    _ = D.χ * (D.χ * (D.χ * (∑' w1, ∑' w2, ∑' w3,
          D.k v w1 * D.k w1 w2 * D.k w1 y * D.k w2 w3))) := hpull
    _ = D.χ * (D.χ * (D.χ * (D.χ * (D.χ * kpow D.k 2 v y)))) := by
        rw [hR]

/-- **Sharpness of the `ℓ = 3` balanced evaluation.** -/
theorem shapeThreeA_eq_of_regular (D : KernelData V) (hreg : ∀ a, (∑' z, D.k a z) = D.χ)
    (v y : V) :
    shapeThreeA D v y = D.χ * (D.χ * (D.χ * (D.χ * kpow D.k 3 v y))) := by
  have hlabel : shapeThreeA D v y =
      ∑' w1, ∑' w2, ∑' w3,
        D.χ * (D.χ * (D.χ * (D.k v w1 * D.k w1 w2 * D.k w1 w3 * D.k w3 y))) := by
    unfold shapeThreeA
    refine tsum_congr fun w1 => tsum_congr fun w2 => tsum_congr fun w3 => ?_
    refine Eq.trans ?_ (peel_labels_eq D hreg w2 w2 w3
        (D.k v w1 * D.k w1 w2 * D.k w1 w3 * D.k w3 y))
    exact tsum_congr fun x1 => tsum_congr fun x2 => tsum_congr fun x3 => by ring
  have hpull :
      (∑' w1, ∑' w2, ∑' w3,
        D.χ * (D.χ * (D.χ * (D.k v w1 * D.k w1 w2 * D.k w1 w3 * D.k w3 y))))
      = D.χ * (D.χ * (D.χ * (∑' w1, ∑' w2, ∑' w3,
          D.k v w1 * D.k w1 w2 * D.k w1 w3 * D.k w3 y))) := by
    simp only [ENNReal.tsum_mul_left]
  have hR :
      (∑' w1, ∑' w2, ∑' w3, D.k v w1 * D.k w1 w2 * D.k w1 w3 * D.k w3 y)
        = D.χ * kpow D.k 3 v y := by
    calc (∑' w1, ∑' w2, ∑' w3, D.k v w1 * D.k w1 w2 * D.k w1 w3 * D.k w3 y)
        = (∑' w1, ∑' w2, ∑' w3,
            (D.k v w1 * D.k w1 w2) * (D.k w1 w3 * D.k w3 y)) := by
          refine tsum_congr fun w1 => tsum_congr fun w2 => tsum_congr fun w3 => ?_
          ring
      _ = (∑' w1, ∑' w2, (D.k v w1 * D.k w1 w2) * kpow D.k 2 w1 y) :=
          tsum_congr fun w1 => tsum_congr fun w2 =>
            tsum_mul_chain_two D w1 y (D.k v w1 * D.k w1 w2)
      _ = (∑' w1, (D.k v w1 * D.χ) * kpow D.k 2 w1 y) :=
          tsum_congr fun w1 => tsum_mul_k_mul_eq D hreg w1 (D.k v w1) (kpow D.k 2 w1 y)
      _ = (∑' w1, D.χ * (D.k v w1 * kpow D.k 2 w1 y)) := by
          refine tsum_congr fun w1 => ?_
          ring
      _ = D.χ * kpow D.k 3 v y := by
          rw [ENNReal.tsum_mul_left, kpow_three]
  calc shapeThreeA D v y
      = ∑' w1, ∑' w2, ∑' w3,
          D.χ * (D.χ * (D.χ * (D.k v w1 * D.k w1 w2 * D.k w1 w3 * D.k w3 y))) := hlabel
    _ = D.χ * (D.χ * (D.χ * (∑' w1, ∑' w2, ∑' w3,
          D.k v w1 * D.k w1 w2 * D.k w1 w3 * D.k w3 y))) := hpull
    _ = D.χ * (D.χ * (D.χ * (D.χ * kpow D.k 3 v y))) := by
        rw [hR]

/-- **Sharpness of the `ℓ = 3` chain evaluation.** -/
theorem shapeThreeB_eq_of_regular (D : KernelData V) (hreg : ∀ a, (∑' z, D.k a z) = D.χ)
    (v y : V) :
    shapeThreeB D v y = D.χ * (D.χ * (D.χ * (D.χ * kpow D.k 3 v y))) := by
  have hlabel : shapeThreeB D v y =
      ∑' w1, ∑' w2, ∑' w3,
        D.χ * (D.χ * (D.χ * (D.k v w1 * D.k w1 w2 * D.k w2 w3 * D.k w2 y))) := by
    unfold shapeThreeB
    refine tsum_congr fun w1 => tsum_congr fun w2 => tsum_congr fun w3 => ?_
    refine Eq.trans ?_ (peel_labels_eq D hreg w1 w3 w3
        (D.k v w1 * D.k w1 w2 * D.k w2 w3 * D.k w2 y))
    exact tsum_congr fun x1 => tsum_congr fun x2 => tsum_congr fun x3 => by ring
  have hpull :
      (∑' w1, ∑' w2, ∑' w3,
        D.χ * (D.χ * (D.χ * (D.k v w1 * D.k w1 w2 * D.k w2 w3 * D.k w2 y))))
      = D.χ * (D.χ * (D.χ * (∑' w1, ∑' w2, ∑' w3,
          D.k v w1 * D.k w1 w2 * D.k w2 w3 * D.k w2 y))) := by
    simp only [ENNReal.tsum_mul_left]
  have hR :
      (∑' w1, ∑' w2, ∑' w3, D.k v w1 * D.k w1 w2 * D.k w2 w3 * D.k w2 y)
        = D.χ * kpow D.k 3 v y := by
    calc (∑' w1, ∑' w2, ∑' w3, D.k v w1 * D.k w1 w2 * D.k w2 w3 * D.k w2 y)
        = (∑' w1, ∑' w2, ∑' w3,
            (D.k v w1 * D.k w1 w2 * D.k w2 y) * D.k w2 w3) := by
          refine tsum_congr fun w1 => tsum_congr fun w2 => tsum_congr fun w3 => ?_
          ring
      _ = (∑' w1, ∑' w2, (D.k v w1 * D.k w1 w2 * D.k w2 y) * D.χ) :=
          tsum_congr fun w1 => tsum_congr fun w2 =>
            tsum_mul_k_eq D hreg w2 (D.k v w1 * D.k w1 w2 * D.k w2 y)
      _ = (∑' w1, ∑' w2, (D.k v w1 * D.χ) * (D.k w1 w2 * D.k w2 y)) := by
          refine tsum_congr fun w1 => tsum_congr fun w2 => ?_
          ring
      _ = (∑' w1, (D.k v w1 * D.χ) * kpow D.k 2 w1 y) :=
          tsum_congr fun w1 => tsum_mul_chain_two D w1 y (D.k v w1 * D.χ)
      _ = (∑' w1, D.χ * (D.k v w1 * kpow D.k 2 w1 y)) := by
          refine tsum_congr fun w1 => ?_
          ring
      _ = D.χ * kpow D.k 3 v y := by
          rw [ENNReal.tsum_mul_left, kpow_three]
  calc shapeThreeB D v y
      = ∑' w1, ∑' w2, ∑' w3,
          D.χ * (D.χ * (D.χ * (D.k v w1 * D.k w1 w2 * D.k w2 w3 * D.k w2 y))) := hlabel
    _ = D.χ * (D.χ * (D.χ * (∑' w1, ∑' w2, ∑' w3,
          D.k v w1 * D.k w1 w2 * D.k w2 w3 * D.k w2 y))) := hpull
    _ = D.χ * (D.χ * (D.χ * (D.χ * kpow D.k 3 v y))) := by
        rw [hR]

/-- **Sharpness of the `ℓ = 4` evaluation.** -/
theorem shapeFour_eq_of_regular (D : KernelData V) (hreg : ∀ a, (∑' z, D.k a z) = D.χ)
    (v y : V) : shapeFour D v y = D.χ * (D.χ * (D.χ * kpow D.k 4 v y)) := by
  have hlabel : shapeFour D v y =
      ∑' w1, ∑' w2, ∑' w3,
        D.χ * (D.χ * (D.χ * (D.k v w1 * D.k w1 w2 * D.k w2 w3 * D.k w3 y))) := by
    unfold shapeFour
    refine tsum_congr fun w1 => tsum_congr fun w2 => tsum_congr fun w3 => ?_
    refine Eq.trans ?_ (peel_labels_eq D hreg w1 w2 w3
        (D.k v w1 * D.k w1 w2 * D.k w2 w3 * D.k w3 y))
    exact tsum_congr fun x1 => tsum_congr fun x2 => tsum_congr fun x3 => by ring
  have hpull :
      (∑' w1, ∑' w2, ∑' w3,
        D.χ * (D.χ * (D.χ * (D.k v w1 * D.k w1 w2 * D.k w2 w3 * D.k w3 y))))
      = D.χ * (D.χ * (D.χ * (∑' w1, ∑' w2, ∑' w3,
          D.k v w1 * D.k w1 w2 * D.k w2 w3 * D.k w3 y))) := by
    simp only [ENNReal.tsum_mul_left]
  have hR :
      (∑' w1, ∑' w2, ∑' w3, D.k v w1 * D.k w1 w2 * D.k w2 w3 * D.k w3 y)
        = kpow D.k 4 v y := by
    rw [← chain_four D v y]
    refine tsum_congr fun w1 => tsum_congr fun w2 => tsum_congr fun w3 => ?_
    ring
  calc shapeFour D v y
      = ∑' w1, ∑' w2, ∑' w3,
          D.χ * (D.χ * (D.χ * (D.k v w1 * D.k w1 w2 * D.k w2 w3 * D.k w3 y))) := hlabel
    _ = D.χ * (D.χ * (D.χ * (∑' w1, ∑' w2, ∑' w3,
          D.k v w1 * D.k w1 w2 * D.k w2 w3 * D.k w3 y))) := hpull
    _ = D.χ * (D.χ * (D.χ * kpow D.k 4 v y)) := by rw [hR]

/-- **The atlas is exact for a regular kernel**: for the source's transitive-graph situation
(constant row mass `E|K| = χ`) the honest three-term atlas equals `3χ⁵T² + 6χ⁴T³ + 6χ³T⁴`
identically, so the `ℓ = 2` coefficient `3χ⁵k²` is genuinely present, not an artefact of the
inequality. -/
theorem atlas_eq_of_regular (D : KernelData V) (hreg : ∀ a, (∑' z, D.k a z) = D.χ) (v y : V) :
    atlas D v y = 3 * (D.χ ^ 5 * PercLib.CriticalLRP.KernelPower.Kpow D.k 2 v y)
      + 6 * (D.χ ^ 4 * PercLib.CriticalLRP.KernelPower.Kpow D.k 3 v y)
      + 6 * (D.χ ^ 3 * PercLib.CriticalLRP.KernelPower.Kpow D.k 4 v y) := by
  unfold atlas
  rw [shapeTwo_eq_of_regular D hreg v y, shapeThreeA_eq_of_regular D hreg v y,
    shapeThreeB_eq_of_regular D hreg v y, shapeFour_eq_of_regular D hreg v y]
  simp only [kpow_eq_Kpow]
  ring

-- ---------------------------------------------------------------------------
-- BLOCK 2  (the four shape evaluations)
-- ---------------------------------------------------------------------------
/-- **Shape `ℓ = 2`**: `shapeTwo ≤ χ⁵ k²`. -/
theorem shapeTwo_le (D : KernelData V) (v y : V) :
    shapeTwo D v y ≤ D.χ * (D.χ * (D.χ * (D.χ * (D.χ * kpow D.k 2 v y)))) := by
  have hlabel : shapeTwo D v y ≤
      ∑' w1, ∑' w2, ∑' w3,
        D.χ * (D.χ * (D.χ * (D.k v w1 * D.k w1 w2 * D.k w1 y * D.k w2 w3))) := by
    unfold shapeTwo
    refine ENNReal.tsum_le_tsum fun w1 => ENNReal.tsum_le_tsum fun w2 =>
      ENNReal.tsum_le_tsum fun w3 => ?_
    refine le_trans (le_of_eq ?_) (peel_labels' D w2 w3 w3
      (D.k v w1 * D.k w1 w2 * D.k w1 y * D.k w2 w3))
    exact tsum_congr fun x1 => tsum_congr fun x2 => tsum_congr fun x3 => by ring
  have hpull :
      (∑' w1, ∑' w2, ∑' w3,
        D.χ * (D.χ * (D.χ * (D.k v w1 * D.k w1 w2 * D.k w1 y * D.k w2 w3))))
      = D.χ * (D.χ * (D.χ * (∑' w1, ∑' w2, ∑' w3,
          D.k v w1 * D.k w1 w2 * D.k w1 y * D.k w2 w3))) := by
    simp only [ENNReal.tsum_mul_left]
  have hR :
      (∑' w1, ∑' w2, ∑' w3, D.k v w1 * D.k w1 w2 * D.k w1 y * D.k w2 w3)
        ≤ D.χ * (D.χ * kpow D.k 2 v y) := by
    calc (∑' w1, ∑' w2, ∑' w3, D.k v w1 * D.k w1 w2 * D.k w1 y * D.k w2 w3)
        = (∑' w1, ∑' w2, ∑' w3,
            (D.k v w1 * D.k w1 y * D.k w1 w2) * D.k w2 w3) := by
          refine tsum_congr fun w1 => tsum_congr fun w2 => tsum_congr fun w3 => ?_
          ring
      _ ≤ (∑' w1, ∑' w2, (D.k v w1 * D.k w1 y * D.k w1 w2) * D.χ) := by
          refine ENNReal.tsum_le_tsum fun w1 => ENNReal.tsum_le_tsum fun w2 => ?_
          exact tsum_mul_k_le D w2 (D.k v w1 * D.k w1 y * D.k w1 w2)
      _ = (∑' w1, ∑' w2, ((D.k v w1 * D.k w1 y) * D.k w1 w2) * D.χ) := by
          refine tsum_congr fun w1 => tsum_congr fun w2 => ?_
          ring
      _ ≤ (∑' w1, ((D.k v w1 * D.k w1 y) * D.χ) * D.χ) := by
          refine ENNReal.tsum_le_tsum fun w1 => ?_
          exact tsum_mul_k_mul_le D w1 (D.k v w1 * D.k w1 y) D.χ
      _ = (∑' w1, (D.χ * D.χ) * (D.k v w1 * D.k w1 y)) := by
          refine tsum_congr fun w1 => ?_
          ring
      _ = (D.χ * D.χ) * kpow D.k 2 v y := tsum_mul_chain_two D v y (D.χ * D.χ)
      _ = D.χ * (D.χ * kpow D.k 2 v y) := by ring
  calc shapeTwo D v y
      ≤ ∑' w1, ∑' w2, ∑' w3,
          D.χ * (D.χ * (D.χ * (D.k v w1 * D.k w1 w2 * D.k w1 y * D.k w2 w3))) := hlabel
    _ = D.χ * (D.χ * (D.χ * (∑' w1, ∑' w2, ∑' w3,
          D.k v w1 * D.k w1 w2 * D.k w1 y * D.k w2 w3))) := hpull
    _ ≤ D.χ * (D.χ * (D.χ * (D.χ * (D.χ * kpow D.k 2 v y)))) := by
        refine mul_le_mul_right (mul_le_mul_right (mul_le_mul_right ?_ D.χ) D.χ) D.χ
        exact hR

/-- **Shape `ℓ = 3`, balanced**: `shapeThreeA ≤ χ⁴ k³`. -/
theorem shapeThreeA_le (D : KernelData V) (v y : V) :
    shapeThreeA D v y ≤ D.χ * (D.χ * (D.χ * (D.χ * kpow D.k 3 v y))) := by
  have hlabel : shapeThreeA D v y ≤
      ∑' w1, ∑' w2, ∑' w3,
        D.χ * (D.χ * (D.χ * (D.k v w1 * D.k w1 w2 * D.k w1 w3 * D.k w3 y))) := by
    unfold shapeThreeA
    refine ENNReal.tsum_le_tsum fun w1 => ENNReal.tsum_le_tsum fun w2 =>
      ENNReal.tsum_le_tsum fun w3 => ?_
    refine le_trans (le_of_eq ?_) (peel_labels' D w2 w2 w3
      (D.k v w1 * D.k w1 w2 * D.k w1 w3 * D.k w3 y))
    exact tsum_congr fun x1 => tsum_congr fun x2 => tsum_congr fun x3 => by ring
  have hpull :
      (∑' w1, ∑' w2, ∑' w3,
        D.χ * (D.χ * (D.χ * (D.k v w1 * D.k w1 w2 * D.k w1 w3 * D.k w3 y))))
      = D.χ * (D.χ * (D.χ * (∑' w1, ∑' w2, ∑' w3,
          D.k v w1 * D.k w1 w2 * D.k w1 w3 * D.k w3 y))) := by
    simp only [ENNReal.tsum_mul_left]
  have hR :
      (∑' w1, ∑' w2, ∑' w3, D.k v w1 * D.k w1 w2 * D.k w1 w3 * D.k w3 y)
        ≤ D.χ * kpow D.k 3 v y := by
    calc (∑' w1, ∑' w2, ∑' w3, D.k v w1 * D.k w1 w2 * D.k w1 w3 * D.k w3 y)
        = (∑' w1, ∑' w2, ∑' w3,
            (D.k v w1 * D.k w1 w2) * (D.k w1 w3 * D.k w3 y)) := by
          refine tsum_congr fun w1 => tsum_congr fun w2 => tsum_congr fun w3 => ?_
          ring
      _ = (∑' w1, ∑' w2, (D.k v w1 * D.k w1 w2) * kpow D.k 2 w1 y) :=
          tsum_congr fun w1 => tsum_congr fun w2 =>
            tsum_mul_chain_two D w1 y (D.k v w1 * D.k w1 w2)
      _ ≤ (∑' w1, (D.k v w1 * D.χ) * kpow D.k 2 w1 y) := by
          refine ENNReal.tsum_le_tsum fun w1 => ?_
          exact tsum_mul_k_mul_le D w1 (D.k v w1) (kpow D.k 2 w1 y)
      _ = (∑' w1, D.χ * (D.k v w1 * kpow D.k 2 w1 y)) := by
          refine tsum_congr fun w1 => ?_
          ring
      _ = D.χ * kpow D.k 3 v y := by
          rw [ENNReal.tsum_mul_left, kpow_three]
  calc shapeThreeA D v y
      ≤ ∑' w1, ∑' w2, ∑' w3,
          D.χ * (D.χ * (D.χ * (D.k v w1 * D.k w1 w2 * D.k w1 w3 * D.k w3 y))) := hlabel
    _ = D.χ * (D.χ * (D.χ * (∑' w1, ∑' w2, ∑' w3,
          D.k v w1 * D.k w1 w2 * D.k w1 w3 * D.k w3 y))) := hpull
    _ ≤ D.χ * (D.χ * (D.χ * (D.χ * kpow D.k 3 v y))) := by
        refine mul_le_mul_right (mul_le_mul_right (mul_le_mul_right ?_ D.χ) D.χ) D.χ
        exact hR

/-- **Shape `ℓ = 3`, chain**: `shapeThreeB ≤ χ⁴ k³`. -/
theorem shapeThreeB_le (D : KernelData V) (v y : V) :
    shapeThreeB D v y ≤ D.χ * (D.χ * (D.χ * (D.χ * kpow D.k 3 v y))) := by
  have hlabel : shapeThreeB D v y ≤
      ∑' w1, ∑' w2, ∑' w3,
        D.χ * (D.χ * (D.χ * (D.k v w1 * D.k w1 w2 * D.k w2 w3 * D.k w2 y))) := by
    unfold shapeThreeB
    refine ENNReal.tsum_le_tsum fun w1 => ENNReal.tsum_le_tsum fun w2 =>
      ENNReal.tsum_le_tsum fun w3 => ?_
    refine le_trans (le_of_eq ?_) (peel_labels' D w1 w3 w3
      (D.k v w1 * D.k w1 w2 * D.k w2 w3 * D.k w2 y))
    exact tsum_congr fun x1 => tsum_congr fun x2 => tsum_congr fun x3 => by ring
  have hpull :
      (∑' w1, ∑' w2, ∑' w3,
        D.χ * (D.χ * (D.χ * (D.k v w1 * D.k w1 w2 * D.k w2 w3 * D.k w2 y))))
      = D.χ * (D.χ * (D.χ * (∑' w1, ∑' w2, ∑' w3,
          D.k v w1 * D.k w1 w2 * D.k w2 w3 * D.k w2 y))) := by
    simp only [ENNReal.tsum_mul_left]
  have hR :
      (∑' w1, ∑' w2, ∑' w3, D.k v w1 * D.k w1 w2 * D.k w2 w3 * D.k w2 y)
        ≤ D.χ * kpow D.k 3 v y := by
    calc (∑' w1, ∑' w2, ∑' w3, D.k v w1 * D.k w1 w2 * D.k w2 w3 * D.k w2 y)
        = (∑' w1, ∑' w2, ∑' w3,
            (D.k v w1 * D.k w1 w2 * D.k w2 y) * D.k w2 w3) := by
          refine tsum_congr fun w1 => tsum_congr fun w2 => tsum_congr fun w3 => ?_
          ring
      _ ≤ (∑' w1, ∑' w2, (D.k v w1 * D.k w1 w2 * D.k w2 y) * D.χ) := by
          refine ENNReal.tsum_le_tsum fun w1 => ENNReal.tsum_le_tsum fun w2 => ?_
          exact tsum_mul_k_le D w2 (D.k v w1 * D.k w1 w2 * D.k w2 y)
      _ = (∑' w1, ∑' w2, (D.k v w1 * D.χ) * (D.k w1 w2 * D.k w2 y)) := by
          refine tsum_congr fun w1 => tsum_congr fun w2 => ?_
          ring
      _ = (∑' w1, (D.k v w1 * D.χ) * kpow D.k 2 w1 y) :=
          tsum_congr fun w1 => tsum_mul_chain_two D w1 y (D.k v w1 * D.χ)
      _ = (∑' w1, D.χ * (D.k v w1 * kpow D.k 2 w1 y)) := by
          refine tsum_congr fun w1 => ?_
          ring
      _ = D.χ * kpow D.k 3 v y := by
          rw [ENNReal.tsum_mul_left, kpow_three]
  calc shapeThreeB D v y
      ≤ ∑' w1, ∑' w2, ∑' w3,
          D.χ * (D.χ * (D.χ * (D.k v w1 * D.k w1 w2 * D.k w2 w3 * D.k w2 y))) := hlabel
    _ = D.χ * (D.χ * (D.χ * (∑' w1, ∑' w2, ∑' w3,
          D.k v w1 * D.k w1 w2 * D.k w2 w3 * D.k w2 y))) := hpull
    _ ≤ D.χ * (D.χ * (D.χ * (D.χ * kpow D.k 3 v y))) := by
        refine mul_le_mul_right (mul_le_mul_right (mul_le_mul_right ?_ D.χ) D.χ) D.χ
        exact hR

/-- **Shape `ℓ = 4`, chain**: `shapeFour ≤ χ³ k⁴`. -/
theorem shapeFour_le (D : KernelData V) (v y : V) :
    shapeFour D v y ≤ D.χ * (D.χ * (D.χ * kpow D.k 4 v y)) := by
  have hlabel : shapeFour D v y ≤
      ∑' w1, ∑' w2, ∑' w3,
        D.χ * (D.χ * (D.χ * (D.k v w1 * D.k w1 w2 * D.k w2 w3 * D.k w3 y))) := by
    unfold shapeFour
    refine ENNReal.tsum_le_tsum fun w1 => ENNReal.tsum_le_tsum fun w2 =>
      ENNReal.tsum_le_tsum fun w3 => ?_
    refine le_trans (le_of_eq ?_) (peel_labels' D w1 w2 w3
      (D.k v w1 * D.k w1 w2 * D.k w2 w3 * D.k w3 y))
    exact tsum_congr fun x1 => tsum_congr fun x2 => tsum_congr fun x3 => by ring
  have hpull :
      (∑' w1, ∑' w2, ∑' w3,
        D.χ * (D.χ * (D.χ * (D.k v w1 * D.k w1 w2 * D.k w2 w3 * D.k w3 y))))
      = D.χ * (D.χ * (D.χ * (∑' w1, ∑' w2, ∑' w3,
          D.k v w1 * D.k w1 w2 * D.k w2 w3 * D.k w3 y))) := by
    simp only [ENNReal.tsum_mul_left]
  have hR :
      (∑' w1, ∑' w2, ∑' w3, D.k v w1 * D.k w1 w2 * D.k w2 w3 * D.k w3 y)
        = kpow D.k 4 v y := by
    rw [← chain_four D v y]
    refine tsum_congr fun w1 => tsum_congr fun w2 => tsum_congr fun w3 => ?_
    ring
  calc shapeFour D v y
      ≤ ∑' w1, ∑' w2, ∑' w3,
          D.χ * (D.χ * (D.χ * (D.k v w1 * D.k w1 w2 * D.k w2 w3 * D.k w3 y))) := hlabel
    _ = D.χ * (D.χ * (D.χ * (∑' w1, ∑' w2, ∑' w3,
          D.k v w1 * D.k w1 w2 * D.k w2 w3 * D.k w3 y))) := hpull
    _ = D.χ * (D.χ * (D.χ * kpow D.k 4 v y)) := by rw [hR]

-- ---------------------------------------------------------------------------
-- BLOCK 3  (production-`Kpow` forms, discharged assembly, collected forms)
-- ---------------------------------------------------------------------------
/-! ## The star bound with the four shape evaluations discharged

`starMoment_le_three_term_nohyp` is m1's `starMoment_le_three_term` with `h2, h3A, h3B, h4`
discharged by the theorems above, so its only hypothesis is the four-label tree-graph input
`hatlas`.  `starMoment_le_three_term_Kpow` restates the bound in the production power
`KernelPower.Kpow = T^ℓ` of Lemma I.4.17 (via `kpow_eq_Kpow` of `Defs.lean`). -/

/-- **Shape `ℓ = 2` in production form**: `shapeTwo ≤ χ⁵ · T²`. -/
theorem shapeTwo_le_Kpow (D : KernelData V) (v y : V) :
    shapeTwo D v y
      ≤ D.χ * (D.χ * (D.χ * (D.χ * (D.χ *
          PercLib.CriticalLRP.KernelPower.Kpow D.k 2 v y)))) := by
  rw [← kpow_eq_Kpow (k := D.k) 2 v y]
  exact shapeTwo_le D v y

/-- **Shape `ℓ = 3` balanced in production form**: `shapeThreeA ≤ χ⁴ · T³`. -/
theorem shapeThreeA_le_Kpow (D : KernelData V) (v y : V) :
    shapeThreeA D v y
      ≤ D.χ * (D.χ * (D.χ * (D.χ *
          PercLib.CriticalLRP.KernelPower.Kpow D.k 3 v y))) := by
  rw [← kpow_eq_Kpow (k := D.k) 3 v y]
  exact shapeThreeA_le D v y

/-- **Shape `ℓ = 3` chain in production form**: `shapeThreeB ≤ χ⁴ · T³`. -/
theorem shapeThreeB_le_Kpow (D : KernelData V) (v y : V) :
    shapeThreeB D v y
      ≤ D.χ * (D.χ * (D.χ * (D.χ *
          PercLib.CriticalLRP.KernelPower.Kpow D.k 3 v y))) := by
  rw [← kpow_eq_Kpow (k := D.k) 3 v y]
  exact shapeThreeB_le D v y

/-- **Shape `ℓ = 4` in production form**: `shapeFour ≤ χ³ · T⁴`. -/
theorem shapeFour_le_Kpow (D : KernelData V) (v y : V) :
    shapeFour D v y
      ≤ D.χ * (D.χ * (D.χ *
          PercLib.CriticalLRP.KernelPower.Kpow D.k 4 v y)) := by
  rw [← kpow_eq_Kpow (k := D.k) 4 v y]
  exact shapeFour_le D v y

/-- **m1's `atlas_le` with the four shape evaluations discharged.** -/
theorem atlas_le_nohyp (D : KernelData V) (v y : V) :
    atlas D v y ≤ 3 * (D.χ * (D.χ * (D.χ * (D.χ * (D.χ * kpow D.k 2 v y)))))
      + 6 * (D.χ * (D.χ * (D.χ * (D.χ * kpow D.k 3 v y))))
      + 6 * (D.χ * (D.χ * (D.χ * kpow D.k 4 v y))) :=
  atlas_le D v y (shapeTwo_le D v y) (shapeThreeA_le D v y) (shapeThreeB_le D v y)
    (shapeFour_le D v y)

/-- **m1's `starMoment_le_three_term` with the four shape evaluations discharged.**

The only remaining input is `hatlas` : the `q = 0`, `p = 3` four-label instance of the tree-graph
inequality (I.2.2), i.e. the realization of the star event by the fifteen diagrams.  That is a tree
realization problem, not an algebraic one, and it is *not* proved here. -/
theorem starMoment_le_three_term_nohyp (π : Sym2 V → unitInterval) (D : KernelData V) (v y : V)
    (hatlas : I417Gen.starMoment π v y 3 ≤ atlas D v y) :
    I417Gen.starMoment π v y 3 ≤
      3 * (D.χ * (D.χ * (D.χ * (D.χ * (D.χ * kpow D.k 2 v y)))))
      + 6 * (D.χ * (D.χ * (D.χ * (D.χ * kpow D.k 3 v y))))
      + 6 * (D.χ * (D.χ * (D.χ * kpow D.k 4 v y))) :=
  hatlas.trans (atlas_le_nohyp D v y)

/-- **The `q = 0`, `p = 3` star bound in production form**
`3χ⁵T² + 6χ⁴T³ + 6χ³T⁴`, with only the tree-graph input `hatlas` as hypothesis. -/
theorem starMoment_le_three_term_Kpow (π : Sym2 V → unitInterval) (D : KernelData V) (v y : V)
    (hatlas : I417Gen.starMoment π v y 3 ≤ atlas D v y) :
    I417Gen.starMoment π v y 3 ≤
      3 * (D.χ * (D.χ * (D.χ * (D.χ * (D.χ *
          PercLib.CriticalLRP.KernelPower.Kpow D.k 2 v y)))))
      + 6 * (D.χ * (D.χ * (D.χ * (D.χ *
          PercLib.CriticalLRP.KernelPower.Kpow D.k 3 v y))))
      + 6 * (D.χ * (D.χ * (D.χ *
          PercLib.CriticalLRP.KernelPower.Kpow D.k 4 v y))) := by
  simpa only [kpow_eq_Kpow] using starMoment_le_three_term_nohyp π D v y hatlas

/-! ## Collected forms: the shape bounds with the power of `χ` collected

These are the same four inequalities, and the assembled star bound, written with `D.χ ^ 5`,
`D.χ ^ 4`, `D.χ ^ 3` and the production power `KernelPower.Kpow = T^ℓ`.  They are the form a
Case-3 consumer wants: `E[|K_x|³ 1(x ↔ y)] ≤ 3χ⁵T²(x,y) + 6χ⁴T³(x,y) + 6χ³T⁴(x,y)`. -/

/-- **Shape `ℓ = 2`, collected**: `shapeTwo ≤ χ⁵ T²`. -/
theorem shapeTwo_le_pow (D : KernelData V) (v y : V) :
    shapeTwo D v y ≤ D.χ ^ 5 * PercLib.CriticalLRP.KernelPower.Kpow D.k 2 v y := by
  refine (shapeTwo_le_Kpow D v y).trans (le_of_eq ?_)
  ring

/-- **Shape `ℓ = 3` balanced, collected**: `shapeThreeA ≤ χ⁴ T³`. -/
theorem shapeThreeA_le_pow (D : KernelData V) (v y : V) :
    shapeThreeA D v y ≤ D.χ ^ 4 * PercLib.CriticalLRP.KernelPower.Kpow D.k 3 v y := by
  refine (shapeThreeA_le_Kpow D v y).trans (le_of_eq ?_)
  ring

/-- **Shape `ℓ = 3` chain, collected**: `shapeThreeB ≤ χ⁴ T³`. -/
theorem shapeThreeB_le_pow (D : KernelData V) (v y : V) :
    shapeThreeB D v y ≤ D.χ ^ 4 * PercLib.CriticalLRP.KernelPower.Kpow D.k 3 v y := by
  refine (shapeThreeB_le_Kpow D v y).trans (le_of_eq ?_)
  ring

/-- **Shape `ℓ = 4`, collected**: `shapeFour ≤ χ³ T⁴`. -/
theorem shapeFour_le_pow (D : KernelData V) (v y : V) :
    shapeFour D v y ≤ D.χ ^ 3 * PercLib.CriticalLRP.KernelPower.Kpow D.k 4 v y := by
  refine (shapeFour_le_Kpow D v y).trans (le_of_eq ?_)
  ring

/-- **The atlas, collected**: `atlas ≤ 3χ⁵T² + 6χ⁴T³ + 6χ³T⁴`. -/
theorem atlas_le_pow (D : KernelData V) (v y : V) :
    atlas D v y ≤ 3 * (D.χ ^ 5 * PercLib.CriticalLRP.KernelPower.Kpow D.k 2 v y)
      + 6 * (D.χ ^ 4 * PercLib.CriticalLRP.KernelPower.Kpow D.k 3 v y)
      + 6 * (D.χ ^ 3 * PercLib.CriticalLRP.KernelPower.Kpow D.k 4 v y) := by
  refine (atlas_le_nohyp D v y).trans (le_of_eq ?_)
  simp only [kpow_eq_Kpow]
  ring

/-- **The `q = 0`, `p = 3` star bound, collected**:
`E[|K_x|³ 1(x ↔ y)] ≤ 3χ⁵T² + 6χ⁴T³ + 6χ³T⁴`. -/
theorem starMoment_le_collected (π : Sym2 V → unitInterval) (D : KernelData V) (v y : V)
    (hatlas : I417Gen.starMoment π v y 3 ≤ atlas D v y) :
    I417Gen.starMoment π v y 3 ≤
      3 * (D.χ ^ 5 * PercLib.CriticalLRP.KernelPower.Kpow D.k 2 v y)
      + 6 * (D.χ ^ 4 * PercLib.CriticalLRP.KernelPower.Kpow D.k 3 v y)
      + 6 * (D.χ ^ 3 * PercLib.CriticalLRP.KernelPower.Kpow D.k 4 v y) := by
  refine (starMoment_le_three_term_nohyp π D v y hatlas).trans (le_of_eq ?_)
  simp only [kpow_eq_Kpow]
  ring


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
