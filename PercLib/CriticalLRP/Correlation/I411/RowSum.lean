module

/-
Copyright (c) 2026 CriticalLRP swarm. Released under Apache 2.0.
-/

public import Mathlib

/-!
# The summation step of Lemma I.4.11 over a countable vertex set

The companion file `I411Core.lean` proves the summation step of Lemma I.4.11 for a
finite vertex type and a real-valued two-point function.  The source, however, sums
over all of `ℤ^d` and does not impose summability in advance; it uses only that the
row sums of the two-point function equal the susceptibility `E|K|`.

This file proves the same step for a countable vertex type and an `ℝ≥0∞`-valued
two-point function, so that no summability or finiteness hypothesis is needed: all
sums are extended nonnegative `tsum`s, and the only model input is the uniform row-sum
bound `∑'_b τ a b ≤ χ`.

## Main results

* `openTriangleE`, `gapLeafE`, `gapMassE`: the open triangle, the five-factor tree
  diagram of Lemma I.4.12, and the excluded mass summed over a finite window and over
  all `x, z`.
* `tsum_four_comm`: interchange of the four-fold `tsum` order.
* `tsum_sep`: `∑'_x ∑'_z u x * v z = (∑'_x u x) * (∑'_z v z)`.
* `tsum_gapLeafE`: the source's factorisation for one middle vertex.
* `gapMassE_le`: `gapMass ≤ χ * χ * ∑_{y ∈ B} ∇(0, y)`, with no finiteness hypothesis.

The two inputs of the source's proof that are *not* the summation step remain:
the two-copy rewriting of the numerator of `E1,r` as the sum of the gap terms, and
Lemma I.4.12 itself (proved in production as `longRange_twoCluster_gap`).
-/

@[expose] public section

noncomputable section

open scoped BigOperators ENNReal

set_option linter.hashCommand false
set_option linter.unusedSectionVars false

namespace PercLib.CriticalLRP.I411

variable {V : Type*} [Countable V]

/-- The open triangle `∇(0, y) = ∑'_{a,b} τ(0, a) τ(a, b) τ(b, y)`. -/
def openTriangleE (τ : V → V → ℝ≥0∞) (o y : V) : ℝ≥0∞ :=
  ∑' a, ∑' b, τ o a * τ a b * τ b y

/-- The five-factor tree diagram of Lemma I.4.12 for one triple `(x, y, z)`. -/
def gapLeafE (τ : V → V → ℝ≥0∞) (o x y z : V) : ℝ≥0∞ :=
  ∑' a, ∑' b, τ o a * τ a x * τ a b * τ b y * τ b z

/-- The excluded mass after applying Lemma I.4.12: summed over the window in the
middle vertex and over all `x` and `z`. -/
def gapMassE (τ : V → V → ℝ≥0∞) (o : V) (B : Finset V) : ℝ≥0∞ :=
  ∑ y ∈ B, ∑' x, ∑' z, gapLeafE τ o x y z

/-- Interchange of the four-fold `tsum` order. -/
theorem tsum_four_comm (F : V → V → V → V → ℝ≥0∞) :
    (∑' x, ∑' z, ∑' a, ∑' b, F x z a b) = ∑' a, ∑' b, ∑' x, ∑' z, F x z a b := by
  have h1 : (∑' x, ∑' z, ∑' a, ∑' b, F x z a b)
      = ∑' x, ∑' a, ∑' z, ∑' b, F x z a b :=
    tsum_congr fun x => ENNReal.tsum_comm
  have h2 : (∑' x, ∑' a, ∑' z, ∑' b, F x z a b)
      = ∑' a, ∑' x, ∑' z, ∑' b, F x z a b := ENNReal.tsum_comm
  have h3 : (∑' a, ∑' x, ∑' z, ∑' b, F x z a b)
      = ∑' a, ∑' x, ∑' b, ∑' z, F x z a b :=
    tsum_congr fun a => tsum_congr fun x => ENNReal.tsum_comm
  have h4 : (∑' a, ∑' x, ∑' b, ∑' z, F x z a b)
      = ∑' a, ∑' b, ∑' x, ∑' z, F x z a b :=
    tsum_congr fun a => ENNReal.tsum_comm
  rw [h1, h2, h3, h4]

/-- A `tsum` of separable products is the product of the `tsum`s. -/
theorem tsum_sep (u v : V → ℝ≥0∞) :
    (∑' x, ∑' z, u x * v z) = (∑' x, u x) * (∑' z, v z) := by
  have h : ∀ x, (∑' z, u x * v z) = u x * ∑' z, v z := fun x =>
    ENNReal.tsum_mul_left
  calc (∑' x, ∑' z, u x * v z) = ∑' x, u x * (∑' z, v z) := tsum_congr h
    _ = (∑' x, u x) * (∑' z, v z) := ENNReal.tsum_mul_right

/-- **The source's factorisation for one middle vertex.** -/
theorem tsum_gapLeafE (τ : V → V → ℝ≥0∞) (o y : V) :
    (∑' x, ∑' z, gapLeafE τ o x y z)
      = ∑' a, ∑' b, (τ o a * τ a b * τ b y) * ((∑' x, τ a x) * (∑' z, τ b z)) := by
  simp only [gapLeafE]
  rw [tsum_four_comm]
  refine tsum_congr fun a => tsum_congr fun b => ?_
  have hsplit : (∑' x, ∑' z, τ o a * τ a x * τ a b * τ b y * τ b z)
      = ∑' x, ∑' z, ((τ o a * τ a b * τ b y) * τ a x) * τ b z := by
    refine tsum_congr fun x => tsum_congr fun z => ?_
    ac_rfl
  rw [hsplit, tsum_sep, ENNReal.tsum_mul_left]
  ac_rfl

/-- **The summation step of Lemma I.4.11 over a countable vertex set.**  If the
two-point function has uniform row sums at most `χ`, then the excluded mass built
from the five-factor diagrams is at most `χ²` times the sum of the open triangle
over the window.  No finiteness or summability hypothesis is used. -/
theorem gapMassE_le (τ : V → V → ℝ≥0∞) (o : V) (B : Finset V) {χ : ℝ≥0∞}
    (hrow : ∀ a, ∑' b, τ a b ≤ χ) :
    gapMassE τ o B ≤ χ * χ * ∑ y ∈ B, openTriangleE τ o y := by
  unfold gapMassE
  have hstep : ∀ y ∈ B,
      (∑' x, ∑' z, gapLeafE τ o x y z) ≤ χ * χ * openTriangleE τ o y := by
    intro y _
    rw [tsum_gapLeafE]
    have hpoint : ∀ a b,
        (τ o a * τ a b * τ b y) * ((∑' x, τ a x) * (∑' z, τ b z))
          ≤ (τ o a * τ a b * τ b y) * (χ * χ) := by
      intro a b
      exact mul_le_mul (le_refl _) (mul_le_mul (hrow a) (hrow b) bot_le bot_le)
        bot_le bot_le
    calc ∑' a, ∑' b, (τ o a * τ a b * τ b y) * ((∑' x, τ a x) * (∑' z, τ b z))
        ≤ ∑' a, ∑' b, (τ o a * τ a b * τ b y) * (χ * χ) :=
          ENNReal.tsum_le_tsum fun a =>
            ENNReal.tsum_le_tsum fun b => hpoint a b
      _ = χ * χ * openTriangleE τ o y := by
          simp only [openTriangleE]
          have h1 : ∀ a, (∑' b, τ o a * τ a b * τ b y * (χ * χ))
              = (∑' b, τ o a * τ a b * τ b y) * (χ * χ) := fun a =>
            ENNReal.tsum_mul_right
          rw [tsum_congr h1, ENNReal.tsum_mul_right, mul_comm]
  calc ∑ y ∈ B, ∑' x, ∑' z, gapLeafE τ o x y z
      ≤ ∑ y ∈ B, χ * χ * openTriangleE τ o y := Finset.sum_le_sum hstep
    _ = χ * χ * ∑ y ∈ B, openTriangleE τ o y := by
        rw [Finset.mul_sum]

#print axioms PercLib.CriticalLRP.I411.tsum_four_comm
#print axioms PercLib.CriticalLRP.I411.tsum_sep
#print axioms PercLib.CriticalLRP.I411.tsum_gapLeafE
#print axioms PercLib.CriticalLRP.I411.gapMassE_le

end PercLib.CriticalLRP.I411
