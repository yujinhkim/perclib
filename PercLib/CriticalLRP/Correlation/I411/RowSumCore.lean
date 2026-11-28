module

/-
Copyright (c) 2026 CriticalLRP swarm. Released under Apache 2.0.
-/

public import Mathlib

/-!
# The final summation step of Lemma I.4.11

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.11 (supplied PDF p. 39):

  `E1,r ≤ |B_r|⁻¹ ∑_{x ∈ B_r} ∇(0, x)` for every `r > 0`,

with the open triangle `∇(0, y) = ∑_{a,b} P(0 ↔ a) P(a ↔ b) P(b ↔ y)`.

The proof in the source has two steps.

1. The source first identifies the numerator of `E1,r` with the excluded mass
   `|B_r| (E|K|)² − E[|K| ∑_{y ∈ B_r} 1(y ∉ K) |K_y|]`, and rewrites
   that quantity as the double sum
   `∑_{y ∈ B_r} ∑_{x,z} (P(0 ↔ x) P(y ↔ z) − P(0 ↔ x ↮ y ↔ z))`
   over *all* lattice points `x, z`, using the two-copy coupling of
   Lemma I.4.12.  That step is not formalised here.

2. Lemma I.4.12 bounds each summand by the five-factor tree diagram
   `∑_{a,b} P(0 ↔ a) P(a ↔ x) P(a ↔ b) P(y ↔ b) P(b ↔ z)`.
   Since the two-point function has row sums `E|K|`, the sums over `x` and
   over `z` factor out, giving
   `excluded mass ≤ ∑_{y ∈ B_r} ∇(0, y) (E|K|)²`,
   and dividing by `|B_r| (E|K|)²` is exactly the claimed bound.

This file formalises step 2 exactly, for an arbitrary nonnegative symmetric-free
kernel `τ` with a uniform row-sum bound `χ` on a finite vertex type.  Nothing is
assumed about probabilities: the content is the interchange of the summation
order with the two-point factors, and the arithmetic of the normalisation.

## Main results

* `openTriangle`, `gapLeaf`, `gapMass`: the source's open triangle, the five-factor
  tree diagram attached to one triple `(x, y, z)`, and its sum over the window and
  over all `x, z`.
* `sum_four_comm`: interchange of the four-fold summation order.
* `gapMass_le`: `gapMass ≤ χ * χ * ∑_{y ∈ B} ∇(0, y)`.
* `lemma_I_4_11_step`: after dividing by `|B| χ²` the bound has the source's shape
  `|B|⁻¹ ∑_{y ∈ B} ∇(0, y)`.
* `nonvacuous`: an explicit instance in which all hypotheses hold and the bound is
  attained, so the statement is not vacuous.
-/

@[expose] public section

open Finset
open scoped BigOperators

set_option linter.hashCommand false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

namespace PercLib.CriticalLRP.I411

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The open triangle `∇(0, y) = ∑_{a,b} τ(0, a) τ(a, b) τ(b, y)` of the source,
written with the two-point function `τ`. -/
def openTriangle (τ : V → V → ℝ) (o y : V) : ℝ :=
  ∑ a, ∑ b, τ o a * τ a b * τ b y

/-- The five-factor tree diagram produced by Lemma I.4.12 for one triple `(x, y, z)`.

The source prints the last factor as `P(y ↔ b)`; by symmetry of the two-point
function that is `τ b y`, which is the form used here. -/
def gapLeaf (τ : V → V → ℝ) (o x y z : V) : ℝ :=
  ∑ a, ∑ b, τ o a * τ a x * τ a b * τ b y * τ b z

/-- The excluded mass of the source after applying Lemma I.4.12: the sum of the
five-factor diagrams over the window `B` in the middle vertex and over all `x, z`. -/
def gapMass (τ : V → V → ℝ) (o : V) (B : Finset V) : ℝ :=
  ∑ y ∈ B, ∑ x, ∑ z, gapLeaf τ o x y z

/-- Interchange of the four-fold summation order. -/
theorem sum_four_comm (F : V → V → V → V → ℝ) :
    (∑ x, ∑ z, ∑ a, ∑ b, F x z a b) = ∑ a, ∑ b, ∑ x, ∑ z, F x z a b := by
  have h1 : (∑ x, ∑ z, ∑ a, ∑ b, F x z a b) = ∑ x, ∑ a, ∑ z, ∑ b, F x z a b := by
    refine Finset.sum_congr rfl fun x _ => ?_
    exact Finset.sum_comm
  have h2 : (∑ x, ∑ a, ∑ z, ∑ b, F x z a b) = ∑ a, ∑ x, ∑ z, ∑ b, F x z a b :=
    Finset.sum_comm
  have h3 : (∑ a, ∑ x, ∑ z, ∑ b, F x z a b) = ∑ a, ∑ x, ∑ b, ∑ z, F x z a b := by
    refine Finset.sum_congr rfl fun a _ => ?_
    refine Finset.sum_congr rfl fun x _ => ?_
    exact Finset.sum_comm
  have h4 : (∑ a, ∑ x, ∑ b, ∑ z, F x z a b) = ∑ a, ∑ b, ∑ x, ∑ z, F x z a b := by
    refine Finset.sum_congr rfl fun a _ => ?_
    exact Finset.sum_comm
  rw [h1, h2, h3, h4]

/-- A sum of separable products is the product of the sums. -/
theorem double_sum_factor (u v : V → ℝ) :
    (∑ x, ∑ z, u x * v z) = (∑ x, u x) * (∑ z, v z) :=
  (Finset.sum_mul_sum Finset.univ Finset.univ u v).symm

/-- **The source's factorisation.**  For one fixed middle vertex `y`, summing the
five-factor diagram over all `x` and `z` and using the row sums of `τ` gives
`(∑_{a,b} τ(0,a) τ(a,b) τ(b,y)) (∑_x τ(a,x)) (∑_z τ(b,z))`. -/
theorem sum_gapLeaf (τ : V → V → ℝ) (o y : V) :
    (∑ x, ∑ z, gapLeaf τ o x y z)
      = ∑ a, ∑ b, (τ o a * τ a b * τ b y) * ((∑ x, τ a x) * (∑ z, τ b z)) := by
  simp only [gapLeaf]
  rw [sum_four_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have hsplit :
      (∑ x, ∑ z, τ o a * τ a x * τ a b * τ b y * τ b z)
        = ∑ x, ∑ z, (τ o a * τ a b * τ b y * τ a x) * τ b z := by
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ => ?_
    ring
  rw [hsplit, double_sum_factor, ← Finset.mul_sum]
  ring

/-- **The summation step of Lemma I.4.11.**  If `τ` is nonnegative with uniform row
sums at most `χ`, then the excluded mass built from the five-factor diagrams is at
most `χ²` times the sum of the open triangle over the window. -/
theorem gapMass_le (τ : V → V → ℝ) (o : V) (B : Finset V) {χ : ℝ}
    (hτ : ∀ a b, 0 ≤ τ a b) (hrow : ∀ a, ∑ b, τ a b ≤ χ) :
    gapMass τ o B ≤ χ * χ * ∑ y ∈ B, openTriangle τ o y := by
  have hrow0 : ∀ a, 0 ≤ ∑ b, τ a b := fun a =>
    Finset.sum_nonneg fun b _ => hτ a b
  unfold gapMass
  have hstep : ∀ y ∈ B,
      (∑ x, ∑ z, gapLeaf τ o x y z)
        ≤ χ * χ * openTriangle τ o y := by
    intro y _
    rw [sum_gapLeaf]
    have hχ0 : 0 ≤ χ := le_trans (hrow0 o) (hrow o)
    have hpoint : ∀ a b,
        (τ o a * τ a b * τ b y) * ((∑ x, τ a x) * (∑ z, τ b z))
          ≤ (τ o a * τ a b * τ b y) * (χ * χ) := by
      intro a b
      have h1 : (0:ℝ) ≤ τ o a * τ a b * τ b y :=
        mul_nonneg (mul_nonneg (hτ o a) (hτ a b)) (hτ b y)
      have h2 : (∑ x, τ a x) ≤ χ := hrow a
      have h3 : (∑ z, τ b z) ≤ χ := hrow b
      have h4 : (0:ℝ) ≤ ∑ x, τ a x := hrow0 a
      have h5 : (0:ℝ) ≤ ∑ z, τ b z := hrow0 b
      have h6 : (∑ x, τ a x) * (∑ z, τ b z) ≤ χ * χ :=
        mul_le_mul h2 h3 h5 hχ0
      exact mul_le_mul_of_nonneg_left h6 h1
    calc ∑ a, ∑ b, (τ o a * τ a b * τ b y) * ((∑ x, τ a x) * (∑ z, τ b z))
        ≤ ∑ a, ∑ b, (τ o a * τ a b * τ b y) * (χ * χ) :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hpoint a b
      _ = χ * χ * openTriangle τ o y := by
          unfold openTriangle
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          ring
  calc ∑ y ∈ B, ∑ x, ∑ z, gapLeaf τ o x y z
      ≤ ∑ y ∈ B, χ * χ * openTriangle τ o y :=
        Finset.sum_le_sum hstep
    _ = χ * χ * ∑ y ∈ B, openTriangle τ o y := by
        rw [Finset.mul_sum]

/-- **Lemma I.4.11, final step.**  Write the numerator of the source's error `E1,r`
as `N`.  The source proves `N ≤ gapMass` (via Lemma I.4.12) and then divides by
`|B| χ²`.  Under that hypothesis the source's conclusion
`E1,r ≤ |B|⁻¹ ∑_{y ∈ B} ∇(0, y)` follows. -/
theorem lemma_I_4_11_step (τ : V → V → ℝ) (o : V) (B : Finset V) {χ N : ℝ}
    (hχ : 0 < χ) (hB : B.Nonempty)
    (hτ : ∀ a b, 0 ≤ τ a b) (hrow : ∀ a, ∑ b, τ a b ≤ χ)
    (hN : N ≤ gapMass τ o B) :
    N / ((B.card : ℝ) * χ ^ 2) ≤ (B.card : ℝ)⁻¹ * ∑ y ∈ B, openTriangle τ o y := by
  have hcard : (0:ℝ) < (B.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hB
  have hden : (0:ℝ) < (B.card : ℝ) * χ ^ 2 := by positivity
  have hmain := gapMass_le τ o B hτ hrow
  have hN' : N ≤ χ * χ * ∑ y ∈ B, openTriangle τ o y := le_trans hN hmain
  have hdiv : N / ((B.card : ℝ) * χ ^ 2)
      ≤ (χ * χ * ∑ y ∈ B, openTriangle τ o y) / ((B.card : ℝ) * χ ^ 2) :=
    div_le_div_of_nonneg_right hN' hden.le
  refine le_trans hdiv (le_of_eq ?_)
  field_simp

/-- **The step loses nothing when the row sums are exactly the susceptibility.**
Under the source's translation-invariant condition that every row sum equals `χ`, the
factorisation of `sum_gapLeaf` is an identity, so the whole content of Lemma I.4.11 is
the gap inequality (Lemma I.4.12). -/
theorem gapMass_eq_of_rowSum (τ : V → V → ℝ) (o : V) (B : Finset V) {χ : ℝ}
    (hτ : ∀ a b, 0 ≤ τ a b) (hrow : ∀ a, ∑ b, τ a b = χ) :
    gapMass τ o B = χ * χ * ∑ y ∈ B, openTriangle τ o y := by
  have hrow0 : ∀ a, 0 ≤ ∑ b, τ a b := fun a =>
    Finset.sum_nonneg fun b _ => hτ a b
  have hχ0 : 0 ≤ χ := by
    rw [← hrow o]
    exact hrow0 o
  unfold gapMass
  have hstep : ∀ y ∈ B,
      (∑ x, ∑ z, gapLeaf τ o x y z) = χ * χ * openTriangle τ o y := by
    intro y _
    rw [sum_gapLeaf]
    have hpoint : ∀ a b,
        (τ o a * τ a b * τ b y) * ((∑ x, τ a x) * (∑ z, τ b z))
          = (τ o a * τ a b * τ b y) * (χ * χ) := by
      intro a b
      rw [hrow a, hrow b]
    calc ∑ a, ∑ b, (τ o a * τ a b * τ b y) * ((∑ x, τ a x) * (∑ z, τ b z))
        = ∑ a, ∑ b, (τ o a * τ a b * τ b y) * (χ * χ) := by
          exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hpoint a b
      _ = χ * χ * openTriangle τ o y := by
          unfold openTriangle
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          ring
  calc ∑ y ∈ B, ∑ x, ∑ z, gapLeaf τ o x y z
      = ∑ y ∈ B, χ * χ * openTriangle τ o y := Finset.sum_congr rfl hstep
    _ = χ * χ * ∑ y ∈ B, openTriangle τ o y := by
        rw [Finset.mul_sum]

/-- **Lemma I.4.11 from its two named inputs.**  Let `g` be the source's gap term
`P(0 ↔ x) P(y ↔ z) − P(0 ↔ x ↮ y ↔ z)`, assumed to obey the pointwise tree bound of
Lemma I.4.12.  Let `N` be the numerator of `E1,r`, that is, the excluded mass after the
source's two-copy rewriting, and assume `N` is at most the sum of `g` over the window
and over all `x, z`.  Then the source's conclusion holds.  The two hypotheses are
exactly the two inputs of the source's proof that are not the summation step. -/
theorem lemma_I_4_11_of_gap (τ : V → V → ℝ) (o : V) (B : Finset V)
    (g : V → V → V → ℝ) {χ N : ℝ}
    (hχ : 0 < χ) (hB : B.Nonempty)
    (hτ : ∀ a b, 0 ≤ τ a b) (hrow : ∀ a, ∑ b, τ a b ≤ χ)
    (hgap : ∀ x y z, g x y z ≤ gapLeaf τ o x y z)
    (hN : N ≤ ∑ y ∈ B, ∑ x, ∑ z, g x y z) :
    N / ((B.card : ℝ) * χ ^ 2) ≤ (B.card : ℝ)⁻¹ * ∑ y ∈ B, openTriangle τ o y := by
  refine lemma_I_4_11_step τ o B hχ hB hτ hrow (le_trans hN ?_)
  refine Finset.sum_le_sum fun y _ => Finset.sum_le_sum fun x _ =>
    Finset.sum_le_sum fun z _ => hgap x y z

/-- **Non-vacuity.**  On a one-point vertex type with the constant kernel `τ ≡ 1`,
window `{o}` and `χ = 1`, every hypothesis of `gapMass_le` holds and the bound is
attained: `gapMass = 1 = χ² ∑_{y ∈ B} ∇(0, y)`.  Hence the summation step is a
statement about a genuine configuration of the hypotheses, not a vacuous one. -/
theorem nonvacuous :
    ∃ (τ : Unit → Unit → ℝ) (o : Unit) (B : Finset Unit) (χ : ℝ),
      0 ≤ χ ∧ (∀ a b, 0 ≤ τ a b) ∧ (∀ a, ∑ b, τ a b ≤ χ) ∧ B.Nonempty ∧
        gapMass τ o B = χ * χ * ∑ y ∈ B, openTriangle τ o y := by
  refine ⟨fun _ _ => 1, (), {()}, 1, by norm_num, by intros; norm_num, ?_,
    ⟨(), by simp⟩, ?_⟩
  · intro a
    simp
  · simp [gapMass, gapLeaf, openTriangle]

#print axioms PercLib.CriticalLRP.I411.sum_four_comm
#print axioms PercLib.CriticalLRP.I411.sum_gapLeaf
#print axioms PercLib.CriticalLRP.I411.gapMass_le
#print axioms PercLib.CriticalLRP.I411.gapMass_eq_of_rowSum
#print axioms PercLib.CriticalLRP.I411.lemma_I_4_11_of_gap
#print axioms PercLib.CriticalLRP.I411.lemma_I_4_11_step
#print axioms PercLib.CriticalLRP.I411.nonvacuous

end PercLib.CriticalLRP.I411
