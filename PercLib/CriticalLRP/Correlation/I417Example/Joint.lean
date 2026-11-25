/- Integrated from independently rebuilt Ultramath work, base revision 75f8858d8e30ea17b20f9ff1d216bc1508c01ce2.
Scratch source: ../../.ultramath/smwpxw774/m1/S474A/Joint.lean ; module path rewritten only.
-/

/-
# The three-terminal tree bound for `E[|Kx|² 1(w ∈ Kx)]`

Summing the tree-graph inequality `I417Example/TreeBound.threeLeaf_treeGraph` over the two
cluster-volume labels `x₁, x₂` and evaluating the three diagram families by transitivity gives

  `jointSq π x w = E[|Kx|² 1(w ∈ Kx)] ≤ χ³ T²(x,w) + 2 χ² T³(x,w)`,   `χ = meanVol π x`,

with `T²(x,y) = ∑_a τ(x,a)τ(a,y)` and `T³(x,y) = ∑_{a,b} τ(x,a)τ(a,b)τ(b,y)` the matrix powers
of the two-point function.  The three families are exactly the three rooted binary trees with
three labelled leaves (`w` at depth two: one; `w` at depth three: two), which is the count
`(2·3−3)!! = 3` of the printed tree-graph expansion.

The evaluation of each family is by Tonelli plus `meanVol π v = χ` (transitivity):
`∑_v τ(u,v) = χ` for every `u`.
-/
module

public import PercLib.CriticalLRP.Correlation.I417Example.TreeBound
public import PercLib.CriticalLRP.Correlation.I417.Final

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.I417Example

open PercLib.CriticalLRP.I417

variable {V : Type*} [Countable V]

/-! ## Tonelli bookkeeping -/

/-- Reordering four nested nonnegative sums. -/
theorem tsum_comm4 {α β γ δ : Type*} [Countable α] [Countable β] [Countable γ] [Countable δ]
    (f : α → β → γ → δ → ℝ≥0∞) :
    (∑' a, ∑' b, ∑' c, ∑' d, f a b c d) = ∑' c, ∑' d, ∑' a, ∑' b, f a b c d := by
  have h1 : (∑' a, ∑' b, ∑' c, ∑' d, f a b c d) = ∑' a, ∑' c, ∑' b, ∑' d, f a b c d :=
    tsum_congr fun a => ENNReal.tsum_comm
  have h2 : (∑' a, ∑' c, ∑' b, ∑' d, f a b c d) = ∑' c, ∑' a, ∑' b, ∑' d, f a b c d :=
    ENNReal.tsum_comm
  have h3 : (∑' c, ∑' a, ∑' b, ∑' d, f a b c d) = ∑' c, ∑' a, ∑' d, ∑' b, f a b c d :=
    tsum_congr fun c => tsum_congr fun a => ENNReal.tsum_comm
  have h4 : (∑' c, ∑' a, ∑' d, ∑' b, f a b c d) = ∑' c, ∑' d, ∑' a, ∑' b, f a b c d :=
    tsum_congr fun c => ENNReal.tsum_comm
  rw [h1, h2, h3, h4]

/-- Factoring a double sum of a product `K * a i * b j`. -/
theorem tsum_tsum_mul_fac {ι : Type*} [Countable ι] (K : ℝ≥0∞) (a b : ι → ℝ≥0∞) :
    (∑' i, ∑' j, K * a i * b j) = K * (∑' i, a i) * (∑' j, b j) := by
  have h1 : ∀ i, (∑' j, K * a i * b j) = K * a i * (∑' j, b j) :=
    fun i => ENNReal.tsum_mul_left
  simp only [h1]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]

/-- Pulling a constant out of a double sum. -/
theorem tsum_tsum_mul_const {ι : Type*} [Countable ι] (f : ι → ι → ℝ≥0∞) (c : ℝ≥0∞) :
    (∑' i, ∑' j, f i j * c) = (∑' i, ∑' j, f i j) * c := by
  simp only [ENNReal.tsum_mul_right]

/-! ## The three diagram values -/

/-- Value of the `w`-at-depth-2 family: `χ³ T²(x,w)`. -/
theorem famA_value (π : Sym2 V → unitInterval) (x w : V)
    (hχ : ∀ v, meanVol π v = meanVol π x) :
    (∑' x₁ : V, ∑' x₂ : V, ∑' u : V, ∑' v : V,
        (edgeMeasure π) (connSet x u) * (edgeMeasure π) (connSet u w) *
          (edgeMeasure π) (connSet u v) * (edgeMeasure π) (connSet v x₁) *
          (edgeMeasure π) (connSet v x₂))
      = (meanVol π x) ^ 3 * T2 π x w := by
  classical
  rw [tsum_comm4]
  have hstep : ∀ u v : V,
      (∑' x₁ : V, ∑' x₂ : V,
          (edgeMeasure π) (connSet x u) * (edgeMeasure π) (connSet u w) *
            (edgeMeasure π) (connSet u v) * (edgeMeasure π) (connSet v x₁) *
            (edgeMeasure π) (connSet v x₂))
        = (edgeMeasure π) (connSet x u) * (edgeMeasure π) (connSet u w) *
            (edgeMeasure π) (connSet u v) * meanVol π v * meanVol π v := by
    intro u v
    rw [tsum_tsum_mul_fac (K := (edgeMeasure π) (connSet x u) * (edgeMeasure π) (connSet u w) *
      (edgeMeasure π) (connSet u v)) (a := fun y => (edgeMeasure π) (connSet v y))
      (b := fun y => (edgeMeasure π) (connSet v y))]
    rfl
  simp only [hstep]
  have hconst : ∀ u v : V,
      (edgeMeasure π) (connSet x u) * (edgeMeasure π) (connSet u w) *
          (edgeMeasure π) (connSet u v) * meanVol π v * meanVol π v
        = (edgeMeasure π) (connSet x u) * (edgeMeasure π) (connSet u w) *
            (edgeMeasure π) (connSet u v) * meanVol π x * meanVol π x := by
    intro u v
    rw [show meanVol π v = meanVol π x from hχ v]
  simp only [hconst]
  rw [tsum_tsum_mul_const, tsum_tsum_mul_const]
  have hinner : (∑' u : V, ∑' v : V, (edgeMeasure π) (connSet x u) *
      (edgeMeasure π) (connSet u w) * (edgeMeasure π) (connSet u v))
      = T2 π x w * meanVol π x := by
    have h1 : ∀ u : V, (∑' v : V, (edgeMeasure π) (connSet x u) *
        (edgeMeasure π) (connSet u w) * (edgeMeasure π) (connSet u v))
        = (edgeMeasure π) (connSet x u) * (edgeMeasure π) (connSet u w) * meanVol π u := by
      intro u
      rw [ENNReal.tsum_mul_left]
      rfl
    simp only [h1]
    have h2 : ∀ u : V, (edgeMeasure π) (connSet x u) * (edgeMeasure π) (connSet u w) *
        meanVol π u = (edgeMeasure π) (connSet x u) * (edgeMeasure π) (connSet u w) *
        meanVol π x := fun u => by rw [show meanVol π u = meanVol π x from hχ u]
    simp only [h2]
    rw [ENNReal.tsum_mul_right]
    rfl
  rw [hinner]
  ring

/-- Value of the first `w`-at-depth-3 family: `χ² T³(x,w)`. -/
theorem famB_value (π : Sym2 V → unitInterval) (x w : V)
    (hχ : ∀ v, meanVol π v = meanVol π x) :
    (∑' x₁ : V, ∑' x₂ : V, ∑' u : V, ∑' v : V,
        (edgeMeasure π) (connSet x v) * (edgeMeasure π) (connSet v u) *
          (edgeMeasure π) (connSet u w) * (edgeMeasure π) (connSet u x₁) *
          (edgeMeasure π) (connSet v x₂))
      = (meanVol π x) ^ 2 * T3 π x w := by
  classical
  rw [tsum_comm4]
  have hstep : ∀ u v : V,
      (∑' x₁ : V, ∑' x₂ : V,
          (edgeMeasure π) (connSet x v) * (edgeMeasure π) (connSet v u) *
            (edgeMeasure π) (connSet u w) * (edgeMeasure π) (connSet u x₁) *
            (edgeMeasure π) (connSet v x₂))
        = (edgeMeasure π) (connSet x v) * (edgeMeasure π) (connSet v u) *
            (edgeMeasure π) (connSet u w) * meanVol π u * meanVol π v := by
    intro u v
    rw [tsum_tsum_mul_fac (K := (edgeMeasure π) (connSet x v) * (edgeMeasure π) (connSet v u) *
      (edgeMeasure π) (connSet u w)) (a := fun y => (edgeMeasure π) (connSet u y))
      (b := fun y => (edgeMeasure π) (connSet v y))]
    rfl
  simp only [hstep]
  have hconst : ∀ u v : V,
      (edgeMeasure π) (connSet x v) * (edgeMeasure π) (connSet v u) *
          (edgeMeasure π) (connSet u w) * meanVol π u * meanVol π v
        = (edgeMeasure π) (connSet x v) * (edgeMeasure π) (connSet v u) *
            (edgeMeasure π) (connSet u w) * meanVol π x * meanVol π x := by
    intro u v
    rw [show meanVol π u = meanVol π x from hχ u,
      show meanVol π v = meanVol π x from hχ v]
  simp only [hconst]
  rw [tsum_tsum_mul_const, tsum_tsum_mul_const]
  have hinner : (∑' u : V, ∑' v : V, (edgeMeasure π) (connSet x v) *
      (edgeMeasure π) (connSet v u) * (edgeMeasure π) (connSet u w))
      = T3 π x w * 1 := by
    rw [mul_one, ← ENNReal.tsum_comm (f := fun v u => (edgeMeasure π) (connSet x v) *
      (edgeMeasure π) (connSet v u) * (edgeMeasure π) (connSet u w))]
    rfl
  rw [hinner]
  ring

/-- Value of the second `w`-at-depth-3 family: `χ² T³(x,w)`. -/
theorem famC_value (π : Sym2 V → unitInterval) (x w : V)
    (hχ : ∀ v, meanVol π v = meanVol π x) :
    (∑' x₁ : V, ∑' x₂ : V, ∑' u : V, ∑' v : V,
        (edgeMeasure π) (connSet x u) * (edgeMeasure π) (connSet u v) *
          (edgeMeasure π) (connSet v w) * (edgeMeasure π) (connSet u x₁) *
          (edgeMeasure π) (connSet v x₂))
      = (meanVol π x) ^ 2 * T3 π x w := by
  classical
  rw [tsum_comm4]
  have hstep : ∀ u v : V,
      (∑' x₁ : V, ∑' x₂ : V,
          (edgeMeasure π) (connSet x u) * (edgeMeasure π) (connSet u v) *
            (edgeMeasure π) (connSet v w) * (edgeMeasure π) (connSet u x₁) *
            (edgeMeasure π) (connSet v x₂))
        = (edgeMeasure π) (connSet x u) * (edgeMeasure π) (connSet u v) *
            (edgeMeasure π) (connSet v w) * meanVol π u * meanVol π v := by
    intro u v
    rw [tsum_tsum_mul_fac (K := (edgeMeasure π) (connSet x u) * (edgeMeasure π) (connSet u v) *
      (edgeMeasure π) (connSet v w)) (a := fun y => (edgeMeasure π) (connSet u y))
      (b := fun y => (edgeMeasure π) (connSet v y))]
    rfl
  simp only [hstep]
  have hconst : ∀ u v : V,
      (edgeMeasure π) (connSet x u) * (edgeMeasure π) (connSet u v) *
          (edgeMeasure π) (connSet v w) * meanVol π u * meanVol π v
        = (edgeMeasure π) (connSet x u) * (edgeMeasure π) (connSet u v) *
            (edgeMeasure π) (connSet v w) * meanVol π x * meanVol π x := by
    intro u v
    rw [show meanVol π u = meanVol π x from hχ u,
      show meanVol π v = meanVol π x from hχ v]
  simp only [hconst]
  rw [tsum_tsum_mul_const, tsum_tsum_mul_const]
  have hinner : (∑' u : V, ∑' v : V, (edgeMeasure π) (connSet x u) *
      (edgeMeasure π) (connSet u v) * (edgeMeasure π) (connSet v w))
      = T3 π x w * 1 := by
    rw [mul_one]
    rfl
  rw [hinner]
  ring

/-! ## The three-terminal bound for `jointSq` -/

/-- **The three-terminal tree bound for the marked second moment**:
`E[|Kx|² 1(w ∈ Kx)] ≤ χ³ T²(x,w) + 2 χ² T³(x,w)`. -/
theorem jointSq_le (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (x w : V)
    (hχ : ∀ v, meanVol π v = meanVol π x) :
    jointSq π x w ≤ (meanVol π x) ^ 3 * T2 π x w + 2 * (meanVol π x) ^ 2 * T3 π x w := by
  classical
  rw [← tsum_tsum_inter_mark_eq π x w]
  have hterm : ∀ x₁ x₂ : V,
      (edgeMeasure π) (connSet x x₁ ∩ connSet x x₂ ∩ connSet x w) ≤
        (∑' u : V, ∑' v : V, (edgeMeasure π) (connSet x u) * (edgeMeasure π) (connSet u w) *
            (edgeMeasure π) (connSet u v) * (edgeMeasure π) (connSet v x₁) *
            (edgeMeasure π) (connSet v x₂)) +
          (∑' u : V, ∑' v : V, (edgeMeasure π) (connSet x v) * (edgeMeasure π) (connSet v u) *
            (edgeMeasure π) (connSet u w) * (edgeMeasure π) (connSet u x₁) *
            (edgeMeasure π) (connSet v x₂)) +
          (∑' u : V, ∑' v : V, (edgeMeasure π) (connSet x u) * (edgeMeasure π) (connSet u v) *
            (edgeMeasure π) (connSet v w) * (edgeMeasure π) (connSet u x₁) *
            (edgeMeasure π) (connSet v x₂)) :=
    fun x₁ x₂ => threeLeaf_treeGraph π hπ x w x₁ x₂
  refine le_trans (ENNReal.tsum_le_tsum fun x₁ => ENNReal.tsum_le_tsum fun x₂ => hterm x₁ x₂) ?_
  simp only [ENNReal.tsum_add]
  rw [famA_value π x w hχ, famB_value π x w hχ, famC_value π x w hχ]
  exact le_of_eq (by ring)

end PercLib.CriticalLRP.I417Example
