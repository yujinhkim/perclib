/- Integrated from independently rebuilt Ultramath work, base revision 75f8858d8e30ea17b20f9ff1d216bc1508c01ce2.
Scratch source: ../../.ultramath/smwpxw774/m1/S474A/Excess.lean ; module path rewritten only.
-/

/-
# The excess families of the `p = 2`, `q = 1` two-copy expansion, evaluated

This file feeds the three-terminal bound `I417Example/Joint.jointSq_le` into the two excess families
produced by direction B (`PercLib.CriticalLRP.I417.excess`):

  `excess π x y = E[|Kx|² 1(y ∈ Kx)] E|Ky| + ∑_w E[|Kx|² 1(w ∈ Kx)] P(y↔w) E|Kw|`.

With `χ = meanVol π x` (transitive graph), and the composition identities
`∑_w T²(x,w) τ(w,y) = T³(x,y)`, `∑_w T³(x,w) τ(w,y) = T⁴(x,y)`, one gets

* the **marked** family alone (`markSet_le`):
  `∑_w E[|Kx|² 1(w∈Kx)] τ(y,w) χ ≤ T³(x,y) χ⁴ + 2 T⁴(x,y) χ³` — exactly the three pictures of
  the printed figure with the printed coefficients `1` and `2`;
* the whole `I417.excess` (`excess_le`), which also contains the `y ∈ Kx` family:
  `≤ χ⁴ T² + 2χ³ T³ + χ⁴ T³ + 2χ³ T⁴`, hence `≤ 2χ⁴ T³ + 4χ³ T⁴` (`excess_le_two_four`).

The `y ∈ Kx` family is the term `E[|Kx|² 1(y∈Kx)] χ`, and it is *not* dominated by the printed
right-hand side through the tree-graph bound; it is redundant in the covering, because
`yInSet x y x₁ x₂ y₁ = markSet x y x₁ x₂ y₁ y` (`yInSet_eq_markSet`).  See
`I417Example/Printed.lean` for the resulting unconditional printed display, which uses the tight
cover and therefore keeps the printed constants `1` and `2`.
-/
module

public import PercLib.CriticalLRP.Correlation.I417Example.Joint

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.I417Example

open PercLib.CriticalLRP.I417

variable {V : Type*} [Countable V]

/-! ## Elementary facts about `connSet` -/

/-- The connection event is symmetric. -/
theorem connSet_comm (a b : V) : connSet a b = connSet b a := by
  ext ω
  exact ⟨connects_symm, connects_symm⟩

/-- `P(a↔a) = 1`. -/
theorem measure_connSet_self (π : Sym2 V → unitInterval) (a : V) :
    (edgeMeasure π) (connSet a a) = 1 := by
  have h : connSet a a = Set.univ := by
    ext ω
    exact ⟨fun _ => trivial, fun _ => connects_refl ω a⟩
  rw [h, measure_univ]

/-! ## The matrix-power composition identities -/

/-- `∑_w T²(x,w) τ(w,y) = T³(x,y)`. -/
theorem tsum_T2_mul (π : Sym2 V → unitInterval) (x y : V) :
    (∑' w : V, T2 π x w * (edgeMeasure π) (connSet w y)) = T3 π x y := by
  have h1 : ∀ w : V, T2 π x w * (edgeMeasure π) (connSet w y)
      = ∑' a : V, (edgeMeasure π) (connSet x a) * (edgeMeasure π) (connSet a w) *
          (edgeMeasure π) (connSet w y) := by
    intro w
    rw [T2, ← ENNReal.tsum_mul_right]
  simp only [h1]
  rw [ENNReal.tsum_comm]
  rfl

/-- `∑_w T³(x,w) τ(w,y) = T⁴(x,y)`. -/
theorem tsum_T3_mul (π : Sym2 V → unitInterval) (x y : V) :
    (∑' w : V, T3 π x w * (edgeMeasure π) (connSet w y)) = T4 π x y := by
  have h1 : ∀ w : V, T3 π x w * (edgeMeasure π) (connSet w y)
      = ∑' a : V, ∑' b : V, (edgeMeasure π) (connSet x a) * (edgeMeasure π) (connSet a b) *
          (edgeMeasure π) (connSet b w) * (edgeMeasure π) (connSet w y) := by
    intro w
    rw [T3, ← ENNReal.tsum_mul_right]
    exact tsum_congr fun a => (by rw [← ENNReal.tsum_mul_right])
  simp only [h1]
  rw [show (∑' w : V, ∑' a : V, ∑' b : V, (edgeMeasure π) (connSet x a) *
        (edgeMeasure π) (connSet a b) * (edgeMeasure π) (connSet b w) *
        (edgeMeasure π) (connSet w y))
      = ∑' a : V, ∑' b : V, ∑' w : V, (edgeMeasure π) (connSet x a) *
        (edgeMeasure π) (connSet a b) * (edgeMeasure π) (connSet b w) *
        (edgeMeasure π) (connSet w y) from by
    rw [ENNReal.tsum_comm]
    exact tsum_congr fun a => ENNReal.tsum_comm]
  rfl

/-! ## Monotonicity of the matrix powers -/

/-- `T² ≤ T³`: the diagonal step `τ(a,a) = 1`. -/
theorem T2_le_T3 (π : Sym2 V → unitInterval) (x y : V) : T2 π x y ≤ T3 π x y := by
  have hterm : ∀ a : V, (edgeMeasure π) (connSet x a) * (edgeMeasure π) (connSet a y)
      ≤ ∑' b : V, (edgeMeasure π) (connSet x a) * (edgeMeasure π) (connSet a b) *
          (edgeMeasure π) (connSet b y) := by
    intro a
    have hb : (edgeMeasure π) (connSet x a) * (edgeMeasure π) (connSet a a) *
        (edgeMeasure π) (connSet a y) ≤
        ∑' b : V, (edgeMeasure π) (connSet x a) * (edgeMeasure π) (connSet a b) *
          (edgeMeasure π) (connSet b y) := ENNReal.le_tsum (f := fun b => (edgeMeasure π) (connSet x a) * (edgeMeasure π) (connSet a b) * (edgeMeasure π) (connSet b y)) a
    rwa [measure_connSet_self, mul_one] at hb
  calc T2 π x y = ∑' a : V, (edgeMeasure π) (connSet x a) * (edgeMeasure π) (connSet a y) := rfl
    _ ≤ ∑' a : V, ∑' b : V, (edgeMeasure π) (connSet x a) * (edgeMeasure π) (connSet a b) *
          (edgeMeasure π) (connSet b y) := ENNReal.tsum_le_tsum hterm
    _ = T3 π x y := rfl

/-- `T³ ≤ T⁴`. -/
theorem T3_le_T4 (π : Sym2 V → unitInterval) (x y : V) : T3 π x y ≤ T4 π x y := by
  have hterm : ∀ a : V, (∑' b : V, (edgeMeasure π) (connSet x a) * (edgeMeasure π) (connSet a b) *
        (edgeMeasure π) (connSet b y))
      ≤ ∑' b : V, ∑' c : V, (edgeMeasure π) (connSet x a) * (edgeMeasure π) (connSet a b) *
          (edgeMeasure π) (connSet b c) * (edgeMeasure π) (connSet c y) := by
    intro a
    refine ENNReal.tsum_le_tsum fun b => ?_
    have hc : (edgeMeasure π) (connSet x a) * (edgeMeasure π) (connSet a b) *
        (edgeMeasure π) (connSet b b) * (edgeMeasure π) (connSet b y) ≤
        ∑' c : V, (edgeMeasure π) (connSet x a) * (edgeMeasure π) (connSet a b) *
          (edgeMeasure π) (connSet b c) * (edgeMeasure π) (connSet c y) := ENNReal.le_tsum (f := fun c => (edgeMeasure π) (connSet x a) * (edgeMeasure π) (connSet a b) * (edgeMeasure π) (connSet b c) * (edgeMeasure π) (connSet c y)) b
    rwa [measure_connSet_self, mul_one] at hc
  calc T3 π x y = ∑' a : V, ∑' b : V, (edgeMeasure π) (connSet x a) *
        (edgeMeasure π) (connSet a b) * (edgeMeasure π) (connSet b y) := rfl
    _ ≤ _ := ENNReal.tsum_le_tsum hterm
    _ = T4 π x y := rfl

/-! ## The marked family -/

/-- **The marked family of the excess, evaluated**: exactly the three printed pictures,
`T³(x,y) χ⁴ + 2 T⁴(x,y) χ³`. -/
theorem markSet_le (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (x y : V)
    (hχ : ∀ v, meanVol π v = meanVol π x) :
    (∑' w : V, jointSq π x w * ((edgeMeasure π) (connSet y w) * meanVol π w)) ≤
      T3 π x y * (meanVol π x) ^ 4 + 2 * T4 π x y * (meanVol π x) ^ 3 := by
  classical
  have hterm : ∀ w : V, jointSq π x w * ((edgeMeasure π) (connSet y w) * meanVol π w) ≤
      ((meanVol π x) ^ 3 * T2 π x w + 2 * (meanVol π x) ^ 2 * T3 π x w) *
        ((edgeMeasure π) (connSet y w) * meanVol π w) :=
    fun w => mul_le_mul' (jointSq_le π hπ x w hχ) le_rfl
  refine le_trans (ENNReal.tsum_le_tsum hterm) (le_of_eq ?_)
  have e1 : ∀ w : V, ((meanVol π x) ^ 3 * T2 π x w + 2 * (meanVol π x) ^ 2 * T3 π x w) *
        ((edgeMeasure π) (connSet y w) * meanVol π w)
      = (meanVol π x) ^ 4 * (T2 π x w * (edgeMeasure π) (connSet w y)) +
        2 * (meanVol π x) ^ 3 * (T3 π x w * (edgeMeasure π) (connSet w y)) := by
    intro w
    rw [show meanVol π w = meanVol π x from hχ w, connSet_comm y w]
    ring
  simp only [e1]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, tsum_T2_mul, tsum_T3_mul]
  ring

/-! ## The whole excess -/

/-- **The `I417.excess` bound up to the redundant `y ∈ Kx` family**: the tree-graph evaluation of
both excess families. -/
theorem excess_le (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (x y : V)
    (hχ : ∀ v, meanVol π v = meanVol π x) :
    excess π x y ≤
      (meanVol π x) ^ 4 * T2 π x y + 2 * (meanVol π x) ^ 3 * T3 π x y +
        (T3 π x y * (meanVol π x) ^ 4 + 2 * T4 π x y * (meanVol π x) ^ 3) := by
  have hy : jointSq π x y * meanVol π y ≤
      (meanVol π x) ^ 4 * T2 π x y + 2 * (meanVol π x) ^ 3 * T3 π x y := by
    have h := mul_le_mul' (jointSq_le π hπ x y hχ)
      (le_of_eq (hχ y) : meanVol π y ≤ meanVol π x)
    refine le_trans h (le_of_eq ?_)
    ring
  have h := add_le_add hy (markSet_le π hπ x y hχ)
  simpa only [excess] using h

/-- **The `I417.excess` bound with uniform constants**: `2 χ⁴ T³ + 4 χ³ T⁴`, from `T² ≤ T³`
and `T³ ≤ T⁴`. -/
theorem excess_le_two_four (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (x y : V)
    (hχ : ∀ v, meanVol π v = meanVol π x) :
    excess π x y ≤
      2 * T3 π x y * (meanVol π x) ^ 4 + 4 * T4 π x y * (meanVol π x) ^ 3 := by
  refine le_trans (excess_le π hπ x y hχ) ?_
  have hA : (meanVol π x) ^ 4 * T2 π x y ≤ T3 π x y * (meanVol π x) ^ 4 :=
    le_trans (mul_le_mul' le_rfl (T2_le_T3 π x y)) (le_of_eq (by ring))
  have hB : 2 * (meanVol π x) ^ 3 * T3 π x y ≤ 2 * T4 π x y * (meanVol π x) ^ 3 :=
    le_trans (mul_le_mul' le_rfl (T3_le_T4 π x y)) (le_of_eq (by ring))
  have hC : T3 π x y * (meanVol π x) ^ 4 ≤ T3 π x y * (meanVol π x) ^ 4 := le_rfl
  have hD : 2 * T4 π x y * (meanVol π x) ^ 3 ≤ 2 * T4 π x y * (meanVol π x) ^ 3 := le_rfl
  have hall := add_le_add (add_le_add (add_le_add hA hB) hC) hD
  have h1 : (meanVol π x) ^ 4 * T2 π x y + 2 * (meanVol π x) ^ 3 * T3 π x y +
        (T3 π x y * (meanVol π x) ^ 4 + 2 * T4 π x y * (meanVol π x) ^ 3) ≤
      (meanVol π x) ^ 4 * T2 π x y + 2 * (meanVol π x) ^ 3 * T3 π x y +
        T3 π x y * (meanVol π x) ^ 4 + 2 * T4 π x y * (meanVol π x) ^ 3 := le_of_eq (by ring)
  refine le_trans h1 (le_trans hall ?_)
  refine le_of_eq ?_
  ring

end PercLib.CriticalLRP.I417Example
