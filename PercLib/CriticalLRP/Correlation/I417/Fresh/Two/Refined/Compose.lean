/-
Independently rebuilt and integrated from the accepted `smwx5p94b/m1` artifact
`.ultramath/smwx5p94b/m1/M1Fresh`. Production integration revision:
`9c345df8dcb6d4027a2e61d7a7785abf4df111cf`. The coordinator assigns the production
namespace and fully qualified imports; the mathematical statements are unchanged.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Two.Refined.Bound

/-!
# Lemma I.4.17 at `q = 2` in the printed normalisation

Composing the marked non-plane bound of `I417/MarkedJoint/Transversal/Depth`

  `jointPow π x p w ≤ ∑_{ℓ ∈ [2,p+1]} C(p,ℓ) χ^(2p+1-ℓ) T^ℓ(x,w)`

with the four-edge fresh bound `tsum_freshMark_le_refined`

  `∑_g P(freshMark y g j w) ≤ χ²T²(w,y) + χ³T(w,y)`

and the polygon identity `∑_w T^ℓ(x,w) T^m(w,y) = T^(ℓ+m)(x,y)` gives

  `E|K_x|^p E|K_y|² − E[|K_x|^p|K_y|²1(x↮y)]
     ≤ 2 ∑_{ℓ∈[2,p+1]} C(p,ℓ) [ χ^(2p+3-ℓ) T^(ℓ+2)(x,y) + χ^(2p+4-ℓ) T^(ℓ+1)(x,y) ]`.

Every monomial carries exactly `(2p+1) + 4 = 2p+5` factors, which is the paper's
`2p+2q+1 = 2p+5` at `q = 2`, and the `T`-powers run over `ℓ+1 ∈ [3,p+2]` and `ℓ+2 ∈ [4,p+3]`,
both inside the printed `3 ≤ ℓ ≤ p+q+1 = p+3`.  The coefficient `2` is the two arm labels
`j : Fin 2`; `C = nonplaneMarkedCount p` is the child-swap transversal count of the marked side.

No fresh-side hypothesis remains: unlike `I417FreshTwo.moment_gap_two_le_poly_fourArm`, the input
`hfresh` here is the proved `tsum_freshMark_le_refined`, not the refuted single-hub four-arm
family.  BK (`π e < 1`) and the constant row sum (transitivity of the mean cluster volume) are the
only analytic inputs.
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

@[expose] public section

namespace PercLib.CriticalLRP.I417FreshTwo.Refined

open PercLib.CriticalLRP
open PercLib.CriticalLRP.I417Base
open PercLib.CriticalLRP.I417Fresh
open PercLib.CriticalLRP.I417FreshTwo
open PercLib.CriticalLRP.I417MarkedTransversal

variable {V : Type*} [Countable V] [DecidableEq V]

attribute [local instance] Classical.propDecidable

/-- **Lemma I.4.17 at `q = 2`, arbitrary `p`, with the printed exponent `2p+5`.** -/
theorem moment_gap_two_le_refined (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (x y : V)
    (hχ : ∀ v : V, I417.meanVol π v = I417.meanVol π x) (p : ℕ) (hp : 1 ≤ p) :
    I417A.momentProd π x y p 2 - I417A.rawDiff π x y p 2 ≤
      2 * (∑ ℓ ∈ Finset.Icc 2 (p + 1), (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
            (I417.meanVol π x ^ (2 * p + 3 - ℓ) * iterPow (kernel π) (ℓ + 2) x y))
      + 2 * (∑ ℓ ∈ Finset.Icc 2 (p + 1), (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
            (I417.meanVol π x ^ (2 * p + 4 - ℓ) * iterPow (kernel π) (ℓ + 1) x y)) := by
  classical
  set χ : ℝ≥0∞ := I417.meanVol π x with hχdef
  have hχsum : ∀ v : V, hubArmSum π v = χ := by
    intro v
    change (∑' z : V, (edgeMeasure π) (connSet v z)) = χ
    rw [hχdef]
    exact hχ v
  refine le_trans (I417Gen.moment_gap_tsub_le_marked π x y (p := p) (q := 2) (by norm_num)) ?_
  refine le_trans (ENNReal.tsum_le_tsum fun jw : Fin 2 × V =>
    mul_le_mul' le_rfl (tsum_freshMark_le_refined_iterPow π hπ y jw.2 χ hχsum jw.1)) ?_
  rw [tsum_finTwo_mul (fun w => I417Gen.jointPow π x p w *
    (χ ^ 2 * iterPow (kernel π) 2 w y + χ ^ 3 * iterPow (kernel π) 1 w y))]
  refine le_trans (mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun w =>
    mul_le_mul' (jointPow_le_nonplane_markedDepth π hπ χ (fun v => hχsum v) x hp w) le_rfl)) ?_
  simp only [show (fun a b : V => (edgeMeasure π) (connSet a b)) = kernel π from rfl]
  have hterm : ∀ ℓ ∈ Finset.Icc 2 (p + 1),
      (∑' w : V, (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
          (χ ^ (2 * p + 1 - ℓ) * iterPow (kernel π) ℓ x w) *
          (χ ^ 2 * iterPow (kernel π) 2 w y + χ ^ 3 * iterPow (kernel π) 1 w y))
        = (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
            (χ ^ (2 * p + 3 - ℓ) * iterPow (kernel π) (ℓ + 2) x y)
          + (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
            (χ ^ (2 * p + 4 - ℓ) * iterPow (kernel π) (ℓ + 1) x y) := by
    intro ℓ hℓ
    rw [Finset.mem_Icc] at hℓ
    have h1 : 2 * p + 1 - ℓ + 2 = 2 * p + 3 - ℓ := by omega
    have h2 : 2 * p + 1 - ℓ + 3 = 2 * p + 4 - ℓ := by omega
    have hsplit : ∀ w : V, (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
          (χ ^ (2 * p + 1 - ℓ) * iterPow (kernel π) ℓ x w) *
          (χ ^ 2 * iterPow (kernel π) 2 w y + χ ^ 3 * iterPow (kernel π) 1 w y)
        = ((nonplaneMarkedCount p ℓ : ℝ≥0∞) * (χ ^ (2 * p + 1 - ℓ) * χ ^ 2)) *
            (iterPow (kernel π) ℓ x w * iterPow (kernel π) 2 w y)
          + ((nonplaneMarkedCount p ℓ : ℝ≥0∞) * (χ ^ (2 * p + 1 - ℓ) * χ ^ 3)) *
            (iterPow (kernel π) ℓ x w * iterPow (kernel π) 1 w y) := by
      intro w
      ring
    simp only [hsplit]
    rw [ENNReal.tsum_add]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
    rw [iterPow_add_right (kernel π) ℓ 2 x y, iterPow_add_right (kernel π) ℓ 1 x y]
    rw [← pow_add, h1, ← pow_add, h2]
    ring
  have hpush : ∀ w : V, (∑ ℓ ∈ Finset.Icc 2 (p + 1), (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
        (χ ^ (2 * p + 1 - ℓ) * iterPow (kernel π) ℓ x w)) *
        (χ ^ 2 * iterPow (kernel π) 2 w y + χ ^ 3 * iterPow (kernel π) 1 w y)
      = ∑ ℓ ∈ Finset.Icc 2 (p + 1), (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
        (χ ^ (2 * p + 1 - ℓ) * iterPow (kernel π) ℓ x w) *
        (χ ^ 2 * iterPow (kernel π) 2 w y + χ ^ 3 * iterPow (kernel π) 1 w y) :=
    fun w => Finset.sum_mul ..
  simp only [hpush]
  rw [I417Base.tsum_finset_sum]
  rw [show (∑ ℓ ∈ Finset.Icc 2 (p + 1), ∑' w : V, (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
        (χ ^ (2 * p + 1 - ℓ) * iterPow (kernel π) ℓ x w) *
        (χ ^ 2 * iterPow (kernel π) 2 w y + χ ^ 3 * iterPow (kernel π) 1 w y))
      = ∑ ℓ ∈ Finset.Icc 2 (p + 1),
          ((nonplaneMarkedCount p ℓ : ℝ≥0∞) *
              (χ ^ (2 * p + 3 - ℓ) * iterPow (kernel π) (ℓ + 2) x y)
            + (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
              (χ ^ (2 * p + 4 - ℓ) * iterPow (kernel π) (ℓ + 1) x y))
      from Finset.sum_congr rfl fun ℓ hℓ => hterm ℓ hℓ]
  rw [Finset.sum_add_distrib]
  exact le_of_eq (by ring)

/-- **The vertex-transitive specialisation**, with no subcriticality or moment-finiteness
hypothesis: the mean cluster volume is constant by `I417Example.meanVol_eq_of_transitive`. -/
theorem moment_gap_two_le_refined_transitive (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (x y : V) (p : ℕ) (hp : 1 ≤ p)
    (htrans : ∀ v : V, ∃ g : V ≃ V, (∀ e : Sym2 V, π (Sym2.map g e) = π e) ∧ g x = v) :
    I417A.momentProd π x y p 2 - I417A.rawDiff π x y p 2 ≤
      2 * (∑ ℓ ∈ Finset.Icc 2 (p + 1), (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
            (I417.meanVol π x ^ (2 * p + 3 - ℓ) * iterPow (kernel π) (ℓ + 2) x y))
      + 2 * (∑ ℓ ∈ Finset.Icc 2 (p + 1), (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
            (I417.meanVol π x ^ (2 * p + 4 - ℓ) * iterPow (kernel π) (ℓ + 1) x y)) :=
  moment_gap_two_le_refined π hπ x y
    (I417Example.meanVol_eq_of_transitive π x htrans) p hp

end PercLib.CriticalLRP.I417FreshTwo.Refined
