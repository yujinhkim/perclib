/-
Independently reviewed and integrated from the completed artifact `smwx6p0op/m1`
at `.ultramath/smwx6p0op/m1/M3Q`. Production integration revision:
`3cd318e5a37d0dc889f23bd3baf1b8884e651a27`. The coordinator uses the production
namespace and fully qualified imports; the proof covers `q = 3`, not arbitrary `q`.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Three.Refined.Summed
public import PercLib.CriticalLRP.Correlation.I417.MarkedJoint.Transversal.Depth

/-!
Independently built for swarm `smwx6p0op`, member `m1`, direction Q3-MARK-ON-PATH-COVER.

# Lemma I.4.17 at `q = 3` in the printed normalisation

Composing the marked non-plane bound of `I417/MarkedJoint/Transversal/Depth`

  `jointPow π x p w ≤ ∑_{ℓ ∈ [2,p+1]} C(p,ℓ) χ^(2p+1-ℓ) T^ℓ(x,w)`

with the six-edge fresh bound `tsum_freshMark_le_refined`

  `∑_g P(freshMark y g j w) ≤ 2χ³T³(w,y) + 3χ⁴T²(w,y) + 3χ⁵T(w,y)`

and the polygon identity `∑_w T^ℓ(x,w) T^m(w,y) = T^(ℓ+m)(x,y)` gives

  `E|K_x|^p E|K_y|³ − E[|K_x|^p|K_y|³1(x↮y)]
     ≤ 3 ∑_{ℓ∈[2,p+1]} C(p,ℓ) [ 2 χ^(2p+4-ℓ) T^(ℓ+3)(x,y)
                                 + 3 χ^(2p+5-ℓ) T^(ℓ+2)(x,y)
                                 + 3 χ^(2p+6-ℓ) T^(ℓ+1)(x,y) ]`.

Every monomial carries exactly `(2p+1) + 6 = 2p+7 = 2p + 2q + 1` factors, and the `T`-powers run
over `ℓ+1 ∈ [3, p+2]`, `ℓ+2 ∈ [4, p+3]`, `ℓ+3 ∈ [5, p+4]`, all inside the printed
`3 ≤ ℓ ≤ p + q + 1 = p + 4`.  The coefficient `3` is the three arm labels `j : Fin 3`.

No fresh-side hypothesis remains: BK (`π e < 1`) and the constant row sum (transitivity of the mean
cluster volume) are the only analytic inputs.
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false

@[expose] public section

namespace PercLib.CriticalLRP.I417FreshThree.Refined

open PercLib.CriticalLRP
open PercLib.CriticalLRP.I417Base
open PercLib.CriticalLRP.I417Fresh
open PercLib.CriticalLRP.I417FreshTwo
open PercLib.CriticalLRP.I417MarkedTransversal

variable {V : Type*} [Countable V] [DecidableEq V]

attribute [local instance] Classical.propDecidable

/-- The three arm labels of a `q = 3` fresh factor contribute a factor `3`, the arm bound being
independent of the selected arm. -/
theorem tsum_finThree_snd (f : V → ℝ≥0∞) :
    (∑' jw : Fin 3 × V, f jw.2) = 3 * ∑' w : V, f w := by
  rw [ENNReal.tsum_prod']
  have h : ∀ j : Fin 3, (∑' w : V, f (j, w).2) = ∑' w : V, f w := by
    intro j
    exact tsum_congr fun w => rfl
  rw [tsum_congr h, tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp

/-- **Lemma I.4.17 at `q = 3`, arbitrary `p`, with the printed exponent `2p+7`.** -/
theorem moment_gap_three_le_refined (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (x y : V)
    (hχ : ∀ v : V, I417.meanVol π v = I417.meanVol π x) (p : ℕ) (hp : 1 ≤ p) :
    I417A.momentProd π x y p 3 - I417A.rawDiff π x y p 3 ≤
      3 * (∑ ℓ ∈ Finset.Icc 2 (p + 1), (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
        (2 * (I417.meanVol π x ^ (2 * p + 4 - ℓ) * iterPow (kernel π) (ℓ + 3) x y)
          + 3 * (I417.meanVol π x ^ (2 * p + 5 - ℓ) * iterPow (kernel π) (ℓ + 2) x y)
          + 3 * (I417.meanVol π x ^ (2 * p + 6 - ℓ) * iterPow (kernel π) (ℓ + 1) x y))) := by
  classical
  set χ : ℝ≥0∞ := I417.meanVol π x with hχdef
  have hχsum : ∀ v : V, hubArmSum π v = χ := by
    intro v
    change (∑' z : V, (edgeMeasure π) (connSet v z)) = χ
    rw [hχdef]
    exact hχ v
  refine le_trans (I417Gen.moment_gap_tsub_le_marked π x y (p := p) (q := 3) (by norm_num)) ?_
  refine le_trans (ENNReal.tsum_le_tsum fun jw : Fin 3 × V =>
    mul_le_mul' le_rfl (tsum_freshMark_le_refined π hπ y jw.2 χ hχsum jw.1)) ?_
  rw [tsum_finThree_snd (fun w => I417Gen.jointPow π x p w * freshThreeRefined π χ y w)]
  refine mul_le_mul' le_rfl ?_
  refine le_trans (ENNReal.tsum_le_tsum fun w =>
    mul_le_mul' (jointPow_le_nonplane_markedDepth π hπ χ (fun v => hχsum v) x hp w) le_rfl) ?_
  have hk : (fun a b : V => (edgeMeasure π) (connSet a b)) = kernel π := by
    funext a b
    exact (I417FreshTwo.kernel_def π a b).symm
  rw [hk]
  have hdef : ∀ w : V, freshThreeRefined π χ y w =
      2 * (χ ^ 3 * iterPow (kernel π) 3 w y) + 3 * (χ ^ 4 * iterPow (kernel π) 2 w y) +
        3 * (χ ^ 5 * iterPow (kernel π) 1 w y) := fun w => rfl
  rw [show (∑' a : V, (∑ ℓ ∈ Finset.Icc 2 (p + 1), (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
        (χ ^ (2 * p + 1 - ℓ) * iterPow (kernel π) ℓ x a)) * freshThreeRefined π χ y a)
      = ∑' a : V, (∑ ℓ ∈ Finset.Icc 2 (p + 1), (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
        (χ ^ (2 * p + 1 - ℓ) * iterPow (kernel π) ℓ x a)) *
        (2 * (χ ^ 3 * iterPow (kernel π) 3 a y) + 3 * (χ ^ 4 * iterPow (kernel π) 2 a y) +
          3 * (χ ^ 5 * iterPow (kernel π) 1 a y)) from
    tsum_congr fun a => by rw [hdef a]]
  have hpush : ∀ w : V, (∑ ℓ ∈ Finset.Icc 2 (p + 1), (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
        (χ ^ (2 * p + 1 - ℓ) * iterPow (kernel π) ℓ x w)) *
        (2 * (χ ^ 3 * iterPow (kernel π) 3 w y) + 3 * (χ ^ 4 * iterPow (kernel π) 2 w y) +
          3 * (χ ^ 5 * iterPow (kernel π) 1 w y))
      = ∑ ℓ ∈ Finset.Icc 2 (p + 1), (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
        (χ ^ (2 * p + 1 - ℓ) * iterPow (kernel π) ℓ x w) *
        (2 * (χ ^ 3 * iterPow (kernel π) 3 w y) + 3 * (χ ^ 4 * iterPow (kernel π) 2 w y) +
          3 * (χ ^ 5 * iterPow (kernel π) 1 w y)) :=
    fun w => Finset.sum_mul ..
  simp only [hpush]
  rw [I417Base.tsum_finset_sum]
  have hterm : ∀ ℓ ∈ Finset.Icc 2 (p + 1),
      (∑' w : V, (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
        (χ ^ (2 * p + 1 - ℓ) * iterPow (kernel π) ℓ x w) *
        (2 * (χ ^ 3 * iterPow (kernel π) 3 w y) + 3 * (χ ^ 4 * iterPow (kernel π) 2 w y) +
          3 * (χ ^ 5 * iterPow (kernel π) 1 w y)))
      = (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
        (2 * (χ ^ (2 * p + 4 - ℓ) * iterPow (kernel π) (ℓ + 3) x y)
          + 3 * (χ ^ (2 * p + 5 - ℓ) * iterPow (kernel π) (ℓ + 2) x y)
          + 3 * (χ ^ (2 * p + 6 - ℓ) * iterPow (kernel π) (ℓ + 1) x y)) := by
    intro ℓ hℓ
    rw [Finset.mem_Icc] at hℓ
    have e1 : 2 * p + 1 - ℓ + 3 = 2 * p + 4 - ℓ := by omega
    have e2 : 2 * p + 1 - ℓ + 4 = 2 * p + 5 - ℓ := by omega
    have e3 : 2 * p + 1 - ℓ + 5 = 2 * p + 6 - ℓ := by omega
    have hsplit : ∀ w : V, (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
          (χ ^ (2 * p + 1 - ℓ) * iterPow (kernel π) ℓ x w) *
          (2 * (χ ^ 3 * iterPow (kernel π) 3 w y) + 3 * (χ ^ 4 * iterPow (kernel π) 2 w y) +
            3 * (χ ^ 5 * iterPow (kernel π) 1 w y))
        = ((nonplaneMarkedCount p ℓ : ℝ≥0∞) * 2 * (χ ^ (2 * p + 1 - ℓ) * χ ^ 3)) *
            (iterPow (kernel π) ℓ x w * iterPow (kernel π) 3 w y)
          + (((nonplaneMarkedCount p ℓ : ℝ≥0∞) * 3 * (χ ^ (2 * p + 1 - ℓ) * χ ^ 4)) *
              (iterPow (kernel π) ℓ x w * iterPow (kernel π) 2 w y)
            + ((nonplaneMarkedCount p ℓ : ℝ≥0∞) * 3 * (χ ^ (2 * p + 1 - ℓ) * χ ^ 5)) *
              (iterPow (kernel π) ℓ x w * iterPow (kernel π) 1 w y)) := fun w => by ring
    rw [tsum_congr hsplit, ENNReal.tsum_add, ENNReal.tsum_add]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
    rw [iterPow_add_right (kernel π) ℓ 3 x y, iterPow_add_right (kernel π) ℓ 2 x y,
      iterPow_add_right (kernel π) ℓ 1 x y]
    rw [← pow_add, e1, ← pow_add, e2, ← pow_add, e3]
    ring
  rw [show (∑ ℓ ∈ Finset.Icc 2 (p + 1), ∑' w : V, (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
        (χ ^ (2 * p + 1 - ℓ) * iterPow (kernel π) ℓ x w) *
        (2 * (χ ^ 3 * iterPow (kernel π) 3 w y) + 3 * (χ ^ 4 * iterPow (kernel π) 2 w y) +
          3 * (χ ^ 5 * iterPow (kernel π) 1 w y)))
      = ∑ ℓ ∈ Finset.Icc 2 (p + 1), (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
        (2 * (χ ^ (2 * p + 4 - ℓ) * iterPow (kernel π) (ℓ + 3) x y)
          + 3 * (χ ^ (2 * p + 5 - ℓ) * iterPow (kernel π) (ℓ + 2) x y)
          + 3 * (χ ^ (2 * p + 6 - ℓ) * iterPow (kernel π) (ℓ + 1) x y)) from
    Finset.sum_congr rfl hterm]

/-- **The vertex-transitive specialisation** of the `q = 3` instance, with no subcriticality or
moment-finiteness hypothesis beyond BK. -/
theorem moment_gap_three_le_refined_transitive (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (x y : V) (p : ℕ) (hp : 1 ≤ p)
    (htrans : ∀ v : V, ∃ g : V ≃ V, (∀ e : Sym2 V, π (Sym2.map g e) = π e) ∧ g x = v) :
    I417A.momentProd π x y p 3 - I417A.rawDiff π x y p 3 ≤
      3 * (∑ ℓ ∈ Finset.Icc 2 (p + 1), (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
        (2 * (I417.meanVol π x ^ (2 * p + 4 - ℓ) * iterPow (kernel π) (ℓ + 3) x y)
          + 3 * (I417.meanVol π x ^ (2 * p + 5 - ℓ) * iterPow (kernel π) (ℓ + 2) x y)
          + 3 * (I417.meanVol π x ^ (2 * p + 6 - ℓ) * iterPow (kernel π) (ℓ + 1) x y))) :=
  moment_gap_three_le_refined π hπ x y
    (I417Example.meanVol_eq_of_transitive π x htrans) p hp

end PercLib.CriticalLRP.I417FreshThree.Refined
