/-
Coordinator assembly for the accepted `smwx9itnu/m1` q=4 fresh evaluation.
Production integration revision: `3163cff3d90175d69f2612903830a27bdf5c0ab6`.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Eval.Summed
public import PercLib.CriticalLRP.Correlation.I417.MarkedJoint.Transversal.Depth
public import PercLib.CriticalLRP.PowerLawTreeMoments

/-!
# Lemma I.4.17 at `q = 4` in the printed normalisation

The proved fresh-copy bound has eight two-point factors per shape. Composing it with
the non-plane marked-depth bound gives total factor count `2p+9` for every
positive `p`, and path powers within the printed interval `[3,p+5]`. No finite
moment or subcriticality input is needed beyond the prescribed BK hypotheses.
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedSimpArgs false
set_option linter.style.longLine false

@[expose] public section

namespace PercLib.CriticalLRP.I417FreshFour.Eval

open PercLib.CriticalLRP
open PercLib.CriticalLRP.I417Base
open PercLib.CriticalLRP.I417Fresh
open PercLib.CriticalLRP.I417FreshTwo
open PercLib.CriticalLRP.I417MarkedTransversal

variable {V : Type*} [Countable V] [DecidableEq V]

attribute [local instance] Classical.propDecidable

/-- Four choices of the marked arm contribute one common factor `4`. -/
theorem tsum_finFour_snd (f : V → ℝ≥0∞) :
    (∑' jw : Fin 4 × V, f jw.2) = 4 * ∑' w : V, f w := by
  rw [ENNReal.tsum_prod']
  have h : ∀ j : Fin 4, (∑' w : V, f (j, w).2) = ∑' w : V, f w := by
    intro j
    exact tsum_congr fun w => rfl
  rw [tsum_congr h, tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp

/-- Lemma I.4.17 at `q = 4`, with total factor count `2p+9`. -/
theorem moment_gap_four_le_eval (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (x y : V)
    (hχ : ∀ v : V, I417.meanVol π v = I417.meanVol π x) (p : ℕ) (hp : 1 ≤ p) :
    I417A.momentProd π x y p 4 - I417A.rawDiff π x y p 4 ≤
      4 * (∑ ℓ ∈ Finset.Icc 2 (p + 1), (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
        (6 * (I417.meanVol π x ^ (2 * p + 5 - ℓ) * iterPow (kernel π) (ℓ + 4) x y) +
          12 * (I417.meanVol π x ^ (2 * p + 6 - ℓ) * iterPow (kernel π) (ℓ + 3) x y) +
          15 * (I417.meanVol π x ^ (2 * p + 7 - ℓ) * iterPow (kernel π) (ℓ + 2) x y) +
          15 * (I417.meanVol π x ^ (2 * p + 8 - ℓ) * iterPow (kernel π) (ℓ + 1) x y))) := by
  classical
  set χ : ℝ≥0∞ := I417.meanVol π x with hχdef
  have hχsum : ∀ v : V, hubArmSum π v = χ := by
    intro v
    change (∑' z : V, (edgeMeasure π) (connSet v z)) = χ
    rw [hχdef]
    exact hχ v
  refine le_trans (I417Gen.moment_gap_tsub_le_marked π x y (p := p) (q := 4) (by norm_num)) ?_
  refine le_trans (ENNReal.tsum_le_tsum fun jw : Fin 4 × V =>
    mul_le_mul' le_rfl (tsum_freshMark_le_profile π hπ y jw.2 χ hχsum jw.1)) ?_
  rw [tsum_finFour_snd (fun w => I417Gen.jointPow π x p w * freshFourProfile π χ y w)]
  refine mul_le_mul' le_rfl ?_
  refine le_trans (ENNReal.tsum_le_tsum fun w =>
    mul_le_mul' (jointPow_le_nonplane_markedDepth π hπ χ (fun v => hχsum v) x hp w) le_rfl) ?_
  have hk : (fun a b : V => (edgeMeasure π) (connSet a b)) = kernel π := by
    funext a b
    exact (I417FreshTwo.kernel_def π a b).symm
  rw [hk]
  simp only [freshFourProfile]
  have hpush : ∀ w : V, (∑ ℓ ∈ Finset.Icc 2 (p + 1), (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
        (χ ^ (2 * p + 1 - ℓ) * iterPow (kernel π) ℓ x w)) *
        (6 * (χ ^ 4 * iterPow (kernel π) 4 w y) + 12 * (χ ^ 5 * iterPow (kernel π) 3 w y) +
          15 * (χ ^ 6 * iterPow (kernel π) 2 w y) + 15 * (χ ^ 7 * iterPow (kernel π) 1 w y)) =
      ∑ ℓ ∈ Finset.Icc 2 (p + 1), (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
        (χ ^ (2 * p + 1 - ℓ) * iterPow (kernel π) ℓ x w) *
        (6 * (χ ^ 4 * iterPow (kernel π) 4 w y) + 12 * (χ ^ 5 * iterPow (kernel π) 3 w y) +
          15 * (χ ^ 6 * iterPow (kernel π) 2 w y) + 15 * (χ ^ 7 * iterPow (kernel π) 1 w y)) := by
    intro w
    rw [Finset.sum_mul]
  simp only [hpush]
  rw [I417Base.tsum_finset_sum]
  have hterm : ∀ ℓ ∈ Finset.Icc 2 (p + 1),
      (∑' w : V, (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
        (χ ^ (2 * p + 1 - ℓ) * iterPow (kernel π) ℓ x w) *
        (6 * (χ ^ 4 * iterPow (kernel π) 4 w y) + 12 * (χ ^ 5 * iterPow (kernel π) 3 w y) +
          15 * (χ ^ 6 * iterPow (kernel π) 2 w y) + 15 * (χ ^ 7 * iterPow (kernel π) 1 w y))) =
      (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
        (6 * (χ ^ (2 * p + 5 - ℓ) * iterPow (kernel π) (ℓ + 4) x y) +
          12 * (χ ^ (2 * p + 6 - ℓ) * iterPow (kernel π) (ℓ + 3) x y) +
          15 * (χ ^ (2 * p + 7 - ℓ) * iterPow (kernel π) (ℓ + 2) x y) +
          15 * (χ ^ (2 * p + 8 - ℓ) * iterPow (kernel π) (ℓ + 1) x y)) := by
    intro ℓ hℓ
    rw [Finset.mem_Icc] at hℓ
    have hsplit : ∀ w : V, (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
          (χ ^ (2 * p + 1 - ℓ) * iterPow (kernel π) ℓ x w) *
          (6 * (χ ^ 4 * iterPow (kernel π) 4 w y) + 12 * (χ ^ 5 * iterPow (kernel π) 3 w y) +
            15 * (χ ^ 6 * iterPow (kernel π) 2 w y) + 15 * (χ ^ 7 * iterPow (kernel π) 1 w y)) =
        ((nonplaneMarkedCount p ℓ : ℝ≥0∞) * 6 *
            (χ ^ (2 * p + 1 - ℓ) * χ ^ 4) *
            (iterPow (kernel π) ℓ x w * iterPow (kernel π) 4 w y) +
          ((nonplaneMarkedCount p ℓ : ℝ≥0∞) * 12 *
              (χ ^ (2 * p + 1 - ℓ) * χ ^ 5) *
              (iterPow (kernel π) ℓ x w * iterPow (kernel π) 3 w y) +
            ((nonplaneMarkedCount p ℓ : ℝ≥0∞) * 15 *
              (χ ^ (2 * p + 1 - ℓ) * χ ^ 6) *
              (iterPow (kernel π) ℓ x w * iterPow (kernel π) 2 w y) +
            (nonplaneMarkedCount p ℓ : ℝ≥0∞) * 15 *
              (χ ^ (2 * p + 1 - ℓ) * χ ^ 7) *
              (iterPow (kernel π) ℓ x w * iterPow (kernel π) 1 w y)))) := by
      intro w
      ring
    rw [tsum_congr hsplit, ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
      ENNReal.tsum_mul_left]
    rw [iterPow_add_right (kernel π) ℓ 4 x y, iterPow_add_right (kernel π) ℓ 3 x y,
      iterPow_add_right (kernel π) ℓ 2 x y, iterPow_add_right (kernel π) ℓ 1 x y]
    have e4 : 2 * p + 1 - ℓ + 4 = 2 * p + 5 - ℓ := by omega
    have e3 : 2 * p + 1 - ℓ + 5 = 2 * p + 6 - ℓ := by omega
    have e2 : 2 * p + 1 - ℓ + 6 = 2 * p + 7 - ℓ := by omega
    have e1 : 2 * p + 1 - ℓ + 7 = 2 * p + 8 - ℓ := by omega
    rw [← pow_add, e4, ← pow_add, e3, ← pow_add, e2, ← pow_add, e1]
    ring
  rw [show (∑ ℓ ∈ Finset.Icc 2 (p + 1), ∑' w : V, (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
        (χ ^ (2 * p + 1 - ℓ) * iterPow (kernel π) ℓ x w) *
        (6 * (χ ^ 4 * iterPow (kernel π) 4 w y) + 12 * (χ ^ 5 * iterPow (kernel π) 3 w y) +
          15 * (χ ^ 6 * iterPow (kernel π) 2 w y) + 15 * (χ ^ 7 * iterPow (kernel π) 1 w y))) =
      ∑ ℓ ∈ Finset.Icc 2 (p + 1), (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
        (6 * (χ ^ (2 * p + 5 - ℓ) * iterPow (kernel π) (ℓ + 4) x y) +
          12 * (χ ^ (2 * p + 6 - ℓ) * iterPow (kernel π) (ℓ + 3) x y) +
          15 * (χ ^ (2 * p + 7 - ℓ) * iterPow (kernel π) (ℓ + 2) x y) +
          15 * (χ ^ (2 * p + 8 - ℓ) * iterPow (kernel π) (ℓ + 1) x y)) from
    Finset.sum_congr rfl hterm]

/-- The vertex-transitive version of the normalized `q = 4` moment gap. -/
theorem moment_gap_four_le_eval_transitive (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (x y : V) (p : ℕ) (hp : 1 ≤ p)
    (htrans : ∀ v : V, ∃ g : V ≃ V, (∀ e : Sym2 V, π (Sym2.map g e) = π e) ∧ g x = v) :
    I417A.momentProd π x y p 4 - I417A.rawDiff π x y p 4 ≤
      4 * (∑ ℓ ∈ Finset.Icc 2 (p + 1), (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
        (6 * (I417.meanVol π x ^ (2 * p + 5 - ℓ) * iterPow (kernel π) (ℓ + 4) x y) +
          12 * (I417.meanVol π x ^ (2 * p + 6 - ℓ) * iterPow (kernel π) (ℓ + 3) x y) +
          15 * (I417.meanVol π x ^ (2 * p + 7 - ℓ) * iterPow (kernel π) (ℓ + 2) x y) +
          15 * (I417.meanVol π x ^ (2 * p + 8 - ℓ) * iterPow (kernel π) (ℓ + 1) x y))) :=
  moment_gap_four_le_eval π hπ x y
    (I417Example.meanVol_eq_of_transitive π x htrans) p hp

/-- The former fresh-evaluation premise is now fully proved. -/
theorem freshFourEval_holds (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) :
    I417FreshFour.Refined.FreshFourEval π := by
  intro χ hχ y w j
  exact tsum_freshMark_le_profile π hπ y w χ hχ j

end PercLib.CriticalLRP.I417FreshFour.Eval

namespace PercLib.CriticalLRP.TreeExpansion

/-- The normalized `q = 4` moment-gap bound at the canonical power-law law on `ℤ^d`. -/
theorem latticeLongRange_moment_gap_four_le_eval (d : ℕ) (α : ℝ) (β : NNReal)
    (x y : Fin d → ℤ) {p : ℕ} (hp : 1 ≤ p) :
    I417A.momentProd (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β) x y p 4 -
      I417A.rawDiff (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β) x y p 4 ≤
      4 * (∑ ℓ ∈ Finset.Icc 2 (p + 1),
        (I417MarkedTransversal.nonplaneMarkedCount p ℓ : ℝ≥0∞) *
          (6 * ((I417.meanVol (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β) x) ^
            (2 * p + 5 - ℓ) * I417Base.iterPow
              (I417FreshTwo.kernel (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β))
              (ℓ + 4) x y) +
          12 * ((I417.meanVol (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β) x) ^
            (2 * p + 6 - ℓ) * I417Base.iterPow
              (I417FreshTwo.kernel (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β))
              (ℓ + 3) x y) +
          15 * ((I417.meanVol (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β) x) ^
            (2 * p + 7 - ℓ) * I417Base.iterPow
              (I417FreshTwo.kernel (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β))
              (ℓ + 2) x y) +
          15 * ((I417.meanVol (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β) x) ^
            (2 * p + 8 - ℓ) * I417Base.iterPow
              (I417FreshTwo.kernel (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β))
              (ℓ + 1) x y))) := by
  apply I417FreshFour.Eval.moment_gap_four_le_eval_transitive _
    (fun e => bernoulliEdgeProb_lt_one (lrKernel_nonneg d α) β e) x y p hp
  intro v
  let g : (Fin d → ℤ) ≃ (Fin d → ℤ) := Equiv.addRight (v - x)
  refine ⟨g, ?_, ?_⟩
  · intro e
    induction e using Sym2.ind with
    | _ a b =>
        simpa only [Sym2.map_mk, Equiv.coe_addRight, g] using
          lrKernel_unitInterval_translation_of_pair d α β a b (v - x)
  · simp [g]

end PercLib.CriticalLRP.TreeExpansion
