/-
Marked-side composition of the independently reviewed `smwxcafk7/m2` q=5 fresh evaluation.
The `Fresh/Five` family is now integrated from `smwxb4a1l/m1`. Its direct `exists_diag_q5` cover
is used; no identification of `q5Shape` with `I417GenIter.genShape` is assumed.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Five.Summed
public import PercLib.CriticalLRP.Correlation.I417.MarkedJoint.Transversal.Depth
public import PercLib.CriticalLRP.PowerLawTreeMoments

/-!
# Lemma I.4.17 at `q = 5` in the printed normalisation

The proved `q = 5` fresh-copy bound has `2q = 10` two-point factors per shape:

`∑_g P(freshMark y g j w) ≤ 24 χ⁵ T⁵(w,y) + 60 χ⁶ T⁴(w,y) + 90 χ⁷ T³(w,y) + 105 χ⁸ T²(w,y)
+ 105 χ⁹ T(w,y)`.

This file composes it with

* the generic two-copy marked expansion `I417Gen.moment_gap_tsub_le_marked` at `q = 5`
  (outer selected-arm factor `5` from `∑_{(j,w) : Fin 5 × V}`),
* the non-plane marked-depth bound `jointPow_le_nonplane_markedDepth` on `E[|K_x|^p 1(w ∈ K_x)]`

and obtains

`E|K_x|^p E|K_y|^5 − E[1(x ↮ y)|K_x|^p|K_y|^5] ≤ 5 ∑_{ℓ=2}^{p+1} C_ℓ ·
 (24 χ^{2p+6−ℓ} T^{ℓ+5} + 60 χ^{2p+7−ℓ} T^{ℓ+4} + 90 χ^{2p+8−ℓ} T^{ℓ+3}
  + 105 χ^{2p+9−ℓ} T^{ℓ+2} + 105 χ^{2p+10−ℓ} T^{ℓ+1})(x,y)`

with `C_ℓ = nonplaneMarkedCount p ℓ`, i.e. total factor count `2p + 11` per monomial
(`factorCount_five`, `factorCount_five_all`), path powers in the printed interval `[3, p+6]`
(`pathPow_range_five`). No moment or finiteness input beyond BK and the constant row sum.

The source is T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.17 and its proof (`../formalization-next/paper.txt` lines 2444--2513,
pp. 43--46), in the form already integrated for `q = 4` in
`PercLib.CriticalLRP.Correlation.I417.Fresh.Eval.Moment`.
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false
set_option linter.style.show false
set_option linter.unusedSimpArgs false
set_option linter.style.multiGoal false

@[expose] public section

namespace PercLib.CriticalLRP.I417FreshFive.Eval

open PercLib.CriticalLRP
open PercLib.CriticalLRP.I417Base
open PercLib.CriticalLRP.I417Fresh
open PercLib.CriticalLRP.I417FreshTwo
open PercLib.CriticalLRP.I417FreshFive
open PercLib.CriticalLRP.I417MarkedTransversal

variable {V : Type*} [Countable V] [DecidableEq V]

attribute [local instance] Classical.propDecidable

/-- Five choices of the marked arm contribute one common factor `5`. -/
theorem tsum_finFive_snd (f : V → ℝ≥0∞) :
    (∑' jw : Fin 5 × V, f jw.2) = 5 * ∑' w : V, f w := by
  rw [ENNReal.tsum_prod']
  have h : ∀ j : Fin 5, (∑' w : V, f (j, w).2) = ∑' w : V, f w := by
    intro j
    exact tsum_congr fun w => rfl
  rw [tsum_congr h, tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp

/-- `hubArmSum` is the mean cluster volume `E|K_v|`: both are `∑_z P(v ↔ z)`. -/
theorem hubArmSum_eq_meanVol (π : Sym2 V → unitInterval) (v : V) :
    hubArmSum π v = I417.meanVol π v := rfl

/-- **Lemma I.4.17 at `q = 5`, general constant row sum `χ`.**  For any `χ` with
`∑_z P(v ↔ z) = χ` for every `v`, total factor count `2p+11`. -/
theorem moment_gap_five_le_eval_rowSum (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (x y : V) (χ : ℝ≥0∞) (hχ : ∀ v : V, hubArmSum π v = χ) (p : ℕ) (hp : 1 ≤ p) :
    I417A.momentProd π x y p 5 - I417A.rawDiff π x y p 5 ≤
      5 * (∑ ℓ ∈ Finset.Icc 2 (p + 1), (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
        (24 * (χ ^ (2 * p + 6 - ℓ) * iterPow (kernel π) (ℓ + 5) x y) +
          60 * (χ ^ (2 * p + 7 - ℓ) * iterPow (kernel π) (ℓ + 4) x y) +
          90 * (χ ^ (2 * p + 8 - ℓ) * iterPow (kernel π) (ℓ + 3) x y) +
          105 * (χ ^ (2 * p + 9 - ℓ) * iterPow (kernel π) (ℓ + 2) x y) +
          105 * (χ ^ (2 * p + 10 - ℓ) * iterPow (kernel π) (ℓ + 1) x y))) := by
  classical
  refine le_trans (I417Gen.moment_gap_tsub_le_marked π x y (p := p) (q := 5) (by norm_num)) ?_
  refine le_trans (ENNReal.tsum_le_tsum fun jw : Fin 5 × V =>
    mul_le_mul' le_rfl (tsum_freshMark_le_profile_five π hπ y jw.2 χ hχ jw.1)) ?_
  rw [tsum_finFive_snd (fun w => I417Gen.jointPow π x p w * freshFiveProfile π χ y w)]
  refine mul_le_mul' le_rfl ?_
  refine le_trans (ENNReal.tsum_le_tsum fun w =>
    mul_le_mul' (jointPow_le_nonplane_markedDepth π hπ χ (fun v => hχ v) x hp w) le_rfl) ?_
  have hk : (fun a b : V => (edgeMeasure π) (connSet a b)) = kernel π := by
    funext a b
    exact (I417FreshTwo.kernel_def π a b).symm
  simp only [freshFiveProfile]
  rw [hk]
  have hpush : ∀ w : V, (∑ ℓ ∈ Finset.Icc 2 (p + 1), (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
        (χ ^ (2 * p + 1 - ℓ) * iterPow (kernel π) ℓ x w)) *
        (24 * (χ ^ 5 * iterPow (kernel π) 5 w y) + 60 * (χ ^ 6 * iterPow (kernel π) 4 w y) +
          90 * (χ ^ 7 * iterPow (kernel π) 3 w y) + 105 * (χ ^ 8 * iterPow (kernel π) 2 w y) +
          105 * (χ ^ 9 * iterPow (kernel π) 1 w y)) =
      ∑ ℓ ∈ Finset.Icc 2 (p + 1), (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
        (χ ^ (2 * p + 1 - ℓ) * iterPow (kernel π) ℓ x w) *
        (24 * (χ ^ 5 * iterPow (kernel π) 5 w y) + 60 * (χ ^ 6 * iterPow (kernel π) 4 w y) +
          90 * (χ ^ 7 * iterPow (kernel π) 3 w y) + 105 * (χ ^ 8 * iterPow (kernel π) 2 w y) +
          105 * (χ ^ 9 * iterPow (kernel π) 1 w y)) := by
    intro w
    rw [Finset.sum_mul]
  simp only [hpush]
  rw [I417Base.tsum_finset_sum]
  have hterm : ∀ ℓ ∈ Finset.Icc 2 (p + 1),
      (∑' w : V, (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
        (χ ^ (2 * p + 1 - ℓ) * iterPow (kernel π) ℓ x w) *
        (24 * (χ ^ 5 * iterPow (kernel π) 5 w y) + 60 * (χ ^ 6 * iterPow (kernel π) 4 w y) +
          90 * (χ ^ 7 * iterPow (kernel π) 3 w y) + 105 * (χ ^ 8 * iterPow (kernel π) 2 w y) +
          105 * (χ ^ 9 * iterPow (kernel π) 1 w y))) =
      (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
        (24 * (χ ^ (2 * p + 6 - ℓ) * iterPow (kernel π) (ℓ + 5) x y) +
          60 * (χ ^ (2 * p + 7 - ℓ) * iterPow (kernel π) (ℓ + 4) x y) +
          90 * (χ ^ (2 * p + 8 - ℓ) * iterPow (kernel π) (ℓ + 3) x y) +
          105 * (χ ^ (2 * p + 9 - ℓ) * iterPow (kernel π) (ℓ + 2) x y) +
          105 * (χ ^ (2 * p + 10 - ℓ) * iterPow (kernel π) (ℓ + 1) x y)) := by
    intro ℓ hℓ
    rw [Finset.mem_Icc] at hℓ
    have hsplit : ∀ w : V, (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
          (χ ^ (2 * p + 1 - ℓ) * iterPow (kernel π) ℓ x w) *
          (24 * (χ ^ 5 * iterPow (kernel π) 5 w y) + 60 * (χ ^ 6 * iterPow (kernel π) 4 w y) +
            90 * (χ ^ 7 * iterPow (kernel π) 3 w y) + 105 * (χ ^ 8 * iterPow (kernel π) 2 w y) +
            105 * (χ ^ 9 * iterPow (kernel π) 1 w y)) =
        ((nonplaneMarkedCount p ℓ : ℝ≥0∞) * 24 *
            (χ ^ (2 * p + 1 - ℓ) * χ ^ 5) *
            (iterPow (kernel π) ℓ x w * iterPow (kernel π) 5 w y) +
          ((nonplaneMarkedCount p ℓ : ℝ≥0∞) * 60 *
              (χ ^ (2 * p + 1 - ℓ) * χ ^ 6) *
              (iterPow (kernel π) ℓ x w * iterPow (kernel π) 4 w y) +
            ((nonplaneMarkedCount p ℓ : ℝ≥0∞) * 90 *
                (χ ^ (2 * p + 1 - ℓ) * χ ^ 7) *
                (iterPow (kernel π) ℓ x w * iterPow (kernel π) 3 w y) +
              ((nonplaneMarkedCount p ℓ : ℝ≥0∞) * 105 *
                  (χ ^ (2 * p + 1 - ℓ) * χ ^ 8) *
                  (iterPow (kernel π) ℓ x w * iterPow (kernel π) 2 w y) +
                (nonplaneMarkedCount p ℓ : ℝ≥0∞) * 105 *
                  (χ ^ (2 * p + 1 - ℓ) * χ ^ 9) *
                  (iterPow (kernel π) ℓ x w * iterPow (kernel π) 1 w y))))) := by
      intro w
      ring
    rw [tsum_congr hsplit, ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add,
      ENNReal.tsum_add]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
      ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
    rw [iterPow_add_right (kernel π) ℓ 5 x y, iterPow_add_right (kernel π) ℓ 4 x y,
      iterPow_add_right (kernel π) ℓ 3 x y, iterPow_add_right (kernel π) ℓ 2 x y,
      iterPow_add_right (kernel π) ℓ 1 x y]
    have e5 : 2 * p + 1 - ℓ + 5 = 2 * p + 6 - ℓ := by omega
    have e4 : 2 * p + 1 - ℓ + 6 = 2 * p + 7 - ℓ := by omega
    have e3 : 2 * p + 1 - ℓ + 7 = 2 * p + 8 - ℓ := by omega
    have e2 : 2 * p + 1 - ℓ + 8 = 2 * p + 9 - ℓ := by omega
    have e1 : 2 * p + 1 - ℓ + 9 = 2 * p + 10 - ℓ := by omega
    rw [← pow_add, e5, ← pow_add, e4, ← pow_add, e3, ← pow_add, e2, ← pow_add, e1]
    ring
  rw [show (∑ ℓ ∈ Finset.Icc 2 (p + 1), ∑' w : V, (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
        (χ ^ (2 * p + 1 - ℓ) * iterPow (kernel π) ℓ x w) *
        (24 * (χ ^ 5 * iterPow (kernel π) 5 w y) + 60 * (χ ^ 6 * iterPow (kernel π) 4 w y) +
          90 * (χ ^ 7 * iterPow (kernel π) 3 w y) + 105 * (χ ^ 8 * iterPow (kernel π) 2 w y) +
          105 * (χ ^ 9 * iterPow (kernel π) 1 w y))) =
      ∑ ℓ ∈ Finset.Icc 2 (p + 1), (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
        (24 * (χ ^ (2 * p + 6 - ℓ) * iterPow (kernel π) (ℓ + 5) x y) +
          60 * (χ ^ (2 * p + 7 - ℓ) * iterPow (kernel π) (ℓ + 4) x y) +
          90 * (χ ^ (2 * p + 8 - ℓ) * iterPow (kernel π) (ℓ + 3) x y) +
          105 * (χ ^ (2 * p + 9 - ℓ) * iterPow (kernel π) (ℓ + 2) x y) +
          105 * (χ ^ (2 * p + 10 - ℓ) * iterPow (kernel π) (ℓ + 1) x y)) from
    Finset.sum_congr rfl hterm]

/-- **Lemma I.4.17 at `q = 5`**, normalized at the constant row sum `χ = E|K_x|`, with total
factor count `2p+11`. -/
theorem moment_gap_five_le_eval (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1) (x y : V)
    (hχ : ∀ v : V, I417.meanVol π v = I417.meanVol π x) (p : ℕ) (hp : 1 ≤ p) :
    I417A.momentProd π x y p 5 - I417A.rawDiff π x y p 5 ≤
      5 * (∑ ℓ ∈ Finset.Icc 2 (p + 1), (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
        (24 * (I417.meanVol π x ^ (2 * p + 6 - ℓ) * iterPow (kernel π) (ℓ + 5) x y) +
          60 * (I417.meanVol π x ^ (2 * p + 7 - ℓ) * iterPow (kernel π) (ℓ + 4) x y) +
          90 * (I417.meanVol π x ^ (2 * p + 8 - ℓ) * iterPow (kernel π) (ℓ + 3) x y) +
          105 * (I417.meanVol π x ^ (2 * p + 9 - ℓ) * iterPow (kernel π) (ℓ + 2) x y) +
          105 * (I417.meanVol π x ^ (2 * p + 10 - ℓ) * iterPow (kernel π) (ℓ + 1) x y))) :=
  moment_gap_five_le_eval_rowSum π hπ x y (I417.meanVol π x)
    (fun v => (hubArmSum_eq_meanVol π v).trans (hχ v)) p hp

/-- The vertex-transitive version of the normalized `q = 5` moment gap. -/
theorem moment_gap_five_le_eval_transitive (π : Sym2 V → unitInterval) (hπ : ∀ e, π e < 1)
    (x y : V) (p : ℕ) (hp : 1 ≤ p)
    (htrans : ∀ v : V, ∃ g : V ≃ V, (∀ e : Sym2 V, π (Sym2.map g e) = π e) ∧ g x = v) :
    I417A.momentProd π x y p 5 - I417A.rawDiff π x y p 5 ≤
      5 * (∑ ℓ ∈ Finset.Icc 2 (p + 1), (nonplaneMarkedCount p ℓ : ℝ≥0∞) *
        (24 * (I417.meanVol π x ^ (2 * p + 6 - ℓ) * iterPow (kernel π) (ℓ + 5) x y) +
          60 * (I417.meanVol π x ^ (2 * p + 7 - ℓ) * iterPow (kernel π) (ℓ + 4) x y) +
          90 * (I417.meanVol π x ^ (2 * p + 8 - ℓ) * iterPow (kernel π) (ℓ + 3) x y) +
          105 * (I417.meanVol π x ^ (2 * p + 9 - ℓ) * iterPow (kernel π) (ℓ + 2) x y) +
          105 * (I417.meanVol π x ^ (2 * p + 10 - ℓ) * iterPow (kernel π) (ℓ + 1) x y))) :=
  moment_gap_five_le_eval π hπ x y
    (I417Example.meanVol_eq_of_transitive π x htrans) p hp

/-! ## The factor count `2p + 11` and the path-power interval `[3, p+6]`

The five monomials of `moment_gap_five_le_eval` are indexed by `k : ℕ` with `k ≤ 4`: the fresh-side
factor `k` is `χ^{5+k} T^{5-k}` (so `k = 0` is `χ⁵ T⁵` and `k = 4` is `χ⁹ T`), and after composition
with `C_ℓ χ^{2p+1-ℓ} T^ℓ` the `χ`-exponent is `2p+6+k-ℓ` and the `T`-exponent is `ℓ+5-k`.  The two
exponents sum to `2p+11`. -/

/-- **Total factor count at `q = 5`.**  For every `ℓ ∈ [2, p+1]` and every fresh-side branch
`k ≤ 4`, a monomial of the composed bound has `χ`-exponent plus `T`-exponent equal to `2p + 11`:
the `2p+1` factors of the marked side plus the `2q = 10` factors of the fresh side. -/
theorem factorCount_five (p ℓ k : ℕ) (hℓ : ℓ ≤ p + 1) (hk : k ≤ 4) :
    (2 * p + 6 + k - ℓ) + (ℓ + 5 - k) = 2 * p + 11 := by
  omega

/-- The same count, with the fresh-side branch written by its path power `j = 5 - k ∈ [1,5]`:
`χ`-exponent `2p + 11 - (ℓ+j)` and `T`-exponent `ℓ+j`. -/
theorem factorCount_five_all (p ℓ j : ℕ) (hℓ : ℓ ≤ p + 1) (hj : 1 ≤ j) (hj5 : j ≤ 5) :
    (2 * p + 11 - (ℓ + j)) + (ℓ + j) = 2 * p + 11 := by
  omega

/-- **Path-power interval at `q = 5`.**  With `2 ≤ ℓ ≤ p+1` the marked-side power `ℓ` and a
fresh-side power `j ∈ [1,5]` give `ℓ + j ∈ [3, p+6]`, the printed interval. -/
theorem pathPow_range_five (p ℓ j : ℕ) (hℓ2 : 2 ≤ ℓ) (hℓ : ℓ ≤ p + 1) (hj : 1 ≤ j)
    (hj5 : j ≤ 5) :
    3 ≤ ℓ + j ∧ ℓ + j ≤ p + 6 := by
  omega

end PercLib.CriticalLRP.I417FreshFive.Eval

namespace PercLib.CriticalLRP.TreeExpansion

/-- The normalized `q = 5` moment-gap bound at the canonical power-law law on `ℤ^d`. -/
theorem latticeLongRange_moment_gap_five_le_eval (d : ℕ) (α : ℝ) (β : NNReal)
    (x y : Fin d → ℤ) {p : ℕ} (hp : 1 ≤ p) :
    I417A.momentProd (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β) x y p 5 -
      I417A.rawDiff (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β) x y p 5 ≤
      5 * (∑ ℓ ∈ Finset.Icc 2 (p + 1),
        (I417MarkedTransversal.nonplaneMarkedCount p ℓ : ℝ≥0∞) *
          (24 * ((I417.meanVol (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β) x) ^
            (2 * p + 6 - ℓ) * I417Base.iterPow
              (I417FreshTwo.kernel (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β))
              (ℓ + 5) x y) +
          60 * ((I417.meanVol (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β) x) ^
            (2 * p + 7 - ℓ) * I417Base.iterPow
              (I417FreshTwo.kernel (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β))
              (ℓ + 4) x y) +
          90 * ((I417.meanVol (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β) x) ^
            (2 * p + 8 - ℓ) * I417Base.iterPow
              (I417FreshTwo.kernel (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β))
              (ℓ + 3) x y) +
          105 * ((I417.meanVol (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β) x) ^
            (2 * p + 9 - ℓ) * I417Base.iterPow
              (I417FreshTwo.kernel (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β))
              (ℓ + 2) x y) +
          105 * ((I417.meanVol (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β) x) ^
            (2 * p + 10 - ℓ) * I417Base.iterPow
              (I417FreshTwo.kernel (bernoulliEdgeProb (lrKernel d α) (lrKernel_nonneg d α) β))
              (ℓ + 1) x y))) := by
  apply PercLib.CriticalLRP.I417FreshFive.Eval.moment_gap_five_le_eval_transitive _
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
