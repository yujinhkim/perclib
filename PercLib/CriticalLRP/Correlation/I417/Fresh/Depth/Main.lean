/-
Independently rebuilt from accepted `smwxb4a1l/m2` coefficient artifacts.
Production revision `d9a001b7f0a33cf6395158f7621ad4de1fe3c7c8`.
Only the finite range/cardinality results are integrated; this does not prove
the arbitrary-q weighted fresh evaluation or the further geometric link lemmas
outlined in the artifact narrative.
-/
/-
Independently built for swarm `smwxb4a1l`, member `m2`, direction
`GENERAL-Q-STRUCTURAL-GAP-AUDIT`.  Proofs only; every definition is in `QDeep/Defs.lean`.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Depth.Defs

/-!
# The pin--mark path length of the iterated first-hit fresh cover: proofs

Source: Lemma I.4.17 of T. Hutchcroft, *Critical long-range percolation I: High effective
dimension* (arXiv:2508.18807v1), supplied text pp. 43--46.  See `QDeep/Defs.lean` for what is
defined and why.

Contents: the recursive pin--mark cardinality machinery, finite coefficient
rows through `q = 5`, the fresh monomial range, and identification with
`I417Fresh.Subdivision.freshPoly`. No weighted evaluation of `genShape`,
no `legs_wSlot` and no endpoint-connectivity proof is claimed here.
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false

@[expose] public section

namespace PercLib.CriticalLRP.I417FreshDepth

open PercLib.CriticalLRP
open PercLib.CriticalLRP.I417GenIter

variable {V : Type*} [Countable V] [DecidableEq V]

/-! ## The path length is at most the number of arms -/

/-- Every branch `k` on `Fin (n+1)` is its own one-round extension. -/
theorem snoc_self {n : ℕ} (k : (t : Fin (n + 1)) → Idx t) :
    Fin.snoc (α := fun t : Fin (n + 1) => Idx t.val)
      (fun t : Fin n => k t.castSucc) (k (Fin.last n)) = k := by
  funext t
  exact Fin.lastCases
    (motive := fun t => Fin.snoc (α := fun t : Fin (n + 1) => Idx t.val)
      (fun t : Fin n => k t.castSucc) (k (Fin.last n)) t = k t)
    (by simp) (fun j => by simp) t

/-- **The successor law of the pin--mark path length**: one more attachment round either lengthens
the path by one leg (if the split leg is on the path) or leaves it unchanged. -/
theorem markDepthK_succ {n : ℕ} (f : (t : Fin n) → Idx t) (i : Idx n) :
    markDepthK (n + 1) (Fin.snoc (α := fun t : Fin (n + 1) => Idx t.val) f i) =
      markDepthK n f + if i ∈ pathLegsK n f then 1 else 0 := by
  have h1 : (fun t : Fin n =>
      Fin.snoc (α := fun t : Fin (n + 1) => Idx t.val) f i t.castSucc) = f := by
    funext t; simp
  have h2 : Fin.snoc (α := fun t : Fin (n + 1) => Idx t.val) f i (Fin.last n) = i := by simp
  simp only [markDepthK, h1, h2]

/-- **The pin--mark path has at least one leg.** -/
theorem markDepthK_pos {n : ℕ} (k : (t : Fin n) → Idx t) : 1 ≤ markDepthK n k := by
  induction n with
  | zero => simp [markDepthK]
  | succ n ih =>
    rw [← snoc_self k, markDepthK_succ]
    have := ih (fun t : Fin n => k t.castSucc)
    split_ifs <;> omega

/-- **The pin--mark path has at most `n + 1` legs** — at `n = q - 1` the printed `T`-power range
`ℓ ∈ [1,q]` of the fresh normal form, derived from the leg model rather than assumed. -/
theorem markDepthK_le {n : ℕ} (k : (t : Fin n) → Idx t) : markDepthK n k ≤ n + 1 := by
  induction n with
  | zero => simp [markDepthK]
  | succ n ih =>
    rw [← snoc_self k, markDepthK_succ]
    have := ih (fun t : Fin n => k t.castSucc)
    split_ifs <;> omega

/-- The same for a history of the iterated first-hit cover. -/
theorem markDepth_bounds {n : ℕ} (H : Hist V n) :
    1 ≤ markDepth H ∧ markDepth H ≤ n + 1 :=
  ⟨markDepthK_pos (splitChoices H), markDepthK_le (splitChoices H)⟩

/-- **The fresh monomial range at `q`**: with `ℓ = markDepth H` for a history of length `q - 1`, the
normal form `χ^(2q-ℓ) T^ℓ` has `2q` edges in total, `T`-power in `[1,q]` and `χ`-exponent in
`[q, 2q-1]`. -/
theorem markDepth_monomial_range {q : ℕ} (H : Hist V (q - 1)) (hq : 1 ≤ q) :
    1 ≤ markDepth H ∧ markDepth H ≤ q ∧ q ≤ 2 * q - markDepth H ∧
      (2 * q - markDepth H) + markDepth H = 2 * q := by
  obtain ⟨h1, h2⟩ := markDepth_bounds H
  omega

/-! ## The coefficient cardinalities `C_ℓ` at `q = 1, …, 5` -/

/-- `q = 1`: one branch, path length `1`. -/
theorem depthCount_zero : depthCount 0 1 = 1 := by decide

/-- `q = 2`: the two branches have path length `1` and `2` (total `2`). -/
theorem depthCount_one : depthCount 1 1 = 1 ∧ depthCount 1 2 = 1 := by decide

/-- `q = 3`: coefficients `(3,3,2)` at `ℓ = 1,2,3`, total `8 = 2·4`. -/
theorem depthCount_two :
    depthCount 2 1 = 3 ∧ depthCount 2 2 = 3 ∧ depthCount 2 3 = 2 := by decide

/-- `q = 4`: coefficients `(15,15,12,6)` at `ℓ = 1,2,3,4`, total `48 = 2·4·6`.  These are exactly
the coefficients of production's accepted `I417FreshFour.Eval.freshFourProfile`
`6 χ⁴T⁴ + 12 χ⁵T³ + 15 χ⁶T² + 15 χ⁷T` (coefficient of `T^ℓ` is `C_ℓ`). -/
theorem depthCount_three :
    depthCount 3 1 = 15 ∧ depthCount 3 2 = 15 ∧ depthCount 3 3 = 12 ∧
      depthCount 3 4 = 6 := by
  set_option maxRecDepth 40000 in
  set_option maxHeartbeats 4000000 in
    decide

/-- `q = 5`: coefficients `(105,105,90,60,24)` at `ℓ = 1,…,5`, total `384 = 2·4·6·8`.  These are
the coefficients of the `q = 5` split-construction profile
`24χ⁵T⁵ + 60χ⁶T⁴ + 90χ⁷T³ + 105χ⁸T² + 105χ⁹T`. -/
theorem depthCount_four :
    depthCount 4 1 = 105 ∧ depthCount 4 2 = 105 ∧ depthCount 4 3 = 90 ∧
      depthCount 4 4 = 60 ∧ depthCount 4 5 = 24 := by
  set_option maxRecDepth 40000 in
  set_option maxHeartbeats 4000000 in
    decide

/-- The totals: the coefficients sum to the number of branches, `2^(q-1) (q-1)!` (production's
`card_histChoices`). -/
theorem depthCount_total :
    (∑ ℓ ∈ Finset.Icc 1 1, depthCount 0 ℓ) = 1 ∧
      (∑ ℓ ∈ Finset.Icc 1 2, depthCount 1 ℓ) = 2 ∧
        (∑ ℓ ∈ Finset.Icc 1 3, depthCount 2 ℓ) = 8 ∧
          (∑ ℓ ∈ Finset.Icc 1 4, depthCount 3 ℓ) = 48 ∧
            (∑ ℓ ∈ Finset.Icc 1 5, depthCount 4 ℓ) = 384 := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  set_option maxRecDepth 40000 in
  set_option maxHeartbeats 4000000 in
    decide

/-- The `q = 5` coefficients in the form used by the split profile. -/
theorem genCoeff_five :
    genCoeff 5 1 = 105 ∧ genCoeff 5 2 = 105 ∧ genCoeff 5 3 = 90 ∧
      genCoeff 5 4 = 60 ∧ genCoeff 5 5 = 24 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [genCoeff] using depthCount_four.1
  · simpa [genCoeff] using depthCount_four.2.1
  · simpa [genCoeff] using depthCount_four.2.2.1
  · simpa [genCoeff] using depthCount_four.2.2.2.1
  · simpa [genCoeff] using depthCount_four.2.2.2.2

/-- The `q = 4` coefficients in the same form. -/
theorem genCoeff_four :
    genCoeff 4 1 = 15 ∧ genCoeff 4 2 = 15 ∧ genCoeff 4 3 = 12 ∧ genCoeff 4 4 = 6 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [genCoeff] using depthCount_three.1
  · simpa [genCoeff] using depthCount_three.2.1
  · simpa [genCoeff] using depthCount_three.2.2.1
  · simpa [genCoeff] using depthCount_three.2.2.2

/-- The `q = 3` coefficients in the same form. -/
theorem genCoeff_three :
    genCoeff 3 1 = 3 ∧ genCoeff 3 2 = 3 ∧ genCoeff 3 3 = 2 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [genCoeff] using depthCount_two.1
  · simpa [genCoeff] using depthCount_two.2.1
  · simpa [genCoeff] using depthCount_two.2.2

/-- **`genFreshProfile` is production's `freshPoly` normalisation** with the cover's own
coefficients `genCoeff q`: the general-`q` fresh polynomial of Lemma I.4.17 with `C_ℓ` the number of
branches of the iterated first-hit cover whose pin--mark path has length `ℓ`. -/
theorem genFreshProfile_eq_freshPoly {V : Type*} [Countable V] [DecidableEq V]
    (k : V → V → ℝ≥0∞) (χ : ℝ≥0∞) (q : ℕ) (v w : V) :
    genFreshProfile k χ q v w =
      PercLib.CriticalLRP.I417Fresh.Subdivision.freshPoly k χ q (genCoeff q) v w := rfl

end PercLib.CriticalLRP.I417FreshDepth
