/- Integrated from independently rebuilt Ultramath work, base revision 4140ac56119d2cd80995f91886669efe004839d5.
Scratch source: ../../.ultramath/smwqozn0q/m3/Witness.lean ; `T1` moved to Defs.lean.
-/
module

/-
Direction C (m3, swarm smwqozn0q): a non-vacuity witness for the hypothesis bundle.

`polygon_bound` is conditional on `PowerInputs` plus the scalar inputs.  This file instantiates
*all* of them concretely (one-point space, kernel `T ≡ 1`, `χ = ∇ = 1`) and derives the conclusion,
so the hypothesis list is jointly satisfiable and the arithmetic is consistent.
-/
public import PercLib.CriticalLRP.Analysis.Polygon.Core

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open scoped BigOperators

@[expose] public section

namespace PercLib.CriticalLRP.I418C

@[simp] theorem T1_apply (x y : PUnit) : T1 x y = 1 := rfl

/-- Every matrix power of the constant-one kernel on the one-point space is `1`. -/
theorem polyK_T1 (m : ℕ) (x y : PUnit) : polyK T1 m x y = 1 := by
  induction m generalizing x y with
  | zero => simp [polyK_zero]
  | succ m ih =>
    rw [polyK_succ]
    have : ∀ z : PUnit, polyK T1 m x z * T1 z y = 1 := by
      intro z; rw [ih, T1_apply, mul_one]
    rw [tsum_congr this]
    simp

/-- **Non-vacuity**: on the one-point space with kernel `T ≡ 1`, `∇ ≡ 1`, `∇_β = χ = 1`, every
field of `PowerInputs` holds. -/
theorem witness_inputs :
    PowerInputs (V := PUnit) (polyK T1) 1 1 where
  nonneg n x y := polyK_nonneg _ (fun _ _ => zero_le_one) n x y
  base x y := polyK_zero _ x y
  comp n := by simp [polyK_T1]
  compSummable n := Summable.of_finite
  colsum n := by simp [polyK_T1]
  colSummable n := Summable.of_finite
  entry n _ y := by simp [polyK_T1]
  selfOne := polyK_T1 1 0 0
  triSup y := by simp [polyK_T1]

/-- The assembled estimate of Lemma I.4.18 instantiated at `ℓ = 4`, `r = 1`, `α = d = c₀ = K = 1`,
`s = univ`, `∇_{r^c} = 0`: both sides evaluate to `1`. -/
theorem witness_bound :
    polyK T1 4 0 0
      ≤ max 1 ((1 : ℝ) * 1 / 1) * (0 + (1 : ℝ) ^ (-(1 / (4 * (1 : ℝ))))) * (1 : ℝ) ^ (4 - 3) := by
  have h := polygon_bound (P := polyK T1)
    (nablaT := 1) (χ := 1) witness_inputs (Finset.univ : Finset PUnit) (fun _ => 0)
    (r := 1) (R := 1) (trc := 0) (d := 1) (α := 1) (c₀ := 1) (K := 1)
    (cc := 1 / (4 * (1 : ℝ))) (ell := 4)
    one_pos (by norm_num) one_pos zero_le_one le_rfl (by norm_num) (by norm_num)
    (by intro y hy; simp at hy)
    (by intro y hy; linarith)
    le_rfl (by norm_num) (by norm_num) (by norm_num)
  simpa using h

end PercLib.CriticalLRP.I418C
