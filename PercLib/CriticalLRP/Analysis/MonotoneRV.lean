/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Doubling and reverse doubling for regularly varying functions, as stated in
T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, p. 27:

  "Finally, let us mention that an increasing function f : [1,∞) → (0,∞) is said
   to be *doubling* if there exists a constant C such that f(2x) ≤ C f(x) for
   every x ≥ 1, so that increasing functions of regular variation are always
   doubling.  An increasing function f : [1,∞) → (0,∞) is said to be *reverse
   doubling* if its inverse is doubling, or equivalently if there exists a
   constant C such that f(Cx) ≥ 2 f(x) for every x ≥ 1; positive, increasing
   functions with regular variation of positive index are both doubling and
   reverse-doubling."

Both claims are immediate from the definition `RegularlyVaryingAtTop` at the
single point `λ = 2`, respectively at a large `λ = C`; no uniform convergence
theorem is needed (and none is used).  Note that neither statement needs
monotonicity: it is a hypothesis in the paper only because the paper's functions
are increasing.

The remaining statements on p. 27-28 ("f is doubling", "f^{-1} is doubling",
etc.) are properties of the specific inequalities `f(2x) ≤ C f(x)`,
`f(Cx) ≥ 2 f(x)`; formalising them as such is `doubling_of_regularlyVarying`
and `reverse_doubling_of_regularlyVarying` below.
-/
module

public import PercLib.CriticalLRP.Analysis.RegularVariation

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open Filter Set MeasureTheory
open scoped Topology

namespace PercLib.CriticalLRP.Analysis

/-- **Increasing functions of regular variation are doubling** (paper, p. 27):
if `f` is regularly varying of index `ρ` and eventually positive, then
`f (2 x) ≤ C f x` for all large `x`. -/
theorem doubling_of_regularlyVarying {f : ℝ → ℝ} {ρ : ℝ}
    (hrv : RegularlyVaryingAtTop f ρ) (hp : ∀ᶠ x in atTop, 0 < f x) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x in atTop, f (2 * x) ≤ C * f x := by
  refine ⟨2 ^ ρ + 1, by positivity, ?_⟩
  have h2 : Tendsto (fun x => f (2 * x) / f x) atTop (𝓝 (2 ^ ρ)) := hrv.2 2 (by norm_num)
  have hev : ∀ᶠ x in atTop, f (2 * x) / f x < 2 ^ ρ + 1 :=
    h2.eventually (eventually_lt_nhds (lt_add_one (2 ^ ρ)))
  filter_upwards [hev, hp] with x hx hxpos
  rw [div_lt_iff₀ hxpos] at hx
  linarith

/-- **Positive-index regularly varying functions are reverse doubling**
(paper, p. 27): there is `C > 0` with `2 f x ≤ f (C x)` for all large `x`. -/
theorem reverse_doubling_of_regularlyVarying {f : ℝ → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hrv : RegularlyVaryingAtTop f ρ) (hp : ∀ᶠ x in atTop, 0 < f x) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ x in atTop, 2 * f x ≤ f (C * x) := by
  obtain ⟨C, hC1, hC2⟩ : ∃ C : ℝ, 1 ≤ C ∧ (3 : ℝ) ≤ C ^ ρ := by
    refine ⟨max 2 ((3 : ℝ) ^ (1 / ρ) + 1), le_trans (by norm_num) (le_max_left _ _), ?_⟩
    have h3 : (0:ℝ) ≤ 3 := by norm_num
    have hbase : (3 : ℝ) ^ (1 / ρ) ≤ max 2 ((3 : ℝ) ^ (1 / ρ) + 1) := by
      linarith [le_max_right (2:ℝ) ((3 : ℝ) ^ (1 / ρ) + 1)]
    have hmono : ((3 : ℝ) ^ (1 / ρ)) ^ ρ ≤ (max 2 ((3 : ℝ) ^ (1 / ρ) + 1)) ^ ρ :=
      Real.rpow_le_rpow (Real.rpow_nonneg h3 _) hbase hρ.le
    have hval : ((3 : ℝ) ^ (1 / ρ)) ^ ρ = 3 := by
      rw [← Real.rpow_mul h3, one_div_mul_cancel hρ.ne', Real.rpow_one]
    linarith
  refine ⟨C, hC1, ?_⟩
  have h2 : Tendsto (fun x => f (C * x) / f x) atTop (𝓝 (C ^ ρ)) :=
    hrv.2 C (lt_of_lt_of_le one_pos hC1)
  have hev : ∀ᶠ x in atTop, (2:ℝ) < f (C * x) / f x :=
    h2.eventually (eventually_gt_nhds (by linarith : (2:ℝ) < C ^ ρ))
  filter_upwards [hev, hp] with x hx hxpos
  rw [lt_div_iff₀ hxpos] at hx
  linarith

end PercLib.CriticalLRP.Analysis

/-! ### Axiom audit -/

#print axioms PercLib.CriticalLRP.Analysis.doubling_of_regularlyVarying
#print axioms PercLib.CriticalLRP.Analysis.reverse_doubling_of_regularlyVarying
