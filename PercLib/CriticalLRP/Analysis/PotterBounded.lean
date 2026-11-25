/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
**From local uniform convergence to bounded-ratio Potter bounds.**

The classical route to Potter's bounds (Bingham–Goldie–Teugels, Theorem 1.5.6)
goes through the uniform convergence theorem (BGT Theorem 1.2.1): one first
proves that `f (λ x)/f x → λ^α` uniformly for `λ` in a compact subset of
`(0,∞)`, and then converts that statement into two-sided power bounds.

This file isolates the *second* step, which is elementary: if the ratios
converge uniformly near `1`, then for every `c ≥ 1` and every `ε > 0` one gets
Potter-type bounds with constants `1 ± ε` and exponents `α ± ε` valid for all
`1 ≤ x/y ≤ c`.  This is exactly the form of Potter's bounds that the proof of
Karamata's integral theorem (paper Lemma I.2.10) consumes, since there the
ratios `x/y` range over the compact interval `[δ, 1/δ]`.

The remaining input, not proved here, is the uniform convergence theorem itself:
for measurable regularly varying `f`, `f (λ x) / f x → λ^α` uniformly for `λ`
in a compact subset of `(0,∞)`.  That statement is `HasLocalUniformRatio` below
(for `λ ∈ [1, 1+δ]`), and it does not follow from the pointwise definition by
any argument available in this development.
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

/-- **Local uniform convergence of the ratios near `1`** — the conclusion of the
uniform convergence theorem (BGT Theorem 1.2.1), in the one-sided form needed
for Potter's bounds. -/
def HasLocalUniformRatio (f : ℝ → ℝ) (α : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η → ∃ X : ℝ, 1 ≤ X ∧ ∀ y : ℝ, X ≤ y →
    ∀ l ∈ Set.Icc (1 : ℝ) (1 + δ), |f (l * y) / f y - l ^ α| ≤ η

/-! ### Iterating a single-step ratio bound along a geometric progression -/

/-- Single-step upper bound iterated along `z ↦ λ z`. -/
theorem telescope_le {f : ℝ → ℝ} {lam X C y : ℝ} (k : ℕ) (hX : 0 < X) (hy : X ≤ y)
    (hlam : 1 ≤ lam) (hC : 0 ≤ C)
    (hf : ∀ z : ℝ, X ≤ z → |f (lam * z)| ≤ C * |f z|) :
    |f (y * lam ^ k)| ≤ C ^ k * |f y| := by
  induction k with
  | zero => simp
  | succ n ih =>
    have hge : X ≤ y * lam ^ n := by
      have h2 : (1:ℝ) ≤ lam ^ n := one_le_pow₀ hlam
      nlinarith
    have hstep : |f (lam * (y * lam ^ n))| ≤ C * |f (y * lam ^ n)| := hf _ hge
    have hpow : |f (y * lam ^ (n + 1))| = |f (lam * (y * lam ^ n))| := by
      rw [pow_succ]; ring_nf
    rw [hpow]
    calc |f (lam * (y * lam ^ n))| ≤ C * |f (y * lam ^ n)| := hstep
      _ ≤ C * (C ^ n * |f y|) := by
          apply mul_le_mul_of_nonneg_left ih hC
      _ = C ^ (n + 1) * |f y| := by ring

/-- Single-step lower bound iterated along `z ↦ lam z`. -/
theorem telescope_ge {f : ℝ → ℝ} {lam X C y : ℝ} (k : ℕ) (hX : 0 < X) (hy : X ≤ y)
    (hlam : 1 ≤ lam) (hC : 0 ≤ C)
    (hf : ∀ z : ℝ, X ≤ z → C * |f z| ≤ |f (lam * z)|) :
    C ^ k * |f y| ≤ |f (y * lam ^ k)| := by
  induction k with
  | zero => simp
  | succ n ih =>
    have hge : X ≤ y * lam ^ n := by
      have h2 : (1:ℝ) ≤ lam ^ n := one_le_pow₀ hlam
      nlinarith
    have hstep : C * |f (y * lam ^ n)| ≤ |f (lam * (y * lam ^ n))| := hf _ hge
    have hpow : |f (y * lam ^ (n + 1))| = |f (lam * (y * lam ^ n))| := by
      rw [pow_succ]; ring_nf
    rw [hpow]
    calc C ^ (n + 1) * |f y| = C * (C ^ n * |f y|) := by ring
      _ ≤ C * |f (y * lam ^ n)| := by
          apply mul_le_mul_of_nonneg_left ih hC
      _ ≤ |f (lam * (y * lam ^ n))| := hstep


/-- For `1 ≤ τ ≤ c` and any exponent `β`, `τ ^ β` is bounded below by
`min 1 (c ^ β)`. -/
theorem rpow_ge_min {τ c β : ℝ} (hτ : 1 ≤ τ) (hτc : τ ≤ c) :
    min 1 (c ^ β) ≤ τ ^ β := by
  rcases le_or_gt 0 β with hβ | hβ
  · exact le_trans (min_le_left _ _) (Real.one_le_rpow hτ hβ)
  · refine le_trans (min_le_right _ _) ?_
    exact Real.rpow_le_rpow_of_nonpos (by linarith) hτc (le_of_lt hβ)

end PercLib.CriticalLRP.Analysis

/-! ### Axiom audit -/

#print axioms PercLib.CriticalLRP.Analysis.telescope_le
#print axioms PercLib.CriticalLRP.Analysis.telescope_ge
#print axioms PercLib.CriticalLRP.Analysis.rpow_ge_min
