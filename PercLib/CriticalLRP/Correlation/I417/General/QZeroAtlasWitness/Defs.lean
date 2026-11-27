/-
Ultramath swarm `smwziumdb`, member `m1`, direction `d7`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwziumdb`.
Supporting integration based on production commit `5d2d681b941eb1c687f1ba17e6a798b8f0175aa0`.

# The constant-kernel witness for the `q = 0` atlas exponent ledger

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1.  Lemma I.4.17 (p. 45) and its proof (pp. 45-46); Lemma I.4.18 (p. 46);
proof of Proposition I.4.15, Case 3 (p. 47); printed pp. 42-47.

## What this file is for

The accepted `q = 0`, `p = 3` atlas (`PercLib.CriticalLRP.QZeroAtlas`, integrated from swarm
`smwzg77c3` member `m1`) records four shape evaluations and their assembly

  `atlas D v y ≤ 3 χ⁵ k²(v,y) + 6 χ⁴ k³(v,y) + 6 χ³ k⁴(v,y)`,

where `χ = D.χ` and `k^ℓ = kpow D.k ℓ`.  Every step of that computation is an *upper* bound:
one row sum `∑_z k a z ≤ χ` per label and per off-path vertex.  The exponent ledger that the
Case-3 consumer reads off it therefore has two questions attached:

1. are the four exponents `χ⁵k²`, `χ⁴k³`, `χ⁴k³`, `χ³k⁴` sharp, or is the atlas bound wasting
   powers of `χ`?
2. is the *window* total — the quantity the Case-3 numerator actually consumes — genuinely
   `Θ(χ⁷)`, or can a better summation order in the atlas reduce it?

This file answers both with one explicit witness.  `constKernel n` is the constant kernel `≡ 1`
on `Fin n`; its `KernelData` package has `χ = n`, and in it

* all four shapes evaluate to exactly `n ^ 6` — *simultaneously*, so each of the four accepted
  shape targets is attained with equality (`shapeTwo_sharp`, `shapeThreeA_sharp`,
  `shapeThreeB_sharp`, `shapeFour_sharp` in `Main.lean`);
* the atlas evaluates to `15 * n ^ 6`, and its window total over `Fin n` is `15 * n ^ 7`
  (`atlas_window_sum_const`), i.e. the `χ⁷` ledger of the window sum is attained and no
  reordering or constant improvement inside the atlas can lower it.

Since every entry of the witness kernel is `≤ 1`, symmetric, has unit diagonal and row sums
exactly `χ`, the witness satisfies exactly the `KernelData` hypotheses under which the accepted
atlas was proved; so the sharpness statements are statements about the accepted packet, not
about a larger hypothesis class.

## The exponent consequence (see `Main.lean`)

Write `15 χ⁷ = χ⁴ · (15 χ³)`: the atlas window total forces the *effective driver* of the
`q = 0` route to be at least `C χ³`, whatever the kernel.  In the source's Case-3
parametrisation `χ ≍ r^α`, `|B_r| ≍ r^d` (with `d ≤ 3α` in Case 3) the corresponding
normalized residual is `χ⁴ / |B_r| ≍ r ^ (4α - d) ≥ r ^ α`, which does not vanish.  That is the
exact sense in which the `q = 0` atlas ledger cannot reach the Case-3 target without an extra
input on the `ℓ = 2` class beyond `KernelData` — the arithmetic is `case3_exponent_ledger` in
`Main.lean`.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.QZeroAtlas.Defs
public import Mathlib

/-! # The constant-kernel witness -/

noncomputable section

open MeasureTheory Measure ProbabilityTheory
open scoped ENNReal NNReal

@[expose] public section

namespace PercLib.CriticalLRP.QZeroAtlas

attribute [local instance] Classical.propDecidable

/-! ## The witness kernel -/

/-- The constant kernel `≡ 1` on `Fin n`.  This is the extremal member of the `KernelData` class
for the atlas: every entry sits at the maximum value `1` allowed by `le_one`, and the row sums
are exactly the susceptibility. -/
def constKernel (n : ℕ) : Fin n → Fin n → ℝ≥0∞ := fun _ _ => 1

/-- The row sum of the constant kernel is `n`, so the extremal `KernelData` package on `Fin n`
has `χ = n`. -/
theorem constKernel_rowSum (n : ℕ) (a : Fin n) :
    (∑' z : Fin n, constKernel n a z) = (n : ℝ≥0∞) := by
  simp [constKernel]

/-- **The constant kernel as `KernelData`.**  It satisfies every hypothesis of the accepted
atlas (`QZeroAtlas.KernelData`: symmetry, entries `≤ 1`, unit diagonal, row sums `≤ χ`) with
`χ = n`.  This is the witness on which the four shape bounds are attained. -/
def constKernelData (n : ℕ) : KernelData (Fin n) where
  k := constKernel n
  χ := (n : ℝ≥0∞)
  symm := fun _ _ => rfl
  le_one := fun _ _ => le_refl 1
  diag := fun _ => rfl
  row := fun a => (constKernel_rowSum n a).le

@[simp] theorem constKernelData_k (n : ℕ) :
    (constKernelData n).k = constKernel n := rfl

@[simp] theorem constKernelData_chi (n : ℕ) : (constKernelData n).χ = (n : ℝ≥0∞) := rfl

/-- The window at the scale of the whole witness space: the Case-3 window `B_r` is a finite set
of vertices, and `Finset.univ` is the extremal choice of it. -/
def fullWindow (n : ℕ) : Finset (Fin n) := Finset.univ

@[simp] theorem fullWindow_card (n : ℕ) : (fullWindow n).card = n := by
  simp [fullWindow]

end PercLib.CriticalLRP.QZeroAtlas
