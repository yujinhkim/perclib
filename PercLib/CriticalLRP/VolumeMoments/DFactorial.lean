/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1.

The odd double factorial in the paper's normalisation,
`(2n-1)!! = 1·3·5···(2n-1)` with the empty-product convention `(-1)!! = 0!! = 1`
(paper p. 10: "the product of all odd integers between 1 and 2p-3").

We use a product definition rather than `Nat.doubleFactorial` because every index
occurring in Lemma I.4.23 / Proposition I.4.20 is of the form `2k-1`, and the
product form makes the recurrence `M(n+1) = (2n+1)M(n)` hold with no case split
and no truncated subtraction.
-/
module

public import Mathlib

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open Finset

namespace PercLib.CriticalLRP.VolumeMoments

/-- `M n = (2n-1)!! = ∏_{i<n}(2i+1)`, i.e. `1·3·5···(2n-1)`; `M 0 = 1` encodes
the empty product `(-1)!! = 1`. -/
def M (n : ℕ) : ℕ := ∏ i ∈ Finset.range n, (2 * i + 1)

@[simp] lemma M_zero : M 0 = 1 := by simp [M]

@[simp] lemma M_one : M 1 = 1 := by simp [M]

@[simp] lemma M_two : M 2 = 3 := by decide

@[simp] lemma M_three : M 3 = 15 := by decide

@[simp] lemma M_four : M 4 = 105 := by decide

/-- The recurrence `(2n+1)!! = (2n+1)·(2n-1)!!`. -/
theorem M_succ (n : ℕ) : M (n + 1) = (2 * n + 1) * M n := by
  rw [M, Finset.prod_range_succ, M]
  ring

/-- `M` is positive (needed to divide by it, and for non-degeneracy). -/
theorem M_pos (n : ℕ) : 0 < M n := by
  rw [M]
  exact Finset.prod_pos fun i _ => by omega

theorem M_ne_zero (n : ℕ) : M n ≠ 0 := (M_pos n).ne'

/-- `M` is strictly increasing from `1` on. -/
theorem M_lt_M_succ {n : ℕ} (hn : 1 ≤ n) : M n < M (n + 1) := by
  rw [M_succ]
  have := M_pos n
  nlinarith

/-- For `n ≥ 1`, `M n` is the odd double factorial `(2n-1)‼` of Mathlib. -/
theorem M_eq_doubleFactorial (n : ℕ) : M (n + 1) = Nat.doubleFactorial (2 * n + 1) := by
  rw [Nat.doubleFactorial_eq_prod_odd, M, Finset.prod_range_succ']
  simp

end PercLib.CriticalLRP.VolumeMoments
