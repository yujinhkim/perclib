/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.23 (p. 49):

  `∑_{k=0}^{n-1} C(n,k) (2k-1)!! (2n-2k-3)!! = (2n-1)!!`  for every `n ≥ 2`.

The paper proves this by multiplying the exponential generating functions
`∑ (2n-1)!! xⁿ/n! = (1-2x)^{-1/2}` and `∑ (2n-3)!! xⁿ/n! = 1 - √(1-2x)`.
Since Mathlib has no binomial series `(1-2x)^{-1/2}` in `PowerSeries`, we give a
self-contained induction instead; it is the same identity and the same
constant, and the proof is complete for **every** `n ≥ 1`
(the paper only needs `n ≥ 2`; `n = 1` holds as well).

Notation: `dd m = (2m-1)‼`.  Because `ℕ`-subtraction is truncated, `dd 0 = 0‼ = 1`,
which is exactly the convention `(-1)‼ = 1` needed for the term `k = n-1`.

Proof outline.  Put

* `S n = ∑_{k<n} C(n,k) (2k-1)‼ (2(n-1-k)-1)‼`   (the left-hand side),
* `U n = ∑_{k≤n} C(n,k) (2k-1)‼ (2(n-k)-1)‼`      (the full convolution),
* `T n = ∑_{k<n} C(n,k) (2k+1)‼ (2(n-1-k)-1)‼`.

1. Pascal's rule `C(n+1,k+1) = C(n,k) + C(n,k+1)`, applied to the `k+1`-term of
   `S (n+1)` (the `k = 0` term is `dd n`), gives `S (n+1) = U n + T n`  (`S_succ`).
2. Termwise, using `(2(k+1)-1)‼ = (2k+1)(2k-1)‼` and
   `(2(n-k)-1)‼ = (2(n-1-k)+1)(2(n-1-k)-1)‼`, the summand of `U n + T n`
   equals `2n` times the summand of `S n`  (`key_term`, `U_add_T`).
3. Hence `S (n+1) = 2n S n + dd n`; with `S 1 = dd 1 = 1` and
   `dd (n+1) = (2n+1) dd n`, induction gives `S n = dd n`  (`S_eq_dd`).
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

open scoped Nat

namespace PercLib.CriticalLRP.Analysis

/-- `dd m = (2m-1)‼`, the double factorial of Lemma I.4.23.  With truncated
subtraction `dd 0 = 0‼ = 1` (the value of `(-1)‼`). -/
def dd (m : ℕ) : ℕ := (2 * m - 1)‼

@[simp] lemma dd_zero : dd 0 = 1 := by simp [dd]

@[simp] lemma dd_one : dd 1 = 1 := by simp [dd]

/-- The recursion `(2(n+1)-1)‼ = (2n+1)(2n-1)‼`. -/
lemma dd_succ (n : ℕ) : dd (n + 1) = (2 * n + 1) * dd n := by
  rcases n with _ | m
  · simp [dd]
  · have h1 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
    have h2 : 2 * (m + 1 + 1) - 1 = 2 * m + 1 + 2 := by omega
    have h3 : 2 * m + 1 + 2 = 2 * (m + 1) + 1 := by omega
    rw [dd, dd, h1, h2, Nat.doubleFactorial_add_two, h3]

/-- The left-hand side `S n` of Lemma I.4.23. -/
def S (n : ℕ) : ℕ := ∑ k ∈ Finset.range n, n.choose k * dd k * dd (n - 1 - k)

/-- The full convolution `U n`. -/
def U (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), n.choose k * dd k * dd (n - k)

/-- The auxiliary sum `T n` (convolution with a shifted double factorial). -/
def T (n : ℕ) : ℕ := ∑ k ∈ Finset.range n, n.choose k * dd (k + 1) * dd (n - 1 - k)

/-- **Step 2 of the proof**: the summand of `U n + T n` is `2n` times the summand of `S n`. -/
lemma key_term (n k : ℕ) (hk : k < n) :
    n.choose k * dd k * dd (n - k) + n.choose k * dd (k + 1) * dd (n - 1 - k)
      = 2 * n * (n.choose k * dd k * dd (n - 1 - k)) := by
  have h1 : dd (n - k) = (2 * (n - 1 - k) + 1) * dd (n - 1 - k) := by
    have h : n - k = (n - 1 - k) + 1 := by omega
    rw [h, dd_succ]
  have h2 : dd (k + 1) = (2 * k + 1) * dd k := dd_succ k
  have h3 : 2 * (n - 1 - k) + 1 + (2 * k + 1) = 2 * n := by omega
  rw [h1, h2]
  calc n.choose k * dd k * ((2 * (n - 1 - k) + 1) * dd (n - 1 - k))
        + n.choose k * ((2 * k + 1) * dd k) * dd (n - 1 - k)
      = n.choose k * dd k * dd (n - 1 - k) * (2 * (n - 1 - k) + 1 + (2 * k + 1)) := by
        ring
    _ = n.choose k * dd k * dd (n - 1 - k) * (2 * n) := by rw [h3]
    _ = 2 * n * (n.choose k * dd k * dd (n - 1 - k)) := by ring

/-- `U n` written as its last term plus the sum over `k < n`. -/
lemma U_eq (n : ℕ) :
    U n = dd n + ∑ k ∈ Finset.range n, n.choose k * dd k * dd (n - k) := by
  rw [U, Finset.sum_range_succ]
  have hlast : n.choose n * dd n * dd (n - n) = dd n := by simp
  rw [hlast]
  ring

/-- **Step 1 of the proof**: Pascal's rule gives `S (n+1) = U n + T n`. -/
lemma S_succ (n : ℕ) : S (n + 1) = U n + T n := by
  have hpeel : S (n + 1) =
      (∑ k ∈ Finset.range n, (n + 1).choose (k + 1) * dd (k + 1) * dd (n - 1 - k)) + dd n := by
    rw [S, Finset.sum_range_succ']
    have hsum : ∀ k ∈ Finset.range n,
        (n + 1).choose (k + 1) * dd (k + 1) * dd (n + 1 - 1 - (k + 1))
          = (n + 1).choose (k + 1) * dd (k + 1) * dd (n - 1 - k) := by
      intro k hk
      have hk' : k < n := Finset.mem_range.1 hk
      have h : n + 1 - 1 - (k + 1) = n - 1 - k := by omega
      rw [h]
    rw [Finset.sum_congr rfl hsum]
    have h0 : (n + 1).choose 0 * dd 0 * dd (n + 1 - 1 - 0) = dd n := by
      have h : n + 1 - 1 - 0 = n := by omega
      rw [h]; simp
    rw [h0]
  have hsplit :
      (∑ k ∈ Finset.range n, (n + 1).choose (k + 1) * dd (k + 1) * dd (n - 1 - k))
        = T n + ∑ k ∈ Finset.range n, n.choose (k + 1) * dd (k + 1) * dd (n - 1 - k) := by
    rw [T, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Nat.choose_succ_succ]
    ring
  have hU : U n =
      (∑ k ∈ Finset.range n, n.choose (k + 1) * dd (k + 1) * dd (n - 1 - k)) + dd n := by
    rw [U, Finset.sum_range_succ']
    have hsum : ∀ k ∈ Finset.range n,
        n.choose (k + 1) * dd (k + 1) * dd (n - (k + 1))
          = n.choose (k + 1) * dd (k + 1) * dd (n - 1 - k) := by
      intro k hk
      have h : n - (k + 1) = n - 1 - k := by omega
      rw [h]
    rw [Finset.sum_congr rfl hsum]
    have h0 : n.choose 0 * dd 0 * dd (n - 0) = dd n := by simp
    rw [h0]
  rw [hpeel, hsplit, hU]
  omega

/-- **Step 2 of the proof, summed**: `U n + T n = 2n S n + dd n`. -/
lemma U_add_T (n : ℕ) : U n + T n = 2 * n * S n + dd n := by
  have hA : U n = dd n + ∑ k ∈ Finset.range n, n.choose k * dd k * dd (n - k) := U_eq n
  have hkey : (∑ k ∈ Finset.range n,
        (n.choose k * dd k * dd (n - k) + n.choose k * dd (k + 1) * dd (n - 1 - k)))
      = ∑ k ∈ Finset.range n, 2 * n * (n.choose k * dd k * dd (n - 1 - k)) := by
    apply Finset.sum_congr rfl
    intro k hk
    exact key_term n k (Finset.mem_range.1 hk)
  have hsplit : (∑ k ∈ Finset.range n,
        (n.choose k * dd k * dd (n - k) + n.choose k * dd (k + 1) * dd (n - 1 - k)))
      = (∑ k ∈ Finset.range n, n.choose k * dd k * dd (n - k))
        + ∑ k ∈ Finset.range n, n.choose k * dd (k + 1) * dd (n - 1 - k) := by
    rw [Finset.sum_add_distrib]
  have h1 : (∑ k ∈ Finset.range n, n.choose k * dd k * dd (n - k))
      + ∑ k ∈ Finset.range n, n.choose k * dd (k + 1) * dd (n - 1 - k)
      = ∑ k ∈ Finset.range n, 2 * n * (n.choose k * dd k * dd (n - 1 - k)) := by
    rw [← Finset.sum_add_distrib]
    exact hkey
  rw [hA, T, Nat.add_assoc, h1]
  simp only [S]
  rw [Finset.mul_sum]
  ring

/-- **The recursion** `S (n+1) = 2n S n + dd n` behind the induction. -/
theorem S_succ_rec (n : ℕ) : S (n + 1) = 2 * n * S n + dd n := by
  rw [S_succ, U_add_T]

/-- `S n = dd n` for every `n ≥ 1`. -/
theorem S_eq_dd (n : ℕ) (hn : 1 ≤ n) : S n = dd n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  induction m with
  | zero => simp [S]
  | succ m ih =>
    rw [S_succ_rec, ih (by omega)]
    have hstep : 2 * (m + 1) * dd (m + 1) + dd (m + 1) = (2 * (m + 1) + 1) * dd (m + 1) := by
      ring
    rw [hstep, ← dd_succ]

/-- **Lemma I.4.23** (Hutchcroft, p. 49), in the paper's notation, for every `n ≥ 1`:
`∑_{k=0}^{n-1} C(n,k) (2k-1)!! (2n-2k-3)!! = (2n-1)!!`.

(The paper states `n ≥ 2`; `n = 1` is also true, both sides being `1`.) -/
theorem lemma_I_4_23 (n : ℕ) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range n, n.choose k * (2 * k - 1)‼ * (2 * n - 2 * k - 3)‼ = (2 * n - 1)‼ := by
  have hS := S_eq_dd n hn
  rw [S, dd] at hS
  rw [← hS]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k < n := Finset.mem_range.1 hk
  have h : 2 * (n - 1 - k) - 1 = 2 * n - 2 * k - 3 := by omega
  rw [dd, dd, h]

end PercLib.CriticalLRP.Analysis
