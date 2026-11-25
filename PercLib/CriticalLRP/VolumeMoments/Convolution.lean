/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.23 (p. 49) and the companion binomial sum used in
the induction step of Proposition I.4.20.

The paper proves Lemma I.4.23 by comparing exponential generating functions.
Here we give a purely combinatorial induction, which needs no formal power
series: with `M n = (2n-1)!!` (so `M(n+1) = (2n+1)M(n)`) put

  `SA n = ∑_{k<n} C(n,k) M k M(n-1-k)`   (the left side of Lemma I.4.23)
  `SB n = ∑_{k<n} C(n,k) M(k+1) M(n-1-k)`
  `ST n = ∑_{k<n} C(n,k+1) M(k+1) M(n-1-k)`
  `SU n = ∑_{k≤n} C(n,k) M k M(n-k)`.

Then
* `SU n = ST n + M n`                                        (`SU_eq`)
* `SA (n+1) = SB n + ST n + M n`                              (`SA_succ_decomp`, Pascal)
* `SB n = 2 * W n + SA n` where `W n = ∑_{k<n} C(n,k) k M k M(n-1-k)`
* `K n + 2 * W n = (2n-1) * SA n` where `K n = ∑_{k<n} C(n,k) M k (2(n-k)-1) M(n-1-k)`
* `SU n = K n + M n`

Adding the last two and the first two gives the induction step
`SA (n+1) = 2 n * SA n + M n`, whence `SA n = M n` because `M (n+1) = (2n+1) M n`.

Note. The plain-text extraction of the paper prints the binomial coefficient of
Lemma I.4.23 as `C(n-1,k)`; the published source (`Zd_renormalizationHD.tex`,
`\label{lem:double_fun}`) has `\binom{n}{k}`, and it is `\binom{n}{k}` that is
true (it fails for `\binom{n-1}{k}` already at `n = 2`).  This file proves the
`\binom{n}{k}` form.
-/
module

public import PercLib.CriticalLRP.VolumeMoments.DFactorial

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open Finset

namespace PercLib.CriticalLRP.VolumeMoments

/-- Left-hand side of Lemma I.4.23, `∑_{k<n} C(n,k) (2k-1)!! (2n-2k-3)!!`. -/
def SA (n : ℕ) : ℕ := ∑ k ∈ Finset.range n, n.choose k * (M k * M (n - 1 - k))

/-- Auxiliary sum `∑_{k<n} C(n,k) (2k+1)!! (2n-2k-3)!!`. -/
def SB (n : ℕ) : ℕ := ∑ k ∈ Finset.range n, n.choose k * (M (k + 1) * M (n - 1 - k))

/-- Auxiliary sum `∑_{k<n} C(n,k+1) (2k+1)!! (2n-2k-3)!!`. -/
def ST (n : ℕ) : ℕ := ∑ k ∈ Finset.range n, n.choose (k + 1) * (M (k + 1) * M (n - 1 - k))

/-- `∑_{k≤n} C(n,k) (2k-1)!! (2n-2k-1)!!`, the binomial convolution of `M` with itself. -/
def SU (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), n.choose k * (M k * M (n - k))

/-! ### The recurrence `M (n-k) = (2(n-k)-1) M (n-1-k)` -/

theorem M_sub_eq {n k : ℕ} (hk : k < n) :
    M (n - k) = (2 * (n - k) - 1) * M (n - 1 - k) := by
  have hn : 1 ≤ n := by omega
  have h2 := M_succ (n - 1 - k)
  have h3 : n - 1 - k + 1 = n - k := by omega
  have h4 : 2 * (n - k) - 1 = 2 * (n - 1 - k) + 1 := by omega
  rw [h3] at h2
  rw [h2, h4]

/-! ### `SU` in terms of `ST` and of `K` -/

theorem SU_split (n : ℕ) :
    SU n = (∑ k ∈ Finset.range n, n.choose k * (M k * M (n - k))) + M n := by
  rw [SU, Finset.sum_range_succ]
  simp

theorem SU_eq (n : ℕ) : SU n = ST n + M n := by
  rw [SU, Finset.sum_range_succ', ST]
  have h : (∑ x ∈ Finset.range n, n.choose (x + 1) * (M (x + 1) * M (n - (x + 1))))
      = ∑ x ∈ Finset.range n, n.choose (x + 1) * (M (x + 1) * M (n - 1 - x)) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx' : x ≤ n - 1 := by have := Finset.mem_range.1 hx; omega
    rw [show n - (x + 1) = n - 1 - x by omega]
  rw [h]
  simp

/-- `K n = ∑_{k<n} C(n,k) (2k-1)!! (2(n-k)-1) (2n-2k-3)!!`, the "one factor of
`(2(n-k)-1)` split off" form of the `SU` sum. -/
def SK (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, n.choose k * (M k * ((2 * (n - k) - 1) * M (n - 1 - k)))

/-- `W n = ∑_{k<n} C(n,k) k (2k-1)!! (2n-2k-3)!!`. -/
def SW (n : ℕ) : ℕ := ∑ k ∈ Finset.range n, n.choose k * (k * (M k * M (n - 1 - k)))

theorem SU_eq_SK (n : ℕ) : SU n = SK n + M n := by
  rw [SU_split]
  congr 1
  rw [SK]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [M_sub_eq (Finset.mem_range.1 hk)]

/-! ### The Pascal step -/

theorem SA_succ_decomp (n : ℕ) : SA (n + 1) = SB n + ST n + M n := by
  have hstep : SA (n + 1)
      = ∑ k ∈ Finset.range (n + 1), (n + 1).choose k * (M k * M (n - k)) := by
    rw [SA]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show n + 1 - 1 - k = n - k by omega]
  rw [hstep, Finset.sum_range_succ']
  have hchoose : (∑ x ∈ Finset.range n,
        (n + 1).choose (x + 1) * (M (x + 1) * M (n - (x + 1))))
      = ∑ x ∈ Finset.range n,
        (n.choose x + n.choose (x + 1)) * (M (x + 1) * M (n - (x + 1))) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Nat.choose_succ_succ]
  rw [hchoose]
  have hsplit : (∑ x ∈ Finset.range n,
        (n.choose x + n.choose (x + 1)) * (M (x + 1) * M (n - (x + 1))))
      = SB n + ST n := by
    rw [SB, ST, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hx' : x ≤ n - 1 := by have := Finset.mem_range.1 hx; omega
    rw [show n - (x + 1) = n - 1 - x by omega, add_mul]
  rw [hsplit]
  simp

theorem SA_succ_eq (n : ℕ) : SA (n + 1) = SB n + SU n := by
  have h1 := SA_succ_decomp n
  have h2 := SU_eq n
  rw [h1, h2]
  ring

/-! ### The two linear relations -/

theorem SB_eq_SW (n : ℕ) : SB n = 2 * SW n + SA n := by
  rw [SB, SW, SA]
  have hpt : ∀ k ∈ Finset.range n,
      n.choose k * (M (k + 1) * M (n - 1 - k))
        = 2 * (n.choose k * (k * (M k * M (n - 1 - k))))
          + n.choose k * (M k * M (n - 1 - k)) := by
    intro k _
    rw [M_succ]
    ring
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl hpt

theorem SK_add_SW (n : ℕ) (hn : 1 ≤ n) : SK n + 2 * SW n = (2 * n - 1) * SA n := by
  have h1 : (2 * n - 1) * SA n
      = ∑ k ∈ Finset.range n, (2 * n - 1) * (n.choose k * (M k * M (n - 1 - k))) := by
    rw [SA, Finset.mul_sum]
  have h2 : SK n
      = ∑ k ∈ Finset.range n,
          n.choose k * (M k * ((2 * (n - k) - 1) * M (n - 1 - k))) := rfl
  have h3 : 2 * SW n
      = ∑ k ∈ Finset.range n, 2 * (n.choose k * (k * (M k * M (n - 1 - k)))) := by
    rw [SW, Finset.mul_sum]
  rw [h1, h2, h3, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n - 1 := by have := Finset.mem_range.1 hk; omega
  have har : 2 * (n - k) - 1 + 2 * k = 2 * n - 1 := by omega
  calc n.choose k * (M k * ((2 * (n - k) - 1) * M (n - 1 - k)))
        + 2 * (n.choose k * (k * (M k * M (n - 1 - k))))
      = (2 * (n - k) - 1) * (n.choose k * (M k * M (n - 1 - k)))
        + (2 * k) * (n.choose k * (M k * M (n - 1 - k))) := by ring
    _ = ((2 * (n - k) - 1) + 2 * k) * (n.choose k * (M k * M (n - 1 - k))) := by
        rw [add_mul]
    _ = (2 * n - 1) * (n.choose k * (M k * M (n - 1 - k))) := by rw [har]

/-! ### The induction step and Lemma I.4.23 -/

theorem SA_succ (n : ℕ) (hn : 1 ≤ n) : SA (n + 1) = 2 * n * SA n + M n := by
  have h1 := SA_succ_eq n
  have h2 := SB_eq_SW n
  have h3 := SK_add_SW n hn
  have h4 := SU_eq_SK n
  rw [h2, h4] at h1
  -- SA(n+1) = (2 SW + SA) + (SK + M)
  have h5 : (2 * n - 1) * SA n + SA n = 2 * n * SA n := by
    rw [← Nat.succ_mul]
    congr 1
    omega
  have h6 : 2 * SW n + SA n + (SK n + M n) = 2 * n * SA n + M n := by
    calc 2 * SW n + SA n + (SK n + M n) = (SK n + 2 * SW n) + SA n + M n := by ring
      _ = (2 * n - 1) * SA n + SA n + M n := by rw [h3]
      _ = 2 * n * SA n + M n := by rw [h5]
  rw [← h6]
  exact h1

/-- **Lemma I.4.23** (Hutchcroft, p. 49): for `n ≥ 1`,
`∑_{k<n} C(n,k) (2k-1)!! (2n-2k-3)!! = (2n-1)!!`. -/
theorem lemma_I_4_23 (n : ℕ) (hn : 1 ≤ n) : SA n = M n := by
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      -- n = 1
      decide
    · have := SA_succ m hm
      rw [this, ih hm]
      rw [M_succ]
      ring


/-! ### The companion binomial sum of Proposition I.4.20

The induction step in the proof of Proposition I.4.20 (paper p. 49) uses

`∑_{ℓ=1}^{p-2} C(p,ℓ) (2ℓ-1)!! (2p-2ℓ-3)!! = (2p-1)!! - (2p-3)!! - p(2p-3)!! = (p-2)(2p-3)!!`,

i.e. Lemma I.4.23 with the two end terms `ℓ = 0` and `ℓ = p-1` removed. We prove the
equivalent additive form (no truncated subtraction): with `M k = (2k-1)!!`,

`(∑_{ℓ ∈ range (p-2)} C(p,ℓ+1) M(ℓ+1) M(p-2-ℓ)) + (p+1) M(p-1) = M p`. -/

/-- `SA p` split into its two end terms and the middle range. -/
theorem SA_split (p : ℕ) (hp : 3 ≤ p) :
    SA p = (∑ ℓ ∈ Finset.range (p - 2), p.choose (ℓ + 1) * (M (ℓ + 1) * M (p - 2 - ℓ)))
      + p * M (p - 1) + M (p - 1) := by
  have hSA : SA p = M p := lemma_I_4_23 p (by omega)
  set f : ℕ → ℕ := fun k => p.choose k * (M k * M (p - 1 - k)) with hf
  have hone : SA p = ∑ k ∈ Finset.range p, f k := by rw [SA]
  rw [hone]
  nth_rewrite 1 [show p = (p - 1) + 1 by omega]
  rw [Finset.sum_range_succ']
  nth_rewrite 1 [show p - 1 = (p - 2) + 1 by omega]
  rw [Finset.sum_range_succ]
  have htail : f (p - 2 + 1) = p * M (p - 1) := by
    have hc : p.choose (p - 1) = p := by
      have h := Nat.choose_succ_self_right (p - 1)
      rwa [show p - 1 + 1 = p by omega] at h
    have h1 : p - 2 + 1 = p - 1 := by omega
    rw [hf]
    simp only [h1, hc, show p - 1 - (p - 1) = 0 by omega, M_zero, mul_one]
  have hhead : f 0 = M (p - 1) := by
    rw [hf]
    simp
  have hmid : (∑ x ∈ Finset.range (p - 2), f (x + 1))
      = ∑ ℓ ∈ Finset.range (p - 2), p.choose (ℓ + 1) * (M (ℓ + 1) * M (p - 2 - ℓ)) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [hf]
    simp only
    rw [show p - 1 - (x + 1) = p - 2 - x by have := Finset.mem_range.1 hx; omega]
  rw [hmid, htail, hhead]

/-- **Companion identity** to Lemma I.4.23, the additive form of the binomial sum
appearing in the induction step of Proposition I.4.20:
`∑_{ℓ ∈ range (p-2)} C(p,ℓ+1) (2ℓ+1)!! (2p-2ℓ-3)!! + (p+1) (2p-3)!! = (2p-1)!!`. -/
theorem SA_middle (p : ℕ) (hp : 3 ≤ p) :
    (∑ ℓ ∈ Finset.range (p - 2), p.choose (ℓ + 1) * (M (ℓ + 1) * M (p - 2 - ℓ)))
      + (p + 1) * M (p - 1) = M p := by
  have h1 := SA_split p hp
  have h2 : SA p = M p := lemma_I_4_23 p (by omega)
  rw [h2] at h1
  rw [h1]
  ring

end PercLib.CriticalLRP.VolumeMoments
