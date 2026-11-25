/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
The final combinatorial step in the proof of Lemma I.4.1 of Hutchcroft,
"Critical long-range percolation I", arXiv:2508.18807v1.

After Russo's formula and the mass-transport principle, the proof of Lemma I.4.1
expands a binomial:

  ∂/∂r E_{β,r}|K|^p = β|J'(r)| E_{β,r}[ |K| ∑_{y∈B_r} 1(y ∉ K)
        ((|K| + |K_y|)^p − |K|^p) ]

and then writes the result as

  β|J'(r)| ∑_{ℓ=0}^{p−1} binom(p,ℓ) E_{β,r}[ |K|^{ℓ+1} ∑_{y∈B_r} 1(y ∉ K) |K_y|^{p−ℓ} ].

Here `a = |K|` and `b = |K_y|`, so the identity required is

  a * ((a + b)^p − a^p) = ∑_{ℓ=0}^{p−1} binom(p,ℓ) a^{ℓ+1} b^{p−ℓ},

which holds in any commutative ring (no positivity or integrality hypotheses).
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

open Finset

namespace PercLib.CriticalLRP.FiniteVolume

/-- `∑_{ℓ<p} binom(p,ℓ) a^ℓ b^{p−ℓ} = (a+b)^p − a^p`. -/
theorem sum_choose_mul_pow_eq_pow_sub (a b : ℝ) (p : ℕ) :
    ∑ ℓ ∈ range p, (p.choose ℓ : ℝ) * a ^ ℓ * b ^ (p - ℓ) = (a + b) ^ p - a ^ p := by
  have h := add_pow a b p
  rw [Finset.sum_range_succ] at h
  have hlast : a ^ p * b ^ (p - p) * (p.choose p : ℝ) = a ^ p := by simp
  rw [hlast] at h
  have h2 : ∑ ℓ ∈ range p, a ^ ℓ * b ^ (p - ℓ) * (p.choose ℓ : ℝ)
      = ∑ ℓ ∈ range p, (p.choose ℓ : ℝ) * a ^ ℓ * b ^ (p - ℓ) := by
    refine sum_congr rfl fun ℓ _ => ?_
    ring
  rw [h2] at h
  linarith

/-- **The binomial identity of Lemma I.4.1**: with `a = |K|` and `b = |K_y|`,

`a * ((a + b)^p − a^p) = ∑_{ℓ=0}^{p−1} binom(p,ℓ) a^{ℓ+1} b^{p−ℓ}`.

This is exactly the passage from the "raw" Russo formula to the displayed
formula (I.4.1), and it uses `binom(p,ℓ)` as in the paper. -/
theorem mul_pow_sub_pow_eq_sum_choose (a b : ℝ) (p : ℕ) :
    a * ((a + b) ^ p - a ^ p)
      = ∑ ℓ ∈ range p, (p.choose ℓ : ℝ) * a ^ (ℓ + 1) * b ^ (p - ℓ) := by
  rw [← sum_choose_mul_pow_eq_pow_sub a b p, Finset.mul_sum]
  refine sum_congr rfl fun ℓ _ => ?_
  rw [pow_succ']
  ring

end PercLib.CriticalLRP.FiniteVolume
