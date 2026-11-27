/- Integrated from independently rebuilt and accepted
`.ultramath/smwypth8o/m1/Squeeze.lean` at production base
`d2b527c1acf9fb8db8ca24854405020a6b3de061`. -/

/-
Swarm `smwypth8o`, member `m1`, direction d1.

# A bounded comparison is not a regular-variation statement

The Case-3 chain plus the ordinary atlas bound give, for the actual cutoff
moments, a two-sided comparison

  `a * (mom 1 r) ^ 3 <= mom 2 r <= b * (mom 1 r) ^ 3`   eventually,

with positive constants `a`, `b` (see `SourceModelData.momOf_two_squeeze` in
`Main.lean`).  This file proves that such a comparison **cannot** be converted
into regular variation of the middle function: there is a function squeezed
between `x` and `3 x` that is not regularly varying of index `1`.

Consequently the second-moment regular variation `h2` of the higher-moment
packet is a genuinely independent input at the current state of the project
(Proposition I.4.15 / gap WS002), not a consequence of the comparison.
-/

module

public import PercLib.CriticalLRP.Analysis.RegularVariation

/-! # Regular variation and its cutoff-model interfaces -/

@[expose] public section

noncomputable section

open Filter Topology
open scoped Topology

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.unusedSectionVars false

namespace PercLib.CriticalLRP.Analysis

/-- **A bounded two-sided comparison with `x` does not give regular variation.**
The witness `x ↦ x * (2 + (-1) ^ ⌊x⌋)` is squeezed between `x` and `3 x` on
`[0, ∞)` but its `2`-scaling ratio takes the values `2` and `6` on two integer
sequences, so it is not regularly varying of index `1`.  Hence a comparison
with the same order of growth leaves the slowly varying prefactor free. -/
theorem exists_squeezed_not_regularlyVarying :
    ∃ h : ℝ → ℝ,
      (∀ x : ℝ, 0 ≤ x → x ≤ h x ∧ h x ≤ 3 * x) ∧ ¬ RegularlyVaryingAtTop h 1 := by
  refine ⟨fun x : ℝ => x * (2 + (-1 : ℝ) ^ Nat.floor x), ?_, ?_⟩
  · intro x _hx
    have hcases : (-1 : ℝ) ^ Nat.floor x = 1 ∨ (-1 : ℝ) ^ Nat.floor x = -1 := by
      rcases Nat.even_or_odd (Nat.floor x) with ⟨k, hk⟩ | ⟨k, hk⟩
      · exact Or.inl (Even.neg_one_pow ⟨k, hk⟩)
      · exact Or.inr (Odd.neg_one_pow ⟨k, hk⟩)
    constructor <;> rcases hcases with hc | hc <;> simp only [] <;> rw [hc] <;> nlinarith
  · intro hRV
    have hlim : Tendsto (fun x : ℝ =>
        (fun y : ℝ => y * (2 + (-1 : ℝ) ^ Nat.floor y)) (2 * x)
          / (fun y : ℝ => y * (2 + (-1 : ℝ) ^ Nat.floor y)) x) atTop (𝓝 (2 ^ (1 : ℝ))) :=
      hRV.2 2 (by norm_num)
    rw [Real.rpow_one] at hlim
    have hseq : Tendsto (fun n : ℕ => (2 * (n : ℝ) + 1)) atTop atTop := by
      have hbase : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
      have hmul : Tendsto (fun n : ℕ => 2 * (n : ℝ)) atTop atTop :=
        hbase.const_mul_atTop (by norm_num)
      exact tendsto_atTop_mono (fun n => by linarith) hmul
    have hcomp := hlim.comp hseq
    have hval : ∀ n : ℕ,
        (fun y : ℝ => y * (2 + (-1 : ℝ) ^ Nat.floor y)) (2 * (2 * (n : ℝ) + 1))
            / (fun y : ℝ => y * (2 + (-1 : ℝ) ^ Nat.floor y)) (2 * (n : ℝ) + 1) = 6 := by
      intro n
      have hodd : Nat.floor (2 * (n : ℝ) + 1) = 2 * n + 1 := by
        have hc : 2 * (n : ℝ) + 1 = ((2 * n + 1 : ℕ) : ℝ) := by push_cast; ring
        rw [hc, Nat.floor_natCast]
      have heven : Nat.floor (2 * (2 * (n : ℝ) + 1)) = 4 * n + 2 := by
        have hc : 2 * (2 * (n : ℝ) + 1) = ((4 * n + 2 : ℕ) : ℝ) := by push_cast; ring
        rw [hc, Nat.floor_natCast]
      have h1 : (-1 : ℝ) ^ (2 * n + 1) = -1 := Odd.neg_one_pow ⟨n, by ring⟩
      have h2 : (-1 : ℝ) ^ (4 * n + 2) = 1 := Even.neg_one_pow ⟨2 * n + 1, by ring⟩
      simp only []
      rw [hodd, heven, h1, h2]
      have hx : 2 * (n : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
      field_simp
      ring
    have hcomp6 : Tendsto (fun _ : ℕ => (6 : ℝ)) atTop (𝓝 2) :=
      hcomp.congr' (Eventually.of_forall hval)
    exact absurd (tendsto_nhds_unique tendsto_const_nhds hcomp6) (by norm_num)

#print axioms exists_squeezed_not_regularlyVarying

end PercLib.CriticalLRP.Analysis
