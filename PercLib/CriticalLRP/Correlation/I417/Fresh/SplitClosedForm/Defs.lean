/-
Definitions for direction `CLOSED-FORM-SPLIT-WEIGHT` (swarm `smwxenel0`, member `m3`).

Read-only against production `repo/.scratch/critical-lrp-orchestration` (HEAD `3f10797`), module
`PercLib.CriticalLRP.Correlation.I417.Fresh.HistSpine.{Defs,Bridge}` and
`PercLib.CriticalLRP.Correlation.I417.Fresh.Depth.Main`.

Everything here is a definition; every theorem is in `Chain.lean`, `Fibre.lean`, `Bridge.lean`.

## What is defined and why

Production's accepted one-step reindexing `I417HistToSpine.histW_snoc_tsum` collapses one
attachment round of the first-hit fresh cover: summing the attachment vertex `z` and the arm
target `d` of `Hist.snoc H s z d` replaces the weight of the split slot `s` by the nested sum
`splitWt`.  Iterating it along a split-choice tuple `k : (t : Fin n) → Idx t` therefore computes
the branch ("fibre") sum of the weight product of the `2(n+1)`-leg diagram, *provided* one knows
the closed form of the iterated split weight.

`chainM` and `chainE` are that closed form, slot by slot.  Reading the fold from the top
(`F n = τ`, `F t = splitWt (F (t+1)) (k t)`):

* `chainM n k t i` is the length of the chain of legs that slot `i` of stage `t` resolves into
  after all remaining splits `k t, …, k (n-1)` have been performed;
* `chainE n k t i` is the number of `χ`-factors (summed free vertices: attached arms and the mark
  arm) carried by that same slot.

Theorem `slotW_step` (`Chain.lean`) says `F t` is exactly `fun i => χ ^ chainE · T ^ chainM`, and
`exp_invariant` says the χ-exponents and the chain lengths always add up to the leg count
`2 * (n + 1)`.  `chainM n k 0 idxZero` is the pin--mark path length of the branch (`markDepthK`,
see `Bridge.lean`), which turns the fibre sum into the printed normal form
`χ ^ (2q - ℓ) · T ^ ℓ (y, w)`.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.HistSpine.Bridge
public import PercLib.CriticalLRP.Correlation.I417.Fresh.Depth.Main

/-!
# Definitions for the closed form of the iterated split weight

`chainM` (chain length of a slot after the remaining splits), `chainE` (the `χ`-exponent the same
slot carries), `slotW` (the resulting slot weight `χ ^ chainE * T ^ chainM`), `restr` (the first `m`
rounds of a split-choice tuple).  Theorems are in `Chain.lean`; the axiom audit is `Check.lean`.
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.show false

@[expose] public section

namespace PercLib.CriticalLRP.I417SplitClosedForm

open PercLib.CriticalLRP

variable {V : Type*} [Countable V] [DecidableEq V]

/-! ## The chain length and the χ-exponent of a slot -/

/-- **Length of the chain a slot resolves into.**  `chainM n k t i` is the number of legs that the
slot `i : Idx t` becomes after the splits `k t, …, k (n-1)` (which are the remaining rounds of the
fold) have all been applied.  Splitting slot `i` at round `t` replaces it by the two halves
`Sum.inl i` and `Sum.inr false` — both stay on the chain, whose length is the sum of theirs — and
by the arm `Sum.inr true`, which leaves the chain.  If slot `i` is not split at round `t` the chain
continues through `Sum.inl i`. -/
noncomputable def chainM (n : ℕ) (k : (u : Fin n) → I417GenIter.Idx u) (t : ℕ)
    (i : I417GenIter.Idx t) : ℕ :=
  if _h : t < n then
    (if i = k ⟨t, _h⟩ then chainM n k (t + 1) (Sum.inl i) + chainM n k (t + 1) (Sum.inr false)
     else chainM n k (t + 1) (Sum.inl i))
  else 1
termination_by n - t
decreasing_by all_goals exact Nat.sub_lt_sub_left ‹t < n› (Nat.lt_succ_self t)

/-- **Number of `χ`-factors carried by a slot.**  At every split of the slot, the newly attached
arm `Sum.inr true` is summed over its target first, and that sum is exactly `χ ^ chainM` of the arm
slot; `chainE` records the resulting exponent.  The chain halves do not contribute new `χ`-factors
of their own, so the exponent of a split slot is the sum of the three children's exponents plus the
arm's chain length. -/
noncomputable def chainE (n : ℕ) (k : (u : Fin n) → I417GenIter.Idx u) (t : ℕ)
    (i : I417GenIter.Idx t) : ℕ :=
  if _h : t < n then
    (if i = k ⟨t, _h⟩ then
      chainE n k (t + 1) (Sum.inl i) + chainE n k (t + 1) (Sum.inr false) +
        (chainE n k (t + 1) (Sum.inr true) + chainM n k (t + 1) (Sum.inr true))
     else chainE n k (t + 1) (Sum.inl i))
  else 0
termination_by n - t
decreasing_by all_goals exact Nat.sub_lt_sub_left ‹t < n› (Nat.lt_succ_self t)

/-- **The weight of one slot after all remaining splits have been folded in**: a chain of
`chainM` legs weighted by the kernel `τ`, times `χ ^ chainE` for the free vertices that the folded
splits have already summed out.  At the top stage `t = n` this is `χ ^ 0 * T ^ 1 = τ` for every
slot, i.e. the base leg weight. -/
noncomputable def slotW (τ : V → V → ℝ≥0∞) (χ : ℝ≥0∞) (n : ℕ)
    (k : (u : Fin n) → I417GenIter.Idx u) (t : ℕ) (i : I417GenIter.Idx t) : V → V → ℝ≥0∞ :=
  fun a b => χ ^ chainE n k t i * I417Base.iterPow τ (chainM n k t i) a b

/-- The split-choice tuple of the first `m` rounds of a branch of length `n`. -/
def restr {n : ℕ} (k : (u : Fin n) → I417GenIter.Idx u) (m : ℕ) (hm : m ≤ n) :
    (u : Fin m) → I417GenIter.Idx u :=
  fun u => k ⟨u.val, Nat.lt_of_lt_of_le u.isLt hm⟩

end PercLib.CriticalLRP.I417SplitClosedForm
