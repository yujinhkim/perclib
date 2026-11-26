/-
The slot/chain invariant of the iterated split weight (`CLOSED-FORM-SPLIT-WEIGHT`, swarm
`smwxenel0`, member `m3`).  Proofs only; definitions are in `SplitClosedForm/Defs.lean`.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.HistSpine.Defs
public import PercLib.CriticalLRP.Correlation.I417.Fresh.Depth.Defs
public import PercLib.CriticalLRP.Correlation.I417.Fresh.SplitClosedForm.Defs

/-!
# The closed form of the iterated split weight, slot by slot

Production's `I417HistToSpine.splitWt` performs one attachment round on the leg weights.  The
theorem `slotW_step` below computes the *whole* iteration of that operation along an actual
split-choice tuple `k : (t : Fin n) → Idx t`:

  `F t = splitWt (F (t+1)) (k t)`  with  `F n = τ`   implies   `F t i = χ ^ chainE · T ^ chainM`.

Two things are being proved at once, and both are needed for the branch value:

* `chainM n k t i` — how many legs slot `i` of stage `t` becomes: a split inserts one interior
  vertex into the chain, so the split slot's chain length is the *sum* of its two halves';
* `chainE n k t i` — how many `χ`-factors (summed free vertices) that slot carries: a split sums
  the freshly attached arm at the split vertex *first*, so the arm contributes the whole `χ ^`
  power of the arm slot's chain length, while the two halves contribute only their own exponents.

`sum_chainE_add_chainM` then says that along every branch the exponents plus the chain lengths
always add up to the total leg count `2 * (n + 1)`: at every split the `χ`-power of the new arm
that `chainE` absorbs is exactly the leg that `chainM` loses.  No `χ` is lost or double-counted.
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.show false

@[expose] public section

namespace PercLib.CriticalLRP.I417SplitClosedForm

open PercLib.CriticalLRP
open PercLib.CriticalLRP.I417HistToSpine (tsum_iterPow_mul tsum_iterPow_chain splitWt)

variable {V : Type*} [Countable V] [DecidableEq V]

/-! ## Unfolding the two recursions -/

theorem chainM_eq_succ (n : ℕ) (k : (u : Fin n) → I417GenIter.Idx u) {t : ℕ} (h : t < n)
    (i : I417GenIter.Idx t) :
    chainM n k t i = (if i = k ⟨t, h⟩ then
      chainM n k (t + 1) (Sum.inl i) + chainM n k (t + 1) (Sum.inr false)
      else chainM n k (t + 1) (Sum.inl i)) := by
  rw [chainM]
  exact dite_eq_left h

theorem chainE_eq_succ (n : ℕ) (k : (u : Fin n) → I417GenIter.Idx u) {t : ℕ} (h : t < n)
    (i : I417GenIter.Idx t) :
    chainE n k t i = (if i = k ⟨t, h⟩ then
      chainE n k (t + 1) (Sum.inl i) + chainE n k (t + 1) (Sum.inr false) +
        (chainE n k (t + 1) (Sum.inr true) + chainM n k (t + 1) (Sum.inr true))
      else chainE n k (t + 1) (Sum.inl i)) := by
  rw [chainE]
  exact dite_eq_left h

theorem chainM_eq_top {n t : ℕ} (h : ¬ t < n) (k : (u : Fin n) → I417GenIter.Idx u)
    (i : I417GenIter.Idx t) : chainM n k t i = 1 := by
  rw [chainM]
  exact dite_eq_right h

theorem chainE_eq_top {n t : ℕ} (h : ¬ t < n) (k : (u : Fin n) → I417GenIter.Idx u)
    (i : I417GenIter.Idx t) : chainE n k t i = 0 := by
  rw [chainE]
  exact dite_eq_right h

/-- **Every slot resolves into at least one leg**, so that the chain sums `∑_b T ^ chainM` can be
evaluated as `χ ^ chainM`. -/
theorem chainM_pos (n : ℕ) (k : (u : Fin n) → I417GenIter.Idx u) :
    ∀ (t : ℕ) (_ : t ≤ n) (i : I417GenIter.Idx t), 1 ≤ chainM n k t i := by
  intro t hle
  refine Nat.decreasingInduction (n := n)
    (motive := fun s _ => ∀ i : I417GenIter.Idx s, 1 ≤ chainM n k s i) ?_ ?_ hle
  · intro m hm ih i
    rw [chainM_eq_succ n k hm i]
    split
    · have h1 := ih (Sum.inl i)
      omega
    · exact ih (Sum.inl i)
  · intro i
    rw [chainM_eq_top (lt_irrefl n) k i]

/-! ## Powers of `χ` -/

theorem pow_add_four (a : ℝ≥0∞) (x y z w : ℕ) :
    a ^ (x + y + (z + w)) = a ^ x * a ^ y * a ^ z * a ^ w := by
  rw [pow_add, pow_add, pow_add]
  ring

/-! ## One split on one slot -/

/-- **One attachment round, on the weight of a single slot.**  If the slot is split, the arm's
weight is summed over its target first — giving `χ ^` the arm slot's chain length — and the two
halves are joined into a single chain of the summed length; the exponents of all three children are
retained.  This is the local content of the closed form. -/
theorem splitWt_slotW_self (τ : V → V → ℝ≥0∞) (χ : ℝ≥0∞)
    (hχ : ∀ a : V, ∑' b : V, τ a b = χ)
    (n : ℕ) (k : (u : Fin n) → I417GenIter.Idx u) {t : ℕ} (h : t < n) (a b : V) :
    splitWt (slotW τ χ n k (t + 1)) (k ⟨t, h⟩) (k ⟨t, h⟩) a b =
      slotW τ χ n k t (k ⟨t, h⟩) a b := by
  have hm3 : 1 ≤ chainM n k (t + 1) (Sum.inr true) := chainM_pos n k (t + 1) (by omega) _
  have hpt2 : ∀ z : V, (∑' d : V, χ ^ chainE n k (t + 1) (Sum.inr true) *
      I417Base.iterPow τ (chainM n k (t + 1) (Sum.inr true)) z d) =
      χ ^ (chainE n k (t + 1) (Sum.inr true) + chainM n k (t + 1) (Sum.inr true)) := by
    intro z
    rw [ENNReal.tsum_mul_left, tsum_iterPow_chain (τ := τ) (χ := χ) hχ _ hm3 z, ← pow_add]
  have hpow : χ ^ (chainE n k (t + 1) (Sum.inl (k ⟨t, h⟩)) +
        chainE n k (t + 1) (Sum.inr false) +
        (chainE n k (t + 1) (Sum.inr true) + chainM n k (t + 1) (Sum.inr true))) =
      χ ^ chainE n k (t + 1) (Sum.inl (k ⟨t, h⟩)) *
        χ ^ chainE n k (t + 1) (Sum.inr false) *
        χ ^ chainE n k (t + 1) (Sum.inr true) *
        χ ^ chainM n k (t + 1) (Sum.inr true) := pow_add_four χ _ _ _ _
  simp only [splitWt, slotW, ↓reduceIte]
  rw [tsum_congr fun z => by rw [hpt2 z]]
  rw [chainE_eq_succ n k h (k ⟨t, h⟩), chainM_eq_succ n k h (k ⟨t, h⟩),
    ite_eq_left rfl, ite_eq_left rfl]
  have hterm : ∀ z : V,
      (χ ^ chainE n k (t + 1) (Sum.inl (k ⟨t, h⟩)) *
          I417Base.iterPow τ (chainM n k (t + 1) (Sum.inl (k ⟨t, h⟩))) a z) *
        (χ ^ chainE n k (t + 1) (Sum.inr false) *
          I417Base.iterPow τ (chainM n k (t + 1) (Sum.inr false)) z b) *
        χ ^ (chainE n k (t + 1) (Sum.inr true) + chainM n k (t + 1) (Sum.inr true)) =
      χ ^ (chainE n k (t + 1) (Sum.inl (k ⟨t, h⟩)) +
            chainE n k (t + 1) (Sum.inr false) +
            (chainE n k (t + 1) (Sum.inr true) + chainM n k (t + 1) (Sum.inr true))) *
        (I417Base.iterPow τ (chainM n k (t + 1) (Sum.inl (k ⟨t, h⟩))) a z *
          I417Base.iterPow τ (chainM n k (t + 1) (Sum.inr false)) z b) := by
    intro z
    rw [hpow]
    ring
  rw [tsum_congr hterm, ENNReal.tsum_mul_left, tsum_iterPow_mul]

/-- **One attachment round on the whole weight family**: iterating `splitWt` along the branch gives
the closed form `χ ^ chainE · T ^ chainM` in every slot. -/
theorem slotW_step (τ : V → V → ℝ≥0∞) (χ : ℝ≥0∞)
    (hχ : ∀ a : V, ∑' b : V, τ a b = χ)
    (n : ℕ) (k : (u : Fin n) → I417GenIter.Idx u) {t : ℕ} (h : t < n)
    (i : I417GenIter.Idx t) :
    splitWt (slotW τ χ n k (t + 1)) (k ⟨t, h⟩) i = slotW τ χ n k t i := by
  funext a b
  by_cases hi : i = k ⟨t, h⟩
  · rw [hi]
    exact splitWt_slotW_self τ χ hχ n k h a b
  · simp only [splitWt, slotW, ite_eq_right hi]
    rw [chainE_eq_succ n k h i, chainM_eq_succ n k h i, ite_eq_right hi, ite_eq_right hi]

/-- The base of the iteration: at the top stage every slot carries the leg weight `τ`. -/
theorem slotW_top (τ : V → V → ℝ≥0∞) (χ : ℝ≥0∞) (n : ℕ)
    (k : (u : Fin n) → I417GenIter.Idx u) (i : I417GenIter.Idx n) :
    slotW τ χ n k n i = τ := by
  funext a b
  simp only [slotW]
  rw [chainE_eq_top (lt_irrefl n) k i, chainM_eq_top (lt_irrefl n) k i,
    I417HistToSpine.iterPow_one_eq]
  simp

/-! ## The leg count is the sum of the χ-exponents and the chain lengths -/

/-- Splitting a sum over the index type of the next stage into the old slots and the two new
ones. -/
theorem sum_idx_succ_eq {M : Type*} [AddCommMonoid M] {m : ℕ}
    (g : (i : I417GenIter.Idx (m + 1)) → M) :
    (∑ i : I417GenIter.Idx (m + 1), g i) =
      (∑ i : I417GenIter.Idx m, g (Sum.inl i)) + (∑ b : Bool, g (Sum.inr b)) := by
  rw [← Fintype.sum_sum_type (fun x : I417GenIter.Idx m ⊕ Bool => g x)]
  rfl

/-- **No `χ` is lost or double counted.**  Along any branch, at any stage, the sum over the slots of
`chainE + chainM` is the total number of legs `2 * (n + 1)` of the final diagram.  This is what
converts the closed form `c · χ ^ e · T ^ m` of a branch fibre into the printed normalisation
`χ ^ (2q - ℓ) · T ^ ℓ`: at every split, the arm's `χ ^` power that `chainE` absorbs is exactly the
leg that `chainM` drops. -/
theorem sum_chainE_add_chainM (n : ℕ) (k : (u : Fin n) → I417GenIter.Idx u) :
    ∀ (t : ℕ) (_ : t ≤ n),
      (∑ i : I417GenIter.Idx t, (chainE n k t i + chainM n k t i)) = 2 * (n + 1) := by
  intro t hle
  refine Nat.decreasingInduction (n := n)
    (motive := fun s _ =>
      (∑ i : I417GenIter.Idx s, (chainE n k s i + chainM n k s i)) = 2 * (n + 1)) ?_ ?_ hle
  · intro m hm ih
    have hterm : ∀ i : I417GenIter.Idx m, chainE n k m i + chainM n k m i =
        (chainE n k (m + 1) (Sum.inl i) + chainM n k (m + 1) (Sum.inl i)) +
          (if i = k ⟨m, hm⟩ then
            (chainE n k (m + 1) (Sum.inr false) + chainM n k (m + 1) (Sum.inr false)) +
              (chainE n k (m + 1) (Sum.inr true) + chainM n k (m + 1) (Sum.inr true))
            else 0) := by
      intro i
      rw [chainE_eq_succ n k hm i, chainM_eq_succ n k hm i]
      split <;> omega
    have h1 : (∑ i : I417GenIter.Idx m, (chainE n k m i + chainM n k m i)) =
        (∑ i : I417GenIter.Idx m,
            (chainE n k (m + 1) (Sum.inl i) + chainM n k (m + 1) (Sum.inl i))) +
          ((chainE n k (m + 1) (Sum.inr false) + chainM n k (m + 1) (Sum.inr false)) +
            (chainE n k (m + 1) (Sum.inr true) + chainM n k (m + 1) (Sum.inr true))) := by
      rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib,
        Finset.sum_ite_eq', ite_eq_left (Finset.mem_univ _)]
    have h2 : (∑ i : I417GenIter.Idx m,
          (chainE n k (m + 1) (Sum.inl i) + chainM n k (m + 1) (Sum.inl i))) +
          ((chainE n k (m + 1) (Sum.inr false) + chainM n k (m + 1) (Sum.inr false)) +
            (chainE n k (m + 1) (Sum.inr true) + chainM n k (m + 1) (Sum.inr true))) =
        (∑ i : I417GenIter.Idx m,
          (chainE n k (m + 1) (Sum.inl i) + chainM n k (m + 1) (Sum.inl i))) +
          (∑ b : Bool, (chainE n k (m + 1) (Sum.inr b) + chainM n k (m + 1) (Sum.inr b))) := by
      rw [Fintype.sum_bool]
      ac_rfl
    have h3 : (∑ i : I417GenIter.Idx m,
          (chainE n k (m + 1) (Sum.inl i) + chainM n k (m + 1) (Sum.inl i))) +
          (∑ b : Bool, (chainE n k (m + 1) (Sum.inr b) + chainM n k (m + 1) (Sum.inr b))) =
        ∑ i : I417GenIter.Idx (m + 1), (chainE n k (m + 1) i + chainM n k (m + 1) i) :=
      (sum_idx_succ_eq (M := ℕ) (m := m)
        (fun i => chainE n k (m + 1) i + chainM n k (m + 1) i)).symm
    rw [h1, h2, h3, ih]
  · have htop : ∀ i : I417GenIter.Idx n, chainE n k n i + chainM n k n i = 1 := by
      intro i
      rw [chainE_eq_top (lt_irrefl n) k i, chainM_eq_top (lt_irrefl n) k i]
    rw [Finset.sum_congr rfl (fun i _ => htop i), Finset.sum_const, smul_eq_mul, mul_one,
      Finset.card_univ]
    exact I417GenIter.card_Idx n

end PercLib.CriticalLRP.I417SplitClosedForm
