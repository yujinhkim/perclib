/-
Theorems for direction `HISTORY-FIBRE-PACKAGING` (swarm `smwxfstjy`, member `m1`).
Proofs only; every definition is in `Defs.lean`, the axiom audit is `Check.lean`.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.HistFibre.Defs
public import PercLib.CriticalLRP.Correlation.I417.Fresh.Depth.Main

/-!
# The history fibre of the iterated first-hit cover, packaged

Production's `I417HistToSpine.histW_snoc_tsum` performs one attachment round inside a single
history.  Part 1--2 below turns it into an iteration over the whole *history fibre*: the
histories of stage `n + 1` whose split choices are `finSnoc k s` are exactly the `snoc H s z d`
with `splitChoices H = k`, so the fibre sum over `finSnoc k s` is the arm-first sum over the
fibre over `k` (`histFibre_snoc`, `histFibre_snoc_splitWt`).  Part 3 iterates this down the whole
spine, using the closed form `slotW` and `slotW_step` of the accepted
`Fresh.SplitClosedForm`; part 4 evaluates the two-slot base stage, and part 5 sums the free arm
target to obtain the branch value `χ ^ (2(n+1) - ℓ) · T ^ ℓ (y,w)` with `ℓ = chainM n k 0 idxZero`.

Part 6 identifies `chainM n k 0 idxZero` with the printed pin--mark depth `markDepthK n k`, so the
same value is `χ ^ (2(n+1) - markDepthK n k) · T ^ (markDepthK n k) (y,w)`.
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

@[expose] public section

namespace PercLib.CriticalLRP.I417HistFibre

open PercLib.CriticalLRP

variable {V : Type*} [Countable V] [DecidableEq V]

/-! ## 0. A monomorphic `tsum_congr` for `ℝ≥0∞` -/

/-- `tsum_congr` with the additive monoid fixed, so that the `TopologicalSpace` instance is never
asked for a metavariable type. -/
theorem tsum_congr_ennreal {α : Type*} {f g : α → ℝ≥0∞} (h : ∀ a, f a = g a) :
    (∑' a, f a) = ∑' a, g a :=
  tsum_congr h

/-! ## 1. The split-choice tuple of a `snoc` -/

theorem splitChoices_snoc_apply_last {n : ℕ} (H : I417GenIter.Hist V n)
    (s : I417GenIter.Idx n) (z d : V) :
    I417FreshDepth.splitChoices (I417GenIter.Hist.snoc H s z d) (Fin.last n) = s := by
  rw [splitChoices_snoc, finSnoc, Fin.snoc_last]

theorem splitChoices_snoc_apply_castSucc {n : ℕ} (H : I417GenIter.Hist V n)
    (s : I417GenIter.Idx n) (z d : V) (t : Fin n) :
    I417FreshDepth.splitChoices (I417GenIter.Hist.snoc H s z d) t.castSucc =
      I417FreshDepth.splitChoices H t := by
  rw [splitChoices_snoc, finSnoc, Fin.snoc_castSucc]

/-! ## 2. The one-round fibre reindexing -/

/-- **The fibre of one attachment round.**  Summing the leg product over all histories of stage
`n + 1` whose split choices are `finSnoc k s` is the same as summing, over the tail histories with
split choices `k`, over the attachment vertex `z` and the arm `d`. -/
theorem histFibre_snoc {n : ℕ} (W : I417GenIter.Idx (n + 1) → V → V → ℝ≥0∞)
    (k : (t : Fin n) → I417GenIter.Idx t) (s : I417GenIter.Idx n) (y w ga : V) :
    I417HistToSpine.histFibre W y w (finSnoc k s) ga =
      ∑' H : {H : I417GenIter.Hist V n // I417FreshDepth.splitChoices H = k},
        ∑' z : V, ∑' d : V,
          I417HistToSpine.histW W (I417GenIter.Hist.snoc H.1 s z d) y w ga := by
  rw [I417HistToSpine.histFibre]
  rw [← Equiv.tsum_eq (fibreSnocEquiv (V := V) k s).symm
    (fun H' => I417HistToSpine.histW W H'.1 y w ga)]
  rw [ENNReal.tsum_prod']
  refine tsum_congr_ennreal fun H => ?_
  rw [ENNReal.tsum_prod']
  exact tsum_congr_ennreal fun z => tsum_congr_ennreal fun d => rfl

/-- **The one-round fibre iteration**: on the fibre over `finSnoc k s`, the arm and the attachment
vertex are summed out first, leaving the split weight `splitWt W s` on the fibre over `k`.  This is
production's `histW_snoc_tsum` uniformly in the tail history. -/
theorem histFibre_snoc_splitWt {n : ℕ} (W : I417GenIter.Idx (n + 1) → V → V → ℝ≥0∞)
    (k : (t : Fin n) → I417GenIter.Idx t) (s : I417GenIter.Idx n) (y w ga : V) :
    I417HistToSpine.histFibre W y w (finSnoc k s) ga =
      I417HistToSpine.histFibre (I417HistToSpine.splitWt W s) y w k ga := by
  rw [histFibre_snoc, I417HistToSpine.histFibre]
  exact tsum_congr_ennreal fun H => I417HistToSpine.histW_snoc_tsum W H.1 s y w ga

/-! ## 3. The base of the fibre recursion -/

/-- At stage `0` there is nothing to sum over but the unique history `nil`, whose split-choice
tuple is the unique tuple of length `0`. -/
theorem histFibre_zero (W : I417GenIter.Idx 0 → V → V → ℝ≥0∞)
    (k : (t : Fin 0) → I417GenIter.Idx t) (y w ga : V) :
    I417HistToSpine.histFibre W y w k ga = I417HistToSpine.histW W I417GenIter.Hist.nil y w ga := by
  rw [I417HistToSpine.histFibre,
    tsum_eq_single ⟨I417GenIter.Hist.nil, by funext t; exact t.elim0⟩]
  · intro b hb
    exact absurd (Subtype.ext (by cases b.1; rfl)) hb

/-! ## 4. The tuples of a succ-stage branch -/

/-- The split-choice tuple of `n + 1` rounds is its first `n` rounds, extended by the last one. -/
theorem restr_succ {n : ℕ} (k : (t : Fin n) → I417GenIter.Idx t) {t : ℕ} (h : t + 1 ≤ n) :
    I417SplitClosedForm.restr k (t + 1) h =
      finSnoc (I417SplitClosedForm.restr k t (le_trans (Nat.le_succ t) h))
        (k ⟨t, lt_of_lt_of_le (Nat.lt_succ_self t) h⟩) := by
  funext u
  refine Fin.lastCases ?_ ?_ u
  · simp [I417SplitClosedForm.restr, finSnoc]
  · intro v
    simp [I417SplitClosedForm.restr, finSnoc]

theorem restr_self {n : ℕ} (k : (t : Fin n) → I417GenIter.Idx t) :
    I417SplitClosedForm.restr k n le_rfl = k := by
  funext u
  rfl

/-! ## 5. Iterating the fibre recursion down the spine -/

/-- **The fibre iteration.**  Starting from the closed-form slot weights `slotW τ χ n k t` at
stage `t`, one round of `histFibre_snoc_splitWt` peels a round off the fibre and one application of
`slotW_step` absorbs it into the closed form, so the whole fibre at stage `t` already carries the
final value. -/
theorem histFibre_slotW_iter {n : ℕ} (τ : V → V → ℝ≥0∞) (χ : ℝ≥0∞)
    (hχ : ∀ a : V, ∑' b : V, τ a b = χ) (k : (t : Fin n) → I417GenIter.Idx t) (y w ga : V) :
    ∀ (t : ℕ) (ht : t ≤ n),
      I417HistToSpine.histFibre (I417SplitClosedForm.slotW τ χ n k t) y w
          (I417SplitClosedForm.restr k t ht) ga =
        I417HistToSpine.histW (I417SplitClosedForm.slotW τ χ n k 0) I417GenIter.Hist.nil y w ga := by
  intro t ht
  induction t with
  | zero => exact histFibre_zero _ _ y w ga
  | succ t ih =>
    have hle : t ≤ n := le_trans (Nat.le_succ t) ht
    have hlt : t < n := lt_of_lt_of_le (Nat.lt_succ_self t) ht
    rw [restr_succ k ht, histFibre_snoc_splitWt]
    rw [show I417HistToSpine.splitWt (I417SplitClosedForm.slotW τ χ n k (t + 1))
          (k ⟨t, hlt⟩) = I417SplitClosedForm.slotW τ χ n k t from
        funext fun i => I417SplitClosedForm.slotW_step τ χ hχ n k hlt i]
    exact ih hle

theorem slotW_top_fun {n : ℕ} (τ : V → V → ℝ≥0∞) (χ : ℝ≥0∞)
    (k : (t : Fin n) → I417GenIter.Idx t) :
    I417SplitClosedForm.slotW τ χ n k n = fun _ => τ := by
  funext i
  exact I417SplitClosedForm.slotW_top τ χ n k i

/-- **The whole history fibre at the top stage**, in closed form: it is the leg product of the
stage-`0` slot weights, i.e. of the two-leg base diagram with every remaining split absorbed. -/
theorem histFibre_eq_histW_slotW {n : ℕ} (τ : V → V → ℝ≥0∞) (χ : ℝ≥0∞)
    (hχ : ∀ a : V, ∑' b : V, τ a b = χ) (k : (t : Fin n) → I417GenIter.Idx t) (y w ga : V) :
    I417HistToSpine.histFibre (fun _ => τ) y w k ga =
      I417HistToSpine.histW (I417SplitClosedForm.slotW τ χ n k 0) I417GenIter.Hist.nil y w ga := by
  have h := histFibre_slotW_iter τ χ hχ k y w ga n le_rfl
  rw [restr_self, slotW_top_fun] at h
  exact h

/-! ## 6. The stage-`0` evaluation -/

/-- The stage-`0` leg product: the base legs are `(y,w)` and `(w,ga)`. -/
theorem histW_nil_eq (W : I417GenIter.Idx 0 → V → V → ℝ≥0∞) (y w ga : V) :
    I417HistToSpine.histW W I417GenIter.Hist.nil y w ga =
      W I417FreshDepth.idxZero y w * W idxOne w ga := by
  rw [show I417HistToSpine.histW W I417GenIter.Hist.nil y w ga =
    ∏ i : Fin 2, W i (I417FreshFour.Refined.baseLegs y w ga i).1
      (I417FreshFour.Refined.baseLegs y w ga i).2 from rfl,
    Fin.prod_univ_two]
  simp [I417FreshFour.Refined.baseLegs, I417FreshDepth.idxZero, idxOne]

/-- **The stage-`0` value of the closed form**: the pin--mark slot carries the chain `y → w` and
the mark--arm slot the chain `w → ga`, each with its own `χ`-exponent. -/
theorem histW_slotW_zero {n : ℕ} (τ : V → V → ℝ≥0∞) (χ : ℝ≥0∞)
    (k : (t : Fin n) → I417GenIter.Idx t) (y w ga : V) :
    I417HistToSpine.histW (I417SplitClosedForm.slotW τ χ n k 0) I417GenIter.Hist.nil y w ga =
      (χ ^ I417SplitClosedForm.chainE n k 0 I417FreshDepth.idxZero *
          I417Base.iterPow τ (I417SplitClosedForm.chainM n k 0 I417FreshDepth.idxZero) y w) *
        (χ ^ I417SplitClosedForm.chainE n k 0 idxOne *
          I417Base.iterPow τ (I417SplitClosedForm.chainM n k 0 idxOne) w ga) := by
  rw [histW_nil_eq]
  simp [I417SplitClosedForm.slotW]

/-! ## 7. The branch value -/

/-- **The value of one branch fibre, with the free arm target summed.**  For a constant-row-sum
kernel the fibre over the split choices `k` evaluates to
`χ ^ (2(n+1) - ℓ) · T^ℓ(y,w)` with `ℓ = chainM n k 0 idxZero` the number of legs of the
pin--mark chain: the mark--arm chain `w → ga` is summed out (it has at least one leg) and the
`χ`-exponents and chain lengths of the two base slots add up to the full leg count. -/
theorem tsum_histFibre_chainM {n : ℕ} (τ : V → V → ℝ≥0∞) (χ : ℝ≥0∞)
    (hχ : ∀ a : V, ∑' b : V, τ a b = χ) (k : (t : Fin n) → I417GenIter.Idx t) (y w : V) :
    (∑' ga : V, I417HistToSpine.histFibre (fun _ => τ) y w k ga) =
      χ ^ (2 * (n + 1) - I417SplitClosedForm.chainM n k 0 I417FreshDepth.idxZero) *
        I417Base.iterPow τ (I417SplitClosedForm.chainM n k 0 I417FreshDepth.idxZero) y w := by
  have hm0 : 1 ≤ I417SplitClosedForm.chainM n k 0 I417FreshDepth.idxZero :=
    I417SplitClosedForm.chainM_pos n k 0 (Nat.zero_le n) _
  have hm1 : 1 ≤ I417SplitClosedForm.chainM n k 0 idxOne :=
    I417SplitClosedForm.chainM_pos n k 0 (Nat.zero_le n) _
  have hcon : (I417SplitClosedForm.chainE n k 0 I417FreshDepth.idxZero +
        I417SplitClosedForm.chainM n k 0 I417FreshDepth.idxZero) +
      (I417SplitClosedForm.chainE n k 0 idxOne +
        I417SplitClosedForm.chainM n k 0 idxOne) = 2 * (n + 1) := by
    have h : (∑ i : Fin 2, (I417SplitClosedForm.chainE n k 0 i +
        I417SplitClosedForm.chainM n k 0 i)) = 2 * (n + 1) :=
      I417SplitClosedForm.sum_chainE_add_chainM n k 0 (Nat.zero_le n)
    rw [Fin.sum_univ_two] at h
    exact h
  rw [tsum_congr_ennreal fun ga => by
    rw [histFibre_eq_histW_slotW τ χ hχ k y w ga, histW_slotW_zero]]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
  rw [I417HistToSpine.tsum_iterPow_chain hχ (I417SplitClosedForm.chainM n k 0 idxOne) hm1 w]
  have he : 2 * (n + 1) - I417SplitClosedForm.chainM n k 0 I417FreshDepth.idxZero =
      I417SplitClosedForm.chainE n k 0 I417FreshDepth.idxZero +
        I417SplitClosedForm.chainE n k 0 idxOne +
        I417SplitClosedForm.chainM n k 0 idxOne := by omega
  rw [he, pow_add, pow_add]
  ring

end PercLib.CriticalLRP.I417HistFibre
