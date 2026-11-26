/-
Direct bridge from production's actual attachment-history model
(`I417GenIter.Hist`, `Hist.legs`, `Hist.snoc`, `I417FreshDepth.splitChoices`) to the reviewed
order-free spine normal form (`Hang`, `spineVal`).  Proofs only; definitions are in `Defs.lean`.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.HistSpine.Defs
public import PercLib.CriticalLRP.Correlation.I417.Fresh.Spine.Profile

/-!
# One-stage attachment reindexing on actual histories

The arm is summed before the chain structure collapses. The decidability-instance mismatch
in `Hist.legs` is handled by `splitAt_eq_of_decidableEq`, not by a definitional bridge.
-/

open MeasureTheory Measure ProbabilityTheory unitInterval


open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false
set_option linter.style.show false

@[expose] public section

namespace PercLib.CriticalLRP.I417HistToSpine

open PercLib.CriticalLRP
open PercLib.CriticalLRP.I417FreshGenSpine

/-! ## 1. The one-step split, on the leg product

The attachment step `splitAt L s z d` replaces the leg in slot `s` by the two halves `(·,z)`, `(z,·)`
and appends the arm `(z,d)`; every other leg is untouched (`splitAt_inl_of_ne`).  Hence the product
of the `2(n+1)` leg weights factors into the untouched slots, the first half, the second half, and
the arm.  Everything in this section is `ι`-generic, so it applies verbatim at every stage of the
attachment recursion. -/

variable {V : Type*} [Countable V] [DecidableEq V]

theorem prod_splitAt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : ι ⊕ Bool → V → V → ℝ≥0∞) (L : ι → V × V) (s : ι) (z d : V) :
    (∏ j : ι ⊕ Bool, W j ((I417FreshFour.Refined.splitAt L s z d) j).1
        ((I417FreshFour.Refined.splitAt L s z d) j).2) =
      (W (Sum.inl s) (L s).1 z * W (Sum.inr false) z (L s).2 * W (Sum.inr true) z d) *
        ∏ i ∈ Finset.univ.erase s, W (Sum.inl i) (L i).1 (L i).2 := by
  have hsplit : (∏ i : ι, W (Sum.inl i)
        ((I417FreshFour.Refined.splitAt L s z d) (Sum.inl i)).1
        ((I417FreshFour.Refined.splitAt L s z d) (Sum.inl i)).2) =
      W (Sum.inl s) (L s).1 z * ∏ i ∈ Finset.univ.erase s, W (Sum.inl i) (L i).1 (L i).2 := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun i => W (Sum.inl i) ((I417FreshFour.Refined.splitAt L s z d) (Sum.inl i)).1
        ((I417FreshFour.Refined.splitAt L s z d) (Sum.inl i)).2) (Finset.mem_univ s)]
    rw [I417FreshFour.Refined.splitAt_inl_self]
    congr 1
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [Finset.mem_erase] at hi
    rw [I417FreshFour.Refined.splitAt_inl_of_ne (k := s) (i := i) hi.1]
  have hb : (∏ b : Bool, W (Sum.inr b)
        ((I417FreshFour.Refined.splitAt L s z d) (Sum.inr b)).1
        ((I417FreshFour.Refined.splitAt L s z d) (Sum.inr b)).2) =
      W (Sum.inr true) z d * W (Sum.inr false) z (L s).2 := by
    rw [Fintype.prod_bool]
    rfl
  rw [Fintype.prod_sum_type, hsplit, hb]
  ring

/-- **The arm is summed out first.**  Summing the split leg product over the attachment vertex `z`
and the arm target `d` gives the untouched slots times the nested sum
`∑_z W(inl s)(a,z) · W(inr false)(z,b) · ∑_d W(inr true)(z,d)`: the inner sum over the arm `d` is
taken *before* the outer sum inserts `z` into the chain.  This is the elementary reindexing that the
hand-ordered `q = 4` evaluation performs once for each of its 48 branches. -/
theorem tsum_splitAt_prod {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : ι ⊕ Bool → V → V → ℝ≥0∞) (L : ι → V × V) (s : ι) :
    (∑' z : V, ∑' d : V, ∏ j : ι ⊕ Bool,
        W j ((I417FreshFour.Refined.splitAt L s z d) j).1
          ((I417FreshFour.Refined.splitAt L s z d) j).2) =
      (∏ i ∈ Finset.univ.erase s, W (Sum.inl i) (L i).1 (L i).2) *
        ∑' z : V, W (Sum.inl s) (L s).1 z * W (Sum.inr false) z (L s).2 *
          (∑' d : V, W (Sum.inr true) z d) := by
  set K : ℝ≥0∞ := ∏ i ∈ Finset.univ.erase s, W (Sum.inl i) (L i).1 (L i).2 with hK
  have hinner : ∀ z : V, (∑' d : V, ∏ j : ι ⊕ Bool,
        W j ((I417FreshFour.Refined.splitAt L s z d) j).1
          ((I417FreshFour.Refined.splitAt L s z d) j).2) =
      K * (W (Sum.inl s) (L s).1 z * W (Sum.inr false) z (L s).2 *
        (∑' d : V, W (Sum.inr true) z d)) := by
    intro z
    calc (∑' d : V, ∏ j : ι ⊕ Bool,
          W j ((I417FreshFour.Refined.splitAt L s z d) j).1
            ((I417FreshFour.Refined.splitAt L s z d) j).2)
        = ∑' d : V, (W (Sum.inl s) (L s).1 z * W (Sum.inr false) z (L s).2 *
            W (Sum.inr true) z d) * K := by
          refine tsum_congr fun d => ?_
          rw [prod_splitAt, ← hK]
      _ = (∑' d : V, W (Sum.inl s) (L s).1 z * W (Sum.inr false) z (L s).2 *
            W (Sum.inr true) z d) * K := ENNReal.tsum_mul_right
      _ = ((W (Sum.inl s) (L s).1 z * W (Sum.inr false) z (L s).2) *
            (∑' d : V, W (Sum.inr true) z d)) * K := by
          rw [ENNReal.tsum_mul_left]
      _ = K * (W (Sum.inl s) (L s).1 z * W (Sum.inr false) z (L s).2 *
            (∑' d : V, W (Sum.inr true) z d)) := by ring
  calc (∑' z : V, ∑' d : V, ∏ j : ι ⊕ Bool,
        W j ((I417FreshFour.Refined.splitAt L s z d) j).1
          ((I417FreshFour.Refined.splitAt L s z d) j).2)
      = ∑' z : V, K * (W (Sum.inl s) (L s).1 z * W (Sum.inr false) z (L s).2 *
          (∑' d : V, W (Sum.inr true) z d)) := tsum_congr hinner
    _ = K * ∑' z : V, W (Sum.inl s) (L s).1 z * W (Sum.inr false) z (L s).2 *
          (∑' d : V, W (Sum.inr true) z d) := ENNReal.tsum_mul_left
    _ = (∏ i ∈ Finset.univ.erase s, W (Sum.inl i) (L i).1 (L i).2) *
          ∑' z : V, W (Sum.inl s) (L s).1 z * W (Sum.inr false) z (L s).2 *
            (∑' d : V, W (Sum.inr true) z d) := by rw [← hK]


/-! ## 2. The two kernel identities the spine normal form needs

`iterPow` is production's matrix power `T^ℓ` (`I417Base.iterPow`, `iterPow k (n+1) v w =
∑_u k v u · iterPow k n u w`).  The printed fresh normal form `χ^(2q-ℓ) · T^ℓ(w,y)` needs exactly
two facts about it, both of which are used by the hand-ordered `q = 4` evaluation at every branch
and by the order-free spine evaluation (`spineVal_eq`) at every `ℓ`:

* `tsum_iterPow_succ` — **a hanging chain of `m+1` legs contributes `χ^(m+1)`**: summing the far
  endpoint of `T^(m+1)(a,·)` over all of `V` gives one `χ` for each of its `m+1` free vertices.
* `tsum_iterPow_mul` — **chains compose**: inserting a summed intermediate vertex between two
  chains splices their lengths.

Both are stated for an arbitrary kernel with constant row sum `χ`, i.e. exactly the hypothesis set
of `GenFreshEval`. -/

section Kernel

variable {τ : V → V → ℝ≥0∞} {χ : ℝ≥0∞}

/-- `T^1 = τ`: one step of the kernel power. -/
theorem iterPow_one_eq (a b : V) : I417Base.iterPow τ 1 a b = τ a b := by
  change (∑' u : V, τ a u * (if u = b then (1 : ℝ≥0∞) else 0)) = τ a b
  refine Eq.trans (tsum_eq_single b fun u hu => ?_) ?_
  · have h : (if u = b then (1 : ℝ≥0∞) else 0) = 0 := by simp [hu]
    rw [h, mul_zero]
  · have h : (if b = b then (1 : ℝ≥0∞) else 0) = 1 := by simp
    rw [h, mul_one]

/-- **A hanging chain of `m + 1` legs contributes `χ ^ (m + 1)`.** -/
theorem tsum_iterPow_succ (hχ : ∀ a : V, ∑' b : V, τ a b = χ) :
    ∀ (m : ℕ) (a : V), (∑' b : V, I417Base.iterPow τ (m + 1) a b) = χ ^ (m + 1)
  | 0, a => by
      show (∑' b : V, I417Base.iterPow τ 1 a b) = χ ^ 1
      rw [tsum_congr fun b => iterPow_one_eq a b, hχ a, pow_one]
  | m + 1, a => by
      have hstep : ∀ b : V, I417Base.iterPow τ (m + 2) a b =
          ∑' u : V, τ a u * I417Base.iterPow τ (m + 1) u b := fun b => rfl
      calc (∑' b : V, I417Base.iterPow τ (m + 2) a b)
          = ∑' b : V, ∑' u : V, τ a u * I417Base.iterPow τ (m + 1) u b :=
            tsum_congr hstep
        _ = ∑' u : V, ∑' b : V, τ a u * I417Base.iterPow τ (m + 1) u b :=
            ENNReal.tsum_comm
        _ = ∑' u : V, τ a u * (∑' b : V, I417Base.iterPow τ (m + 1) u b) :=
            tsum_congr fun u => ENNReal.tsum_mul_left
        _ = ∑' u : V, τ a u * χ ^ (m + 1) :=
            tsum_congr fun u => by rw [tsum_iterPow_succ hχ m u]
        _ = χ * χ ^ (m + 1) := by rw [ENNReal.tsum_mul_right, hχ]
        _ = χ ^ (m + 2) := by
            rw [show χ ^ (m + 1 + 1) = χ ^ (m + 2) from rfl, pow_succ, pow_succ]
            ring

/-- **Chains compose**: `∑_z T^m(a,z) · T^{m'}(z,b) = T^{m+m'}(a,b)`. -/
theorem tsum_iterPow_mul :
    ∀ (m : ℕ) (m' : ℕ) (a b : V),
      (∑' z : V, I417Base.iterPow τ m a z * I417Base.iterPow τ m' z b) =
        I417Base.iterPow τ (m + m') a b
  | 0, m', a, b => by
      rw [Nat.zero_add]
      refine Eq.trans (tsum_eq_single a fun z hz => ?_) ?_
      · have h0 : I417Base.iterPow τ 0 a z = 0 := by
          change (if a = z then (1 : ℝ≥0∞) else 0) = 0
          simp [Ne.symm hz]
        rw [h0, zero_mul]
      · have h1 : I417Base.iterPow τ 0 a a = 1 := by
          change (if a = a then (1 : ℝ≥0∞) else 0) = 1
          simp
        rw [h1, one_mul]
  | m + 1, m', a, b => by
      have hmove : ∀ z : V, I417Base.iterPow τ (m + 1) a z * I417Base.iterPow τ m' z b =
          ∑' u : V, (τ a u * I417Base.iterPow τ m u z) *
            I417Base.iterPow τ m' z b := by
        intro z
        rw [show I417Base.iterPow τ (m + 1) a z =
          ∑' u : V, τ a u * I417Base.iterPow τ m u z from rfl,
          ENNReal.tsum_mul_right]
      calc (∑' z : V, I417Base.iterPow τ (m + 1) a z *
            I417Base.iterPow τ m' z b)
          = ∑' z : V, ∑' u : V, (τ a u * I417Base.iterPow τ m u z) *
              I417Base.iterPow τ m' z b := tsum_congr hmove
        _ = ∑' u : V, ∑' z : V, (τ a u * I417Base.iterPow τ m u z) *
              I417Base.iterPow τ m' z b := ENNReal.tsum_comm
        _ = ∑' u : V, τ a u * (∑' z : V, I417Base.iterPow τ m u z *
              I417Base.iterPow τ m' z b) := by
            refine tsum_congr fun u => ?_
            rw [show (∑' z : V, (τ a u * I417Base.iterPow τ m u z) *
                I417Base.iterPow τ m' z b)
                = ∑' z : V, τ a u * (I417Base.iterPow τ m u z *
                  I417Base.iterPow τ m' z b) from
              tsum_congr fun z => by ring,
              ENNReal.tsum_mul_left]
        _ = ∑' u : V, τ a u * I417Base.iterPow τ (m + m') u b :=
            tsum_congr fun u => by rw [tsum_iterPow_mul m m' u b]
        _ = I417Base.iterPow τ (m + 1 + m') a b := by
            rw [show m + 1 + m' = m + m' + 1 from by omega]
            rfl

/-- **A hanging chain with `m ≥ 1` legs contributes `χ ^ m`**; the `m = 0` case is the diagonal
indicator and is deliberately excluded. -/
theorem tsum_iterPow_chain (hχ : ∀ a : V, ∑' b : V, τ a b = χ) (m : ℕ) (hm : 1 ≤ m) (a : V) :
    (∑' b : V, I417Base.iterPow τ m a b) = χ ^ m := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  exact tsum_iterPow_succ hχ m' a

end Kernel


/-! ## 3. The reindexing at the level of one actual attachment history

`histW_snoc_tsum` is the local form of the step: for **one** attachment history `H` at stage `n`, the
sum over the next attachment point `z` and the next arm `d` of the `2(n+1)`-leg product of
`Hist.snoc H s z d` equals the `2n`-leg product of `H` with the split weight `splitWt W s`.  Here the
inner `∑_d` is performed first, at the split vertex, and only then is `z` summed into the chain —
the order the printed proof uses and the opposite of summing in attachment-time order.

`histFibre_zero` is the base of the attachment recursion evaluated on the actual production objects:
at `n = 0` there is nothing left to sum but the arm target, and the answer is the spine normal form
`χ ^ (2·1 - 1) · T^1(y,w)`. -/

section HistStep

variable {τ : V → V → ℝ≥0∞} {χ : ℝ≥0∞}

/- Production's `Hist.legs` is elaborated under `Classical.propDecidable` (a local instance of
`Fresh/Iter/Defs.lean`), so the same instance is used here whenever a `splitAt` of an actual
history leg is compared with an unfolded one. -/
attribute [local instance] Classical.propDecidable

/-- `splitAt` does not depend on which `DecidableEq` instance on the index type is used: the two
`if i = k` tests have the same proposition, so they agree.  This is needed because production's
`Hist.legs` is elaborated under `Classical.propDecidable` (a local instance inside
`Fresh/Iter/Defs.lean`) while `I417FreshDepth.instDecidableEqIdx` is a global instance; the two are
not definitionally equal, so the endpoint equation has to be transported. -/
theorem splitAt_eq_of_decidableEq {ι : Type*} (d₁ d₂ : DecidableEq ι) (L : ι → V × V) (k : ι)
    (z d : V) :
    @I417FreshFour.Refined.splitAt V ι d₁ L k z d =
      @I417FreshFour.Refined.splitAt V ι d₂ L k z d := by
  funext i
  cases i with
  | inl i => simp only [I417FreshFour.Refined.splitAt]; by_cases h : i = k <;> simp [h]
  | inr b => cases b <;> rfl

/-- The product of `splitWt` weights expands into the untouched slots times the nested sum over the
split vertex and the arm. -/
theorem prod_splitWt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : ι ⊕ Bool → V → V → ℝ≥0∞) (s : ι) (L : ι → V × V) :
    (∏ i : ι, splitWt W s i (L i).1 (L i).2) =
      (∏ i ∈ Finset.univ.erase s, W (Sum.inl i) (L i).1 (L i).2) *
        ∑' z : V, W (Sum.inl s) (L s).1 z * W (Sum.inr false) z (L s).2 *
          (∑' d : V, W (Sum.inr true) z d) := by
  rw [← Finset.mul_prod_erase Finset.univ
    (fun i => splitWt W s i (L i).1 (L i).2) (Finset.mem_univ s)]
  have hself : splitWt W s s (L s).1 (L s).2 =
      ∑' z : V, W (Sum.inl s) (L s).1 z * W (Sum.inr false) z (L s).2 *
        (∑' d : V, W (Sum.inr true) z d) := by
    simp [splitWt]
  have hprodeq : (∏ i ∈ Finset.univ.erase s, splitWt W s i (L i).1 (L i).2) =
      ∏ i ∈ Finset.univ.erase s, W (Sum.inl i) (L i).1 (L i).2 := by
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [Finset.mem_erase] at hi
    simp [splitWt, hi.1]
  rw [hself, hprodeq, mul_comm]

/-- **One attachment step on an actual history.**  Summing the product of the `2(n+1)` leg weights
of `Hist.snoc H s z d` over the attachment vertex `z` and the arm `d` collapses it to the `2n`-leg
product of `H` with the split weight `splitWt W s` in slot `s`. -/
theorem histW_snoc_tsum {n : ℕ} (W : I417GenIter.Idx (n + 1) → V → V → ℝ≥0∞)
    (H : I417GenIter.Hist V n) (s : I417GenIter.Idx n) (y w ga : V) :
    (∑' z : V, ∑' d : V, histW W (I417GenIter.Hist.snoc H s z d) y w ga) =
      histW (splitWt W s) H y w ga := by
  have hterm : ∀ z d : V, histW W (I417GenIter.Hist.snoc H s z d) y w ga =
      ∏ j : I417GenIter.Idx n ⊕ Bool,
        W j ((I417FreshFour.Refined.splitAt (H.legs y w ga) s z d) j).1
          ((I417FreshFour.Refined.splitAt (H.legs y w ga) s z d) j).2 := by
    intro z d
    simp only [histW, I417GenIter.Hist.legs]
    exact Finset.prod_congr rfl fun i _ => by rw [splitAt_eq_of_decidableEq]
  calc (∑' z : V, ∑' d : V, histW W (I417GenIter.Hist.snoc H s z d) y w ga)
      = ∑' z : V, ∑' d : V, ∏ j : I417GenIter.Idx n ⊕ Bool,
          W j ((I417FreshFour.Refined.splitAt (H.legs y w ga) s z d) j).1
            ((I417FreshFour.Refined.splitAt (H.legs y w ga) s z d) j).2 := by
        refine tsum_congr fun z => tsum_congr fun d => ?_
        exact hterm z d
    _ = (∏ i ∈ Finset.univ.erase s, W (Sum.inl i) (H.legs y w ga i).1 (H.legs y w ga i).2) *
          ∑' z : V, W (Sum.inl s) (H.legs y w ga s).1 z * W (Sum.inr false) z (H.legs y w ga s).2 *
            (∑' d : V, W (Sum.inr true) z d) :=
        tsum_splitAt_prod W (fun i => H.legs y w ga i) s
    _ = histW (splitWt W s) H y w ga :=
        (prod_splitWt W s (fun i => H.legs y w ga i)).symm

end HistStep

end PercLib.CriticalLRP.I417HistToSpine
