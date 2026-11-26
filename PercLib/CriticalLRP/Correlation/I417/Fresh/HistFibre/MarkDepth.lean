/-
Identification of the closed-form chain length `chainM` with the printed pin--mark depth
`I417FreshDepth.markDepthK` (direction `HISTORY-FIBRE-PACKAGING`, swarm `smwxfstjy`, member `m1`).
Proofs only; every definition is in `Defs.lean`.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.HistFibre.Defs
public import PercLib.CriticalLRP.Correlation.I417.Fresh.Depth.Main

/-!
# The first slot's chain is the pin--mark path

`I417SplitClosedForm.chainM` unfolds the split choices from the *first* round downwards, while
production's `I417FreshDepth.pathLegsK` builds the pin--mark path up from the *last* round.  This
file shows that the two recursions compute the same set of slots of the final diagram
(`chainF_zero_eq_pathLegsK`), hence the same cardinality, and therefore
`chainM n k 0 idxZero = markDepthK n k`: the first slot's chain length *is* the printed `ℓ` of the
fresh normal form.

The forward propagation `chainF` is a finite set of slots, so the bridge is carried by three
elementary facts: it commutes with unions (`chainF_union`), the chain sets of distinct slots are
disjoint (`chainF_singleton_disjoint`), and adding one round commutes with the recursion
(`chainF_succ_last`).
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.style.longLine false

@[expose] public section

namespace PercLib.CriticalLRP.I417HistFibre

open PercLib.CriticalLRP
open PercLib.CriticalLRP.I417GenIter (Idx)
open PercLib.CriticalLRP.I417FreshDepth (pathLegsK markDepthK idxZero)
open PercLib.CriticalLRP.I417SplitClosedForm (chainM)

/-! ## 1. Unfolding the forward propagation and the step -/

theorem slotInl_injective {m : ℕ} : Function.Injective (slotInl (m := m)) :=
  fun _ _ h => Sum.inl.inj h

theorem slotInl_ne_slotInr {m : ℕ} (a : Idx m) (b : Bool) :
    slotInl a ≠ slotInr (m := m) b := by
  change Sum.inl a ≠ Sum.inr b
  intro h
  exact nomatch h

theorem chainF_eq_succ {n : ℕ} (k : (u : Fin n) → Idx u) (t : Fin (n + 1)) (h : t.val < n)
    (S : Finset (Idx t.val)) :
    chainF n k t S =
      chainF n k ⟨t.val + 1, Nat.succ_lt_succ h⟩ (stepSet (k ⟨t.val, h⟩) S) := by
  rw [chainF]
  exact dite_eq_left h

theorem chainF_eq_top {n : ℕ} (k : (u : Fin n) → Idx u) (S : Finset (Idx n)) :
    chainF n k ⟨n, Nat.lt_succ_self n⟩ S = S := by
  rw [chainF]
  rw [dite_eq_right (lt_irrefl n)]

theorem stepArm_eq_empty {m : ℕ} {j a : Idx m} (h : a ≠ j) : stepArm j a = ∅ := by
  by_cases h' : j = a
  · exact absurd h'.symm h
  · simp [stepArm, h, h']

theorem stepArm_eq_singleton {m : ℕ} {j a : Idx m} (h : a = j) :
    stepArm j a = ({slotInr false} : Finset (Idx (m + 1))) := by
  subst h
  simp [stepArm]

theorem stepSet_empty {m : ℕ} (j : Idx m) : stepSet j (∅ : Finset (Idx m)) = ∅ := by
  rw [stepSet, Finset.image_empty, Finset.empty_union]
  rw [ite_eq_right (by simp)]

theorem stepSet_union {m : ℕ} (j : Idx m) (A B : Finset (Idx m)) :
    stepSet j (A ∪ B) = stepSet j A ∪ stepSet j B := by
  rw [stepSet, stepSet, stepSet, Finset.image_union]
  by_cases hA : j ∈ A <;> by_cases hB : j ∈ B <;>
    simp [hA, hB, Finset.mem_union, Finset.union_assoc, Finset.union_comm]

theorem stepSet_singleton {m : ℕ} (j a : Idx m) :
    stepSet j ({a} : Finset (Idx m)) = {slotInl a} ∪ stepArm j a := by
  rw [stepSet, Finset.image_singleton]
  by_cases h : a = j
  · subst h
    simp [stepArm]
  · have h' : ¬ j = a := fun hc => h hc.symm
    simp [stepArm, h, h']

/-- The `erase`/`image` form of the step, which is the form production's `pathLegsK` uses. -/
theorem stepSet_eq_erase_image {m : ℕ} (j : Idx m) (A : Finset (Idx m)) :
    stepSet j A = if j ∈ A then (A.erase j).image slotInl ∪ {slotInl j, slotInr false}
      else A.image slotInl := by
  by_cases h : j ∈ A
  · rw [stepSet, ite_eq_left h, ite_eq_left h, ← Finset.insert_erase h, Finset.image_insert]
    simp [Finset.singleton_union, Finset.union_assoc, Finset.union_comm]
  · rw [stepSet, ite_eq_right h, ite_eq_right h, Finset.union_empty]

/-! ## 2. Forward induction along the attachment rounds -/

/-- **Forward recursion principle for `chainF`.**  A property of the slots `t : Fin (n+1)` that is
preserved by one attachment round and holds at the top stage `t = n` holds at every stage. -/
theorem chainF_ind (n : ℕ) (k : (u : Fin n) → Idx u) (P : (t : Fin (n + 1)) → Prop)
    (hstep : ∀ (t : Fin (n + 1)) (h : t.val < n),
      P ⟨t.val + 1, Nat.succ_lt_succ h⟩ → P t)
    (htop : P ⟨n, Nat.lt_succ_self n⟩) : ∀ t, P t := by
  intro t
  have key : ∀ d : ℕ, ∀ t : Fin (n + 1), n - t.val = d → P t := by
    intro d
    induction d with
    | zero =>
      intro t ht
      have hle : n ≤ t.val := by omega
      have htn : t.val = n := Nat.le_antisymm (Nat.le_of_lt_succ t.isLt) hle
      rw [show t = ⟨n, Nat.lt_succ_self n⟩ from Fin.ext htn]
      exact htop
    | succ d ih =>
      intro t ht
      have hlt : t.val < n := by omega
      have hd : n - (t.val + 1) = d := by omega
      exact hstep t hlt (ih ⟨t.val + 1, Nat.succ_lt_succ hlt⟩ hd)
  exact key (n - t.val) t rfl

theorem chainF_empty (n : ℕ) (k : (u : Fin n) → Idx u) (t : Fin (n + 1)) :
    chainF n k t (∅ : Finset (Idx t.val)) = ∅ := by
  refine chainF_ind n k (fun t => chainF n k t (∅ : Finset (Idx t.val)) = ∅) ?_ ?_ t
  · intro t h ih
    rw [chainF_eq_succ (k := k) (t := t) h]
    exact ih
  · rw [chainF_eq_top]

theorem chainF_union (n : ℕ) (k : (u : Fin n) → Idx u) (t : Fin (n + 1))
    (A B : Finset (Idx t.val)) :
    chainF n k t (A ∪ B) = chainF n k t A ∪ chainF n k t B := by
  refine chainF_ind n k (fun t => ∀ A B : Finset (Idx t.val),
    chainF n k t (A ∪ B) = chainF n k t A ∪ chainF n k t B) ?_ ?_ t A B
  · intro t h ih A B
    rw [chainF_eq_succ (k := k) (t := t) h, chainF_eq_succ (k := k) (t := t) h,
      chainF_eq_succ (k := k) (t := t) h, stepSet_union, ih]
  · intro A B
    rw [chainF_eq_top, chainF_eq_top, chainF_eq_top]

theorem chainF_singleton_disjoint (n : ℕ) (k : (u : Fin n) → Idx u) (t : Fin (n + 1))
    {a b : Idx t.val} (hab : a ≠ b) :
    Disjoint (chainF n k t {a}) (chainF n k t {b}) := by
  refine chainF_ind n k (fun t => ∀ a b : Idx t.val, a ≠ b →
    Disjoint (chainF n k t {a}) (chainF n k t {b})) ?_ ?_ t a b hab
  · intro t h ih a b hab
    have hA : chainF n k t {a} =
        chainF n k ⟨t.val + 1, Nat.succ_lt_succ h⟩ ({slotInl a} ∪ stepArm (k ⟨t.val, h⟩) a) := by
      rw [chainF_eq_succ (k := k) (t := t) h, stepSet_singleton]
    have hB : chainF n k t {b} =
        chainF n k ⟨t.val + 1, Nat.succ_lt_succ h⟩ ({slotInl b} ∪ stepArm (k ⟨t.val, h⟩) b) := by
      rw [chainF_eq_succ (k := k) (t := t) h, stepSet_singleton]
    rw [hA, hB, chainF_union, chainF_union]
    refine Finset.disjoint_union_left.mpr
      ⟨Finset.disjoint_union_right.mpr ⟨?_, ?_⟩, Finset.disjoint_union_right.mpr ⟨?_, ?_⟩⟩
    · exact ih (slotInl a) (slotInl b) (fun hcon => hab (slotInl_injective hcon))
    · by_cases hb : b = k ⟨t.val, h⟩
      · rw [stepArm_eq_singleton hb]
        exact ih (slotInl a) (slotInr false) (slotInl_ne_slotInr a false)
      · rw [stepArm_eq_empty hb, chainF_empty]
        exact Finset.disjoint_empty_right _
    · by_cases ha : a = k ⟨t.val, h⟩
      · rw [stepArm_eq_singleton ha]
        exact (ih (slotInl b) (slotInr false) (slotInl_ne_slotInr b false)).symm
      · rw [stepArm_eq_empty ha, chainF_empty]
        exact Finset.disjoint_empty_left _
    · by_cases ha : a = k ⟨t.val, h⟩
      · by_cases hb : b = k ⟨t.val, h⟩
        · exact absurd (ha.trans hb.symm) hab
        · rw [stepArm_eq_empty hb, chainF_empty]
          exact Finset.disjoint_empty_right _
      · rw [stepArm_eq_empty ha, chainF_empty]
        exact Finset.disjoint_empty_left _
  · intro a b hab
    rw [chainF_eq_top, chainF_eq_top]
    exact Finset.disjoint_singleton_left.mpr (by simpa [Finset.mem_singleton] using hab)

/-- **The step adds exactly one slot when the split slot is in the set** — the new leg
`Sum.inr false` — and nothing otherwise. -/
theorem card_stepSet {m : ℕ} (j : Idx m) (A : Finset (Idx m)) :
    (stepSet j A).card = A.card + if j ∈ A then 1 else 0 := by
  rw [stepSet_eq_erase_image]
  by_cases h : j ∈ A
  · rw [ite_eq_left h, ite_eq_left h]
    have hdis : Disjoint ((A.erase j).image slotInl)
        ({slotInl j, slotInr false} : Finset (Idx (m + 1))) := by
      rw [Finset.disjoint_left]
      intro x hx hx2
      simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton] at hx hx2
      obtain ⟨i, hi, rfl⟩ := hx
      rcases hx2 with h2 | h2
      · have hij : i = j := slotInl_injective h2
        rw [hij] at hi
        exact (Finset.mem_erase.mp hi).1 rfl
      · exact slotInl_ne_slotInr i false h2
    rw [Finset.card_union_of_disjoint hdis,
      Finset.card_image_of_injective _ slotInl_injective,
      Finset.card_erase_of_mem h,
      Finset.card_pair (slotInl_ne_slotInr j false)]
    have hpos : 0 < A.card := Finset.card_pos.mpr ⟨j, h⟩
    omega
  · rw [ite_eq_right h, ite_eq_right h, Finset.card_image_of_injective _ slotInl_injective,
      Nat.add_zero]

/-! ## 3. `chainM` is the cardinality of the chain set -/

theorem chainM_eq_card_chainF (n : ℕ) (k : (u : Fin n) → Idx u) (t : Fin (n + 1))
    (i : Idx t.val) : chainM n k t.val i = (chainF n k t {i}).card := by
  refine chainF_ind n k (fun t => ∀ i : Idx t.val,
    chainM n k t.val i = (chainF n k t {i}).card) ?_ ?_ t i
  · intro t h ih i
    have hcm := I417SplitClosedForm.chainM_eq_succ n k h i
    have hF : chainF n k t {i} =
        chainF n k ⟨t.val + 1, Nat.succ_lt_succ h⟩ ({slotInl i} ∪ stepArm (k ⟨t.val, h⟩) i) := by
      rw [chainF_eq_succ (k := k) (t := t) h, stepSet_singleton]
    have hdis : Disjoint (chainF n k ⟨t.val + 1, Nat.succ_lt_succ h⟩ {slotInl i})
        (chainF n k ⟨t.val + 1, Nat.succ_lt_succ h⟩ {slotInr false}) :=
      chainF_singleton_disjoint n k _ (slotInl_ne_slotInr i false)
    by_cases hi : i = k ⟨t.val, h⟩
    · rw [hF, stepArm_eq_singleton hi, chainF_union, Finset.card_union_of_disjoint hdis,
        hcm, ite_eq_left hi]
      rw [ih (Sum.inl i), ih (Sum.inr false)]
      rfl
    · rw [hF, stepArm_eq_empty hi, Finset.union_empty, hcm, ite_eq_right hi]
      rw [ih (Sum.inl i)]
      rfl
  · intro i
    rw [chainF_eq_top, Finset.card_singleton]
    exact I417SplitClosedForm.chainM_eq_top (lt_irrefl n) k i

/-! ## 4. The pin--mark path is the chain of the first slot -/

theorem pathLegsK_eq_stepSet {n : ℕ} (k : (u : Fin (n + 1)) → Idx u) :
    pathLegsK (n + 1) k =
      stepSet (k (Fin.last n)) (pathLegsK n (fun u : Fin n => k u.castSucc)) := by
  rw [pathLegsK, stepSet_eq_erase_image]
  rfl

/-- **One more round on the chain set.**  The chain set of stage `t` propagated through the rounds
`t, …, n` of the branch `k` is the chain set of stage `t` propagated through the rounds `t, …, n-1`
and then through the last round.  This is the bridge between the forward recursion `chainF` and the
backward recursion `pathLegsK`. -/
theorem chainF_succ_last {n : ℕ} (k : (u : Fin (n + 1)) → Idx u) (t : Fin (n + 1))
    (S : Finset (Idx t.val)) :
    chainF (n + 1) k ⟨t.val, Nat.lt_succ_of_lt t.isLt⟩ S =
      stepSet (k (Fin.last n)) (chainF n (fun u : Fin n => k u.castSucc) t S) := by
  suffices key : ∀ d : ℕ, ∀ t : Fin (n + 1), n - t.val = d → ∀ S : Finset (Idx t.val),
      chainF (n + 1) k ⟨t.val, Nat.lt_succ_of_lt t.isLt⟩ S =
        stepSet (k (Fin.last n)) (chainF n (fun u : Fin n => k u.castSucc) t S) from
    key (n - t.val) t rfl S
  intro d
  induction d with
  | zero =>
    intro t ht S
    have htn : t.val = n := by have := t.isLt; omega
    revert S
    rw [show t = (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) from Fin.ext htn]
    intro S
    rw [chainF_eq_succ (n := n + 1) (k := k) (t := (⟨n, by omega⟩ : Fin (n + 1 + 1)))
      (h := (by omega : n < n + 1))]
    rw [chainF_eq_top, chainF_eq_top]
    rfl
  | succ d ih =>
    intro t ht S
    have hlt : t.val < n := by have := t.isLt; omega
    have hlt' : t.val < n + 1 := by omega
    rw [chainF_eq_succ (n := n + 1) (k := k)
      (t := (⟨t.val, by omega⟩ : Fin (n + 1 + 1))) (h := hlt')]
    have hd : n - (t.val + 1) = d := by omega
    rw [ih (⟨t.val + 1, by omega⟩ : Fin (n + 1)) hd]
    rw [chainF_eq_succ (n := n) (k := fun u : Fin n => k u.castSucc) (t := t) hlt]
    rfl

theorem chainF_zero_eq_pathLegsK (n : ℕ) (k : (u : Fin n) → Idx u) :
    chainF n k ⟨0, Nat.succ_pos n⟩ {idxZero} = pathLegsK n k := by
  induction n with
  | zero =>
    rw [chainF_eq_top]
    rfl
  | succ n ih =>
    refine (chainF_succ_last (n := n) (k := k) (t := (⟨0, Nat.succ_pos n⟩ : Fin (n + 1)))
      (S := {idxZero})).trans ?_
    rw [ih, pathLegsK_eq_stepSet]

theorem markDepthK_eq_card_pathLegsK (n : ℕ) (k : (u : Fin n) → Idx u) :
    markDepthK n k = (pathLegsK n k).card := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hdepth : markDepthK (n + 1) k = markDepthK n (fun t : Fin n => k t.castSucc) +
        (if k (Fin.last n) ∈ pathLegsK n (fun t : Fin n => k t.castSucc) then 1 else 0) := by
      have h := I417FreshDepth.markDepthK_succ (f := fun t : Fin n => k t.castSucc)
        (i := k (Fin.last n))
      rw [I417FreshDepth.snoc_self k] at h
      exact h
    have hpath : (pathLegsK (n + 1) k).card =
        (pathLegsK n (fun t : Fin n => k t.castSucc)).card +
          (if k (Fin.last n) ∈ pathLegsK n (fun t : Fin n => k t.castSucc) then 1 else 0) := by
      rw [pathLegsK_eq_stepSet, card_stepSet]
    rw [hdepth, hpath, ih]

theorem markDepthK_eq_chainM (n : ℕ) (k : (u : Fin n) → Idx u) :
    chainM n k 0 idxZero = markDepthK n k := by
  rw [chainM_eq_card_chainF n k ⟨0, Nat.succ_pos n⟩ idxZero,
    chainF_zero_eq_pathLegsK, markDepthK_eq_card_pathLegsK]

end PercLib.CriticalLRP.I417HistFibre
