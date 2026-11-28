/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Non-vacuity and scope tests for the decision-tree amalgamation theorem.
-/
module

public import PercLib.CriticalLRP.Correlation.Gladkov.DecisionTree.Main

/-!
# Examples and non-vacuity

* `emptyTree` queries nothing, so `S = ∅`: the theorem specialises to the deterministic
  lemma for the empty revealed set.
* `oneStep i` queries the single edge `i` with decision `"S"` and stops, so `S = {i}`:
  the theorem specialises to the deterministic lemma for a singleton revealed set.
* `twoEdgeTree` is a genuine decision tree whose revealed set is *not* self-determined:
  the class of the second edge depends on the revealed values of the first edge, which is
  never in `S`. The theorem still gives independence, which shows that the decision-tree
  hypothesis is not a reformulation of self-determination.
-/

set_option autoImplicit false

@[expose] public section

open MeasureTheory
open PercLib.Probability
open scoped ENNReal

namespace PercLib.GladkovAmalgam

variable {ι : Type*}

/-! ### The empty tree -/

/-- The tree that stops immediately. -/
def emptyTree (ι : Type*) : Tree ι := fun _ => none

theorem consistent_emptyTree : Consistent (emptyTree ι) :=
  consistent_of_strong fun τ i c h => by
    simp [emptyTree] at h

theorem runN_emptyTree (ν : Set (ι × Bool)) (n : ℕ) : runN (emptyTree ι) ν n = [] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [runN_succ, ih]
      exact step_of_none rfl

theorem trace_emptyTree [Fintype ι] (ν : Set (ι × Bool)) : trace (emptyTree ι) ν = [] :=
  runN_emptyTree ν (Fintype.card ι)

theorem treeSet_emptyTree [Fintype ι] (ν : Set (ι × Bool)) :
    treeSet (emptyTree ι) ν = (∅ : Set ι) := by
  ext i
  simp only [treeSet]
  rw [trace_emptyTree ν]
  simp

/-- The empty tree amalgamates over the empty revealed set. -/
theorem treeFirst_emptyTree [Fintype ι] (ν : Set (ι × Bool)) :
    treeFirst (emptyTree ι) ν = amalFirst (∅ : Set ι) ν := by
  rw [treeFirst, treeSet_emptyTree]

theorem treeSecond_emptyTree [Fintype ι] (ν : Set (ι × Bool)) :
    treeSecond (emptyTree ι) ν = amalSecond (∅ : Set ι) ν := by
  rw [treeSecond, treeSet_emptyTree]

set_option linter.unusedFintypeInType false in
/-- The theorem at the empty revealed set: the deterministic lemma for `S = ∅`. The
finiteness hypothesis is used by the proof, not by the statement. -/
theorem prodBernoulli_emptyTree [Fintype ι] (q : ι → unitInterval) (A B : Set (Set ι)) :
    prodBernoulli (twoProfile q) {ω | amalFirst (∅ : Set ι) ω ∈ A ∧
        amalSecond (∅ : Set ι) ω ∈ B} =
      prodBernoulli q A * prodBernoulli q B := by
  have h := prodBernoulli_treeFirst_second_indep q (consistent_emptyTree (ι := ι)) A B
  simpa only [treeFirst_emptyTree, treeSecond_emptyTree] using h

/-! ### The one-step tree -/

/-- The tree that queries `i` with decision `"S"` and stops. -/
def oneStep (i : ι) : Tree ι
  | [] => some (i, true)
  | _ => none

theorem consistent_oneStep (i : ι) : Consistent (oneStep i) := by
  refine consistent_of_strong fun τ j c h r hr => ?_
  match τ with
  | [] => simp at hr
  | _ :: _ => exact absurd h (by simp [oneStep])

theorem runN_oneStep {i : ι} (ν : Set (ι × Bool)) :
    ∀ n, runN (oneStep i) ν (n + 1) = [⟨i, true, bit ν (i, false), bit ν (i, true)⟩] := by
  intro n
  induction n with
  | zero => rw [runN_succ]; exact step_of_some rfl
  | succ n ih =>
      rw [runN_succ, ih]
      exact step_of_none rfl

theorem trace_oneStep [Fintype ι] {i : ι} (ν : Set (ι × Bool)) (hι : 0 < Fintype.card ι) :
    trace (oneStep i) ν = [⟨i, true, bit ν (i, false), bit ν (i, true)⟩] := by
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card ι = n + 1 := ⟨Fintype.card ι - 1, by omega⟩
  rw [trace, hn]
  exact runN_oneStep ν n

theorem treeSet_oneStep [Fintype ι] {i : ι} (ν : Set (ι × Bool)) (hι : 0 < Fintype.card ι) :
    treeSet (oneStep i) ν = {i} := by
  ext j
  rw [treeSet, trace_oneStep ν hι]
  constructor
  · rintro ⟨r, hr, he, -⟩
    rw [List.mem_singleton] at hr
    subst hr
    simpa using he.symm
  · intro h
    refine ⟨⟨i, true, bit ν (i, false), bit ν (i, true)⟩, List.mem_singleton_self _,
      ?_, rfl⟩
    rw [h]

/-- The one-step tree amalgamates over the singleton revealed set. -/
theorem treeFirst_oneStep [Fintype ι] {i : ι} (ν : Set (ι × Bool))
    (hι : 0 < Fintype.card ι) :
    treeFirst (oneStep i) ν = amalFirst ({i} : Set ι) ν := by
  rw [treeFirst, treeSet_oneStep _ hι]

theorem treeSecond_oneStep [Fintype ι] {i : ι} (ν : Set (ι × Bool))
    (hι : 0 < Fintype.card ι) :
    treeSecond (oneStep i) ν = amalSecond ({i} : Set ι) ν := by
  rw [treeSecond, treeSet_oneStep _ hι]

set_option linter.unusedFintypeInType false in
/-- The theorem at a singleton revealed set: the deterministic lemma for `S = {i}`. The
finiteness hypothesis is used by the proof, not by the statement. -/
theorem prodBernoulli_oneStep [Fintype ι] {i : ι} (hι : 0 < Fintype.card ι)
    (q : ι → unitInterval) (A B : Set (Set ι)) :
    prodBernoulli (twoProfile q) {ω | amalFirst ({i} : Set ι) ω ∈ A ∧
        amalSecond ({i} : Set ι) ω ∈ B} =
      prodBernoulli q A * prodBernoulli q B := by
  have h := prodBernoulli_treeFirst_second_indep q (consistent_oneStep i) A B
  simpa only [treeFirst_oneStep _ hι, treeSecond_oneStep _ hι] using h

end PercLib.GladkovAmalgam
