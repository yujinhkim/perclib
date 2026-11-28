/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

An adaptive two-edge decision tree whose revealed set is not self-determined.
-/
module

public import PercLib.CriticalLRP.Correlation.Gladkov.DecisionTree.Main

/-!
# A decision tree that decides after revealing

On the two edges `false`, `true` the tree

1. queries the edge `false` with decision `"S̄"` (so that edge is never in `S`),
2. if the first copy of that edge is open, queries the edge `true` with decision `"S"`,
   otherwise stops.

The revealed set is therefore `{true}` when the first copy of `false` is open and `∅`
otherwise. Its value at the edge `false` decides the set, while `false ∉ S`: the set is
not determined by the configuration restricted to itself. Nevertheless
`prodBernoulli_treeFirst_second_indep` applies, because the class of every edge is fixed
before the values of that edge are revealed.
-/

set_option autoImplicit false

@[expose] public section

open MeasureTheory
open PercLib.Probability
open scoped ENNReal

namespace PercLib.GladkovAmalgam

/-- The adaptive two-edge tree. -/
def twoEdgeTree : Tree Bool
  | [] => some (false, false)
  | [r] => if r.edge = false ∧ r.v1 then some (true, true) else none
  | _ => none

theorem consistent_twoEdgeTree : Consistent twoEdgeTree := by
  refine consistent_of_strong fun τ i c h r hr => ?_
  match τ with
  | [] => simp at hr
  | [s] =>
      by_cases hcond : s.edge = false ∧ s.v1
      · have hσ : twoEdgeTree [s] = some (true, true) := by
          simp [twoEdgeTree, hcond.1, hcond.2]
        rw [hσ] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨h1, -⟩ := h
        rw [List.mem_singleton] at hr
        subst hr
        rw [← h1, hcond.1]
        simp
      · have hσ : twoEdgeTree [s] = none := by
          simp [twoEdgeTree, hcond]
        rw [hσ] at h
        exact absurd h (by simp)
  | a :: b :: rest =>
      have hσ : twoEdgeTree (a :: b :: rest) = none := by simp [twoEdgeTree]
      rw [hσ] at h
      exact absurd h (by simp)

/-- The configuration in which the first copy is open at both edges. -/
def adaptiveOmega : Set (Bool × Bool) := {(false, false), (true, false)}

/-- The configuration in which only the first copy of `true` is open. -/
def adaptiveOmega' : Set (Bool × Bool) := {(true, false)}

/-- The transcript of the run on `adaptiveOmega`: both edges are queried, the second with
decision `"S"`. -/
theorem trace_twoEdgeTree_adaptiveOmega :
    trace twoEdgeTree adaptiveOmega =
      [⟨false, false, true, false⟩, ⟨true, true, true, false⟩] := by
  simp [trace, Fintype.card_bool, runN, step, twoEdgeTree, adaptiveOmega, bit]

/-- The transcript of the run on `adaptiveOmega'`: the tree stops after the first edge. -/
theorem trace_twoEdgeTree_adaptiveOmega' :
    trace twoEdgeTree adaptiveOmega' = [⟨false, false, false, false⟩] := by
  simp [trace, Fintype.card_bool, runN, step, twoEdgeTree, adaptiveOmega', bit]

theorem treeSet_twoEdgeTree_adaptiveOmega :
    treeSet twoEdgeTree adaptiveOmega = {true} := by
  ext i
  rw [treeSet, trace_twoEdgeTree_adaptiveOmega]
  cases i <;> simp

theorem treeSet_twoEdgeTree_adaptiveOmega' :
    treeSet twoEdgeTree adaptiveOmega' = (∅ : Set Bool) := by
  ext i
  rw [treeSet, trace_twoEdgeTree_adaptiveOmega']
  cases i <;> simp

/-- **The revealed set is not self-determined.** `adaptiveOmega` and `adaptiveOmega'` agree
on the coordinates of the revealed set `{true}`, yet the revealed sets differ: the value at
the edge `false`, which is itself never in the set, decides it. -/
theorem not_selfDetermined_twoEdgeTree :
    ∃ ω ω' : Set (Bool × Bool),
      ω ∩ {x : Bool × Bool | x.1 ∈ treeSet twoEdgeTree ω} =
          ω' ∩ {x : Bool × Bool | x.1 ∈ treeSet twoEdgeTree ω} ∧
        treeSet twoEdgeTree ω ≠ treeSet twoEdgeTree ω' := by
  refine ⟨adaptiveOmega, adaptiveOmega', ?_, ?_⟩
  · rw [treeSet_twoEdgeTree_adaptiveOmega]
    ext x
    rcases x with ⟨a, b⟩
    cases a <;> cases b <;> simp [adaptiveOmega, adaptiveOmega']
  · rw [treeSet_twoEdgeTree_adaptiveOmega, treeSet_twoEdgeTree_adaptiveOmega']
    simp

/-! ### The countable-family form does not cover this tree -/

/-- The two-element family of possible revealed sets of `twoEdgeTree`. -/
def adaptiveSfam : ℕ → Set Bool := fun n => if n = 1 then {true} else ∅

/-- The selection map: index `1` reveals `{true}`, index `0` reveals `∅`. -/
noncomputable def adaptiveIdx (ω : Set (Bool × Bool)) : ℕ :=
  if treeSet twoEdgeTree ω = {true} then 1 else 0

theorem adaptiveIdx_omega : adaptiveIdx adaptiveOmega = 1 := by
  simp [adaptiveIdx, treeSet_twoEdgeTree_adaptiveOmega]

theorem adaptiveIdx_omega' : adaptiveIdx adaptiveOmega' = 0 := by
  simp [adaptiveIdx, treeSet_twoEdgeTree_adaptiveOmega']

theorem adaptiveSfam_omega : adaptiveSfam (adaptiveIdx adaptiveOmega) = {true} := by
  rw [adaptiveIdx_omega]
  simp [adaptiveSfam]

theorem adaptiveSfam_omega' : adaptiveSfam (adaptiveIdx adaptiveOmega') = (∅ : Set Bool) := by
  rw [adaptiveIdx_omega']
  simp [adaptiveSfam]

/-- **The revealed set of `twoEdgeTree` is a measurable selection from the two-element
family `{∅, {true}}` that is not self-determined.** Hence the countable-family theorem
`prodBernoulli_random_amalgam_indep` does not apply to it, while the decision-tree theorem
`prodBernoulli_treeFirst_second_indep` does. -/
theorem not_selfDetermined_adaptive : ¬ SelfDetermined adaptiveSfam adaptiveIdx := by
  intro h
  have hagree : adaptiveOmega ∩
        {x : Bool × Bool | x.1 ∈ adaptiveSfam (adaptiveIdx adaptiveOmega)} =
      adaptiveOmega' ∩
        {x : Bool × Bool | x.1 ∈ adaptiveSfam (adaptiveIdx adaptiveOmega)} := by
    rw [adaptiveSfam_omega]
    ext x
    rcases x with ⟨a, b⟩
    cases a <;> cases b <;> simp [adaptiveOmega, adaptiveOmega']
  have hidx := h adaptiveOmega adaptiveOmega' hagree
  rw [adaptiveIdx_omega, adaptiveIdx_omega'] at hidx
  exact absurd hidx (by decide)

/-- The amalgamation theorem applies to the adaptive tree, so `C1 →_S C2` and
`C2 →_S C1` are independent and have the original law although `S` is not self-determined. -/
theorem prodBernoulli_twoEdgeTree (q : Bool → unitInterval) (A B : Set (Set Bool)) :
    prodBernoulli (twoProfile q) {ω | treeFirst twoEdgeTree ω ∈ A ∧
        treeSecond twoEdgeTree ω ∈ B} =
      prodBernoulli q A * prodBernoulli q B :=
  prodBernoulli_treeFirst_second_indep q consistent_twoEdgeTree A B

end PercLib.GladkovAmalgam
