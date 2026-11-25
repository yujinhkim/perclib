/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Measurability of BFS states, generations and queried coordinates.

Accepted from independent submission `smwpalb9h` direction D2.
No generation-moment induction or cluster-moment finiteness is asserted here.
-/
module

/-
Private swarm module (member m2, swarm smwpalb9h), direction 2.

Measurability of the exploration on the actual product law.  The only
hypothesis is `[Countable V]`, used exactly for the existential over the
frontier (`∃ x ∈ A k, s(x,y) ∈ ω`) and for the set-equality events.
-/
public import PercLib.CriticalLRP.Exploration.BFS.History

set_option autoImplicit false


@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Percolation.Bond
open scoped ENNReal BigOperators

namespace PercLib.CriticalLRP.Exploration.BFS

variable {V : Type*}

/-- Membership of a fixed vertex in the three state components is measurable,
simultaneously by induction on the step. -/
theorem measurableSet_mem_state [Countable V] (o : V) (k : ℕ) (y : V) :
    MeasurableSet {ω : Config V | y ∈ A ω o k} ∧
      MeasurableSet {ω : Config V | y ∈ P ω o k} ∧
      MeasurableSet {ω : Config V | y ∈ U ω o k} := by
  induction k generalizing y with
  | zero =>
      have hA : MeasurableSet {ω : Config V | y ∈ A ω o 0} := by
        by_cases hy : y = o
        · simp [A_zero, hy]
        · simp [A_zero, hy]
      have hP : MeasurableSet {ω : Config V | y ∈ P ω o 0} := by
        simp [P_zero]
      have hU : MeasurableSet {ω : Config V | y ∈ U ω o 0} := by
        by_cases hy : y = o
        · simp [U_zero, hy]
        · simp [U_zero, hy]
      exact ⟨hA, hP, hU⟩
  | succ k ih =>
      have hA : MeasurableSet {ω : Config V | y ∈ A ω o (k + 1)} := by
        have hset : {ω : Config V | y ∈ A ω o (k + 1)} =
            {ω : Config V | y ∈ U ω o k} ∩
              ⋃ x : V, ({ω : Config V | x ∈ A ω o k} ∩ {ω : Config V | s(x, y) ∈ ω}) := by
          ext ω
          simp only [A_succ, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iUnion]
        rw [hset]
        exact (ih y).2.2.inter
          (MeasurableSet.iUnion fun x => (ih x).1.inter (measurableSet_mem (s(x, y))))
      have hP : MeasurableSet {ω : Config V | y ∈ P ω o (k + 1)} := by
        have hset : {ω : Config V | y ∈ P ω o (k + 1)} =
            {ω : Config V | y ∈ P ω o k} ∪ {ω : Config V | y ∈ A ω o k} := by
          ext ω
          simp only [P_succ, Set.mem_ofPred_eq, Set.mem_union]
        rw [hset]
        exact (ih y).2.1.union (ih y).1
      have hU : MeasurableSet {ω : Config V | y ∈ U ω o (k + 1)} := by
        have hset : {ω : Config V | y ∈ U ω o (k + 1)} =
            {ω : Config V | y ∈ U ω o k} \ {ω : Config V | y ∈ A ω o (k + 1)} := by
          ext ω
          simp only [U_succ, Set.mem_ofPred_eq, Set.mem_sdiff]
        rw [hset]
        exact (ih y).2.2.diff hA
      exact ⟨hA, hP, hU⟩

theorem measurableSet_mem_A [Countable V] (o : V) (k : ℕ) (y : V) :
    MeasurableSet {ω : Config V | y ∈ A ω o k} :=
  (measurableSet_mem_state o k y).1

theorem measurableSet_mem_P [Countable V] (o : V) (k : ℕ) (y : V) :
    MeasurableSet {ω : Config V | y ∈ P ω o k} :=
  (measurableSet_mem_state o k y).2.1

theorem measurableSet_mem_U [Countable V] (o : V) (k : ℕ) (y : V) :
    MeasurableSet {ω : Config V | y ∈ U ω o k} :=
  (measurableSet_mem_state o k y).2.2

/-- The event that the frontier at step `k` is a fixed set is measurable. -/
theorem measurableSet_A_eq [Countable V] (o : V) (k : ℕ) (s : Set V) :
    MeasurableSet {ω : Config V | A ω o k = s} := by
  have h : {ω : Config V | A ω o k = s} =
      ⋂ y : V, {ω : Config V | (y ∈ A ω o k ↔ y ∈ s)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.ext_iff]
  rw [h]
  refine MeasurableSet.iInter fun y => ?_
  by_cases hy : y ∈ s
  · have : {ω : Config V | (y ∈ A ω o k ↔ y ∈ s)} = {ω : Config V | y ∈ A ω o k} := by
      ext ω; simp [hy]
    rw [this]
    exact measurableSet_mem_A o k y
  · have : {ω : Config V | (y ∈ A ω o k ↔ y ∈ s)} = {ω : Config V | y ∈ A ω o k}ᶜ := by
      ext ω; simp [hy]
    rw [this]
    exact (measurableSet_mem_A o k y).compl

theorem measurableSet_P_eq [Countable V] (o : V) (k : ℕ) (s : Set V) :
    MeasurableSet {ω : Config V | P ω o k = s} := by
  have h : {ω : Config V | P ω o k = s} =
      ⋂ y : V, {ω : Config V | (y ∈ P ω o k ↔ y ∈ s)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.ext_iff]
  rw [h]
  refine MeasurableSet.iInter fun y => ?_
  by_cases hy : y ∈ s
  · have : {ω : Config V | (y ∈ P ω o k ↔ y ∈ s)} = {ω : Config V | y ∈ P ω o k} := by
      ext ω; simp [hy]
    rw [this]
    exact measurableSet_mem_P o k y
  · have : {ω : Config V | (y ∈ P ω o k ↔ y ∈ s)} = {ω : Config V | y ∈ P ω o k}ᶜ := by
      ext ω; simp [hy]
    rw [this]
    exact (measurableSet_mem_P o k y).compl

theorem measurableSet_U_eq [Countable V] (o : V) (k : ℕ) (s : Set V) :
    MeasurableSet {ω : Config V | U ω o k = s} := by
  have h : {ω : Config V | U ω o k = s} =
      ⋂ y : V, {ω : Config V | (y ∈ U ω o k ↔ y ∈ s)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.ext_iff]
  rw [h]
  refine MeasurableSet.iInter fun y => ?_
  by_cases hy : y ∈ s
  · have : {ω : Config V | (y ∈ U ω o k ↔ y ∈ s)} = {ω : Config V | y ∈ U ω o k} := by
      ext ω; simp [hy]
    rw [this]
    exact measurableSet_mem_U o k y
  · have : {ω : Config V | (y ∈ U ω o k ↔ y ∈ s)} = {ω : Config V | y ∈ U ω o k}ᶜ := by
      ext ω; simp [hy]
    rw [this]
    exact (measurableSet_mem_U o k y).compl

/-- The event that the full state at step `k` is a fixed state is measurable. -/
theorem measurableSet_state_eq [Countable V] (o : V) (k : ℕ) (st : State V) :
    MeasurableSet {ω : Config V | state ω o k = st} := by
  have h : {ω : Config V | state ω o k = st} =
      {ω : Config V | A ω o k = st.A} ∩ {ω : Config V | P ω o k = st.P} ∩
        {ω : Config V | U ω o k = st.U} := by
    ext ω
    simp only [Set.mem_ofPred_eq, state_eq, Set.mem_inter_iff]
    constructor
    · rintro rfl
      exact ⟨⟨rfl, rfl⟩, rfl⟩
    · rintro ⟨⟨hA, hP⟩, hU⟩
      rw [hA, hP, hU]
  rw [h]
  exact ((measurableSet_A_eq o k st.A).inter (measurableSet_P_eq o k st.P)).inter
    (measurableSet_U_eq o k st.U)

/-- The event that a fixed edge is queried at step `k` is measurable. -/
theorem measurableSet_mem_queried [Countable V] (o : V) (k : ℕ) (e : Sym2 V) :
    MeasurableSet {ω : Config V | e ∈ queried ω o k} := by
  have h : {ω : Config V | e ∈ queried ω o k} =
      ⋃ x : V, ⋃ y : V, ({ω : Config V | x ∈ A ω o k} ∩
        {ω : Config V | y ∈ U ω o k} ∩ {ω : Config V | e = s(x, y)}) := by
    ext ω
    simp only [queried, edgeSet, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩
      exact ⟨x, y, ⟨hx, hy⟩, rfl⟩
    · rintro ⟨x, y, ⟨hx, hy⟩, rfl⟩
      exact ⟨x, hx, y, hy, rfl⟩
  rw [h]
  exact MeasurableSet.iUnion fun x => MeasurableSet.iUnion fun y =>
    ((measurableSet_mem_A o k x).inter (measurableSet_mem_U o k y)).inter
      (MeasurableSet.const (e = s(x, y)))

end PercLib.CriticalLRP.Exploration.BFS
