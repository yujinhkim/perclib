/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Frontier-moment ingredients: row sums and revealed-block histories

Swarm `smwpbvro2`, member m2, direction d2.

Definitions and bookkeeping for the high-temperature generation-moment induction on
the committed BFS exploration (`PercLib.CriticalLRP.Exploration.BFS`):

* `RowSum p m`, the uniform real row-sum hypothesis (R_m);
* `hist o k ω = ω ∩ revealFin (finState ω o k)`, the revealed block at step `k`, and
  `IsHistFun o k G`, the statement that `G` is a function of that block.

Nothing here asserts a cluster bound; the moment induction lives in
`GenMomInduction.lean`.
-/
module

public import PercLib.CriticalLRP.Exploration.BFS.Limit
public import PercLib.CriticalLRP.Exploration.BFS.BFSProduct
public import PercLib.CriticalLRP.Exploration.BFS.Poisson.Scalar

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Percolation.Bond
open PercLib.Probability.AdaptedReveal
open scoped ENNReal BigOperators Topology

namespace PercLib.CriticalLRP.Exploration.BFS

variable {V : Type*} [Countable V]

/-! ### The uniform real row-sum hypothesis -/

/-- **(R_m): uniform real row sum.**  Every finite partial row sum of the edge
intensities is at most `m`.  For a nonnegative kernel this is the same as
`∑_y p(x,y) ≤ m`; the finite-partial-sum form avoids any junk value and is what the
row-sum charging of the queried set uses. -/
def RowSum (p : Sym2 V → unitInterval) (m : ℝ) : Prop :=
  ∀ x : V, ∀ t : Finset V, ∑ y ∈ t, ((p (s(x, y)) : ℝ)) ≤ m

/-! ### The revealed block and history functions -/

/-- The revealed block of coordinates at step `k`: the configuration, as a set, restricted
to `revealFin (finState ω o k)`. -/
def hist (o : V) (k : ℕ) (ω : Config V) : Set (Sym2 V) :=
  ω ∩ revealFin (finState ω o k)

theorem hist_def (o : V) (k : ℕ) (ω : Config V) :
    hist o k ω = ω ∩ revealFin (finState ω o k) := rfl

theorem hist_subset (o : V) (k : ℕ) (ω : Config V) : hist o k ω ⊆ ω :=
  Set.inter_subset_left

/-- **A history function at step `k`**: a measurable function of the revealed block
`hist o k`.  This is the class of test functions the generation induction is stated for. -/
def IsHistFun (o : V) (k : ℕ) (G : Config V → ℝ≥0∞) : Prop :=
  ∃ H : Set (Sym2 V) → ℝ≥0∞, Measurable H ∧ ∀ ω, G ω = H (hist o k ω)

theorem IsHistFun.congr {o : V} {k : ℕ} {G G' : Config V → ℝ≥0∞} (h : IsHistFun o k G)
    (hGG' : ∀ ω, G' ω = G ω) : IsHistFun o k G' := by
  obtain ⟨H, hH, hEq⟩ := h
  exact ⟨H, hH, fun ω => by rw [hGG', hEq ω]⟩

theorem IsHistFun.const (o : V) (k : ℕ) (c : ℝ≥0∞) : IsHistFun o k (fun _ => c) :=
  ⟨fun _ => c, measurable_const, fun _ => rfl⟩

/-! ### The revealed set is contained in the revealed block -/

theorem revealed_subset_revealFin (ω : Config V) (o : V) (k : ℕ) :
    revealed ω o k ⊆ revealFin (finState ω o k) := by
  classical
  intro e he
  obtain ⟨v, hv, hve⟩ := he
  unfold finState
  by_cases hfin : (P ω o k).Finite ∧ (A ω o k).Finite
  · rw [dite_eq_left hfin]
    refine ⟨v, ?_, hve⟩
    rw [Set.Finite.coe_toFinset]
    exact hv
  · rw [dite_eq_right hfin]
    exact Set.mem_univ e

/-- `revealFin` depends only on the processed set, hence is monotone in the step. -/
theorem revealFin_finState_subset_succ (ω : Config V) (o : V) (k : ℕ) :
    revealFin (finState ω o k) ⊆ revealFin (finState ω o (k + 1)) := by
  classical
  cases h2 : finState ω o (k + 1) with
  | none => exact Set.subset_univ _
  | some QT =>
    obtain ⟨Q', T'⟩ := QT
    obtain ⟨hQ', -⟩ := finState_eq_some_iff.mp h2
    have hfk : finState ω o k ≠ none := by
      intro h0
      unfold finState at h0
      by_cases hfin : (P ω o k).Finite ∧ (A ω o k).Finite
      · rw [dite_eq_left hfin] at h0
        exact absurd h0 (by simp)
      · have hPfin : (P ω o (k + 1)).Finite := hQ' ▸ Q'.finite_toSet
        have hPsub : P ω o k ⊆ P ω o (k + 1) := P_subset_succ ω o k
        have hAsub : A ω o k ⊆ P ω o (k + 1) := A_subset_P_succ ω o k
        exact hfin ⟨Set.Finite.subset hPfin hPsub, Set.Finite.subset hPfin hAsub⟩
    cases h1 : finState ω o k with
    | none => exact absurd h1 hfk
    | some QT' =>
      obtain ⟨Q, T⟩ := QT'
      obtain ⟨hQ, -⟩ := finState_eq_some_iff.mp h1
      have hsub : (Q : Set V) ⊆ (Q' : Set V) := by
        rw [hQ, hQ']
        exact P_subset_succ ω o k
      intro e he
      obtain ⟨v, hv, hve⟩ := he
      exact ⟨v, hsub hv, hve⟩

/-! ### Measurability of the compressed state and of the revealed block -/

theorem measurableSet_finState_mem (o : V) (k : ℕ) (S : Set (FinState V)) :
    MeasurableSet {ω : Config V | finState ω o k ∈ S} := by
  have h : {ω : Config V | finState ω o k ∈ S} =
      ⋃ σ ∈ S, {ω : Config V | finState ω o k = σ} := by
    ext ω
    simp
  rw [h]
  exact MeasurableSet.biUnion S.to_countable (fun σ _ => measurableSet_finState_eq o k σ)

/-- The revealed block is measurable. -/
theorem measurable_hist (o : V) (k : ℕ) : Measurable (hist o k) := by
  rw [measurable_set_iff]
  intro e
  apply measurableSet_setOfPred.mp
  have hset : {ω : Config V | e ∈ hist o k ω} =
      {ω : Config V | e ∈ ω} ∩
        {ω : Config V | finState ω o k ∈ {σ : FinState V | e ∈ revealFin σ}} := by
    ext ω
    simp [hist]
  rw [hset]
  exact (measurableSet_mem e).inter
    (measurableSet_finState_mem o k {σ : FinState V | e ∈ revealFin σ})

/-- Two configurations with the same processed set and frontier have the same compressed
state. -/
theorem finState_eq_of_P_eq {ω ω' : Config V} {o : V} {k : ℕ}
    (hP : P ω o k = P ω' o k) (hA : A ω o k = A ω' o k) :
    finState ω o k = finState ω' o k := by
  classical
  by_cases hfin : (P ω o k).Finite ∧ (A ω o k).Finite
  · have hfin' : (P ω' o k).Finite ∧ (A ω' o k).Finite := by rw [← hP, ← hA]; exact hfin
    have h1 : finState ω o k = some (hfin.1.toFinset, hfin.2.toFinset) := by
      unfold finState; exact dite_eq_left hfin
    have h2 : finState ω' o k = some (hfin'.1.toFinset, hfin'.2.toFinset) := by
      unfold finState; exact dite_eq_left hfin'
    rw [h1, h2]
    congr 2
    · ext v
      rw [Set.Finite.mem_toFinset, Set.Finite.mem_toFinset, hP]
    · ext v
      rw [Set.Finite.mem_toFinset, Set.Finite.mem_toFinset, hA]
  · have hfin' : ¬((P ω' o k).Finite ∧ (A ω' o k).Finite) := by rw [← hP, ← hA]; exact hfin
    have h1 : finState ω o k = none := by unfold finState; exact dite_eq_right hfin
    have h2 : finState ω' o k = none := by unfold finState; exact dite_eq_right hfin'
    rw [h1, h2]

/-- The state at step `k` is determined by `hist o k` (the block contains the state's own
revealed set). -/
theorem finState_hist_eq (o : V) (k : ℕ) (ω : Config V) :
    finState (hist o k ω) o k = finState ω o k := by
  have h : ∀ e ∈ revealed ω o k, (e ∈ ω ↔ e ∈ hist o k ω) := by
    intro e he
    exact ⟨fun h1 => ⟨h1, revealed_subset_revealFin ω o k he⟩, fun h1 => h1.1⟩
  have hstate := state_eq_of_eqOn_revealed ω (hist o k ω) o k h
  exact finState_eq_of_P_eq (congrArg State.P hstate).symm (congrArg State.A hstate).symm

/-! ### Revealed blocks increase with the step -/

theorem revealed_subset_revealFin_succ (o : V) (k : ℕ) (ω : Config V) :
    revealed ω o k ⊆ revealFin (finState ω o (k + 1)) :=
  (revealed_mono ω o (Nat.le_succ k)).trans (revealed_subset_revealFin ω o (k + 1))

/-- The comparison map on blocks: from a block at step `k+1` recover the block at `k`. -/
def histShift (o : V) (k : ℕ) (h : Set (Sym2 V)) : Set (Sym2 V) :=
  h ∩ revealFin (finState h o k)

/-- `hist o k` is a function of `hist o (k+1)`. -/
theorem hist_eq_of_succ (o : V) (k : ℕ) (ω : Config V) :
    hist o k ω = histShift o k (hist o (k + 1) ω) := by
  have h : ∀ e ∈ revealed ω o k, (e ∈ ω ↔ e ∈ hist o (k + 1) ω) := by
    intro e he
    exact ⟨fun h1 => ⟨h1, revealed_subset_revealFin_succ o k ω he⟩, fun h1 => h1.1⟩
  have hstate := state_eq_of_eqOn_revealed ω (hist o (k + 1) ω) o k h
  have hfin : finState (hist o (k + 1) ω) o k = finState ω o k :=
    finState_eq_of_P_eq (congrArg State.P hstate).symm (congrArg State.A hstate).symm
  have hmono : revealFin (finState ω o k) ⊆ revealFin (finState ω o (k + 1)) :=
    revealFin_finState_subset_succ ω o k
  have h1 : hist o (k + 1) ω = ω ∩ revealFin (finState ω o (k + 1)) := rfl
  show ω ∩ revealFin (finState ω o k) = histShift o k (hist o (k + 1) ω)
  rw [histShift, hfin, h1, Set.inter_assoc, Set.inter_eq_right.mpr hmono]

theorem measurable_histShift (o : V) (k : ℕ) : Measurable (histShift o k) := by
  rw [measurable_set_iff]
  intro e
  apply measurableSet_setOfPred.mp
  have hset : {h : Set (Sym2 V) | e ∈ histShift o k h} =
      {h : Set (Sym2 V) | e ∈ h} ∩
        {h : Set (Sym2 V) | finState h o k ∈ {σ : FinState V | e ∈ revealFin σ}} := by
    ext h
    simp [histShift]
  rw [hset]
  exact (measurableSet_mem e).inter
    (measurableSet_finState_mem o k {σ : FinState V | e ∈ revealFin σ})

/-- History functions at step `k` are history functions at step `k+1`. -/
theorem IsHistFun.succ {o : V} {k : ℕ} {G : Config V → ℝ≥0∞} (h : IsHistFun o k G) :
    IsHistFun o (k + 1) G := by
  obtain ⟨H, hH, hEq⟩ := h
  exact ⟨fun h' => H (histShift o k h'), hH.comp (measurable_histShift o k),
    fun ω => by rw [hEq ω, hist_eq_of_succ o k ω]⟩
