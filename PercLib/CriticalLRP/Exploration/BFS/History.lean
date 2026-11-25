/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# Determinism of the BFS state on its revealed history.

Accepted from independent submission `smwpalb9h` direction D2.
No generation-moment induction or cluster-moment finiteness is asserted here.
-/
module

/-
Private swarm module (member m2, swarm smwpalb9h), direction 2.

Adapted revelation: the state after `k` steps is a function of the configuration
restricted to the edges actually queried before step `k` (`seen`), and those
queried edges are pairwise disjoint across steps and disjoint from the next
step's queried set `E(A k, U k)`.  This is the deterministic input for the
conditional-product argument of direction 1.
-/
public import PercLib.CriticalLRP.Exploration.BFS.Basic

set_option autoImplicit false


@[expose] public section

noncomputable section

open MeasureTheory Set PercLib.Percolation.Bond
open scoped ENNReal BigOperators

namespace PercLib.CriticalLRP.Exploration.BFS

variable {V : Type*}

/-- The new generation only depends on the configuration through the edges of
`A × U`. -/
theorem newGen_congr {ω ω' : Config V} {A U : Set V}
    (h : ∀ x ∈ A, ∀ y ∈ U, (s(x, y) ∈ ω ↔ s(x, y) ∈ ω')) :
    newGen ω A U = newGen ω' A U := by
  ext y
  constructor
  · rintro ⟨hyU, x, hxA, hxy⟩
    exact ⟨hyU, x, hxA, (h x hxA y hyU).mp hxy⟩
  · rintro ⟨hyU, x, hxA, hxy⟩
    exact ⟨hyU, x, hxA, (h x hxA y hyU).mpr hxy⟩

theorem step_congr {ω ω' : Config V} {st : State V}
    (h : ∀ x ∈ st.A, ∀ y ∈ st.U, (s(x, y) ∈ ω ↔ s(x, y) ∈ ω')) :
    step ω st = step ω' st := by
  have hgen : newGen ω st.A st.U = newGen ω' st.A st.U := newGen_congr h
  simp only [step]
  rw [hgen]

/-- **Adapted revelation.**  If two configurations agree on all edges queried
before step `k`, then the exploration states at step `k` agree.  In particular
the state at step `k` is determined by the revealed history, although the
queried edge set may be infinite (no degree bound). -/
theorem state_eq_of_eqOn_seen (ω ω' : Config V) (o : V) (k : ℕ)
    (h : ∀ e, e ∈ seen ω o k → (e ∈ ω ↔ e ∈ ω')) :
    state ω o k = state ω' o k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hk : ∀ e, e ∈ seen ω o k → (e ∈ ω ↔ e ∈ ω') :=
        fun e he => h e (seen_mono ω o (Nat.le_succ k) he)
      have hstate : state ω o k = state ω' o k := ih hk
      have hstep : step ω (state ω o k) = step ω' (state ω o k) := by
        apply step_congr
        intro x hx y hy
        apply h
        rw [seen]
        exact Set.mem_iUnion.mpr ⟨⟨k, Nat.lt_succ_self k⟩, ⟨x, hx, y, hy, rfl⟩⟩
      rw [show state ω o (k + 1) = step ω (state ω o k) from rfl,
        show state ω' o (k + 1) = step ω' (state ω' o k) from rfl, ← hstate]
      exact hstep

/-- The same statement with the outline's revealed set `R k` instead of the
actually queried set: agreement on all edges incident to `P k` suffices. -/
theorem state_eq_of_eqOn_revealed (ω ω' : Config V) (o : V) (k : ℕ)
    (h : ∀ e, e ∈ revealed ω o k → (e ∈ ω ↔ e ∈ ω')) :
    state ω o k = state ω' o k :=
  state_eq_of_eqOn_seen ω ω' o k fun e he => h e (seen_subset_revealed ω o k he)

theorem A_eq_of_eqOn_seen (ω ω' : Config V) (o : V) (k : ℕ)
    (h : ∀ e, e ∈ seen ω o k → (e ∈ ω ↔ e ∈ ω')) :
    A ω o k = A ω' o k :=
  congrArg State.A (state_eq_of_eqOn_seen ω ω' o k h)

theorem P_eq_of_eqOn_seen (ω ω' : Config V) (o : V) (k : ℕ)
    (h : ∀ e, e ∈ seen ω o k → (e ∈ ω ↔ e ∈ ω')) :
    P ω o k = P ω' o k :=
  congrArg State.P (state_eq_of_eqOn_seen ω ω' o k h)

theorem U_eq_of_eqOn_seen (ω ω' : Config V) (o : V) (k : ℕ)
    (h : ∀ e, e ∈ seen ω o k → (e ∈ ω ↔ e ∈ ω')) :
    U ω o k = U ω' o k :=
  congrArg State.U (state_eq_of_eqOn_seen ω ω' o k h)

/-! ### Queried edge sets at different steps are disjoint -/

theorem disjoint_queried {ω : Config V} {o : V} {i k : ℕ} (h : i < k) :
    Disjoint (queried ω o i) (queried ω o k) := by
  rw [Set.disjoint_left]
  rintro e ⟨x, hxA, y, hyU, rfl⟩ ⟨x', hx'A, y', hy'U, heq⟩
  rcases Sym2.eq_iff.mp heq with ⟨hxx', -⟩ | ⟨hxy', hyx'⟩
  · exact (Set.disjoint_left.mp (pairwiseDisjoint_A ω o (Nat.ne_of_lt h))
      hxA) (hxx' ▸ hx'A)
  · have hxP : x ∈ P ω o k := A_subset_P_of_lt h hxA
    have hxU : x ∈ U ω o k := hxy' ▸ hy'U
    exact (not_mem_U_of_mem_P hxP) hxU

theorem disjoint_seen_queried (ω : Config V) (o : V) (k : ℕ) :
    Disjoint (seen ω o k) (queried ω o k) := by
  rw [Set.disjoint_left]
  intro e he hq
  rw [seen, Set.mem_iUnion] at he
  obtain ⟨j, hje⟩ := he
  exact (Set.disjoint_left.mp (disjoint_queried j.2) hje) hq

/-- The edges queried at step `k` are exactly the edges incident to the frontier
that were not revealed before step `k`. -/
theorem queried_subset_compl_seen (ω : Config V) (o : V) (k : ℕ) :
    queried ω o k ⊆ (seen ω o k)ᶜ := by
  intro e he hse
  exact (Set.disjoint_left.mp (disjoint_seen_queried ω o k) hse) he

end PercLib.CriticalLRP.Exploration.BFS
