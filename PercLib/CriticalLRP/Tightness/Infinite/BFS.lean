/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# BFS parent map of an open cluster on an ARBITRARY vertex type

Reference: T. Hutchcroft, arXiv:2008.11197v2, Section 2.1, proof of Theorem 2.3.

The repository's `Tightness/BFSParent.lean` builds the shortest-path parent map of the open
cluster of `r` **only for `[Fintype V]`**, because it works on the finite subtype `Cl G ω r` of
the cluster and applies the finite tree-piece lemma `exists_tree_pieces` to that whole subtype.
For a countable vertex set the cluster is infinite, so that route is unavailable; the source's
sentence "the infinite cases follow by exhaustion over finite subgraphs" is one way around it.

This file redoes the *local* part of that construction with no finiteness assumption at all:
the balls `openBall`, the BFS distance `bdist`, the predecessor step `exists_parent_step` and a
globally defined parent map `par : V → V` with

* `par_open` : the parent edge of a non-root point of the cluster is an open edge of `G`,
* `par_bdist_succ` : the parent is exactly one step closer to `r`,
* `par_reaches` : every point of the cluster reaches `r` along iterated parents.

`par` is the identity off the cluster of `r` (and at `r` itself), so it is a self-map of `V`; the
rooted-forest property `IsRootedForest` is *not* claimed on `V` (it would force `V` to be a single
cluster), only on finite `par`-closed regions inside the cluster — see `TruncatedPieces.lean`.
-/
module

public import Mathlib
public import PercLib.CriticalLRP.Tightness.MaxClusterPower

set_option autoImplicit true

@[expose] public section

namespace Hutchcroft
namespace Countable

open PercLib.CriticalLRP.Percolation

set_option linter.unusedSectionVars false

attribute [local instance] Classical.propDecidable

variable {V : Type*} [DecidableEq V] {E : Type*}

/-! ### Balls of the open graph -/

section Ball

variable (G : BondGraph V E) (ω : Set E) (r : V)

/-- `openBall G ω r n`: the vertices reachable from `r` by a path of at most `n` *open* edges. -/
def openBall : ℕ → Set V
  | 0 => {r}
  | n + 1 => openBall n ∪ {y | ∃ x ∈ openBall n, ∃ e ∈ ω, G e = s(x, y)}

@[simp] theorem mem_openBall_zero {y : V} : y ∈ openBall G ω r 0 ↔ y = r := Iff.rfl

theorem openBall_subset_succ (n : ℕ) : openBall G ω r n ⊆ openBall G ω r (n + 1) :=
  Set.subset_union_left

theorem mem_openBall_succ_of_edge {n : ℕ} {x y : V} (hx : x ∈ openBall G ω r n)
    {e : E} (he : e ∈ ω) (hxy : G e = s(x, y)) : y ∈ openBall G ω r (n + 1) :=
  Set.mem_union_right _ ⟨x, hx, e, he, hxy⟩

theorem mem_openBall_succ {n : ℕ} {y : V} (h : y ∈ openBall G ω r (n + 1)) :
    y ∈ openBall G ω r n ∨ ∃ x ∈ openBall G ω r n, ∃ e ∈ ω, G e = s(x, y) := h

theorem openBall_mono {n m : ℕ} (h : n ≤ m) : openBall G ω r n ⊆ openBall G ω r m := by
  induction m with
  | zero => rw [Nat.le_zero.mp h]
  | succ k ih =>
      rcases Nat.lt_or_eq_of_le h with hlt | heq
      · exact (ih (Nat.le_of_lt_succ hlt)).trans (openBall_subset_succ G ω r k)
      · rw [heq]

/-- Every point of a ball is in the open cluster of `r`. -/
theorem openBall_subset_conn (n : ℕ) : ∀ x : V, x ∈ openBall G ω r n → Conn G ω r x := by
  induction n with
  | zero =>
      intro x h
      rw [(mem_openBall_zero G ω r).mp h]
      exact conn_refl G ω r
  | succ k ih =>
      intro x h
      rcases mem_openBall_succ G ω r h with h' | ⟨z, hz, e, he, hze⟩
      · exact ih x h'
      · exact (ih z hz).tail ⟨e, he, hze⟩

/-- Every point of the cluster of `r` lies in some ball. -/
theorem conn_exists_openBall {x : V} (h : Conn G ω r x) : ∃ n, x ∈ openBall G ω r n := by
  induction h with
  | refl => exact ⟨0, by simp⟩
  | tail _ hstep ih =>
      obtain ⟨n, hn⟩ := ih
      obtain ⟨e, hmem⟩ := hstep
      obtain ⟨he, hE⟩ := hmem
      exact ⟨n + 1, mem_openBall_succ_of_edge G ω r hn he hE⟩

end Ball

/-! ### The BFS distance -/

section Dist

variable (G : BondGraph V E) (ω : Set E) (r : V)

/-- The graph distance from `r` in the open subgraph; `0` off the cluster of `r`. -/
noncomputable def bdist (x : V) : ℕ :=
  if h : ∃ n, x ∈ openBall G ω r n then Nat.find h else 0

theorem bdist_spec {x : V} (h : ∃ n, x ∈ openBall G ω r n) :
    x ∈ openBall G ω r (bdist G ω r x) := by
  rw [bdist, dite_eq_left h]
  exact Nat.find_spec h

theorem bdist_le {x : V} {n : ℕ} (h : x ∈ openBall G ω r n) : bdist G ω r x ≤ n := by
  have hex : ∃ m, x ∈ openBall G ω r m := ⟨n, h⟩
  rw [bdist, dite_eq_left hex]
  exact Nat.find_min' hex h

theorem bdist_eq_zero_iff {x : V} (hx : Conn G ω r x) : bdist G ω r x = 0 ↔ x = r := by
  constructor
  · intro h0
    have hex : ∃ n, x ∈ openBall G ω r n := conn_exists_openBall G ω r hx
    have hspec := bdist_spec G ω r hex
    rw [h0] at hspec
    exact (mem_openBall_zero G ω r).mp hspec
  · intro h
    rw [h]
    have hex : ∃ n, r ∈ openBall G ω r n := ⟨0, (mem_openBall_zero G ω r).mpr rfl⟩
    rw [bdist, dite_eq_left hex]
    have hle := Nat.find_min' hex ((mem_openBall_zero G ω r).mpr rfl)
    omega

/-- **The BFS predecessor step**, with no finiteness assumption. -/
theorem exists_parent_step {x : V} (hx : Conn G ω r x) (hne : x ≠ r) :
    ∃ y : V, Conn G ω r y ∧ bdist G ω r y + 1 = bdist G ω r x ∧
      ∃ e ∈ ω, G e = s(x, y) := by
  classical
  have hex : ∃ n, x ∈ openBall G ω r n := conn_exists_openBall G ω r hx
  have hpos : 1 ≤ bdist G ω r x := by
    rcases Nat.eq_zero_or_pos (bdist G ω r x) with h | h
    · exact absurd ((bdist_eq_zero_iff G ω r hx).mp h) hne
    · exact h
  obtain ⟨m, hm⟩ : ∃ m, bdist G ω r x = m + 1 := ⟨bdist G ω r x - 1, by omega⟩
  have hspec : x ∈ openBall G ω r (m + 1) := hm ▸ bdist_spec G ω r hex
  rcases mem_openBall_succ G ω r hspec with hin | ⟨y, hy, e, he, hE⟩
  · exact absurd (bdist_le G ω r hin) (by omega)
  · have hyb : bdist G ω r y ≤ m := bdist_le G ω r hy
    have hxb : bdist G ω r x ≤ bdist G ω r y + 1 :=
      bdist_le G ω r (mem_openBall_succ_of_edge G ω r (bdist_spec G ω r ⟨m, hy⟩) he hE)
    refine ⟨y, openBall_subset_conn G ω r _ y hy, by omega, e, he, ?_⟩
    rw [hE, Sym2.eq_swap]

end Dist

/-! ### The parent map on `V` -/

section Parent

variable (G : BondGraph V E) (ω : Set E) (r : V)

/-- **The BFS parent map of the cluster of `r`, as a self-map of `V`.**  A point of the cluster
other than `r` is sent to a chosen open neighbour one BFS step closer to `r`; every other point
(including `r`) is fixed. -/
noncomputable def par (x : V) : V :=
  if h : Conn G ω r x ∧ x ≠ r then
    Classical.choose (exists_parent_step G ω r h.1 h.2)
  else x

theorem par_of_mem {x : V} (hc : Conn G ω r x) (hne : x ≠ r) :
    par G ω r x = Classical.choose (exists_parent_step G ω r hc hne) := by
  rw [par, dite_eq_left ⟨hc, hne⟩]

theorem par_off {x : V} (h : ¬ (Conn G ω r x ∧ x ≠ r)) : par G ω r x = x := by
  rw [par, dite_eq_right h]

@[simp] theorem par_root : par G ω r r = r := par_off G ω r (fun h => h.2 rfl)

/-- The root is fixed by every iterate of the parent map. -/
theorem par_iterate_root (n : ℕ) : (par G ω r)^[n] r = r := by
  induction n with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply, par_root, ih]

/-- The parent of a non-root point of the cluster is in the cluster. -/
theorem par_conn {x : V} (hc : Conn G ω r x) (hne : x ≠ r) : Conn G ω r (par G ω r x) := by
  rw [par_of_mem G ω r hc hne]
  exact (Classical.choose_spec (exists_parent_step G ω r hc hne)).1

/-- The parent is exactly one BFS step closer to the root. -/
theorem par_bdist_succ {x : V} (hc : Conn G ω r x) (hne : x ≠ r) :
    bdist G ω r (par G ω r x) + 1 = bdist G ω r x := by
  rw [par_of_mem G ω r hc hne]
  exact (Classical.choose_spec (exists_parent_step G ω r hc hne)).2.1

/-- The parent is strictly closer to the root. -/
theorem par_bdist_lt {x : V} (hc : Conn G ω r x) (hne : x ≠ r) :
    bdist G ω r (par G ω r x) < bdist G ω r x := by
  have := par_bdist_succ G ω r hc hne
  omega

/-- **The parent edge is open** (at a non-root point of the cluster). -/
theorem par_open {x : V} (hc : Conn G ω r x) (hne : x ≠ r) :
    ∃ e ∈ ω, G e = s(x, par G ω r x) := by
  rw [par_of_mem G ω r hc hne]
  exact (Classical.choose_spec (exists_parent_step G ω r hc hne)).2.2

/-- **Every point of the cluster reaches `r` along iterated parents.** -/
theorem par_reaches_aux (k : ℕ) : ∀ x : V, Conn G ω r x → bdist G ω r x = k →
    ∃ n : ℕ, (par G ω r)^[n] x = r := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
      intro x hc hk
      by_cases h : x = r
      · refine ⟨0, ?_⟩
        rw [h, Function.iterate_zero_apply]
      · obtain ⟨n, hn⟩ := ih (bdist G ω r (par G ω r x))
          (by rw [← hk]; exact par_bdist_lt G ω r hc h) (par G ω r x)
          (par_conn G ω r hc h) rfl
        exact ⟨n + 1, by rw [Function.iterate_succ_apply]; exact hn⟩

theorem par_reaches {x : V} (hc : Conn G ω r x) : ∃ n : ℕ, (par G ω r)^[n] x = r :=
  par_reaches_aux G ω r _ x hc rfl

/-- Iterates of the parent map stay in the cluster. -/
theorem par_iterate_conn {x : V} (hc : Conn G ω r x) (n : ℕ) :
    Conn G ω r ((par G ω r)^[n] x) := by
  induction n with
  | zero => simpa using hc
  | succ j ih =>
      rw [Function.iterate_succ_apply']
      by_cases h : (par G ω r)^[j] x = r
      · rw [h, par_root]; exact conn_refl G ω r
      · exact par_conn G ω r ih h

/-- After `bdist x` parent steps one reaches the root: the exact iterate count. -/
theorem par_bdist_iterate {x : V} (hc : Conn G ω r x) :
    (par G ω r)^[bdist G ω r x] x = r := by
  suffices H : ∀ k : ℕ, ∀ x : V, Conn G ω r x → bdist G ω r x = k →
      (par G ω r)^[k] x = r from H _ x hc rfl
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
      intro x hc hk
      by_cases h : x = r
      · rw [h] at hk ⊢
        rw [← hk]
        exact par_iterate_root G ω r _
      · have hpb := par_bdist_succ G ω r hc h
        have hlt : bdist G ω r (par G ω r x) < k := by rw [hk] at hpb; omega
        have hk' : k = bdist G ω r (par G ω r x) + 1 := by omega
        rw [hk', Function.iterate_succ_apply]
        exact ih _ hlt (par G ω r x) (par_conn G ω r hc h) rfl

end Parent

end Countable
end Hutchcroft
