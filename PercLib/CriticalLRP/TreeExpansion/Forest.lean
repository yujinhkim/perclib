/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
The shortest-path forest rooted at a vertex, and the branch-point ("Steiner tree") structure
behind the tree-graph inequality (I.2.2) of

  T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
  arXiv:2508.18807v1, Section I.2.1, p. 22.

Setting: as in `CriticalPercLib.CriticalLRP.TreeGraph.Connectivity`, `E` is a finite type of
possible edges, `ends : E → Sym2 V` assigns endpoints (no injectivity assumed) and a
configuration is a `Finset E` of open edges.  Everything in this file is deterministic
(no probability).

* `lvl` — graph distance from the root `v`;
* `par` — parent in a shortest-path tree, `par_spec` — the parent step is realised by an open
  edge; `stepEdge u` is the singleton (or empty) set of those edges;
* `par_iter_root` — the parent chain reaches the root after `lvl u` steps;
* `belowChain u w` — the parent edges on the chain from a descendant `u` of `w` up to `w`,
  with `conn_belowChain : Conn belowChain w u` and `mem_belowChain`;
* `Anc u w` — `w` is `u` or an ancestor of `u`; the ancestor at a level is unique;
* `disjoint_belowChain` — chains through two different children of `w` are edge-disjoint.
-/
module

public import Mathlib
public import PercLib.CriticalLRP.TreeGraph.Connectivity

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP.TreeGraph

open Finset

variable {V : Type*} [DecidableEq V]
variable {E : Type*} [Fintype E] [DecidableEq E]

noncomputable section

/-! ### Levels -/

/-- The level of `u`: the graph distance from the root `v` in the open graph of `s`. -/
def lvl (ends : E → Sym2 V) (s : Finset E) (v u : V) : ℕ := (openGraph ends s).dist v u

variable {ends : E → Sym2 V} {s : Finset E} {v : V}

@[simp] theorem lvl_root : lvl ends s v v = 0 := SimpleGraph.dist_self

theorem lvl_le_of_conn {w : V} (p : (openGraph ends s).Walk v w) : lvl ends s v w ≤ p.length :=
  SimpleGraph.dist_le p

theorem lvl_eq_zero_iff_of_conn {u : V} (h : Conn ends s v u) : lvl ends s v u = 0 ↔ u = v := by
  have := h.dist_eq_zero_iff
  simpa [lvl, eq_comm] using this

/-! ### The parent of a vertex -/

/-- Every vertex at positive level has a parent one level below, joined to it by an open edge. -/
theorem exists_parent {u : V} (hu : 0 < lvl ends s v u) :
    ∃ p : E × V, p.1 ∈ s ∧ ends p.1 = s(u, p.2) ∧ lvl ends s v p.2 + 1 = lvl ends s v u := by
  have hne : lvl ends s v u ≠ 0 := by omega
  have hreach : (openGraph ends s).Reachable v u := SimpleGraph.Reachable.of_dist_ne_zero hne
  obtain ⟨p, hp⟩ := hreach.exists_walk_length_eq_dist
  have hp' : p.length = lvl ends s v u := hp
  have hnil : ¬ p.Nil := by rw [SimpleGraph.Walk.not_nil_iff_lt_length]; omega
  have hadj : (openGraph ends s).Adj p.penultimate u := SimpleGraph.Walk.adj_penultimate hnil
  have hle : lvl ends s v p.penultimate ≤ lvl ends s v u - 1 := by
    have h2 : lvl ends s v p.penultimate ≤ (p.take (p.length - 1)).length :=
      lvl_le_of_conn (p.take (p.length - 1))
    rw [SimpleGraph.Walk.take_length] at h2
    omega
  have hreach' : (openGraph ends s).Reachable v p.penultimate := hreach.trans hadj.reachable.symm
  have hge : lvl ends s v u ≤ lvl ends s v p.penultimate + 1 := by
    have h2 := hreach'.dist_triangle_left u
    have h3 : (openGraph ends s).dist p.penultimate u = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj
    simp only [lvl] at h2 ⊢
    omega
  have hlvl : lvl ends s v p.penultimate + 1 = lvl ends s v u := by
    have htri : lvl ends s v u = lvl ends s v p.penultimate ∨
        lvl ends s v u = lvl ends s v p.penultimate + 1 ∨
        lvl ends s v u = lvl ends s v p.penultimate - 1 := hadj.diff_dist_adj (u := v)
    omega
  obtain ⟨⟨a, ha, he⟩, -⟩ := openGraph_adj.mp hadj
  exact ⟨(a, p.penultimate), ha, by rw [he, Sym2.eq_swap], hlvl⟩

/-- A parent of `u` in a shortest-path tree; `par u = u` at level `0`. -/
def par (ends : E → Sym2 V) (s : Finset E) (v u : V) : V :=
  if h : 0 < lvl ends s v u then
    (Classical.choose (exists_parent (ends := ends) (s := s) (v := v) h)).2
  else u

/-- The open edges joining `u` to its parent: a singleton at positive level, empty at level `0`. -/
def stepEdge (ends : E → Sym2 V) (s : Finset E) (v u : V) : Finset E :=
  if h : 0 < lvl ends s v u then
    ({(Classical.choose (exists_parent (ends := ends) (s := s) (v := v) h)).1} : Finset E)
  else ∅

theorem par_eq_choose {u : V} (hu : 0 < lvl ends s v u) :
    par ends s v u = (Classical.choose (exists_parent (ends := ends) (s := s) (v := v) hu)).2 := by
  simp only [par]
  exact dite_eq_left hu

theorem stepEdge_eq_choose {u : V} (hu : 0 < lvl ends s v u) :
    stepEdge ends s v u =
      ({(Classical.choose (exists_parent (ends := ends) (s := s) (v := v) hu)).1} : Finset E) := by
  simp only [stepEdge]
  exact dite_eq_left hu

theorem par_spec {u : V} (hu : 0 < lvl ends s v u) :
    ∃ a : E, a ∈ s ∧ ends a = s(u, par ends s v u) ∧
      lvl ends s v (par ends s v u) + 1 = lvl ends s v u := by
  have h := Classical.choose_spec (exists_parent (ends := ends) (s := s) (v := v) hu)
  refine ⟨(Classical.choose (exists_parent (ends := ends) (s := s) (v := v) hu)).1, h.1, ?_, ?_⟩
  · rw [par_eq_choose hu]; exact h.2.1
  · rw [par_eq_choose hu]; exact h.2.2

theorem stepEdge_spec {u : V} (hu : 0 < lvl ends s v u) {a : E}
    (ha : a ∈ stepEdge ends s v u) : a ∈ s ∧ ends a = s(u, par ends s v u) := by
  have h := Classical.choose_spec (exists_parent (ends := ends) (s := s) (v := v) hu)
  have ha' : a = (Classical.choose (exists_parent (ends := ends) (s := s) (v := v) hu)).1 := by
    rw [stepEdge_eq_choose hu] at ha
    simpa using ha
  subst ha'
  exact ⟨h.1, by rw [par_eq_choose hu]; exact h.2.1⟩

theorem stepEdge_nonempty {u : V} (hu : 0 < lvl ends s v u) :
    (stepEdge ends s v u).Nonempty := by
  rw [stepEdge_eq_choose hu]
  exact Finset.singleton_nonempty _

theorem stepEdge_eq_empty {u : V} (hu : ¬ 0 < lvl ends s v u) :
    stepEdge ends s v u = ∅ := by
  simp only [stepEdge, dite_eq_right hu]

theorem par_eq_self {u : V} (hu : ¬ 0 < lvl ends s v u) : par ends s v u = u := by
  simp only [par, dite_eq_right hu]

theorem par_lvl_eq {u : V} (hu : 0 < lvl ends s v u) :
    lvl ends s v (par ends s v u) = lvl ends s v u - 1 := by
  have := (par_spec (ends := ends) (s := s) (v := v) hu).choose_spec.2.2
  omega

theorem par_lvl_lt {u : V} (hu : 0 < lvl ends s v u) :
    lvl ends s v (par ends s v u) < lvl ends s v u := by
  have := par_lvl_eq (ends := ends) (s := s) (v := v) hu
  omega

theorem par_adj {u : V} (hu : 0 < lvl ends s v u) :
    (openGraph ends s).Adj u (par ends s v u) := by
  obtain ⟨a, hmem, hends, -⟩ := par_spec (ends := ends) (s := s) (v := v) hu
  rw [openGraph_adj]
  refine ⟨⟨a, hmem, hends⟩, ?_⟩
  intro h
  have hlt := par_lvl_lt (ends := ends) (s := s) (v := v) hu
  rw [← h] at hlt
  exact absurd hlt (lt_irrefl _)

theorem eq_of_stepEdge_common {z z' : V} {a : E} (h1 : a ∈ stepEdge ends s v z)
    (h2 : a ∈ stepEdge ends s v z') : z = z' := by
  by_contra hne
  have hz : 0 < lvl ends s v z := by
    rcases Nat.eq_zero_or_pos (lvl ends s v z) with h0 | h0
    · rw [stepEdge_eq_empty (by omega : ¬ 0 < lvl ends s v z)] at h1
      simp at h1
    · exact h0
  have hz' : 0 < lvl ends s v z' := by
    rcases Nat.eq_zero_or_pos (lvl ends s v z') with h0 | h0
    · rw [stepEdge_eq_empty (by omega : ¬ 0 < lvl ends s v z')] at h2
      simp at h2
    · exact h0
  obtain ⟨-, h1'⟩ := stepEdge_spec hz h1
  obtain ⟨-, h2'⟩ := stepEdge_spec hz' h2
  rw [h1'] at h2'
  have := Sym2.eq_iff.mp h2'
  rcases this with ⟨rfl, -⟩ | ⟨hz1, hz2⟩
  · exact hne rfl
  · have e1 : lvl ends s v z = lvl ends s v z' - 1 := by rw [hz1]; exact par_lvl_eq hz'
    have e2 : lvl ends s v z' = lvl ends s v z - 1 := by rw [← hz2]; exact par_lvl_eq hz
    omega

/-! ### Iterates of the parent map -/

theorem lvl_par_iter (u : V) :
    ∀ k ≤ lvl ends s v u, lvl ends s v ((par ends s v)^[k] u) + k = lvl ends s v u := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
      intro hk
      have hk' : k ≤ lvl ends s v u := by omega
      have h1 := ih hk'
      have hpos : 0 < lvl ends s v ((par ends s v)^[k] u) := by omega
      have h2 := par_lvl_eq (ends := ends) (s := s) (v := v) hpos
      rw [Function.iterate_succ_apply']
      omega

theorem lvl_par_iter_eq (u : V) {k : ℕ} (hk : k ≤ lvl ends s v u) :
    lvl ends s v ((par ends s v)^[k] u) = lvl ends s v u - k := by
  have := lvl_par_iter (ends := ends) (s := s) (v := v) u k hk
  omega

theorem conn_par_iter {u : V} (hu : Conn ends s v u) :
    ∀ k, Conn ends s v ((par ends s v)^[k] u) := by
  intro k
  induction k with
  | zero => simpa using hu
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      by_cases hpos : 0 < lvl ends s v ((par ends s v)^[k] u)
      · exact ih.trans (par_adj hpos).reachable
      · rw [par_eq_self (ends := ends) (s := s) (v := v) hpos]; exact ih

/-- The parent chain reaches the root after `lvl u` steps. -/
theorem par_iter_root {u : V} (hu : Conn ends s v u) :
    (par ends s v)^[lvl ends s v u] u = v := by
  have hconn := conn_par_iter (ends := ends) (s := s) (v := v) hu (lvl ends s v u)
  have h0 : lvl ends s v ((par ends s v)^[lvl ends s v u] u) = 0 := by
    have := lvl_par_iter_eq (ends := ends) (s := s) (v := v) u (le_refl (lvl ends s v u))
    omega
  exact (lvl_eq_zero_iff_of_conn hconn).mp h0

/-! ### Ancestors -/

/-- `Anc u w`: `w` is `u` or an ancestor of `u` in the parent tree. -/
def Anc (ends : E → Sym2 V) (s : Finset E) (v u w : V) : Prop :=
  ∃ k ≤ lvl ends s v u, (par ends s v)^[k] u = w

theorem anc_refl (u : V) : Anc ends s v u u := ⟨0, Nat.zero_le _, rfl⟩

theorem anc_lvl_le {u w : V} (h : Anc ends s v u w) : lvl ends s v w ≤ lvl ends s v u := by
  obtain ⟨k, hk, hkw⟩ := h
  have hlev := lvl_par_iter_eq (ends := ends) (s := s) (v := v) u hk
  rw [← hkw]
  omega

theorem anc_par_iter {u w : V} (h : Anc ends s v u w) :
    (par ends s v)^[lvl ends s v u - lvl ends s v w] u = w := by
  obtain ⟨k, hk, hkw⟩ := h
  have hlev : lvl ends s v ((par ends s v)^[k] u) = lvl ends s v u - k :=
    lvl_par_iter_eq (ends := ends) (s := s) (v := v) u hk
  have hw : lvl ends s v w = lvl ends s v u - k := by rw [← hkw]; exact hlev
  have : lvl ends s v u - lvl ends s v w = k := by omega
  rw [this, hkw]

theorem anc_eq_of_lvl_eq {u w w' : V} (h : Anc ends s v u w) (h' : Anc ends s v u w')
    (hl : lvl ends s v w = lvl ends s v w') : w = w' := by
  rw [← anc_par_iter (ends := ends) (s := s) (v := v) h,
    ← anc_par_iter (ends := ends) (s := s) (v := v) h', hl]

theorem anc_iter {u : V} {k : ℕ} (hk : k ≤ lvl ends s v u) :
    Anc ends s v u ((par ends s v)^[k] u) := ⟨k, hk, rfl⟩

theorem anc_of_par_iter {u w : V} (h : Anc ends s v u w) (hw : lvl ends s v w < lvl ends s v u) :
    Anc ends s v (par ends s v u) w := by
  obtain ⟨k, hk, hkw⟩ := h
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0] at hkw; simp at hkw; subst hkw; omega
    · exact h0
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hpos : 0 < lvl ends s v u := by omega
  refine ⟨k', ?_, ?_⟩
  · rw [par_lvl_eq hpos]; omega
  · rw [Nat.succ_eq_add_one, Function.iterate_succ_apply] at hkw
    exact hkw

theorem par_iter_swap (j : ℕ) (u : V) :
    (par ends s v)^[j] (par ends s v u) = (par ends s v)^[j + 1] u := by
  rw [Function.iterate_succ_apply]

theorem par_iter_swap' (j : ℕ) (u : V) :
    par ends s v ((par ends s v)^[j] u) = (par ends s v)^[j + 1] u := by
  rw [Function.iterate_succ_apply']

/-! ### The chain from a descendant to an ancestor -/

/-- The parent edges on the chain from `u` up to `w` (using the chain length `lvl u - lvl w`);
empty unless `w` is an ancestor of `u`. -/
def belowChain (ends : E → Sym2 V) (s : Finset E) (v u w : V) : Finset E :=
  (Finset.range (lvl ends s v u - lvl ends s v w)).biUnion (fun j => stepEdge ends s v ((par ends s v)^[j] u))

theorem mem_belowChain {u w : V} {a : E} :
    a ∈ belowChain ends s v u w ↔
      ∃ j < lvl ends s v u - lvl ends s v w, a ∈ stepEdge ends s v ((par ends s v)^[j] u) := by
  simp [belowChain]

theorem belowChain_subset {u w : V} (hwu : lvl ends s v w ≤ lvl ends s v u) :
    belowChain ends s v u w ⊆ s := by
  intro a ha
  rw [mem_belowChain] at ha
  obtain ⟨j, hj, hj'⟩ := ha
  have hk : j ≤ lvl ends s v u := by omega
  have hlv := lvl_par_iter_eq (ends := ends) (s := s) (v := v) u hk
  have hpos : 0 < lvl ends s v ((par ends s v)^[j] u) := by omega
  exact (stepEdge_spec hpos hj').1

theorem belowChain_par {u w : V} (hu : lvl ends s v w < lvl ends s v u) :
    belowChain ends s v u w = stepEdge ends s v u ∪ belowChain ends s v (par ends s v u) w := by
  have hpos : 0 < lvl ends s v u := by omega
  have hl := par_lvl_eq (ends := ends) (s := s) (v := v) hpos
  ext a
  rw [mem_belowChain, Finset.mem_union, mem_belowChain]
  constructor
  · rintro ⟨j, hj, ha⟩
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · left; rw [h0] at ha; simpa using ha
    · right
      obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
      refine ⟨j', by omega, ?_⟩
      rw [Function.iterate_succ_apply'] at ha
      rw [par_iter_swap'] at ha
      rw [par_iter_swap]
      exact ha
  · rintro (ha | ⟨j, hj, ha⟩)
    · exact ⟨0, by omega, by simpa using ha⟩
    · refine ⟨j + 1, by omega, ?_⟩
      rw [par_iter_swap] at ha
      exact ha

theorem belowChain_self (u : V) : belowChain ends s v u u = ∅ := by
  have : lvl ends s v u - lvl ends s v u = 0 := by omega
  simp only [belowChain, this, Finset.range_zero, Finset.biUnion_empty]

/-- The parent-chain edges connect a descendant to its ancestor. -/
theorem conn_belowChain_aux (u w : V) (k : ℕ) (hk : k ≤ lvl ends s v u)
    (hkw : (par ends s v)^[k] u = w) : Conn ends (belowChain ends s v u w) w u := by
  revert u
  induction k with
  | zero =>
      intro u hk hkw
      have hwu : u = w := by simpa using hkw
      rw [hwu, belowChain_self]
      exact conn_refl ends ∅ w
  | succ k ih =>
      intro u hk hkw
      have hpos : 0 < lvl ends s v u := by omega
      have hstep : (par ends s v)^[k] (par ends s v u) = w := by
        rw [par_iter_swap]
        exact hkw
      have hk' : k ≤ lvl ends s v (par ends s v u) := by
        rw [par_lvl_eq hpos]; omega
      have hpar := ih (par ends s v u) hk' hstep
      have hlt : lvl ends s v w < lvl ends s v u := by
        have hlev := lvl_par_iter_eq (ends := ends) (s := s) (v := v) u hk
        rw [hkw] at hlev
        omega
      rw [belowChain_par hlt]
      have hconn1 : Conn ends (stepEdge ends s v u ∪ belowChain ends s v (par ends s v u) w)
          w (par ends s v u) := conn_mono Finset.subset_union_right hpar
      obtain ⟨a, ha⟩ := stepEdge_nonempty (ends := ends) (s := s) (v := v) hpos
      obtain ⟨hmems, hends⟩ := stepEdge_spec hpos ha
      have hadj : (openGraph ends (stepEdge ends s v u ∪ belowChain ends s v (par ends s v u) w)).Adj
          u (par ends s v u) := by
        rw [openGraph_adj]
        refine ⟨⟨a, Finset.subset_union_left ha, hends⟩, ?_⟩
        intro h
        have hlt2 := par_lvl_lt (ends := ends) (s := s) (v := v) hpos
        rw [← h] at hlt2
        exact absurd hlt2 (lt_irrefl _)
      exact hconn1.trans hadj.reachable.symm

theorem conn_belowChain {u w : V} (h : Anc ends s v u w) :
    Conn ends (belowChain ends s v u w) w u := by
  obtain ⟨k, hk, hkw⟩ := h
  exact conn_belowChain_aux u w k hk hkw

/-- The child of `w` on the chain from a descendant `u` up to `w`. -/
def childOf (ends : E → Sym2 V) (s : Finset E) (v u w : V) : V :=
  (par ends s v)^[lvl ends s v u - lvl ends s v w - 1] u

theorem childOf_par {u w : V} (h : Anc ends s v u w) (hw : lvl ends s v w < lvl ends s v u) :
    par ends s v (childOf ends s v u w) = w := by
  have hd : lvl ends s v u - lvl ends s v w ≠ 0 := by omega
  obtain ⟨d, hd'⟩ := Nat.exists_eq_succ_of_ne_zero hd
  have hexp : lvl ends s v u - lvl ends s v w - 1 = d := by omega
  have h1 : (par ends s v)^[Nat.succ d] u = w := by
    have h2 := anc_par_iter h
    rw [show lvl ends s v u - lvl ends s v w = Nat.succ d from by omega] at h2
    exact h2
  rw [childOf, hexp]
  rw [← Function.iterate_succ_apply' (par ends s v) d u]
  exact h1

theorem childOf_lvl {u w : V} (h : Anc ends s v u w) (hw : lvl ends s v w < lvl ends s v u) :
    lvl ends s v (childOf ends s v u w) = lvl ends s v w + 1 := by
  have hd : lvl ends s v u - lvl ends s v w ≠ 0 := by omega
  obtain ⟨d, hd'⟩ := Nat.exists_eq_succ_of_ne_zero hd
  have hexp : lvl ends s v u - lvl ends s v w - 1 = d := by omega
  have hk : d ≤ lvl ends s v u := by omega
  have := lvl_par_iter_eq (ends := ends) (s := s) (v := v) u hk
  rw [childOf, hexp]
  omega

/-- Every vertex of the part of the chain strictly below `w` has the same child of `w`. -/
theorem childOf_iter {u w : V} (h : Anc ends s v u w) {j : ℕ}
    (hj : j < lvl ends s v u - lvl ends s v w) :
    childOf ends s v ((par ends s v)^[j] u) w = childOf ends s v u w := by
  have hjle : j ≤ lvl ends s v u := by omega
  have hlv := lvl_par_iter_eq (ends := ends) (s := s) (v := v) u hjle
  have hanc : Anc ends s v ((par ends s v)^[j] u) w :=
    ⟨lvl ends s v u - lvl ends s v w - j, by omega, by
      rw [← Function.iterate_add_apply, show lvl ends s v u - lvl ends s v w - j + j
          = lvl ends s v u - lvl ends s v w from by omega, anc_par_iter h]⟩
  have hlt : lvl ends s v w < lvl ends s v ((par ends s v)^[j] u) := by omega
  simp only [childOf]
  rw [hlv, ← Function.iterate_add_apply]
  congr 1
  omega

/-- Chains through two different children of `w` are edge-disjoint. -/
theorem disjoint_belowChain {u u' w : V} (hu : Anc ends s v u w) (hu' : Anc ends s v u' w)
    (hne : childOf ends s v u w ≠ childOf ends s v u' w) :
    Disjoint (belowChain ends s v u w) (belowChain ends s v u' w) := by
  rw [Finset.disjoint_left]
  intro a ha ha'
  rw [mem_belowChain] at ha ha'
  obtain ⟨j, hj, hmem⟩ := ha
  obtain ⟨j', hj', hmem'⟩ := ha'
  have hz : (par ends s v)^[j] u = (par ends s v)^[j'] u' := eq_of_stepEdge_common hmem hmem'
  have c1 := childOf_iter (ends := ends) (s := s) (v := v) hu hj
  have c2 := childOf_iter (ends := ends) (s := s) (v := v) hu' hj'
  exact hne (by rw [← c1, ← c2, hz])

/-- Level separation: the chain from the root to `w` and any chain below `w` are disjoint. -/
theorem disjoint_belowChain_root {u w : V} (h : Anc ends s v u w)
    (hw : lvl ends s v w < lvl ends s v u) :
    Disjoint (belowChain ends s v w v) (belowChain ends s v u w) := by
  rw [Finset.disjoint_left]
  intro a ha ha'
  rw [mem_belowChain] at ha ha'
  obtain ⟨j, hj, hmem⟩ := ha
  obtain ⟨j', hj', hmem'⟩ := ha'
  simp only [lvl_root] at hj
  have hz : (par ends s v)^[j] w = (par ends s v)^[j'] u := eq_of_stepEdge_common hmem hmem'
  have hlv1 := lvl_par_iter_eq (ends := ends) (s := s) (v := v) w (by omega : j ≤ lvl ends s v w)
  have hlv2 := lvl_par_iter_eq (ends := ends) (s := s) (v := v) u (by omega : j' ≤ lvl ends s v u)
  have hlveq : lvl ends s v w - j = lvl ends s v u - j' := by rw [← hlv1, ← hlv2, hz]
  omega

end

end PercLib.CriticalLRP.TreeGraph
