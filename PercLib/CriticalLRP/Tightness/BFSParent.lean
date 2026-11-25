/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
# The BFS (shortest-path) parent map of an open percolation cluster, on the cluster's vertex type

Reference: T. Hutchcroft, *Power-law bounds for critical long-range percolation below the
upper-critical dimension*, arXiv:2008.11197v2, Section 2.1 (proof of Theorem 2.3): the witnesses for
the BK step are the edges of a spanning tree of the open cluster `K_v`, cut into pieces.  This file
supplies the parent map of such a spanning tree for an arbitrary (not necessarily connected) finite
bond graph and open edge set, working **inside one cluster at a time**.

Main points:

* `openBall G ω r n` is the set of vertices reachable from `r` by at most `n` open edges, and
  `bdist G ω r x` is the least such `n` (a junk value `0` off the cluster).
* `Cl G ω r` is the vertex type of the open cluster of `r`, i.e. the subtype `{x // Conn G ω r x}`.
  Working with this subtype means no global root is invented and no open edge is invented between
  distinct clusters: `Cl` is *one* actual cluster.
* `bfsParent G ω r : Cl G ω r → Cl G ω r` sends `x ≠ r` to a chosen open neighbour `y` with
  `bdist y + 1 = bdist x` (the predecessor of `x` on a shortest open path from `r`), and fixes `r`.
* `bfsParent_open`: the parent edge of every `x ≠ r` is an *open* edge of `G`, and both endpoints
  lie in the cluster.
* `bfsParent_isRootedForest`: `IsRootedForest (bfsParent G ω r) r`, i.e. `r` is fixed and every
  vertex of the cluster reaches `r` along parent edges. This is the hypothesis of
  `Hutchcroft.exists_tree_pieces`.
* `bfsParent_periodic`: the only periodic point of the BFS parent map is the root.
-/
module

public import Mathlib
public import PercLib.CriticalLRP.BK.Graph
public import PercLib.CriticalLRP.Tightness.TreePieces

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

@[expose] public section

namespace Hutchcroft

open PercLib.CriticalLRP.Percolation

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V] {E : Type*}

/-! ### Balls of the open graph -/

section Ball

variable (G : BondGraph V E) (ω : Set E) (r : V)

/-- `openBall G ω r n`: the vertices of `V` reachable from `r` by a path of at most `n` *open*
edges (`y` is added at stage `n+1` if it is joined to a vertex of stage `n` by an edge of `ω`). -/
def openBall : ℕ → Set V
  | 0 => {r}
  | n + 1 => openBall n ∪ {y | ∃ x ∈ openBall n, ∃ e ∈ ω, G e = s(x, y)}

@[simp] theorem mem_openBall_zero {y : V} : y ∈ openBall G ω r 0 ↔ y = r := Iff.rfl

theorem openBall_subset_succ (n : ℕ) : openBall G ω r n ⊆ openBall G ω r (n + 1) :=
  Set.subset_union_left

/-- The stage-`n+1` rule: an open edge out of stage `n` puts its far endpoint in stage `n+1`. -/
theorem mem_openBall_succ_of_edge {n : ℕ} {x y : V} (hx : x ∈ openBall G ω r n)
    {e : E} (he : e ∈ ω) (hxy : G e = s(x, y)) : y ∈ openBall G ω r (n + 1) :=
  Set.mem_union_right _ ⟨x, hx, e, he, hxy⟩

theorem mem_openBall_succ {n : ℕ} {y : V} (h : y ∈ openBall G ω r (n + 1)) :
    y ∈ openBall G ω r n ∨ ∃ x ∈ openBall G ω r n, ∃ e ∈ ω, G e = s(x, y) := h

/-- Balls are monotone in the radius. -/
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

/-- The graph distance from `r` in the open subgraph (least `n` with `x` reachable in `≤ n` open
steps); `0` off the cluster of `r`. -/
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

/-- On the cluster of `r`, the BFS distance vanishes exactly at the root. -/
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

/-- **The BFS predecessor step.**  Every vertex of the cluster of `r` other than `r` has an open
neighbour one step closer to `r` in the open graph. -/
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

/-! ### The parent map on the vertex type of one open cluster -/

section Parent

variable (G : BondGraph V E) (ω : Set E) (r : V)

/-- The vertex type of the open cluster of `r`: `{x // Conn G ω r x}`.  Working on this subtype is
what makes the construction component-wise: the parent map never leaves the cluster of `r`, and no
root or open edge between distinct clusters is invented. -/
abbrev Cl : Type _ := {x : V // Conn G ω r x}

noncomputable instance instFintypeCl : Fintype (Cl G ω r) := by
  classical exact Subtype.fintype _

/-- The root of the cluster, as an element of `Cl G ω r`. -/
def clRoot : Cl G ω r := ⟨r, conn_refl G ω r⟩

@[simp] theorem clRoot_val : (clRoot G ω r : V) = r := rfl

/-- **The BFS parent map** of the open cluster of `r`: `x ≠ r` is sent to a chosen open neighbour
one step closer to `r`; `r` is sent to itself. -/
noncomputable def bfsParent (x : Cl G ω r) : Cl G ω r :=
  if h : (x : V) = r then clRoot G ω r
  else
    ⟨Classical.choose (exists_parent_step G ω r x.2 h),
      (Classical.choose_spec (exists_parent_step G ω r x.2 h)).1⟩

theorem bfsParent_val_of_ne {x : Cl G ω r} (h : (x : V) ≠ r) :
    (bfsParent G ω r x : V) = Classical.choose (exists_parent_step G ω r x.2 h) := by
  rw [bfsParent, dite_eq_right h]

/-- **Parent edges are open.**  For every vertex of the cluster other than the root, the edge to its
parent exists in the graph and belongs to `ω`. -/
theorem bfsParent_open {x : Cl G ω r} (h : (x : V) ≠ r) :
    ∃ e ∈ ω, G e = s((x : V), (bfsParent G ω r x : V)) := by
  rw [bfsParent_val_of_ne G ω r h]
  exact (Classical.choose_spec (exists_parent_step G ω r x.2 h)).2.2

/-- The parent of a non-root vertex is strictly closer to the root. -/
theorem bfsParent_rank_lt {x : Cl G ω r} (h : (x : V) ≠ r) :
    bdist G ω r (bfsParent G ω r x : V) < bdist G ω r (x : V) := by
  rw [bfsParent_val_of_ne G ω r h]
  have := (Classical.choose_spec (exists_parent_step G ω r x.2 h)).2.1
  omega

/-- The parent of a non-root vertex is exactly one step closer to the root. -/
theorem bfsParent_bdist_succ {x : Cl G ω r} (h : (x : V) ≠ r) :
    bdist G ω r (bfsParent G ω r x : V) + 1 = bdist G ω r (x : V) := by
  rw [bfsParent_val_of_ne G ω r h]
  exact (Classical.choose_spec (exists_parent_step G ω r x.2 h)).2.1

/-- The root is a fixed point of the parent map (its "parent edge" is not a real edge). -/
@[simp] theorem bfsParent_root : bfsParent G ω r (clRoot G ω r) = clRoot G ω r := by
  unfold bfsParent
  rw [dite_eq_left (clRoot_val G ω r)]

/-- **Every vertex of the cluster reaches the root along parent edges.** -/
theorem bfsParent_reaches_root_aux (k : ℕ) :
    ∀ x : Cl G ω r, bdist G ω r (x : V) = k →
      ∃ n : ℕ, (bfsParent G ω r)^[n] x = clRoot G ω r := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
      intro x hk
      by_cases h : (x : V) = r
      · refine ⟨0, ?_⟩
        rw [Function.iterate_zero_apply]
        exact Subtype.ext h
      · obtain ⟨n, hn⟩ :=
          ih (bdist G ω r (bfsParent G ω r x : V))
            (by rw [← hk]; exact bfsParent_rank_lt G ω r h) (bfsParent G ω r x) rfl
        exact ⟨n + 1, by rw [Function.iterate_succ_apply]; exact hn⟩

theorem bfsParent_reaches_root (x : Cl G ω r) :
    ∃ n : ℕ, (bfsParent G ω r)^[n] x = clRoot G ω r :=
  bfsParent_reaches_root_aux G ω r _ x rfl

/-- **The BFS parent map is the parent map of a rooted forest.**  This is precisely the hypothesis
of the corrected tree-piece lemma `Hutchcroft.exists_tree_pieces`. -/
theorem bfsParent_isRootedForest : IsRootedForest (bfsParent G ω r) (clRoot G ω r) :=
  ⟨bfsParent_root G ω r, bfsParent_reaches_root G ω r⟩

/-- **The only periodic point of the BFS parent map is the root.**  In particular
`bfsParent x ≠ x` for `x ≠ r`: the parent edge of a non-root vertex is a genuine edge and is open. -/
theorem bfsParent_periodic {n : ℕ} (hn : 1 ≤ n) {x : Cl G ω r}
    (hx : (bfsParent G ω r)^[n] x = x) : x = clRoot G ω r :=
  isRootedForest_periodic (bfsParent_isRootedForest G ω r) hn hx

/-- No vertex of the cluster other than the root is its own parent (so parent edges of distinct
vertices in a piece are distinct edges). -/
theorem bfsParent_ne_self {x : Cl G ω r} (h : x ≠ clRoot G ω r) : bfsParent G ω r x ≠ x := by
  intro hx
  exact h (bfsParent_periodic G ω r le_rfl (by rw [Function.iterate_one]; exact hx))

/-! ### The cluster is connected, and the parent map stays inside it -/

/-- All points of the cluster lie in one cluster of the open graph: pairwise connectivity. -/
theorem cl_conn (x y : Cl G ω r) : Conn G ω (x : V) (y : V) :=
  conn_trans G ω (conn_symm G ω x.2) y.2

theorem cl_conn_root (x : Cl G ω r) : Conn G ω r (x : V) := x.2

/-- The vertex set of `Cl G ω r` really is the cluster of `r`. -/
theorem cl_val_mem_cluster (x : Cl G ω r) : (x : V) ∈ cluster G ω r := x.2

end Parent

end Hutchcroft
