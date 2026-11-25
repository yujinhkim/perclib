/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
The `m = 2` instance of the tree sum, checked against the repository's three-point
tree-graph inequality `three_point_tree_graph` (equation (I.2.1), the `k = 2` case of
(I.2.2)):

  `P_β(x↔y↔z) ≤ ∑_w P_β(x↔w) P_β(w↔y) P_β(w↔z)`.

This file proves that the tree sum of `TreeExpansion.I23` at `m = 2`,
`treeSum k 2 v x = 2^{-1} ∑_{t} wt k t x v` over the two plane trees with two labelled
leaves, is exactly the three-point sum `∑_w k v w · k w (x 0) · k w (x 1)`. This checks
both the `2^{-(m-1)}` normalisation and the tree-weight convention against the one
instance of (I.2.2) that the repository already proves. Consequently the `m = 2` instance
of `TreeGraphBound` follows from `three_point_tree_graph`, so the hypothesis of
`moment_bound_of_tree_graph` is consistent with the established correlation inequality.
-/
module

public import Mathlib
public import PercLib.CriticalLRP.TreeExpansion.Consistency

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

set_option autoImplicit false

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion

open Finset
open PercLib.CriticalLRP.TreeGraph

namespace RTree

variable {V : Type*} {k : V → V → ℝ}

/-- The plane tree `node (leaf 0) (leaf 1)`, fully labelled. -/
def tL : RTree.LT (Fin 2) :=
  ⟨node (leaf 0) (leaf 1), by
    refine ⟨?_, ?_⟩
    · simp
    · simp [numLeaves]⟩

/-- The plane tree `node (leaf 1) (leaf 0)`, fully labelled. -/
def tR : RTree.LT (Fin 2) :=
  ⟨node (leaf 1) (leaf 0), by
    refine ⟨?_, ?_⟩
    · simp
    · simp [numLeaves]⟩

theorem tL_ne_tR : tL ≠ tR := by
  intro h
  have := congrArg (fun s : RTree.LT (Fin 2) => s.val) h
  simp [tL, tR] at this

/-- The two fully labelled plane trees with two leaves over `Fin 2`. -/
theorem LT_fin_two_cases (t : RTree.LT (Fin 2)) : t = tL ∨ t = tR := by
  obtain ⟨s, hs⟩ := t
  obtain ⟨hnd, hlen⟩ := hs
  have hnum : s.numLeaves = 2 := by
    rw [show s.numLeaves = s.leaves.length from rfl, hlen, Fintype.card_fin]
  match s with
  | leaf a =>
      simp only [numLeaves, leaves_leaf, List.length_cons, List.length_nil] at hnum
      exact absurd hnum (by norm_num)
  | node l r =>
      match l with
      | leaf a =>
          match r with
          | leaf b =>
              rw [leaves_node, leaves_leaf, leaves_leaf] at hnd
              have hab : a ≠ b := by
                intro h
                subst h
                simp at hnd
              have hcases : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
                revert hab
                fin_cases a <;> fin_cases b <;> simp_all
              rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact Or.inl (Subtype.ext rfl)
              · exact Or.inr (Subtype.ext rfl)
          | node rl rr =>
              exfalso
              simp only [numLeaves, leaves_node, leaves_leaf, List.length_append,
                List.length_cons, List.length_nil] at hnum
              have h1 : 0 < rl.numLeaves := numLeaves_pos rl
              have h2 : 0 < rr.numLeaves := numLeaves_pos rr
              simp only [numLeaves] at h1 h2
              omega
      | node ll lr =>
          exfalso
          simp only [numLeaves, leaves_node, leaves_leaf, List.length_append,
            List.length_cons, List.length_nil] at hnum
          have h1 : 0 < ll.numLeaves := numLeaves_pos ll
          have h2 : 0 < lr.numLeaves := numLeaves_pos lr
          have h3 : 0 < r.numLeaves := numLeaves_pos r
          simp only [numLeaves] at h1 h2 h3
          omega

/-- The tree weight of `tL`. -/
theorem wt_two_left [Fintype V] (k : V → V → ℝ) (v : V) (x : Fin 2 → V) :
    wt k tL.val (fun q => x (leafOfPos tL.val q)) v
      = ∑ w : V, k v w * k w (x 0) * k w (x 1) := rfl

/-- The tree weight of `tR`. -/
theorem wt_two_right [Fintype V] (k : V → V → ℝ) (v : V) (x : Fin 2 → V) :
    wt k tR.val (fun q => x (leafOfPos tR.val q)) v
      = ∑ w : V, k v w * k w (x 1) * k w (x 0) := rfl

end RTree

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The tree sum at `m = 2` is the three-point sum.** -/
theorem treeSum_two (k : V → V → ℝ) (v : V) (x : Fin 2 → V) :
    treeSum k 2 v x = ∑ w : V, k v w * k w (x 0) * k w (x 1) := by
  classical
  have huniv : (Finset.univ : Finset (RTree.LT (Fin 2))) = {RTree.tL, RTree.tR} := by
    ext t
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact RTree.LT_fin_two_cases t
  have hL : RTree.wt k RTree.tL.val (fun q => x (RTree.leafOfPos RTree.tL.val q)) v
      = ∑ w : V, k v w * k w (x 0) * k w (x 1) := RTree.wt_two_left k v x
  have hR : RTree.wt k RTree.tR.val (fun q => x (RTree.leafOfPos RTree.tR.val q)) v
      = ∑ w : V, k v w * k w (x 0) * k w (x 1) := by
    rw [RTree.wt_two_right]
    exact Finset.sum_congr rfl fun w _ => by ring
  rw [treeSum, huniv, Finset.sum_pair RTree.tL_ne_tR, hL, hR]
  ring

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- **The `m = 2` case of (I.2.2)**: `TreeGraphBound` at `m = 2` is the three-point
tree-graph inequality (I.2.1). -/
theorem treeGraphBound_two_of_three_point (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e)
    (hp1 : ∀ e, pr e ≤ 1) (hBK : BKIncreasing pr) (ends : E → Sym2 V) :
    ∀ x : Fin 3 → V,
      prob pr {s | ∀ i : Fin 3, Conn ends s (x 0) (x i)}
        ≤ treeSum (twoPoint pr ends) 2 (x 0) (fun j => x (Fin.succ j)) := by
  intro x
  rw [treeSum_two]
  have hset : {s | ∀ i : Fin 3, Conn ends s (x 0) (x i)}
      = {s | Conn ends s (x 0) (x 1) ∧ Conn ends s (x 0) (x 2)} := by
    ext s
    constructor
    · intro h
      exact ⟨h 1, h 2⟩
    · intro h i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact conn_refl ends s _
      · fin_cases j
        · exact h.1
        · exact h.2
  rw [hset]
  have h3 := three_point_tree_graph (p := pr) hp hp1 hBK ends (x 0) (x 1) (x 2)
  refine le_trans h3 ?_
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
  intro w _ _
  refine mul_nonneg (mul_nonneg (prob_nonneg hp hp1 _) (prob_nonneg hp hp1 _))
    (prob_nonneg hp hp1 _)

end PercLib.CriticalLRP.TreeExpansion
