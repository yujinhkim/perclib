/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
The tree-graph inequality (I.2.2) of Hutchcroft, *Critical long-range percolation I*,
arXiv:2508.18807v1, Section I.2.1, p. 22, proved from the BK inequality.

The proof combines
* the deterministic branch-point decomposition `exists_branch_split` (Forest/Decomp),
* the BK inequality `bk_three` for three increasing events with disjoint witnesses,
* the tree-sum recursion step `TS_split_le` (TreeRec),

by strong induction on the number of terminals.
-/
module

public import Mathlib
public import PercLib.CriticalLRP.TreeExpansion.TreeSumRecursion
public import PercLib.CriticalLRP.TreeExpansion.BranchSplit
public import PercLib.CriticalLRP.TreeGraph.ThreePoint
public import PercLib.CriticalLRP.TreeExpansion.Moments

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

@[expose] public section

namespace PercLib.CriticalLRP.TreeGraph

open Finset
open PercLib.CriticalLRP.TreeExpansion

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {E : Type*} [Fintype E] [DecidableEq E]
variable {ends : E → Sym2 V} {s : Finset E} {v : V}

/-! ### The tree sum at a single label, and its constant lower bound -/

/-- There is only one tree whose leaves are labelled by a single label. -/
theorem LTon.subsingleton_singleton {α : Type*} [DecidableEq α] (a : α) :
    Subsingleton (LTon α {a}) := by
  constructor
  intro t t'
  have ht : t = ⟨RTree.leaf a, by simp⟩ := by
    obtain ⟨tl, hnd, htf⟩ := t
    cases tl with
    | leaf b =>
        have : b = a := by simpa using htf
        subst this; rfl
    | node l r =>
        have h3 : (RTree.node l r).leaves.length = 1 := by
          rw [← List.toFinset_card_of_nodup hnd, htf]; simp
        have h2 : (RTree.node l r).leaves.length = l.leaves.length + r.leaves.length := by
          rw [RTree.leaves_node, List.length_append]
        have hp1 : 0 < l.leaves.length := RTree.numLeaves_pos l
        have hp2 : 0 < r.leaves.length := RTree.numLeaves_pos r
        omega
  have ht' : t' = ⟨RTree.leaf a, by simp⟩ := by
    obtain ⟨tl, hnd, htf⟩ := t'
    cases tl with
    | leaf b =>
        have : b = a := by simpa using htf
        subst this; rfl
    | node l r =>
        have h3 : (RTree.node l r).leaves.length = 1 := by
          rw [← List.toFinset_card_of_nodup hnd, htf]; simp
        have h2 : (RTree.node l r).leaves.length = l.leaves.length + r.leaves.length := by
          rw [RTree.leaves_node, List.length_append]
        have hp1 : 0 < l.leaves.length := RTree.numLeaves_pos l
        have hp2 : 0 < r.leaves.length := RTree.numLeaves_pos r
        omega
  rw [ht, ht']

theorem OnTrees_singleton {α : Type*} [DecidableEq α] (k : V → V → ℝ) (a : α) (y : α → V)
    (v : V) : OnTrees k ({a} : Finset α) y v = k v (y a) := by
  classical
  have := LTon.subsingleton_singleton (α := α) a
  rw [OnTrees, Finset.sum_eq_single (⟨RTree.leaf a, by simp⟩ : LTon α {a})]
  · simp
  · intro b _ hb
    exact absurd (Subsingleton.elim b _) hb
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem TS_singleton {α : Type*} [DecidableEq α] (k : V → V → ℝ) (a : α) (y : α → V)
    (v : V) : TS k ({a} : Finset α) y v = k v (y a) := by
  rw [TS, OnTrees_singleton]
  simp

/-- **A constant lower bound for the tree sum**: if all leaves carry the value `u` and
`k u u = 1`, the normalized tree sum at the root `u` is at least `1`. -/
theorem one_le_TS_const {α : Type*} [DecidableEq α] (k : V → V → ℝ) (hk : ∀ a b, 0 ≤ k a b)
    {u : V} (huu : k u u = 1) :
    ∀ (n : ℕ) (Z : Finset α), Z.card = n → Z.Nonempty →
      1 ≤ TS k Z (fun _ => u) u := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Z hZ hne
    rcases Nat.lt_or_ge Z.card 2 with h1 | h1
    · -- a single label
      have hc1 : Z.card = 1 := by
        have := Finset.card_pos.mpr hne
        omega
      obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc1
      rw [TS_singleton, huu]
    · -- split off one label
      obtain ⟨a, ha⟩ := hne
      have hne' : Z.Nonempty := ⟨a, ha⟩
      have hdisj : Disjoint ({a} : Finset α) (Z.erase a) :=
        Finset.disjoint_singleton_left.mpr (Finset.notMem_erase a Z)
      have h1' : ({a} : Finset α).Nonempty := ⟨a, Finset.mem_singleton_self a⟩
      have h2' : (Z.erase a).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem ha]
        have := Finset.card_pos.mpr hne'
        omega
      have hsplit := TS_split_le (k := k) hk hdisj h1' h2' (fun _ => u) u
      have hsingle : ∀ w : V, TS k ({a} : Finset α) (fun _ => u) w = k w u :=
        fun w => by rw [TS_singleton]
      rw [← Finset.insert_eq, Finset.insert_erase ha] at hsplit
      have hsum : (∑ w : V, k u w * TS k ({a} : Finset α) (fun _ => u) w *
            TS k (Z.erase a) (fun _ => u) w)
          = ∑ w : V, k u w * k w u * TS k (Z.erase a) (fun _ => u) w := by
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [hsingle w]
      rw [hsum] at hsplit
      have hterm : TS k (Z.erase a) (fun _ => u) u
          ≤ ∑ w : V, k u w * k w u * TS k (Z.erase a) (fun _ => u) w := by
        have h0 : 0 ≤ TS k (Z.erase a) (fun _ => u) u := TS_nonneg hk _ _ _
        have h1u : k u u * k u u * TS k (Z.erase a) (fun _ => u) u
            = TS k (Z.erase a) (fun _ => u) u := by rw [huu, one_mul, one_mul]
        calc TS k (Z.erase a) (fun _ => u) u
            = k u u * k u u * TS k (Z.erase a) (fun _ => u) u := h1u.symm
          _ ≤ _ := by
            refine Finset.single_le_sum (f := fun w => k u w * k w u *
              TS k (Z.erase a) (fun _ => u) w) (fun w _ => ?_) (Finset.mem_univ u)
            have h2 : 0 ≤ TS k (Z.erase a) (fun _ => u) w := TS_nonneg hk _ _ _
            exact mul_nonneg (mul_nonneg (hk _ _) (hk _ _)) h2
      have hcard : (Z.erase a).card < n := by
        rw [Finset.card_erase_of_mem ha]
        have := Finset.card_pos.mpr hne'
        omega
      exact le_trans (ih _ hcard _ rfl h2') (le_trans hterm hsplit)



/-! ### The split strengthening of the branch decomposition -/

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The branch decomposition with the split containing a prescribed basepoint. -/
theorem exists_branch_split_mem (y : α → V) (hconn : ∀ a, Conn ends s v (y a))
    (hne : ∃ a b : α, y a ≠ y b) (a₀ : α) :
    ∃ (w : V) (A : Finset α) (W0 WA WB : Finset E),
      a₀ ∈ A ∧ A.Nonempty ∧ Aᶜ.Nonempty ∧ W0 ⊆ s ∧ WA ⊆ s ∧ WB ⊆ s ∧
      Disjoint W0 WA ∧ Disjoint W0 WB ∧ Disjoint WA WB ∧
      Conn ends W0 v w ∧
      (∀ a ∈ A, Conn ends WA w (y a)) ∧
      (∀ b ∈ Aᶜ, Conn ends WB w (y b)) := by
  classical
  obtain ⟨w, A, W0, WA, WB, hneA, hcA, hW0, hWA, hWB, hd1, hd2, hd3, hconn0, hconnA, hconnB⟩ :=
    exists_branch_split y hconn hne
  by_cases ha : a₀ ∈ A
  · exact ⟨w, A, W0, WA, WB, ha, hneA, hcA, hW0, hWA, hWB, hd1, hd2, hd3, hconn0,
      hconnA, hconnB⟩
  · refine ⟨w, Aᶜ, W0, WB, WA, Finset.mem_compl.mpr ha, hcA,
      (by simpa using hneA), hW0, hWB, hWA,
      hd2, hd1, disjoint_comm.mp hd3, hconn0, hconnB, ?_⟩
    intro b hb
    rw [compl_compl] at hb
    exact hconnA b hb

end PercLib.CriticalLRP.TreeGraph
