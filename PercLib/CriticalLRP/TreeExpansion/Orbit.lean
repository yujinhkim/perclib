/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
The orbit count behind the phrase "isomorphism classes" in (I.2.2) of

  T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
  arXiv:2508.18807v1, Section I.2.1, p. 22.

`RTree` is a type of *plane* (ordered) trees. `RTree.swapFiber t` is the finite set of
plane trees obtained from `t` by independently swapping the two children at some vertices;
its elements are exactly the plane representatives of the non-plane tree underlying `t`.

The main result, `RTree.card_swapFiber`, is the orbit count: for a tree with distinct leaf
labels,

  `#(swapFiber t) = 2^(#leaves t − 1)`,

i.e. a non-plane tree with `p` distinctly labelled leaves has exactly `2^(p−1)` plane
orderings. Combined with `RTree.card_LT_fin_le` this yields the paper's count
`#{non-plane trees with p labelled leaves} ≤ (2p−3)!!`.
-/
module

public import Mathlib
public import PercLib.CriticalLRP.TreeExpansion.Count

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

set_option autoImplicit false

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion

namespace RTree

variable {α : Type*} [DecidableEq α]

/-- The plane trees obtained from `t` by independently swapping children. -/
def swapFiber : RTree α → Finset (RTree α)
  | leaf a => {leaf a}
  | node l r =>
      (((swapFiber l).product (swapFiber r)).image (fun p => node p.1 p.2)) ∪
        (((swapFiber l).product (swapFiber r)).image (fun p => node p.2 p.1))

@[simp] theorem swapFiber_leaf (a : α) : swapFiber (leaf a) = {leaf a} := rfl

theorem swapFiber_node (l r : RTree α) :
    swapFiber (node l r) =
      (((swapFiber l).product (swapFiber r)).image (fun p => node p.1 p.2)) ∪
        (((swapFiber l).product (swapFiber r)).image (fun p => node p.2 p.1)) := rfl

/-- Swapping children preserves the multiset of leaf labels. -/
theorem perm_of_mem_swapFiber {t : RTree α} :
    ∀ {t' : RTree α}, t' ∈ swapFiber t → List.Perm t'.leaves t.leaves := by
  induction t with
  | leaf a =>
      intro t' h
      rw [swapFiber_leaf, Finset.mem_singleton] at h
      rw [h]
  | node l r ihl ihr =>
      intro t' h
      rw [swapFiber_node] at h
      rcases Finset.mem_union.mp h with h | h
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
        obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
        rw [leaves_node, leaves_node]
        exact (ihl h1).append (ihr h2)
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
        obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
        rw [leaves_node, leaves_node]
        exact ((ihr h2).append (ihl h1)).trans (List.perm_append_comm)

/-- Two disjoint nonempty lists cannot be permutations of each other. -/
theorem not_perm_of_disjoint {l r : List α} (hl : l ≠ []) (hd : l.Disjoint r) :
    ¬ r.Perm l := by
  intro hp
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil l hl
  have har : a ∈ r := hp.mem_iff.mpr ha
  exact (List.disjoint_left.mp hd ha har)

/-- **The orbit count.** A tree with distinct leaf labels has exactly `2^(#leaves − 1)`
plane representatives. -/
theorem card_swapFiber : ∀ (t : RTree α), t.leaves.Nodup →
    (swapFiber t).card = 2 ^ (t.numLeaves - 1) := by
  intro t
  induction t with
  | leaf a =>
      intro _
      simp
  | node l r ihl ihr =>
      intro hnd
      rw [leaves_node] at hnd
      obtain ⟨hl, hr, hdisj⟩ := List.nodup_append.mp hnd
      have hcl : (swapFiber l).card = 2 ^ (l.numLeaves - 1) := ihl hl
      have hcr : (swapFiber r).card = 2 ^ (r.numLeaves - 1) := ihr hr
      have hinjA : Function.Injective (fun p : RTree α × RTree α => node p.1 p.2) := by
        intro p q hpq
        simp only [node.injEq] at hpq
        exact Prod.ext hpq.1 hpq.2
      have hinjB : Function.Injective (fun p : RTree α × RTree α => node p.2 p.1) := by
        intro p q hpq
        simp only [node.injEq] at hpq
        exact Prod.ext hpq.2 hpq.1
      have hcardA : (((swapFiber l).product (swapFiber r)).image (fun p => node p.1 p.2)).card
          = (swapFiber l).card * (swapFiber r).card := by
        rw [Finset.card_image_of_injective _ hinjA]
        exact Finset.card_product _ _
      have hcardB : (((swapFiber l).product (swapFiber r)).image (fun p => node p.2 p.1)).card
          = (swapFiber l).card * (swapFiber r).card := by
        rw [Finset.card_image_of_injective _ hinjB]
        exact Finset.card_product _ _
      have hdisjAB : Disjoint
          (((swapFiber l).product (swapFiber r)).image (fun p => node p.1 p.2))
          (((swapFiber l).product (swapFiber r)).image (fun p => node p.2 p.1)) := by
        rw [Finset.disjoint_left]
        intro t' h1 h2
        obtain ⟨p, hp, hpv⟩ := Finset.mem_image.mp h1
        obtain ⟨q, hq, hqv⟩ := Finset.mem_image.mp h2
        obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
        obtain ⟨hq1, hq2⟩ := Finset.mem_product.mp hq
        -- `node p.1 p.2 = t' = node q.2 q.1`
        have heq : node p.1 p.2 = node q.2 q.1 := by rw [hpv, hqv]
        simp only [node.injEq] at heq
        obtain ⟨h1eq, h2eq⟩ := heq
        have hperm1 : List.Perm p.1.leaves l.leaves := perm_of_mem_swapFiber hp1
        have hperm2 : List.Perm q.2.leaves r.leaves := perm_of_mem_swapFiber hq2
        rw [h1eq] at hperm1
        have hlne : l.leaves ≠ [] := by
          intro h0
          have := numLeaves_pos l
          simp only [numLeaves, h0, List.length_nil] at this
          omega
        obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil l.leaves hlne
        have ha2 : a ∈ q.2.leaves := hperm1.symm.mem_iff.mp ha
        have har : a ∈ r.leaves := hperm2.mem_iff.mp ha2
        exact (hdisj a ha a har) rfl
      rw [swapFiber_node, Finset.card_union_of_disjoint hdisjAB, hcardA, hcardB, hcl, hcr,
        numLeaves_node]
      have h1 : 0 < l.numLeaves := numLeaves_pos l
      have h2 : 0 < r.numLeaves := numLeaves_pos r
      have hexp : (l.numLeaves - 1) + (r.numLeaves - 1) + 1 = l.numLeaves + r.numLeaves - 1 := by
        omega
      calc 2 ^ (l.numLeaves - 1) * 2 ^ (r.numLeaves - 1)
            + 2 ^ (l.numLeaves - 1) * 2 ^ (r.numLeaves - 1)
          = 2 * (2 ^ (l.numLeaves - 1) * 2 ^ (r.numLeaves - 1)) := by ring
        _ = 2 ^ ((l.numLeaves - 1) + (r.numLeaves - 1) + 1) := by
            rw [pow_succ]
            ring
        _ = 2 ^ (l.numLeaves + r.numLeaves - 1) := by rw [hexp]

end RTree

end PercLib.CriticalLRP.TreeExpansion
