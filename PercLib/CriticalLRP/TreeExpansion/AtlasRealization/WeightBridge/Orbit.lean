/- Integrated from independently rebuilt Ultramath work.
Production base 50c2eed0682a7e1b078ae771dbef463ebe00701d.
Scratch source: repository-root .ultramath/.
-/

/-
Orbit facts for the child-swap action, and the precise gap in the shape count.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.WeightBridge.Moment
public import PercLib.CriticalLRP.TreeExpansion.Orbit

/-!
# The child-swap orbit: what the plane multiplicity is

`RTree.swapFiber t` (`TreeExpansion.Orbit`) is the finite set of plane trees obtained from `t`
by independently exchanging the two children at vertices — one full orbit of the child-swap
action.  `RTree.card_swapFiber` says a tree with distinct leaf labels has `2^(#leaves-1)` plane
representatives.

This file proves that the tree weight is constant on an orbit (`wtL_eq_of_mem_swapFiber`), so a
union bound over the plane family charges each non-plane diagram `2^(p-1)` times: the factor
`2^(p-1)` in `prob_conn_le_two_pow_mul_treeSum` is a pure over-count of the index set, not a
weaker bound on any individual diagram.

## The one missing lemma

To remove the factor one must take the union bound over **one representative per orbit** rather
than over all plane shapes.  By the argument above this needs exactly one further input:

  if `t' ∈ RTree.swapFiber t` and the atlas of `t` is realized inside `ω`, then the atlas of `t'`
  is realized inside `ω` as well — indeed with the *same* witness sets, since exchanging the
  children of a vertex only exchanges which child is the `false` / `true` child, and the atlas
  edges of `t` and `t'` can be matched so that the unordered pair of endpoints of each edge is
  unchanged (`Conn` is symmetric).

Formally that is a bijection `t.IPos ≃ t'.IPos` together with, for every atlas edge, the matching
atlas edge of the other tree having the same two ends; `IsRealization` then transports verbatim
(subset, disjointness and connectivity are all invariant under the matching).  With that,
`⋃ φ, DiagEvent t φ = ⋃ φ, DiagEvent t' φ`, hence the sums
`∑ φ, P(DiagEvent t φ)` agree on an orbit, and the union bound over representatives gives
`2^(-(p-1))` times the plane sum — i.e. `treeSum` and the source constant.  Neither the position
bijection nor the transport is in production, and this file does not construct it.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace PercLib.CriticalLRP.TreeExpansion

namespace RTree

variable {α : Type*} [DecidableEq α]

/-- Every tree is in its own swap orbit. -/
theorem swapFiber_self (t : RTree α) : t ∈ swapFiber t := by
  induction t with
  | leaf a => simp
  | node l r ihl ihr =>
      rw [swapFiber_node]
      refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(l, r), ?_, rfl⟩)
      exact Finset.mem_product.mpr ⟨ihl, ihr⟩

/-- The child-swap relation is symmetric. -/
theorem swapFiber_symm : ∀ {t t' : RTree α}, t' ∈ swapFiber t → t ∈ swapFiber t'
  | leaf a, t', h => by
      rw [swapFiber_leaf, Finset.mem_singleton] at h
      subst h
      exact swapFiber_self _
  | node l r, t', h => by
      rw [swapFiber_node] at h
      rcases Finset.mem_union.mp h with h | h
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
        obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
        rw [swapFiber_node]
        refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(l, r), ?_, rfl⟩)
        exact Finset.mem_product.mpr ⟨swapFiber_symm h1, swapFiber_symm h2⟩
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
        obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
        rw [swapFiber_node]
        refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(r, l), ?_, rfl⟩)
        exact Finset.mem_product.mpr ⟨swapFiber_symm h2, swapFiber_symm h1⟩

/-- Swapping the two children of a node exchanges the two images. -/
theorem image_node_prod_comm (S T : Finset (RTree α)) :
    ((S.product T).image (fun p : RTree α × RTree α => node p.1 p.2))
      = ((T.product S).image (fun p : RTree α × RTree α => node p.2 p.1)) := by
  ext u
  constructor
  · intro hu
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
    exact Finset.mem_image.mpr ⟨(p.2, p.1), Finset.mem_product.mpr ⟨h2, h1⟩, rfl⟩
  · intro hu
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
    exact Finset.mem_image.mpr ⟨(p.2, p.1), Finset.mem_product.mpr ⟨h2, h1⟩, rfl⟩

/-- `swapFiber` is constant on an orbit: two plane representatives of the same non-plane tree
have the same orbit. -/
theorem swapFiber_congr : ∀ {t t' : RTree α}, t' ∈ swapFiber t → swapFiber t' = swapFiber t
  | leaf a, t', h => by
      rw [swapFiber_leaf, Finset.mem_singleton] at h
      subst h
      rfl
  | node l r, t', h => by
      rw [swapFiber_node] at h
      rcases Finset.mem_union.mp h with h | h
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
        obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
        show swapFiber (node p.1 p.2) = swapFiber (node l r)
        rw [swapFiber_node, swapFiber_node, swapFiber_congr h1, swapFiber_congr h2]
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
        obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
        show swapFiber (node p.2 p.1) = swapFiber (node l r)
        rw [swapFiber_node, swapFiber_node, swapFiber_congr h1, swapFiber_congr h2,
          image_node_prod_comm (swapFiber r) (swapFiber l),
          image_node_prod_comm (swapFiber l) (swapFiber r), Finset.union_comm]

end RTree

/-- The tree weight is constant on a child-swap orbit.  Hence all `2^(p-1)` plane
representatives of one non-plane diagram contribute the same value to the union bound, and the
plane sum is exactly `2^(p-1)` times the sum over isomorphism classes. -/
theorem wtL_eq_of_mem_swapFiber {α : Type*} [DecidableEq α] {V : Type*} [Fintype V]
    (k : V → V → ℝ) (t : RTree α) :
    ∀ {t' : RTree α}, t' ∈ RTree.swapFiber t → ∀ (y : α → V) (v : V),
      RTree.wtL k t' y v = RTree.wtL k t y v := by
  induction t with
  | leaf a =>
      intro t' h y v
      rw [RTree.swapFiber_leaf, Finset.mem_singleton] at h
      subst h
      rfl
  | node l r ihl ihr =>
      intro t' h y v
      rw [RTree.swapFiber_node] at h
      rcases Finset.mem_union.mp h with h | h
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
        obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
        rw [RTree.wtL_node, RTree.wtL_node]
        exact Finset.sum_congr rfl fun w _ => by rw [ihl h1 y w, ihr h2 y w]
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
        obtain ⟨h1, h2⟩ := Finset.mem_product.mp hp
        rw [RTree.wtL_node, RTree.wtL_node]
        exact Finset.sum_congr rfl fun w _ => by
          rw [ihl h1 y w, ihr h2 y w]
          ac_rfl

end PercLib.CriticalLRP.TreeExpansion
