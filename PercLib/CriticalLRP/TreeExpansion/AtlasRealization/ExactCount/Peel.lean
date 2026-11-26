/- Independently reviewed exact-count proof from smwwtnhaw/m1, with a
strict fresh rebuild and standard-axiom audit at the current integration bank. -/
/-
Independent UltraMath work, swarm `smwwtnhaw`, member `m1`.
Production base `4c53bb5a8e76a4358a426adf71169b916b90f51f` (read-only package
`.scratch/critical-lrp-orchestration`), Lean 4.35.0. Nothing outside this directory is modified.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.ExactCount.Defs

/-!
# `peel` is the inverse of a fresh-leaf insertion

This file proves the correctness of the canonical peel `RTree.peel` of `OrbitCount/Defs.lean`:

* `RTree.peel_insertAt` : `peel (insertAt Sum.inl (Sum.inr ()) b t p) = (t, posPath t p, b)`;
* `RTree.posPath_inj` : a vertex is determined by its direction chain;
* `RTree.insertMap_injective` : the insertion map `insertMap` of `TreeExpansion/Count.lean` is
  injective.

Production proves only surjectivity (`RTree.insertMap_surjective`, giving the inequality
`RTree.card_LT_sum`); injectivity is the missing half of the exact plane-tree count, and the
counting consequences are in `OrbitCount/Exact.lean`.

The proof of `peel_insertAt` is by induction on the source tree `t` only: the image of an
insertion at a left descendant is a node whose left child is again an insertion image, one step to
the left; at a right descendant one step to the right; and at the root it is
`node (leaf (inr ())) _` or `node _ (leaf (inr ()))`, where the fresh leaf is peeled off and its
parent suppressed.  No case split between the two source trees and the two vertices is needed.
-/

set_option autoImplicit false

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion

namespace RTree

/-! ### The direction chains -/

section PosPath

variable {α : Type*}

@[simp] theorem posPath_leaf (a : α) (p : Pos (leaf a)) : posPath (leaf a) p = [] := by
  cases p
  rfl

@[simp] theorem posPath_node_inl (l r : RTree α) (p : Pos l) :
    posPath (node l r) (Sum.inl p) = false :: posPath l p := rfl

@[simp] theorem posPath_node_inr_inl (l r : RTree α) (p : Pos r) :
    posPath (node l r) (Sum.inr (Sum.inl p)) = true :: posPath r p := rfl

@[simp] theorem posPath_node_root (l r : RTree α) (u : PUnit) :
    posPath (node l r) (Sum.inr (Sum.inr u)) = [] := rfl

/-- A vertex of a tree is determined by its direction chain. -/
theorem posPath_inj : (t : RTree α) → ∀ p q : Pos t, posPath t p = posPath t q → p = q
  | leaf _, ⟨⟩, ⟨⟩, _ => rfl
  | node l r, Sum.inl p, Sum.inl q, h => by
      rw [posPath_node_inl, posPath_node_inl] at h
      rw [posPath_inj l p q (List.cons.inj h).2]
  | node l r, Sum.inl p, Sum.inr (Sum.inl q), h => by
      rw [posPath_node_inl, posPath_node_inr_inl] at h
      exact absurd h (by simp)
  | node l r, Sum.inl p, Sum.inr (Sum.inr u), h => by
      rw [posPath_node_inl, posPath_node_root] at h
      exact absurd h (by simp)
  | node l r, Sum.inr (Sum.inl p), Sum.inl q, h => by
      rw [posPath_node_inl, posPath_node_inr_inl] at h
      exact absurd h (by simp)
  | node l r, Sum.inr (Sum.inl p), Sum.inr (Sum.inl q), h => by
      rw [posPath_node_inr_inl, posPath_node_inr_inl] at h
      rw [posPath_inj r p q (List.cons.inj h).2]
  | node l r, Sum.inr (Sum.inl p), Sum.inr (Sum.inr u), h => by
      rw [posPath_node_inr_inl, posPath_node_root] at h
      exact absurd h (by simp)
  | node l r, Sum.inr (Sum.inr u), Sum.inl q, h => by
      rw [posPath_node_inl, posPath_node_root] at h
      exact absurd h (by simp)
  | node l r, Sum.inr (Sum.inr u), Sum.inr (Sum.inl q), h => by
      rw [posPath_node_inr_inl, posPath_node_root] at h
      exact absurd h (by simp)
  | node l r, Sum.inr (Sum.inr u), Sum.inr (Sum.inr v), _ =>
      congrArg (fun w : PUnit => (Sum.inr (Sum.inr w) : Pos (node l r))) (Subsingleton.elim u v)

end PosPath

/-! ### The fresh label -/

section Count

variable {α : Type*} [DecidableEq α]

/-- A relabelled tree carries no fresh label. -/
@[simp] theorem count_inr_mapLabel_inl (t : RTree α) :
    (t.mapLabel (Sum.inl : α → α ⊕ PUnit)).leaves.count (Sum.inr ⟨⟩) = 0 := by
  rw [leaves_mapLabel]
  exact count_inr_map_inl t.leaves

/-- An inserted tree carries the fresh label exactly once. -/
theorem count_inr_insertAt (t : RTree α) (p : Pos t) (b : Bool) :
    (insertAt (Sum.inl : α → α ⊕ PUnit) (Sum.inr ⟨⟩) b t p).leaves.count (Sum.inr ⟨⟩)
      = 1 := by
  have h := leaves_insertAt (Sum.inl : α → α ⊕ PUnit) (Sum.inr ⟨⟩) b t p
  rw [h.count_eq]
  simp [count_inr_map_inl]

end Count

/-! ### The leaf count -/

section NumLeaves

variable {α : Type*}

/-- An inserted tree has one leaf more than its source. -/
theorem numLeaves_insertAt (t : RTree α) (p : Pos t) (b : Bool) :
    (insertAt (Sum.inl : α → α ⊕ PUnit) (Sum.inr ⟨⟩) b t p).numLeaves
      = t.numLeaves + 1 := by
  have h := leaves_insertAt (Sum.inl : α → α ⊕ PUnit) (Sum.inr ⟨⟩) b t p
  change (insertAt (Sum.inl : α → α ⊕ PUnit) (Sum.inr ⟨⟩) b t p).leaves.length
      = t.leaves.length + 1
  rw [h.length_eq]
  simp

end NumLeaves

/-! ### Forgetting the fresh label -/

section Strip

variable {α : Type*} [Nonempty α]

/-- Forgetting the fresh label inverts the relabelling `Sum.inl`. -/
theorem stripInr_mapLabel_inl (t : RTree α) :
    stripInr (t.mapLabel (Sum.inl : α → α ⊕ PUnit)) = t := by
  rw [stripInr, mapLabel_mapLabel]
  have h : (fun a => stripInrLabel (Sum.inl a : α ⊕ PUnit)) = id := by funext a; rfl
  rw [h, mapLabel_id]

@[simp] theorem stripInr_node (u v : RTree (α ⊕ PUnit)) :
    stripInr (u.node v) = (stripInr u).node (stripInr v) := rfl

@[simp] theorem stripInr_leaf_inl (a : α) :
    stripInr (leaf (Sum.inl a) : RTree (α ⊕ PUnit)) = leaf a := rfl

end Strip

/-! ### The equations of `peel` -/

section Peel

variable {α : Type*} [DecidableEq α] [Nonempty α]

/-- The defining equation of `peel` at a node. -/
theorem peel_node (l r : RTree (α ⊕ PUnit)) :
    peel (node l r) =
      (if 0 < l.leaves.count (Sum.inr ⟨⟩) then
        (if l.numLeaves = 1 then (stripInr r, [], true)
         else ((peel l).1.node (stripInr r), false :: (peel l).2.1, (peel l).2.2))
       else if 0 < r.leaves.count (Sum.inr ⟨⟩) then
        (if r.numLeaves = 1 then (stripInr l, [], false)
         else ((stripInr l).node (peel r).1, true :: (peel r).2.1, (peel r).2.2))
       else (defaultTree, [], false)) := rfl

/-- `peel` at a node whose left subtree is the fresh leaf: the insertion was at the root. -/
theorem peel_node_left_fresh (v : RTree (α ⊕ PUnit)) :
    peel ((leaf (Sum.inr ⟨⟩)).node v) = (stripInr v, [], true) := by
  rw [peel_node]
  simp

/-- `peel` at a node whose left subtree contains the fresh label and is not itself the fresh
leaf: the insertion was inside the left subtree, one step down. -/
theorem peel_node_left (u v : RTree (α ⊕ PUnit)) (h1 : 0 < u.leaves.count (Sum.inr ⟨⟩))
    (h2 : ¬ u.numLeaves = 1) :
    peel (u.node v) = ((peel u).1.node (stripInr v), false :: (peel u).2.1, (peel u).2.2) := by
  rw [peel_node]
  simp [h1, h2]

/-- `peel` at a node whose right subtree is the fresh leaf: the insertion was at the root. -/
theorem peel_node_right_fresh (u : RTree (α ⊕ PUnit))
    (h1 : ¬ 0 < u.leaves.count (Sum.inr ⟨⟩)) :
    peel (u.node (leaf (Sum.inr ⟨⟩))) = (stripInr u, [], false) := by
  rw [peel_node]
  simp [h1]

/-- `peel` at a node whose right subtree contains the fresh label and is not itself the fresh
leaf: the insertion was inside the right subtree, one step down. -/
theorem peel_node_right (u v : RTree (α ⊕ PUnit)) (h1 : ¬ 0 < u.leaves.count (Sum.inr ⟨⟩))
    (h2 : 0 < v.leaves.count (Sum.inr ⟨⟩)) (h3 : ¬ v.numLeaves = 1) :
    peel (u.node v) = ((stripInr u).node (peel v).1, true :: (peel v).2.1, (peel v).2.2) := by
  rw [peel_node]
  simp [h1, h2, h3]

/-! ### Correctness of the peel -/

/-- **The peel inverts an insertion.**  Recovering the tree, the direction chain of the vertex and
the side from the image of one insertion gives back exactly the data that was inserted. -/
theorem peel_insertAt (t : RTree α) :
    ∀ (p : Pos t) (b : Bool),
      peel (insertAt (Sum.inl : α → α ⊕ PUnit) (Sum.inr ⟨⟩) b t p)
        = (t, posPath t p, b) := by
  induction t with
  | leaf a =>
      intro p b
      cases p
      cases b
      · change peel ((leaf (Sum.inl a)).node (leaf (Sum.inr ⟨⟩)))
          = (leaf a, posPath (leaf a) ⟨⟩, false)
        rw [peel_node_right_fresh _ (by simp), stripInr_leaf_inl]
        rfl
      · change peel ((leaf (Sum.inr ⟨⟩)).node (leaf (Sum.inl a)))
          = (leaf a, posPath (leaf a) ⟨⟩, true)
        rw [peel_node_left_fresh, stripInr_leaf_inl]
        rfl
  | node l r ihl ihr =>
      intro p b
      cases p with
      | inl p0 =>
          change peel ((insertAt (Sum.inl : α → α ⊕ PUnit) (Sum.inr ⟨⟩) b l p0).node
              (r.mapLabel (Sum.inl : α → α ⊕ PUnit)))
            = (l.node r, posPath (l.node r) (Sum.inl p0), b)
          rw [peel_node_left _ _
            (by rw [count_inr_insertAt]; norm_num)
            (by rw [numLeaves_insertAt]; have h := numLeaves_pos l; omega),
            ihl p0 b]
          dsimp only
          rw [stripInr_mapLabel_inl]
          rfl
      | inr p' =>
          cases p' with
          | inl p0 =>
              change peel ((l.mapLabel (Sum.inl : α → α ⊕ PUnit)).node
                  (insertAt (Sum.inl : α → α ⊕ PUnit) (Sum.inr ⟨⟩) b r p0))
                = (l.node r, posPath (l.node r) (Sum.inr (Sum.inl p0)), b)
              rw [peel_node_right _ _
                (by rw [count_inr_mapLabel_inl]; simp)
                (by rw [count_inr_insertAt]; norm_num)
                (by rw [numLeaves_insertAt]; have h := numLeaves_pos r; omega),
                ihr p0 b]
              dsimp only
              rw [stripInr_mapLabel_inl]
              rfl
          | inr u =>
              cases b
              · change peel (((l.mapLabel (Sum.inl : α → α ⊕ PUnit)).node
                    (r.mapLabel (Sum.inl : α → α ⊕ PUnit))).node (leaf (Sum.inr ⟨⟩)))
                  = (l.node r, posPath (l.node r) (Sum.inr (Sum.inr u)), false)
                rw [peel_node_right_fresh _ (by simp),
                  stripInr_node, stripInr_mapLabel_inl, stripInr_mapLabel_inl]
                rfl
              · change peel ((leaf (Sum.inr ⟨⟩)).node
                    ((l.mapLabel (Sum.inl : α → α ⊕ PUnit)).node
                      (r.mapLabel (Sum.inl : α → α ⊕ PUnit))))
                  = (l.node r, posPath (l.node r) (Sum.inr (Sum.inr u)), true)
                rw [peel_node_left_fresh, stripInr_node, stripInr_mapLabel_inl,
                  stripInr_mapLabel_inl]
                rfl

end Peel

/-! ### Injectivity of the insertion map -/

variable {α : Type*} [DecidableEq α] [Nonempty α] [Fintype α]

/-- **`insertMap` is injective.**  The plane tree, the vertex and the side are recovered from the
image by `peel`, `posPath_inj` and the side component of the peel. -/
theorem insertMap_injective : Function.Injective (insertMap (α := α)) := by
  rintro ⟨⟨t, ht⟩, p, b⟩ ⟨⟨t', ht'⟩, p', b'⟩ h
  have h' : insertAt (Sum.inl : α → α ⊕ PUnit) (Sum.inr ⟨⟩) b t p
      = insertAt (Sum.inl : α → α ⊕ PUnit) (Sum.inr ⟨⟩) b' t' p' := congrArg Subtype.val h
  have hp : peel (insertAt (Sum.inl : α → α ⊕ PUnit) (Sum.inr ⟨⟩) b t p)
      = peel (insertAt (Sum.inl : α → α ⊕ PUnit) (Sum.inr ⟨⟩) b' t' p') := by rw [h']
  rw [peel_insertAt, peel_insertAt] at hp
  have h1 : t = t' := congrArg (fun x : RTree α × List Bool × Bool => x.1) hp
  have h2 : posPath t p = posPath t' p' :=
    congrArg (fun x : RTree α × List Bool × Bool => x.2.1) hp
  have h3 : b = b' := congrArg (fun x : RTree α × List Bool × Bool => x.2.2) hp
  subst h1
  have hpp : p = p' := posPath_inj t p p' h2
  subst hpp
  subst h3
  exact Sigma.ext (Subtype.ext rfl) (HEq.refl _)

end RTree

end PercLib.CriticalLRP.TreeExpansion
