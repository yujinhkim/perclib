/- Independently reviewed exact-count proof from smwwtnhaw/m1, with a
strict fresh rebuild and standard-axiom audit at the current integration bank. -/
/-
Independent UltraMath work, swarm `smwwtnhaw`, member `m1`.
Production base `4c53bb5a8e76a4358a426adf71169b916b90f51f` (read-only package
`.scratch/critical-lrp-orchestration`), Lean 4.35.0. Nothing outside this directory is modified.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.OrbitCount.Partition
public import PercLib.CriticalLRP.TreeExpansion.Moments

/-!
# Definitions for the exact child-swap orbit count

The count of `RTree.swapOrbits (Fin p)` is `Fintype.card (RTree.LT (Fin p)) / 2 ^ (p - 1)`
(production `RTree.card_swapOrbits_mul`, `RTree.card_swapOrbits_eq_div`), so the exact orbit count
needs the *exact* number of fully labelled plane trees.  Production
(`TreeExpansion/Count.lean`) has the insertion map

`RTree.insertMap : (Σ t : RTree.LT α, Pos t.val × Bool) → RTree.LT (α ⊕ PUnit)`

and proves only that it is surjective (`RTree.insertMap_surjective`), which gives the inequality
`RTree.card_LT_sum`.  Equality needs injectivity, i.e. recovery of `(t, p, side)` from the image.

This file contains the definitions of the canonical *peel*: the explicit inverse of one insertion
step, i.e. of the map `insertAt (Sum.inl) (Sum.inr ()) side t p`.  Peeling does not descend into a
case split on the two trees and the two positions at once (36 cases); it walks down the *image*
tree along the unique fresh label and rebuilds the source tree on the way up.

* `stripInrLabel` — a default label of `α`, used to forget the fresh label `Sum.inr ⟨⟩`;
* `stripInr` — relabel a tree over `α ⊕ PUnit` by `stripInrLabel`; on trees avoiding the fresh
  label (in particular on `t.mapLabel Sum.inl`) this inverts `Sum.inl`;
* `defaultTree` — a junk tree, used as the value of `peel` off its domain;
* `posPath` — the direction chain from the root to a vertex, a *non-dependent* shadow of `Pos t`
  (`[]` at the root, `false :: _` in the left subtree, `true :: _` in the right subtree);
* `peel` — the canonical peel: from a tree over `α ⊕ PUnit` recover the source tree over `α`,
  the direction chain of the vertex the leaf hangs from, and the side of the leaf.

`peel` returns a *non-dependent* type `RTree α × List Bool × Bool`, so the correctness statement
`RTree.peel_insertAt` is an equality of triples and injectivity of `insertMap` needs no dependent
transport.  All theorems are in `OrbitCount/Peel.lean`; this file only defines and compiles
independently.
-/

set_option autoImplicit false

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion

namespace RTree

variable {α : Type*}

/-- A default label of `α`, used to forget the fresh label `Sum.inr ⟨⟩`. -/
noncomputable def stripInrLabel [Nonempty α] : α ⊕ PUnit → α :=
  Sum.elim id fun _ => Classical.arbitrary α

/-- The junk tree, returned by `peel` on inputs which are not of the form
`insertAt Sum.inl (Sum.inr ()) side t p`. -/
noncomputable def defaultTree [Nonempty α] : RTree α :=
  leaf (Classical.arbitrary α)

/-- **Forget the fresh label.**  Relabel a tree over `α ⊕ PUnit` by `stripInrLabel`.  On trees
whose labels avoid `Sum.inr ⟨⟩` — in particular on `t.mapLabel Sum.inl` — this is the inverse
of the relabelling `Sum.inl`.  On the fresh leaf itself the function is junk; that is what makes
it total. -/
noncomputable def stripInr [Nonempty α] (t : RTree (α ⊕ PUnit)) : RTree α :=
  t.mapLabel stripInrLabel

variable [DecidableEq α]

/-- **The direction chain to a vertex.**  The root corresponds to the empty chain, a vertex of the
left subtree to `false :: _`, and a vertex of the right subtree to `true :: _`.  This is the
non-dependent shadow of `Pos t` used by `peel`. -/
def posPath : (t : RTree α) → Pos t → List Bool
  | leaf _, ⟨⟩ => []
  | node l _, Sum.inl p => false :: posPath l p
  | node _ r, Sum.inr (Sum.inl p) => true :: posPath r p
  | node _ _, Sum.inr (Sum.inr _) => []

/-- **Peel the fresh leaf.**  From a tree over `α ⊕ PUnit` recover the source tree over `α`, the
direction chain of the vertex the fresh leaf hangs from, and the side of the fresh leaf.  The
result is junk when the fresh label does not occur exactly once, or occurs at a place where its
parent cannot be suppressed; on the image of `insertAt Sum.inl (Sum.inr ())` it is exact
(`RTree.peel_insertAt`).

If the fresh label sits in the left subtree and the left subtree is the fresh leaf itself, then the
insertion was at the root with side `true`; if it sits in the left subtree and that subtree is a
node, the insertion was inside it, one step to the left.  The right cases are symmetric. -/
noncomputable def peel [Nonempty α] : RTree (α ⊕ PUnit) → RTree α × List Bool × Bool
  | leaf _ => (defaultTree, [], false)
  | node l r =>
      if 0 < l.leaves.count (Sum.inr ⟨⟩) then
        if l.numLeaves = 1 then (stripInr r, [], true)
        else (node (peel l).1 (stripInr r), false :: (peel l).2.1, (peel l).2.2)
      else if 0 < r.leaves.count (Sum.inr ⟨⟩) then
        if r.numLeaves = 1 then (stripInr l, [], false)
        else (node (stripInr l) (peel r).1, true :: (peel r).2.1, (peel r).2.2)
      else (defaultTree, [], false)

end RTree

end PercLib.CriticalLRP.TreeExpansion
