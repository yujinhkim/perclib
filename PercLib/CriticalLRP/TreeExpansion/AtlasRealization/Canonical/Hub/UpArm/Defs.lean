/-
Root-versus-parent analysis of the up arm of `CanonAtlas.hubStarJoint`.

Prepared from `.ultramath/smwx4z71g/m1/HubUpArm` at production revision
`5e579c30ee2c5caa2d151372f1929efd8ed587fb`; independently rebuilt and integrated by the
coordinator with production-qualified imports.  This file holds the *new definitions* of the
layer; every proof is in the sibling modules `UpArm.lean` and `ParentIncl.lean`.

## The object

`CanonAtlas.hubStarJoint y c t φ v` is the joint (disjoint-occurrence) event of the three atlas
edges of the 3-star of the internal vertex `v` of a shape `t`.  The three slots are

* the two *down* edges `Sum.inl (v, false)`, `Sum.inl (v, true)` of `v`, whose source is `φ v` and
  whose destinations are the two child positions `childPos t φ y v b`;
* the *up* edge `RTree.upEdge` of `v`, whose destination is `φ v` but whose **source is not**
  `φ v`: it is the root leaf vertex `c` when `v` is the root of `t`, and the parent's position
  `φ (parent v)` otherwise (production `Real.src_upEdge`, `Real.upEdge_dstPos`).

## What is defined

* `IsRootIpos t v` -- `v` is the root internal vertex, expressed on the address `pathOf t v`.
* `parentIPos t v h` -- the **parent internal vertex** of a non-root `v`, i.e. the internal vertex
  at the address `(pathOf t v).1.dropLast`.  This is a genuine `t.IPos`, not an alias: it is the
  vertex whose own down arm the up arm of `v` is.
* `hubUpSrc t φ c v` -- the exact source of the up arm of the 3-star of `v`: `c` at the root and
  `φ (parentIPos t v h)` elsewhere.  It is a *definition* of the far end, never an identification
  with `φ v`; `hubUpSrc_ne_dst` and its variants in `UpArm.lean` show when the two are distinct.
* `hubUpEdge t v` -- the up arm as a realized atlas edge `AEdge t` (the `atlasEdgeEquiv` image of
  `RTree.upEdge`), so that its slot, its two ends and its membership in `hubStarAEdges t v` can be
  named.
* `hubFar t φ y c v : Fin 3 → V` -- the three far ends of the 3-star of `v` as seen from the hub
  position `φ v`, in the order `(child false, child true, up-arm source)`.  The third entry keeps
  the root/parent distinction of `hubUpSrc`; no generic `φ` alias is used.
* `hubThreePoint y c t φ v` -- the **parent-aware joint three-point function at the hub**: one
  configuration connecting the hub position `φ v` to all three far ends `hubFar`.  It is an
  intersection of three connection events (a joint value), deliberately neither a product of
  two-point factors nor a disjoint occurrence.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Canonical.Hub.Evaluation.Defs

/-!
# Definitions: parent of a hub, source of its up arm, three far ends, parent-aware three-point

Definitions only.
-/

@[expose] public section

open PercLib.CriticalLRP (Config connSet)
open PercLib.CriticalLRP.TreeExpansion (RTree)
open PercLib.CriticalLRP.TreeExpansion.Real (AEdge atlasEdgeEquiv childPos)

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace HubUpArm

variable {V : Type*}
variable {α : Type*}

/-- **`v` is the root internal vertex of `t`**, expressed on its address: `pathOf t v` is empty.

This is the exact predicate that separates the two cases of the up arm's source.  It is not a
property of the position assignment `φ`: `φ` may identify the root with any other vertex, and the
address layer is what decides which arm is the root edge. -/
def IsRootIpos (t : RTree α) (v : t.IPos) : Prop :=
  (RTree.pathOf t v).1 = []

/-- **The parent internal vertex of a non-root internal vertex `v`**: the internal vertex at the
address `(pathOf t v).1.dropLast`.

It is a genuine `t.IPos` (`parentIPos_ne` in `UpArm.lean` proves it is *not* `v`), and the up arm
of `v` is literally the down arm of this vertex in the direction `(pathOf t v).1.getLast`
(`hubUpEdge_eq_parentDown`).  For the root there is no parent, which is why this definition is
indexed by a proof of non-rootedness. -/
noncomputable def parentIPos (t : RTree α) (v : t.IPos) (h : ¬ IsRootIpos t v) : t.IPos :=
  RTree.iposOfPath t (RTree.pathOf t v).1.dropLast
    (RTree.dropLast_mem_ipaths (RTree.pathOf t v).2 h)

/-- **The exact source of the up arm of the 3-star of `v`.**

The root leaf vertex `c` when `v` is the root of `t` (the up arm is then the atlas root edge
`Sum.inr ⟨⟩`), and the parent's position `φ (parentIPos t v h)` otherwise (the up arm is then the
down arm of the parent).  The destination of the same arm is always `φ v`; keeping the two apart
is the whole content of the root-versus-parent analysis. -/
noncomputable def hubUpSrc (t : RTree α) (φ : t.IPos → V) (c : V) (v : t.IPos) : V :=
  if h : (RTree.pathOf t v).1 = [] then c else φ (parentIPos t v h)

/-- **The up arm of the 3-star of `v` as a realized atlas edge**: the `atlasEdgeEquiv` image of
production's address-level `RTree.upEdge`.  This is the slot whose two ends `hubUpSrc` and `φ v`
are computed in `UpArm.lean`, and the slot that `ParentIncl.lean` transports. -/
noncomputable def hubUpEdge (t : RTree α) (v : t.IPos) : AEdge t :=
  atlasEdgeEquiv t (RTree.upEdge t (RTree.pathOf t v).1 (RTree.pathOf t v).2)

/-- **The three far ends of the 3-star of `v`**, seen from the hub position `φ v`:
`(child false, child true, up-arm source)`.

The first two are the child positions (`childPos t φ y v b`, which are `φ` of an internal child or
the terminal `y a` of a leaf child); the third is `hubUpSrc t φ c v`, i.e. the root leaf `c` or the
parent's position.  Nothing here is an alias for `φ v`. -/
noncomputable def hubFar (t : RTree α) (φ : t.IPos → V) (y : α → V) (c : V) (v : t.IPos) :
    Fin 3 → V :=
  ![childPos t φ y v false, childPos t φ y v true, hubUpSrc t φ c v]

/-- **The parent-aware joint three-point function at the hub `v`.**  One configuration in which the
hub position `φ v` is connected to each of the three far ends `hubFar t φ y c v`.

This is an intersection of three connection events: a joint value at the single vertex `φ v`, not a
product of two-point factors and not a disjoint occurrence.  Its three connection points are
*physical*: the two child ends and the up-arm's own end (`c` at the root, the parent's position
otherwise). -/
def hubThreePoint (y : α → V) (c : V) (t : RTree α) (φ : t.IPos → V) (v : t.IPos) :
    Set (Config V) :=
  connSet (φ v) (hubFar t φ y c v 0) ∩ connSet (φ v) (hubFar t φ y c v 1) ∩
    connSet (φ v) (hubFar t φ y c v 2)

end HubUpArm
