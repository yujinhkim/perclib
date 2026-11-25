/-
Migration source: https://github.com/yujinhkim/Critical-Long-range-percolation
Integration revision: 3b3d1d0e43ef940bfaa2292ee5c2ee094ac4edbf
Licence: Apache-2.0 for the PercLib Lean sources and tooling; see third_party/critical-lrp/.
External provenance and modifications are recorded in the file-specific notices below.
-/

/-
Rooted binary trees, their vertices, and the enumeration of leaf-labelled rooted
binary trees.

Combinatorial layer behind inequalities (I.2.2) and (I.2.3) of

  T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
  arXiv:2508.18807v1, Section I.2.1, p. 22.

(I.2.2) sums over "(representatives of) isomorphism classes of trees with leaves
labelled `0, 1, ..., k` and unlabelled non-leaf vertices all of degree 3", and (I.2.3)
carries the factor `(2p − 3)!!`, "the number of trees with `p + 1` leaves labelled
`{0, ..., p}` and with all other vertices unlabelled and of degree 3".

A tree with leaves labelled `0, ..., k` and all other vertices of degree 3 is the same
thing as a rooted binary tree with leaves labelled `1, ..., k`: delete the leaf `0` and
suppress the resulting degree-2 vertex. Both counts equal `(2p − 3)!!` for `p + 1`
leaves. This file proves the second count (`RTree.card_labelled`) and the vertex counts
behind the insertion bijection.

Contents:
* `RTree` — rooted binary trees with leaves drawn from a type `α`;
* `RTree.leaves`, `RTree.LeafPos`, `RTree.Pos`, `RTree.IPos` — leaves and positions;
* `RTree.card_pos`, `RTree.card_ipos` — `#vertices = 2·#leaves − 1`, `#internal = #leaves − 1`;
* `RTree.insert`, `RTree.stripLeaf` — insertion of a leaf above a vertex and its inverse;
* `RTree.card_labelled` — `#{leaf-labelled trees with p leaves} = (2p − 3)!!`.

The paper's double factorial `(2n−1)!!` is `PercLib.CriticalLRP.VolumeMoments.M n`,
reused from `CriticalPercLib.CriticalLRP.VolumeMoments.DFactorial`.
-/
module

public import Mathlib
public import PercLib.CriticalLRP.VolumeMoments.DFactorial

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

set_option autoImplicit true

set_option autoImplicit false

@[expose] public section

namespace PercLib.CriticalLRP.TreeExpansion

universe u

/-- Rooted binary (plane-free) trees whose leaves are labelled by elements of `α`.
Every internal vertex has exactly two children. In the underlying unrooted tree such a
vertex has degree three (two children and a parent), except the root, which has degree
two and plays the role of the vertex suppressed when the leaf `0` is deleted from a
tree with all internal vertices of degree three. -/
inductive RTree (α : Type u) : Type u
  | leaf : α → RTree α
  | node : RTree α → RTree α → RTree α
  deriving DecidableEq

namespace RTree

variable {α : Type*} {β : Type*}

/-! ### Leaves -/

/-- The list of leaf labels, in left-to-right order. -/
def leaves : RTree α → List α
  | leaf a => [a]
  | node l r => leaves l ++ leaves r

@[simp] theorem leaves_leaf (a : α) : (leaf a).leaves = [a] := rfl

@[simp] theorem leaves_node (l r : RTree α) : (node l r).leaves = l.leaves ++ r.leaves := rfl

/-- The number of leaves. -/
def numLeaves (t : RTree α) : ℕ := t.leaves.length

@[simp] theorem numLeaves_leaf (a : α) : (leaf a).numLeaves = 1 := rfl

theorem numLeaves_node (l r : RTree α) : (node l r).numLeaves = l.numLeaves + r.numLeaves := by
  simp [numLeaves]

theorem numLeaves_pos (t : RTree α) : 0 < t.numLeaves := by
  cases t with
  | leaf a => simp
  | node l r => rw [numLeaves_node]; have := numLeaves_pos l; omega

/-! ### Relabelling -/

/-- Apply a function to every leaf label. -/
def mapLabel (f : α → β) : RTree α → RTree β
  | leaf a => leaf (f a)
  | node l r => node (mapLabel f l) (mapLabel f r)

@[simp] theorem leaves_mapLabel (f : α → β) (t : RTree α) :
    (t.mapLabel f).leaves = t.leaves.map f := by
  induction t with
  | leaf a => rfl
  | node l r ihl ihr => simp [mapLabel, ihl, ihr]

@[simp] theorem numLeaves_mapLabel (f : α → β) (t : RTree α) :
    (t.mapLabel f).numLeaves = t.numLeaves := by
  simp [numLeaves]

/-! ### Positions (vertices) -/

/-- The vertices of a tree: every vertex, the root included. The root of a `node` is the
`PUnit` summand, and the children are the two recursive summands. -/
def Pos : (t : RTree α) → Type
  | leaf _ => PUnit
  | node l r => Pos l ⊕ Pos r ⊕ PUnit

/-- The leaves of a tree, as a type. -/
def LeafPos : (t : RTree α) → Type
  | leaf _ => PUnit
  | node l r => LeafPos l ⊕ LeafPos r

/-- The internal (non-leaf) vertices of a tree. -/
def IPos : (t : RTree α) → Type
  | leaf _ => Empty
  | node l r => IPos l ⊕ IPos r ⊕ PUnit

instance instFintypePos {α : Type*} : (t : RTree α) → Fintype (Pos t)
  | leaf _ => inferInstanceAs (Fintype PUnit)
  | node l r => by
      haveI : Fintype (Pos l) := instFintypePos l
      haveI : Fintype (Pos r) := instFintypePos r
      exact inferInstanceAs (Fintype (Pos l ⊕ Pos r ⊕ PUnit))

instance instFintypeLeafPos {α : Type*} : (t : RTree α) → Fintype (LeafPos t)
  | leaf _ => inferInstanceAs (Fintype PUnit)
  | node l r => by
      haveI : Fintype (LeafPos l) := instFintypeLeafPos l
      haveI : Fintype (LeafPos r) := instFintypeLeafPos r
      exact inferInstanceAs (Fintype (LeafPos l ⊕ LeafPos r))

instance instFintypeIPos {α : Type*} : (t : RTree α) → Fintype (IPos t)
  | leaf _ => inferInstanceAs (Fintype Empty)
  | node l r => by
      haveI : Fintype (IPos l) := instFintypeIPos l
      haveI : Fintype (IPos r) := instFintypeIPos r
      exact inferInstanceAs (Fintype (IPos l ⊕ IPos r ⊕ PUnit))

instance instDecidableEqPos {α : Type*} : (t : RTree α) → DecidableEq (Pos t)
  | leaf _ => inferInstanceAs (DecidableEq PUnit)
  | node l r => by
      haveI : DecidableEq (Pos l) := instDecidableEqPos l
      haveI : DecidableEq (Pos r) := instDecidableEqPos r
      exact inferInstanceAs (DecidableEq (Pos l ⊕ Pos r ⊕ PUnit))

instance instDecidableEqLeafPos {α : Type*} : (t : RTree α) → DecidableEq (LeafPos t)
  | leaf _ => inferInstanceAs (DecidableEq PUnit)
  | node l r => by
      haveI : DecidableEq (LeafPos l) := instDecidableEqLeafPos l
      haveI : DecidableEq (LeafPos r) := instDecidableEqLeafPos r
      exact inferInstanceAs (DecidableEq (LeafPos l ⊕ LeafPos r))

instance instDecidableEqIPos {α : Type*} : (t : RTree α) → DecidableEq (IPos t)
  | leaf _ => inferInstanceAs (DecidableEq Empty)
  | node l r => by
      haveI : DecidableEq (IPos l) := instDecidableEqIPos l
      haveI : DecidableEq (IPos r) := instDecidableEqIPos r
      exact inferInstanceAs (DecidableEq (IPos l ⊕ IPos r ⊕ PUnit))

/-- `#vertices = 2·#leaves − 1`. -/
theorem card_pos (t : RTree α) : Fintype.card (Pos t) = 2 * t.numLeaves - 1 := by
  induction t with
  | leaf a => show (Fintype.card PUnit : ℕ) = 1; exact Fintype.card_punit
  | node l r ihl ihr =>
      have hpos : 0 < l.numLeaves := numLeaves_pos l
      have hpos' : 0 < r.numLeaves := numLeaves_pos r
      show Fintype.card (Pos l ⊕ Pos r ⊕ PUnit) = _
      rw [Fintype.card_sum, Fintype.card_sum, ihl, ihr, numLeaves_node]
      simp
      omega

/-- `#leaves` computed from the leaf positions. -/
theorem card_leafPos (t : RTree α) : Fintype.card (LeafPos t) = t.numLeaves := by
  induction t with
  | leaf a => show (Fintype.card PUnit : ℕ) = 1; exact Fintype.card_punit
  | node l r ihl ihr =>
      show Fintype.card (LeafPos l ⊕ LeafPos r) = _
      rw [Fintype.card_sum, ihl, ihr, numLeaves_node]

/-- `#internal vertices = #leaves − 1`. -/
theorem card_ipos (t : RTree α) : Fintype.card (IPos t) = t.numLeaves - 1 := by
  induction t with
  | leaf a => show (Fintype.card Empty : ℕ) = 0; exact Fintype.card_empty
  | node l r ihl ihr =>
      have hpos : 0 < l.numLeaves := numLeaves_pos l
      have hpos' : 0 < r.numLeaves := numLeaves_pos r
      show Fintype.card (IPos l ⊕ IPos r ⊕ PUnit) = _
      rw [Fintype.card_sum, Fintype.card_sum, ihl, ihr, numLeaves_node]
      simp
      omega

end RTree

end PercLib.CriticalLRP.TreeExpansion
