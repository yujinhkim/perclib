/-
The exact root-versus-parent source position of a hub's up arm.

Prepared from `.ultramath/smwx4z71g/m1/HubUpArm/UpArm.lean` at production revision
`5e579c30ee2c5caa2d151372f1929efd8ed587fb`; independently rebuilt and integrated by the
coordinator.  Definitions are in `Hub/UpArm/Defs.lean`; this file proves the source-position
results.

Production already proves the address-level statement `Real.src_upEdge`,
`srcPos t φ c (atlasEdgeEquiv t (upEdge t s hs)) = if s = [] then c else φ (iposOfPath …)`,
and `Real.upEdge_dstPos`, `… = φ (iposOfPath t s hs)`.  What is proved here is the same statement
at the level of a *hub* `v : t.IPos` and of a genuine parent vertex, which is what a slot statement
about `CanonAtlas.hubStarJoint` needs:

* `srcPos_hubUpEdge` -- the source of the up arm of the 3-star of `v` is exactly `hubUpSrc t φ c v`;
* `dstPos_hubUpEdge` -- its destination is exactly `φ v`;
* `hubUpSrc_eq_root`, `hubUpSrc_eq_parent` -- the two branches, with `c` in the root case and
  `φ (parentIPos t v h)` in the parent case;
* `isRootIpos_iff_eq_root` -- at a node, being the root hub is *equivalent* to being the `PUnit`
  summand, so the case split is exhaustive and exact, not a convention;
* `pathOf_parentIPos`, `parentIPos_ne` -- the parent is a genuine internal vertex at the address
  `dropLast`, and in particular it is **not** `v`;
* `hubUpEdge_eq_parentDown` -- for a non-root hub the up arm *is* the parent's down arm in the
  direction `getLast`, with source `φ (parent v)` and destination `φ v`;
* `hubUpEdge_eq_rootEdge` -- for the root hub the up arm is the atlas root edge `Sum.inr ⟨⟩`, with
  source the root leaf `c`;
* `hubUpSrc_eq_hubPos_iff` -- exactly when the up arm's source coincides with the hub position
  `φ v`: at the root iff `c = φ v`, and never for a non-root hub under injective `φ`;
* `hubStarArms_ends` -- the three arms of the 3-star seen from `φ v`: the two down arms end at
  `hubFar 0`, `hubFar 1` and start at `φ v`, the up arm starts at `hubFar 2` and ends at `φ v`.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Canonical.Hub.UpArm.Defs

/-!
# The source of a hub's up arm: root leaf `c`, or the parent's position
-/

@[expose] public section

open PercLib.CriticalLRP (Config connSet)
open PercLib.CriticalLRP.TreeExpansion (RTree)
open PercLib.CriticalLRP.TreeExpansion.Real
  (AEdge atlasEdgeEquiv srcPos dstPos childPos rootPos hubStarAEdges hubStarAEdges_eq
   srcPos_inl dstPos_inl)

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace HubUpArm

variable {V : Type*} [DecidableEq V]
variable {α : Type*} [DecidableEq α]

/-! ### The root predicate, exactly -/

/-- Being the root hub is the same as having depth zero. -/
theorem isRootIpos_iff_depth (t : RTree α) (v : t.IPos) :
    IsRootIpos t v ↔ RTree.iposDepth t v = 0 := by
  simp [IsRootIpos, RTree.iposDepth]

/-- **Characterisation of the root hub by its address**: it is the internal vertex at the empty
address.  This is the exact split used for the up arm: at the root the arm is the root edge. -/
theorem isRootIpos_iff_eq_iposOfPath_nil (t : RTree α) (v : t.IPos)
    (hmem : ([] : List Bool) ∈ RTree.ipaths t) :
    IsRootIpos t v ↔ v = RTree.iposOfPath t [] hmem := by
  constructor
  · intro h
    refine RTree.pathOf_injective t (Subtype.ext ?_)
    change (RTree.pathOf t v).1 = (RTree.pathOf t (RTree.iposOfPath t [] hmem)).1
    rw [RTree.pathOf_iposOfPath]
    exact h
  · intro h
    rw [h]
    change (RTree.pathOf t (RTree.iposOfPath t [] hmem)).1 = []
    rw [RTree.pathOf_iposOfPath]

/-- **At a node, the root hub is exactly the `PUnit` summand**, and every other internal vertex has
a parent.  So the two branches of the up arm are exhaustive. -/
theorem isRootIpos_node_iff (l r : RTree α) (v : (RTree.node l r).IPos) :
    IsRootIpos (RTree.node l r) v ↔
      v = (Sum.inr (Sum.inr ⟨⟩) : (RTree.node l r).IPos) := by
  have hmem : ([] : List Bool) ∈ RTree.ipaths (RTree.node l r) := by simp [RTree.ipaths]
  rw [isRootIpos_iff_eq_iposOfPath_nil (RTree.node l r) v hmem]
  rfl

/-! ### The parent vertex -/

/-- The parent's address is the hub's address with the last step removed. -/
theorem pathOf_parentIPos (t : RTree α) (v : t.IPos) (h : ¬ IsRootIpos t v) :
    (RTree.pathOf t (parentIPos t v h)).1 = (RTree.pathOf t v).1.dropLast := by
  unfold parentIPos
  rw [RTree.pathOf_iposOfPath]

/-- **The parent is not the hub.**  The up arm's far end `φ (parent v)` is therefore the image of a
different internal vertex than the hub, and the arm is not one of the hub's own down arms. -/
theorem parentIPos_ne (t : RTree α) (v : t.IPos) (h : ¬ IsRootIpos t v) :
    parentIPos t v h ≠ v := by
  intro heq
  have h1 : (RTree.pathOf t (parentIPos t v h)).1 = (RTree.pathOf t v).1 := by rw [heq]
  rw [pathOf_parentIPos] at h1
  have hlen := congrArg List.length h1
  rw [List.length_dropLast] at hlen
  have hpos : 0 < (RTree.pathOf t v).1.length := List.length_pos_of_ne_nil h
  omega

/-! ### The two branches of the up arm's source -/

/-- In the root case the up arm's source is the root leaf's vertex `c`. -/
theorem hubUpSrc_eq_root (t : RTree α) (φ : t.IPos → V) (c : V) (v : t.IPos)
    (h : IsRootIpos t v) : hubUpSrc t φ c v = c := by
  unfold hubUpSrc
  exact dite_eq_left h

/-- In the parent case the up arm's source is the parent's position `φ (parentIPos t v h)`. -/
theorem hubUpSrc_eq_parent (t : RTree α) (φ : t.IPos → V) (c : V) (v : t.IPos)
    (h : ¬ IsRootIpos t v) : hubUpSrc t φ c v = φ (parentIPos t v h) := by
  unfold hubUpSrc
  exact dite_eq_right h

/-- **The source of the up arm of the 3-star of `v`**, as a statement about the realized atlas
edge.  This is `Real.src_upEdge` at the hub, with the address `pathOf t v` and the parent vertex
`parentIPos` made explicit. -/
theorem srcPos_hubUpEdge (t : RTree α) (φ : t.IPos → V) (c : V) (v : t.IPos) :
    srcPos t φ c (hubUpEdge t v) = hubUpSrc t φ c v := by
  unfold hubUpEdge hubUpSrc parentIPos
  rw [PercLib.CriticalLRP.TreeExpansion.Real.src_upEdge]

/-- **The destination of the up arm of the 3-star of `v` is the hub position `φ v`** (this is
`Real.upEdge_dstPos` at the hub).  Keep it apart from the source: only in the degenerate case
`hubUpSrc t φ c v = φ v` do the two ends of this arm coincide. -/
theorem dstPos_hubUpEdge (t : RTree α) (φ : t.IPos → V) (y : α → V) (v : t.IPos) :
    dstPos t φ y (hubUpEdge t v) = φ v := by
  unfold hubUpEdge
  rw [PercLib.CriticalLRP.TreeExpansion.Real.upEdge_dstPos, RTree.iposOfPath_pathOf]

/-- The up arm belongs to the 3-star of its own hub. -/
theorem hubUpEdge_mem_hubStarAEdges (t : RTree α) (v : t.IPos) :
    hubUpEdge t v ∈ hubStarAEdges t v := by
  rw [hubStarAEdges_eq]
  simp [hubUpEdge]

/-! ### The up arm as the parent's down arm, and as the root edge -/

/-- **For a non-root hub the up arm is the parent's down arm** in the direction `getLast` of the
hub's own address.  This is the slot identity behind the parent-aware evaluation: the hub's third
arm is not a slot of its own 3-star in the down direction, it is a down slot of the parent. -/
theorem hubUpEdge_eq_parentDown (t : RTree α) (v : t.IPos) (h : ¬ IsRootIpos t v) :
    hubUpEdge t v =
      Sum.inl (parentIPos t v h, (RTree.pathOf t v).1.getLast h) := by
  have h' : (RTree.pathOf t v).1 ≠ [] := h
  unfold hubUpEdge parentIPos
  rw [RTree.upEdge, dite_eq_right h',
    PercLib.CriticalLRP.TreeExpansion.Real.atlasEdgeEquiv_inl]

/-- **For the root hub the up arm is the atlas root edge** `Sum.inr ⟨⟩`, the edge joining the root
leaf `c` to the root position. -/
theorem hubUpEdge_eq_rootEdge (t : RTree α) (v : t.IPos) (h : IsRootIpos t v) :
    hubUpEdge t v = Sum.inr ⟨⟩ := by
  have h' : (RTree.pathOf t v).1 = [] := h
  unfold hubUpEdge
  rw [RTree.upEdge, dite_eq_left h',
    PercLib.CriticalLRP.TreeExpansion.Real.atlasEdgeEquiv_root]

/-- The two ends of the parent's down arm are the parent's position and `φ v`: the child end of the
internal child at direction `getLast` is the hub position.  (Consequence of
`Real.childPos_iposOfPath_app`, read off from `dstPos_hubUpEdge`.) -/
theorem childPos_parent_getLast (t : RTree α) (φ : t.IPos → V) (y : α → V) (v : t.IPos)
    (h : ¬ IsRootIpos t v) :
    childPos t φ y (parentIPos t v h) ((RTree.pathOf t v).1.getLast h) = φ v := by
  have h1 := dstPos_hubUpEdge t φ y v
  rw [hubUpEdge_eq_parentDown t v h] at h1
  simpa only [dstPos_inl] using h1

/-- The up arm is not one of the hub's own down arms: its slot is the parent's down slot. -/
theorem hubUpEdge_ne_downEdge (t : RTree α) (v : t.IPos) (b : Bool) :
    hubUpEdge t v ≠ Sum.inl (v, b) := by
  by_cases h : IsRootIpos t v
  · rw [hubUpEdge_eq_rootEdge t v h]
    intro he
    cases he
  · rw [hubUpEdge_eq_parentDown t v h]
    intro he
    have h2 : parentIPos t v h = v := by
      have hp : (parentIPos t v h, (RTree.pathOf t v).1.getLast h) = (v, b) := by
        simpa using he
      simpa using congrArg Prod.fst hp
    exact parentIPos_ne t v h h2

/-! ### When does the up arm degenerate?

The up arm's two ends are `hubUpSrc t φ c v` and `φ v`.  They coincide only in the explicitly
described cases; this is the exact content of "keep the root and the parent distinct". -/

/-- At the root hub the up arm has equal ends exactly when the root leaf is at the hub. -/
theorem hubUpSrc_eq_hubPos_of_root (t : RTree α) (φ : t.IPos → V) (c : V) (v : t.IPos)
    (h : IsRootIpos t v) : hubUpSrc t φ c v = φ v ↔ c = φ v := by
  rw [hubUpSrc_eq_root t φ c v h]

/-- **Exact characterisation of a degenerate up arm** (for injective positions): the up arm's source
is the hub position iff the hub is the root *and* the root leaf sits at the hub position.  For a
non-root hub with injective `φ` the up arm is never degenerate, because the parent is a different
internal vertex. -/
theorem hubUpSrc_eq_hubPos_iff (t : RTree α) (φ : t.IPos → V) (c : V) (v : t.IPos)
    (hφ : Function.Injective φ) :
    hubUpSrc t φ c v = φ v ↔ IsRootIpos t v ∧ c = φ v := by
  by_cases h : IsRootIpos t v
  · rw [hubUpSrc_eq_root t φ c v h]
    exact ⟨fun hc => ⟨h, hc⟩, fun hc => hc.2⟩
  · refine ⟨fun he => ?_, fun hc => absurd hc.1 h⟩
    rw [hubUpSrc_eq_parent t φ c v h] at he
    exact (parentIPos_ne t v h (hφ he)).elim

/-- Consequently, for injective positions and a non-root hub, the two ends of the up arm differ. -/
theorem hubUpSrc_ne_hubPos_of_parent (t : RTree α) (φ : t.IPos → V) (c : V) (v : t.IPos)
    (h : ¬ IsRootIpos t v) (hφ : Function.Injective φ) :
    hubUpSrc t φ c v ≠ φ v := by
  rw [hubUpSrc_eq_parent t φ c v h]
  intro he
  exact parentIPos_ne t v h (hφ he)

/-- At the root, if the root leaf is not at the hub position then the up arm is non-degenerate. -/
theorem hubUpSrc_ne_hubPos_of_root (t : RTree α) (φ : t.IPos → V) (c : V) (v : t.IPos)
    (h : IsRootIpos t v) (hc : c ≠ φ v) : hubUpSrc t φ c v ≠ φ v := by
  rw [hubUpSrc_eq_root t φ c v h]
  exact hc

/-! ### The three arms seen from the hub position -/

/-- The first far end: the `false` child's position. -/
@[simp] theorem hubFar_zero (t : RTree α) (φ : t.IPos → V) (y : α → V) (c : V) (v : t.IPos) :
    hubFar t φ y c v 0 = childPos t φ y v false := rfl

/-- The second far end: the `true` child's position. -/
@[simp] theorem hubFar_one (t : RTree α) (φ : t.IPos → V) (y : α → V) (c : V) (v : t.IPos) :
    hubFar t φ y c v 1 = childPos t φ y v true := rfl

/-- The third far end: the up arm's own source, `c` at the root and `φ (parent v)` otherwise. -/
@[simp] theorem hubFar_two (t : RTree α) (φ : t.IPos → V) (y : α → V) (c : V) (v : t.IPos) :
    hubFar t φ y c v 2 = hubUpSrc t φ c v := rfl

/-- **The ends of the three arms of the 3-star of `v`.**

Each of the three edges of `hubStarAEdges t v` has `φ v` as one end and the corresponding entry of
`hubFar t φ y c v` as the other: the two down arms start at `φ v` and end at the child positions,
the up arm starts at the up-arm source (`c` at the root, `φ (parent v)` otherwise) and ends at
`φ v`.  This is the slot bookkeeping that the parent-aware evaluation uses. -/
theorem hubStarArms_ends (t : RTree α) (φ : t.IPos → V) (y : α → V) (c : V) (v : t.IPos) :
    (srcPos t φ c (Sum.inl (v, false)) = φ v ∧
      dstPos t φ y (Sum.inl (v, false)) = hubFar t φ y c v 0) ∧
    (srcPos t φ c (Sum.inl (v, true)) = φ v ∧
      dstPos t φ y (Sum.inl (v, true)) = hubFar t φ y c v 1) ∧
    (srcPos t φ c (hubUpEdge t v) = hubFar t φ y c v 2 ∧
      dstPos t φ y (hubUpEdge t v) = φ v) := by
  refine ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩, ?_⟩
  exact ⟨srcPos_hubUpEdge t φ c v, dstPos_hubUpEdge t φ y v⟩

end HubUpArm
