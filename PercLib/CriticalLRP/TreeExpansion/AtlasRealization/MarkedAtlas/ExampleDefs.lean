/- Auxiliary shape definitions migrated from independently verified Ultramath work:
smwwt6noq, member m1. -/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.MarkedAtlas.Defs

/-!
# Small explicit marked shapes and two-leaf atlas-edge indices

The single-mark shape at `p = 0`, the two marked-label orderings at `p = 1`, and
their named internal and atlas-edge positions. These definitions introduce no probability model.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.haveILetI false

namespace PercLib.CriticalLRP.MarkedAtlas

open Finset
open PercLib.CriticalLRP.TreeExpansion (RTree LTon)
open PercLib.CriticalLRP.TreeExpansion.Real (AEdge)

variable {α : Type*} [DecidableEq α]

/-! ## The two-leaf atlas-edge indices -/

/-- The root branch point of a two-leaf shape. -/
abbrev twoLeafRoot (a b : α) : (RTree.node (RTree.leaf a) (RTree.leaf b)).IPos :=
  Sum.inr (Sum.inr ⟨⟩)

/-- The atlas edge from the root branch point to the first leaf. -/
abbrev twoLeafEdgeA (a b : α) : AEdge (RTree.node (RTree.leaf a) (RTree.leaf b)) :=
  Sum.inl (twoLeafRoot a b, false)

/-- The atlas edge from the root branch point to the second leaf. -/
abbrev twoLeafEdgeB (a b : α) : AEdge (RTree.node (RTree.leaf a) (RTree.leaf b)) :=
  Sum.inl (twoLeafRoot a b, true)

/-- The root atlas edge, from the root vertex to the root branch point. -/
abbrev twoLeafEdgeRoot (a b : α) : AEdge (RTree.node (RTree.leaf a) (RTree.leaf b)) :=
  Sum.inr ⟨⟩


/-! ## The marked label type at zero ordinary arms -/

instance instSubsingletonMarkLabelZero : Subsingleton (MarkLabel 0) :=
  ⟨fun a b => by
    rcases a with (i | ⟨⟩) <;> rcases b with (j | ⟨⟩)
    · exact Fin.elim0 i
    · exact Fin.elim0 i
    · exact Fin.elim0 j
    · rfl⟩

/-- The unique labelled shape at `p = 0`: the single marked leaf. -/
def markShapeP0 : LTon (MarkLabel 0) (markLabels 0) :=
  ⟨RTree.leaf (markLabelOf (p := 0)), by
    refine ⟨List.nodup_singleton _, ?_⟩
    change ([markLabelOf (p := 0)] : List (MarkLabel 0)).toFinset = Finset.univ
    rw [Finset.eq_univ_iff_forall]
    intro x
    rw [List.mem_toFinset, List.mem_singleton]
    exact Subsingleton.elim x _⟩


/-! ## The two marked-label orderings at one ordinary arm -/

def markShapeP1a : LTon (MarkLabel 1) (markLabels 1) :=
  ⟨RTree.node (RTree.leaf (Sum.inl 0)) (RTree.leaf (markLabelOf (p := 1))), by
    refine ⟨?_, ?_⟩
    · rw [RTree.leaves_node]
      simp [markLabelOf]
    · rw [RTree.leaves_node, List.toFinset_append]
      simp only [RTree.leaves_leaf, markLabels]
      rw [Finset.eq_univ_iff_forall]
      intro z
      rcases z with (i | u)
      · have hi : i = 0 := Subsingleton.elim i 0
        subst hi
        simp
      · have hu : u = ⟨⟩ := Subsingleton.elim u ⟨⟩
        subst hu
        simp [markLabelOf]⟩

/-- The second `p = 1` shape: the unmarked arm on the right. -/
def markShapeP1b : LTon (MarkLabel 1) (markLabels 1) :=
  ⟨RTree.node (RTree.leaf (markLabelOf (p := 1))) (RTree.leaf (Sum.inl 0)), by
    refine ⟨?_, ?_⟩
    · rw [RTree.leaves_node]
      simp [markLabelOf]
    · rw [RTree.leaves_node, List.toFinset_append]
      simp only [RTree.leaves_leaf, markLabels]
      rw [Finset.eq_univ_iff_forall]
      intro z
      rcases z with (i | u)
      · have hi : i = 0 := Subsingleton.elim i 0
        subst hi
        simp
      · have hu : u = ⟨⟩ := Subsingleton.elim u ⟨⟩
        subst hu
        simp [markLabelOf]⟩


end PercLib.CriticalLRP.MarkedAtlas
