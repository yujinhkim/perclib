/- Independently rebuilt and verified at production revision
    eb9b71a3cf20a0fe9906271415f5b17efd80f5ad.
    Original scratch source is recorded below. -/
/-
Direction A of swarm `smwwt6noq`: the concrete `p = 0` instantiation of the finite marked atlas
bound, and the small-shape classifications used by it (`p = 1` follows in `TwoLeaf.lean`).

At `p = 0` the label type is `Fin 0 ⊕ PUnit`, which is a singleton: there is exactly one labelled
shape (the marked leaf), its internal-position space is empty, and its atlas has exactly one edge
(the root edge from the root vertex `x` to the marked terminal `w`).  The finite marked diagram
expression therefore collapses to a single two-point function, and the marked atlas bound is an
*equality* — which is the sharpest possible check that the marked decomposition of `Bound.lean`
does not lose or duplicate terms, and that the bookkeeping of the marked leaf at `p = 0` is
correct.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.MarkedAtlas.Bound
public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.MarkedAtlas.ExampleDefs

/-! # The `p = 0` instantiation of the marked atlas bound -/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
-- `haveI` is needed: the facts below are type-class instances for `rw`, not hypotheses.
set_option linter.style.haveILetI false

namespace PercLib.CriticalLRP.MarkedAtlas

open Finset
open PercLib.CriticalLRP.TreeExpansion (RTree LTon)
open PercLib.CriticalLRP.TreeExpansion.Real
open PercLib.CriticalLRP.TreeGraph (Conn prob BKIncreasing)

variable {V : Type*} [Fintype V] [DecidableEq V] {E : Type*} [Fintype E] [DecidableEq E]

/-! ## Classifying shapes with one and two leaves -/

/-- A rooted binary tree with a single leaf is that leaf. -/
theorem eq_leaf_of_numLeaves_eq_one {α : Type*} (t : RTree α) (h : t.numLeaves = 1) :
    ∃ a, t = RTree.leaf a := by
  cases t with
  | leaf a => exact ⟨a, rfl⟩
  | node l r =>
      have h1 := RTree.numLeaves_pos l
      have h2 := RTree.numLeaves_pos r
      rw [RTree.numLeaves_node] at h
      omega

/-- A rooted binary tree with two leaves is a node of two leaves. -/
theorem eq_node_leaf_leaf_of_numLeaves_eq_two {α : Type*} (t : RTree α) (h : t.numLeaves = 2) :
    ∃ a b, t = RTree.node (RTree.leaf a) (RTree.leaf b) := by
  cases t with
  | leaf a =>
      rw [RTree.numLeaves_leaf] at h
      exact absurd h (by norm_num)
  | node l r =>
      rw [RTree.numLeaves_node] at h
      have h1 := RTree.numLeaves_pos l
      have h2 := RTree.numLeaves_pos r
      have h1' : l.numLeaves = 1 := by omega
      have h2' : r.numLeaves = 1 := by omega
      obtain ⟨a, ha⟩ := eq_leaf_of_numLeaves_eq_one l h1'
      obtain ⟨b, hb⟩ := eq_leaf_of_numLeaves_eq_one r h2'
      exact ⟨a, b, by rw [ha, hb]⟩

/-! ## The marked label type at `p = 0` -/

/-- At `p = 0` the label type `Fin 0 ⊕ PUnit` is a singleton, so the marked terminal map is
constantly `w` whatever the (empty) arm assignment is. -/
theorem markTerm_p0 {V : Type*} (f : Fin 0 → V) (w : V) (a : MarkLabel 0) :
    markTerm f w a = w := by
  rcases a with (i | ⟨⟩)
  · exact Fin.elim0 i
  · rfl

/-- **There is only one labelled shape at `p = 0`.** -/
theorem eq_markShapeP0 (t : LTon (MarkLabel 0) (markLabels 0)) : t = markShapeP0 := by
  obtain ⟨u, hu⟩ := t
  have hnum : u.numLeaves = 1 := by
    rw [RTree.numLeaves, ← List.toFinset_card_of_nodup hu.1, hu.2]
    simp [markLabels]
  obtain ⟨a, ha⟩ := eq_leaf_of_numLeaves_eq_one u hnum
  have htree : u = markShapeP0.1 := by
    rw [ha]
    change RTree.leaf a = RTree.leaf (markLabelOf (p := 0))
    rw [Subsingleton.elim a (markLabelOf (p := 0))]
  exact Subtype.ext htree

/-- The marked depth at `p = 0` is `1`: the mark is the root's only child. -/
theorem markDepth_p0 (t : LTon (MarkLabel 0) (markLabels 0))
    (hc : markLabelOf (p := 0) ∈ markLabels 0) :
    markDepth (markLabelOf (p := 0)) t hc = 1 := by
  obtain ⟨u, hu⟩ := t
  have hnum : u.numLeaves = 1 := by
    rw [RTree.numLeaves, ← List.toFinset_card_of_nodup hu.1, hu.2]
    simp [markLabels]
  obtain ⟨a, ha⟩ := eq_leaf_of_numLeaves_eq_one u hnum
  subst ha
  simp only [markDepth]
  rfl

/-! ## The single atlas edge of the marked leaf -/

/-- The atlas-edge type of a single leaf is a singleton: only the root edge exists. -/
theorem aedge_leaf_subsingleton {α : Type*} (a : α) : Subsingleton (AEdge (RTree.leaf a)) :=
  ⟨fun x y => by
    rcases x with (⟨u, _⟩ | ⟨⟩) <;> rcases y with (⟨u', _⟩ | ⟨⟩)
    · exact u.elim
    · exact u.elim
    · exact u'.elim
    · rfl⟩

/-- **The marked diagram of the single `p = 0` shape is the two-point function.**  Its unique
atlas edge joins the root vertex `x` to the marked terminal `w`, and its internal-position space
is empty, so the sum over internal positions and the product over atlas edges both collapse. -/
theorem markDiag_p0 (pr : E → ℝ) (ends : E → Sym2 V) (x : V) (f : Fin 0 → V) (w : V)
    (t : LTon (MarkLabel 0) (markLabels 0)) :
    markDiag pr ends x (markTerm f w) t = pconn pr ends x w := by
  obtain ⟨u, hu⟩ := t
  have hnum : u.numLeaves = 1 := by
    rw [RTree.numLeaves, ← List.toFinset_card_of_nodup hu.1, hu.2]
    simp [markLabels]
  obtain ⟨a, ha⟩ := eq_leaf_of_numLeaves_eq_one u hnum
  subst ha
  simp only [markDiag]
  haveI hpsub : Subsingleton ((RTree.leaf a).IPos → V) :=
    ⟨fun f g => by funext u; exact u.elim⟩
  rw [Fintype.sum_subsingleton _ (fun u => u.elim)]
  haveI hsub : Subsingleton (AEdge (RTree.leaf a)) := aedge_leaf_subsingleton a
  rw [Fintype.prod_subsingleton _ (Sum.inr ⟨⟩ : AEdge (RTree.leaf a)), pconn]
  congr 1
  ext ω
  simp only [ConnEvent, Set.mem_ofPred_eq, srcPos_root, dstPos_root, rootPos_leaf,
    markTerm_p0 f w a]

/-- The whole labelled-shape sum at `p = 0` is the two-point function. -/
theorem sum_markDiag_p0 (pr : E → ℝ) (ends : E → Sym2 V) (x : V) (f : Fin 0 → V) (w : V) :
    (∑ t : LTon (MarkLabel 0) (markLabels 0), markDiag pr ends x (markTerm f w) t)
      = pconn pr ends x w := by
  haveI : Subsingleton (LTon (MarkLabel 0) (markLabels 0)) :=
    ⟨fun a b => by rw [eq_markShapeP0 a, eq_markShapeP0 b]⟩
  rw [Fintype.sum_subsingleton _ markShapeP0, markDiag_p0]

/-! ## The marked coefficients at `p = 0` -/

/-- No shape has marked depth `0` (`markDepth_pos`): the coefficient at `ℓ = 0` vanishes. -/
theorem markCoeff_p0_zero (pr : E → ℝ) (ends : E → Sym2 V) (x : V) (f : Fin 0 → V) (w : V) :
    markCoeff pr ends x (markTerm f w) (markLabelOf (p := 0)) (markLabelOf_mem 0) 0 = 0 := by
  rw [markCoeff]
  have hempty : (Finset.univ.filter (fun t : LTon (MarkLabel 0) (markLabels 0) =>
      markDepth (markLabelOf (p := 0)) t (markLabelOf_mem 0) = 0)) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro t _
    rw [markDepth_p0 t]
    omega
  rw [hempty, Finset.sum_empty]

/-- Every shape has marked depth `1`, so the coefficient at `ℓ = 1` is the whole shape sum,
i.e. the two-point function. -/
theorem markCoeff_p0_one (pr : E → ℝ) (ends : E → Sym2 V) (x : V) (f : Fin 0 → V) (w : V) :
    markCoeff pr ends x (markTerm f w) (markLabelOf (p := 0)) (markLabelOf_mem 0) 1
      = pconn pr ends x w := by
  rw [markCoeff]
  have hfilter : (Finset.univ.filter (fun t : LTon (MarkLabel 0) (markLabels 0) =>
      markDepth (markLabelOf (p := 0)) t (markLabelOf_mem 0) = 1)) = Finset.univ := by
    refine Finset.filter_true_of_mem ?_
    intro t _
    rw [markDepth_p0 t]
  rw [hfilter, sum_markDiag_p0]

/-! ## The bound at `p = 0` -/

/-- **The finite marked diagram expression at `p = 0` is the two-point function.**  The marked
coefficient sum over the depth range `{0, 1}` has the single nonvanishing term `ℓ = 1`. -/
theorem markedBound_p0 (pr : E → ℝ) (ends : E → Sym2 V) (x : V) (f : Fin 0 → V) (w : V) :
    markedBound pr ends x f w = pconn pr ends x w := by
  rw [markedBound, markBound, markLabels_card]
  rw [show (0 + 1 + 1 : ℕ) = 1 + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_one,
    markCoeff_p0_zero, markCoeff_p0_one]
  ring

/-- At `p = 0` the marked base event is just `{x ↔ w}`. -/
theorem markedBaseEvent_p0 (ends : E → Sym2 V) (x : V) (f : Fin 0 → V) (w : V) :
    MarkedBaseEvent ends x f w = {ω : Finset E | Conn ends ω x w} := by
  rw [markedBaseEvent_eq]
  ext ω
  simp only [Set.mem_ofPred_eq]
  exact ⟨fun h => h.2, fun h => ⟨fun i => Fin.elim0 i, h⟩⟩

/-- **The marked atlas bound at `p = 0` is an equality**: both sides are the two-point function
`P(x ↔ w)`.  No hypothesis on the finite law is needed for the identity itself. -/
theorem prob_markedBase_p0 (pr : E → ℝ) (ends : E → Sym2 V) (x : V) (f : Fin 0 → V) (w : V) :
    prob pr (MarkedBaseEvent ends x f w) = pconn pr ends x w := by
  rw [markedBaseEvent_p0, pconn]

/-- The `p = 0` instance of `prob_markedBase_le_markedBound`, with the marked coefficient
expression evaluated to the two-point function.  The conclusion is an equality, so the general
bound is sharp at `p = 0`. -/
theorem prob_markedBase_le_pconn_p0 (pr : E → ℝ) (hp : ∀ e, 0 ≤ pr e) (hp1 : ∀ e, pr e ≤ 1)
    (hBK : BKIncreasing pr) (ends : E → Sym2 V) (x : V) (f : Fin 0 → V) (w : V) :
    prob pr (MarkedBaseEvent ends x f w) ≤ pconn pr ends x w := by
  have h := prob_markedBase_le_markedBound pr hp hp1 hBK ends x f w
  rwa [markedBound_p0] at h

end PercLib.CriticalLRP.MarkedAtlas
