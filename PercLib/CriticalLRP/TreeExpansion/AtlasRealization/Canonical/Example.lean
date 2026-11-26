/-
Independently built worked example for swarm `smwwtd5t5`, member `m1` (direction A).

## Why an example

The covering theorem `CanonAtlas.exists_canonical_realization` is an existence statement about an
arbitrary countable vertex set and an arbitrary configuration, so on its own it could in principle
be vacuous (e.g. if `IsCanonRealization` were unsatisfiable).  This file exhibits an explicit
canonical realization on the smallest non-degenerate instance: three vertices `0, 1, 2`, the two
terminals at vertices `1` and `2`, the root at vertex `0`, and the two-leaf shape
`node (leaf 0) (leaf 1)` whose single internal vertex sits at vertex `1`.

The atlas has `2 * 2 - 1 = 3` edges, with witnesses

* root leaf edge `0 — 1` (root vertex to the internal vertex): `{s(0,1)}`,
* down edge towards the label `1` at vertex `2`: `{s(1,2)}`,
* down edge towards the label `0`, which also sits at vertex `1`: its two ends are both vertex
  `1`, its witness is `∅`, and `degenerate_edge` below *proves* that the two ends coincide.

The three witnesses are pairwise disjoint, so this is a genuine atlas, and its middle edge is the
degenerate edge of the source, with factor `P(1 ↔ 1) = 1`.  This is exactly the configuration the
paper's union bound has to cover, and it shows that the degenerate case is handled by the honest
empty witness rather than being excluded.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Canonical.Prob

/-!
# A worked two-leaf atlas with a degenerate edge
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace CanonAtlas.Example

open Finset

open PercLib.CriticalLRP (Config Connects connSet connects_refl)

open PercLib.CriticalLRP.TreeExpansion (RTree LTon)

open PercLib.CriticalLRP.TreeExpansion.Real (AEdge srcPos dstPos IsLabelledShape)

/-- The shape with two leaves, labelled `0` and `1`. -/
def twoLeaf : RTree (Fin 2) := RTree.node (RTree.leaf 0) (RTree.leaf 1)

/-- The terminals sit at the vertices `1` and `2`. -/
def labels : Fin 2 → Fin 3 := fun i => ⟨i.val + 1, by omega⟩

/-- The single internal vertex of the shape sits at the vertex `1`, which is the vertex of the
label `0`: the atlas edge between them is the degenerate one. -/
def phi : twoLeaf.IPos → Fin 3 := fun _ => 1

/-- The witnesses: `{s(1,2)}` for the down edge towards the label `1`, `∅` for the down edge
towards the label `0` (degenerate), and `{s(0,1)}` for the root leaf edge.  The down witnesses do
not depend on the internal position, which is unique for this shape. -/
def wit : AEdge twoLeaf → Finset (Sym2 (Fin 3))
  | Sum.inl (_, true) => {s(1, 2)}
  | Sum.inl (_, false) => ∅
  | Sum.inr _ => {s(0, 1)}

/-- The internal vertex of the two-leaf shape is unique: it is the root. -/
theorem eq_root (u : twoLeaf.IPos) : u = Sum.inr (Sum.inr ⟨⟩) := by
  rcases u with (u | u | x)
  · exact nomatch u
  · exact nomatch u
  · rw [Subsingleton.elim x ⟨⟩]

/-- The upper end of either down edge of the two-leaf shape is the internal vertex, at `1`. -/
theorem srcPos_down (u : twoLeaf.IPos) (b : Bool) :
    srcPos twoLeaf phi 0 (Sum.inl (u, b)) = 1 := by
  rw [PercLib.CriticalLRP.TreeExpansion.Real.srcPos_inl]
  rfl

/-- The lower end of the down edge in the `false` direction is the label `0`, at vertex `1`. -/
theorem dstPos_false (u : twoLeaf.IPos) :
    dstPos twoLeaf phi labels (Sum.inl (u, false)) = 1 := by
  rw [PercLib.CriticalLRP.TreeExpansion.Real.dstPos_inl, eq_root u]
  rfl

/-- The lower end of the down edge in the `true` direction is the label `1`, at vertex `2`. -/
theorem dstPos_true (u : twoLeaf.IPos) :
    dstPos twoLeaf phi labels (Sum.inl (u, true)) = 2 := by
  rw [PercLib.CriticalLRP.TreeExpansion.Real.dstPos_inl, eq_root u]
  rfl

/-- The upper end of the root leaf edge is the root vertex `0`. -/
theorem srcPos_root' (x : PUnit) : srcPos twoLeaf phi 0 (Sum.inr x) = 0 := rfl

/-- The lower end of the root leaf edge is the internal vertex, at `1`. -/
theorem dstPos_root' (x : PUnit) : dstPos twoLeaf phi labels (Sum.inr x) = 1 := rfl

theorem wit_down_false (u : twoLeaf.IPos) : wit (Sum.inl (u, false)) = ∅ := rfl

theorem wit_down_true (u : twoLeaf.IPos) : wit (Sum.inl (u, true)) = {s(1, 2)} := rfl

theorem wit_root (x : PUnit) : wit (Sum.inr x) = {s(0, 1)} := rfl

/-- The explicit canonical realization: a genuine two-leaf atlas with one degenerate edge. -/
theorem isRealization :
    IsCanonRealization (Set.univ : Config (Fin 3)) labels 0 phi wit where
  subset _ := fun _ _ => Set.mem_univ _
  disjoint e e' hne := by
    rcases e with (⟨u, b⟩ | x) <;> rcases e' with (⟨u', b'⟩ | x')
    · cases b <;> cases b'
      · exact absurd (by rw [eq_root u, eq_root u']) hne
      · rw [wit_down_false, wit_down_true]; decide
      · rw [wit_down_true, wit_down_false]; decide
      · exact absurd (by rw [eq_root u, eq_root u']) hne
    · cases b
      · rw [wit_down_false, wit_root]; decide
      · rw [wit_down_true, wit_root]; decide
    · cases b'
      · rw [wit_root, wit_down_false]; decide
      · rw [wit_root, wit_down_true]; decide
    · exact absurd (by rw [Subsingleton.elim x x']) hne
  conn e := by
    rcases e with (⟨u, b⟩ | x)
    · cases b
      · rw [wit_down_false, srcPos_down, dstPos_false]
      · rw [wit_down_true, srcPos_down, dstPos_true]
        refine SimpleGraph.Adj.reachable ?_
        rw [PercLib.CriticalLRP.openGraph_adj]
        exact ⟨by decide, by simp⟩
    · rw [wit_root, srcPos_root', dstPos_root']
      refine SimpleGraph.Adj.reachable ?_
      rw [PercLib.CriticalLRP.openGraph_adj]
      exact ⟨by decide, by simp⟩

/-- The two-leaf shape is a genuinely fully labelled shape on two labels. -/
theorem isLabelledShape : IsLabelledShape twoLeaf Finset.univ := by
  refine ⟨?_, ?_⟩
  · decide
  · decide

/-- The atlas of this shape has `2 * 2 - 1 = 3` edges. -/
theorem card_aedge_twoLeaf : Fintype.card (AEdge twoLeaf) = 3 := by
  have h := card_aedge_of_labelled isLabelledShape (q := 2)
  simpa using h

/-- The completely open configuration is in the canonical atlas event of this diagram. -/
theorem mem_atlasEvent : (Set.univ : Config (Fin 3)) ∈ CanonAtlasEvent labels 0 twoLeaf phi :=
  ⟨wit, isRealization⟩

/-- Consequently the completely open configuration is in the canonical atlas cover of the
two-label terminal event. -/
theorem mem_canonCover_example : (Set.univ : Config (Fin 3)) ∈ CanonCover 2 labels 0 := by
  rw [CanonAtlas.mem_canonCover]
  exact ⟨⟨⟨twoLeaf, isLabelledShape⟩, phi⟩, mem_atlasEvent⟩

/-- **The degenerate edge really is degenerate**: its two ends are the same vertex, which is why
its empty witness is the honest factor `P(1 ↔ 1) = 1` and not a hidden open edge. -/
theorem degenerate_edge :
    srcPos twoLeaf phi 0 (Sum.inl (Sum.inr (Sum.inr ⟨⟩), false)) =
      dstPos twoLeaf phi labels (Sum.inl (Sum.inr (Sum.inr ⟨⟩), false)) :=
  srcPos_eq_dstPos_of_wit_eq_empty isRealization rfl

end CanonAtlas.Example
