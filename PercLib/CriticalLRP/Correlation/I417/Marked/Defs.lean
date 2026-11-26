/- Independently rebuilt and verified at production revision
    eb9b71a3cf20a0fe9906271415f5b17efd80f5ad.
    Original scratch source is recorded below. -/
/-
An independently rebuilt direction (Ultramath swarm `smwwt6noq`, member `m2`, direction B).
Production base `4c53bb5a8e76a4358a426adf71169b916b90f51f`.
-/

module

public import PercLib.CriticalLRP.Correlation.I417.Base.Depth
public import PercLib.CriticalLRP.TreeExpansion.LabelledWeights
public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.WeightBridge.Bridge

/-!
# Definitions: labelled marked shapes for `Fin p ⊕ PUnit`

The base event of Lemma I.4.17 in Hutchcroft, *Critical long-range percolation I*
(arXiv:2508.18807v1, p. 45) is

  `E[|K_x|^p 1(w ∈ K_x)]`,

i.e. `p` unmarked terminals (the "arms" of `x`) together with **one** marked terminal `w`.
The tree-graph expansion of that event produces rooted binary trees on `p + 1` leaves, all of
them carrying *distinct* labels: the arms `Sum.inl i`, `i : Fin p`, and the mark
`Sum.inr ⟨⟩`.  Every such tree therefore has exactly one leaf labelled by the mark, and that
leaf -- determined by the labelling, not chosen by hand -- is the one whose value is pinned.

This file only *defines* the objects.  Proofs live in `I417Marked/Marked.lean` (the
label-to-position API and the exact diagram reduction) and `I417Marked/Numerics.lean`
(the `p = 0` and `p = 1` evaluations).

## The pieces

* `Label p`, `markLabel p`, `armLabel p i` -- the label type `Fin p ⊕ PUnit`, the label of the
  marked terminal and the label of the `i`-th arm.
* `markPos m t` -- the leaf position carrying the label `m`.  This is the label-to-position
  map: it has an arbitrary (definitionally irrelevant) default on trees where `m` does not
  occur, and `markPos_spec` identifies it on trees where it does.
* `markDepth m t` -- `RTree.depth` of that position: the length of the marked path, the `ℓ`
  of the source's `T^ℓ(x,y)`.
* `markedShapes p` -- the **genuine labelled marked shape family**: every injectively
  labelled binary tree whose leaf set is the whole label set `Fin p ⊕ PUnit`, paired with its
  marked leaf position.  It is a `Finset`, i.e. it is finite because the leaf set is exactly
  the finite label set, and it is enumerated from `LTon (Label p) univ`.
* `markedCount p ℓ` -- the number of shapes of that family whose marked leaf has depth `ℓ`;
  this is the source's `C_{p,ℓ}` as an explicit `Finset.card`.
* `markedDiagram k p x w`, `labelledMarkedDiagram k p x w` -- the per-shape marked diagram sum
  in the two equivalent presentations (leaf-position assignments vs. label assignments with
  the atlas product over the internal positions).
* `markedPolygonBound χ k p x w` -- the finite diagram expression
  `∑_ℓ markedCount p ℓ · χ^(2p+1-ℓ) · T^ℓ(x,w)` with `T = iterPow k`.

## Source discrepancies

None in this file.  Nothing here assumes probability, transitivity, or `p ≥ 1`; `p = 0` is
the family with the single tree `leaf (Sum.inr ⟨⟩)`.  The full source statement
`C_{p,q,ℓ} = ` the paper's diagram counts, the `(2p-1)!!` total, and the two-copy `q` side are
*not* claimed here.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ENNReal NNReal

@[expose] public section

namespace PercLib.CriticalLRP.I417Marked

open PercLib.CriticalLRP.TreeExpansion

universe u

/-! ## The labels -/

/-- The label type of the marked base event: `p` arm labels `Sum.inl i` and one mark label
`Sum.inr ⟨⟩`. -/
abbrev Label (p : ℕ) : Type := Fin p ⊕ PUnit

/-- The label of the marked terminal: the `PUnit` summand of `Fin p ⊕ PUnit`. -/
def markLabel (p : ℕ) : Label p := Sum.inr ⟨⟩

/-- The label of the `i`-th arm of `x`: the `Fin p` summand. -/
def armLabel (p : ℕ) (i : Fin p) : Label p := Sum.inl i

/-! ## The leaf position of a label -/

/-- The **leftmost** leaf position of a tree.  It exists only to give `markPos` a total
definition; it is never the marked position of a marked shape. -/
def firstLeafPos {α : Type u} : (t : RTree α) → t.LeafPos
  | RTree.leaf _ => ⟨⟩
  | RTree.node l _ => Sum.inl (firstLeafPos l)

/-- **The label-to-position map.**  The leaf position of `t` carrying the label `m`.  On a tree
in which `m` occurs this is a genuine choice from `RTree.exists_leafOfPos`; otherwise it is the
arbitrary default `firstLeafPos t`. -/
noncomputable def markPos {α : Type u} [DecidableEq α] (m : α) (t : RTree α) : t.LeafPos :=
  if h : m ∈ t.leaves then Classical.choose (RTree.exists_leafOfPos t m h) else firstLeafPos t

/-- The **marked depth**: the length `ℓ` of the path from the root of `t` to the leaf carrying
the label `m`.  This is the `ℓ` of the source's `T^ℓ(x,y)`. -/
noncomputable def markDepth {α : Type u} [DecidableEq α] (m : α) (t : RTree α) : ℕ :=
  RTree.depth t (markPos m t)

/-! ## The labelled marked shape family -/

/-- The index type of the marked shape family: a labelled binary tree over `Fin p ⊕ PUnit`
together with one of its leaf positions. -/
abbrev MarkedShape (p : ℕ) : Type := (t : RTree (Label p)) × t.LeafPos

/-- The **genuine labelled marked shape family** of the base side of Lemma I.4.17 at `p`:
every binary tree whose leaves are labelled injectively by *all* of `Fin p ⊕ PUnit`, paired
with the leaf position carrying the mark `markLabel p`. -/
noncomputable def markedShapes (p : ℕ) : Finset (MarkedShape p) :=
  Finset.univ.image (fun t : LTon (Label p) (Finset.univ) =>
    (⟨t.1, markPos (markLabel p) t.1⟩ : MarkedShape p))

/-- The number of shapes of the labelled family whose marked leaf has depth `ℓ`: the source's
`C_{p,ℓ}`, as an explicit finite cardinality. -/
noncomputable def markedCount (p : ℕ) (ℓ : ℕ) : ℕ :=
  ((markedShapes p).filter (fun A => RTree.depth A.1 A.2 = ℓ)).card

/-! ## The marked diagram sum and its collapsed form -/

/-- **The per-shape marked diagram sum.**  For every marked labelled shape `A` of the family,
the tree weight `wtE k A.1 · x` (which sums the values of the internal vertices, and of the
leaves, over the whole vertex set) with the leaf `A.2` pinned at `w`. -/
noncomputable def markedDiagram {W : Type u} [DecidableEq W] (k : W → W → ℝ≥0∞) (p : ℕ)
    (x w : W) : ℝ≥0∞ :=
  ∑ A ∈ markedShapes p,
    ∑' ζ : A.1.LeafPos → W, (if ζ A.2 = w then 1 else 0) * I417Base.wtE k A.1 ζ x

/-- **The per-shape marked diagram sum in label form**: for every marked labelled shape, the
atlas product `∏_e k (src e) (dst e)` (summed over the assignments of vertices to the internal
positions of the shape) with the leaf labels summed over and the mark pinned at `w`. -/
noncomputable def labelledMarkedDiagram {W : Type u} [DecidableEq W] (k : W → W → ℝ≥0∞)
    (p : ℕ) (x w : W) : ℝ≥0∞ :=
  ∑ t : LTon (Label p) Finset.univ,
    ∑' y : Label p → W,
      (if y (markLabel p) = w then 1 else 0) *
        PercLib.CriticalLRP.TreeExpansion.Real.posSumWtE k t.1 y x

/-- **The finite diagram expression**: the marked family collapsed by marked depth,

  `∑_{ℓ=1}^{p+1} markedCount p ℓ · χ^(2p+1-ℓ) · T^ℓ(x,w)`.

The index set is `Icc 1 (p+1)` because a leaf of a `p+1`-leaf tree has depth between `1` and
`p+1` (`depth_pos`, `RTree.depth_le_numLeaves`); the coefficient `markedCount p ℓ` is an
explicit `Finset.card`, not an assumed integer. -/
noncomputable def markedPolygonBound {W : Type u} [DecidableEq W] (χ : ℝ≥0∞)
    (k : W → W → ℝ≥0∞) (p : ℕ) (x w : W) : ℝ≥0∞ :=
  ∑ ℓ ∈ Finset.Icc 1 (p + 1),
    (markedCount p ℓ : ℝ≥0∞) * (χ ^ (2 * p + 1 - ℓ) * I417Base.iterPow k ℓ x w)

end PercLib.CriticalLRP.I417Marked
