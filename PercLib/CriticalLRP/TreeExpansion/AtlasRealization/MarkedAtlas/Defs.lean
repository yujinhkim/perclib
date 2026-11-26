/- Independently rebuilt and verified at production revision
    eb9b71a3cf20a0fe9906271415f5b17efd80f5ad.
    Original scratch source is recorded below. -/
/-
Direction A of swarm `smwwt6noq`: the **finite marked atlas** at production HEAD
`4c53bb5a8e76a4358a426adf71169b916b90f51f` (source tree
`.scratch/critical-lrp-orchestration`, base revision 4c53bb5).

Source: T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.17 and its proof (p. 45): tree diagrams with two pinned
vertices at `x` and `y`, total edge number `2p+2q+1`, of which `ℓ` lie on the path
connecting `x` and `y`.  The **base factor** of every such diagram is a marked moment

    `E[|K_x|^p 1(w ∈ K_x)]`,

i.e. `p` unmarked arms at `x` together with **one leaf pinned at `w`**.  This file fixes the
definitions for that marked factor on the *finite* side: a finite edge set `E` with a finite
vertex set `V`, the finite Bernoulli law `prob pr` of `PercLib.CriticalLRP.TreeGraph.ThreePoint`,
and the atlas of `PercLib.CriticalLRP.TreeExpansion.Real`.

## Modelling choices, and why they are faithful

* **The label type.**  `MarkLabel p = Fin p ⊕ PUnit` has one label per arm and one label for
  the mark; `markLabels p = univ` uses *all* of them, so every labelled shape in
  `LTon (MarkLabel p) (markLabels p)` has exactly `p + 1` leaves and `2 * (p + 1) - 1 = 2p + 1`
  atlas edges, matching the source's `2p+2q+1` with `q = 0` and the `+1` of the marked leaf.
  `p = 0` is a genuine value here: then `MarkLabel 0 = PUnit` is a singleton and the shape
  family has one element.

* **The marked terminal map.**  `markTerm f w` sends label `Sum.inl i` to `f i` and the mark
  `Sum.inr ⟨⟩` to `w`.  It is not assumed injective: two arms may coincide with each other or
  with the mark, and any of them may equal the root vertex `x`.  Nothing downstream assumes
  injectivity, so those coincidences are handled by the degenerate branch split of
  `Real.exists_split` (empty arm witnesses, factor `P(w ↔ w) = 1`), not excluded.

* **The marked leaf position.**  `markPos t a ha` is the leaf position of `t` carrying the
  label `a`, obtained from the production leaf API `RTree.exists_leafOfPos`.  The leaf ends of
  the atlas are *not* free: they are the terminal values `y a`, so pinning the leaf `a` pins
  its terminal at `w`.  The marked leaf is unique because `LTon` leaf lists are `Nodup`
  (`markPos_unique` in `Bound.lean`).

* **The marked depth.**  `markDepth c t hc = RTree.depth t (markPos t c hc)` is the number of
  atlas edges on the root-to-mark path, the source's `ℓ`.  The decomposition of the finite
  diagram sum by `ℓ` is `Bound.prob_markedBase_le_markedBound`, whose coefficients are finite
  sums over shapes and internal positions (`markCoeff`), **not** a `wt`/`wtL` equality.

* **What is deliberately not defined here.**  No infinite-volume measure, no `edgeMeasure`, no
  `(2p-1)!!` coefficient, and no statement identifying `markBound` with `χ^(2p+1-ℓ) T^ℓ(x,w)`:
  that evaluation is Direction B (`tsum_wtE_marked`) plus the `ℝ`/`ℝ≥0∞` bridge, and is not
  claimed in this direction.

Definitions only in this file; every result is in `Bound.lean` and `Example.lean`.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Cover
public import PercLib.CriticalLRP.TreeExpansion.Moments
public import PercLib.CriticalLRP.TreeExpansion.PathWeightedTreeSum

/-! # The finite marked atlas: definitions -/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace PercLib.CriticalLRP.MarkedAtlas

open Finset
open PercLib.CriticalLRP.TreeExpansion (RTree LTon)
open PercLib.CriticalLRP.TreeExpansion.Real
open PercLib.CriticalLRP.TreeGraph (Conn prob)

variable {V : Type*} {E : Type*}

/-! ## Labels and terminals -/

/-- The labels of the marked base diagram: `p` unmarked arms `Fin p` and one mark.  It is an
abbreviation so that all the `Fintype`/`DecidableEq` instances of the sum type are inherited,
and so that the label type of `p = 0` is literally `PUnit`. -/
abbrev MarkLabel (p : ℕ) : Type := Fin p ⊕ PUnit

/-- The marked terminal map: arm `i` sits at `f i`, the mark sits at `w`.  No injectivity is
assumed or needed. -/
def markTerm {V : Type*} {p : ℕ} (f : Fin p → V) (w : V) : MarkLabel p → V
  | Sum.inl i => f i
  | Sum.inr _ => w

@[simp] theorem markTerm_inl {p : ℕ} (f : Fin p → V) (w : V) (i : Fin p) :
    markTerm f w (Sum.inl i) = f i := rfl

@[simp] theorem markTerm_mark {p : ℕ} (f : Fin p → V) (w : V) (u : PUnit) :
    markTerm f w (Sum.inr u) = w := rfl

/-- The label carrying the mark. -/
def markLabelOf {p : ℕ} : MarkLabel p := Sum.inr ⟨⟩

@[simp] theorem markTerm_labelOf {p : ℕ} (f : Fin p → V) (w : V) :
    markTerm f w (markLabelOf (p := p)) = w := rfl

/-- The marked label set: every label is used exactly once in this injectively labelled
family. No exact double-factorial cardinality theorem is assumed for this family. -/
def markLabels (p : ℕ) : Finset (MarkLabel p) := Finset.univ

theorem markLabels_card (p : ℕ) : (markLabels p).card = p + 1 := by
  simp [markLabels]

theorem markLabelOf_mem (p : ℕ) : markLabelOf (p := p) ∈ markLabels p :=
  Finset.mem_univ _

/-! ## The marked base event and the two-point function -/

variable [Fintype E] [DecidableEq E]

/-- **The marked base event.**  The root `x` is connected by open edges (inside the
configuration `ω`) to every arm `f i` and to the mark `w`.  This is the event whose
probability is the base factor `E[|K_x|^p 1(w ∈ K_x)]` of the marked diagrams of Lemma
I.4.17; it is stated for all `p : ℕ`, including `p = 0`, and it is not assumed that the
terminal values `f i`, `w`, `x` are distinct. -/
def MarkedBaseEvent (ends : E → Sym2 V) (x : V) {p : ℕ} (f : Fin p → V) (w : V) :
    Set (Finset E) :=
  {ω | ∀ a ∈ markLabels p, Conn ends ω x (markTerm f w a)}

/-- The probability that `a` and `b` are connected by open edges under the finite Bernoulli
law `pr`.  This is `prob pr` of a single two-point connection event, the `T(x,y)` of the
source at the level of the finite law. -/
noncomputable def pconn (pr : E → ℝ) (ends : E → Sym2 V) (a b : V) : ℝ :=
  prob pr {ω : Finset E | Conn ends ω a b}

/-! ## The marked leaf position -/

variable {α : Type*}

/-- The leaf position of `t` carrying the label `a`, chosen from the leaf list by
`RTree.exists_leafOfPos`.  Because `LTon` leaf lists are injective, this position is unique
(`markPos_unique`). -/
noncomputable def markPos (t : RTree α) (a : α) (ha : a ∈ t.leaves) : t.LeafPos :=
  Classical.choose (RTree.exists_leafOfPos t a ha)

variable [DecidableEq α]

/-- **The marked depth** `ℓ`: the number of edges on the tree path from the root to the leaf
carrying the mark `c`, for a shape whose leaf labels are exactly `Z` and `c ∈ Z`.  This is the
source's "some number `ℓ` of which belong to the path connecting `x` and `y`". -/
noncomputable def markDepth {Z : Finset α} (c : α) (t : LTon α Z) (hc : c ∈ Z) : ℕ :=
  RTree.depth t.1 (markPos t.1 c (by rw [← List.mem_toFinset, t.2.2]; exact hc))

/-! ## The finite marked diagram, coefficient and bound -/

variable [Fintype V] [DecidableEq V] [Fintype α]

/-- The row sum of the finite two-point kernel at `u`: the finite analogue of
`χ = E|K| = ∑_v T(u,v)`, which the marked diagram evaluation reduces each summed ordinary leaf
to (via transitivity in the source; here it is simply a definition, so no constant-row-sum
hypothesis is needed). -/
noncomputable def rowSum (pr : E → ℝ) (ends : E → Sym2 V) (u : V) : ℝ :=
  ∑ v : V, pconn pr ends u v

/-- **The finite marked diagram of one labelled shape.**  The root is at `x`, the leaf ends are
the terminal values `y a` (so the leaf carrying the mark is pinned at `y c = w`, while the other
leaves keep their values), the internal vertices are summed over the finite vertex set `V`, and
each of the `2 #Z - 1` atlas edges contributes its connection probability.  This is the finite
`ℝ`-valued analogue of the diagram sum of Lemma I.4.16/17, with one leaf pinned. -/
noncomputable def markDiag (pr : E → ℝ) (ends : E → Sym2 V) (x : V) (y : α → V)
    {Z : Finset α} (t : LTon α Z) : ℝ :=
  ∑ φ : t.1.IPos → V, ∏ e : AEdge t.1, prob pr (ConnEvent ends y x t.1 φ e)

/-- **The finite marked coefficient at marked depth `ℓ`.**  The sum of the marked diagrams of
all labelled shapes on `Z` whose marked leaf hangs at depth `ℓ`.  It is a finite sum
(`Finset.univ.filter` over the finite shape family `LTon α Z` and over the finite internal
position space), with the mark pinned and the ordinary leaves carried by `y`. -/
noncomputable def markCoeff (pr : E → ℝ) (ends : E → Sym2 V) (x : V) (y : α → V) (c : α)
    {Z : Finset α} (hc : c ∈ Z) (ℓ : ℕ) : ℝ :=
  ∑ t ∈ Finset.univ.filter (fun t : LTon α Z => markDepth c t hc = ℓ), markDiag pr ends x y t

/-- **The finite marked diagram expression**: the marked coefficient summed over all depths
that can occur (`1 ≤ ℓ ≤ #Z`). -/
noncomputable def markBound (pr : E → ℝ) (ends : E → Sym2 V) (x : V) (y : α → V) (c : α)
    {Z : Finset α} (hc : c ∈ Z) : ℝ :=
  ∑ ℓ ∈ Finset.range (Z.card + 1), markCoeff pr ends x y c hc ℓ

/-- The marked diagram expression specialised to the base factor: labels `Fin p ⊕ PUnit`,
all labels used, the mark at `w`, the arms at `f`. -/
noncomputable def markedBound (pr : E → ℝ) (ends : E → Sym2 V) (x : V) {p : ℕ}
    (f : Fin p → V) (w : V) : ℝ :=
  markBound pr ends x (markTerm f w) (markLabelOf (p := p)) (markLabelOf_mem p)

/-- The three-point diagram of the two-leaf shapes: root `x`, branch point `u`, arms at `a`
and `b`.  This is the shape of the `p = 1` marked bound. -/
noncomputable def threePoint (pr : E → ℝ) (ends : E → Sym2 V) (x u a b : V) : ℝ :=
  pconn pr ends x u * pconn pr ends u a * pconn pr ends u b

end PercLib.CriticalLRP.MarkedAtlas
