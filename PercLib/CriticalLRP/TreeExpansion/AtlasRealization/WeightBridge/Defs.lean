/- Integrated from independently rebuilt Ultramath work.
Production base 50c2eed0682a7e1b078ae771dbef463ebe00701d.
Scratch source: repository-root .ultramath/.
-/

/-
Weight/positions bridge between the atlas realization of `TreeExpansion.AtlasRealization`
and the ordinary tree weight of `TreeExpansion.Weight` / `Correlation.I417.Base`.
-/

/-
# The atlas-side weight and the ordinary tree weight

The generalized tree-graph inequality (Lemma I.4.16) and the marked-leaf Lemma I.4.17 of

  T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
  arXiv:2508.18807v1,

are proved by expanding a connection event into a union over "tree diagrams": a rooted binary
shape `t` whose internal vertices carry vertices of the graph, together with one connection per
edge of the atlas `AEdge t` of the shape.  Two sums then arise:

* the **atlas-side weight** `posSumWt k t y c`, the sum over the internal positions `φ` of the
  product of `k` over the `2p - 1` atlas edges, with the root leaf pinned at `c` and the leaf
  labelled `a` pinned at `y a`;
* the **tree-graph weight** `RTree.wtL k t y c` (finite vertex set, `ℝ`) and `I417Base.wtE`
  (arbitrary vertex set, `ℝ≥0∞`), the sum over the values at the internal vertices of the
  product of `k` over the `2p - 1` edges of the rooted tree itself.

`WeightBridge.Bridge` proves that the two agree exactly, for every shape and every label map.
That is the step the atlas covering theorem (`AtlasRealization.Cover`) leaves open: its own
report states that "regrouping the product ... and summing over the internal positions to
produce `RTree.wt`" is not performed there.

Nothing here weakens a source bound or adds a hypothesis: `posSumWt` is a definitional reading of
the quantity that the union bound of `Cover.prob_le_sum_shapes` produces.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Defs
public import PercLib.CriticalLRP.TreeExpansion.LabelledWeights
public import PercLib.CriticalLRP.Correlation.I417.Base.Defs

/-! The atlas-side weight, over a finite and over an arbitrary vertex set. -/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

open scoped ENNReal

namespace PercLib.CriticalLRP.TreeExpansion.Real

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {α : Type*} [DecidableEq α]

/-- The **atlas-side weight** of the shape `t` with leaf labels `y` and root leaf at `c`: the
sum over all assignments `φ` of vertices to the internal positions of `t` of the product of the
kernel `k` over the `2 * #t.leaves - 1` atlas edges of `t`, the atlas edge `e` contributing
`k (srcPos t φ c e) (dstPos t φ y e)`.

This is exactly the quantity produced by the covering + BK union bound of
`AtlasRealization.Cover.prob_le_sum_shapes` for the kernel `k a b = P(a ↔ b)`, and
`WeightBridge.Bridge.posSumWt_eq_wtL` identifies it with the ordinary tree weight
`RTree.wtL k t y c`. -/
noncomputable def posSumWt (k : V → V → ℝ) (t : RTree α) (y : α → V) (c : V) : ℝ :=
  ∑ φ : t.IPos → V, ∏ e : AEdge t, k (srcPos t φ c e) (dstPos t φ y e)

section Infinite

variable {W : Type*}

/-- The atlas-side weight `posSumWt` with values in `ℝ≥0∞` and **no finiteness of the vertex
set**: the sum over internal positions is an `ℝ≥0∞`-valued `tsum`, so it applies to the
countable canonical model of Lemma I.4.17, where the two-point function may take the value `⊤`
and the vertex set is countably infinite.  This is the counterpart of `I417Base.wtE`, and
`WeightBridge.Bridge.posSumWtE_eq_wtE` identifies the two. -/
noncomputable def posSumWtE (k : W → W → ℝ≥0∞) (t : RTree α) (y : α → W) (c : W) : ℝ≥0∞ :=
  ∑' φ : t.IPos → W, ∏ e : AEdge t, k (srcPos t φ c e) (dstPos t φ y e)

end Infinite

/-- For a finite label type `α`, the shapes whose leaf set is *all* of `α` (`LTon α univ`)
are the fully labelled trees `RTree.LT α`.  The two conditions `leaves.toFinset = univ` and
`leaves.length = card α` (together with `Nodup`) are equivalent.

This is a pure bookkeeping equivalence between the shape family of the atlas covering theorem
and the shape family of `treeSum` (the tree sum of (I.2.2)); it introduces no new shapes. -/
noncomputable def ltonUnivEquivLT (α : Type*) [Fintype α] [DecidableEq α] :
    LTon α (Finset.univ : Finset α) ≃ RTree.LT α where
  toFun t :=
    ⟨t.1, t.2.1, by
      rw [← List.toFinset_card_of_nodup t.2.1, t.2.2, Finset.card_univ]⟩
  invFun t :=
    ⟨t.1, t.2.1, by
      have hnodup : t.1.leaves.Nodup := t.2.1
      have hlen : t.1.leaves.length = Fintype.card α := t.2.2
      have hcard : t.1.leaves.toFinset.card = (Finset.univ : Finset α).card := by
        rw [List.toFinset_card_of_nodup hnodup, hlen, Finset.card_univ]
      exact Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (le_of_eq hcard.symm)⟩
  left_inv t := Subtype.ext rfl
  right_inv t := Subtype.ext rfl

end PercLib.CriticalLRP.TreeExpansion.Real
