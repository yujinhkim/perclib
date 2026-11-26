/-
Independently built probabilistic assembly for swarm `smwwtd5t5`, member `m1`
(direction A).

## What this file proves, and what it takes as an explicit input

`Cover.lean` proves the *deterministic* covering statement of Lemma I.4.16 of Hutchcroft,
*Critical long-range percolation I: High effective dimension*, arXiv:2508.18807v1, pp. 43--45, in
the canonical countable model:

  `I417A.labelEvent x f ⊆ ⋃ (t, φ), CanonAtlasEvent f x t φ`   (`labelEvent_subset_canonCover`)

with the atlas event indexed by the *finite* shape family `LTon (Fin q) Finset.univ` and the
countable position space `t.IPos → V`.  This file takes the two remaining measure-theoretic steps,

  1. countable subadditivity of `edgeMeasure π` over that cover, and
  2. the BK product bound for one atlas diagram,

and obtains the exact measure bound that the source's union-bound step produces:

  `edgeMeasure π (labelEvent x f) ≤ ∑' (t, φ), ∏ e : AEdge t, edgeMeasure π (connSet e-ends)`.

Step 1 is proved here from `measure_iUnion_le`; it uses only the countability of the index type
(proved in `Cover.countable_atlasIndex`) and, notably, needs **no measurability** of the atlas
events, no interchange of sum and limit, and no finite truncation of the union --
`measure_iUnion_le` is the honest countable subadditivity of a measure.

Step 2 is *not* proved here: it is the per-diagram BK inequality for the canonical iterated
disjoint-occurrence law at the finite index type `Real.AEdge t`, i.e. Reimer's inequality applied to
the `2q - 1` connection events `connSet (srcPos ..) (dstPos ..)`.  It is taken as the explicit
hypothesis `hBK`, one diagram at a time, with the product over the actual atlas edges -- this is
exactly the statement that direction B of this swarm is building from
`PercLib.CriticalLRP.edgeMeasure_bk_list`.  It is *not* the desired bound restated: the desired
bound is the tree-graph moment inequality, whereas `hBK` is the single-diagram BK inequality, a
strictly weaker standard input.  Everything else in the chain is proved.

The diagonal case `u = v` needs no separate treatment here and no fictitious edge: `connSet u u` is
the whole space (production `measure_connSet_self`), and a degenerate atlas edge, whose two ends
coincide, has a *proved* empty witness (`srcPos_eq_dstPos_of_wit_eq_empty`) -- so the factor `1` is
honest rather than an artefact of an empty product over `Sym2 V`.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Canonical.Cases

/-!
# From the deterministic cover to the measure bound
-/

@[expose] public section

open scoped ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace CanonAtlas

open Finset

open PercLib.CriticalLRP (Config Connects connSet edgeMeasure)

open PercLib.CriticalLRP.TreeExpansion (RTree LTon)

open PercLib.CriticalLRP.TreeExpansion.Real (AEdge srcPos dstPos)

namespace Measure

variable {V : Type*} [DecidableEq V] [Countable V]

/-- The product of connection probabilities attached to the atlas edges of a shape at positions
`φ`, i.e. the right-hand side of the BK inequality for the diagram `(t, φ)`. -/
noncomputable def atlasProduct (π : Sym2 V → unitInterval) {q : ℕ} (x : V) (f : Fin q → V)
    (t : RTree (Fin q)) (φ : t.IPos → V) : ℝ≥0∞ :=
  ∏ e : AEdge t, edgeMeasure π (connSet (srcPos t φ x e) (dstPos t φ f e))

/-- **The union-bound step of Lemma I.4.16 in the canonical countable model.**

Given the per-diagram BK bound `hBK` (one diagram at a time, product over the `2q - 1` actual atlas
edges), the probability that the root `x` is connected to all `q` labelled terminals is at most the
sum over all fully labelled shapes `t` and all positions `φ` of the internal vertices of the BK
product of `t` at `φ`.

No finiteness of `V`, no truncation of the configuration, no measurability hypothesis and no
interchange of limits is used: the cover is countable and the bound is countable subadditivity. -/
theorem measure_labelEvent_le_tsum (π : Sym2 V → unitInterval) {q : ℕ} (hq : 1 ≤ q) (x : V)
    (f : Fin q → V)
    (hBK : ∀ (t : LTon (Fin q) Finset.univ) (φ : t.1.IPos → V),
      edgeMeasure π (CanonAtlasEvent f x t.1 φ) ≤ atlasProduct π x f t.1 φ) :
    edgeMeasure π (PercLib.CriticalLRP.I417A.labelEvent x f) ≤
      ∑' p : (Σ t : LTon (Fin q) Finset.univ, t.1.IPos → V),
        atlasProduct π x f p.1.1 p.2 := by
  calc edgeMeasure π (PercLib.CriticalLRP.I417A.labelEvent x f)
      ≤ edgeMeasure π (CanonCover q f x) :=
        MeasureTheory.measure_mono (labelEvent_subset_canonCover x hq f)
    _ = edgeMeasure π (⋃ p : (Σ t : LTon (Fin q) Finset.univ, t.1.IPos → V),
          CanonAtlasEvent f x p.1.1 p.2) := rfl
    _ ≤ ∑' p : (Σ t : LTon (Fin q) Finset.univ, t.1.IPos → V),
          edgeMeasure π (CanonAtlasEvent f x p.1.1 p.2) :=
        MeasureTheory.measure_iUnion_le _
    _ ≤ ∑' p : (Σ t : LTon (Fin q) Finset.univ, t.1.IPos → V),
          atlasProduct π x f p.1.1 p.2 :=
        ENNReal.tsum_le_tsum fun p => hBK p.1 p.2

/-- The bound of `measure_labelEvent_le_tsum` with the sum split into the shape sum and, for each
shape, the sum over the positions of its internal vertices -- the shape in which the source writes
the union bound, and the form in which the positional sum can subsequently be recognised as the
tree weight `RTree.wt`. -/
theorem measure_labelEvent_le_tsum_shapes (π : Sym2 V → unitInterval) {q : ℕ} (hq : 1 ≤ q)
    (x : V) (f : Fin q → V)
    (hBK : ∀ (t : LTon (Fin q) Finset.univ) (φ : t.1.IPos → V),
      edgeMeasure π (CanonAtlasEvent f x t.1 φ) ≤ atlasProduct π x f t.1 φ) :
    edgeMeasure π (PercLib.CriticalLRP.I417A.labelEvent x f) ≤
      ∑' t : LTon (Fin q) Finset.univ, ∑' φ : t.1.IPos → V, atlasProduct π x f t.1 φ := by
  refine (measure_labelEvent_le_tsum π hq x f hBK).trans (le_of_eq ?_)
  exact ENNReal.tsum_sigma
    (f := fun (t : LTon (Fin q) Finset.univ) (φ : t.1.IPos → V) => atlasProduct π x f t.1 φ)

end Measure

end CanonAtlas
