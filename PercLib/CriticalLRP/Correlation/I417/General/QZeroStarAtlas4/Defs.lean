/-
Ultramath swarm `smwziumdb`, member `m7`, direction `d4`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwziumdb`.
Supporting integration based on production commit `5d2d681b941eb1c687f1ba17e6a798b8f0175aa0`.

# The four-label canonical atlas of the `q = 0`, `p = 3` star of Lemma I.4.17

Source: T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.17 (p. 45) and its proof (pp. 45-46), together with the
tree-graph inequality (I.2.2) of Section I.2.1 (p. 22) and Proposition I.4.15 Case 3 (p. 47),
whose numerator is `E_{β_c,r}[|K|³ |K ∩ B_r|] = ∑_{y ∈ B_r} E[|K_0|³ 1(y ∈ K_0)]`.

At `(p,q) = (3,0)` the mark set `{y_1,…,y_q}` of the printed proof is empty, so the printed
union bound (which marks a vertex on a path from `y` to that set) degenerates; the object that
survives is the **one-copy star moment** `I417Gen.starMoment π x y 3 = E[|K_x|³ 1(x ↔ y)]`
(`Correlation/I417/General/QZeroStar`), which is the `(3+1)`-point event
`{x_1, x_2, x_3, y ∈ K_x}` summed over `x_1, x_2, x_3`
(`I417Gen.starMoment_eq_tsum_labelEvent`).

This file fixes the **atlas side** of that event in the canonical countable model
`Config V = Set (Sym2 V)`: the terminal tuple `(x_1, x_2, x_3, y)` is the leaf labelling
`Fin 4 → V` that puts the mark `y` at the last label, and the diagram family is production's
canonical atlas sum `CanonAtlas.Measure.atlasProduct`, indexed by the fully labelled shapes
`TreeExpansion.LTon (Fin 4) Finset.univ` (fifteen rooted binary trees on four labels) and by
the positions `t.IPos → V` of their internal vertices.  Products are over the `2·4 − 1 = 7`
atlas edges, which is the source's edge count `2p + 2q + 1` at `p = 3`, `q = 0`.

`Main.lean` proves the realization `starMoment π x y 3 ≤ starAtlasSum π x y` in this model from
the production covering + BK chain (`CanonAtlas.Measure.measure_labelEvent_le_tsum_shapes_bk`),
with no hypothesis beyond `π e < 1`; the `ℓ = 2` class that makes the printed range
`3 ≤ ℓ ≤ p+q+1` false at `q = 0` is *kept*, not removed.

Definitions only in this file; every result is in `Main.lean`.
-/
module

public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Canonical.Join
public import PercLib.CriticalLRP.Correlation.I417.General.QZeroStar.Main
public import PercLib.CriticalLRP.Correlation.I417.Base.Depth
public import PercLib.CriticalLRP.Correlation.I417Example.Trans
public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Canonical.Transversal
public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.MarkedAtlas.Defs

/-! # The canonical four-label star atlas -/

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

open PercLib.CriticalLRP.TreeExpansion

@[expose] public section

namespace PercLib.CriticalLRP.QZeroStarAtlas4

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Countable V]

/-- **The leaf labelling of the `(p,q) = (3,0)` star.**  The three arms `x_1, x_2, x_3` are the
labels `0, 1, 2` and the mark `y` is the last label `3`; `Fin.snoc` is the source's
"`x_1, …, x_p` together with `y`". -/
def starLabels (f : Fin 3 → V) (y : V) : Fin 4 → V :=
  Fin.snoc (n := 3) (α := fun _ => V) f y

@[simp] theorem starLabels_castSucc (f : Fin 3 → V) (y : V) (i : Fin 3) :
    starLabels f y i.castSucc = f i :=
  Fin.snoc_castSucc (n := 3) (α := fun _ => V) (p := f) (x := y) i

@[simp] theorem starLabels_three (f : Fin 3 → V) (y : V) :
    starLabels f y (3 : Fin 4) = y :=
  Fin.snoc_last (n := 3) (α := fun _ => V) (p := f) (x := y)

/-- The value at the last label, in the `Fin.last` form used by `Fin.lastCases`. -/
theorem starLabels_last (f : Fin 3 → V) (y : V) :
    starLabels f y (Fin.last 3) = y :=
  starLabels_three f y

/-- **The canonical atlas sum of the `q = 0`, `p = 3` star.**  Sum over the three arms
`x_1, x_2, x_3`, then over the fifteen fully labelled shapes on the four labels
`(x_1, x_2, x_3, y)`, then over the positions of the internal vertices, of the product of the
two-point function over the `2·4 − 1 = 7` atlas edges of the shape.

This is the right-hand side that the four-label tree-graph realization has to produce; the mark
`y` is *pinned* (it is the value of the last leaf label, never summed over), which is exactly
what keeps the `ℓ`-fold chain `k^ℓ(x,y)` of Lemma I.4.17 in the diagram values. -/
noncomputable def starAtlasSum (π : Sym2 V → unitInterval) (x y : V) : ℝ≥0∞ :=
  ∑' f : Fin 3 → V,
    ∑' t : PercLib.CriticalLRP.TreeExpansion.LTon (Fin 4) Finset.univ,
      ∑' φ : t.1.IPos → V,
        CanonAtlas.Measure.atlasProduct π x (starLabels f y) t.1 φ

/-! ## Splitting the last label off a four-label tuple -/

/-- **Splitting the last label off.**  A four-label tuple is its last value together with its
first three values; this is the index change that turns the pinned-mark sum over
`Fin 3 → V` into a sum over all of `Fin 4 → V` with the last coordinate fixed. -/
def fin4Split (g : Fin 4 → V) : V × (Fin 3 → V) :=
  (g (Fin.last 3), fun i => g i.castSucc)

/-- The inverse of `fin4Split`: the last label is `p.1` and the first three are `p.2`. -/
def fin4Join (p : V × (Fin 3 → V)) : Fin 4 → V := starLabels p.2 p.1

theorem fin4Join_fin4Split (g : Fin 4 → V) : fin4Join (fin4Split g) = g := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact starLabels_last (fun i => g i.castSucc) (g (Fin.last 3))
  · exact starLabels_castSucc (fun i => g i.castSucc) (g (Fin.last 3)) j

theorem fin4Split_fin4Join (p : V × (Fin 3 → V)) : fin4Split (fin4Join p) = p := by
  obtain ⟨v, f⟩ := p
  refine Prod.ext ?_ ?_
  · exact starLabels_last f v
  · funext i
    exact starLabels_castSucc f v i

/-- `(Fin 4 → V) ≃ V × (Fin 3 → V)`, last coordinate first. -/
def fin4Equiv : (Fin 4 → V) ≃ V × (Fin 3 → V) where
  toFun := fin4Split
  invFun := fin4Join
  left_inv := fin4Join_fin4Split
  right_inv := fin4Split_fin4Join

/-! ## The two-point kernel and the marked depth of a four-label shape -/

/-- **The two-point function of the canonical model**, as an `ℝ≥0∞`-valued kernel:
`tauK π a b = P(a ↔ b)`.  Its row sums are `E|K| = meanVol` by transitivity. -/
noncomputable def tauK (π : Sym2 V → unitInterval) : V → V → ℝ≥0∞ :=
  fun a b => edgeMeasure π (connSet a b)

/-- **The marked depth** of a four-label shape: the length `ℓ` of the tree path from the root to
the leaf carrying the marked last label `3`.  This is the source's "some number `ℓ` of which
belong to the path connecting `x` and `y`"; at four labels it takes the values `1` to `4`, and
the class `ℓ = 2` is exactly the one absent from the printed range `3 ≤ ℓ ≤ p+q+1` at `q = 0`. -/
noncomputable def starDepth (t : PercLib.CriticalLRP.TreeExpansion.LTon (Fin 4) Finset.univ) : ℕ :=
  MarkedAtlas.markDepth (Fin.last 3) t (Finset.mem_univ _)

end PercLib.CriticalLRP.QZeroStarAtlas4
