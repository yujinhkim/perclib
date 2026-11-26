/-
Independently reviewed and integrated from the completed artifact `smwx6p0op/m1`
at `.ultramath/smwx6p0op/m1/M3Q`. Production integration revision:
`3cd318e5a37d0dc889f23bd3baf1b8884e651a27`. The coordinator uses the production
namespace and fully qualified imports; the proof covers `q = 3`, not arbitrary `q`.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.Defs
public import PercLib.CriticalLRP.Correlation.I417Example.Branch
public import PercLib.CriticalLRP.Correlation.I417.Fresh.Two.Poly.Main

/-!
Independently built for swarm `smwx6p0op`, member `m1`, direction Q3-MARK-ON-PATH-COVER.

# Lemma I.4.17 at `q = 3`: the six-edge mark-on-the-path fresh diagrams

Source: T. Hutchcroft, *Critical long-range percolation I: high effective dimension*,
arXiv:2508.18807v1, Lemma I.4.17 and its proof (paper text lines 2444--2464): "We obtain a bound
in terms of tree diagrams with two pinned vertices at `x` and `y`, with `2p + 2q + 1` edges in
total, some number `3 ≤ ℓ ≤ p + q + 1` of which belong to the path connecting `x` and `y`."

The marked side carries `2p + 1` edges, so the fresh side carries `2q`.  At `q = 3` that is **six**
two-point factors.  The diagram is a rooted binary tree with root the pin `y` and the three labelled
arms as leaves (`2q - 1 = 5` edges, all internal vertices of degree three), with the mark `w`
*subdividing* one edge of the path from `y` to the selected arm: `5 + 1 = 6`.  Up to relabelling
there are `(2q-3)!! = 3` such trees, and the path `y → g j` has 2 or 3 edges in them, so there are
`2 + 3 + 3 = 8` subdivided diagrams.  `legsA0`--`legsB3` below are exactly those eight, indexed by
which of the four segments of the `q = 2` diagram carries the second branch point `q`.

Conventions: `y` and `w` are the two pinned vertices (`y` the root, `w` the mark on the path),
`ga` is the selected arm `g j` (the one on the marked path), `gb` and `gc` are the two remaining
labelled arms, and `p`, `q` are the summed branch points.  Every diagram is written as a list of
six *connection events* `(start, end)`; each contributes exactly one two-point factor `τ`, and the
three arm ends are summed over, giving `χ³`.

The eight families, with `y`-leg length (distance from `y` to `w` in the diagram):

* `legsA0`: `y–q–p–w`, arms at `w`, `p`, `q`   (y-leg 3)
* `legsA1`: `y–p–q–w`, arms at `w`, `p`, `q`   (y-leg 3)
* `legsA2`: `y–p–w`, leaf `q` at `w`, arms at `q`, `p`, `q`   (y-leg 2)
* `legsA3`: `y–p–w`, leaf `q` at `p`, arms at `w`, `q`, `q`   (y-leg 2)
* `legsB0`: `y–q–w`, leaf `p` at `w`, arms at `p`, `p`, `q`   (y-leg 2)
* `legsB1`: `y–w`, chain `w–q–p`, arms at `p`, `p`, `q`   (y-leg 1)
* `legsB2`: `y–w`, chain `w–p–q`, arms at `q`, `p`, `q`   (y-leg 1)
* `legsB3`: `y–w`, chain `w–p–q`, arms at `p`, `q`, `q`   (y-leg 1)

Summed over the three arms and `p, q` these evaluate to `2χ³T³(w,y) + 3χ⁴T²(w,y) + 3χ⁵T(w,y)`:
eight monomials, each with exactly six two-point factors and `y`-leg `1 ≤ m ≤ 3`.

Definitions only in this file.
-/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

@[expose] public section

namespace PercLib.CriticalLRP.I417FreshThree.Refined

open PercLib.CriticalLRP

variable {V : Type*} [Countable V] [DecidableEq V]

attribute [local instance] Classical.propDecidable

/-! ## Six legs, six walks -/

/-- Six ordered pairs of vertices: the six connection events of a six-edge diagram. -/
def legs6 (a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 : V) : Fin 6 → V × V
  | 0 => (a0, b0)
  | 1 => (a1, b1)
  | 2 => (a2, b2)
  | 3 => (a3, b3)
  | 4 => (a4, b4)
  | 5 => (a5, b5)

/-- Six walks matching the six legs of `legs6`. -/
def walks6 {a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 : V}
    (W0 : (⊤ : SimpleGraph V).Walk a0 b0) (W1 : (⊤ : SimpleGraph V).Walk a1 b1)
    (W2 : (⊤ : SimpleGraph V).Walk a2 b2) (W3 : (⊤ : SimpleGraph V).Walk a3 b3)
    (W4 : (⊤ : SimpleGraph V).Walk a4 b4) (W5 : (⊤ : SimpleGraph V).Walk a5 b5) :
    (i : Fin 6) → (⊤ : SimpleGraph V).Walk ((legs6 a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 i).1)
      ((legs6 a0 b0 a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 i).2)
  | 0 => W0
  | 1 => W1
  | 2 => W2
  | 3 => W3
  | 4 => W4
  | 5 => W5

/-- The **six-fold disjoint occurrence** of a legs family: the configuration carries six pairwise
disjoint finite witnesses, one for each connection event.  This is
`Percolation.DisjointOccurrenceFin` written through the legs, so that a whole diagram family is a
single object. -/
def ShapeOf (L : Fin 6 → V × V) : Set (Config V) :=
  Percolation.DisjointOccurrenceFin (fun i => connSet (L i).1 (L i).2)

/-! ## The eight subdivided binary trees -/

/-- `y–q–p–w`, arms at `w`, `p`, `q`. -/
def legsA0 (y w ga gb gc p q : V) : Fin 6 → V × V :=
  legs6 y q q p p w w ga p gb q gc

/-- `y–p–q–w`, arms at `w`, `p`, `q`. -/
def legsA1 (y w ga gb gc p q : V) : Fin 6 → V × V :=
  legs6 p q q w y p w ga p gb q gc

/-- `y–p–w` with the leaf `q` at `w`; arms at `q`, `p`, `q`. -/
def legsA2 (y w ga gb gc p q : V) : Fin 6 → V × V :=
  legs6 w q q ga y p p w p gb q gc

/-- `y–p–w` with the leaf `q` at `p`; arms at `w`, `q`, `q`. -/
def legsA3 (y w ga gb gc p q : V) : Fin 6 → V × V :=
  legs6 p q q gb y p p w w ga q gc

/-- `y–q–w` with the leaf `p` at `w`; arms at `p`, `p`, `q`. -/
def legsB0 (y w ga gb gc p q : V) : Fin 6 → V × V :=
  legs6 y q q w w p p ga p gb q gc

/-- The edge `y–w` with the chain `w–q–p`; arms at `p`, `p`, `q`. -/
def legsB1 (y w ga gb gc p q : V) : Fin 6 → V × V :=
  legs6 w q q p y w p ga p gb q gc

/-- The edge `y–w` with the chain `w–p–q`; arms at `q`, `p`, `q`. -/
def legsB2 (y w ga gb gc p q : V) : Fin 6 → V × V :=
  legs6 p q q ga y w w p p gb q gc

/-- The edge `y–w` with the chain `w–p–q`; arms at `p`, `q`, `q`. -/
def legsB3 (y w ga gb gc p q : V) : Fin 6 → V × V :=
  legs6 p q q gb y w w p p ga q gc

/-! ## The fresh event family -/

/-- **The `q = 3` mark-on-the-path fresh diagram family**: the union over the two summed branch
points `p, q` of the eight six-edge subdivided binary trees.  The selected arm `ga = g j` sits on
the marked path `y → w → ga`; `gb`, `gc` are the other two arms. -/
def ShapeQ3 (y w ga gb gc : V) : Set (Config V) :=
  ⋃ p : V, ⋃ q : V,
    (ShapeOf (legsA0 y w ga gb gc p q) ∪ ShapeOf (legsA1 y w ga gb gc p q) ∪
      ShapeOf (legsA2 y w ga gb gc p q) ∪ ShapeOf (legsA3 y w ga gb gc p q) ∪
      ShapeOf (legsB0 y w ga gb gc p q) ∪ ShapeOf (legsB1 y w ga gb gc p q) ∪
      ShapeOf (legsB2 y w ga gb gc p q) ∪ ShapeOf (legsB3 y w ga gb gc p q))

/-- **The `q = 3` fresh-side majorant**: `2χ³T³(w,y) + 3χ⁴T²(w,y) + 3χ⁵T(w,y)`.  Every monomial
carries exactly `2q = 6` two-point factors; the `y`-legs have length `1, 2, 3`, inside the printed
range `3 ≤ ℓ ≤ p + q + 1` after composition with the `2p + 1`-edge marked side. -/
noncomputable def freshThreeRefined (π : Sym2 V → unitInterval) (χ : ℝ≥0∞) (y w : V) : ℝ≥0∞ :=
  2 * (χ ^ 3 * I417Base.iterPow (I417FreshTwo.kernel π) 3 w y) +
    3 * (χ ^ 4 * I417Base.iterPow (I417FreshTwo.kernel π) 2 w y) +
    3 * (χ ^ 5 * I417Base.iterPow (I417FreshTwo.kernel π) 1 w y)

/-- **The eight six-leg products**, in the order of `legsA0`--`legsB3`.  Each summand has exactly
six two-point factors: three arm legs (at `ga`, `gb`, `gc`) and the three legs of the tree
structure, which form a path from `y` to `w` of length `3` (`legsA0`, `legsA1`), a path of
length `2` with one free end (`legsA2`, `legsA3`, `legsB0`), or a path of length `1` with two free
ends (`legsB1`, `legsB2`, `legsB3`). -/
noncomputable def freshShapeSum (π : Sym2 V → unitInterval) (y w ga gb gc p q : V) : ℝ≥0∞ :=
  I417Fresh.tau π y q * I417Fresh.tau π q p * I417Fresh.tau π p w *
      I417Fresh.tau π w ga * I417Fresh.tau π p gb * I417Fresh.tau π q gc
  + I417Fresh.tau π p q * I417Fresh.tau π q w * I417Fresh.tau π y p *
      I417Fresh.tau π w ga * I417Fresh.tau π p gb * I417Fresh.tau π q gc
  + I417Fresh.tau π w q * I417Fresh.tau π q ga * I417Fresh.tau π y p *
      I417Fresh.tau π p w * I417Fresh.tau π p gb * I417Fresh.tau π q gc
  + I417Fresh.tau π p q * I417Fresh.tau π q gb * I417Fresh.tau π y p *
      I417Fresh.tau π p w * I417Fresh.tau π w ga * I417Fresh.tau π q gc
  + I417Fresh.tau π y q * I417Fresh.tau π q w * I417Fresh.tau π w p *
      I417Fresh.tau π p ga * I417Fresh.tau π p gb * I417Fresh.tau π q gc
  + I417Fresh.tau π w q * I417Fresh.tau π q p * I417Fresh.tau π y w *
      I417Fresh.tau π p ga * I417Fresh.tau π p gb * I417Fresh.tau π q gc
  + I417Fresh.tau π p q * I417Fresh.tau π q ga * I417Fresh.tau π y w *
      I417Fresh.tau π w p * I417Fresh.tau π p gb * I417Fresh.tau π q gc
  + I417Fresh.tau π p q * I417Fresh.tau π q gb * I417Fresh.tau π y w *
      I417Fresh.tau π w p * I417Fresh.tau π p ga * I417Fresh.tau π q gc

/-- **The arm reindexing**: for three distinct labels `a b c : Fin 3`, the triple of coordinates
`(g a, g b, g c)` runs over `V × V × V` exactly once.  This is what lets the three labelled arms of
a fresh diagram be summed out independently. -/
def armEquiv (a b c : Fin 3) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (Fin 3 → V) ≃ V × V × V where
  toFun g := (g a, g b, g c)
  invFun p := fun i => if i = a then p.1 else if i = b then p.2.1 else p.2.2
  left_inv g := by
    funext i
    by_cases hia : i = a
    · rw [hia]; simp
    by_cases hib : i = b
    · rw [hib]; simp [hab.symm]
    · have hic : i = c := by
        have h1 : i.val ≠ a.val := fun h => hia (Fin.ext h)
        have h2 : i.val ≠ b.val := fun h => hib (Fin.ext h)
        have h3 : c.val ≠ a.val := fun h => hac (Fin.ext h.symm)
        have h4 : c.val ≠ b.val := fun h => hbc (Fin.ext h.symm)
        have h5 := i.isLt
        have h6 := a.isLt
        have h7 := b.isLt
        have h8 := c.isLt
        exact Fin.ext (by omega)
      rw [hic]; simp [hac.symm, hbc.symm]
  right_inv p := by
    simp [hab.symm, hac.symm, hbc.symm]

end PercLib.CriticalLRP.I417FreshThree.Refined
