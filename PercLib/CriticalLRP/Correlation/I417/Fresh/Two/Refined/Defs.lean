/-
Independently rebuilt and integrated from the accepted `smwx5p94b/m1` artifact
`.ultramath/smwx5p94b/m1/M1Fresh`. Production integration revision:
`9c345df8dcb6d4027a2e61d7a7785abf4df111cf`. The coordinator assigns the production
namespace and fully qualified imports; the mathematical statements are unchanged.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Two.Poly.Main
public import PercLib.CriticalLRP.Correlation.I417Example.Branch


/-!
Independently built for swarm `smwx5p94b`, member `m1`, direction Q2-FRESH-NORMALIZATION.

# Lemma I.4.17, `q = 2`: the four-edge fresh-side shapes and the refined fresh polynomial

Source: T. Hutchcroft, *Critical long-range percolation I: high effective dimension*,
arXiv:2508.18807v1, Lemma I.4.17 and its proof (supplied PDF pp. 45--46).  The proof splits the
two-copy moment difference into a marked factor on the base copy and a **fresh-copy factor**

  `F(y,w) = ∑_{y₁,…,y_q} P(y₁,…,y_q ∈ K̃_y, w on a simple open path connecting y to {y₁,…,y_q})`,

and then states that the tree expansion has `2p + 2q + 1` edges in total, `ℓ` of them on the path
joining the two pinned vertices, with `3 ≤ ℓ ≤ p + q + 1`.

The marked side is `2p + 1` edges (`I417/MarkedJoint/Transversal/Depth`).  Hence the printed
fresh side carries **`2q`** edges.  At `q = 2` that is four edges, exactly the count of a rooted
binary tree with the two labelled arms as leaves and the mark `w` *subdividing* one of its three
edges.  The fresh event already supplies that subdivision: `w` lies on an open path from `y` to
the arm `g j`, so the two halves `y → w` and `w → g j` are edge-disjoint
(`I417Gen.freshMark = DisjointOccurrence (connSet y w) (connSet w (g j)) ∩ labelEvent y g`).

The two four-edge shapes produced by `exists_refined_branch` are, with `p` a summed
vertex and `j'` the other arm label,

* `ShapeA` : `{y↔p} ∘ {p↔w} ∘ {w↔g j} ∘ {p↔g j'}`   (`w` at depth two, the arm at depth one),
* `ShapeB` : `{y↔w} ∘ {w↔p} ∘ {p↔g j} ∘ {p↔g j'}`   (`w` at depth one, the arm at depth two).

Summed over the two arms and `p` these evaluate to `χ²T²(w,y)` and `χ³T(w,y)`; both have exactly
four two-point factors and `y`-legs of length `2` and `1`.  Composing with the marked side then
gives total exponent `(2p+1) + 4 = 2p+5` and `T`-powers `ℓ + 2 ∈ [4, p+3]`, `ℓ + 1 ∈ [3, p+2]`,
both inside the printed range `3 ≤ ℓ ≤ p + q + 1 = p + 3`.

Definitions only in this file.  Nothing here is a paper theorem on its own.
-/
open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

@[expose] public section

namespace PercLib.CriticalLRP.I417FreshTwo.Refined

open PercLib.CriticalLRP

variable {V : Type*} [Countable V]

attribute [local instance] Classical.propDecidable

/-- **Four-fold disjoint occurrence** of the events `A, B, C, D`: the configuration carries four
pairwise disjoint finite witnesses, one for each event. -/
def Tree4 (A B C D : Set (Config V)) : Set (Config V) :=
  Percolation.DisjointOccurrenceFin (fun i : Fin 4 => ![A, B, C, D] i)

/-- **Fresh shape A**: the spine `y → p → w` with the mark `w` at depth two, and the two arms
hanging at `w` and at `p`.  Four edge events, all disjoint. -/
def ShapeA (y w g0 g1 p : V) : Set (Config V) :=
  Tree4 (connSet y p) (connSet p w) (connSet w g0) (connSet p g1)

/-- **Fresh shape B**: the spine `y → w → p` with the mark `w` at depth one and both arms hanging
at `p`.  Four edge events, all disjoint. -/
def ShapeB (y w g0 g1 p : V) : Set (Config V) :=
  Tree4 (connSet y w) (connSet w p) (connSet p g0) (connSet p g1)

/-- **The refined `q = 2` fresh majorant**: `χ²·T²(w,y) + χ³·T(w,y)`.  Both monomials carry
exactly four two-point factors, i.e. the printed `2q = 4`; the `y`-legs have length `2` and `1`. -/
noncomputable abbrev freshTwoRefined (π : Sym2 V → unitInterval) (χ : ℝ≥0∞) (y w : V) : ℝ≥0∞ :=
  χ ^ 2 * (∑' z : V, I417Fresh.tau π w z * I417Fresh.tau π z y) + χ ^ 3 * I417Fresh.tau π w y

end PercLib.CriticalLRP.I417FreshTwo.Refined
