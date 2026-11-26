/- Independently rebuilt and integrated UltraMath package `smwwz58hv`, member `m1`.
Production integration revision: `4478d0f5a412be93a92b607d6e30a20cbd89bdb6`.
The accepted candidates were `.ultramath/smwwz58hv/m1/I417MarkedTransversal/`. -/

module

public import PercLib.CriticalLRP.Correlation.I417.MarkedJoint.Relabel.Main
public import PercLib.CriticalLRP.TreeExpansion.AtlasRealization.Canonical.Transversal

/-!
# The marked joint moment over one plane representative per child-swap orbit

Source: T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1, Lemma I.4.17 (arbitrary `p`), marked base side.

`PercLib.CriticalLRP.I417Marked.markedAtlasBound` sums over the whole family
`LTon (Fin (p+1)) Finset.univ` of fully labelled **plane** shapes: it keeps the plane
multiplicity `2^p`, the number of plane presentations of a non-plane `(p+1)`-leaf tree with
distinct labels.  The canonical covering theorem is available in the stronger orbit form
`CanonAtlas.measure_labelEvent_le_sum_transversal_bk`, which unions only over the transversal
`RTree.transversal (Fin (p+1))` (one plane representative per child-swap orbit).

This file introduces the marked transversal right-hand side that matches that bound, together
with the honest non-plane marked depth count: the number of child-swap orbits of fully labelled
`(p+1)`-leaf shapes whose marked leaf has depth `ℓ`.  Nothing here is a probability statement;
the bound and the depth regrouping are in `Main.lean` and `Depth.lean`.

## The objects

* `markedTransversalBound π x w p` -- the marked atlas/BK sum over the transversal:
  `∑_{r ∈ transversal} ∑_{φ : r.IPos → V} ∑_{y : Fin (p+1) → V} [y (last p) = w] ·
   atlasProduct π x y r φ`.
  The marks and the arm labels are *unchanged*: the terminal tuples are still
  `Fin (p+1) → V` with the physical mark pinned by `y (Fin.last p) = w`, and the position
  variable is still `r.IPos → V`.  Only the shape family is reduced from all plane shapes to
  one representative per orbit, and the position sum is taken at that same representative.

* `transversalMarkedShapes p` -- the transversal, paired with the leaf position carrying the
  marking label `Fin.last p`.  This is the family of marked diagrams on which the depth
  coefficients are counted; the carrier is not `LTon` but the transversal itself.

* `nonplaneMarkedCount p ℓ` -- the number of those diagrams whose marked leaf has depth `ℓ`.
  This is the non-plane version of `I417Marked.markedCount p ℓ`: for `p = 1` it is `1` at
  depth `2`, where the plane count is `2`.

## Why the mark is `Fin.last p` and not a chosen child

`markedTransversalBound` pins the *physical* last terminal: `y (Fin.last p) = w`, exactly as
`markedAtlasBound`.  The pin is a statement about the terminal value, not about a choice of
child, so repeated physical vertices are allowed and the `Empty` witness at coincident
endpoints is untouched.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped ENNReal

@[expose] public section

namespace PercLib.CriticalLRP.I417MarkedTransversal

open PercLib.CriticalLRP.TreeExpansion

/-- **The marked atlas/BK sum over a child-swap transversal.**

The sum runs over one plane representative `r` of each child-swap orbit of fully labelled
`(p+1)`-leaf shapes (`RTree.transversal (Fin (p+1))`), over the internal positions `φ` of that
representative and over the terminal tuples `y : Fin (p+1) → V` whose **last** entry is the
physical marked vertex `w`.  Compared with `I417Marked.markedAtlasBound` only the shape family
changed: it is the transversal, not all plane shapes. -/
noncomputable def markedTransversalBound {V : Type*} (π : Sym2 V → unitInterval) (x w : V)
    (p : ℕ) : ℝ≥0∞ :=
  ∑ r ∈ RTree.transversal (Fin (p + 1)),
    ∑' φ : r.IPos → V, ∑' y : Fin (p + 1) → V,
      PercLib.CriticalLRP.I417MarkedRelabel.pinLast w y *
        CanonAtlas.Measure.atlasProduct π x y r φ

/-- The transversal of shapes with `p+1` labels, paired with the leaf position carrying the
marking label `Fin.last p`.  This is the marked diagram family over one representative per
child-swap orbit: the leaf-position/depth statistic of `A ∈ transversalMarkedShapes p` is
`A.1.depth A.2 = RTree.depth r (markPos (Fin.last p) r)` for `A = ⟨r, markPos (Fin.last p) r⟩`,
which is the statistic `nonplaneMarkedCount` filters on.  The regrouping proofs in `Depth.lean`
work on the transversal directly and do not need the `Σ`-type packaging. -/
noncomputable def transversalMarkedShapes (p : ℕ) :
    Finset ((t : RTree (Fin (p + 1))) × t.LeafPos) :=
  (RTree.transversal (Fin (p + 1))).image
    (fun r => (⟨r, PercLib.CriticalLRP.I417Marked.markPos (Fin.last p) r⟩ :
      (t : RTree (Fin (p + 1))) × t.LeafPos))

/-- **The non-plane marked depth count**: the number of child-swap orbits of fully labelled
`(p+1)`-leaf shapes whose marking leaf `Fin.last p` has depth `ℓ`.

Child swaps change left/right address but not path length, so the marked depth is a function of
the orbit; counting one representative per orbit is therefore an honest count of non-plane
marked diagrams, not a finite-family count with a divisor applied.  At `p = 1` the value at
depth `2` is `1`, where the plane count `I417Marked.markedCount 1 2` is `2`. -/
noncomputable def nonplaneMarkedCount (p ℓ : ℕ) : ℕ :=
  ((RTree.transversal (Fin (p + 1))).filter
    (fun r => RTree.depth r (PercLib.CriticalLRP.I417Marked.markPos (Fin.last p) r) = ℓ)).card

end PercLib.CriticalLRP.I417MarkedTransversal
