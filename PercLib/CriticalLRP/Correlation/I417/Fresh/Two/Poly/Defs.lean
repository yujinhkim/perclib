/- Independently rebuilt from the accepted `smwx05qau` component, member `m1`.
Production integration revision: `5bd358885b7d12588d7216ae2d6dcee3a9dd5622`.

# Lemma I.4.17, `q = 2`, arbitrary `p`: the polygon monomials of the `∑_w` composition

Source: T. Hutchcroft, *Critical long-range percolation I: high effective dimension*,
arXiv:2508.18807v1, Lemma I.4.17 (p. 45).

This file fixes the two monomial families that the `q = 2` composition of the marked base side with
the fresh side produces, and nothing else.  No new mathematical assumption is introduced.

## What is being composed

The marked base side of I.4.17 (already proved in
`Correlation/I417/MarkedJoint/Transversal/Depth`) bounds the `p`-th marked cluster moment by

  `jointPow π x p w ≤ ∑_{ℓ ∈ [2,p+1]} C(p,ℓ) · χ^(2p+1-ℓ) · T^ℓ(x,w)`,

with `C = nonplaneMarkedCount p` counting child-swap orbits of fully labelled `(p+1)`-leaf shapes,
`χ = E|K|` the constant mean volume and `T` the two-point matrix `T(a,b) = τ(a,b) = P(a↔b)`.

The fresh side at `q = 2` is bounded (proved in `Correlation/I417/Fresh/Two/Main`,
`freshCombBound_two`) by the evaluated fresh diagram family.  Composing the two with the
polygon identity `∑_w T^ℓ(x,w)·T^m(w,y) = T^(ℓ+m)(x,y)` turns each product of a marked
monomial with a fresh monomial into one polygon monomial `χ^a · T^b(x,y)` with `a + b` the total
number of two-point factors.

## The two fresh-side monomial families

* `freshTwoPoly π χ y w` — the **unconditional** `q = 2` fresh majorant obtained from the proved
  three-terminal tree-graph inequality `I417Example.threeLeaf_treeGraph`: it has five two-point
  factors, `χ³T²(w,y) + 2χ²T³(w,y)`.  Composing it with the marked monomial gives
  `χ^(2p+4-ℓ)T^(ℓ+2)(x,y)` and `2χ^(2p+3-ℓ)T^(ℓ+3)(x,y)`, i.e. total factor count `2p+6` and
  `y`-legs of length `2` and `3`.

* `fourArmFresh π y w` — the **single-hub four-arm** fresh bound `∑_a τ(w,a)τ(a,y)χ(a)²`, which has
  exactly four two-point factors and a `y`-leg of length `2`.  It is the fresh-side input that lands
  exactly on the paper's normalisation `C_{p,2,ℓ} T^ℓ(x,y)(E|K|)^{2p+5-ℓ}` with `3 ≤ ℓ ≤ p+3`
  (the total factor count `(2p+1) + 4 = 2p+5`).  This is an auxiliary four-factor candidate,
  not an axiom or an available general theorem. `Poly/Counterexample.not_fourArmFresh_bound`
  proves that the corresponding universal hypothesis is false on the inhomogeneous two-edge
  star at `Fin 3`. The counterexample does not assert a failure of Lemma I.4.17 in the paper's
  transitive setting. `QTwoMain.lean` gives only the conditional reduction when this extra
  hypothesis is supplied; it cannot make it available at arbitrary countable vertex types.
  The proved, unaffected majorant is `freshTwoPoly`.

Definitions only in this file.
-/

module

public import PercLib.CriticalLRP.Correlation.I417.Fresh.Two.Main
public import PercLib.CriticalLRP.Correlation.I417.Base.Poly

/-! The evaluated two-arm fresh polynomial and the conditional four-arm input. -/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal
open PercLib.CriticalLRP.I417Base

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

@[expose] public section

namespace PercLib.CriticalLRP.I417FreshTwo

variable {V : Type*} [Countable V] [DecidableEq V]

/-- The two-point kernel `T(a,b) = τ(a,b)`; `I417Fresh.tau` is the same function, rewritten here as
an explicit kernel argument so that `iterPow` can be applied to it. -/
noncomputable def kernel (π : Sym2 V → unitInterval) : V → V → ℝ≥0∞ :=
  fun a b => (edgeMeasure π) (connSet a b)

theorem kernel_def (π : Sym2 V → unitInterval) (a b : V) :
    kernel π a b = I417Fresh.tau π a b := rfl

/-- **The evaluated `q = 2` fresh majorant with five two-point factors**,
`χ³·T²(w,y) + 2·χ²·T³(w,y)`.

This is the exact value of the summed three-terminal fresh diagram `∑_g leafShape π y w g` when the
two-point kernel has the constant row sum `χ` (`QTwoMain.tsum_leafShape_eq_poly`), and it bounds the
fresh-copy factor `∑_g P(freshMark y g j w)` of I.4.17 at `q = 2`
(`QTwoMain.tsum_freshMark_le_poly`).  The `y`-legs have length `2` and `3`; the factor counts are
`5` in both terms. -/
noncomputable def freshTwoPoly (π : Sym2 V → unitInterval) (χ : ℝ≥0∞) (y w : V) : ℝ≥0∞ :=
  χ ^ 3 * iterPow (kernel π) 2 w y + 2 * (χ ^ 2 * iterPow (kernel π) 3 w y)

/-- **The single-hub four-arm fresh bound at `q = 2`**: the spine `w → a`, the arm `a → y` and the
two labelled arms `a → g 0`, `a → g 1` all hanging off one hub `a`.  Summed over `a` and over the
two arms this is `∑_a τ(w,a)·τ(a,y)·χ(a)²`, i.e. **four** two-point factors with a `y`-leg of
length `2` — exactly the count `(2p+1) + 4 = 2p+5` of the paper's normalisation.

This is the fresh-side input that is missing for the `q = 2` case; it is a definition here so that
the reduction in `QTwoMain.moment_gap_two_le_poly_fourArm` can name it.  It is not an axiom and not
assumed anywhere unconditionally. -/
noncomputable def fourArmFresh (π : Sym2 V → unitInterval) (y w : V) : ℝ≥0∞ :=
  ∑' a : V, kernel π w a * kernel π a y * (I417Fresh.hubArmSum π a * I417Fresh.hubArmSum π a)

end PercLib.CriticalLRP.I417FreshTwo
