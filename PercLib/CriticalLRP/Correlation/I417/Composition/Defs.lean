/-
Definitions for the composed marked/fresh moment polynomial of Lemma I.4.17.

Extracted from the reviewed `smwxtabcx/m1` regimented final-composition package.
The fresh arm-pinning reindexing is not duplicated: it is supplied by
`Correlation/I417/SummedFresh`.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.MarkedJoint.Transversal.Depth
public import PercLib.CriticalLRP.Correlation.I417.Fresh.Profile.Profile

/-! ## The printed normal form of Lemma I.4.17 -/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

@[expose] public section

namespace PercLib.CriticalLRP.I417SummedClose

open PercLib.CriticalLRP

variable {V : Type*} [Countable V] [DecidableEq V]

/-! ## The printed normal form of Lemma I.4.17

The composed marked expansion has two pinned vertices `x` and `y`, `2p + 1` marked (base) edges and
`2q` fresh edges, `2p + 2q + 1` in total.  The base side contributes `T^ℓ(x,w)` with
`ℓ ∈ [2,p+1]` (`I417MarkedTransversal.nonplaneMarkedCount p ℓ` diagrams), the fresh side `T^m(w,y)`
with `m ∈ [1,q]` (`I417FreshDepth.genCoeff q m` diagrams), and the marked vertex `w` is summed out by
the polygon identity, producing path length `L = ℓ + m ∈ [3, p+q+1]` with `χ`-power
`2p + 2q + 1 - L`. -/

/-- **The composed path-length coefficient `C_{p,q,L}`**: `q` choices of the marked terminal
`j : Fin q` (free because the `q` fresh arms are exchangeable), times the number of pairs of
depths `(ℓ, m)` with `ℓ + m = L`, weighted by the base count and the fresh count.  The summand
vanishes for `L - ℓ ∉ [1,q]` because the fresh coefficient does. -/
noncomputable def composedCoeff (p q L : ℕ) : ℕ :=
  q * ∑ ℓ ∈ Finset.Icc 2 (p + 1),
    I417MarkedTransversal.nonplaneMarkedCount p ℓ * I417FreshDepth.genCoeff q (L - ℓ)

/-- **The printed normal form** of Lemma I.4.17 at `p, q`:
`∑_{L∈[3,p+q+1]} C_{p,q,L} · χ^(2p+2q+1-L) · T^L(x,y)` with `T a b = P(a ↔ b)`.  Exponent plus
path length is always the source's total edge count `2p + 2q + 1`. -/
noncomputable def markedGapPoly (π : Sym2 V → unitInterval) (p q : ℕ) (χ : ℝ≥0∞) (x y : V) :
    ℝ≥0∞ :=
  ∑ L ∈ Finset.Icc 3 (p + q + 1),
    (composedCoeff p q L : ℝ≥0∞) *
      (χ ^ (2 * p + 2 * q + 1 - L) *
        I417Base.iterPow (fun a b => (edgeMeasure π) (connSet a b)) L x y)

/-- **The same normal form, un-grouped over the pair of depths `(ℓ, m)`**: the product of the base
and fresh polynomials with the marked vertex summed out.  Every term carries the honest integer
coefficient `q · C^{base}_{p,ℓ} · C^{fresh}_{q,m}`.  `markedPairSum_eq_markedGapPoly` is the
regrouping by `L = ℓ + m`. -/
noncomputable def markedPairSum (π : Sym2 V → unitInterval) (p q : ℕ) (χ : ℝ≥0∞) (x y : V) :
    ℝ≥0∞ :=
  ∑ ℓ ∈ Finset.Icc 2 (p + 1), ∑ m ∈ Finset.Icc 1 q,
    ((q * I417MarkedTransversal.nonplaneMarkedCount p ℓ * I417FreshDepth.genCoeff q m : ℕ) :
        ℝ≥0∞) *
      (χ ^ (2 * p + 2 * q + 1 - (ℓ + m)) *
        I417Base.iterPow (fun a b => (edgeMeasure π) (connSet a b)) (ℓ + m) x y)

end PercLib.CriticalLRP.I417SummedClose
