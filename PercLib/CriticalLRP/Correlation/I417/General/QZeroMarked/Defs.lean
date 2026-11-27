/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted from Ultramath `smwzg77c3`, member `m2`, independently rebuilt.
Production integration based on commit `81c6038182e9a883ffcd3d870aed7cd4829649d4`.
Original direction `d5`.

# The `q = 0`, `p = 3` per-vertex tree gap: the residual class of the marked route

Source: Tom Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1,
Lemma I.4.17 (printed p. 45), its proof (pp. 45-46), and the Case-3 use at p. 47.

The target of this direction is the per-vertex two-term estimate at the cutoff law, for
`p = 3`, `q = 0`:

```lean
E_{β_c,r}[|K_0|³ 1(y ∈ K_0)]
  ≤ C3 · T^3_{β_c,r}(0,y) · χ^4 + C4 · T^4_{β_c,r}(0,y) · χ^3 .
```

`qzeroTwoTermBound` below is exactly that statement.  The landed marked route
(`SecondMomentCase3.MarkedPolygon`) gives the *four*-term marked polygon bound, whose `ℓ`-th
summand carries `χ^(2p+1-ℓ) T^ℓ`.  At `p = 3` this file isolates the one class that is *not* of
the target's shape: `ℓ = 2`, i.e. `χ^5 T^2`.  The three names below are:

* `qzeroEllTwoClass` -- the `ℓ = 2` marked class `markedCount 3 2 · χ^5 · T^2(0,y)` (source's `χ`
  and cutoff matrix powers);
* `qzeroEllTwoAbsorbed` -- the single inequality that absorbs that class into the target's shape;
* `qzeroChiMulSquareLe` -- the equivalent "one missing factor of `χ`" form
  `χ · T^2(0,y) ≤ K · T^3(0,y)`, which is the pure two-point input that the marked route
  cannot supply (see `Main.lean` and the report).

Nothing here asserts a probability statement; this is a definition layer only.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.MarkedPolygon

/-! # Definitions for the residual `ℓ = 2` class of the marked route -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MeasureTheory Measure
open scoped ENNReal NNReal BigOperators

@[expose] public section

noncomputable section


namespace PercLib.CriticalLRP.QZeroGap

/-- The marked per-depth coefficient of the base side of Lemma I.4.17 at `p = 3`, as landed:
`I417Marked.markedCount 3 ℓ`, the number of fully labelled plane trees on `4 = p + 1` leaves
whose marked leaf sits at depth `ℓ`.  Kept as a name so that no numerical value is smuggled into
a definition.  It does not depend on the model, hence lives outside the `SourceModelData`
namespace. -/
def markedCoeff (ℓ : ℕ) : ℕ := PercLib.CriticalLRP.I417Marked.markedCount 3 ℓ

end PercLib.CriticalLRP.QZeroGap

open PercLib.CriticalLRP.QZeroGap

namespace PercLib.CriticalLRP.Orchestration
namespace SourceModelData


variable (M : PercLib.CriticalLRP.Orchestration.SourceModelData)

/-- The source's `χ = E_{β_c,r}|K|` at the cutoff law, in `ℝ`: `(M.cutMassAt r 0).toReal`.

The target is stated with this normalization; no `⊤ ↦ 0` conversion is made anywhere, and the
finiteness `M.cutMassAt r 0 ≠ ⊤` is carried as an explicit hypothesis by every theorem that
takes a `toReal`. -/
def qzeroChi (r : ℝ) : ℝ := (M.cutMassAt r 0).toReal

/-- The source's `T^ℓ_{β_c,r}(0,y)`: the `ℓ`-fold power of the cutoff two-point matrix, i.e.
`I418C.polyK (M.cutTwoPoint r) ℓ 0 y` (`polyK` is defined by the iterated `tsum` of the real
cutoff kernel, so this is the matrix power and not a truncated finite-set surrogate). -/
def qzeroTpow (r : ℝ) (ℓ : ℕ) (y : M.V) : ℝ :=
  PercLib.CriticalLRP.I418C.polyK (M.cutTwoPoint r) ℓ 0 y


/-- **The target**: the per-vertex two-term `q = 0`, `p = 3` estimate with constants `C3, C4`,
for every `r ≥ 1` and every vertex `y`.

Both summands are the source's own shape `T^ℓ(0,y) χ^(2p+1-ℓ)` at `ℓ = 3, 4`; no window, no
supremum over `y`, and no inhomogeneous analogue. -/
def qzeroTwoTermBound (C3 C4 : ℝ) : Prop :=
  ∀ r : ℝ, 1 ≤ r → ∀ y : M.V,
    (M.connCubeVertexMass r y).toReal ≤
      C3 * (M.qzeroChi r) ^ 4 * M.qzeroTpow r 3 y + C4 * (M.qzeroChi r) ^ 3 * M.qzeroTpow r 4 y

/-- **The `ℓ = 2` marked class**: `markedCount 3 2 · χ^5 · T^2(0,y)`.

This is the single summand of the landed marked polygon bound at `p = 3` whose `χ`-power is
`5`, i.e. the only class that the target's two-term shape does not contain.  (`ℓ = 1` is
provably empty at `p = 3`: see `Main.markedCoeff_one_eq_zero`.) -/
def qzeroEllTwoClass (r : ℝ) (y : M.V) : ℝ :=
  (markedCoeff 2 : ℝ) * (M.qzeroChi r) ^ 5 * M.qzeroTpow r 2 y

/-- **Absorption of the `ℓ = 2` class** into the target's two exponent classes, with constants
`A3, A4`.  This is the *entire* remaining obligation of the marked route at `p = 3`, `q = 0`
(`Main.twoTermBound_of_ellTwoAbsorbed`). -/
def qzeroEllTwoAbsorbed (A3 A4 : ℝ) : Prop :=
  ∀ r : ℝ, 1 ≤ r → ∀ y : M.V,
    M.qzeroEllTwoClass r y
      ≤ A3 * (M.qzeroChi r) ^ 4 * M.qzeroTpow r 3 y
        + A4 * (M.qzeroChi r) ^ 3 * M.qzeroTpow r 4 y

/-- **The two-point regularity residual**: one factor of `χ` between consecutive powers of the
cutoff two-point matrix, `χ · T^2(0,y) ≤ K · T^3(0,y)`.

This is the exact content that the marked route cannot produce by monotonicity
(`T^ℓ ≤ T^(ℓ+1)` gives only `χ^5 T^2 ≤ χ · (χ^4 T^3)`, i.e. it leaves precisely this factor of
`χ`).  It is a statement about the two-point function alone, not about the star, and it is not
an instance of the source's Lemma I.4.18 (whose displayed bound is an upper bound on `T^ℓ` and
whose `ℓ = 2, 3` instances are refuted; see `Main` and the report). -/
def qzeroChiMulSquareLe (K : ℝ) : Prop :=
  ∀ r : ℝ, 1 ≤ r → ∀ y : M.V, M.qzeroChi r * M.qzeroTpow r 2 y ≤ K * M.qzeroTpow r 3 y

/-- **The alternative two-point residual** with the fourth power:
`χ² · T^2(0,y) ≤ K · T^4(0,y)`.  It also absorbs the `ℓ = 2` class (use the target's `ℓ = 4`
monomial with coefficient `A4 = m2 · K`), and it is heuristically of the same strength as
`qzeroChiMulSquareLe` because `T^(ℓ+1)(0,y) ≈ χ · T^ℓ(0,y)`; which of the two is available is a
question about lower bounds on the cutoff two-point powers, and the fourth-power form is the one
that can pair with the landed `ℓ = 4` polygon machinery. -/
def qzeroChiSqMulSquareLe (K : ℝ) : Prop :=
  ∀ r : ℝ, 1 ≤ r → ∀ y : M.V,
    M.qzeroChi r * M.qzeroChi r * M.qzeroTpow r 2 y ≤ K * M.qzeroTpow r 4 y

end SourceModelData
end PercLib.CriticalLRP.Orchestration
