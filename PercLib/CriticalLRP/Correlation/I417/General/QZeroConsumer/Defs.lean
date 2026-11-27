/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted from Ultramath `smwzg77c3`, member `m6`, independently rebuilt.
Production integration based on commit `81c6038182e9a883ffcd3d870aed7cd4829649d4`.
Original direction `d9`.

# The two-term `q = 0` star-gap interface of Lemma I.4.17

Source: Tom Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1.
Lemma I.4.17 (printed p. 45) with `p = 3`, `q = 0` reads

```
E[|K_0|³ 1(y ∈ K_0)] ≤ C_{3,0,3} T³(0,y) (E|K|)⁴ + C_{3,0,4} T⁴(0,y) (E|K|)³,
```

with `T = T_{β_c,r}` and `E|K| = E_{β_c,r}|K|`; the exponent of `E|K|` is `2p + 2q + 1 - ℓ = 7 - ℓ`
and the printed range is `3 ≤ ℓ ≤ p + q + 1 = 4`.  This file fixes only the *interface*: the
per-vertex statement (`TwoTermStarGap`), the sharper sufficient condition (`SharpProfile`, the
`χ³ T` profile), and the `χ` and right-hand-side notation.  No inequality is asserted here.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.QZeroStar.Main
public import PercLib.CriticalLRP.Analysis.Cutoff.KpowSum
public import PercLib.CriticalLRP.Analysis.Polygon.Defs
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case3.CutPoly.Defs

/-! # Interface definitions for the `q = 0` two-term star gap -/

noncomputable section

open MeasureTheory Measure ProbabilityTheory
open scoped ENNReal NNReal BigOperators

@[expose] public section

namespace PercLib.CriticalLRP.I417QZeroConsumer

open PercLib.CriticalLRP.Orchestration

variable (M : SourceModelData)

/-- `χ = (E_{β_c,r}|K|)`, the source's `E|K|` at the truncated law, as a real number. -/
def chi (r : ℝ) : ℝ := (M.cutMassAt r 0).toReal

/-- The source's per-vertex right-hand side at `p = 3`, `q = 0`:
`C₃ T³(0,y) χ⁴ + C₄ T⁴(0,y) χ³`, with `T^ℓ` the `ℓ`-fold matrix power of the truncated
two-point function `T = T_{β_c,r}` (`I418C.polyK`). -/
def starRHS (C3 C4 : ℝ) (r : ℝ) (y : M.V) : ℝ :=
  C3 * I418C.polyK (M.cutTwoPoint r) 3 0 y * chi M r ^ 4
    + C4 * I418C.polyK (M.cutTwoPoint r) 4 0 y * chi M r ^ 3

/-- **The target statement** (Lemma I.4.17 at `p = 3`, `q = 0`, per vertex, `r ≥ 1`): the
Case-3 per-vertex numerator `E_{β_c,r}[|K_0|³ 1(y ∈ K_0)]` (`M.connCubeVertexMass`) is bounded by
the two-term source right-hand side, with constants `C3`, `C4` independent of `r` and `y`. -/
def TwoTermStarGap (C3 C4 : ℝ) : Prop :=
  ∀ (r : ℝ), 1 ≤ r → ∀ y : M.V, (M.connCubeVertexMass r y).toReal ≤ starRHS M C3 C4 r y

/-- **A *stronger* single-term condition**: the `χ³ T` profile
`E[|K_0|³ 1(y ∈ K_0)] ≤ C χ³ T(0,y)`.  It implies `TwoTermStarGap M C 0`
(`sharpProfile_implies_twoTermStarGap` in `Main.lean`) because `T^ℓ(0,y) ≥ T(0,y)` for every
`ℓ ≥ 1` and `χ ≥ 1`, and it is what Case 3 needs with no polygon driver (`Sharp.lean`).

**It is inconsistent with unbounded χ under the stated Case-3 moment gap**: at `y = 0` it demands `E|K_0|³ ≤ C χ³`, which contradicts the Case-3
growth of the moments (`Diagonal.lean`, `sharpProfile_diag_no_go`).  It is recorded only to show
that the two-term shape of the source's display is the correct one. -/
def SharpProfile (C : ℝ) : Prop :=
  ∀ (r : ℝ), 1 ≤ r → ∀ y : M.V,
    (M.connCubeVertexMass r y).toReal ≤ C * chi M r ^ 3 * M.cutTwoPoint r 0 y

/-- The extended-real two-term right-hand side: `ofReal C₃ * T³(0,y) * χ⁴ +
ofReal C₄ * T⁴(0,y) * χ³` with the *genuine* `ℝ≥0∞` matrix power `Kpow` of the truncated
two-point kernel and `χ = M.cutMassAt r 0` (the source's `E_{β_c,r}|K|`, in `ℝ≥0∞`). -/
def starRHSE (C3 C4 : ℝ) (r : ℝ) (y : M.V) : ℝ≥0∞ :=
  ENNReal.ofReal C3 * KernelPower.Kpow (M.cutTwoPointE r) 3 (0 : M.V) y
      * (M.cutMassAt r 0) ^ 4
    + ENNReal.ofReal C4 * KernelPower.Kpow (M.cutTwoPointE r) 4 (0 : M.V) y
      * (M.cutMassAt r 0) ^ 3

/-- **The `ℝ≥0∞` parent of the target**: the one-copy star moment
`starMoment (M.cutProb r) 0 y 3` is bounded by the two-term source right-hand side in extended
reals.  `twoTermStarGapE_toReal` converts this to `TwoTermStarGap` at finite `χ`. -/
def TwoTermStarGapE (C3 C4 : ℝ) : Prop :=
  ∀ (r : ℝ), 1 ≤ r → ∀ y : M.V,
    I417Gen.starMoment (M.cutProb r) (0 : M.V) y 3 ≤ starRHSE M C3 C4 r y

end PercLib.CriticalLRP.I417QZeroConsumer
