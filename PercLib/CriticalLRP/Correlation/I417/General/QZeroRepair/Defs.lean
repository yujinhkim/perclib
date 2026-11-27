/-
Accepted from Ultramath `smwzg77c3`, member `m7`, independently rebuilt.
Production integration based on commit `81c6038182e9a883ffcd3d870aed7cd4829649d4`.
Original direction `d6`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The per-vertex two-term source estimate of Lemma I.4.17 at `p = 3`, `q = 0`

Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, Lemma I.4.17 (printed p. 45).
At `p = 3`, `q = 0` the printed display reads, for every pair of vertices `x`, `y`,

```
E|K|^3 - E[|K_x|^3 1(x nleftrightarrow y)] <= C3 T^3(x,y) (E|K|)^4 + C4 T^4(x,y) (E|K|)^3 ,
```

and the left-hand side is *exactly* the one-copy `q = 0` connected star moment
`E[|K_x|^3 1(x <-> y)]` (`I417Gen.rawDiff_add_starMoment`), i.e. the Case-3 per-vertex numerator
`M.connCubeVertexMass r y`.  This file records that statement once, in the two forms the
downstream consumers use:

* `StarTwoTermBound M C3 C4` — all vertices `y` (the strongest reading of the target);
* `StarTwoTermBoundWindow M C3 C4` — `y` ranging over the window `ballF M r`, which is the
  hypothesis `hgap` of `SecondMomentCase3.connCubeMass_toReal_le_of_perVertex_gap`;
* `StarTwoTermBoundFar M C3 C4 rho` — the corrected reading in which the bound is only demanded
  outside the spatial ball of radius `rho r`.  `Main.lean` proves that the unconditional reading
  is *false* at `y = 0` in the source's own Case-3 asymptotic regime, so the far form (or an
  explicit diagonal term) is the source-faithful statement.

`chi M r` is the `chi = (M.cutMassAt r 0).toReal` of the target, repeated so that the right-hand
side can be written once.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.QZeroStar.Main
public import PercLib.CriticalLRP.Analysis.Polygon.Consumer

/-! # The two-term per-vertex statements -/

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.hashCommand false

@[expose] public section

namespace PercLib.CriticalLRP.Smwzg77c3.M7

open PercLib.CriticalLRP Orchestration

variable (M : SourceModelData)

/-- The finite-cutoff susceptibility `chi = E_{beta_c,r}|K_0|` in `RR`, i.e. the `chi` of the
target estimate. -/
def chi (r : ℝ) : ℝ := (M.cutMassAt r 0).toReal

/-- **The per-vertex two-term source estimate**, uniformly in the vertex:
`E[|K_0|^3 1(y in K_0)] <= C3 * T^3(0,y) * chi^4 + C4 * T^4(0,y) * chi^3`, where `T` is the
cutoff two-point matrix `M.cutTwoPoint r` and `T^k` its `k`-fold matrix power
`I418C.polyK (M.cutTwoPoint r) k 0 y`. -/
def StarTwoTermBound (C3 C4 : ℝ) : Prop :=
  ∀ (r : ℝ), 1 ≤ r → ∀ y : M.V,
    (M.connCubeVertexMass r y).toReal ≤
      C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * (M.cutMassAt r 0).toReal ^ 4
        + C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * (M.cutMassAt r 0).toReal ^ 3

/-- **The window form** of the same estimate: `y` ranges over the Case-3 window
`E1Sign.ballF M r`.  This is the shape of the hypothesis `hgap` consumed by
`SecondMomentCase3.connCubeMass_toReal_le_of_perVertex_gap`. -/
def StarTwoTermBoundWindow (C3 C4 : ℝ) : Prop :=
  ∀ (r : ℝ), 1 ≤ r → ∀ y ∈ E1Sign.ballF M r,
    (M.connCubeVertexMass r y).toReal ≤
      C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * (M.cutMassAt r 0).toReal ^ 4
        + C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * (M.cutMassAt r 0).toReal ^ 3

/-- **The corrected (far) form**: the two-term estimate is demanded only on vertices outside the
ball of radius `rho r`.  `Main.lean` shows that demanding it at `y = 0` is incompatible with the
source's own higher-moment asymptotic (Proposition I.4.20), while the complement of the far region
still has `o(|B_r|)` vertices, so the Case-3 window sum is unaffected. -/
def StarTwoTermBoundFar (C3 C4 : ℝ) (rho : ℝ → ℝ) : Prop :=
  ∀ (r : ℝ), 1 ≤ r → ∀ y : M.V, y ∉ M.ball (rho r) →
    (M.connCubeVertexMass r y).toReal ≤
      C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * (M.cutMassAt r 0).toReal ^ 4
        + C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * (M.cutMassAt r 0).toReal ^ 3

/-- **The corrected (additive) form**: the two-term estimate with the diagonal-carrying term
`C5 * T(0,y) * chi^5` added.  At `y = 0` the added term is `C5 * chi^5`, which is the size that
the source's Proposition I.4.20 forces for `E|K_0|^3`, so the diagonal obstruction of `Main.lean`
disappears; summed over the window the added term costs `C5 * chi^6`, i.e. `C5 * chi^2 / |B_r|` in
the Case-3 error, which vanishes and is logarithmically integrable for `alpha <= d / 2`. -/
def StarTwoTermBoundAdd (C3 C4 C5 : ℝ) : Prop :=
  ∀ (r : ℝ), 1 ≤ r → ∀ y : M.V,
    (M.connCubeVertexMass r y).toReal ≤
      C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * (M.cutMassAt r 0).toReal ^ 4
        + C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * (M.cutMassAt r 0).toReal ^ 3
        + C5 * M.cutTwoPoint r (0 : M.V) y * (M.cutMassAt r 0).toReal ^ 5

end PercLib.CriticalLRP.Smwzg77c3.M7
