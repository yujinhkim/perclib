/-
Accepted and independently rebuilt from Ultramath `smwzg77c3`, member `m3`, direction `d3`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The `p = 3`, `q = 0` `hgap` target: statement and the Case-3 diagonal inputs

Source: Tom Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1.

* **Lemma I.4.17** (printed p. 45): for percolation on a transitive weighted graph and integers
  `p, q ≥ 0`,
  ```
  0 ≤ E|K|^p E|K|^q − E[|K_x|^p |K_y|^q 1(x ↮ y)]
      ≤ ∑_{ℓ=3}^{p+q+1} C_{p,q,ℓ} T^ℓ(x,y) (E|K|)^{2p+2q+1−ℓ}
  ```
  where `T^ℓ` is the `ℓ`-fold power of the two-point matrix.
* **Proposition I.4.20** (printed p. 48): under any of the three conditions of Proposition I.4.2,
  `E_{β_c,r}|K|^p ∼ (2p−3)!! (E_{β_c,r}|K|^2 / E_{β_c,r}|K|)^{p−1} E_{β_c,r}|K|`.

At `p = 3`, `q = 0` the gap is the one-copy star moment
(`I417Gen.rawDiff_add_starMoment`, `SourceModelData.connCubeVertexMass_eq_starMoment`), so the
source's display reads
`E[|K_0|³ 1(y ∈ K_0)] ≤ C₃ T³(0,y) χ⁴ + C₄ T⁴(0,y) χ³` with `χ = E_{β_c,r}|K|`.

## What this file contains

* `SourceModelData.chiReal` — the source's `χ = E_{β_c,r}|K|` as a real number.
* `HasPerVertexTwoTermHgap` — the campaign's per-vertex two-term target, verbatim: constants
  `C₃, C₄` **independent of `r`**, every `r ≥ 1`, every vertex `y` of the window (the quantifier
  is over all of `M.V`; the window is a subset of it).
* `QZeroDiagInputs` — the source's Case-3 inputs, each one carried explicitly and attributed:
  1. `powerInputs` — the landed `I418C.PowerInputs` instance for the cutoff powers, whose
     `triSup` field is the triangle-condition input `T³(0,y) ≤ ∇ = M.triSelf` and whose `colsum`
     field is the row-sum identity `∑_y T^ℓ(y,0) = χ^ℓ`;
  2. `chi_one_le` — `χ ≥ 1` (the cluster of `0` contains `0`);
  3. `chi_unbounded` — `χ = E_{β_c,r}|K| → ∞`, the source's `E_{β_c,r}|K| ⪰ r^α` of
     Proposition I.4.2 (used at p. 46 of the source);
  4. `third_lower` — the third-moment lower bound `E_{β_c,r}|K|³ ⪰ c χ^5`, i.e. Proposition I.4.20
     at `p = 3` together with `E_{β_c,r}|K|² ⪰ (E_{β_c,r}|K|)³`, both asserted in the source's
     Case 3 (p. 46).

`Main.lean` proves that these inputs make the per-vertex two-term target **false**, at the single
vertex `y = 0`, and locates the exact reason: at `y = 0` the left-hand side is the third cutoff
moment `E|K|³ ≍ χ^5`, while the right-hand side is the diagonal `T³(0,0) ≤ ∇ = O(1)` times `χ⁴`.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.QZeroStar.Main
public import PercLib.CriticalLRP.Analysis.Polygon.Consumer

/-! # Definitions for the diagonal obstruction to the per-vertex `hgap` -/

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

@[expose] public section

namespace PercLib.CriticalLRP
namespace Orchestration

open PercLib.CriticalLRP

/-- **The source's `χ = E_{β_c,r}|K|`**, as a real number.  This is exactly the `χ` of the
campaign target and of Lemma I.4.17 (`(E|K|)^{2p+2q+1−ℓ}` at `p = 3`, `q = 0`). -/
noncomputable def SourceModelData.chiReal (M : SourceModelData) (r : ℝ) : ℝ :=
  (M.cutMassAt r 0).toReal

/-- **The campaign's per-vertex two-term `hgap`.**  The claimed estimate is

`connCubeVertexMass r y ≤ C₃ · T³(0,y) · χ⁴ + C₄ · T⁴(0,y) · χ³`

for **every** `r ≥ 1` and **every** window vertex `y`, with constants `C₃, C₄` that do not depend
on `r`.  `T^ℓ(0,y) = I418C.polyK (M.cutTwoPoint r) ℓ 0 y` is the `ℓ`-fold power of the cutoff
two-point kernel, i.e. the source's `T^ℓ_{β_c,r}(0,y)`.

`Main.lean` proves `not_hasPerVertexTwoTermHgap`: under the source's Case-3 inputs this predicate
is unsatisfiable. -/
def SourceModelData.HasPerVertexTwoTermHgap (M : SourceModelData) (C3 C4 : ℝ) : Prop :=
  ∀ r : ℝ, 1 ≤ r → ∀ y : M.V,
    (M.connCubeVertexMass r y).toReal ≤
      C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * M.chiReal r ^ 4 +
        C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * M.chiReal r ^ 3

/-- **The repaired per-vertex target: the root summand is excluded.**

`Main.lean` proves that `HasPerVertexTwoTermHgap` is false, and that the failure is *local to*
`y = 0`: there the left-hand side is exactly `E_{β_c,r}|K|³`.  The repaired statement therefore
quantifies over `y ≠ 0` only, and the root summand is accounted for exactly (as `cutMoment 3`)
in `windowSum_le_of_repaired`.  This is the shape that the source's window sum can consume. -/
def SourceModelData.HasRepairedPerVertexHgap (M : SourceModelData) (C3 C4 : ℝ) : Prop :=
  ∀ r : ℝ, 1 ≤ r → ∀ y : M.V, y ≠ 0 →
    (M.connCubeVertexMass r y).toReal ≤
      C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * M.chiReal r ^ 4 +
        C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * M.chiReal r ^ 3

/-- **The source's Case-3 inputs at the diagonal.**  Every field is an input of the source's
proof of Proposition I.4.15, Case 3 (pp. 45–47); none of them is invented here, and none is
discharged.

* `powerInputs` — the landed cutoff matrix-power package: `polyK (M.cutTwoPoint r)` is a
  non-negative matrix power with `P 0 = δ`, `P 1 0 0 = 1`, composition and summability,
  column sums `∑_y P ℓ (y,0) = χ^ℓ`, entry bounds `P ℓ y 0 ≤ χ^{ℓ−1}`, and the
  **triangle-condition** bound `P 3 0 y ≤ M.triSelf = ∇` for every `y`
  (`SourceModelData.source_powerInputs` produces this from the source's uncut
  triangle/tail/summability inputs).  All fields are stated on the tail `r ≥ max R 1`: the source's
  asymptotic inputs are eventual, and the target quantifies over `r ≥ 1`, so no small-radius
  conversion is smuggled in.
* `chi_one_le` — `1 ≤ χ`, because the cluster of `0` contains `0`.
* `chi_unbounded` — `χ = E_{β_c,r}|K|` is unbounded along the tail `r ≥ max R 1` (source:
  `E_{β_c,r}|K| ⪰ r^α`).
* `third_lower` — `E_{β_c,r}|K|³ ⪰ c χ^5`.  Proposition I.4.20 at `p = 3` gives
  `E|K|³ ∼ 3 (E|K|²/χ)² χ`, and Case 3 of Proposition I.4.15 asserts `E|K|² ⪰ χ³`; together
  `E|K|³ ⪰ 3 χ^5` for large `r`.  Only the lower bound with exponent `5` is used below. -/
structure QZeroDiagInputs (M : SourceModelData) (c R : ℝ) : Prop where
  /-- The constant of the third-moment lower bound is positive. -/
  c_pos : 0 < c
  /-- The landed matrix-power package for the cutoff two-point kernel, with triangle bound
  `∇ = M.triSelf` and column sums `χ ^ ℓ`. -/
  powerInputs : ∀ r : ℝ, max R 1 ≤ r →
    I418C.PowerInputs (I418C.polyK (M.cutTwoPoint r)) M.triSelf (M.cutMassAt r 0).toReal
  /-- `χ = E_{β_c,r}|K| ≥ 1`. -/
  chi_one_le : ∀ r : ℝ, max R 1 ≤ r → 1 ≤ M.chiReal r
  /-- `χ = E_{β_c,r}|K|` is unbounded along the tail `r ≥ max R 1`. -/
  chi_unbounded : ∀ B : ℝ, ∃ r : ℝ, max R 1 ≤ r ∧ B ≤ M.chiReal r
  /-- `E_{β_c,r}|K|³ ⪰ c χ^5`: Proposition I.4.20 at `p = 3` with `E|K|² ⪰ χ³`, eventually in
  `r` (whence the cut-off radius `R`). -/
  third_lower : ∀ r : ℝ, max R 1 ≤ r → c * M.chiReal r ^ 5 ≤ (M.cutMoment 3 r).toReal

end Orchestration
end PercLib.CriticalLRP
