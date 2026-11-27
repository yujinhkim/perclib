/-
Ultramath swarm `smwziumdb`, member `m5`, direction `d2`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwziumdb`, member `m5`.
Product-numerator integration based on production commit `e59e9347a3988d8c181ba0308758fa84fc2ec15f`.

# The Case-3 numerator of Proposition I.4.15 as a *product-minus-excluded* `(2,1)` difference

Hutchcroft, *Critical long-range percolation I* (arXiv:2508.18807v1), proof of
Proposition I.4.15, p. 43, definition of `E_{2,r}`:

```
          |B_r| E|K| E|K|²  −  E[|K| ∑_{y∈B_r} 1(y∉K)|K_y|²]
  E_{2,r} := ----------------------------------------------------
                       |B_r| E|K| E|K|²
```

and the second displayed form of the same numerator,

```
  |B_r| E|K| E|K|² − E[|K| ∑_{y∈B_r}|K_y|²] + E[|K|³ |K ∩ B_r|] ,
```

where the last term is the `q = 0` star `E[|K|³|K ∩ B_r|]`; p. 43 then bounds
`0 ≤ E_{2,r} ≤ E[|K|³|K∩B_r|] / (|B_r| E|K| E|K|²)` (I.4.16), which is the route the paper
uses in Cases 1 and 2.  In Case 3 (p. 46) the paper instead invokes Lemma I.4.17 (the
`p = 2`, `q = 1` two-copy gap) for the *same* numerator.

The point of this file is that the numerator itself, before any inequality by the star, is a
window sum of `(p,q) = (2,1)` product-minus-excluded differences, one per window vertex, with
the **second** moment on the window vertex `y` and the **first** moment on the root `0`:

```
  |B_r| E|K| E|K|² − E[|K| ∑_{y∈B_r} 1(y∉K)|K_y|²]
    = ∑_{y∈B_r} [ E|K_y|² E|K_0| − E[ |K_y|² 1(0∉K_y) |K_0| ] ] .
```

The right-hand side is *literally* the `(2,1)` difference `I417.volSq · I417.meanVol −
I417.exclMomentSq` at the **swapped** pair `(x, y) = (y, 0)` — no restoration, no joint
semantics, no labelling, and (crucially) no use of a swap automorphism: the interchange is
only the trivial one `E|K|²E|K| = E|K|E|K|²` together with `0 ∉ K_y ↔ y ∉ K_0`.  Translation
invariance enters exactly once, to make `E|K_y|²` root-independent (`volSq_cutProb_eq`), which
is what lets the per-vertex product term be read as the constant `E|K| E|K|²`.

This is therefore *not* a bound on the star, and it does not bound the star: on the two-vertex
graph the numerator is `5p + 3p²` while the star is `8p` (`notes.md`, exact rational check).
`Main.lean` proves `case3Numerator_le_case3DiffWindow` (the identity) and
`case3Numerator_le_polygonWindow` (the landed `(2,1)` gap plus its tree evaluation
`I417Example.printed_le`), replacing the `p = 3`, `q = 0` star input `hgap` of
`SecondMomentCase3` by the *proved* product gap.

No `sorry`, no custom axioms.  Definitions only in this file.
-/
module

public import PercLib.CriticalLRP.Correlation.I417Example.Printed
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.WindowedEllThree.Case3Windowed
public import PercLib.CriticalLRP.Analysis.Cutoff.Translation
public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.MarkedPolygon

/-! # Case-3 product-minus-excluded window definitions -/

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal

set_option linter.unusedSectionVars false

@[expose] public section

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

variable (M : SourceModelData)

/-- **The Case-3 numerator of (I.4.16), before the inequality by the star.**

`|B_r| E_{β_c,r}|K| E_{β_c,r}|K|² − E_{β_c,r}[|K_0| ∑_{y∈B_r} 1(y∉K_0)|K_y|²]`, as an
`ℝ≥0∞` (never truncated).  This is exactly the numerator of the source's `E_{2,r}`; the
`ℝ≥0∞` subtraction is the paper's difference whenever it is non-negative, which
`exclMassQuad_le_ball_mul_moments` records. -/
noncomputable def case3Numerator (r : ℝ) : ℝ≥0∞ :=
  ((M.ball r).ncard : ℝ≥0∞) * M.cutMoment 2 r * M.cutMoment 1 r - M.exclMassQuad r

/-- **The window sum of the `(2,1)` product-minus-excluded differences at the swapped pairs
`(y, 0)`.**

`∑_{y∈B_r} [ E|K_y|² E|K_0| − E[|K_y|² 1(0∉K_y)|K_0|] ]`, with `E|K_y|² = I417.volSq`,
`E|K_0| = I417.meanVol` and the excluded moment `I417.exclMomentSq` — i.e. the `(p,q) = (2,1)`
source difference, *not* a restored/joint moment and *not* the `q = 0` star.  The identity
`case3Numerator_eq_sum_sub_sum` shows the source numerator is this sum read as
`(∑_y E|K_y|²E|K_0|) − (∑_y excluded_y)`, and `case3Numerator_le_case3DiffWindow` converts the
difference of sums into the sum of differences. -/
noncomputable def case3DiffWindow (r : ℝ) : ℝ≥0∞ :=
  ∑ y ∈ E1Sign.ballF M r,
    (I417.volSq (M.cutProb r) y * I417.meanVol (M.cutProb r) (0 : M.V) -
      I417.exclMomentSq (M.cutProb r) y (0 : M.V))

/-- **The source's Case-3 numerator estimate, right-hand side.**

`∑_{y∈B_r} [T³(0,y) χ⁴ + 2 T⁴(0,y) χ³]` with `χ = E_{β_c,r}|K| = M.cutMassAt r 0`: the
`p = 2`, `q = 1` printed display `T³(E|K|)⁴ + 2T⁴(E|K|)³` of Lemma I.4.17 summed over the
window, with the printed constants `1` and `2`.  Summing the printed display *at the swapped
pair* `(y,0)` and using the symmetry of the matrix powers produces exactly this. -/
noncomputable def polygonWindow (r : ℝ) : ℝ≥0∞ :=
  ∑ y ∈ E1Sign.ballF M r,
    (I417.T3 (M.cutProb r) (0 : M.V) y * (M.cutMassAt r 0) ^ 4 +
      2 * (I417.T4 (M.cutProb r) (0 : M.V) y * (M.cutMassAt r 0) ^ 3))

/-- The `ℓ`-th windowed polygon sum `∑_{y∈B_r} T^ℓ_{β_c,r}(0,y)`, in the repository's
canonical iterated matrix power `I417Base.iterPow` of the cutoff connection kernel.
`windowTPow_three_toReal` identifies its `ℓ = 3` `ℝ`-normalisation with the landed
`M.windowPolyKThree` (`∑_y I418C.polyK (M.cutTwoPoint r) 3 0 y`). -/
noncomputable def windowTPow (ℓ : ℕ) (r : ℝ) : ℝ≥0∞ :=
  ∑ y ∈ E1Sign.ballF M r,
    I417Base.iterPow (fun u v : M.V => (edgeMeasure (M.cutProb r)) (connSet u v)) ℓ
      (0 : M.V) y

/-- **The two landed Lemma-I.4.18 polygon inputs of Case 3**: the windowed `ℓ = 3` sum
(`M.WindowedEllThreeGap`, which `WindowedEllThree/Windowed.lean` proves from the triangle
condition and the ball count) and the per-vertex `ℓ = 4` bound
(`M.exists_polygonBound_four`).  Both are stated at the source driver
`M.case3Driver c r = ∇_{r^c} + r^{-c}`. -/
def PolygonWindowInputs (Cp c : ℝ) : Prop :=
  M.WindowedEllThreeGap c Cp ∧
    (∀ r : ℝ, 1 ≤ r → ∀ x : M.V,
      I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) x ≤
        Cp * M.case3Driver c r * (M.cutMassAt r 0).toReal)

end SourceModelData
end Orchestration
end PercLib.CriticalLRP
