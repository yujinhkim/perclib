/-
Accepted from Ultramath `smwzg77c3`, member `m7`, independently rebuilt.
Production integration based on commit `81c6038182e9a883ffcd3d870aed7cd4829649d4`.
Original direction `d6`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The unconditional per-vertex constraint

`Harris.lean` proves the positive-association lower bound (H),
`T(0,y) * E|K_0|^3 <= E[|K_0|^3 1(y in K_0)]`, from the landed Harris--FKG machinery.  Feeding it
into `Vertex.lean`'s `T_mul_chi_le_of_twoTerm` removes the only hypothesis that was not a landed
or source-level input, giving the unconditional statement:

> if the source's two-term estimate at `p = 3`, `q = 0` holds at a vertex `y`, and
> `E|K_0|^3 >= K chi^5` (Proposition I.4.20 at `p = 3` with `chi_2 >~ chi^3`), then
> `K * T(0,y) * chi <= (C3 + C4) * nabla`.

Consequences recorded here:

* `T_le_of_twoTerm'`: `T(0,y) <= (C3 + C4) * nabla / (K * chi_r)`, so the estimate can only hold
  where the two-point function is `O(1/chi_r)`;
* `not_twoTerm_of_T_ge`: at every vertex whose connection probability is bounded below by `t`
  with `K * t * chi_r > (C3 + C4) * nabla` (in particular at `y = 0`, where `T(0,0) = 1`), the
  two-term estimate **fails**.  Nothing here is specific to the basepoint: the same obstruction
  sits at every near vertex, so deleting `y = 0` from the vertex range does not repair the
  statement.

No `sorry`, no custom axioms, no `⊤ ↦ 0` conversion.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.QZeroRepair.Vertex
public import PercLib.CriticalLRP.Correlation.I417.General.QZeroRepair.Harris

/-! # The per-vertex constraint, unconditionally -/

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.hashCommand false

@[expose] public section

namespace PercLib.CriticalLRP.Smwzg77c3.M7

open PercLib.CriticalLRP Orchestration
open PercLib.CriticalLRP.I418C

variable (M : SourceModelData)

/-- **The per-vertex constraint, unconditionally**: the two-term estimate at `y` forces
`K * T(0,y) * chi <= (C3 + C4) * nabla`. -/
theorem T_mul_chi_le_of_twoTerm' {C3 C4 K : ℝ} (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4)
    {r : ℝ} (hχ : M.cutMassAt r 0 ≠ ⊤) (h3 : M.cutMoment 3 r ≠ ⊤)
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤)
    {y : M.V}
    (hgrowth : K * chi M r ^ 5 ≤ (M.cutMoment 3 r).toReal)
    (hinst : (M.connCubeVertexMass r y).toReal ≤
      C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * chi M r ^ 4
        + C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * chi M r ^ 3) :
    K * M.cutTwoPoint r (0 : M.V) y * chi M r ≤ (C3 + C4) * M.triSelf :=
  T_mul_chi_le_of_twoTerm M hC3 hC4 hχ hTri (harris_cutMoment M r h3 y) hgrowth hinst

/-- **The admissible region**: `T(0,y) <= (C3 + C4) * nabla / (K * chi_r)`. -/
theorem T_le_of_twoTerm' {C3 C4 K : ℝ} (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4) (hK : 0 < K)
    {r : ℝ} (hχ : M.cutMassAt r 0 ≠ ⊤) (h3 : M.cutMoment 3 r ≠ ⊤)
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤)
    {y : M.V}
    (hgrowth : K * chi M r ^ 5 ≤ (M.cutMoment 3 r).toReal)
    (hinst : (M.connCubeVertexMass r y).toReal ≤
      C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * chi M r ^ 4
        + C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * chi M r ^ 3) :
    M.cutTwoPoint r (0 : M.V) y ≤ (C3 + C4) * M.triSelf / (K * chi M r) :=
  T_le_of_twoTerm M hC3 hC4 hK hχ hTri (harris_cutMoment M r h3 y) hgrowth hinst

/-- **The two-term estimate fails wherever the connection probability is bounded below.**
If `t <= T(0,y)` and `K * t * chi_r > (C3 + C4) * nabla`, there is no way for the estimate to
hold at `y`.  With `y = 0` (`T(0,0) = 1`, `t = 1`) this is the diagonal refutation of `Main.lean`;
with `t` the edge probability of a fixed neighbour it is the same refutation at a *near but
non-zero* vertex. -/
theorem not_twoTerm_of_T_ge {C3 C4 K t : ℝ} (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4) (hK : 0 ≤ K)
    {r : ℝ} (hχ : M.cutMassAt r 0 ≠ ⊤) (h3 : M.cutMoment 3 r ≠ ⊤)
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤)
    {y : M.V} (hT : t ≤ M.cutTwoPoint r (0 : M.V) y)
    (hgrowth : K * chi M r ^ 5 ≤ (M.cutMoment 3 r).toReal)
    (hbig : (C3 + C4) * M.triSelf < K * t * chi M r) :
    ¬ ((M.connCubeVertexMass r y).toReal ≤
      C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * chi M r ^ 4
        + C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * chi M r ^ 3) := by
  intro hinst
  have hle := T_mul_chi_le_of_twoTerm' M hC3 hC4 hχ h3 hTri hgrowth hinst
  have hχnn : (0 : ℝ) ≤ chi M r := ENNReal.toReal_nonneg
  have hmono : K * t * chi M r ≤ K * M.cutTwoPoint r (0 : M.V) y * chi M r := by
    have h1 : K * t ≤ K * M.cutTwoPoint r (0 : M.V) y := mul_le_mul_of_nonneg_left hT hK
    exact mul_le_mul_of_nonneg_right h1 hχnn
  linarith

end PercLib.CriticalLRP.Smwzg77c3.M7

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.Smwzg77c3.M7.T_mul_chi_le_of_twoTerm'
#print axioms PercLib.CriticalLRP.Smwzg77c3.M7.T_le_of_twoTerm'
#print axioms PercLib.CriticalLRP.Smwzg77c3.M7.not_twoTerm_of_T_ge
