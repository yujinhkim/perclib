/-
Accepted from Ultramath `smwzg77c3`, member `m7`, independently rebuilt.
Production integration based on commit `81c6038182e9a883ffcd3d870aed7cd4829649d4`.
Original direction `d6`.

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The per-vertex form can only hold where the two-point function is small

`Main.lean` refutes the two-term estimate at the basepoint using only that the diagonal threefold
power is the bounded triangle sum.  That argument does not use anything special about the
basepoint: it uses the *lower* bound that positive association gives for the star moment at `y`,

    E[|K_0|^3 1(y ∈ K_0)] ≥ T(0,y) · E|K_0|^3 ,                              (H)

(Harris/FKG applied to the increasing functions `|K_0|^3` and `1(y ∈ K_0)`; at `y = 0` it is an
equality, which is why `Main.lean` needs no probabilistic input at all).  With (H) and the source's
Proposition I.4.20 growth `E|K_0|^3 >~ chi^5`, the two-term estimate at `y` gives

    K * T(0,y) * chi ≤ (C3 + C4) * nabla ,                                   (V)

i.e. it can only hold at vertices where `T(0,y) ≤ (C3 + C4) * nabla / (K * chi_r)`, and
`chi_r → infinity`.  So a repair that only deletes `y = 0` from the vertex range leaves the same
obstruction at every near vertex whose connection probability does not decay with `r`; the vertex
range has to be cut by *smallness of `T(0,y)`* (`StarTwoTermBoundFar` with a threshold on the
two-point function), not merely by `y != 0`.

(H) is the only ingredient here not assembled in PercLib yet; the reduction is
`starMoment_eq_tsum_labelEvent` (labelled expansion of the star moment) plus the Harris inequality
for increasing events `PercLib.Probability.prodBernoulli_harris` /
`law_harris_conn`-style two-event association applied termwise.  It is carried as an explicit
hypothesis `hHarris` so that nothing is smuggled in.  Note that at `y = 0` the hypothesis is
trivial (`T(0,0) = 1` and `connCubeVertexMass r 0 = M.cutMoment 3 r`), so `Main.lean`'s diagonal
refutation is the exact basepoint case of the theorem below.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.QZeroRepair.Main

/-! # The per-vertex constraint -/

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

/-- **The per-vertex constraint (V).**  If the two-term estimate holds at `y`, the star moment at
`y` dominates `T(0,y) * E|K_0|^3` (Harris), and `E|K_0|^3 ≥ K * chi^5`, then
`K * T(0,y) * chi ≤ (C3 + C4) * nabla`. -/
theorem T_mul_chi_le_of_twoTerm {C3 C4 K : ℝ} (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4)
    {r : ℝ} (hχ : M.cutMassAt r 0 ≠ ⊤)
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤)
    {y : M.V}
    (hHarris : M.cutTwoPoint r (0 : M.V) y * (M.cutMoment 3 r).toReal
      ≤ (M.connCubeVertexMass r y).toReal)
    (hgrowth : K * chi M r ^ 5 ≤ (M.cutMoment 3 r).toReal)
    (hinst : (M.connCubeVertexMass r y).toReal ≤
      C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * chi M r ^ 4
        + C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * chi M r ^ 3) :
    K * M.cutTwoPoint r (0 : M.V) y * chi M r ≤ (C3 + C4) * M.triSelf := by
  have hTnn : (0 : ℝ) ≤ M.cutTwoPoint r (0 : M.V) y := M.cutTwoPoint_nonneg r 0 y
  have hΛ : (0 : ℝ) ≤ M.triSelf := ENNReal.toReal_nonneg
  have hχnn : (0 : ℝ) ≤ chi M r := ENNReal.toReal_nonneg
  have hP3 : I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y ≤ M.triSelf := by
    obtain ⟨hB2, hB3, hlink⟩ := M.hB2_hB3_hlink_derived hTri
    exact I418C.source_polyK_three_le_triSelf M r hχ hTri hB2 hB3 hlink y
  have hP4 : I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y ≤ M.triSelf * chi M r :=
    (M.source_polyK_le_diag r hχ 4 y).trans (polyK_four_diag_le M hχ hTri)
  have hLHS : M.cutTwoPoint r (0 : M.V) y * (K * chi M r ^ 5) ≤
      (M.connCubeVertexMass r y).toReal :=
    (mul_le_mul_of_nonneg_left hgrowth hTnn).trans hHarris
  have hRHS : (M.connCubeVertexMass r y).toReal ≤ (C3 + C4) * M.triSelf * chi M r ^ 4 := by
    refine hinst.trans ?_
    have hχ3 : (0 : ℝ) ≤ chi M r ^ 3 := pow_nonneg hχnn 3
    have hχ4 : (0 : ℝ) ≤ chi M r ^ 4 := pow_nonneg hχnn 4
    have h1 : C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * chi M r ^ 4
        ≤ C3 * M.triSelf * chi M r ^ 4 := by
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP3 hC3) hχ4
      linarith
    have h2 : C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * chi M r ^ 3
        ≤ C4 * M.triSelf * chi M r ^ 4 := by
      have hP4' : C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * chi M r ^ 3
          ≤ C4 * (M.triSelf * chi M r) * chi M r ^ 3 := by
        have := mul_le_mul_of_nonneg_left hP4 hC4
        nlinarith
      calc C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * chi M r ^ 3
          ≤ C4 * (M.triSelf * chi M r) * chi M r ^ 3 := hP4'
        _ = C4 * M.triSelf * chi M r ^ 4 := by ring
    calc C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * chi M r ^ 4
          + C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * chi M r ^ 3
        ≤ C3 * M.triSelf * chi M r ^ 4 + C4 * M.triSelf * chi M r ^ 4 := add_le_add h1 h2
      _ = (C3 + C4) * M.triSelf * chi M r ^ 4 := by ring
  have hmain : M.cutTwoPoint r (0 : M.V) y * (K * chi M r ^ 5)
      ≤ (C3 + C4) * M.triSelf * chi M r ^ 4 := hLHS.trans hRHS
  have hχ4 : (0 : ℝ) < chi M r ^ 4 := by
    have hpos := chi_pos M r hχ
    positivity
  have e1 : M.cutTwoPoint r (0 : M.V) y * (K * chi M r ^ 5)
      = (K * M.cutTwoPoint r (0 : M.V) y * chi M r) * chi M r ^ 4 := by ring
  have e2 : (C3 + C4) * M.triSelf * chi M r ^ 4
      = ((C3 + C4) * M.triSelf) * chi M r ^ 4 := by ring
  rw [e1, e2] at hmain
  exact le_of_mul_le_mul_right hmain hχ4

/-- **The divided form**: the two-term estimate at `y` forces
`T(0,y) ≤ (C3 + C4) * nabla / (K * chi)`. -/
theorem T_le_of_twoTerm {C3 C4 K : ℝ} (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4) (hK : 0 < K)
    {r : ℝ} (hχ : M.cutMassAt r 0 ≠ ⊤)
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤)
    {y : M.V}
    (hHarris : M.cutTwoPoint r (0 : M.V) y * (M.cutMoment 3 r).toReal
      ≤ (M.connCubeVertexMass r y).toReal)
    (hgrowth : K * chi M r ^ 5 ≤ (M.cutMoment 3 r).toReal)
    (hinst : (M.connCubeVertexMass r y).toReal ≤
      C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * chi M r ^ 4
        + C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * chi M r ^ 3) :
    M.cutTwoPoint r (0 : M.V) y ≤ (C3 + C4) * M.triSelf / (K * chi M r) := by
  have h := T_mul_chi_le_of_twoTerm M hC3 hC4 hχ hTri hHarris hgrowth hinst
  have hχ0 := chi_pos M r hχ
  have hKχ : (0 : ℝ) < K * chi M r := mul_pos hK hχ0
  rw [le_div_iff₀ hKχ]
  calc M.cutTwoPoint r (0 : M.V) y * (K * chi M r) = K * M.cutTwoPoint r (0 : M.V) y * chi M r :=
        by ring
    _ ≤ (C3 + C4) * M.triSelf := h

/-- **At the basepoint the Harris hypothesis is an equality**, so the diagonal instance of
`Main.lean` is the exact `y = 0` case of the per-vertex constraint. -/
theorem T_mul_chi_le_of_twoTerm_basepoint {C3 C4 K : ℝ} (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4)
    {r : ℝ} (hχ : M.cutMassAt r 0 ≠ ⊤)
    (hTri : PercLib.CriticalLRP.TriTail.openTriangleSelf M.kernel M.kernel_nonneg M.betaCrit 0
      < ⊤)
    (hgrowth : K * chi M r ^ 5 ≤ (M.cutMoment 3 r).toReal)
    (hinst : (M.connCubeVertexMass r (0 : M.V)).toReal ≤
      C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) 0 * chi M r ^ 4
        + C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) 0 * chi M r ^ 3) :
    K * chi M r ≤ (C3 + C4) * M.triSelf := by
  have hself : M.cutTwoPoint r (0 : M.V) 0 = 1 := M.cutTwoPoint_self_eq_one r 0
  have hHarris : M.cutTwoPoint r (0 : M.V) 0 * (M.cutMoment 3 r).toReal
      ≤ (M.connCubeVertexMass r (0 : M.V)).toReal := by
    rw [hself, one_mul, connCubeVertexMass_zero]
  have h := T_mul_chi_le_of_twoTerm M hC3 hC4 hχ hTri hHarris hgrowth hinst
  simpa only [hself, mul_one, one_mul] using h

end PercLib.CriticalLRP.Smwzg77c3.M7

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.Smwzg77c3.M7.T_mul_chi_le_of_twoTerm
#print axioms PercLib.CriticalLRP.Smwzg77c3.M7.T_le_of_twoTerm
#print axioms PercLib.CriticalLRP.Smwzg77c3.M7.T_mul_chi_le_of_twoTerm_basepoint
