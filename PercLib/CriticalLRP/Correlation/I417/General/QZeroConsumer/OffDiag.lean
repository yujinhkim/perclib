/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted from Ultramath `smwzg77c3`, member `m6`, independently rebuilt.
Production integration based on commit `81c6038182e9a883ffcd3d870aed7cd4829649d4`.
Original direction `d9`.

# The repaired Case-3 consumer: off-diagonal two-term target plus the diagonal summand

The literal per-vertex two-term statement is not available at the basepoint: at `y = 0` the
left-hand side is the third moment `E|K_0|³` (`connCubeVertexMass_zero`) while the right-hand side
is `C₃ T³(0,0) χ⁴ + C₄ T⁴(0,0) χ³ ≤ (C₃ + C₄) ∇ χ⁴`, which cannot carry the Case-3 growth
`E|K|³ ⪰ χ⁵`; see `Diagonal.lean` for the compiled version of the same obstruction for the
single-term profile, and the swarm's `d6` audit for the two-term statement.  Accordingly the
consumer has to be fed

* the two-term bound **off the diagonal** (`y ≠ 0`), and
* a separate additive bound `D` for the single basepoint summand.

`connCubeMass_toReal_le_of_twoTermStarGap_offDiag` below does exactly that summation, and
`p2ExclError_le_of_offDiag` feeds the result into the landed Case-3 error estimate.  The
off-diagonal two-term bound itself is *not* proved here. After the Harris constraint, a
small-two-point region or an additive correction must replace a sole `y ≠ 0` restriction in the
remaining mathematical target; the theorem below is conditional arithmetic, not that repair.

No `sorry`, no `admit`, no `native_decide`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.QZeroConsumer.Main
public import PercLib.CriticalLRP.Correlation.I417.General.QZeroConsumer.Diagonal

/-! # Off-diagonal consumer assembly -/

noncomputable section

open MeasureTheory Measure ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology

@[expose] public section

namespace PercLib.CriticalLRP.I417QZeroConsumer

open PercLib.CriticalLRP.Orchestration
open PercLib.CriticalLRP.KernelPower

variable (M : SourceModelData)

/-- The basepoint lies in the window at nonnegative radius. -/
theorem zero_mem_ballF {r : ℝ} (hr : 0 ≤ r) : (0 : M.V) ∈ E1Sign.ballF M r := by
  rw [PercLib.CriticalLRP.E1Sign.mem_ballF, SourceModelData.ball]
  have hz : toVec (0 : M.V) = (0 : Fin M.d → ℝ) := by
    funext i
    simp [toVec]
  rw [Set.mem_ofPred_eq, hz, M.S.ρ_zero]
  exact hr

/-- **Off-diagonal two-term bound `⟹` window numerator bound, with the diagonal kept.**  The
window sum splits into the basepoint summand (bounded by `D`) and the off-diagonal summands (each
bounded by the source's two-term right-hand side and then by the polygon drivers). -/
theorem connCubeMass_toReal_le_of_twoTermStarGap_offDiag (C3 C4 Cp drv D : ℝ)
    (hgap : ∀ (r : ℝ), 1 ≤ r → ∀ y : M.V, y ≠ 0 →
      (M.connCubeVertexMass r y).toReal ≤ starRHS M C3 C4 r y)
    (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4) (_hCp : 0 ≤ Cp) (_hdrv : 0 ≤ drv)
    (r : ℝ) (hr : 1 ≤ r) (hM3 : M.cutMoment 3 r ≠ ⊤)
    (hD : (M.connCubeVertexMass r 0).toReal ≤ D)
    (hT3 : ∀ y ∈ E1Sign.ballF M r, y ≠ 0 →
      I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y ≤ Cp * drv)
    (hT4 : ∀ y ∈ E1Sign.ballF M r, y ≠ 0 →
      I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y ≤ Cp * drv * chi M r) :
    (M.connCubeMass r).toReal
      ≤ (C3 + C4) * Cp * ((M.ball r).ncard : ℝ) * drv * chi M r ^ 4 + D := by
  classical
  have hχ0 : 0 ≤ chi M r := ENNReal.toReal_nonneg
  have h0mem : (0 : M.V) ∈ E1Sign.ballF M r := zero_mem_ballF M (le_trans zero_le_one hr)
  have hne : ∀ y ∈ E1Sign.ballF M r, M.connCubeVertexMass r y ≠ ⊤ := fun y _ =>
    ne_top_of_le_ne_top hM3 (M.connCubeVertexMass_le_cutMoment_three r y)
  have hb : ∀ y ∈ E1Sign.ballF M r, y ≠ 0 →
      (M.connCubeVertexMass r y).toReal ≤ ((C3 + C4) * Cp) * drv * chi M r ^ 4 := by
    intro y hy hy0
    refine (hgap r hr y hy0).trans ?_
    have h3 : C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * chi M r ^ 4
        ≤ C3 * (Cp * drv) * chi M r ^ 4 := by
      refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hχ0 4)
      exact mul_le_mul_of_nonneg_left (hT3 y hy hy0) hC3
    have h4 : C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * chi M r ^ 3
        ≤ C4 * (Cp * drv * chi M r) * chi M r ^ 3 := by
      refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hχ0 3)
      exact mul_le_mul_of_nonneg_left (hT4 y hy hy0) hC4
    have hsum : C3 * (Cp * drv) * chi M r ^ 4 + C4 * (Cp * drv * chi M r) * chi M r ^ 3
        = ((C3 + C4) * Cp) * drv * chi M r ^ 4 := by ring
    have hrhs : starRHS M C3 C4 r y
        = C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * chi M r ^ 4
          + C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * chi M r ^ 3 := rfl
    rw [hrhs]
    linarith [h3, h4, hsum.le, hsum.ge]
  have hsplit : ∑ y ∈ E1Sign.ballF M r, (M.connCubeVertexMass r y).toReal
      = (M.connCubeVertexMass r 0).toReal
        + ∑ y ∈ (E1Sign.ballF M r).erase 0, (M.connCubeVertexMass r y).toReal := by
    rw [eq_comm, Finset.add_sum_erase _ (fun y => (M.connCubeVertexMass r y).toReal) h0mem]
  have hoff : ∑ y ∈ (E1Sign.ballF M r).erase 0, (M.connCubeVertexMass r y).toReal
      ≤ ∑ _y ∈ (E1Sign.ballF M r).erase 0, ((C3 + C4) * Cp) * drv * chi M r ^ 4 := by
    refine Finset.sum_le_sum fun y hy => ?_
    exact hb y (Finset.mem_of_mem_erase hy) (Finset.ne_of_mem_erase hy)
  have hcard : ((E1Sign.ballF M r).erase 0).card ≤ (E1Sign.ballF M r).card :=
    Finset.card_erase_le
  have hconst : (0 : ℝ) ≤ ((C3 + C4) * Cp) * drv * chi M r ^ 4 := by
    have : (0 : ℝ) ≤ (C3 + C4) * Cp := by
      have := add_nonneg hC3 hC4
      positivity
    positivity
  rw [M.connCubeMass_eq_sum_vertex r, ENNReal.toReal_sum hne, hsplit]
  have hoff2 : ∑ _y ∈ (E1Sign.ballF M r).erase 0, ((C3 + C4) * Cp) * drv * chi M r ^ 4
      ≤ ((M.ball r).ncard : ℝ) * (((C3 + C4) * Cp) * drv * chi M r ^ 4) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ hconst
    have : (((E1Sign.ballF M r).erase 0).card : ℝ) ≤ ((E1Sign.ballF M r).card : ℝ) := by
      exact_mod_cast hcard
    rwa [E1Sign.card_ballF] at this
  have := hoff.trans hoff2
  have hfinal : ((E1Sign.ballF M r).erase 0).card • (((C3 + C4) * Cp) * drv * chi M r ^ 4)
      = (↑((E1Sign.ballF M r).erase 0).card : ℝ) * (((C3 + C4) * Cp) * drv * chi M r ^ 4) :=
    nsmul_eq_mul _ _
  linarith [this, hD, hfinal]

/-- **The repaired Case-3 conclusion.**  If the off-diagonal two-term bound holds, the basepoint
summand `D` is absorbable in the window (`D ≤ (C₃+C₄) Cp |B_r| drv χ⁴`), and the Case-3 moment gap
holds, then `E_{2,r} ≤ (2 (C₃+C₄) Cp / c₃) (∇_{r^c} + r^{-c})` eventually.  The factor `2` is the
single bookkeeping cost of keeping the diagonal summand separate. -/
theorem p2ExclError_le_of_offDiag (C3 C4 Cp c c3 D : ℝ)
    (hgap : ∀ (r : ℝ), 1 ≤ r → ∀ y : M.V, y ≠ 0 →
      (M.connCubeVertexMass r y).toReal ≤ starRHS M C3 C4 r y)
    (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4) (hCp : 0 ≤ Cp) (hc3 : 0 < c3)
    (h2 : ∀ r : ℝ, 1 ≤ r → M.cutMoment 2 r ≠ ⊤)
    (hM3 : ∀ r : ℝ, 1 ≤ r → M.cutMoment 3 r ≠ ⊤)
    (hcm : ∀ r : ℝ, 1 ≤ r → M.connCubeMass r ≠ ⊤)
    (hD : ∀ r : ℝ, 1 ≤ r → (M.connCubeVertexMass r 0).toReal ≤ D)
    (hDabs : ∀ r : ℝ, 1 ≤ r →
      D ≤ (C3 + C4) * Cp * ((M.ball r).ncard : ℝ) * M.case3Driver c r * chi M r ^ 4)
    (hT3 : ∀ r : ℝ, 1 ≤ r → ∀ y ∈ E1Sign.ballF M r, y ≠ 0 →
      I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y ≤ Cp * M.case3Driver c r)
    (hT4 : ∀ r : ℝ, 1 ≤ r → ∀ y ∈ E1Sign.ballF M r, y ≠ 0 →
      I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y ≤ Cp * M.case3Driver c r * chi M r)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * chi M r ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    ∀ᶠ r : ℝ in atTop,
      M.p2ExclError r ≤ ((2 * ((C3 + C4) * Cp)) / c3) * M.case3Driver c r := by
  have hK : (0 : ℝ) ≤ (C3 + C4) * Cp := by
    have := add_nonneg hC3 hC4
    positivity
  have hnum : ∀ᶠ r : ℝ in atTop,
      (M.connCubeMass r).toReal ≤
        (2 * ((C3 + C4) * Cp)) * ((M.ball r).ncard : ℝ) * M.case3Driver c r
          * chi M r ^ 4 := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
    have hdrv : (0 : ℝ) ≤ M.case3Driver c r := M.case3Driver_nonneg_of_one_le hr
    have h1 := connCubeMass_toReal_le_of_twoTermStarGap_offDiag M C3 C4 Cp
      (M.case3Driver c r) D hgap hC3 hC4 hCp hdrv r hr (hM3 r hr) (hD r hr)
      (hT3 r hr) (hT4 r hr)
    have h2' := hDabs r hr
    calc (M.connCubeMass r).toReal
        ≤ (C3 + C4) * Cp * ((M.ball r).ncard : ℝ) * M.case3Driver c r * chi M r ^ 4 + D := h1
      _ ≤ (C3 + C4) * Cp * ((M.ball r).ncard : ℝ) * M.case3Driver c r * chi M r ^ 4
            + (C3 + C4) * Cp * ((M.ball r).ncard : ℝ) * M.case3Driver c r * chi M r ^ 4 := by
          linarith
      _ = (2 * ((C3 + C4) * Cp)) * ((M.ball r).ncard : ℝ) * M.case3Driver c r
            * chi M r ^ 4 := by ring
  exact M.p2ExclError_le_case3Driver (K := 2 * ((C3 + C4) * Cp)) (c := c) (r₀ := 1)
    (by positivity) hc3 (fun r hr => h2 r hr) hcm hnum hgm

/-- **The repaired consumer with the basepoint bound made concrete.**  Taking the basepoint
summand to be its tree-graph bound `E|K_0|³ ≤ 3 χ⁵` (`connCubeVertexMass_zero_le`), the
off-diagonal two-term bound and the polygon drivers give

`E[|K_0|³ |K_0 ∩ B_r|] ≤ 2 (C₃+C₄) Cp |B_r| drv χ⁴`

under the single scalar condition `3 χ ≤ (C₃+C₄) Cp |B_r| drv` (which holds for large `r` in
Case 3, where `χ ≍ r^α` and `|B_r| drv ≍ r^d drv` with `α < d`). -/
theorem connCubeMass_toReal_le_of_twoTermStarGap_offDiag_three (C3 C4 Cp drv : ℝ)
    (hgap : ∀ (r : ℝ), 1 ≤ r → ∀ y : M.V, y ≠ 0 →
      (M.connCubeVertexMass r y).toReal ≤ starRHS M C3 C4 r y)
    (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4) (hCp : 0 ≤ Cp) (hdrv : 0 ≤ drv)
    (r : ℝ) (hr : 1 ≤ r) (hM3 : M.cutMoment 3 r ≠ ⊤) (hχ : M.cutMassAt r 0 ≠ ⊤)
    (hT3 : ∀ y ∈ E1Sign.ballF M r, y ≠ 0 →
      I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y ≤ Cp * drv)
    (hT4 : ∀ y ∈ E1Sign.ballF M r, y ≠ 0 →
      I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y ≤ Cp * drv * chi M r)
    (hsmall : 3 * chi M r ≤ (C3 + C4) * Cp * ((M.ball r).ncard : ℝ) * drv) :
    (M.connCubeMass r).toReal
      ≤ 2 * ((C3 + C4) * Cp * ((M.ball r).ncard : ℝ) * drv * chi M r ^ 4) := by
  have hχ0 : 0 ≤ chi M r := ENNReal.toReal_nonneg
  have hdiag : (M.connCubeVertexMass r 0).toReal ≤ 3 * chi M r ^ 5 := by
    have h := connCubeVertexMass_zero_le M r
    have hne : 3 * (M.cutMassAt r 0) ^ 5 ≠ ⊤ :=
      ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top hχ)
    have h' := ENNReal.toReal_mono hne h
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_pow, ← chi] at h'
    exact h'
  have hDabs : 3 * chi M r ^ 5
      ≤ (C3 + C4) * Cp * ((M.ball r).ncard : ℝ) * drv * chi M r ^ 4 := by
    have hmul := mul_le_mul_of_nonneg_right hsmall (pow_nonneg hχ0 4)
    calc 3 * chi M r ^ 5 = (3 * chi M r) * chi M r ^ 4 := by ring
      _ ≤ ((C3 + C4) * Cp * ((M.ball r).ncard : ℝ) * drv) * chi M r ^ 4 := hmul
      _ = (C3 + C4) * Cp * ((M.ball r).ncard : ℝ) * drv * chi M r ^ 4 := by ring
  have hmain := connCubeMass_toReal_le_of_twoTermStarGap_offDiag M C3 C4 Cp drv
    (3 * chi M r ^ 5) hgap hC3 hC4 hCp hdrv r hr hM3 hdiag hT3 hT4
  linarith [hmain, hDabs]

end PercLib.CriticalLRP.I417QZeroConsumer
