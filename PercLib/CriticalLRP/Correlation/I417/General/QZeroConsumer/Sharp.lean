/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted from Ultramath `smwzg77c3`, member `m6`, independently rebuilt.
Production integration based on commit `81c6038182e9a883ffcd3d870aed7cd4829649d4`.
Original direction `d9`.

# The `χ³ T` sharp profile closes the Case-3 numerator with no polygon driver

The single-term profile bound `E[|K_0|³ 1(y ∈ K_0)] ≤ C χ³ T(0,y)` (`SharpProfile`) sums over the
window against the row sum `∑_y T(0,y) = χ`, giving `E[|K_0|³ |K_0 ∩ B_r|] ≤ C χ⁴` and hence
`E_{2,r} ≤ (C / c₃) / |B_r|` — with no `|B_r|` window factor, no `∇` driver, and in particular
without the pointwise `ℓ = 3` driver that is refuted at the origin
(`pointwise_driver_three_obstructed` in `Main.lean`).  This is the Case-3 numerator estimate for
which the source uses Lemma I.4.17 at `p = 3`, `q = 0`.

**Caveat — the hypothesis is not attainable.**  `SharpProfile` is *strictly stronger* than the
two-term display, and at the basepoint it demands `E|K_0|³ ≤ C χ³`.  `Diagonal.lean` proves that
log-convexity of the cluster moments together with the Case-3 moment gap `c₃ χ³ ≤ E|K|²` turn this
into `χ² ≤ C / c₃²`, i.e. a bound on the susceptibility: `sharpProfile_diag_no_go`.  So this file
is a *conditional consumer* (its conclusion is what Case 3 needs, its hypothesis is unattainable),
and the two-term source display remains the statement to prove, off the diagonal.

No `sorry`, no `admit`, no `native_decide`, no custom axioms.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.QZeroConsumer.Main

/-! # The sharp profile and the Case-3 numerator -/

noncomputable section

open MeasureTheory Measure ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology

@[expose] public section

namespace PercLib.CriticalLRP.I417QZeroConsumer

open PercLib.CriticalLRP.Orchestration
open PercLib.CriticalLRP.KernelPower

variable (M : SourceModelData)

/-! ## The sharp profile closes the Case-3 numerator with no driver at all -/

/-- The real row sum `∑_y T(0,y) = χ` of the truncated two-point function. -/
theorem tsum_cutTwoPoint_row (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) :
    (∑' y : M.V, M.cutTwoPoint r (0 : M.V) y) = chi M r := by
  rw [show (∑' y : M.V, M.cutTwoPoint r (0 : M.V) y)
      = ∑' y : M.V, I418C.polyK (M.cutTwoPoint r) 1 (0 : M.V) y from
      tsum_congr fun y => (I418C.polyK_one (M.cutTwoPoint r) 0 y).symm]
  simpa using tsum_polyK_row M r hχ 1

/-- The rows of the truncated two-point function are summable in `ℝ`. -/
theorem summable_cutTwoPoint_row (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) :
    Summable (fun y : M.V => M.cutTwoPoint r (0 : M.V) y) := by
  have h := summable_polyK_row M r hχ 1
  simpa only [I418C.polyK_one] using h

/-- **The sharp profile bounds the whole Case-3 numerator by `C χ⁴`.**  Summing
`E[|K_0|³ 1(y ∈ K_0)] ≤ C χ³ T(0,y)` over the window and using the row sum
`∑_y T(0,y) = χ` gives `E[|K_0|³ |K_0 ∩ B_r|] ≤ C χ⁴`, with no polygon driver and no `|B_r|`. -/
theorem connCubeMass_toReal_le_of_sharpProfile (C : ℝ) (hC : 0 ≤ C) (hsharp : SharpProfile M C)
    (r : ℝ) (hr : 1 ≤ r) (hχ : M.cutMassAt r 0 ≠ ⊤) (hM3 : M.cutMoment 3 r ≠ ⊤) :
    (M.connCubeMass r).toReal ≤ C * chi M r ^ 4 := by
  classical
  have hχ0 : 0 ≤ chi M r := ENNReal.toReal_nonneg
  have hne : ∀ y ∈ E1Sign.ballF M r, M.connCubeVertexMass r y ≠ ⊤ := fun y _ =>
    ne_top_of_le_ne_top hM3 (M.connCubeVertexMass_le_cutMoment_three r y)
  have hsumm : Summable (fun y : M.V => M.cutTwoPoint r (0 : M.V) y) :=
    summable_cutTwoPoint_row M r hχ
  have hT0 : ∀ y : M.V, 0 ≤ M.cutTwoPoint r (0 : M.V) y := fun y =>
    M.cutTwoPoint_nonneg r 0 y
  rw [M.connCubeMass_eq_sum_vertex r, ENNReal.toReal_sum hne]
  refine (Finset.sum_le_sum fun y _ => hsharp r hr y).trans ?_
  have hstep : ∑ y ∈ E1Sign.ballF M r, C * chi M r ^ 3 * M.cutTwoPoint r (0 : M.V) y
      ≤ C * chi M r ^ 3 * (∑' y : M.V, M.cutTwoPoint r (0 : M.V) y) := by
    have := Summable.sum_le_tsum (s := E1Sign.ballF M r)
      (f := fun y : M.V => C * chi M r ^ 3 * M.cutTwoPoint r (0 : M.V) y)
      (fun i _ => mul_nonneg (mul_nonneg hC (pow_nonneg hχ0 3)) (hT0 i))
      (hsumm.mul_left (C * chi M r ^ 3))
    rwa [tsum_mul_left] at this
  refine hstep.trans ?_
  rw [tsum_cutTwoPoint_row M r hχ]
  have hpow : C * chi M r ^ 3 * chi M r = C * chi M r ^ 4 := by ring
  rw [hpow]

/-- **The sharp profile gives `E_{2,r} ≤ (C / c₃) / |B_r|`**: vanishing, and logarithmically
integrable without any polygon input, because the `χ⁴` of the numerator is exactly cancelled by
the `χ · c₃ χ³` of the denominator.  This is the Case-3 numerator estimate that the two-term
`ℓ = 3, 4` display is used for in the source, obtained from the single-term sharp profile. -/
theorem p2ExclError_le_of_sharpProfile (C c3 : ℝ) (hC : 0 ≤ C) (hc3 : 0 < c3)
    (hsharp : SharpProfile M C) (hM2 : ∀ r : ℝ, 1 ≤ r → M.cutMoment 2 r ≠ ⊤)
    (hM3 : ∀ r : ℝ, 1 ≤ r → M.cutMoment 3 r ≠ ⊤)
    (hcm : ∀ r : ℝ, 1 ≤ r → M.connCubeMass r ≠ ⊤)
    (hgm : ∀ᶠ r : ℝ in atTop, c3 * chi M r ^ 3 ≤ (M.cutMoment 2 r).toReal) :
    ∀ᶠ r : ℝ in atTop, M.p2ExclError r ≤ (C / c3) / ((M.ball r).ncard : ℝ) := by
  filter_upwards [eventually_ge_atTop (1 : ℝ), hgm] with r hr hg
  have h2 := hM2 r hr
  have h3 := hM3 r hr
  have hc := hcm r hr
  have h1 : M.cutMoment 1 r ≠ ⊤ := M.cutMoment_one_ne_top_of_two h2
  have hχeq : M.cutMassAt r 0 = M.cutMoment 1 r := M.cutMassAt_zero_eq_cutMoment r
  have hχne : M.cutMassAt r 0 ≠ ⊤ := by rw [hχeq]; exact h1
  have hA1 : (1 : ℝ) ≤ (M.cutMoment 1 r).toReal := M.one_le_cutMoment_one_toReal r h1
  have hA2 : (0 : ℝ) < (M.cutMoment 2 r).toReal :=
    lt_of_lt_of_le one_pos (M.one_le_cutMoment_two_toReal r h2)
  have hb : (0 : ℝ) < ((M.ball r).ncard : ℝ) := by
    exact_mod_cast M.ball_ncard_pos r (le_trans zero_le_one hr)
  have hA1eq : (M.cutMoment 1 r).toReal = chi M r := by
    rw [chi, ← hχeq]
  have hnum : (M.connCubeMass r).toReal ≤ C * chi M r ^ 4 :=
    connCubeMass_toReal_le_of_sharpProfile M C hC hsharp r hr hχne h3
  have hden : (0 : ℝ) < ((M.ball r).ncard : ℝ) * (M.cutMoment 1 r).toReal
      * (M.cutMoment 2 r).toReal := by
    have : (0 : ℝ) < (M.cutMoment 1 r).toReal := lt_of_lt_of_le one_pos hA1
    positivity
  have hden1 : (0 : ℝ) < ((M.ball r).ncard : ℝ) * (M.cutMoment 1 r).toReal
      * (c3 * chi M r ^ 3) := by
    have hχ0 : 0 < chi M r := by rw [← hA1eq]; exact lt_of_lt_of_le one_pos hA1
    positivity
  have hden_le : ((M.ball r).ncard : ℝ) * (M.cutMoment 1 r).toReal * (c3 * chi M r ^ 3)
      ≤ ((M.ball r).ncard : ℝ) * (M.cutMoment 1 r).toReal * (M.cutMoment 2 r).toReal := by
    refine mul_le_mul_of_nonneg_left hg ?_
    have hχ0 : 0 < chi M r := by rw [← hA1eq]; exact lt_of_lt_of_le one_pos hA1
    positivity
  have hstep : (C * chi M r ^ 4) / (((M.ball r).ncard : ℝ) * (M.cutMoment 1 r).toReal
        * (M.cutMoment 2 r).toReal)
      ≤ (C * chi M r ^ 4) / (((M.ball r).ncard : ℝ) * (M.cutMoment 1 r).toReal
        * (c3 * chi M r ^ 3)) :=
    div_le_div_of_nonneg_left (by positivity) hden1 hden_le
  have hsimp : (C * chi M r ^ 4) / (((M.ball r).ncard : ℝ) * (M.cutMoment 1 r).toReal
        * (c3 * chi M r ^ 3))
      = (C / c3) / ((M.ball r).ncard : ℝ) := by
    rw [hA1eq]
    have hχ0 : chi M r ≠ 0 := by
      intro h0
      have h1' : (1 : ℝ) ≤ chi M r := by rw [← hA1eq]; exact hA1
      rw [h0] at h1'; linarith
    have hbn : ((M.ball r).ncard : ℝ) ≠ 0 := ne_of_gt hb
    have hc3n : c3 ≠ 0 := ne_of_gt hc3
    field_simp
  exact (M.p2ExclError_le_connCubeMass_div r (le_trans zero_le_one hr) h2 hc).trans
    ((div_le_div_of_nonneg_right hnum hden.le).trans (hstep.trans (le_of_eq hsimp)))


end PercLib.CriticalLRP.I417QZeroConsumer
