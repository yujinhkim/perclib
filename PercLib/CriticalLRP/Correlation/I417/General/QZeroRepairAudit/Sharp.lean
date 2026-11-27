/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwziumdb`.
Supporting integration based on production commit `5d2d681b941eb1c687f1ba17e6a798b8f0175aa0`.

Ultramath swarm `smwziumdb`, member `m2`, direction `d5`.

# Sharpness of the additive repair, and the input it actually needs

The `q = 0`, `p = 3` star target

  `E[|K_0|³ 1(y ∈ K_0)] ≤ C₃ T³(0,y) χ⁴ + C₄ T⁴(0,y) χ³`

is false at the diagonal (`QZeroDiagonal.not_hasPerVertexTwoTermHgap`), so every repair under audit
adds a correction term.  This file proves three things about any such repair.

1. `diag_correction_lower_bound` — at `y = 0` the source's Case-3 inputs (`QZeroDiagInputs`:
   `E|K|³ ⪰ c χ⁵`, `T³(0,0) ≤ ∇`, `T⁴(0,0) ≤ ∇χ`) force *every* correction `E(r)` at the
   diagonal to satisfy `c χ⁵ ≤ (C₃+C₄) ∇ χ⁴ + E(r)`.  Since `∇ < ∞` and `χ → ∞`, the two main
   terms contribute `o(χ⁵)`: **the correction must itself be of order `χ⁵` at the diagonal.**
2. `additive_const_ge` — consequently the additive repair `… + C₅ T(0,y) χ⁵` needs `C₅ ≥ c`.
   With Proposition I.4.20 at `p = 3`, `c = (2·3−3)!! = 3`: the `χ⁵` correction is sharp.
3. `additive_of_gap_of_cov` — the additive repair is *implied by* the product-gap target
   `HasProductGap` (Lemma I.4.17 at `(1,2)`, equivalently the `(2,1)` interface at the reversed
   pair) together with a positive-association **covariance** bound `HasCovBound`.

Points 2 and 3 together identify the missing input of the `q = 0` star repair precisely: it is a
Harris-type upper bound on `Cov(|K_0|,|K_y|²)` with constant at least `3`, not a tree-diagram
count.  The product-gap target itself is not refuted at the diagonal
(`gapVert_diag_cutProb`: there the gap is `χ · E|K|²`).
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.QZeroRepairAudit.Model

/-! # Independently reviewed Case-3 repair-audit module: Sharp -/


noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Measure ProbabilityTheory unitInterval Filter
open scoped ENNReal NNReal Topology BigOperators

@[expose] public section

namespace PercLib.CriticalLRP
namespace QZeroRepairAudit

attribute [local instance] Classical.propDecidable

open Orchestration

namespace SourceModelData

variable (M : SourceModelData)

/-! ## 2. The two diagonal matrix powers from the landed `PowerInputs` package -/

/-- `T³(0,0) ≤ ∇`: the diagonal `ℓ = 3` entry is the triangle constant (field `triSup` of the
landed `I418C.PowerInputs`). -/
theorem polyK_three_diag_le {c R : ℝ} (hQI : QZeroDiagInputs M c R) {r : ℝ}
    (hr : max R 1 ≤ r) :
    I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) 0 ≤ M.triSelf :=
  (hQI.powerInputs r hr).triSup 0

/-- `T⁴(0,0) ≤ ∇ χ`: composing `T³` with the column sum `∑_y T(y,0) = χ` (fields `comp` and
`colsum` of `I418C.PowerInputs`). -/
theorem polyK_four_diag_le {c R : ℝ} (hQI : QZeroDiagInputs M c R) {r : ℝ}
    (hr : max R 1 ≤ r) :
    I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) 0 ≤ M.triSelf * M.chiReal r := by
  have hPI := hQI.powerInputs r hr
  have hcomp := hPI.comp 1
  rw [show (1 : ℕ) + 3 = 4 from rfl] at hcomp
  have hsummable : Summable (fun y : M.V =>
      M.triSelf * I418C.polyK (M.cutTwoPoint r) 1 y 0) :=
    (hPI.colSummable 1).mul_left M.triSelf
  have hbound : ∀ y : M.V, I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y *
        I418C.polyK (M.cutTwoPoint r) 1 y 0
      ≤ M.triSelf * I418C.polyK (M.cutTwoPoint r) 1 y 0 :=
    fun y => mul_le_mul_of_nonneg_right (hPI.triSup y) (hPI.nonneg 1 y 0)
  rw [hcomp]
  calc ∑' y : M.V, I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y *
        I418C.polyK (M.cutTwoPoint r) 1 y 0
      ≤ ∑' y : M.V, M.triSelf * I418C.polyK (M.cutTwoPoint r) 1 y 0 :=
        (hPI.compSummable 1).tsum_le_tsum hbound hsummable
    _ = M.triSelf * ∑' y : M.V, I418C.polyK (M.cutTwoPoint r) 1 y 0 := tsum_mul_left
    _ = M.triSelf * M.chiReal r := by rw [hPI.colsum 1, pow_one]; rfl

/-- A pure-real division inequality: if `A ≥ 0`, `ε > 0` and `A/ε + 1 ≤ χ` then `A/χ ≤ ε`. -/
theorem div_le_of_le_div_add_one {A ε χ : ℝ} (hε : 0 < ε) (hχpos : 0 < χ)
    (hχ : A / ε + 1 ≤ χ) : A / χ ≤ ε := by
  have hAεlt : A / ε < χ := by linarith
  have hAlt : A < χ * ε := (div_lt_iff₀ hε).mp hAεlt
  rw [div_le_iff₀ hχpos]
  calc A ≤ χ * ε := le_of_lt hAlt
    _ = ε * χ := by ring

/-! ## 3. The diagonal constraint on any correction term -/

/-- **Every correction term is bounded below at the diagonal.**

Let `E : ℝ` be *any* correction added to the two-term display at the vertex `y = 0`.  Under the
source's Case-3 inputs, the instance at `y = 0` (where `T^ℓ(0,0) ≤ ∇`, the left-hand side is
`(M.cutMoment 3 r).toReal ⪰ c χ⁵`) forces

  `c χ⁵ ≤ (C₃ + C₄) ∇ χ⁴ + E`.

Since `χ → ∞` and `∇ < ∞`, the two main terms are `o(χ⁵)`: the correction must be of order `χ⁵`
at the diagonal. -/
theorem diag_correction_lower_bound {c R : ℝ} (hQI : QZeroDiagInputs M c R) {C3 C4 E : ℝ}
    (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4) {r : ℝ} (hr : max R 1 ≤ r)
    (hinst : (M.connCubeVertexMass r 0).toReal ≤
      C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) 0 * M.chiReal r ^ 4 +
        C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) 0 * M.chiReal r ^ 3 + E) :
    c * M.chiReal r ^ 5 ≤ (C3 + C4) * M.triSelf * M.chiReal r ^ 4 + E := by
  have h3 := hQI.third_lower r hr
  have hP3 := polyK_three_diag_le M hQI hr
  have hP4 := polyK_four_diag_le M hQI hr
  have hχ1 := hQI.chi_one_le r hr
  have hχ0 : (0 : ℝ) ≤ M.chiReal r := ENNReal.toReal_nonneg
  have hχ3 : (0 : ℝ) ≤ M.chiReal r ^ 3 := pow_nonneg hχ0 3
  have hχ4 : (0 : ℝ) ≤ M.chiReal r ^ 4 := pow_nonneg hχ0 4
  have hstep : C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) 0 * M.chiReal r ^ 4 +
        C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) 0 * M.chiReal r ^ 3
      ≤ (C3 + C4) * M.triSelf * M.chiReal r ^ 4 := by
    have h1 : C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) 0 * M.chiReal r ^ 4
        ≤ C3 * M.triSelf * M.chiReal r ^ 4 := by
      have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP3 hC3) hχ4
      linarith [h]
    have h2 : C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) 0 * M.chiReal r ^ 3
        ≤ C4 * M.triSelf * M.chiReal r ^ 4 := by
      have h4 := mul_le_mul_of_nonneg_left hP4 hC4
      calc C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) 0 * M.chiReal r ^ 3
          ≤ C4 * (M.triSelf * M.chiReal r) * M.chiReal r ^ 3 :=
            mul_le_mul_of_nonneg_right h4 hχ3
        _ = C4 * M.triSelf * M.chiReal r ^ 4 := by ring
    linarith
  calc c * M.chiReal r ^ 5 ≤ (M.cutMoment 3 r).toReal := h3
    _ = (M.connCubeVertexMass r 0).toReal := by rw [M.connCubeVertexMass_zero]
    _ ≤ C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) 0 * M.chiReal r ^ 4 +
          C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) 0 * M.chiReal r ^ 3 + E := hinst
    _ ≤ (C3 + C4) * M.triSelf * M.chiReal r ^ 4 + E := by linarith

/-! ## 4. The additive constant is at least the third-moment coefficient -/

/-- **`C₅ ≥ c`: the `χ⁵` correction cannot be cheaper than the third-moment coefficient.**

If the additive repair `HasAdditiveStar C3 C4 C5` holds, then the source's Case-3 inputs force
`c ≤ C₅`.  With Proposition I.4.20 at `p = 3`, `c = (2·3−3)!! = 3`.  In particular `C₅ = 0` is
impossible, which recovers the diagonal obstruction. -/
theorem additive_const_ge {c R : ℝ} (hQI : QZeroDiagInputs M c R) {C3 C4 C5 : ℝ}
    (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4) (hadd : HasAdditiveStar M C3 C4 C5) : c ≤ C5 := by
  by_contra hcon
  rw [not_le] at hcon
  have hε : 0 < (c - C5) / 2 := by linarith
  obtain ⟨r, hr, hbig⟩ :=
    hQI.chi_unbounded ((C3 + C4) * M.triSelf / ((c - C5) / 2) + 1)
  have hr1 : (1 : ℝ) ≤ r := le_trans (le_max_right R 1) hr
  have hχ1 := hQI.chi_one_le r hr
  have hχpos : (0 : ℝ) < M.chiReal r := lt_of_lt_of_le one_pos hχ1
  have hx : (C3 + C4) * M.triSelf / M.chiReal r ≤ (c - C5) / 2 :=
    div_le_of_le_div_add_one hε hχpos hbig
  have hinst := hadd r hr1 0
  rw [M.cutTwoPoint_self_eq_one r (0 : M.V), mul_one] at hinst
  have hb := diag_correction_lower_bound M hQI hC3 hC4 hr hinst
  have hχ5 : (0 : ℝ) < M.chiReal r ^ 5 := by positivity
  have hdiv : c ≤ ((C3 + C4) * M.triSelf * M.chiReal r ^ 4 + C5 * M.chiReal r ^ 5)
      / M.chiReal r ^ 5 :=
    (le_div_iff₀ hχ5).mpr (by linarith [hb])
  have hsimp : ((C3 + C4) * M.triSelf * M.chiReal r ^ 4 + C5 * M.chiReal r ^ 5)
      / M.chiReal r ^ 5 = (C3 + C4) * M.triSelf / M.chiReal r + C5 := by
    field_simp
  rw [hsimp] at hdiv
  linarith

/-! ## 5. The per-vertex decomposition in the model, and the covariance reduction -/

/-- **The per-vertex star is the per-vertex product gap plus the covariance**, at the source's
cutoff law, with the finiteness of the first two cutoff moments and of the third star moment. -/
theorem connCubeVertexMass_toReal_eq_gapVert_add_covVert (r : ℝ) (y : M.V)
    (h2 : M.cutMoment 2 r ≠ ⊤) (h3 : M.cutMoment 3 r ≠ ⊤) :
    (M.connCubeVertexMass r y).toReal
      = (gapVert (M.cutProb r) (0 : M.V) y 1 2).toReal +
        (covVert (M.cutProb r) (0 : M.V) y 1 2).toReal := by
  classical
  let := Encodable.ofCountable (Sym2 M.V)
  have h1 : M.cutMoment 1 r ≠ ⊤ := M.cutMoment_one_ne_top_of_two h2
  have hP : prodVert (M.cutProb r) (0 : M.V) y 1 2 ≠ ⊤ := by
    rw [prodVert, M.powMomentAt_cutProb_eq_cutMoment, M.powMomentAt_cutProb_eq_cutMoment]
    exact ENNReal.mul_ne_top h1 h2
  have hstar : starVert (M.cutProb r) (0 : M.V) y 3 ≤ M.cutMoment 3 r := by
    rw [starVert_cutProb_eq_connCubeVertexMass M r y]
    exact M.connCubeVertexMass_le_cutMoment_three r y
  have hJ : jointVert (M.cutProb r) (0 : M.V) y 1 2 ≠ ⊤ := by
    have hje := jointVert_eq_excl_add_star (M.cutProb r) (0 : M.V) y 1 2
    have hexcl : exclVert (M.cutProb r) (0 : M.V) y 1 2
        ≤ prodVert (M.cutProb r) (0 : M.V) y 1 2 :=
      exclVert_le_prodVert (M.cutProb r) (E1Sign.cutProb_lt_one M r)
        (Percolation.edgeExhaustion (E := Sym2 M.V)) Percolation.edgeExhaustion_mono
        Percolation.edgeExhaustion_cover (0 : M.V) y 1 2
    rw [hje]
    exact ENNReal.add_ne_top.mpr
      ⟨ne_top_of_le_ne_top hP hexcl, ne_top_of_le_ne_top h3 hstar⟩
  rw [← starVert_cutProb_eq_connCubeVertexMass M r y]
  exact starVert_toReal_eq_gapVert_add_covVert (M.cutProb r) (E1Sign.cutProb_lt_one M r)
    (Percolation.edgeExhaustion (E := Sym2 M.V)) Percolation.edgeExhaustion_mono
    Percolation.edgeExhaustion_cover (0 : M.V) y 1 2 hP hJ

/-- **The additive repair follows from the product gap plus a covariance bound.**

This is the exact identification of the missing input: `HasProductGap` is the diagram/Lemma-I.4.17
side (which the `(2,1)` interface supplies at the reversed pair `(y,0)`), and `HasCovBound` is a
positive-association upper bound on `Cov(|K_0|,|K_y|²)`.  Nothing in the product-gap target alone
controls the star (`Main.starVert_toReal_eq_gapVert_add_covVert`). -/
theorem additive_of_gap_of_cov {C3 C4 C5 : ℝ} (hgap : HasProductGap M C3 C4)
    (hcov : HasCovBound M C5) (h2 : ∀ r : ℝ, 1 ≤ r → M.cutMoment 2 r ≠ ⊤)
    (h3 : ∀ r : ℝ, 1 ≤ r → M.cutMoment 3 r ≠ ⊤) : HasAdditiveStar M C3 C4 C5 := by
  intro r hr y
  rw [connCubeVertexMass_toReal_eq_gapVert_add_covVert M r y (h2 r hr) (h3 r hr)]
  have hg := hgap r hr y
  have hc := hcov r hr y
  linarith

/-- **The product gap at the diagonal is `χ · E|K|²`.**  This is why the product-gap target
survives the diagonal that refutes the star target: there the star is `E|K|³ ≍ χ⁵` while the
product gap is the product of the first two moments, `≍ χ⁴`. -/
theorem gapVert_diag_cutProb (r : ℝ) :
    gapVert (M.cutProb r) (0 : M.V) (0 : M.V) 1 2
      = M.cutMoment 1 r * M.cutMoment 2 r := by
  rw [gapVert_self_eq_prodVert]
  simp only [prodVert, M.powMomentAt_cutProb_eq_cutMoment]

end SourceModelData

end QZeroRepairAudit
end PercLib.CriticalLRP
