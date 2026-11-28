/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

# The off-diagonal covariance target is the pinned `q = 0`, `p = 3` star of Lemma I.4.17

Source: T. Hutchcroft, *Critical long-range percolation I: High effective dimension*,
arXiv:2508.18807v1.

* Lemma I.4.17, printed p. 45: there are universal integers `C_{p,q,ℓ}` with
  `0 ≤ E|K|^p E|K|^q − E[|K_x|^p |K_y|^q 1(x ↮ y)]`
  `  ≤ ∑_{ℓ=3}^{p+q+1} C_{p,q,ℓ} T^ℓ(x,y) (E|K|)^{2p+2q+1−ℓ}`
  for all `x, y`, where `T^ℓ` is the `ℓ`-fold power of the two-point matrix.  At `(p,q) = (0,3)`
  the difference is *exactly* the one-copy star `E[|K_y|³ 1(x ↔ y)]` and the right-hand side is
  `C_{0,3,3} T³(x,y) χ⁴ + C_{0,3,4} T⁴(x,y) χ³`.
* Lemma I.2.1 (printed p. 21):
  `0 ≤ E[F(K_x)G(K_y)] − E F(K_x) E G(K_y) ≤ E[F(K_x)G(K_y) 1(x ↔ y)]`,
  i.e. at `F = |K|`, `G = |K|²` the covariance is dominated by the star.

The campaign's repair target `QZeroRepairAudit.SourceModelData.HasCovBound M C₅` is
`Cov(|K_0|,|K_y|²) ≤ C₅ T(0,y) χ⁵` for every cutoff radius `r ≥ 1` and every vertex `y`
(`QZeroRepairAudit/Defs.lean`).  By the second display it is implied by the *star-forced* bound
`E[1(y ∈ K_0)|K_0|³] ≤ C₅ T(0,y) χ⁵`
(`QZeroRepairAudit.Diagonal.Main.hasCovBound_of_starWeighted`), and by
`starVert_toReal_eq_gapVert_add_covVert` and the *proved* `(2,1)` product gap
(`QZeroRepairAudit.ProductGap.hasProductGap_one_two`) this star bound is equivalent, up to the
printed `T³χ⁴`/`T⁴χ³` diagrams and explicit constants, to the `q = 0`, `p = 3` instance of
Lemma I.4.17.

## What this file proves

`HasPinnedStar M C₃ C₄ C₅` is that `q = 0`, `p = 3` instance written with the source's own
matrix powers `T^ℓ = I418C.polyK (M.cutTwoPoint r) ℓ 0 y`, degree-three part included.

* `hasCovBound_of_hasPinnedStar`: the pinned instance, together with the matrix-power comparison
  `T³(0,y) ≤ c₃T(0,y)` and `T⁴(0,y) ≤ c₄T(0,y)`, implies
  `HasCovBound M (C₃c₃ + C₄c₄ + C₅)`.
  This is the direction the campaign needs: a proof of the printed lemma at `q = 0` supplies the
  repaired covariance target.  The comparison is *not* automatic: `T^ℓ(0,y) ≥ T(0,y)` because
  `T(y,y) = 1`, so the printed `T^ℓ` weights are never smaller than the campaign's `T` weight;
  forcing `T^ℓ ≤ cT` is the extra geometric input in this direction, and it is the exact reason
  the campaign's `T`-weighted form is *stronger* than the printed `T^ℓ`-weighted conclusion.
* `hasPinnedStar_of_hasCovBound`: conversely `HasCovBound M C₅` gives the pinned instance with
  constants `(1, 2, C₅)` and *no* comparison hypothesis, using the proved `(2,1)` product gap and
  the exact identity `star = gap + cov`.  So `HasCovBound` is the stronger statement, and the
  residual of the off-diagonal case is a single source-shaped inequality.

Nothing here proves `HasPinnedStar` (that is the `q = 0` tree count the printed proof of
Lemma I.4.17 does not give: its union bound marks a vertex on a path from `y` to the mark set
`{y₁,…,y_q}`, which is empty at `q = 0`; see `QZeroStarAtlas4`).  Nothing here assumes a star,
product-gap or covariance hypothesis: `HasCovBound` is a conclusion of the first theorem and a
hypothesis of the second.
-/
module

public import PercLib.CriticalLRP.Correlation.I417.General.QZeroRepairAudit.ProductGap
public import PercLib.CriticalLRP.Correlation.I417.General.QZeroRepairAudit.Diagonal.Main
public import PercLib.CriticalLRP.Analysis.SecondMomentError.Bounds

/-! # The pinned `q = 0` star and the off-diagonal covariance target -/

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval Filter
open scoped ENNReal NNReal Topology BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

@[expose] public section

open PercLib.CriticalLRP.QZeroRepairAudit (starVert gapVert covVert jointVert prodVert)

attribute [local instance] Classical.propDecidable

variable (M : SourceModelData)

/-! ## §1 The pinned `q = 0`, `p = 3` statement -/

/-- **The `(p,q) = (0,3)` instance of Lemma I.4.17's printed conclusion.**

`E[1(y ∈ K_0)|K_0|³] ≤ C₃ T³(0,y) χ⁴ + C₄ T⁴(0,y) χ³ + C₅ T(0,y) χ⁵`

at every cutoff radius `r ≥ 1` and every vertex `y`.  The first two terms are the printed
`ℓ = 3, 4` diagrams of Lemma I.4.17 (with its unspecified universal integers absorbed into
`C₃, C₄`); the last term is the diagonal scale `E|K|³ ⪯ χ⁵`, which the printed range `ℓ ≥ 3`
does not reach at `q = 0` and which cannot be dropped: at `y = 0` the left-hand side is the third
cutoff moment, so the pure two-term form is false (`QZeroDiagonal.not_hasPerVertexTwoTermHgap`).
-/
def HasPinnedStar (C3 C4 C5 : ℝ) : Prop :=
  ∀ r : ℝ, 1 ≤ r → ∀ y : M.V,
    (starVert (M.cutProb r) (0 : M.V) y 3).toReal ≤
      C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * M.chiReal r ^ 4 +
        C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * M.chiReal r ^ 3 +
          C5 * M.cutTwoPoint r (0 : M.V) y * M.chiReal r ^ 5

/-! ## §2 The pinned instance forces the covariance target

The only extra input is the comparison of the matrix power `T³, T⁴` with `T` itself.  It is not
implied by `T ≤ 1`; here it is what converts the printed weights into the campaign's weight. -/

/-- **`HasPinnedStar` plus the matrix-power comparison implies `HasCovBound`.**

If `T³(0,y) ≤ c₃T(0,y)` and `T⁴(0,y) ≤ c₄T(0,y)` at every radius and vertex, then the
pinned `q = 0`, `p = 3` instance of Lemma I.4.17 gives the off-diagonal covariance bound
with constant `C₃c₃ + C₄c₄ + C₅`.  The diagram terms are absorbed with `χ⁴, χ³ ≤ χ⁵`,
as `χ ≥ 1`. -/
theorem hasCovBound_of_hasPinnedStar {C3 C4 C5 c3 c4 : ℝ}
    (hC3 : 0 ≤ C3) (hC4 : 0 ≤ C4) (hP : M.HasPinnedStar C3 C4 C5)
    (h3 : ∀ r : ℝ, 1 ≤ r → ∀ y : M.V,
      I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y ≤ c3 * M.cutTwoPoint r (0 : M.V) y)
    (h4 : ∀ r : ℝ, 1 ≤ r → ∀ y : M.V,
      I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y ≤ c4 * M.cutTwoPoint r (0 : M.V) y)
    (hc3 : 0 ≤ c3) (hc4 : 0 ≤ c4) (hχ : ∀ r : ℝ, 1 ≤ r → M.cutMoment 1 r ≠ ⊤) :
    QZeroRepairAudit.SourceModelData.HasCovBound M (C3 * c3 + C4 * c4 + C5) := by
  refine hasCovBound_of_starWeighted (M := M) (C5 := C3 * c3 + C4 * c4 + C5)
    (fun r hr y => ?_) hχ
  have hχ1 : (1 : ℝ) ≤ M.chiReal r := by
    rw [chiReal_eq_cutMoment_toReal]
    exact one_le_cutMoment_one_toReal M r (hχ r hr)
  have hT0 : (0 : ℝ) ≤ M.cutTwoPoint r (0 : M.V) y := M.cutTwoPoint_nonneg r _ _
  have hp3 : (0 : ℝ) ≤ I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y :=
    I418C.polyK_nonneg _ (fun a b => M.cutTwoPoint_nonneg r a b) 3 (0 : M.V) y
  have hp4 : (0 : ℝ) ≤ I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y :=
    I418C.polyK_nonneg _ (fun a b => M.cutTwoPoint_nonneg r a b) 4 (0 : M.V) y
  have hpow : ∀ n : ℕ, M.chiReal r ^ n ≤ M.chiReal r ^ (n + 1) := by
    intro n
    have h0 : (0 : ℝ) ≤ M.chiReal r ^ n := pow_nonneg (le_trans zero_le_one hχ1) n
    rw [pow_succ]
    calc M.chiReal r ^ n = M.chiReal r ^ n * 1 := by ring
      _ ≤ M.chiReal r ^ n * M.chiReal r := by gcongr
  have hχ4 : M.chiReal r ^ 4 ≤ M.chiReal r ^ 5 := by
    have := hpow 4
    simpa using this
  have hχ3 : M.chiReal r ^ 3 ≤ M.chiReal r ^ 5 := by
    have h34 : M.chiReal r ^ 3 ≤ M.chiReal r ^ 4 := by
      have := hpow 3
      simpa using this
    calc M.chiReal r ^ 3 ≤ M.chiReal r ^ 4 := h34
      _ ≤ M.chiReal r ^ 5 := hχ4
  have hχ4' : (0 : ℝ) ≤ M.chiReal r ^ 4 := pow_nonneg (le_trans zero_le_one hχ1) 4
  have hχ3' : (0 : ℝ) ≤ M.chiReal r ^ 3 := pow_nonneg (le_trans zero_le_one hχ1) 3
  have key : (starVert (M.cutProb r) (0 : M.V) y 3).toReal
      ≤ (C3 * c3 + C4 * c4 + C5) * M.cutTwoPoint r (0 : M.V) y * M.chiReal r ^ 5 := by
    refine le_trans (hP r hr y) ?_
    have h1 : C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * M.chiReal r ^ 4
        ≤ C3 * c3 * (M.cutTwoPoint r (0 : M.V) y * M.chiReal r ^ 5) := by
      have hle : I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * M.chiReal r ^ 4
          ≤ (c3 * M.cutTwoPoint r (0 : M.V) y) * M.chiReal r ^ 5 := by
        refine mul_le_mul (h3 r hr y) hχ4 hχ4' ?_
        exact mul_nonneg hc3 hT0
      calc C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * M.chiReal r ^ 4
          = C3 * (I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * M.chiReal r ^ 4) := by ring
        _ ≤ C3 * ((c3 * M.cutTwoPoint r (0 : M.V) y) * M.chiReal r ^ 5) :=
            mul_le_mul_of_nonneg_left hle hC3
        _ = C3 * c3 * (M.cutTwoPoint r (0 : M.V) y * M.chiReal r ^ 5) := by ring
    have h2 : C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * M.chiReal r ^ 3
        ≤ C4 * c4 * (M.cutTwoPoint r (0 : M.V) y * M.chiReal r ^ 5) := by
      have hle : I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * M.chiReal r ^ 3
          ≤ (c4 * M.cutTwoPoint r (0 : M.V) y) * M.chiReal r ^ 5 := by
        refine mul_le_mul (h4 r hr y) hχ3 hχ3' ?_
        exact mul_nonneg hc4 hT0
      calc C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * M.chiReal r ^ 3
          = C4 * (I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * M.chiReal r ^ 3) := by ring
        _ ≤ C4 * ((c4 * M.cutTwoPoint r (0 : M.V) y) * M.chiReal r ^ 5) :=
            mul_le_mul_of_nonneg_left hle hC4
        _ = C4 * c4 * (M.cutTwoPoint r (0 : M.V) y * M.chiReal r ^ 5) := by ring
    have h3' : C5 * M.cutTwoPoint r (0 : M.V) y * M.chiReal r ^ 5
        = C5 * (M.cutTwoPoint r (0 : M.V) y * M.chiReal r ^ 5) := by ring
    calc C3 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * M.chiReal r ^ 4 +
          C4 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * M.chiReal r ^ 3 +
          C5 * M.cutTwoPoint r (0 : M.V) y * M.chiReal r ^ 5
        ≤ C3 * c3 * (M.cutTwoPoint r (0 : M.V) y * M.chiReal r ^ 5) +
            C4 * c4 * (M.cutTwoPoint r (0 : M.V) y * M.chiReal r ^ 5) +
            C5 * (M.cutTwoPoint r (0 : M.V) y * M.chiReal r ^ 5) := by
          rw [h3']
          linarith [h1, h2]
      _ = (C3 * c3 + C4 * c4 + C5) * M.cutTwoPoint r (0 : M.V) y * M.chiReal r ^ 5 := by ring
  exact key

/-! ## §3 Conversely the covariance target gives the pinned instance

No comparison hypothesis is needed in this direction: the proved `(2,1)` product gap supplies the
two printed diagram terms, and `star = gap + cov` splits the star exactly. -/

/-- **`HasCovBound` implies the pinned `q = 0`, `p = 3` statement with constants `(1, 2, C₅)`.**

The two diagram terms are the *proved* `(2,1)` product gap (`T³χ⁴ + 2T⁴χ³`,
`hasProductGap_one_two`), and the discrepancy between the star and the gap is exactly the
covariance (`starVert_toReal_eq_gapVert_add_covVert`). -/
theorem hasPinnedStar_of_hasCovBound {C5 : ℝ} (_hC5 : 0 ≤ C5)
    (hcov : QZeroRepairAudit.SourceModelData.HasCovBound M C5)
    (hχ : ∀ r : ℝ, 1 ≤ r → M.cutMassAt r 0 ≠ ⊤)
    (h2 : ∀ r : ℝ, 1 ≤ r → M.cutMoment 2 r ≠ ⊤)
    (h3 : ∀ r : ℝ, 1 ≤ r → M.cutMoment 3 r ≠ ⊤) :
    M.HasPinnedStar 1 2 C5 := by
  classical
  let := Encodable.ofCountable (Sym2 M.V)
  have hgap : QZeroRepairAudit.SourceModelData.HasProductGap M 1 2 := hasProductGap_one_two M hχ
  intro r hr y
  have h1 : M.cutMoment 1 r ≠ ⊤ := by
    rw [← M.cutMassAt_zero_eq_cutMoment r]; exact hχ r hr
  have hP : prodVert (M.cutProb r) (0 : M.V) y 1 2 ≠ ⊤ := by
    rw [prodVert, M.powMomentAt_cutProb_eq_cutMoment,
      M.powMomentAt_cutProb_eq_cutMoment]
    exact ENNReal.mul_ne_top h1 (h2 r hr)
  have hJ : jointVert (M.cutProb r) (0 : M.V) y 1 2 ≠ ⊤ := by
    rw [QZeroRepairAudit.jointVert_eq_excl_add_star]
    refine ENNReal.add_ne_top.2 ⟨?_, ?_⟩
    · exact ne_top_of_le_ne_top hP
        (QZeroRepairAudit.exclVert_le_prodVert (M.cutProb r) (E1Sign.cutProb_lt_one M r)
          (Percolation.edgeExhaustion (E := Sym2 M.V)) Percolation.edgeExhaustion_mono
          Percolation.edgeExhaustion_cover (0 : M.V) y 1 2)
    · rw [show (1 : ℕ) + 2 = 3 from rfl]
      exact ne_top_of_le_ne_top (h3 r hr) (starVert_le_cutMoment_three M r y)
  have hsplit := QZeroRepairAudit.starVert_toReal_eq_gapVert_add_covVert (M.cutProb r)
    (E1Sign.cutProb_lt_one M r) (Percolation.edgeExhaustion (E := Sym2 M.V))
    Percolation.edgeExhaustion_mono Percolation.edgeExhaustion_cover (0 : M.V) y 1 2 hP hJ
  have hgapb := hgap r hr y
  have hcovb := hcov r hr y
  have hstar : (starVert (M.cutProb r) (0 : M.V) y 3).toReal
      = (gapVert (M.cutProb r) (0 : M.V) y 1 2).toReal
        + (covVert (M.cutProb r) (0 : M.V) y 1 2).toReal := by
    rw [show (1 : ℕ) + 2 = 3 from rfl] at hsplit
    exact hsplit
  have hgap'' : (gapVert (M.cutProb r) (0 : M.V) y 1 2).toReal
      ≤ I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * M.chiReal r ^ 4 +
        2 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * M.chiReal r ^ 3 := by
    have hp3 : I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * M.chiReal r ^ 4
        = 1 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * M.chiReal r ^ 4 := by ring
    simpa [hp3, mul_assoc] using hgapb
  rw [hstar]
  calc (gapVert (M.cutProb r) (0 : M.V) y 1 2).toReal
        + (covVert (M.cutProb r) (0 : M.V) y 1 2).toReal
      ≤ (I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * M.chiReal r ^ 4 +
          2 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * M.chiReal r ^ 3) +
          C5 * M.cutTwoPoint r (0 : M.V) y * M.chiReal r ^ 5 := by
        linarith [hgap'', hcovb]
    _ = 1 * I418C.polyK (M.cutTwoPoint r) 3 (0 : M.V) y * M.chiReal r ^ 4 +
          2 * I418C.polyK (M.cutTwoPoint r) 4 (0 : M.V) y * M.chiReal r ^ 3 +
            C5 * M.cutTwoPoint r (0 : M.V) y * M.chiReal r ^ 5 := by ring

end

end SourceModelData
end Orchestration
end PercLib.CriticalLRP

/-! ## Axiom audit -/

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.hasCovBound_of_hasPinnedStar
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.hasPinnedStar_of_hasCovBound
