/-
Ultramath swarm `smwznoz6j`, member `m3`, direction `d9` (campaign direction (J)).

Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwznoz6j`, member m3.
Latest independent rebuild at production HEAD `16d9f2aa1e83afeda3fc66117e38ed3352b2e567`; reviewed scratch source `.scratch/review-smwznoz6j/m3/Main.lean`.

# The covariance target at the cutoff law: uniform weight and the sharp diagonal constant

`QZeroRepairAudit.SourceModelData.HasCovBound M C5` (production, `QZeroRepairAudit/Defs.lean`)
is the last input of the additive repair of the refuted `q = 0`, `p = 3` star:

  `Cov(|K_0|, |K_y|²) ≤ C₅ · T_{β_c,r}(0,y) · χ^5`   for every `r ≥ 1` and every `y`.

This file proves three things about it, all at the model's own range-cutoff law
`M.cutLaw r = edgeMeasure (M.cutProb r)` and with no extra hypothesis beyond finiteness of the
first cutoff moment where a real number is produced:

1. `covVert_le_cutMoment_three` — the covariance is dominated by the third cutoff moment,
   `Cov(|K_0|,|K_y|²) ≤ E_{β_c,r}|K|³`, **for every `y`**.  The proof uses only the exact
   per-vertex partition `E[|K_0||K_y|²] = E[1(0↮y)|K_0||K_y|²] + E[1(0↔y)|K_0|³]`
   (`jointVert_eq_excl_add_star`) and the BK half `E[1(0↮y)|K_0||K_y|²] ≤ E|K_0| E|K_y|²`
   (`exclVert_le_prodVert`); the star half is bounded pointwise by `|K_0|³`.

2. `covVert_toReal_le_three_mul_chi_pow_five` — consequently
   `Cov(|K_0|,|K_y|²) ≤ 3 χ^5` uniformly in `y`, with `3 = (2·3 − 3)!!` coming from the
   tree-graph inequality (I.2.3) at `p = 3` (`Defs.lean`,
   `cutMoment_three_le_three_mul_pow_five`).  Since `0 ≤ T_{β_c,r}(0,y) ≤ 1`, this is the
   **weaker-weight** form of `HasCovBound`: weight `1` in place of the two-point weight `T`.

3. `hasCovBound_of_starWeighted` — a sufficient condition: `HasCovBound` follows from the
   `T`-weighted *star-only* bound `E[1(0 ↔ y)|K_0|³] ≤ C₅ T(0,y) χ^5`.  Since `starVert ≥ covVert`,
   this is not a weakening of `HasCovBound`; what it shows is that the covariance target needs no
   `T³χ⁴`/`T⁴χ³` diagram terms at all, only the spatial decay of the star moment against `T`.

4. `covVert_diag_toReal_eq` — at the diagonal the truncated subtraction is exact:
   `Cov(|K_0|,|K_0|²) = E_{β_c,r}|K|³ − χ · E_{β_c,r}|K|²`, the quantity that
   `QZeroDiagInputs.third_lower` bounds below by `c χ^5`.

5. `connCubeVertexMass_le_three_mul_chi_pow_five` — the same uniform bound in the campaign's own
   vocabulary for the `q = 0`, `p = 3` star: `E[1(y ∈ K_0)|K_0|³] ≤ 3 χ^5`, for every `y`.

At the diagonal `T(0,0) = 1` (`cutTwoPoint_self_eq_one`), so item 2 *is* the `y = 0` instance of
`HasCovBound` for every `C₅ ≥ 3` (`hasCovBound_diag`).  Sharpness is production's
`QZeroRepairAudit.SourceModelData.additive_const_ge`: together with the proved product gap,
`HasCovBound M C₅` forces `c ≤ C₅` where `c` is the third-moment coefficient of
Proposition I.4.20 (`le_of_hasCovBound`).  Hence the diagonal instance of `HasCovBound` is
attained at, and cannot go below, the source's constant `3`.

Nothing here proves `HasCovBound` for `y ≠ 0`: the tree-graph bound is `y`-uniform, so it cannot
produce the factor `T(0,y)` that vanishes as `y → ∞`.  That is the exact residual.
-/
module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase3.TriangleFromHD.Main
public import PercLib.CriticalLRP.Correlation.I417.General.QZeroRepairAudit.ProductGap
public import PercLib.CriticalLRP.Correlation.I417.General.QZeroDiagonal.Defs
public import PercLib.CriticalLRP.Analysis.Cutoff.Translation
public import PercLib.CriticalLRP.Analysis.Cutoff.Basic
public import PercLib.CriticalLRP.Analysis.Cutoff.Defect.Defs
public import PercLib.CriticalLRP.Correlation.I417.General.QZeroRepairAudit.Diagonal.Defs

/-! # Uniform covariance bound and sharp diagonal constant -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.hashCommand false
set_option linter.style.longLine false

@[expose] public section

noncomputable section

open MeasureTheory Measure ProbabilityTheory unitInterval Filter
open scoped ENNReal NNReal Topology BigOperators

namespace PercLib.CriticalLRP
namespace Orchestration
namespace SourceModelData

attribute [local instance] Classical.propDecidable

variable (M : SourceModelData)

/-! ## §1 `χ = E_{β_c,r}|K|` as a real number -/

/-- `chiReal r` is the real value of the first cutoff moment. -/
theorem chiReal_eq_cutMoment_toReal (r : ℝ) :
    M.chiReal r = (M.cutMoment 1 r).toReal := by
  rw [PercLib.CriticalLRP.Orchestration.SourceModelData.chiReal,
    M.cutMassAt_zero_eq_cutMoment]

/-! ## §2 The star half is dominated by the third cutoff moment -/

/-- **`E[1(y ∈ K_0) |K_0|³] ≤ E|K_0|³`** at the model's cutoff law: the star term of the
per-vertex partition is dominated by the third cutoff moment, pointwise and for every `y`. -/
theorem starVert_le_cutMoment_three (r : ℝ) (y : M.V) :
    QZeroRepairAudit.starVert (M.cutProb r) (0 : M.V) y 3 ≤ M.cutMoment 3 r := by
  rw [QZeroRepairAudit.starVert]
  rw [← M.lintegral_cardFun_pow_eq_cutMoment r 3]
  refine lintegral_mono fun ω => ?_
  have hind : (cluster ω (0 : M.V)).indicator (fun _ => (1 : ℝ≥0∞)) y ≤ 1 := by
    by_cases hy : y ∈ cluster ω (0 : M.V)
    · simp only [Set.indicator_of_mem hy, le_refl]
    · simp only [Set.indicator_of_notMem hy, zero_le]
  calc clusterVol ω (0 : M.V) ^ 3 * (cluster ω (0 : M.V)).indicator (fun _ => (1 : ℝ≥0∞)) y
      ≤ clusterVol ω (0 : M.V) ^ 3 * 1 := by gcongr
    _ = clusterVol ω (0 : M.V) ^ 3 := mul_one _
    _ = Percolation.cardFun (cluster ω (0 : M.V)) ^ 3 := by
        rw [Percolation.cardFun_eq_encard, clusterVol_eq_encard]

/-! ## §3 The covariance is dominated by the star -/

/-- **`Cov(|K_0|,|K_y|²) ≤ E[1(y ∈ K_0)|K_0|³]`.**

`covVert = jointVert ⊖ prodVert`, `jointVert = exclVert + starVert`
(`jointVert_eq_excl_add_star`) and `exclVert ≤ prodVert` (the BK half), so the covariance is at
most the star moment.  This is the exact point where the `y`-decay of `HasCovBound` lives. -/
theorem covVert_le_starVert (r : ℝ) (y : M.V) :
    QZeroRepairAudit.covVert (M.cutProb r) (0 : M.V) y 1 2
      ≤ QZeroRepairAudit.starVert (M.cutProb r) (0 : M.V) y 3 := by
  classical
  let := Encodable.ofCountable (Sym2 M.V)
  have hid := QZeroRepairAudit.jointVert_eq_excl_add_star (M.cutProb r) (0 : M.V) y 1 2
  rw [show (1 : ℕ) + 2 = 3 from rfl] at hid
  have hex := QZeroRepairAudit.exclVert_le_prodVert (M.cutProb r)
    (E1Sign.cutProb_lt_one M r) (Percolation.edgeExhaustion (E := Sym2 M.V))
    Percolation.edgeExhaustion_mono Percolation.edgeExhaustion_cover (0 : M.V) y 1 2
  rw [QZeroRepairAudit.covVert, hid, tsub_le_iff_left]
  exact add_le_add hex le_rfl

/-! ## §4 The uniform covariance bound -/

/-- **`Cov(|K_0|,|K_y|²) ≤ E|K_0|³` at the cutoff law, uniformly in `y`.** -/
theorem covVert_le_cutMoment_three (r : ℝ) (y : M.V) :
    QZeroRepairAudit.covVert (M.cutProb r) (0 : M.V) y 1 2 ≤ M.cutMoment 3 r :=
  (M.covVert_le_starVert r y).trans (M.starVert_le_cutMoment_three r y)

/-- **`Cov(|K_0|,|K_y|²) ≤ 3 (E_{β_c,r}|K|)^5`, uniformly in `y`.**

This is the weight-`1` form of `HasCovBound`: the tree-graph constant `3 = (2·3 − 3)!!` and the
`(E|K|)^5` power of source display (I.2.3) at `p = 3`, with no two-point weight. -/
theorem covVert_le_three_mul_pow_five (r : ℝ) (y : M.V) :
    QZeroRepairAudit.covVert (M.cutProb r) (0 : M.V) y 1 2 ≤ 3 * M.cutMoment 1 r ^ 5 :=
  (M.covVert_le_cutMoment_three r y).trans (M.cutMoment_three_le_three_mul_pow_five r)

/-- The real-number form of the uniform covariance bound. -/
theorem covVert_toReal_le_three_mul_chi_pow_five (r : ℝ) (y : M.V)
    (h1 : M.cutMoment 1 r ≠ ⊤) :
    (QZeroRepairAudit.covVert (M.cutProb r) (0 : M.V) y 1 2).toReal
      ≤ 3 * M.chiReal r ^ 5 := by
  have hfin : 3 * M.cutMoment 1 r ^ 5 ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top h1)
  refine (ENNReal.toReal_mono hfin (M.covVert_le_three_mul_pow_five r y)).trans (le_of_eq ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat, M.chiReal_eq_cutMoment_toReal]

/-- The star moment alone obeys the same uniform bound. -/
theorem starVert_toReal_le_three_mul_chi_pow_five (r : ℝ) (y : M.V)
    (h1 : M.cutMoment 1 r ≠ ⊤) :
    (QZeroRepairAudit.starVert (M.cutProb r) (0 : M.V) y 3).toReal
      ≤ 3 * M.chiReal r ^ 5 := by
  have hfin : 3 * M.cutMoment 1 r ^ 5 ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top h1)
  refine (ENNReal.toReal_mono hfin
    ((M.starVert_le_cutMoment_three r y).trans (M.cutMoment_three_le_three_mul_pow_five r))).trans
    (le_of_eq ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat, M.chiReal_eq_cutMoment_toReal]

/-- **The `q = 0`, `p = 3` star moment is `O(χ^5)`, uniformly in `y`**, in the campaign's own
vocabulary: `E[1(y ∈ K_0)|K_0|³] ≤ 3 (E_{β_c,r}|K|)^5`.

This holds with no triangle condition, no product-gap input, no star hypothesis, and no
two-point weight: it is the tree-graph bound read at the model's cutoff law.  What the source's
additive star repair still needs is the two-term diagram shape and the weight `T(0,y)`. -/
theorem connCubeVertexMass_le_three_mul_chi_pow_five (r : ℝ) (y : M.V)
    (h1 : M.cutMoment 1 r ≠ ⊤) :
    (M.connCubeVertexMass r y).toReal ≤ 3 * M.chiReal r ^ 5 := by
  rw [← QZeroRepairAudit.SourceModelData.starVert_cutProb_eq_connCubeVertexMass M r y]
  exact M.starVert_toReal_le_three_mul_chi_pow_five r y h1

/-! ## §4b The diagonal covariance, exactly -/

/-- **`Cov(|K_0|,|K_0|²) = E_{β_c,r}|K|³ − χ · E_{β_c,r}|K|²`.**

The truncated `ℝ≥0∞` subtraction in `covVert` is exact at the diagonal because Harris/FKG gives
`E|K_0| E|K_0|² ≤ E|K_0|³` (`prodVert_le_jointVert`).  This is the quantity that
`QZeroDiagInputs.third_lower` bounds below by `c χ^5`, which is why the diagonal forces
`C₅ ≥ c`. -/
theorem covVert_diag_toReal_eq (r : ℝ) (h1 : M.cutMoment 1 r ≠ ⊤) :
    (QZeroRepairAudit.covVert (M.cutProb r) (0 : M.V) (0 : M.V) 1 2).toReal
      = (M.cutMoment 3 r).toReal - M.chiReal r * (M.cutMoment 2 r).toReal := by
  classical
  let := Encodable.ofCountable (Sym2 M.V)
  have hjoint : QZeroRepairAudit.jointVert (M.cutProb r) (0 : M.V) (0 : M.V) 1 2
      = M.cutMoment 3 r := by
    rw [QZeroRepairAudit.jointVert, cutMoment]
    refine lintegral_congr fun ω => ?_
    rw [pow_one, show (3 : ℕ) = 1 + 2 from rfl, pow_add, pow_one]
  have hprod : QZeroRepairAudit.prodVert (M.cutProb r) (0 : M.V) (0 : M.V) 1 2
      = M.cutMoment 1 r * M.cutMoment 2 r := by
    rw [QZeroRepairAudit.prodVert, M.powMomentAt_cutProb_eq_cutMoment,
      M.powMomentAt_cutProb_eq_cutMoment]
  have hle : QZeroRepairAudit.prodVert (M.cutProb r) (0 : M.V) (0 : M.V) 1 2
      ≤ QZeroRepairAudit.jointVert (M.cutProb r) (0 : M.V) (0 : M.V) 1 2 :=
    QZeroRepairAudit.prodVert_le_jointVert (M.cutProb r) (E1Sign.cutProb_lt_one M r)
      (Percolation.edgeExhaustion (E := Sym2 M.V)) Percolation.edgeExhaustion_mono
      Percolation.edgeExhaustion_cover (0 : M.V) (0 : M.V) 1 2
  have h3 : M.cutMoment 3 r ≠ ⊤ :=
    ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top h1))
      (M.cutMoment_three_le_three_mul_pow_five r)
  have hle' : M.cutMoment 1 r * M.cutMoment 2 r ≤ M.cutMoment 3 r := by
    rw [← hprod, ← hjoint]
    exact hle
  rw [QZeroRepairAudit.covVert, hjoint, hprod, ENNReal.toReal_sub_of_le hle' h3,
    ENNReal.toReal_mul, M.chiReal_eq_cutMoment_toReal]

/-! ## §4c The star target in weight-`1` form, at the printed constants -/

/-- **The `q = 0`, `p = 3` star target in weight-`1` form at `(C₃,C₄,C₅) = (1,2,3)`.**

Assembled from the proved `(2,1)` product gap (`hasProductGap_one_two`, whose diagram constants
are the source's `1` and `2`), the uniform covariance bound of §4 (constant `3 = (2·3−3)!!`) and
the exact per-vertex split `star = gap + cov`
(`connCubeVertexMass_toReal_eq_gapVert_add_covVert`).

Hypotheses: finiteness of the first three cutoff moments (`hχ`, `h2`, `h3`).  No triangle
condition, no moment gap, no two-point decay, no star hypothesis. -/
theorem hasUniformWeightStar_one_two_three
    (hχ : ∀ r : ℝ, 1 ≤ r → M.cutMassAt r 0 ≠ ⊤)
    (h2 : ∀ r : ℝ, 1 ≤ r → M.cutMoment 2 r ≠ ⊤)
    (h3 : ∀ r : ℝ, 1 ≤ r → M.cutMoment 3 r ≠ ⊤) :
    M.HasUniformWeightStar 1 2 3 := by
  intro r hr y
  have h1 : M.cutMoment 1 r ≠ ⊤ := by
    rw [← M.cutMassAt_zero_eq_cutMoment]
    exact hχ r hr
  rw [QZeroRepairAudit.SourceModelData.connCubeVertexMass_toReal_eq_gapVert_add_covVert M r y
    (h2 r hr) (h3 r hr)]
  have hg := hasProductGap_one_two M hχ r hr y
  have hc := M.covVert_toReal_le_three_mul_chi_pow_five r y h1
  linarith

/-! ## §5 The diagonal instance of `HasCovBound`, at every `C₅ ≥ 3` -/

/-- **The `y = 0` instance of `HasCovBound` holds at every `C₅ ≥ 3`, with no hypothesis.**

At the diagonal `T_{β_c,r}(0,0) = 1`, so the weight-`1` bound of §4 is exactly the covariance
target.  If `χ_r = ⊤` the product factor `E|K_0| · E|K_0|²` is itself `⊤`, so the truncated
covariance is `0` while `χ_r` read as a real number is `0`; otherwise §4 applies.

With `le_of_hasCovBound` below, `3` is both sufficient and (in the mean-field regime where the
third moment grows like `χ^5`) necessary. -/
theorem hasCovBound_diag {C5 : ℝ} (hC5 : 3 ≤ C5) (r : ℝ) :
    (QZeroRepairAudit.covVert (M.cutProb r) (0 : M.V) (0 : M.V) 1 2).toReal
      ≤ C5 * M.cutTwoPoint r (0 : M.V) (0 : M.V) * M.chiReal r ^ 5 := by
  rcases eq_or_ne (M.cutMoment 1 r) ⊤ with h1 | h1
  · -- `χ = ⊤`: the product factor is `⊤`, so the truncated covariance is `0` and `toReal χ = 0`.
    have h2ne : M.cutMoment 2 r ≠ 0 := by
      have hone : (1 : ℝ≥0∞) = ∫⁻ (_ω : Config M.V), (1 : ℝ≥0∞) ∂(M.cutLaw r) := by simp
      have hle : (1 : ℝ≥0∞) ≤ M.cutMoment 2 r := by
        rw [cutMoment, hone]
        refine lintegral_mono fun ω => ?_
        exact le_trans (SourceModelData.one_le_clusterVol ω (0 : M.V))
          (le_self_pow (SourceModelData.one_le_clusterVol ω (0 : M.V)) (by norm_num : 2 ≠ 0))
      exact ne_of_gt (lt_of_lt_of_le one_pos hle)
    have hprod : QZeroRepairAudit.prodVert (M.cutProb r) (0 : M.V) (0 : M.V) 1 2 = ⊤ := by
      rw [QZeroRepairAudit.prodVert, M.powMomentAt_cutProb_eq_cutMoment,
        M.powMomentAt_cutProb_eq_cutMoment, h1]
      exact ENNReal.top_mul h2ne
    have hcov : QZeroRepairAudit.covVert (M.cutProb r) (0 : M.V) (0 : M.V) 1 2 = 0 := by
      rw [QZeroRepairAudit.covVert, hprod, ENNReal.sub_top]
    rw [hcov, M.chiReal_eq_cutMoment_toReal, h1]
    simp
  · have h := M.covVert_toReal_le_three_mul_chi_pow_five r 0 h1
    rw [M.cutTwoPoint_self_eq_one r (0 : M.V), mul_one]
    have hχ : (0 : ℝ) ≤ M.chiReal r := ENNReal.toReal_nonneg
    have hχ5 : (0 : ℝ) ≤ M.chiReal r ^ 5 := pow_nonneg hχ 5
    nlinarith [h, hχ5, hC5]

/-! ## §6 The exact reduction: `T`-weighted star bound implies `HasCovBound` -/

/-- **`HasCovBound` follows from the `T`-weighted star-only bound.**

Since `Cov(|K_0|,|K_y|²) ≤ E[1(y ∈ K_0)|K_0|³]` (`covVert_le_starVert`), the covariance target
is implied by the `T`-weighted star bound.  This is a sufficient condition rather than a
weakening of `HasCovBound` (`starVert ≥ covVert`), but it isolates what the covariance target
still needs: the spatial decay of `E[1(0 ↔ y)|K_0|³]` against `T_{β_c,r}(0,y)`.  This route needs
strictly less than `HasAdditiveStar`: no product-gap term and no `T³χ⁴`, `T⁴χ³` summands. -/
theorem hasCovBound_of_starWeighted {C5 : ℝ}
    (hstar : ∀ r : ℝ, 1 ≤ r → ∀ y : M.V,
      (QZeroRepairAudit.starVert (M.cutProb r) (0 : M.V) y 3).toReal
        ≤ C5 * M.cutTwoPoint r (0 : M.V) y * M.chiReal r ^ 5)
    (hχ : ∀ r : ℝ, 1 ≤ r → M.cutMoment 1 r ≠ ⊤) :
    QZeroRepairAudit.SourceModelData.HasCovBound M C5 := by
  intro r hr y
  have h3top : M.cutMoment 3 r ≠ ⊤ :=
    ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top (hχ r hr)))
      (M.cutMoment_three_le_three_mul_pow_five r)
  have hstarTop : QZeroRepairAudit.starVert (M.cutProb r) (0 : M.V) y 3 ≠ ⊤ :=
    ne_top_of_le_ne_top h3top (M.starVert_le_cutMoment_three r y)
  exact (ENNReal.toReal_mono hstarTop (M.covVert_le_starVert r y)).trans (hstar r hr y)

/-! ## §7 Sharpness of the diagonal constant -/

/-- **`HasCovBound` cannot use a constant below the third-moment coefficient.**

Given the source's Case-3 diagonal inputs `QZeroDiagInputs M c R` and the proved product gap,
`HasCovBound M C₅` yields the additive star repair (`hasAdditiveStar_of_covBound`), so
production's `additive_const_ge` forces `c ≤ C₅`.  With Proposition I.4.20 at `p = 3`,
`c = (2·3 − 3)!! = 3`: the constant of §5 is optimal. -/
theorem le_of_hasCovBound {c R C5 : ℝ} (hQI : QZeroDiagInputs M c R)
    (hχ : ∀ r : ℝ, 1 ≤ r → M.cutMassAt r 0 ≠ ⊤)
    (h2 : ∀ r : ℝ, 1 ≤ r → M.cutMoment 2 r ≠ ⊤)
    (h3 : ∀ r : ℝ, 1 ≤ r → M.cutMoment 3 r ≠ ⊤)
    (hcov : QZeroRepairAudit.SourceModelData.HasCovBound M C5) : c ≤ C5 :=
  PercLib.CriticalLRP.QZeroRepairAudit.SourceModelData.additive_const_ge M hQI
    (by norm_num) (by norm_num) (M.hasAdditiveStar_of_covBound hχ h2 h3 hcov)

end SourceModelData
end Orchestration
end PercLib.CriticalLRP

end

/-! ## Axiom audit -/

#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.chiReal_eq_cutMoment_toReal
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.starVert_le_cutMoment_three
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.covVert_le_starVert
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.covVert_le_cutMoment_three
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.covVert_le_three_mul_pow_five
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.covVert_toReal_le_three_mul_chi_pow_five
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.starVert_toReal_le_three_mul_chi_pow_five
#print axioms
  PercLib.CriticalLRP.Orchestration.SourceModelData.connCubeVertexMass_le_three_mul_chi_pow_five
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.covVert_diag_toReal_eq
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.hasUniformWeightStar_one_two_three
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.hasCovBound_diag
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.hasCovBound_of_starWeighted
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.le_of_hasCovBound
