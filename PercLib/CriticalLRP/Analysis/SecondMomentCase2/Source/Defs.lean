/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Accepted and independently rebuilt from Ultramath `smwznoz6j`, member m2.
Latest independent rebuild at production HEAD `bd25afb1130f7fe93446b447f9a68a4d3aba08cc`;
reviewed scratch source `.scratch/review-smwznoz6j/m2/Case2.lean`.

# Case 2 of Proposition I.4.15 (`d = 3α` together with (Hydro))

Hutchcroft, *Critical long-range percolation I*, arXiv:2508.18807v1, proof of
Proposition I.4.15, Case 2 (paper p. 44, displays (I.4.16)–(I.4.18)):

```
  E_{β_c,r}[|K|³ |K ∩ B_r|] ≤ √(E_{β_c,r}|K|⁶) √(E_{β_c,r}|K ∩ B_r|²)
                            ⪯ (E|K|²)(E|K|)^{5/2} · (M_r E|K|)^{1/2}      (I.4.17)
      so that   E_{2,r} ⪯ (E|K|)² M_r^{1/2} / |B_r|
      and hence E_{2,r} = o(r^{2α-d+(d+α)/4}) = o(1)  when d = 3α.        (I.4.18)
```

The paper's two moment inputs are

* **Lemma I.4.16 at `p = 6`, `k = 2`**: `E|K|⁶ ≤ 9!! (E|K|²)² (E|K|)⁵`, and
* **universal tightness (Corollary I.2.5)**: `E_r|K ∩ B_r|² ⪯ M_r E_r|K|`
  (the paper prints the derived shape `r^α M_r`; `E_r|K| ⪯ r^α` converts one
  into the other, and both give the same exponent).

Everything else — the Cauchy–Schwarz step (I.4.17), the exact cancellation of
`E|K|²`, the rate `(9α - 3d)/4` and the limit `E_{2,r} → 0` at `d = 3α` — is proved
here from those two inputs, the first-moment asymptotic and (Hydro).  The second
input is *discharged* from the landed Corollary I.2.5 at the cutoff law
(`interSecond_le_edian`), so in the capstone
`p2ExclError_tendsto_zero_of_caseTwo'` the only remaining input is Lemma I.4.16 at
`p = 6`, `k = 2`, carried as the named predicate `SixthMomentMixed` — the
generalized tree-graph inequality, which production has only up to `p = 5`.
-/

module

public import PercLib.CriticalLRP.Analysis.SecondMomentCase1
public import PercLib.CriticalLRP.VolumeMoments.HigherMoments.I420Case2.Main
public import PercLib.CriticalLRP.Analysis.TriangleAverage
public import PercLib.CriticalLRP.Tightness.Universal

/-! ## Case-2 error estimate and its named mixed-moment input

The Cauchy–Schwarz and tightness arguments here preserve the actual cutoff
moments and their constants; only Lemma I.4.16 at p=6,k=2 remains a premise of
the final vanishing statement.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Topology

namespace PercLib.CriticalLRP
namespace CaseTwo

open Orchestration

/-! ## 1. The source numerator as `E_r[|K|³ |K ∩ B_r|]` -/

/-- **The `p = 2` numerator of (I.4.16) is the cutoff-law integral of `|K|³ |K ∩ B_r|`.**
`M.connCubeMass r` is defined on the mark space; on the cutoff law it is
`∫ |K|³ · #{y ∈ B_r : y ∈ K}`, and `#{y ∈ B_r : y ∈ K} = |K ∩ B_r|`. -/
theorem connCubeMass_eq_jointMoment_two (M : SourceModelData) (r : ℝ) :
    M.connCubeMass r = Analysis.I420Case2.jointMoment M 2 r := by
  rw [SourceModelData.connCubeMass_eq_lintegral M r]
  simp only [Analysis.I420Case2.jointMoment, Analysis.I420Case2.interVol]
  refine lintegral_congr fun ω => ?_
  congr 1
  rw [clusterVolIn_eq_tsum]
  rw [tsum_eq_sum (s := E1Sign.ballF M r) ?_]
  · refine Finset.sum_congr rfl fun y hy => ?_
    have hy' : y ∈ M.ball r := (E1Sign.mem_ballF M).mp hy
    by_cases hyK : y ∈ cluster ω (0 : M.V)
    · rw [Set.indicator_of_mem hyK (fun (_ : M.V) => (1 : ℝ≥0∞)),
          Set.indicator_of_mem (Set.mem_inter hyK hy') (fun (_ : M.V) => (1 : ℝ≥0∞))]
    · have h : y ∉ cluster ω (0 : M.V) ∩ M.ball r := fun hh => hyK hh.1
      rw [Set.indicator_of_notMem hyK (fun (_ : M.V) => (1 : ℝ≥0∞)),
        Set.indicator_of_notMem h (fun (_ : M.V) => (1 : ℝ≥0∞))]
  · intro y hy
    have hy' : y ∉ cluster ω (0 : M.V) ∩ M.ball r :=
      fun h => hy ((E1Sign.mem_ballF M).mpr h.2)
    exact Set.indicator_of_notMem hy' (fun (_ : M.V) => (1 : ℝ≥0∞))

/-- **Cauchy–Schwarz step (I.4.17)**, at `p = 2`:
`E_r[|K|³ |K ∩ B_r|] ≤ √(E_r|K|⁶) √(E_r|K ∩ B_r|²)`. -/
theorem connCubeMass_le_cs (M : SourceModelData) (r : ℝ) :
    M.connCubeMass r ≤ (M.cutMoment 6 r) ^ (1 / 2 : ℝ)
      * (Analysis.I420Case2.interSecond M r) ^ (1 / 2 : ℝ) := by
  rw [connCubeMass_eq_jointMoment_two M r]
  have h := Analysis.I420Case2.jointMoment_le_cs M 2 r
  simpa using h

/-! ## 2. The two source inputs, as named predicates -/

/-- **Lemma I.4.16 at `p = 6`, `k = 2`** (the moment input of (I.4.17)):
`E_{β_c,r}|K|⁶ ≤ 9!! (E_{β_c,r}|K|²)² (E_{β_c,r}|K|)⁵`, `9!! = 945`.

The constant is the paper's `(2p-3)!!` at `p = 6`.  This is the one combinatorial
statement of Case 2 that the repository does not yet have: the landed generalized
tree-graph inequalities stop at `p = 5` (`SixPoint.fifth_moment_all_k_le`,
`MixedK2.fifth_moment_all_k_le_of_hubBound`). -/
def SixthMomentMixed (M : SourceModelData) : Prop :=
  ∀ r : ℝ, 0 ≤ r →
    M.cutMoment 6 r ≤ (945 : ℝ≥0∞) * (M.cutMoment 2 r) ^ 2 * (M.cutMoment 1 r) ^ 5

/-- **Universal tightness (Corollary I.2.5) at `p = 1`, `q = 1`** in the form used in
(I.4.17): `E_r|K ∩ B_r|² ≤ C₁ · M_r · E_r|K|` eventually, with `M_r` the edian of the
(Hydro) hypothesis.

The constant `C₁` is **not** cosmetic: the paper's `⪯` absorbs a universal constant,
and the landed form of Corollary I.2.5 (`Tightness.MomentRatio.momentConst 1 1`)
delivers a large explicit one.  Stating this bound with `C₁ = 1` would be a
strengthening, not a consequence of I.2.5. -/
def TightInterSecond (M : SourceModelData) (C₁ : ℝ) : Prop :=
  0 < C₁ ∧ ∀ᶠ r : ℝ in atTop,
    Analysis.I420Case2.interSecond M r
      ≤ ENNReal.ofReal (C₁ * (M.Mr r : ℝ) * (M.cutMoment 1 r).toReal)

/-! ## 3. Scalar algebra for the square roots -/

/-- `√(D B² A⁵) = √D · B · A² · √A` for `A, B, D ≥ 0`. -/
theorem sqrt_mul_sq_mul_pow_five {D A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D) :
    Real.sqrt (D * B ^ 2 * A ^ 5) = Real.sqrt D * B * A ^ 2 * Real.sqrt A := by
  have hsq : (Real.sqrt D * B * A ^ 2) ^ 2 * A = D * B ^ 2 * A ^ 5 := by
    rw [show (Real.sqrt D * B * A ^ 2) ^ 2 * A
        = (Real.sqrt D) ^ 2 * B ^ 2 * A ^ 5 by ring,
      Real.sq_sqrt hD]
  have hnn : 0 ≤ Real.sqrt D * B * A ^ 2 :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg D) hB) (pow_nonneg hA 2)
  have h2 : Real.sqrt ((Real.sqrt D * B * A ^ 2) ^ 2 * A)
      = Real.sqrt ((Real.sqrt D * B * A ^ 2) ^ 2) * Real.sqrt A :=
    Real.sqrt_mul (x := (Real.sqrt D * B * A ^ 2) ^ 2) (pow_nonneg hnn 2) A
  rw [← hsq, h2, Real.sqrt_sq hnn]

/-- The Case-2 ratio: the `(E|K|)²` factor cancels exactly and leaves
`√D (E|K|)² √M_r / |B_r|`. -/
theorem caseTwo_ratio_algebra {nb A B Mr D : ℝ} (hA : 0 < A) (hB : 0 < B) (hnb : 0 < nb) :
    Real.sqrt D * B * A ^ 2 * Real.sqrt A * Real.sqrt Mr * Real.sqrt A / (nb * A * B)
      = Real.sqrt D * A ^ 2 * Real.sqrt Mr / nb := by
  field_simp
  rw [Real.sq_sqrt hA.le]

/-! ## 4. Case 2: the ratio `E_{2,r} ≤ √(945 C₁) (E|K|)² √M_r / |B_r|` -/

/-- **Case 2 of (I.4.16)–(I.4.17).**  From the Cauchy–Schwarz step, Lemma I.4.16 at
`p = 6`, `k = 2` and universal tightness `E_r|K ∩ B_r|² ≤ C₁ M_r E_r|K|`,

`E_{2,r} ≤ √(945 C₁) (E_{β_c,r}|K|)² √M_r / |B_r|`.

The `(E|K|)²` factor cancels *exactly* against the denominator, so no second-moment
bound is used at all — this is the Case-2 contrast with Case 1's `(E|K|)³/|B_r|`. -/
theorem p2ExclError_le_caseTwo (M : SourceModelData) (C₁ : ℝ) (hC₁ : 0 < C₁)
    (r : ℝ) (hr : 0 ≤ r)
    (h2 : M.cutMoment 2 r ≠ ⊤)
    (h6 : M.cutMoment 6 r ≤ (945 : ℝ≥0∞) * (M.cutMoment 2 r) ^ 2 * (M.cutMoment 1 r) ^ 5)
    (hT : Analysis.I420Case2.interSecond M r
      ≤ ENNReal.ofReal (C₁ * (M.Mr r : ℝ) * (M.cutMoment 1 r).toReal)) :
    M.p2ExclError r ≤ Real.sqrt (945 * C₁) * (M.cutMoment 1 r).toReal ^ 2
      * Real.sqrt ((M.Mr r : ℝ)) / ((M.ball r).ncard : ℝ) := by
  have h1t : M.cutMoment 1 r ≠ ⊤ := M.cutMoment_one_ne_top_of_two h2
  have h6t : M.cutMoment 6 r ≠ ⊤ :=
    ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top h2))
        (ENNReal.pow_ne_top h1t)) h6
  have hISt : Analysis.I420Case2.interSecond M r ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hT
  have hRHSfin : (M.cutMoment 6 r) ^ (1 / 2 : ℝ)
      * (Analysis.I420Case2.interSecond M r) ^ (1 / 2 : ℝ) ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) h6t).ne
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hISt).ne
  have hconn : M.connCubeMass r ≠ ⊤ :=
    ne_top_of_le_ne_top hRHSfin (connCubeMass_le_cs M r)
  have h6r : (M.cutMoment 6 r).toReal ≤ 945 * (M.cutMoment 2 r).toReal ^ 2
      * (M.cutMoment 1 r).toReal ^ 5 := by
    have hfin : (945 : ℝ≥0∞) * (M.cutMoment 2 r) ^ 2 * (M.cutMoment 1 r) ^ 5 ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top h2))
        (ENNReal.pow_ne_top h1t)
    have h := ENNReal.toReal_mono hfin h6
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofNat] using h
  have hTr : (Analysis.I420Case2.interSecond M r).toReal
      ≤ C₁ * (M.Mr r : ℝ) * (M.cutMoment 1 r).toReal := by
    have hcast : (ENNReal.ofReal (C₁ * (M.Mr r : ℝ) * (M.cutMoment 1 r).toReal)).toReal
        = C₁ * (M.Mr r : ℝ) * (M.cutMoment 1 r).toReal :=
      ENNReal.toReal_ofReal (by positivity)
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hT
    rwa [hcast] at h
  have hcs_real : (M.connCubeMass r).toReal
      ≤ Real.sqrt (945 * (M.cutMoment 2 r).toReal ^ 2 * (M.cutMoment 1 r).toReal ^ 5)
        * Real.sqrt (C₁ * (M.Mr r : ℝ) * (M.cutMoment 1 r).toReal) := by
    have hstep := ENNReal.toReal_mono hRHSfin (connCubeMass_le_cs M r)
    rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow,
      ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hstep
    refine hstep.trans ?_
    exact mul_le_mul (Real.sqrt_le_sqrt h6r) (Real.sqrt_le_sqrt hTr) (by positivity) (by positivity)
  have hden : (0 : ℝ) < ((M.ball r).ncard : ℝ) * (M.cutMoment 1 r).toReal
      * (M.cutMoment 2 r).toReal := CaseOne.window_den_pos M hr h2
  have hA : (0 : ℝ) < (M.cutMoment 1 r).toReal := by
    have := SourceModelData.one_le_cutMoment_one_toReal M r h1t; linarith
  have hB : (0 : ℝ) < (M.cutMoment 2 r).toReal := by
    have := SourceModelData.one_le_cutMoment_two_toReal M r h2; linarith
  have hnb : (0 : ℝ) < ((M.ball r).ncard : ℝ) := by
    exact_mod_cast SourceModelData.ball_ncard_pos M r hr
  have hmid : (M.connCubeMass r).toReal
      ≤ Real.sqrt (945 * C₁) * (M.cutMoment 2 r).toReal * (M.cutMoment 1 r).toReal ^ 2
        * Real.sqrt (M.cutMoment 1 r).toReal * Real.sqrt ((M.Mr r : ℝ))
        * Real.sqrt (M.cutMoment 1 r).toReal := by
    have h := hcs_real
    rw [sqrt_mul_sq_mul_pow_five hA.le hB.le (show (0 : ℝ) ≤ 945 by norm_num)] at h
    refine h.trans_eq ?_
    rw [Real.sqrt_mul (show (0 : ℝ) ≤ 945 by norm_num),
      Real.sqrt_mul (show (0 : ℝ) ≤ C₁ * (M.Mr r : ℝ) by positivity),
      Real.sqrt_mul hC₁.le]
    ring
  refine (M.p2ExclError_le_connCubeMass_div r hr h2 hconn).trans ?_
  exact (div_le_div_of_nonneg_right hmid hden.le).trans_eq
    (caseTwo_ratio_algebra hA hB hnb)

/-! ## 5. Scalar lemmas for the Case-2 rate `(9α - 3d)/4` -/

/-- `(2κ r^a)² = (2κ)² r^{2a}`. -/
theorem sq_two_mul_rpow {r κ a : ℝ} (hr : 0 ≤ r) :
    (2 * κ * r ^ a) ^ 2 = (2 * κ) ^ 2 * r ^ (2 * a) := by
  rw [mul_pow, mul_pow, ← Real.rpow_natCast (r ^ a) 2, ← Real.rpow_mul hr]
  ring_nf

/-- `r^{2a} · r^{(e+a)/4} · r^{-e} = r^{(9a-3e)/4}`. -/
theorem rpow_combine {r : ℝ} (hr : 0 < r) (a e : ℝ) :
    r ^ (2 * a) * r ^ ((e + a) / 4) * r ^ (-e) = r ^ ((9 * a - 3 * e) / 4) := by
  rw [← Real.rpow_add hr, ← Real.rpow_add hr]
  congr 1
  ring

/-- `√M ≤ √ε r^{(e+a)/4}` from `M ≤ ε r^{(e+a)/2}`. -/
theorem sqrt_le_sqrt_mul_rpow {r ε Mr e a : ℝ} (hr : 0 < r) (hε : 0 ≤ ε)
    (h : Mr ≤ ε * r ^ ((e + a) / 2)) :
    Real.sqrt Mr ≤ Real.sqrt ε * r ^ ((e + a) / 4) := by
  have hsq : Real.sqrt (ε * r ^ ((e + a) / 2)) = Real.sqrt ε * r ^ ((e + a) / 4) := by
    rw [Real.sqrt_mul hε]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hr.le,
      show (e + a) / 2 * (1 / 2 : ℝ) = (e + a) / 4 by ring]
  rw [← hsq]
  exact Real.sqrt_le_sqrt h

/-- `1/nb ≤ B r^{-e}` from `r^e/nb ≤ B`. -/
theorem one_div_le_mul_rpow_neg {r nb B e : ℝ} (hr : 0 < r) (h : r ^ e / nb ≤ B) :
    1 / nb ≤ B * r ^ (-e) := by
  have hpe : (0 : ℝ) < r ^ e := Real.rpow_pos_of_pos hr e
  have h1 : (r ^ e)⁻¹ * (r ^ e / nb) ≤ (r ^ e)⁻¹ * B :=
    mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hpe.le)
  have hl : (r ^ e)⁻¹ * (r ^ e / nb) = 1 / nb := by
    rw [div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ hpe.ne', one_mul, one_div]
  have hr' : (r ^ e)⁻¹ * B = B * r ^ (-e) := by
    rw [Real.rpow_neg hr.le]; ring
  rwa [hl, hr'] at h1

/-! ## 6. Case 2: the rate (I.4.18) and `E_{2,r} → 0` at `d = 3α` -/

/-- **The Case-2 rate (I.4.18)**, with the `o` of (Hydro) resolved into an explicit `ε`:

`E_{2,r} ≤ √(945 C₁) (2α/β_c)² 2^d √ε · r^{(9α-3d)/4}` eventually, for every `ε > 0`.

The exponent is the paper's `2α - d + (d+α)/4 = (9α - 3d)/4`; the
`M_r = o(r^{(d+α)/2})` of (Hydro) enters only through `√M_r ≤ √ε r^{(d+α)/4}`. -/
theorem eventually_p2ExclError_le_sqrt (M : SourceModelData) (C₁ : ℝ)
    (hT : TightInterSecond M C₁)
    (hκ : 0 < M.α / (M.betaCrit : ℝ))
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hH : Hydro M)
    (h2 : ∀ᶠ r : ℝ in atTop, M.cutMoment 2 r ≠ ⊤)
    (h6 : ∀ᶠ r : ℝ in atTop,
      M.cutMoment 6 r ≤ (945 : ℝ≥0∞) * (M.cutMoment 2 r) ^ 2 * (M.cutMoment 1 r) ^ 5)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℝ in atTop, M.p2ExclError r ≤
      Real.sqrt (945 * C₁) * (2 * (M.α / (M.betaCrit : ℝ))) ^ 2 * (2 : ℝ) ^ (M.d : ℝ)
        * Real.sqrt ε * r ^ ((9 * M.α - 3 * (M.d : ℝ)) / 4) := by
  obtain ⟨hC₁, hTe⟩ := hT
  have hrpos : ∀ᶠ r : ℝ in atTop, 0 < r := eventually_gt_atTop 0
  have hm1 : ∀ᶠ r : ℝ in atTop,
      (M.cutMoment 1 r).toReal ≤ 2 * (M.α / (M.betaCrit : ℝ)) * r ^ M.α := by
    have hlt : ∀ᶠ r : ℝ in atTop,
        (M.cutMassAt r 0).toReal / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α) < 2 :=
      (tendsto_order.1 hP).2 2 (by norm_num)
    filter_upwards [hlt, hrpos] with r hr hrr
    have hpos : (0 : ℝ) < (M.α / (M.betaCrit : ℝ)) * r ^ M.α :=
      mul_pos hκ (Real.rpow_pos_of_pos hrr M.α)
    rw [SourceModelData.cutMassAt_zero_eq_cutMoment] at hr
    rw [div_lt_iff₀ hpos] at hr
    linarith
  have hMrle : ∀ᶠ r : ℝ in atTop,
      (M.Mr r : ℝ) ≤ ε * r ^ (((M.d : ℝ) + M.α) / 2) := by
    have hlt : ∀ᶠ r : ℝ in atTop, (M.Mr r : ℝ) / r ^ (((M.d : ℝ) + M.α) / 2) < ε :=
      (tendsto_order.1 hH).2 ε hε
    filter_upwards [hlt, hrpos] with r hr hrr
    have hpos : (0 : ℝ) < r ^ (((M.d : ℝ) + M.α) / 2) := Real.rpow_pos_of_pos hrr _
    rw [div_lt_iff₀ hpos] at hr
    linarith
  filter_upwards [h6, hTe, h2, hm1, hMrle, TriangleAverage.eventually_pow_div_ncard_le M, hrpos]
    with r h6r hTr h2r hm1r hMrr hballr hr
  have hbase := p2ExclError_le_caseTwo M C₁ hC₁ r hr.le h2r h6r hTr
  have h1t : M.cutMoment 1 r ≠ ⊤ := M.cutMoment_one_ne_top_of_two h2r
  have hA : (0 : ℝ) < (M.cutMoment 1 r).toReal := by
    have := SourceModelData.one_le_cutMoment_one_toReal M r h1t; linarith
  have hnb : (0 : ℝ) < ((M.ball r).ncard : ℝ) := by
    exact_mod_cast SourceModelData.ball_ncard_pos M r hr.le
  have hP945 : (0 : ℝ) ≤ Real.sqrt (945 * C₁) := Real.sqrt_nonneg _
  have hs1 : (M.cutMoment 1 r).toReal ^ 2
      ≤ (2 * (M.α / (M.betaCrit : ℝ))) ^ 2 * r ^ (2 * M.α) := by
    have h := pow_le_pow_left₀ hA.le hm1r 2
    rwa [sq_two_mul_rpow hr.le] at h
  have hs2 : Real.sqrt ((M.Mr r : ℝ))
      ≤ Real.sqrt ε * r ^ (((M.d : ℝ) + M.α) / 4) :=
    sqrt_le_sqrt_mul_rpow hr hε.le hMrr
  have hs3 : (1 : ℝ) / ((M.ball r).ncard : ℝ)
      ≤ (2 : ℝ) ^ (M.d : ℝ) * r ^ (-(M.d : ℝ)) := by
    refine one_div_le_mul_rpow_neg hr ?_
    simpa only [Real.rpow_natCast] using hballr
  have step1 : Real.sqrt (945 * C₁) * (M.cutMoment 1 r).toReal ^ 2
      ≤ Real.sqrt (945 * C₁) * ((2 * (M.α / (M.betaCrit : ℝ))) ^ 2 * r ^ (2 * M.α)) :=
    mul_le_mul_of_nonneg_left hs1 hP945
  have step2 : Real.sqrt (945 * C₁) * (M.cutMoment 1 r).toReal ^ 2 * Real.sqrt ((M.Mr r : ℝ))
      ≤ Real.sqrt (945 * C₁) * ((2 * (M.α / (M.betaCrit : ℝ))) ^ 2 * r ^ (2 * M.α))
        * (Real.sqrt ε * r ^ (((M.d : ℝ) + M.α) / 4)) :=
    mul_le_mul step1 hs2 (Real.sqrt_nonneg _) (by positivity)
  have step3 : Real.sqrt (945 * C₁) * (M.cutMoment 1 r).toReal ^ 2
        * Real.sqrt ((M.Mr r : ℝ)) * (1 / ((M.ball r).ncard : ℝ))
      ≤ Real.sqrt (945 * C₁) * ((2 * (M.α / (M.betaCrit : ℝ))) ^ 2 * r ^ (2 * M.α))
        * (Real.sqrt ε * r ^ (((M.d : ℝ) + M.α) / 4))
        * ((2 : ℝ) ^ (M.d : ℝ) * r ^ (-(M.d : ℝ))) :=
    mul_le_mul step2 hs3 (by positivity) (by positivity)
  have hfinal : Real.sqrt (945 * C₁) * ((2 * (M.α / (M.betaCrit : ℝ))) ^ 2 * r ^ (2 * M.α))
        * (Real.sqrt ε * r ^ (((M.d : ℝ) + M.α) / 4))
        * ((2 : ℝ) ^ (M.d : ℝ) * r ^ (-(M.d : ℝ)))
      = Real.sqrt (945 * C₁) * (2 * (M.α / (M.betaCrit : ℝ))) ^ 2 * (2 : ℝ) ^ (M.d : ℝ)
        * Real.sqrt ε * r ^ ((9 * M.α - 3 * (M.d : ℝ)) / 4) := by
    have hre : r ^ (2 * M.α) * r ^ (((M.d : ℝ) + M.α) / 4) * r ^ (-(M.d : ℝ))
        = r ^ ((9 * M.α - 3 * (M.d : ℝ)) / 4) := rpow_combine hr M.α (M.d : ℝ)
    calc Real.sqrt (945 * C₁) * ((2 * (M.α / (M.betaCrit : ℝ))) ^ 2 * r ^ (2 * M.α))
          * (Real.sqrt ε * r ^ (((M.d : ℝ) + M.α) / 4))
          * ((2 : ℝ) ^ (M.d : ℝ) * r ^ (-(M.d : ℝ)))
        = Real.sqrt (945 * C₁) * ((2 * (M.α / (M.betaCrit : ℝ))) ^ 2 * (2 : ℝ) ^ (M.d : ℝ)
            * Real.sqrt ε)
          * (r ^ (2 * M.α) * r ^ (((M.d : ℝ) + M.α) / 4) * r ^ (-(M.d : ℝ))) := by ring
      _ = Real.sqrt (945 * C₁) * ((2 * (M.α / (M.betaCrit : ℝ))) ^ 2 * (2 : ℝ) ^ (M.d : ℝ)
            * Real.sqrt ε) * r ^ ((9 * M.α - 3 * (M.d : ℝ)) / 4) := by rw [hre]
      _ = Real.sqrt (945 * C₁) * (2 * (M.α / (M.betaCrit : ℝ))) ^ 2 * (2 : ℝ) ^ (M.d : ℝ)
          * Real.sqrt ε * r ^ ((9 * M.α - 3 * (M.d : ℝ)) / 4) := by ring
  refine hbase.trans ?_
  rw [div_eq_mul_one_div]
  exact step3.trans_eq hfinal

/-- `9!! = 945`, the constant `(2p-3)!!` of Lemma I.4.16 at `p = 6`. -/
theorem doubleFactorial_nine : Nat.doubleFactorial (2 * 6 - 3) = 945 := by decide

/-- **The Case-2 rate (I.4.18)** in the paper's own shape: along (Hydro),
`E_{2,r} ⪯ r^{(9α-3d)/4}`, which is `o(1)` exactly when `d = 3α`. -/
theorem eventually_p2ExclError_le_rpow (M : SourceModelData) (C₁ : ℝ)
    (hT : TightInterSecond M C₁)
    (hκ : 0 < M.α / (M.betaCrit : ℝ))
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hH : Hydro M)
    (h2 : ∀ᶠ r : ℝ in atTop, M.cutMoment 2 r ≠ ⊤)
    (h6 : ∀ᶠ r : ℝ in atTop,
      M.cutMoment 6 r ≤ (945 : ℝ≥0∞) * (M.cutMoment 2 r) ^ 2 * (M.cutMoment 1 r) ^ 5) :
    ∀ᶠ r : ℝ in atTop, M.p2ExclError r ≤
      Real.sqrt (945 * C₁) * (2 * (M.α / (M.betaCrit : ℝ))) ^ 2 * (2 : ℝ) ^ (M.d : ℝ)
        * r ^ ((9 * M.α - 3 * (M.d : ℝ)) / 4) := by
  have h := eventually_p2ExclError_le_sqrt M C₁ hT hκ hP hH h2 h6 (ε := 1) one_pos
  simpa using h

/-- **Case 2 of Proposition I.4.15**: `E_{2,r} → 0` when `d = 3α` and (Hydro) holds. -/
theorem p2ExclError_tendsto_zero_of_caseTwo (M : SourceModelData) (C₁ : ℝ)
    (hT : TightInterSecond M C₁)
    (hd : (M.d : ℝ) = 3 * M.α)
    (hκ : 0 < M.α / (M.betaCrit : ℝ))
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hH : Hydro M)
    (h2 : ∀ᶠ r : ℝ in atTop, M.cutMoment 2 r ≠ ⊤)
    (h6 : ∀ᶠ r : ℝ in atTop,
      M.cutMoment 6 r ≤ (945 : ℝ≥0∞) * (M.cutMoment 2 r) ^ 2 * (M.cutMoment 1 r) ^ 5) :
    Tendsto M.p2ExclError atTop (𝓝 0) := by
  have hC₁ : 0 < C₁ := hT.1
  have hnn : ∀ᶠ r : ℝ in atTop, 0 ≤ M.p2ExclError r := by
    filter_upwards [h2, eventually_ge_atTop (0 : ℝ)] with r h2r hr
    exact SourceModelData.p2ExclError_nonneg M r hr h2r
  have hKpos : (0 : ℝ) < Real.sqrt (945 * C₁) * (2 * (M.α / (M.betaCrit : ℝ))) ^ 2
      * (2 : ℝ) ^ (M.d : ℝ) := by
    have h1 : (0 : ℝ) < Real.sqrt (945 * C₁) :=
      Real.sqrt_pos.2 (by have : (0:ℝ) < C₁ := hC₁; positivity)
    have h2' : (0 : ℝ) < 2 * (M.α / (M.betaCrit : ℝ)) := by positivity
    have h3 : (0 : ℝ) < (2 : ℝ) ^ (M.d : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
    have h4 : (0 : ℝ) < (2 * (M.α / (M.betaCrit : ℝ))) ^ 2 := by positivity
    positivity
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · filter_upwards [hnn] with r hr
    linarith
  · set K : ℝ := Real.sqrt (945 * C₁) * (2 * (M.α / (M.betaCrit : ℝ))) ^ 2
      * (2 : ℝ) ^ (M.d : ℝ) with hK
    have hKpos' : (0 : ℝ) < K := by rw [hK]; exact hKpos
    have hbK : (0 : ℝ) < b / (2 * K) := by positivity
    have hε : (0 : ℝ) < (b / (2 * K)) ^ 2 := by positivity
    have hev := eventually_p2ExclError_le_sqrt M C₁ hT hκ hP hH h2 h6
      (ε := (b / (2 * K)) ^ 2) hε
    refine hev.mono ?_
    intro r hr
    have hexp : (9 * M.α - 3 * (M.d : ℝ)) / 4 = 0 := by rw [hd]; ring
    have hsq : Real.sqrt ((b / (2 * K)) ^ 2) = b / (2 * K) := Real.sqrt_sq hbK.le
    rw [hexp, Real.rpow_zero, mul_one, hsq, ← hK] at hr
    have hKb : K * (b / (2 * K)) = b / 2 := by
      field_simp
    rw [hKb] at hr
    linarith

/-! ## 6b. Universal tightness (Corollary I.2.5) at the cutoff law, discharged -/

/-- The cutoff law is a probability measure (it is `edgeMeasure` of a `unitInterval` profile). -/
instance instIsProbabilityMeasureCutLaw (M : SourceModelData) (r : ℝ) :
    IsProbabilityMeasure (M.cutLaw r) :=
  M.cutLaw_eq_edgeMeasure r ▸ inferInstance

/-- The closed ball as a finite set, with underlying set `M.ball r`. -/
theorem coe_ballF (M : SourceModelData) (r : ℝ) :
    ((E1Sign.ballF M r : Finset M.V) : Set M.V) = M.ball r :=
  (M.finite_ball r).coe_toFinset

/-- The origin lies in the closed window for `0 ≤ r`. -/
theorem zero_mem_ball (M : SourceModelData) {r : ℝ} (hr : 0 ≤ r) : (0 : M.V) ∈ M.ball r := by
  change M.S.ρ (toVec (0 : M.V)) ≤ r
  have h0 : toVec (0 : M.V) = 0 := by
    funext i
    simp [toVec]
  rw [h0, M.S.ρ_zero]
  exact hr

/-- **`|K_max(B_r)|` is `maxClusterInBall`**: every cluster meeting `B_r` meets it in a vertex
of `B_r`, so the supremum over all of `V` is the supremum over `B_r`. -/
theorem clusterMaxVol_ballF (M : SourceModelData) (r : ℝ) (ω : Config M.V) :
    Percolation.clusterMaxVol ω (E1Sign.ballF M r) = M.maxClusterInBall r ω := by
  refine le_antisymm ?_ ?_
  · rw [Percolation.clusterMaxVol, SourceModelData.maxClusterInBall, coe_ballF M r]
    exact Finset.sup_le fun w _ => le_iSup (fun x : M.V => clusterVolIn ω x (M.ball r)) w
  · rw [SourceModelData.maxClusterInBall]
    refine iSup_le fun x => ?_
    by_cases hne : (cluster ω x ∩ M.ball r).Nonempty
    · obtain ⟨z, hzK, hzB⟩ := hne
      have hzW : z ∈ E1Sign.ballF M r := (E1Sign.mem_ballF M).mpr hzB
      have hcl : cluster ω x = cluster ω z := cluster_eq_iff.mpr (mem_cluster_iff.mp hzK)
      have hEq : clusterVolIn ω x (M.ball r) = clusterVolIn ω z (M.ball r) := by
        simp only [clusterVolIn, hcl]
      have hz := Percolation.clusterVolIn_le_clusterMaxVol ω hzW
      rw [coe_ballF M r] at hz
      rw [hEq]
      exact hz
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      simp [clusterVolIn, hne]

/-- **The edian of the model is the paper's `M_β(B_r)`**: both are the least `n` with
`P(|K_max(B_r)| ≥ n) ≤ e^{-1}`. -/
theorem Mr_eq_edianMaxVol (M : SourceModelData) (r : ℝ) :
    M.Mr r = Percolation.edianMaxVol (M.cutLaw r) (E1Sign.ballF M r)
      (Percolation.exists_edianMaxVol (E1Sign.ballF M r)) := by
  classical
  have hset : ∀ n : ℕ,
      ((M.cutLaw r).real {ω : Config M.V | (n : ℝ≥0∞) ≤ M.maxClusterInBall r ω} ≤ Real.exp (-1))
        ↔ ((M.cutLaw r) {ω : Config M.V | (n : ℝ≥0∞) ≤
            Percolation.clusterMaxVol ω (E1Sign.ballF M r)} ≤ ENNReal.ofReal (Real.exp (-1))) := by
    intro n
    have hEq : {ω : Config M.V | (n : ℝ≥0∞) ≤ M.maxClusterInBall r ω}
        = {ω : Config M.V | (n : ℝ≥0∞) ≤ Percolation.clusterMaxVol ω (E1Sign.ballF M r)} := by
      ext ω
      rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, clusterMaxVol_ballF M r ω]
    rw [hEq, Measure.real,
      ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (Real.exp_pos (-1)).le]
  have hne : ({n : ℕ | (M.cutLaw r).real
      {ω : Config M.V | (n : ℝ≥0∞) ≤ M.maxClusterInBall r ω} ≤ Real.exp (-1)}).Nonempty :=
    ⟨_, (hset _).mpr (Nat.find_spec (Percolation.exists_edianMaxVol (E1Sign.ballF M r)))⟩
  refine le_antisymm ?_ ?_
  · rw [SourceModelData.Mr]
    exact Nat.sInf_le ((hset _).mpr (Nat.find_spec
      (Percolation.exists_edianMaxVol (E1Sign.ballF M r))))
  · rw [SourceModelData.Mr]
    exact Nat.find_min' (Percolation.exists_edianMaxVol (E1Sign.ballF M r))
      ((hset _).mp (Nat.sInf_mem hne))

/-- **Corollary I.2.5 at `p = 1`, `q = 1` at the cutoff law**:
`E_r|K ∩ B_r|² ≤ momentConst 1 1 · M_r · E_r|K ∩ B_r|`. -/
theorem interSecond_le_edian (M : SourceModelData) (r : ℝ) (hr : 0 ≤ r) :
    Analysis.I420Case2.interSecond M r
      ≤ ENNReal.ofReal (Tightness.momentConst 1 1)
        * ENNReal.ofReal ((Percolation.edianMaxVol (M.cutLaw r) (E1Sign.ballF M r)
            (Percolation.exists_edianMaxVol (E1Sign.ballF M r)) : ℝ))
        * (M.cutMoment 1 r) := by
  have hzero : (0 : M.V) ∈ E1Sign.ballF M r := (E1Sign.mem_ballF M).mpr (zero_mem_ball M hr)
  have hne : (E1Sign.ballF M r).Nonempty := ⟨0, hzero⟩
  have h28 : Percolation.Display28 (M.cutLaw r)
      (fun ω => Percolation.clusterMaxVol ω (E1Sign.ballF M r)) := by
    rw [M.cutLaw_eq_edgeMeasure]
    exact Percolation.display28_edgeMeasure _ hne (M.cutProb r) (E1Sign.cutProb_lt_one M r)
  have h29 : Percolation.Display29 (M.cutLaw r)
      (fun ω => Percolation.clusterMaxVol ω (E1Sign.ballF M r))
      (fun ω => clusterVolIn ω (0 : M.V) ((E1Sign.ballF M r : Finset M.V) : Set M.V)) := by
    rw [M.cutLaw_eq_edgeMeasure]
    exact Percolation.display29_edgeMeasure _ hne 0 (M.cutProb r) (E1Sign.cutProb_lt_one M r)
  have hI23 : Percolation.UniversalTightnessI23 (M.cutLaw r)
      (fun ω => Percolation.clusterMaxVol ω (E1Sign.ballF M r))
      (fun ω => clusterVolIn ω (0 : M.V) ((E1Sign.ballF M r : Finset M.V) : Set M.V))
      (Percolation.edianMaxVol (M.cutLaw r) (E1Sign.ballF M r)
        (Percolation.exists_edianMaxVol (E1Sign.ballF M r))) :=
    Percolation.universalTightnessI23_of_displays _ 0 h28 h29
  have h := Percolation.corollary_I_2_5_at_edian (μ := M.cutLaw r) (0 : M.V)
    (E1Sign.ballF M r) hzero hI23 1 1 le_rfl
  rw [coe_ballF M r] at h
  simp only [pow_one] at h
  have hLHS : (∫⁻ ω, clusterVolIn ω (0 : M.V) (M.ball r) ^ (1 + 1) ∂(M.cutLaw r))
      = Analysis.I420Case2.interSecond M r := by
    simp only [Analysis.I420Case2.interSecond, Analysis.I420Case2.interVol]
  rw [hLHS] at h
  have hstep : (∫⁻ ω, clusterVolIn ω (0 : M.V) (M.ball r) ∂(M.cutLaw r)) ≤ M.cutMoment 1 r := by
    rw [SourceModelData.cutMoment]
    exact lintegral_mono fun ω => by
      simpa only [pow_one] using Percolation.clusterVolIn_le_clusterVol ω 0 (M.ball r)
  exact h.trans (mul_le_mul_of_nonneg_left hstep bot_le)

/-- **Universal tightness is not an extra hypothesis**: `TightInterSecond` holds with the
explicit constant `momentConst 1 1` of Corollary I.2.5. -/
theorem tightInterSecond_momentConst (M : SourceModelData)
    (h2 : ∀ᶠ r : ℝ in atTop, M.cutMoment 2 r ≠ ⊤) :
    TightInterSecond M (Tightness.momentConst 1 1) := by
  have hmc : (0 : ℝ) < Tightness.momentConst 1 1 := by
    rw [Tightness.momentConst]; positivity
  refine ⟨hmc, ?_⟩
  filter_upwards [eventually_ge_atTop (0 : ℝ), h2] with r hr h2r
  have hm1 : M.cutMoment 1 r ≠ ⊤ := M.cutMoment_one_ne_top_of_two h2r
  refine (interSecond_le_edian M r hr).trans_eq ?_
  have hed : Percolation.edianMaxVol (M.cutLaw r) (E1Sign.ballF M r)
      (Percolation.exists_edianMaxVol (E1Sign.ballF M r)) = M.Mr r :=
    (Mr_eq_edianMaxVol M r).symm
  have hcut : M.cutMoment 1 r = ENNReal.ofReal ((M.cutMoment 1 r).toReal) :=
    (ENNReal.ofReal_toReal hm1).symm
  rw [hcut]
  rw [show (ENNReal.ofReal ((M.cutMoment 1 r).toReal)).toReal = (M.cutMoment 1 r).toReal from
    ENNReal.toReal_ofReal (by positivity)]
  rw [hed]
  have h2' : ENNReal.ofReal (Tightness.momentConst 1 1) * ENNReal.ofReal ((M.Mr r : ℝ))
      = ENNReal.ofReal (Tightness.momentConst 1 1 * (M.Mr r : ℝ)) :=
    (ENNReal.ofReal_mul hmc.le).symm
  rw [h2']
  exact (ENNReal.ofReal_mul (by positivity)).symm

/-- **Case 2 of Proposition I.4.15, with universal tightness discharged.**
At `d = 3α` with (Hydro), the *only* remaining input is Lemma I.4.16 at `p = 6`, `k = 2`. -/
theorem p2ExclError_tendsto_zero_of_caseTwo' (M : SourceModelData)
    (hd : (M.d : ℝ) = 3 * M.α)
    (hκ : 0 < M.α / (M.betaCrit : ℝ))
    (hP : Tendsto (fun r : ℝ => (M.cutMassAt r 0).toReal
      / ((M.α / (M.betaCrit : ℝ)) * r ^ M.α)) atTop (𝓝 1))
    (hH : Hydro M)
    (h2 : ∀ᶠ r : ℝ in atTop, M.cutMoment 2 r ≠ ⊤)
    (h6 : ∀ᶠ r : ℝ in atTop,
      M.cutMoment 6 r ≤ (945 : ℝ≥0∞) * (M.cutMoment 2 r) ^ 2 * (M.cutMoment 1 r) ^ 5) :
    Tendsto M.p2ExclError atTop (𝓝 0) :=
  p2ExclError_tendsto_zero_of_caseTwo M _ (tightInterSecond_momentConst M h2) hd hκ hP hH h2 h6

/-! ## 7. Axiom audit -/

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.CaseTwo.connCubeMass_eq_jointMoment_two
#print axioms PercLib.CriticalLRP.CaseTwo.connCubeMass_le_cs
#print axioms PercLib.CriticalLRP.CaseTwo.sqrt_mul_sq_mul_pow_five
#print axioms PercLib.CriticalLRP.CaseTwo.caseTwo_ratio_algebra
#print axioms PercLib.CriticalLRP.CaseTwo.p2ExclError_le_caseTwo
#print axioms PercLib.CriticalLRP.CaseTwo.sq_two_mul_rpow
#print axioms PercLib.CriticalLRP.CaseTwo.rpow_combine
#print axioms PercLib.CriticalLRP.CaseTwo.sqrt_le_sqrt_mul_rpow
#print axioms PercLib.CriticalLRP.CaseTwo.one_div_le_mul_rpow_neg
#print axioms PercLib.CriticalLRP.CaseTwo.doubleFactorial_nine
#print axioms PercLib.CriticalLRP.CaseTwo.eventually_p2ExclError_le_sqrt
#print axioms PercLib.CriticalLRP.CaseTwo.eventually_p2ExclError_le_rpow
#print axioms PercLib.CriticalLRP.CaseTwo.p2ExclError_tendsto_zero_of_caseTwo
#print axioms PercLib.CriticalLRP.CaseTwo.coe_ballF
#print axioms PercLib.CriticalLRP.CaseTwo.zero_mem_ball
#print axioms PercLib.CriticalLRP.CaseTwo.clusterMaxVol_ballF
#print axioms PercLib.CriticalLRP.CaseTwo.Mr_eq_edianMaxVol
#print axioms PercLib.CriticalLRP.CaseTwo.interSecond_le_edian
#print axioms PercLib.CriticalLRP.CaseTwo.tightInterSecond_momentConst
#print axioms PercLib.CriticalLRP.CaseTwo.p2ExclError_tendsto_zero_of_caseTwo'

end CaseTwo
end PercLib.CriticalLRP
