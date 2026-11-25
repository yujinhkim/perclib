/-
Case 3 of `(HD)` at an arbitrary normalized source norm, in the **literal printed** form.

The paper's third disjunct of `(HD)` (arXiv:2508.18807v1, p. 9, as it appears in
`Orchestration.Defs.HD`) is

  `τ_{β_c}(x,y) ≤ C (log ‖x-y‖_S)^(-1) ‖x-y‖_S^(-d+2)`   for `x ≠ y`, `d = 6`, `α = 2`,

with the *raw, unshifted* `Real.log` at the model's normalized source norm `S.ρ`.  The landed
`Analysis/OpenTriangle/Case3Literal/Main` proves the Case 3 tail theorem from a domination stated
at the lattice **sup norm** and only for `‖z‖ ≥ 2`.

This file closes the gap between the two, and records exactly what the raw logarithm costs.

# The sign structure of the raw logarithm (this is the point)

For `0 < ρ < 1` one has `(log ρ)⁻¹ < 0`, so at a pair with source norm below `1` the printed
hypothesis would force `τ < 0`.  Since `τ` is a probability (`M.twoPoint_nonneg`), that cannot
happen: **the printed HD(3) implies that the normalized source norm has no nonzero lattice vector
of norm `< 1`** (`one_le_srcNorm_of_HD3`).  At `ρ = 1` Lean's `(Real.log 1)⁻¹ = 0` forces
`τ = 0` (`twoPoint_eq_zero_of_srcNorm_one`).  Consequently no positive lower gap is invented and
no `log (1+ρ)` is substituted for `log ρ`: the bridge below is the literal one, and the only price
is an explicit constant.

# What is proved

* `HD3_to_supNorm` — the printed source-norm domination implies the sup-norm domination
  `τ z ≤ C' ‖z‖^(-d+2) (log ‖z‖)⁻¹` for `‖z‖ ≥ 2`, with the explicit constant
  `case3SrcConst d C S = max (C c^(-d+2) (1 + (-log c)/log 4))
   ((T^e)⁻¹ log T) + 1`, `c = srcLowerUnit S`, `T = max 2 (4/c)`, `e = -d+2`.
* `openTriangle_toReal_le_logMajorant_case3` — the pointwise square-logarithmic bound at the
  model's own radius `M.S.dist 0 y`, with every `srcUpperConst`/log comparison constant retained.
* `isLogErrorFunction_nablaTail_of_HD_third_disjunct` — `Analysis.IsLogErrorFunction` of
  `fun r => (M.nablaTail r).toReal`, i.e. Lemma I.4.3 Case 3 at the configured model, from the
  printed third disjunct verbatim.

No `SourceNormData` instantiation of an unshifted global form, no Kozma factorization, no
`M.nablaTail`-level triangle condition: only the literal HD(3) input is used.
-/
module

public import PercLib.CriticalLRP.Analysis.OpenTriangle.Case3SrcNorm.Defs
public import PercLib.CriticalLRP.Analysis.OpenTriangleLogTail
public import PercLib.CriticalLRP.Analysis.LatticeConvolution.NormShell
public import PercLib.CriticalLRP.Analysis.Polygon.Model

/-!
# Literal printed Case 3 at an arbitrary normalized source norm

Proofs that the raw, unshifted HD(3) hypothesis gives logarithmic integrability of the actual
source-model open-triangle tail. The threshold and input/output constants are defined in
`Case3SrcNorm.Defs`. This is the literal printed hypothesis, not the shifted-log repair, and no
non-vacuity assertion is made for it on a prescribed model.
-/

@[expose] public section

set_option autoImplicit false

set_option linter.hashCommand false

open scoped ENNReal NNReal Topology

open Filter

namespace PercLib.CriticalLRP.Orchestration

open CriticalLRPConv

/-! ## §1 The transfer threshold and constant

Nothing here depends on the model: the threshold `T = max 2 (4 / c)` is where the lower
comparison `c‖z‖ ≤ ρ` makes `log (c‖z‖)` safely positive, and the constant collects the two
regimes `‖z‖ ≥ T` (genuine transfer) and `2 ≤ ‖z‖ < T` (where only `τ ≤ 1` is available, but the
region is bounded). -/

theorem two_le_case3SrcThreshold {d : ℕ} (S : SourceNormData d) :
    (2 : ℝ) ≤ case3SrcThreshold S :=
  le_max_left _ _

theorem one_lt_case3SrcThreshold {d : ℕ} (S : SourceNormData d) :
    (1 : ℝ) < case3SrcThreshold S :=
  lt_of_lt_of_le one_lt_two (two_le_case3SrcThreshold S)

theorem case3SrcThreshold_pos {d : ℕ} (S : SourceNormData d) : 0 < case3SrcThreshold S :=
  lt_of_lt_of_le zero_lt_two (two_le_case3SrcThreshold S)

theorem log_four_pos : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)

theorem log_case3SrcThreshold_pos {d : ℕ} (S : SourceNormData d) :
    0 < Real.log (case3SrcThreshold S) :=
  Real.log_pos (one_lt_case3SrcThreshold S)

/-- `srcLowerUnit S * T ≥ 4`: the reason for the threshold. -/
theorem four_le_srcLowerUnit_mul_threshold {d : ℕ} (S : SourceNormData d) (hd : 1 ≤ d) :
    (4 : ℝ) ≤ srcLowerUnit S * case3SrcThreshold S := by
  have hc : 0 < srcLowerUnit S := srcLowerUnit_pos S hd
  have hR : 4 / srcLowerUnit S ≤ case3SrcThreshold S := le_max_right _ _
  have h4 : srcLowerUnit S * (4 / srcLowerUnit S) = 4 := by
    field_simp
  calc (4 : ℝ) = srcLowerUnit S * (4 / srcLowerUnit S) := h4.symm
    _ ≤ srcLowerUnit S * case3SrcThreshold S := mul_le_mul_of_nonneg_left hR hc.le

theorem one_lt_srcLowerUnit_mul_threshold {d : ℕ} (S : SourceNormData d) (hd : 1 ≤ d) :
    (1 : ℝ) < srcLowerUnit S * case3SrcThreshold S :=
  lt_of_lt_of_le (by norm_num) (four_le_srcLowerUnit_mul_threshold S hd)

theorem log_srcLowerUnit_mul_threshold_pos {d : ℕ} (S : SourceNormData d) (hd : 1 ≤ d) :
    0 < Real.log (srcLowerUnit S * case3SrcThreshold S) :=
  Real.log_pos (one_lt_srcLowerUnit_mul_threshold S hd)

theorem case3SrcConst_pos (d : ℕ) (C : ℝ) (S : SourceNormData d) :
    0 < case3SrcConst d C S := by
  have hB : 0 ≤ (case3SrcThreshold S ^ (-(d : ℝ) + 2))⁻¹ * Real.log (case3SrcThreshold S) :=
    mul_nonneg (inv_nonneg.mpr (Real.rpow_nonneg (case3SrcThreshold_pos S).le _))
      (log_case3SrcThreshold_pos S).le
  rw [case3SrcConst]
  have : (0 : ℝ) ≤ max (C * (srcLowerUnit S) ^ (-(d : ℝ) + 2) *
        (1 + (-(Real.log (srcLowerUnit S))) / Real.log 4))
      ((case3SrcThreshold S ^ (-(d : ℝ) + 2))⁻¹ * Real.log (case3SrcThreshold S)) :=
    le_trans hB (le_max_right _ _)
  linarith

/-- The first (genuine transfer) branch feeds the constant. -/
theorem le_case3SrcConst_of_le_left (d : ℕ) (C : ℝ) (S : SourceNormData d) {A : ℝ}
    (hA : A ≤ C * (srcLowerUnit S) ^ (-(d : ℝ) + 2) *
        (1 + (-(Real.log (srcLowerUnit S))) / Real.log 4)) :
    A ≤ case3SrcConst d C S := by
  rw [case3SrcConst]
  exact hA.trans (le_trans (le_max_left _ _) (le_add_of_nonneg_right zero_le_one))

/-- The second (bounded-region) branch feeds the constant. -/
theorem le_case3SrcConst_of_le_right (d : ℕ) (C : ℝ) (S : SourceNormData d) {B : ℝ}
    (hB : B ≤ (case3SrcThreshold S ^ (-(d : ℝ) + 2))⁻¹ * Real.log (case3SrcThreshold S)) :
    B ≤ case3SrcConst d C S := by
  rw [case3SrcConst]
  exact hB.trans (le_trans (le_max_right _ _) (le_add_of_nonneg_right zero_le_one))

/-- **The logarithmic ratio behind the transfer.**  For `0 < c ≤ 1` and `4 ≤ c s`,

`log s / log (c s) = 1 + (-log c) / log (c s) ≤ 1 + (-log c) / log 4`.

No information about the *upper* norm comparison is used; the whole loss is the additive
`-log c` absorbed by the margin `log 4` supplied by the threshold. -/
theorem log_div_log_le_one_add {c s : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hcs : 4 ≤ c * s) :
    Real.log s / Real.log (c * s) ≤ 1 + (-(Real.log c)) / Real.log 4 := by
  have hs : 0 < s := by nlinarith
  have hcs0 : 0 < c * s := by linarith
  have hlogcs : 0 < Real.log (c * s) := Real.log_pos (by linarith)
  have hlog4 : 0 < Real.log 4 := log_four_pos
  have hlog4le : Real.log 4 ≤ Real.log (c * s) := Real.log_le_log (by norm_num) hcs
  have hlc : Real.log c ≤ 0 := Real.log_nonpos hc.le hc1
  have hL : (0 : ℝ) ≤ -(Real.log c) := neg_nonneg.mpr hlc
  have hsub : Real.log s = Real.log (c * s) + (-(Real.log c)) := by
    have := Real.log_mul hc.ne' hs.ne'
    linarith
  have h1 : (Real.log (c * s) + (-(Real.log c))) / Real.log (c * s)
      = 1 + (-(Real.log c)) / Real.log (c * s) := by
    field_simp
  rw [hsub, h1]
  have h2 : (-(Real.log c)) / Real.log (c * s) ≤ (-(Real.log c)) / Real.log 4 := by
    rw [div_le_div_iff₀ hlogcs hlog4]
    exact mul_le_mul_of_nonneg_left hlog4le hL
  linarith

/-- The reciprocal form used in the pointwise estimate. -/
theorem inv_log_le_const_mul_inv_log {c s : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hcs : 4 ≤ c * s) :
    (Real.log (c * s))⁻¹ ≤ (1 + (-(Real.log c)) / Real.log 4) * (Real.log s)⁻¹ := by
  have hs : 0 < s := by nlinarith
  have hlogs : 0 < Real.log s := Real.log_pos (by nlinarith)
  have h := log_div_log_le_one_add hc hc1 hcs
  have h' := mul_le_mul_of_nonneg_right h (inv_nonneg.mpr hlogs.le)
  have e : Real.log s / Real.log (c * s) * (Real.log s)⁻¹ = (Real.log (c * s))⁻¹ := by
    rw [div_eq_mul_inv, mul_assoc, mul_comm (Real.log (c * s))⁻¹, ← mul_assoc,
      mul_inv_cancel₀ hlogs.ne', one_mul]
  rwa [e] at h'


/-! ## §2 Lattice and sign helpers -/

/-- A nonzero lattice vector has nonzero image in `ℝ^d`. -/
theorem toVec_ne_zero {d : ℕ} {z : Fin d → ℤ} (hz : z ≠ 0) : toVec z ≠ 0 := by
  intro h
  apply hz
  funext i
  have hi := congrFun h i
  simp only [toVec, Pi.zero_apply] at hi
  exact_mod_cast hi

/-- The source norm is even, so the pair `(0, z)` sees the same radius as `z`. -/
theorem rho_toVec_zero_sub {d : ℕ} (S : SourceNormData d) (z : Fin d → ℤ) :
    S.ρ (toVec ((0 : Fin d → ℤ) - z)) = S.ρ (toVec z) := by
  rw [show toVec ((0 : Fin d → ℤ) - z) = -(toVec z) from by funext i; simp [toVec]]
  exact S.ρ_neg (toVec z)

end PercLib.CriticalLRP.Orchestration

namespace PercLib.CriticalLRP.Orchestration.SourceModelData

open PercLib.CriticalLRP.Orchestration

variable (M : SourceModelData)

/-- The model's two-point function is nonnegative: it is the real value of a probability. -/
theorem twoPoint_nonneg (β : ℝ≥0) (x y : M.V) : 0 ≤ M.twoPoint β x y :=
  ENNReal.toReal_nonneg

/-- At the origin pair the model's real two-point function *is* the literal `litT` profile. -/
theorem twoPoint_eq_litT (β : ℝ≥0) (z : M.V) :
    M.twoPoint β 0 z = HD.litT M.kernel M.kernel_nonneg β z := rfl

/-- The origin two-point function is a probability. -/
theorem twoPoint_zero_le_one (β : ℝ≥0) (z : M.V) : M.twoPoint β 0 z ≤ 1 := by
  rw [M.twoPoint_eq_litT β z]
  exact HD.litT_le_one M.kernel M.kernel_nonneg β z

/-- **The printed HD(3) forbids small nonzero source norms.**

For `0 < ρ < 1` the factor `(log ρ)⁻¹` is negative, while `ρ^(-d+2) > 0` and `C > 0`, so the
printed domination would give `τ < 0`, contradicting `twoPoint_nonneg`.  Hence, under the printed
hypothesis, every nonzero lattice vector has source norm at least `1`.  This is *derived*, not
assumed: no positive lower gap is introduced, and the conclusion is exactly what the raw
(unshifted) logarithm yields. -/
theorem one_le_srcNorm_of_HD3 {C : ℝ} (hC : 0 < C) {β : ℝ≥0}
    (hHD : ∀ x y : M.V, x ≠ y →
      M.twoPoint β x y ≤ C * (Real.log (M.S.ρ (toVec (x - y))))⁻¹ *
        (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2))
    {z : M.V} (hz : z ≠ 0) : 1 ≤ M.S.ρ (toVec z) := by
  by_contra hlt
  rw [not_le] at hlt
  have hρpos : 0 < M.S.ρ (toVec z) := M.S.ρ_pos _ (toVec_ne_zero hz)
  have hkey := hHD 0 z (Ne.symm hz)
  rw [rho_toVec_zero_sub] at hkey
  have hlog : (Real.log (M.S.ρ (toVec z)))⁻¹ < 0 :=
    inv_neg''.mpr (Real.log_neg hρpos hlt)
  have hpos_pow : 0 < (M.S.ρ (toVec z)) ^ (-(M.d : ℝ) + 2) := Real.rpow_pos_of_pos hρpos _
  have hneg : C * (Real.log (M.S.ρ (toVec z)))⁻¹ * (M.S.ρ (toVec z)) ^ (-(M.d : ℝ) + 2) < 0 := by
    have h1 : (Real.log (M.S.ρ (toVec z)))⁻¹ * (M.S.ρ (toVec z)) ^ (-(M.d : ℝ) + 2) < 0 :=
      mul_neg_of_neg_of_pos hlog hpos_pow
    have h2 := mul_neg_of_pos_of_neg hC h1
    calc C * (Real.log (M.S.ρ (toVec z)))⁻¹ * (M.S.ρ (toVec z)) ^ (-(M.d : ℝ) + 2)
        = C * ((Real.log (M.S.ρ (toVec z)))⁻¹ * (M.S.ρ (toVec z)) ^ (-(M.d : ℝ) + 2)) := by
          ring
      _ < 0 := h2
  have hnn := M.twoPoint_nonneg β 0 z
  linarith

/-- **The unit source shell is killed by the printed HD(3).**

At `ρ = 1`, Lean's `(Real.log 1)⁻¹ = 0` makes the printed bound `τ ≤ 0`, so `τ = 0` there.  This
is the second half of the near-origin bookkeeping: the raw logarithm has no blow-up at `ρ = 1` in
Lean's convention, it has a zero. -/
theorem twoPoint_eq_zero_of_srcNorm_one {C : ℝ} {β : ℝ≥0}
    (hHD : ∀ x y : M.V, x ≠ y →
      M.twoPoint β x y ≤ C * (Real.log (M.S.ρ (toVec (x - y))))⁻¹ *
        (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2))
    {z : M.V} (hz : z ≠ 0) (hρ : M.S.ρ (toVec z) = 1) : M.twoPoint β 0 z = 0 := by
  have hkey := hHD 0 z (Ne.symm hz)
  rw [rho_toVec_zero_sub, hρ, Real.log_one, inv_zero, Real.one_rpow] at hkey
  have hle : M.twoPoint β 0 z ≤ 0 := by simpa using hkey
  exact le_antisymm hle (M.twoPoint_nonneg β 0 z)

end PercLib.CriticalLRP.Orchestration.SourceModelData

namespace PercLib.CriticalLRP.Orchestration

open CriticalLRPConv

/-! ## §3 The transfer: printed source-norm HD(3) ⇒ sup-norm HD(3)

This is the step the problem singles out: `srcLowerUnit S * ‖z‖ ≤ S.ρ (toVec z)` alone does not
transfer the domination, because the raw logarithm is compared against `log ‖z‖`, and
`log (c‖z‖)` can be arbitrarily small for `c‖z‖` near `1`.  The threshold `T = max 2 (4/c)` makes
`log (c‖z‖) ≥ log 4`, and the bounded region `2 ≤ ‖z‖ ≤ T` is closed by `τ ≤ 1`. -/
theorem HD3_to_supNorm {M : SourceModelData} (hd2 : 2 < M.d) {C : ℝ} (hC : 0 < C) {β : ℝ≥0}
    (hHD : ∀ x y : M.V, x ≠ y →
      M.twoPoint β x y ≤ C * (Real.log (M.S.ρ (toVec (x - y))))⁻¹ *
        (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2))
    {z : M.V} (hz2 : 2 ≤ ‖z‖) :
    twoPointFunction M.kernel M.kernel_nonneg β 0 z ≤
      ENNReal.ofReal
        (case3SrcConst M.d C M.S * ‖z‖ ^ (-(M.d : ℝ) + 2) * (Real.log ‖z‖)⁻¹) := by
  have hd1 : 1 ≤ M.d := by omega
  have he0 : (-(M.d : ℝ) + 2) ≤ 0 := by
    have h2 : (2 : ℝ) ≤ (M.d : ℝ) := by exact_mod_cast hd2.le
    linarith
  have hz : z ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hz2
    linarith
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hρpos : 0 < M.S.ρ (toVec z) := M.S.ρ_pos _ (toVec_ne_zero hz)
  have hρ1 : 1 ≤ M.S.ρ (toVec z) := M.one_le_srcNorm_of_HD3 hC hHD hz
  have hτraw : M.twoPoint β 0 z ≤
      C * (Real.log (M.S.ρ (toVec z)))⁻¹ * (M.S.ρ (toVec z)) ^ (-(M.d : ℝ) + 2) := by
    have hkey := hHD 0 z (Ne.symm hz)
    rwa [rho_toVec_zero_sub] at hkey
  have hc : 0 < srcLowerUnit M.S := srcLowerUnit_pos M.S hd1
  have hc1 : srcLowerUnit M.S ≤ 1 := srcLowerUnit_le_one M.S
  have hlow : srcLowerUnit M.S * ‖z‖ ≤ M.S.ρ (toVec z) := by
    have h := srcLowerUnit_mul_linfNorm_le M.S hd1 z
    rwa [← coe_norm_eq_linfNorm z] at h
  have hlogz : 0 ≤ Real.log ‖z‖ := Real.log_nonneg (by linarith)
  have hX : 0 ≤ ‖z‖ ^ (-(M.d : ℝ) + 2) * (Real.log ‖z‖)⁻¹ :=
    mul_nonneg (Real.rpow_nonneg hzpos.le _) (inv_nonneg.mpr hlogz)
  have hfin : M.twoPoint β 0 z ≤
      case3SrcConst M.d C M.S * ‖z‖ ^ (-(M.d : ℝ) + 2) * (Real.log ‖z‖)⁻¹ := by
    by_cases hbig : case3SrcThreshold M.S ≤ ‖z‖
    · -- regime `‖z‖ ≥ T`: the genuine transfer
      have hcs4 : (4 : ℝ) ≤ srcLowerUnit M.S * ‖z‖ :=
        le_trans (four_le_srcLowerUnit_mul_threshold M.S hd1)
          (mul_le_mul_of_nonneg_left hbig hc.le)
      have hcspos : 0 < srcLowerUnit M.S * ‖z‖ := by linarith
      have hlogcs : 0 < Real.log (srcLowerUnit M.S * ‖z‖) := Real.log_pos (by linarith)
      have hlogcmp : (Real.log (M.S.ρ (toVec z)))⁻¹ ≤ (Real.log (srcLowerUnit M.S * ‖z‖))⁻¹ :=
        inv_anti₀ hlogcs (Real.log_le_log hcspos hlow)
      have hpowcmp : (M.S.ρ (toVec z)) ^ (-(M.d : ℝ) + 2) ≤
          (srcLowerUnit M.S * ‖z‖) ^ (-(M.d : ℝ) + 2) :=
        Real.rpow_le_rpow_of_nonpos hcspos hlow he0
      have hstep1 : C * (Real.log (M.S.ρ (toVec z)))⁻¹ * (M.S.ρ (toVec z)) ^ (-(M.d : ℝ) + 2)
          ≤ C * (Real.log (srcLowerUnit M.S * ‖z‖))⁻¹ *
              (srcLowerUnit M.S * ‖z‖) ^ (-(M.d : ℝ) + 2) := by
        refine mul_le_mul ?_ hpowcmp (Real.rpow_nonneg hρpos.le _) ?_
        · exact mul_le_mul_of_nonneg_left hlogcmp hC.le
        · exact mul_nonneg hC.le (inv_nonneg.mpr hlogcs.le)
      have hsplit : (srcLowerUnit M.S * ‖z‖) ^ (-(M.d : ℝ) + 2)
          = (srcLowerUnit M.S) ^ (-(M.d : ℝ) + 2) * ‖z‖ ^ (-(M.d : ℝ) + 2) :=
        Real.mul_rpow hc.le hzpos.le
      have hratio : (Real.log (srcLowerUnit M.S * ‖z‖))⁻¹
          ≤ (1 + (-(Real.log (srcLowerUnit M.S))) / Real.log 4) * (Real.log ‖z‖)⁻¹ :=
        inv_log_le_const_mul_inv_log hc hc1 hcs4
      have hstep2 : C * (Real.log (srcLowerUnit M.S * ‖z‖))⁻¹ *
            (srcLowerUnit M.S * ‖z‖) ^ (-(M.d : ℝ) + 2)
          ≤ C * (srcLowerUnit M.S) ^ (-(M.d : ℝ) + 2) *
              (1 + (-(Real.log (srcLowerUnit M.S))) / Real.log 4) *
              ‖z‖ ^ (-(M.d : ℝ) + 2) * (Real.log ‖z‖)⁻¹ := by
        rw [hsplit]
        have h0 : 0 ≤ C * (srcLowerUnit M.S) ^ (-(M.d : ℝ) + 2) *
            ‖z‖ ^ (-(M.d : ℝ) + 2) :=
          mul_nonneg (mul_nonneg hC.le (Real.rpow_nonneg hc.le _))
            (Real.rpow_nonneg hzpos.le _)
        have hstep := mul_le_mul_of_nonneg_left hratio h0
        calc C * (Real.log (srcLowerUnit M.S * ‖z‖))⁻¹ *
              ((srcLowerUnit M.S) ^ (-(M.d : ℝ) + 2) * ‖z‖ ^ (-(M.d : ℝ) + 2))
            = (C * (srcLowerUnit M.S) ^ (-(M.d : ℝ) + 2) * ‖z‖ ^ (-(M.d : ℝ) + 2)) *
                (Real.log (srcLowerUnit M.S * ‖z‖))⁻¹ := by ring
          _ ≤ (C * (srcLowerUnit M.S) ^ (-(M.d : ℝ) + 2) * ‖z‖ ^ (-(M.d : ℝ) + 2)) *
                ((1 + (-(Real.log (srcLowerUnit M.S))) / Real.log 4) * (Real.log ‖z‖)⁻¹) := hstep
          _ = C * (srcLowerUnit M.S) ^ (-(M.d : ℝ) + 2) *
                (1 + (-(Real.log (srcLowerUnit M.S))) / Real.log 4) *
                ‖z‖ ^ (-(M.d : ℝ) + 2) * (Real.log ‖z‖)⁻¹ := by ring
      have hA : C * (srcLowerUnit M.S) ^ (-(M.d : ℝ) + 2) *
            (1 + (-(Real.log (srcLowerUnit M.S))) / Real.log 4) ≤ case3SrcConst M.d C M.S :=
        le_case3SrcConst_of_le_left M.d C M.S le_rfl
      have hstep3 := mul_le_mul_of_nonneg_right hA hX
      have hstep4 : C * (srcLowerUnit M.S) ^ (-(M.d : ℝ) + 2) *
              (1 + (-(Real.log (srcLowerUnit M.S))) / Real.log 4) *
              ‖z‖ ^ (-(M.d : ℝ) + 2) * (Real.log ‖z‖)⁻¹
          ≤ case3SrcConst M.d C M.S * ‖z‖ ^ (-(M.d : ℝ) + 2) * (Real.log ‖z‖)⁻¹ := by
        calc C * (srcLowerUnit M.S) ^ (-(M.d : ℝ) + 2) *
                (1 + (-(Real.log (srcLowerUnit M.S))) / Real.log 4) *
                ‖z‖ ^ (-(M.d : ℝ) + 2) * (Real.log ‖z‖)⁻¹
            = (C * (srcLowerUnit M.S) ^ (-(M.d : ℝ) + 2) *
                (1 + (-(Real.log (srcLowerUnit M.S))) / Real.log 4)) *
                (‖z‖ ^ (-(M.d : ℝ) + 2) * (Real.log ‖z‖)⁻¹) := by ring
          _ ≤ case3SrcConst M.d C M.S *
                (‖z‖ ^ (-(M.d : ℝ) + 2) * (Real.log ‖z‖)⁻¹) := hstep3
          _ = case3SrcConst M.d C M.S * ‖z‖ ^ (-(M.d : ℝ) + 2) * (Real.log ‖z‖)⁻¹ := by ring
      exact hτraw.trans (by linarith [hstep1, hstep2, hstep4])
    · -- regime `2 ≤ ‖z‖ ≤ T`: bounded region, closed by `τ ≤ 1` and the branch `(T^e)⁻¹ log T`
      have hsmall : ‖z‖ < case3SrcThreshold M.S := lt_of_not_ge hbig
      have hzle : ‖z‖ ≤ case3SrcThreshold M.S := le_of_lt hsmall
      have hTpos : 0 < case3SrcThreshold M.S := case3SrcThreshold_pos M.S
      have hlogs : 0 < Real.log ‖z‖ := Real.log_pos (by linarith)
      have h1 : 1 ≤ (case3SrcThreshold M.S ^ (-(M.d : ℝ) + 2))⁻¹ *
          ‖z‖ ^ (-(M.d : ℝ) + 2) := by
        rw [← div_eq_inv_mul]
        refine (one_le_div₀ (Real.rpow_pos_of_pos hTpos _)).mpr ?_
        exact Real.rpow_le_rpow_of_nonpos hzpos hzle he0
      have h2 : 1 ≤ Real.log (case3SrcThreshold M.S) * (Real.log ‖z‖)⁻¹ := by
        rw [← div_eq_mul_inv]
        exact (one_le_div₀ hlogs).mpr (Real.log_le_log hzpos hzle)
      have h3 : 1 ≤ ((case3SrcThreshold M.S ^ (-(M.d : ℝ) + 2))⁻¹ *
            ‖z‖ ^ (-(M.d : ℝ) + 2)) *
          (Real.log (case3SrcThreshold M.S) * (Real.log ‖z‖)⁻¹) := by
        calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
          _ ≤ _ := mul_le_mul h1 h2 zero_le_one (by positivity)
      have hB : 1 ≤ ((case3SrcThreshold M.S ^ (-(M.d : ℝ) + 2))⁻¹ *
            Real.log (case3SrcThreshold M.S)) *
          ‖z‖ ^ (-(M.d : ℝ) + 2) * (Real.log ‖z‖)⁻¹ := by
        calc (1 : ℝ) ≤ ((case3SrcThreshold M.S ^ (-(M.d : ℝ) + 2))⁻¹ *
              ‖z‖ ^ (-(M.d : ℝ) + 2)) *
              (Real.log (case3SrcThreshold M.S) * (Real.log ‖z‖)⁻¹) := h3
          _ = ((case3SrcThreshold M.S ^ (-(M.d : ℝ) + 2))⁻¹ *
              Real.log (case3SrcThreshold M.S)) *
              ‖z‖ ^ (-(M.d : ℝ) + 2) * (Real.log ‖z‖)⁻¹ := by ring
      have hBC : ((case3SrcThreshold M.S ^ (-(M.d : ℝ) + 2))⁻¹ *
            Real.log (case3SrcThreshold M.S)) ≤ case3SrcConst M.d C M.S :=
        le_case3SrcConst_of_le_right M.d C M.S le_rfl
      have hstep := mul_le_mul_of_nonneg_right hBC hX
      have hτ1 : M.twoPoint β 0 z ≤ 1 := M.twoPoint_zero_le_one β z
      refine hτ1.trans (hB.trans ?_)
      calc ((case3SrcThreshold M.S ^ (-(M.d : ℝ) + 2))⁻¹ *
            Real.log (case3SrcThreshold M.S)) *
            ‖z‖ ^ (-(M.d : ℝ) + 2) * (Real.log ‖z‖)⁻¹
          = ((case3SrcThreshold M.S ^ (-(M.d : ℝ) + 2))⁻¹ *
              Real.log (case3SrcThreshold M.S)) *
              (‖z‖ ^ (-(M.d : ℝ) + 2) * (Real.log ‖z‖)⁻¹) := by ring
        _ ≤ case3SrcConst M.d C M.S *
              (‖z‖ ^ (-(M.d : ℝ) + 2) * (Real.log ‖z‖)⁻¹) := hstep
        _ = case3SrcConst M.d C M.S * ‖z‖ ^ (-(M.d : ℝ) + 2) * (Real.log ‖z‖)⁻¹ := by ring
  have hτ : twoPointFunction M.kernel M.kernel_nonneg β 0 z
      = ENNReal.ofReal (M.twoPoint β 0 z) := by
    rw [← ENNReal.ofReal_toReal (HD.twoPointFunction_ne_top M.kernel M.kernel_nonneg β 0 z)]
    rfl
  rw [hτ]
  exact ENNReal.ofReal_le_ofReal hfin


/-! ## §4 The output side: from the sup-norm radius to the source radius

The landed Case 3 shell theorem bounds the open triangle by `K (log (1 + ‖x‖))^(-2)` at the sup
norm.  The source-norm tail consumes `K' (log (1 + S.ρ))^(-2)`.  Since `S.ρ (toVec x) ≤ C ‖x‖`
with `C = srcUpperConst S ≥ 1`, the two logarithms differ by the explicit factor
`srcLogConstUpper S = 1 + log (2 + C)/log 2`, and the square of that factor is the whole output
cost. -/

/-- The upper logarithmic comparison constant is positive. -/
theorem srcLogConstUpper_pos {d : ℕ} (S : SourceNormData d) : 0 < srcLogConstUpper S := by
  have h1 : (0 : ℝ) < Real.log (2 + srcUpperConst S) :=
    Real.log_pos (by linarith [one_le_srcUpperConst S])
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : (0 : ℝ) < Real.log (2 + srcUpperConst S) / Real.log 2 := div_pos h1 h2
  simp only [srcLogConstUpper]
  linarith

theorem case3SrcOutConst_nonneg (d : ℕ) (C : ℝ) (S : SourceNormData d) :
    0 ≤ case3SrcOutConst d C S :=
  mul_nonneg (HD.Case3.case3Conv3ConstShell_nonneg (case3SrcConst_pos d C S).le)
    (Real.rpow_nonneg (srcLogConstUpper_pos S).le _)

/-- **A negative power of the smaller argument.**  If `0 < a ≤ K b` with `K > 0`, then
`b^(-2) ≤ K^2 a^(-2)`.  Used to move `(log (1 + ‖x‖))^(-2)` to `(log (1 + S.ρ x))^(-2)`. -/
theorem rpow_neg_two_le_of_le_mul {a b K : ℝ} (ha : 0 < a) (hb : 0 < b) (hK : 0 < K)
    (h : a ≤ K * b) : b ^ (-2 : ℝ) ≤ K ^ (2 : ℝ) * a ^ (-2 : ℝ) := by
  have hKb : 0 < K * b := mul_pos hK hb
  have h1 : (K * b) ^ (-2 : ℝ) ≤ a ^ (-2 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos ha h (by norm_num)
  have h2 : (K * b) ^ (-2 : ℝ) = K ^ (-2 : ℝ) * b ^ (-2 : ℝ) := Real.mul_rpow hK.le hb.le
  have h3 : K ^ (2 : ℝ) * K ^ (-2 : ℝ) = 1 := by
    rw [show (-2 : ℝ) = -(2 : ℝ) from by norm_num, Real.rpow_neg hK.le]
    exact mul_inv_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos hK 2))
  calc b ^ (-2 : ℝ) = (K ^ (2 : ℝ) * K ^ (-2 : ℝ)) * b ^ (-2 : ℝ) := by rw [h3, one_mul]
    _ = K ^ (2 : ℝ) * (K ^ (-2 : ℝ) * b ^ (-2 : ℝ)) := by ring
    _ = K ^ (2 : ℝ) * (K * b) ^ (-2 : ℝ) := by rw [h2]
    _ ≤ K ^ (2 : ℝ) * a ^ (-2 : ℝ) := mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hK.le _)

/-- **The output-side logarithmic comparison.**  For a nonzero lattice point,
`log (1 + S.dist 0 y) ≤ srcLogConstUpper S * log (1 + ‖y‖)`: the only loss between the source
radius and the sup-norm radius, with the constant displayed. -/
theorem log_one_add_sdist_le (M : SourceModelData) {y : M.V} (hy : 1 ≤ ‖y‖) :
    Real.log (1 + M.S.dist 0 y) ≤ srcLogConstUpper M.S * Real.log (1 + ‖y‖) := by
  have hdist : M.S.dist 0 y = M.S.ρ (toVec y) := dist_zero_eq_srcNorm M.S y
  have hupper : M.S.ρ (toVec y) ≤ srcUpperConst M.S * ‖y‖ := by
    have h := srcNorm_le_upper_linfNorm M.S y
    rwa [← coe_norm_eq_linfNorm y] at h
  have hC1 : 1 ≤ srcUpperConst M.S := one_le_srcUpperConst M.S
  have hCpos : 0 < srcUpperConst M.S := srcUpperConst_pos M.S
  have hρ0 : 0 ≤ M.S.ρ (toVec y) := src_nonneg M.S (toVec y)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogy : 0 < Real.log (1 + ‖y‖) := Real.log_pos (by linarith)
  have hlogC : 0 < Real.log (2 + srcUpperConst M.S) := Real.log_pos (by linarith)
  have h1 : 1 + M.S.ρ (toVec y) ≤ srcUpperConst M.S * (1 + ‖y‖) := by nlinarith
  have h3 : Real.log (1 + M.S.ρ (toVec y)) ≤ Real.log (srcUpperConst M.S * (1 + ‖y‖)) :=
    Real.log_le_log (by linarith) h1
  rw [Real.log_mul hCpos.ne' (by linarith : (1 + ‖y‖) ≠ 0)] at h3
  have h4 : Real.log (srcUpperConst M.S) ≤
      (Real.log (2 + srcUpperConst M.S) / Real.log 2) * Real.log (1 + ‖y‖) := by
    have hlogC' : Real.log (srcUpperConst M.S) ≤ Real.log (2 + srcUpperConst M.S) :=
      Real.log_le_log hCpos (by linarith)
    have h6 : Real.log 2 ≤ Real.log (1 + ‖y‖) := Real.log_le_log (by norm_num) (by linarith)
    have h7 : 0 ≤ Real.log (2 + srcUpperConst M.S) / Real.log 2 := div_nonneg hlogC.le hlog2.le
    calc Real.log (srcUpperConst M.S) ≤ Real.log (2 + srcUpperConst M.S) := hlogC'
      _ = Real.log (2 + srcUpperConst M.S) / Real.log 2 * Real.log 2 := by
          rw [div_mul_cancel₀ _ hlog2.ne']
      _ ≤ Real.log (2 + srcUpperConst M.S) / Real.log 2 * Real.log (1 + ‖y‖) :=
          mul_le_mul_of_nonneg_left h6 h7
  calc Real.log (1 + M.S.dist 0 y) = Real.log (1 + M.S.ρ (toVec y)) := by rw [hdist]
    _ ≤ Real.log (srcUpperConst M.S) + Real.log (1 + ‖y‖) := h3
    _ ≤ (Real.log (2 + srcUpperConst M.S) / Real.log 2) * Real.log (1 + ‖y‖) +
          Real.log (1 + ‖y‖) := by linarith
    _ = srcLogConstUpper M.S * Real.log (1 + ‖y‖) := by
        rw [srcLogConstUpper]; ring


/-- Nonzero lattice points have sup norm at least `1` (any dimension). -/
theorem one_le_norm_of_ne_zero_gen {d : ℕ} {z : Fin d → ℤ} (hz : z ≠ 0) : (1 : ℝ) ≤ ‖z‖ := by
  have hone : (1 : ℕ) ≤ FiniteVolume.linfNorm z :=
    Nat.one_le_iff_ne_zero.mpr (fun h => hz (FiniteVolume.linfNorm_eq_zero_iff.mp h))
  rw [coe_norm_eq_linfNorm]
  exact_mod_cast hone

end PercLib.CriticalLRP.Orchestration

namespace PercLib.CriticalLRP.Orchestration

open CriticalLRPConv

/-! ## §5 The literal Case 3 bound at the configured model (`d = 6`)

The landed shell theorem lives on `Fin 6 → ℤ`; the model carries its dimension as a field, so the
statements below take `hd6 : M.d = 6` and specialise the model inside the proof (`obtain`/`subst`),
keeping the *statement* at `M.V`. -/

/-- **Lemma I.4.3 shape, pointwise, at the model's own source radius**, from the printed HD(3).

The open triangle at `y ≠ 0` is bounded by
`case3Conv3ConstShell C' · srcLogConstUpper(S)^2 · (log (1 + S.dist 0 y))^(-2)`, where `C'` is the
transferred sup-norm constant of `HD3_to_supNorm`.  Every constant is displayed; the two
logarithms are compared by `log_one_add_sdist_le`, and the `srcUpperConst` is where the output norm
comparison is spent. -/
theorem openTriangle_toReal_le_logMajorant_case3 (M : SourceModelData) (hd6 : M.d = 6)
    {C : ℝ} (_hC : 0 < C) {β : ℝ≥0}
    (hHDsup : ∀ z : M.V, 2 ≤ ‖z‖ →
      twoPointFunction M.kernel M.kernel_nonneg β 0 z ≤
        ENNReal.ofReal
          (case3SrcConst M.d C M.S * ‖z‖ ^ (-(M.d : ℝ) + 2) * (Real.log ‖z‖)⁻¹))
    {y : M.V} (hy : y ≠ 0) :
    (TriTail.openTriangle M.kernel M.kernel_nonneg β 0 y).toReal
      ≤ Analysis.logMajorant (case3SrcOutConst M.d C M.S) 2 (M.S.dist 0 y) := by
  obtain ⟨d, hd1, α, hα, S, K, K0, K1, K2, K3, K4⟩ := M
  subst hd6
  let M6 : SourceModelData := ⟨6, hd1, α, hα, S, K, K0, K1, K2, K3, K4⟩
  change (TriTail.openTriangle M6.kernel M6.kernel_nonneg β 0 y).toReal
      ≤ Analysis.logMajorant (case3SrcOutConst M6.d C M6.S) 2 (M6.S.dist 0 y)
  have hHD6 : ∀ z : M6.V, 2 ≤ ‖z‖ →
      twoPointFunction M6.kernel M6.kernel_nonneg β 0 z ≤
        ENNReal.ofReal
          (case3SrcConst M6.d C M6.S * ‖z‖ ^ (-(M6.d : ℝ) + 2) * (Real.log ‖z‖)⁻¹) := hHDsup
  have hy6 : y ≠ 0 := hy
  have hC' : (0 : ℝ) ≤ case3SrcConst M6.d C M6.S := (case3SrcConst_pos M6.d C M6.S).le
  have hJinv : ∀ (a : M6.V) (e : Sym2 M6.V),
      M6.kernel (Sym2.map (fun x => x + a) e) = M6.kernel e := fun a e => M6.kernel_shift a e
  have hshell : TriTail.openTriangle M6.kernel M6.kernel_nonneg β 0 y
      ≤ ENNReal.ofReal (HD.Case3.case3Conv3ConstShell (case3SrcConst M6.d C M6.S) *
          (Real.log (1 + ‖y‖)) ^ (-2 : ℝ)) :=
    HD.openTriangle_le_ofReal_log_sq_case3Shell (J := M6.kernel) (hJ := M6.kernel_nonneg)
      (β := β) hJinv hC' hHD6 hy6
  have hKc : (0 : ℝ) ≤ HD.Case3.case3Conv3ConstShell (case3SrcConst M6.d C M6.S) :=
    HD.Case3.case3Conv3ConstShell_nonneg hC'
  have hbnonneg : (0 : ℝ) ≤
      HD.Case3.case3Conv3ConstShell (case3SrcConst M6.d C M6.S) *
        (Real.log (1 + ‖y‖)) ^ (-2 : ℝ) :=
    mul_nonneg hKc
      (Real.rpow_nonneg (Real.log_nonneg (by linarith [one_le_norm_of_ne_zero_gen hy6])) _)
  have hreal : (TriTail.openTriangle M6.kernel M6.kernel_nonneg β 0 y).toReal
      ≤ HD.Case3.case3Conv3ConstShell (case3SrcConst M6.d C M6.S) *
          (Real.log (1 + ‖y‖)) ^ (-2 : ℝ) := by
    calc (TriTail.openTriangle M6.kernel M6.kernel_nonneg β 0 y).toReal
        ≤ (ENNReal.ofReal (HD.Case3.case3Conv3ConstShell (case3SrcConst M6.d C M6.S) *
            (Real.log (1 + ‖y‖)) ^ (-2 : ℝ))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hshell
      _ = _ := ENNReal.toReal_ofReal hbnonneg
  have hy1 : (1 : ℝ) ≤ ‖y‖ := one_le_norm_of_ne_zero_gen hy6
  have hlogcmp : Real.log (1 + M6.S.dist 0 y) ≤ srcLogConstUpper M6.S * Real.log (1 + ‖y‖) :=
    log_one_add_sdist_le M6 hy1
  have hdy : 0 < M6.S.dist 0 y := by
    rw [dist_zero_eq_srcNorm]
    exact M6.S.ρ_pos _ (toVec_ne_zero hy6)
  have hloga : 0 < Real.log (1 + M6.S.dist 0 y) := Real.log_pos (by linarith)
  have hlogb : 0 < Real.log (1 + ‖y‖) := Real.log_pos (by linarith)
  have hKpos : 0 < srcLogConstUpper M6.S := srcLogConstUpper_pos M6.S
  have hmono : (Real.log (1 + ‖y‖)) ^ (-2 : ℝ)
      ≤ (srcLogConstUpper M6.S) ^ (2 : ℝ) *
          (Real.log (1 + M6.S.dist 0 y)) ^ (-2 : ℝ) :=
    rpow_neg_two_le_of_le_mul hloga hlogb hKpos hlogcmp
  calc (TriTail.openTriangle M6.kernel M6.kernel_nonneg β 0 y).toReal
      ≤ HD.Case3.case3Conv3ConstShell (case3SrcConst M6.d C M6.S) *
          (Real.log (1 + ‖y‖)) ^ (-2 : ℝ) := hreal
    _ ≤ HD.Case3.case3Conv3ConstShell (case3SrcConst M6.d C M6.S) *
          ((srcLogConstUpper M6.S) ^ (2 : ℝ) *
            (Real.log (1 + M6.S.dist 0 y)) ^ (-2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hmono hKc
    _ = Analysis.logMajorant (case3SrcOutConst M6.d C M6.S) 2 (M6.S.dist 0 y) := by
        rw [Analysis.logMajorant, case3SrcOutConst]
        ring

/-- **Finiteness of the literal open triangle at the configured model** under the printed HD(3). -/
theorem openTriangle_ne_top_case3 (M : SourceModelData) (hd6 : M.d = 6)
    {C : ℝ} (_hC : 0 < C) {β : ℝ≥0}
    (hHDsup : ∀ z : M.V, 2 ≤ ‖z‖ →
      twoPointFunction M.kernel M.kernel_nonneg β 0 z ≤
        ENNReal.ofReal
          (case3SrcConst M.d C M.S * ‖z‖ ^ (-(M.d : ℝ) + 2) * (Real.log ‖z‖)⁻¹))
    (y : M.V) : TriTail.openTriangle M.kernel M.kernel_nonneg β 0 y ≠ ⊤ := by
  obtain ⟨d, hd1, α, hα, S, K, K0, K1, K2, K3, K4⟩ := M
  subst hd6
  let M6 : SourceModelData := ⟨6, hd1, α, hα, S, K, K0, K1, K2, K3, K4⟩
  change TriTail.openTriangle M6.kernel M6.kernel_nonneg β 0 y ≠ ⊤
  have hHD6 : ∀ z : M6.V, 2 ≤ ‖z‖ →
      twoPointFunction M6.kernel M6.kernel_nonneg β 0 z ≤
        ENNReal.ofReal
          (case3SrcConst M6.d C M6.S * ‖z‖ ^ (-(M6.d : ℝ) + 2) * (Real.log ‖z‖)⁻¹) := hHDsup
  have hC' : (0 : ℝ) ≤ case3SrcConst M6.d C M6.S := (case3SrcConst_pos M6.d C M6.S).le
  have hJinv : ∀ (a : M6.V) (e : Sym2 M6.V),
      M6.kernel (Sym2.map (fun x => x + a) e) = M6.kernel e := fun a e => M6.kernel_shift a e
  exact HD.openTriangle_ne_top_case3Shell (J := M6.kernel) (hJ := M6.kernel_nonneg) (β := β)
    hJinv hC' hHD6 y


/-! ## §6 The Case 3 conclusions at the configured model -/

/-- **The explicit source-norm tail bound** `∇_r ⪯ (log (1 + r))^(-2)`, `r > 0`. -/
theorem nablaTail_le_logMajorant_case3 (M : SourceModelData) (hd6 : M.d = 6)
    {C : ℝ} (hC : 0 < C)
    (hHDsup : ∀ z : M.V, 2 ≤ ‖z‖ →
      twoPointFunction M.kernel M.kernel_nonneg M.betaCrit 0 z ≤
        ENNReal.ofReal
          (case3SrcConst M.d C M.S * ‖z‖ ^ (-(M.d : ℝ) + 2) * (Real.log ‖z‖)⁻¹))
    {r : ℝ} (hr : 0 < r) :
    M.nablaTail r
      ≤ ENNReal.ofReal (Analysis.logMajorant (case3SrcOutConst M.d C M.S) 2 r) := by
  have hbound : ∀ y : M.V, y ≠ 0 →
      (TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y).toReal
        ≤ Analysis.logMajorant (case3SrcOutConst M.d C M.S) 2 (M.S.dist 0 y) :=
    fun y hy => openTriangle_toReal_le_logMajorant_case3 M hd6 hC hHDsup hy
  have hfin : ∀ y : M.V, y ≠ 0 →
      TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y ≠ ⊤ :=
    fun y _ => openTriangle_ne_top_case3 M hd6 hC hHDsup y
  have hF := M.logRadialBound_of_toReal_le (C := case3SrcOutConst M.d C M.S) (p := 2) hbound hfin
  have hmain := Analysis.radialTailSup_le_logMajorant
    (nrm := fun y : M.V => M.S.dist 0 y)
    (F := fun y : M.V => TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y)
    (case3SrcOutConst_nonneg M.d C M.S) (by norm_num : (0 : ℝ) ≤ 2) hr hF
  simpa only [SourceModelData.nablaTail_eq_radialTailSup] using hmain

/-- **`∇_r → 0` in `ℝ≥0∞`** under the printed HD(3), read off from the uniform pointwise bound.
This is the smoothness half of Lemma I.4.3, not a triangle-condition/operator statement. -/
theorem tendsto_nablaTail_zero_of_HD3 (M : SourceModelData) (hd6 : M.d = 6)
    {C : ℝ} (hC : 0 < C)
    (hHDsup : ∀ z : M.V, 2 ≤ ‖z‖ →
      twoPointFunction M.kernel M.kernel_nonneg M.betaCrit 0 z ≤
        ENNReal.ofReal
          (case3SrcConst M.d C M.S * ‖z‖ ^ (-(M.d : ℝ) + 2) * (Real.log ‖z‖)⁻¹)) :
    Tendsto (fun r => M.nablaTail r) atTop (𝓝 0) := by
  have hof : Tendsto (fun r : ℝ =>
      ENNReal.ofReal (Analysis.logMajorant (case3SrcOutConst M.d C M.S) 2 r)) atTop (𝓝 0) := by
    have h := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp
      (Analysis.tendsto_logMajorant_zero (C := case3SrcOutConst M.d C M.S) (p := 2)
        (by norm_num : (0 : ℝ) < 2))
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hof
    (Eventually.of_forall fun r => zero_le) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr
  exact nablaTail_le_logMajorant_case3 M hd6 hC hHDsup (by linarith)

/-- **Lemma I.4.3, Case 3, at the configured model, from the printed (unshifted-log) HD(3).**

`M : SourceModelData` with `M.d = 6`, `C > 0`, and the *literal printed* domination
`τ_{β_c}(x,y) ≤ C (log ‖x-y‖_S)^(-1) ‖x-y‖_S^(-d+2)` at every `x ≠ y`.  Then the source
open-triangle tail is a logarithmically integrable error function:
`∫^∞ ∇_r dr / r < ∞` and `∇_r → 0`, where `∇_r = M.nablaTail r` is built from the literal uncut
`TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 ·`.

The `α = 2` conjunct of the third disjunct is *not* used here: the open-triangle tail statement
only needs `d = 6`.  No `log (1 + ρ)` is substituted for `log ρ`; the transfer of the hypothesis to
the sup norm is `HD3_to_supNorm`, which spends the explicit constant `case3SrcConst M.d C M.S`. -/
theorem isLogErrorFunction_nablaTail_of_HD3 (M : SourceModelData) (hd6 : M.d = 6)
    {C : ℝ} (hC : 0 < C)
    (hHD : ∀ x y : M.V, x ≠ y →
      M.twoPoint M.betaCrit x y ≤ C * (Real.log (M.S.ρ (toVec (x - y))))⁻¹ *
        (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2)) :
    Analysis.IsLogErrorFunction (fun r => (M.nablaTail r).toReal) := by
  have hd2 : 2 < M.d := by omega
  have hHDsup : ∀ z : M.V, 2 ≤ ‖z‖ →
      twoPointFunction M.kernel M.kernel_nonneg M.betaCrit 0 z ≤
        ENNReal.ofReal
          (case3SrcConst M.d C M.S * ‖z‖ ^ (-(M.d : ℝ) + 2) * (Real.log ‖z‖)⁻¹) :=
    fun z hz => HD3_to_supNorm hd2 hC hHD hz
  refine M.isLogErrorFunction_nablaTail_of_toReal_le
    (C := case3SrcOutConst M.d C M.S) (p := 2) (case3SrcOutConst_nonneg M.d C M.S)
    (by norm_num : (1 : ℝ) < 2) ?_ ?_
  · intro y hy
    exact openTriangle_toReal_le_logMajorant_case3 M hd6 hC (β := M.betaCrit) hHDsup hy
  · intro y _
    exact openTriangle_ne_top_case3 M hd6 hC (β := M.betaCrit) hHDsup y

/-- **The third disjunct of `Orchestration.HD`, verbatim, implies Lemma I.4.3 Case 3** at the
configured model.  This is the exact printed-v1 hypothesis (`0 < C`, unshifted `Real.log`, the
normalized source norm `M.S.ρ`) with no repair, no gap assumption and no non-vacuity claim. -/
theorem isLogErrorFunction_nablaTail_of_HD_third_disjunct (M : SourceModelData)
    (h : M.d = 6 ∧ M.α = 2 ∧ ∃ C : ℝ, 0 < C ∧ ∀ x y : M.V, x ≠ y →
      M.twoPoint M.betaCrit x y ≤ C * (Real.log (M.S.ρ (toVec (x - y))))⁻¹ *
        (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2)) :
    Analysis.IsLogErrorFunction (fun r => (M.nablaTail r).toReal) := by
  obtain ⟨hd6, _hα, C, hC, hHD⟩ := h
  exact isLogErrorFunction_nablaTail_of_HD3 M hd6 hC hHD

/-- **The packaged Case 3 bridge under the printed HD(3).**  One statement carrying the four pieces:
the pointwise square-logarithmic bound at the model's own radius (with the explicit constant
`case3SrcOutConst M.d C M.S`), the finiteness of the literal open triangle, the explicit tail
bound at `M.nablaTail`, the `ℝ≥0∞` vanishing of the tail, and the log-error conclusion. -/
theorem case3SrcNormBridge (M : SourceModelData) (hd6 : M.d = 6) {C : ℝ} (hC : 0 < C)
    (hHD : ∀ x y : M.V, x ≠ y →
      M.twoPoint M.betaCrit x y ≤ C * (Real.log (M.S.ρ (toVec (x - y))))⁻¹ *
        (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2)) :
    (∀ y : M.V, y ≠ 0 →
        (TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y).toReal ≤
          Analysis.logMajorant (case3SrcOutConst M.d C M.S) 2 (M.S.dist 0 y)) ∧
      (∀ y : M.V, TriTail.openTriangle M.kernel M.kernel_nonneg M.betaCrit 0 y ≠ ⊤) ∧
      (∀ r : ℝ, 0 < r → M.nablaTail r ≤
        ENNReal.ofReal (Analysis.logMajorant (case3SrcOutConst M.d C M.S) 2 r)) ∧
      Tendsto (fun r => M.nablaTail r) atTop (𝓝 0) ∧
      Analysis.IsLogErrorFunction (fun r => (M.nablaTail r).toReal) := by
  have hd2 : 2 < M.d := by omega
  have hHDsup : ∀ z : M.V, 2 ≤ ‖z‖ →
      twoPointFunction M.kernel M.kernel_nonneg M.betaCrit 0 z ≤
        ENNReal.ofReal
          (case3SrcConst M.d C M.S * ‖z‖ ^ (-(M.d : ℝ) + 2) * (Real.log ‖z‖)⁻¹) :=
    fun z hz => HD3_to_supNorm hd2 hC hHD hz
  exact ⟨fun y hy => openTriangle_toReal_le_logMajorant_case3 M hd6 hC (β := M.betaCrit) hHDsup hy,
    fun y => openTriangle_ne_top_case3 M hd6 hC (β := M.betaCrit) hHDsup y,
    fun r hr => nablaTail_le_logMajorant_case3 M hd6 hC hHDsup hr,
    tendsto_nablaTail_zero_of_HD3 M hd6 hC hHDsup,
    isLogErrorFunction_nablaTail_of_HD3 M hd6 hC hHD⟩

/-- **The Case 3 hypothesis used above is literally the third disjunct of `Orchestration.HD`.**

The proof term is `Or.inr (Or.inr h)`: this elaborates only if the displayed hypothesis is
syntactically the third disjunct of `HD M`, so it is a checked identification, not a paraphrase. -/
theorem HD_of_HD3 (M : SourceModelData)
    (h : M.d = 6 ∧ M.α = 2 ∧ ∃ C : ℝ, 0 < C ∧ ∀ x y : M.V, x ≠ y →
      M.twoPoint M.betaCrit x y ≤ C * (Real.log (M.S.ρ (toVec (x - y))))⁻¹ *
        (M.S.ρ (toVec (x - y))) ^ (-(M.d : ℝ) + 2)) : HD M :=
  Or.inr (Or.inr h)

end PercLib.CriticalLRP.Orchestration

/-! ## §7 Axiom audit

Every declaration of this packet is expected to use only `propext`, `Classical.choice`, and
`Quot.sound`.
-/
#print axioms PercLib.CriticalLRP.Orchestration.case3SrcThreshold
#print axioms PercLib.CriticalLRP.Orchestration.case3SrcConst
#print axioms PercLib.CriticalLRP.Orchestration.two_le_case3SrcThreshold
#print axioms PercLib.CriticalLRP.Orchestration.one_lt_case3SrcThreshold
#print axioms PercLib.CriticalLRP.Orchestration.case3SrcThreshold_pos
#print axioms PercLib.CriticalLRP.Orchestration.log_four_pos
#print axioms PercLib.CriticalLRP.Orchestration.log_case3SrcThreshold_pos
#print axioms PercLib.CriticalLRP.Orchestration.four_le_srcLowerUnit_mul_threshold
#print axioms PercLib.CriticalLRP.Orchestration.one_lt_srcLowerUnit_mul_threshold
#print axioms PercLib.CriticalLRP.Orchestration.log_srcLowerUnit_mul_threshold_pos
#print axioms PercLib.CriticalLRP.Orchestration.case3SrcConst_pos
#print axioms PercLib.CriticalLRP.Orchestration.le_case3SrcConst_of_le_left
#print axioms PercLib.CriticalLRP.Orchestration.le_case3SrcConst_of_le_right
#print axioms PercLib.CriticalLRP.Orchestration.log_div_log_le_one_add
#print axioms PercLib.CriticalLRP.Orchestration.inv_log_le_const_mul_inv_log
#print axioms PercLib.CriticalLRP.Orchestration.toVec_ne_zero
#print axioms PercLib.CriticalLRP.Orchestration.rho_toVec_zero_sub
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.twoPoint_nonneg
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.twoPoint_eq_litT
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.twoPoint_zero_le_one
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.one_le_srcNorm_of_HD3
#print axioms PercLib.CriticalLRP.Orchestration.SourceModelData.twoPoint_eq_zero_of_srcNorm_one
#print axioms PercLib.CriticalLRP.Orchestration.HD3_to_supNorm
#print axioms PercLib.CriticalLRP.Orchestration.case3SrcOutConst
#print axioms PercLib.CriticalLRP.Orchestration.srcLogConstUpper_pos
#print axioms PercLib.CriticalLRP.Orchestration.case3SrcOutConst_nonneg
#print axioms PercLib.CriticalLRP.Orchestration.rpow_neg_two_le_of_le_mul
#print axioms PercLib.CriticalLRP.Orchestration.log_one_add_sdist_le
#print axioms PercLib.CriticalLRP.Orchestration.one_le_norm_of_ne_zero_gen
#print axioms PercLib.CriticalLRP.Orchestration.openTriangle_toReal_le_logMajorant_case3
#print axioms PercLib.CriticalLRP.Orchestration.openTriangle_ne_top_case3
#print axioms PercLib.CriticalLRP.Orchestration.nablaTail_le_logMajorant_case3
#print axioms PercLib.CriticalLRP.Orchestration.tendsto_nablaTail_zero_of_HD3
#print axioms PercLib.CriticalLRP.Orchestration.isLogErrorFunction_nablaTail_of_HD3
#print axioms PercLib.CriticalLRP.Orchestration.isLogErrorFunction_nablaTail_of_HD_third_disjunct
#print axioms PercLib.CriticalLRP.Orchestration.case3SrcNormBridge
#print axioms PercLib.CriticalLRP.Orchestration.HD_of_HD3
