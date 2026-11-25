/-
Direction B: the log-corrected Case 3 threefold convolution profile at `d = 6`.

Proofs only.  The constants live in `Case3Profile.Defs`; this file proves the profile
conversions, the two convolutions, their companions and the non-vacuity witness.

Source shape of the Case 3 HD input (PDF p. 9, as recorded in
`docs/CRITICAL_LRP_HD_CONVOLUTION_PLAN.md`): `d = 6`, `α = 2` and

  `P_βc(x ↔ y) ≼ (log ‖x-y‖)^(-1) ‖x-y‖^(-d+2)`   for `x ≠ y`.

Profile level only: an abstract real nonnegative `t` (either normalised by `t 0 = 1` or
bounded by `1`) and the displayed domination away from the origin.  No percolation two-point input,
no literal `TriTail.openTriangle` identification, and no Proposition I.4.2 / Lemma I.4.3 claim.
-/
module

public import PercLib.CriticalLRP.Analysis.OpenTriangle.Case3Profile.Defs
public import PercLib.CriticalLRP.Analysis.LatticeConvolution.ConvAssembly.PaperForm
public import PercLib.CriticalLRP.Analysis.LatticeConvolution.MargConv.Main
public import PercLib.CriticalLRP.Analysis.LatticeConvolution.SrcNormConv.Transfer

/-!
# The Case 3 logarithmic threefold convolution profile (`d = 6`)

The source takes the strict convolution first, `t * t ≼ ⟨x⟩^(-d+4) (log⟨x⟩)^(-2)`, and then
the marginal convolution with `a = 4`, `b = 2`, `â = 2`, `b̂ = 1` in dimension `d = 6`.  The
marginal exponent is `â + b̂ = 3 > 1`, so the `c ↦ c - 1` loss of the critical step leaves
`(log⟨x⟩)^(-2)`, not `(log⟨x⟩)^(-1)` and not `(log⟨x⟩)^(-3)`.

Everything below is stated for an abstract real-valued `t`; summability of every displayed
series is returned as part of the conclusions.
-/

set_option autoImplicit false
set_option linter.hashCommand false
set_option linter.deprecated false

@[expose] public section

namespace PercLib.CriticalLRP.Orchestration.HD.Case3

open CriticalLRPConv
open PercLib.CriticalLRP.FiniteVolume (linfNorm)

variable {d : ℕ}

/-! ## §1 Nonnegativity of the conversion constants (defined in `Case3Profile.Defs`) -/


lemma case3LamConst_nonneg {C : ℝ} (hC : 0 ≤ C) : 0 ≤ case3LamConst d C := by
  unfold case3LamConst
  have : (0 : ℝ) ≤ (2 : ℝ) ^ ((d : ℝ) - 2) := Real.rpow_nonneg (by norm_num) _
  positivity

lemma case3LogConst_nonneg {C : ℝ} (hC : 0 ≤ C) : 0 ≤ case3LogConst d C := by
  unfold case3LogConst
  have : (0 : ℝ) ≤ (2 : ℝ) ^ ((d : ℝ) - 2) := Real.rpow_nonneg (by norm_num) _
  positivity

lemma case3Conv2Const_nonneg {d : ℕ} (hd : 4 < d) {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ case3Conv2Const d C := by
  unfold case3Conv2Const
  have h4 : (2 : ℝ) + 2 < (d : ℝ) := by exact_mod_cast hd
  exact mul_nonneg (mul_nonneg (case3LogConst_nonneg hC) (case3LogConst_nonneg hC))
    (SrcNormConv.convConst_nonneg (by omega) (by norm_num) (by norm_num) h4
      (by norm_num) (by norm_num))

lemma case3Conv3Const_nonneg {C : ℝ} (hC : 0 ≤ C) : 0 ≤ case3Conv3Const C := by
  unfold case3Conv3Const
  exact mul_nonneg (mul_nonneg (case3Conv2Const_nonneg (by norm_num) hC)
    (case3LogConst_nonneg hC))
    (margConst_nonneg (d := 6) (a := 4) (b := 2) (ah := 2) (bh := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num))

/-! ## §2 Profile conversions: the raw Case 3 input versus the frozen `Wt` profile -/

/-- **The power loss of the shift `‖x‖ ↦ 1 + ‖x‖`.**  A nonzero lattice point has `‖x‖ ≥ 1`,
so `1 + ‖x‖ ≤ 2‖x‖` and hence `‖x‖ ^ (-e) ≤ 2^e (1 + ‖x‖) ^ (-e)` for `e ≥ 0`.  This is the
`2^(d-2)` of the Case 2 conversion, kept separate here so that the logarithmic loss can be
recorded independently. -/
lemma norm_rpow_neg_le_const_mul {e : ℝ} (he : 0 ≤ e) {x : Fin d → ℤ} (hx : x ≠ 0) :
    ‖x‖ ^ (-e) ≤ (2 : ℝ) ^ e * (1 + ‖x‖) ^ (-e) := by
  have hnormpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hone : (1 : ℕ) ≤ linfNorm x :=
    Nat.one_le_iff_ne_zero.mpr (fun h => hx (FiniteVolume.linfNorm_eq_zero_iff.mp h))
  have honeR : (1 : ℝ) ≤ ‖x‖ := by
    rw [CriticalLRPConv.coe_norm_eq_linfNorm]
    exact_mod_cast hone
  have htwo : 1 + ‖x‖ ≤ 2 * ‖x‖ := by linarith
  have hpow : (2 * ‖x‖) ^ (-e) ≤ (1 + ‖x‖) ^ (-e) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) htwo (by linarith)
  have hmul : (2 * ‖x‖) ^ (-e) = (2 : ℝ) ^ (-e) * ‖x‖ ^ (-e) :=
    Real.mul_rpow (by norm_num) (norm_nonneg x)
  have hcancel : (2 : ℝ) ^ (-e) * (2 : ℝ) ^ e = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    simp
  have hfac : (0 : ℝ) < (2 : ℝ) ^ e := Real.rpow_pos_of_pos (by norm_num) _
  calc ‖x‖ ^ (-e) = 1 * ‖x‖ ^ (-e) := (one_mul _).symm
    _ = ((2 : ℝ) ^ (-e) * (2 : ℝ) ^ e) * ‖x‖ ^ (-e) := by rw [hcancel]
    _ = (2 : ℝ) ^ e * ((2 : ℝ) ^ (-e) * ‖x‖ ^ (-e)) := by ring
    _ ≤ (2 : ℝ) ^ e * (1 + ‖x‖) ^ (-e) := by
        refine mul_le_mul_of_nonneg_left ?_ hfac.le
        rw [← hmul]
        exact hpow

/-- **The logarithmic loss of the literal reading.**  For a lattice point of sup norm `≥ 2`,
`log (2 + ‖x‖) ≤ 3 log ‖x‖`.  Writing `r = ‖x‖`: `log (2+r) ≤ log (4r) = log 4 + log r`
and `log 4 = 2 log 2 ≤ 2 log r`, so the total factor is `3`.  Only the radius `‖x‖ = 1` is
left out, and there the source factor `(log ‖x‖)^(-1)` is `0` in Lean's real logarithm
convention. -/
lemma log_inv_le_three_mul_LamR_inv {x : Fin d → ℤ} (hx : 2 ≤ ‖x‖) :
    (Real.log ‖x‖)⁻¹ ≤ 3 * (LamR ‖x‖)⁻¹ := by
  have hr : (0 : ℝ) < ‖x‖ := by linarith
  have hr1 : (1 : ℝ) < ‖x‖ := by linarith
  have hlr : 0 < Real.log ‖x‖ := Real.log_pos hr1
  have h2r : (0 : ℝ) < 2 + ‖x‖ := by linarith
  have hLpos : 0 < LamR ‖x‖ := LamR_pos (by linarith)
  have hmono : Real.log (2 + ‖x‖) ≤ Real.log (4 * ‖x‖) :=
    Real.log_le_log h2r (by linarith)
  have hsplit : Real.log (4 * ‖x‖) = Real.log 4 + Real.log ‖x‖ :=
    Real.log_mul (by norm_num) (ne_of_gt hr)
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    ring
  have hlog2 : Real.log 2 ≤ Real.log ‖x‖ := Real.log_le_log (by norm_num) (by linarith)
  have hle : LamR ‖x‖ ≤ 3 * Real.log ‖x‖ := by
    have hA : Real.log (2 + ‖x‖) ≤ Real.log 4 + Real.log ‖x‖ := by
      rw [← hsplit]
      exact hmono
    have hB : Real.log 4 + Real.log ‖x‖ ≤ 3 * Real.log ‖x‖ := by
      rw [h4]
      linarith
    have hC' : Real.log (2 + ‖x‖) ≤ 3 * Real.log ‖x‖ := le_trans hA hB
    simpa only [LamR] using hC'
  have h1 : (3 * Real.log ‖x‖)⁻¹ ≤ (LamR ‖x‖)⁻¹ := by
    rw [inv_eq_one_div, inv_eq_one_div]
    exact one_div_le_one_div_of_le hLpos hle
  have h2 : (3 * Real.log ‖x‖)⁻¹ = (1 / 3 : ℝ) * (Real.log ‖x‖)⁻¹ := by
    rw [mul_inv, show ((3 : ℝ))⁻¹ = 1 / 3 by norm_num]
  have h3 : (1 / 3 : ℝ) * (Real.log ‖x‖)⁻¹ ≤ (LamR ‖x‖)⁻¹ := h2 ▸ h1
  linarith

/-- **Case 3 profile conversion, frozen logarithm.**  If `t` is real, nonnegative, `t 0 = 1`,
and obeys the Case 3 domination `t x ≤ C ‖x‖^(-d+2) (log⟨x⟩)^(-1)` away from the origin,
then `|t x| ≤ case3LamConst d C · Wt (d-2) 1 ‖x‖`, i.e. `t` is dominated by the frozen
profile `⟨x⟩^(-d+2) (log⟨x⟩)^(-1)`.  This is the input shape of both convolution assemblies. -/
theorem abs_le_conv_wt_of_case3Lam (hd : 2 < d) {t : (Fin d → ℤ) → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (htnn : ∀ x, 0 ≤ t x) (ht0 : t 0 = 1)
    (ht : ∀ x ≠ 0, t x ≤ C * ‖x‖ ^ (-(d : ℝ) + 2) * (LamR ‖x‖)⁻¹) (x : Fin d → ℤ) :
    |t x| ≤ case3LamConst d C * Wt ((d : ℝ) - 2) 1 ‖x‖ := by
  rw [abs_of_nonneg (htnn x)]
  have hK : 0 ≤ case3LamConst d C := case3LamConst_nonneg hC
  have hWt : 0 ≤ Wt ((d : ℝ) - 2) 1 ‖x‖ := Wt_nonneg (norm_nonneg x)
  have hd2 : (0 : ℝ) ≤ (d : ℝ) - 2 := by
    have : (2 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    linarith
  by_cases hx : x = 0
  · subst hx
    have hW0 : Wt ((d : ℝ) - 2) 1 (0 : ℝ) = (Real.log 2)⁻¹ := by
      unfold Wt LamR
      rw [show (1 : ℝ) + 0 = 1 by norm_num, Real.one_rpow, one_mul, Real.rpow_neg_one]
      norm_num
    have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2le : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      linarith
    have hinv : (1 : ℝ) ≤ (Real.log 2)⁻¹ := (one_le_inv₀ hlog2pos).mpr hlog2le
    have hK1 : (1 : ℝ) ≤ case3LamConst d C := by
      have hfac : (0 : ℝ) ≤ C * (2 : ℝ) ^ ((d : ℝ) - 2) :=
        mul_nonneg hC (Real.rpow_nonneg (by norm_num) _)
      unfold case3LamConst
      linarith
    have hfin : (1 : ℝ) ≤ case3LamConst d C * Wt ((d : ℝ) - 2) 1 (0 : ℝ) := by
      rw [hW0]
      calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
        _ ≤ case3LamConst d C * (Real.log 2)⁻¹ :=
            mul_le_mul hK1 hinv (by norm_num) hK
    have hnorm0 : ‖(0 : Fin d → ℤ)‖ = 0 := norm_zero
    simpa [ht0, hnorm0] using hfin
  · have hpow := norm_rpow_neg_le_const_mul (e := (d : ℝ) - 2) hd2 hx
    have hLamInv : (0 : ℝ) ≤ (LamR ‖x‖)⁻¹ :=
      inv_nonneg.mpr (LamR_nonneg (norm_nonneg x))
    have hstep : ‖x‖ ^ (-((d : ℝ) - 2)) * (LamR ‖x‖)⁻¹ ≤
        ((2 : ℝ) ^ ((d : ℝ) - 2) * (1 + ‖x‖) ^ (-((d : ℝ) - 2))) * (LamR ‖x‖)⁻¹ :=
      mul_le_mul_of_nonneg_right hpow hLamInv
    calc t x ≤ C * ‖x‖ ^ (-(d : ℝ) + 2) * (LamR ‖x‖)⁻¹ := ht x hx
      _ = C * (‖x‖ ^ (-((d : ℝ) - 2)) * (LamR ‖x‖)⁻¹) := by
          rw [show (-(d : ℝ) + 2) = -((d : ℝ) - 2) by ring]
          ring
      _ ≤ C * (((2 : ℝ) ^ ((d : ℝ) - 2) * (1 + ‖x‖) ^ (-((d : ℝ) - 2))) *
            (LamR ‖x‖)⁻¹) := mul_le_mul_of_nonneg_left hstep hC
      _ = (C * (2 : ℝ) ^ ((d : ℝ) - 2)) * Wt ((d : ℝ) - 2) 1 ‖x‖ := by
          unfold Wt
          rw [Real.rpow_neg_one]
          ring
      _ ≤ case3LamConst d C * Wt ((d : ℝ) - 2) 1 ‖x‖ := by
          refine mul_le_mul_of_nonneg_right ?_ hWt
          unfold case3LamConst
          linarith

/-- **Case 3 profile conversion, literal logarithm.**  The same conversion starting from the
literal source domination `t x ≤ C ‖x‖^(-d+2) (log ‖x‖)^(-1)`.  Two cases exhaust a nonzero
lattice point: `‖x‖ = 1`, where `(log ‖x‖)^(-1) = 0` and the hypothesis forces `t x ≤ 0`; and
`‖x‖ ≥ 2`, where `log (2 + ‖x‖) ≤ 3 log ‖x‖`.  Hence the extra factor `3` against
`case3LamConst` and nothing else. -/
theorem abs_le_conv_wt_of_case3Raw (hd : 2 < d) {t : (Fin d → ℤ) → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (htnn : ∀ x, 0 ≤ t x) (ht0 : t 0 = 1)
    (ht : ∀ x ≠ 0, t x ≤ C * ‖x‖ ^ (-(d : ℝ) + 2) * (Real.log ‖x‖)⁻¹) (x : Fin d → ℤ) :
    |t x| ≤ case3LogConst d C * Wt ((d : ℝ) - 2) 1 ‖x‖ := by
  rw [abs_of_nonneg (htnn x)]
  have hK : 0 ≤ case3LogConst d C := case3LogConst_nonneg hC
  have hWt : 0 ≤ Wt ((d : ℝ) - 2) 1 ‖x‖ := Wt_nonneg (norm_nonneg x)
  have hd2 : (0 : ℝ) ≤ (d : ℝ) - 2 := by
    have : (2 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    linarith
  by_cases hx : x = 0
  · subst hx
    have hW0 : Wt ((d : ℝ) - 2) 1 (0 : ℝ) = (Real.log 2)⁻¹ := by
      unfold Wt LamR
      rw [show (1 : ℝ) + 0 = 1 by norm_num, Real.one_rpow, one_mul, Real.rpow_neg_one]
      norm_num
    have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have hlog2le : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      linarith
    have hinv : (1 : ℝ) ≤ (Real.log 2)⁻¹ := (one_le_inv₀ hlog2pos).mpr hlog2le
    have hK1 : (1 : ℝ) ≤ case3LogConst d C := by
      have hfac : (0 : ℝ) ≤ C * (3 * (2 : ℝ) ^ ((d : ℝ) - 2)) :=
        mul_nonneg hC (mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _))
      unfold case3LogConst
      linarith
    have hfin : (1 : ℝ) ≤ case3LogConst d C * Wt ((d : ℝ) - 2) 1 (0 : ℝ) := by
      rw [hW0]
      calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
        _ ≤ case3LogConst d C * (Real.log 2)⁻¹ := mul_le_mul hK1 hinv (by norm_num) hK
    have hnorm0 : ‖(0 : Fin d → ℤ)‖ = 0 := norm_zero
    simpa [ht0, hnorm0] using hfin
  · have honeR : (1 : ℝ) ≤ ‖x‖ := by
      have hone : (1 : ℕ) ≤ linfNorm x :=
        Nat.one_le_iff_ne_zero.mpr (fun h => hx (FiniteVolume.linfNorm_eq_zero_iff.mp h))
      rw [CriticalLRPConv.coe_norm_eq_linfNorm]
      exact_mod_cast hone
    have hLamInv : (0 : ℝ) ≤ (LamR ‖x‖)⁻¹ :=
      inv_nonneg.mpr (LamR_nonneg (norm_nonneg x))
    by_cases hsmall : ‖x‖ = 1
    · have hlog1 : Real.log ‖x‖ = 0 := by rw [hsmall, Real.log_one]
      have hzero : t x ≤ 0 := by
        have := ht x hx
        rw [hlog1] at this
        simpa using this
      exact hzero.trans (mul_nonneg hK hWt)
    · have h2 : (2 : ℝ) ≤ ‖x‖ := by
        have hlin1 : (1 : ℕ) ≤ linfNorm x :=
          Nat.one_le_iff_ne_zero.mpr (fun h => hx (FiniteVolume.linfNorm_eq_zero_iff.mp h))
        have hlinne : linfNorm x ≠ 1 := by
          intro h
          apply hsmall
          rw [CriticalLRPConv.coe_norm_eq_linfNorm, h]
          norm_num
        have hlin2 : (2 : ℕ) ≤ linfNorm x := by omega
        rw [CriticalLRPConv.coe_norm_eq_linfNorm]
        exact_mod_cast hlin2
      have hpow := norm_rpow_neg_le_const_mul (e := (d : ℝ) - 2) hd2 hx
      have hlog := log_inv_le_three_mul_LamR_inv h2
      have hlogpos : 0 ≤ (Real.log ‖x‖)⁻¹ := by
        have : (0 : ℝ) < Real.log ‖x‖ := Real.log_pos (by linarith)
        exact inv_nonneg.mpr this.le
      have hstep1 : ‖x‖ ^ (-((d : ℝ) - 2)) * (Real.log ‖x‖)⁻¹ ≤
          ((2 : ℝ) ^ ((d : ℝ) - 2) * (1 + ‖x‖) ^ (-((d : ℝ) - 2))) * (Real.log ‖x‖)⁻¹ :=
        mul_le_mul_of_nonneg_right hpow hlogpos
      have hstep2 : ((2 : ℝ) ^ ((d : ℝ) - 2) * (1 + ‖x‖) ^ (-((d : ℝ) - 2))) *
            (Real.log ‖x‖)⁻¹ ≤
          ((2 : ℝ) ^ ((d : ℝ) - 2) * (1 + ‖x‖) ^ (-((d : ℝ) - 2))) *
            (3 * (LamR ‖x‖)⁻¹) := by
        refine mul_le_mul_of_nonneg_left hlog ?_
        exact mul_nonneg (Real.rpow_pos_of_pos (by norm_num) _).le
          (Real.rpow_pos_of_pos (by linarith [norm_nonneg x]) _).le
      calc t x ≤ C * ‖x‖ ^ (-(d : ℝ) + 2) * (Real.log ‖x‖)⁻¹ := ht x hx
        _ = C * (‖x‖ ^ (-((d : ℝ) - 2)) * (Real.log ‖x‖)⁻¹) := by
            rw [show (-(d : ℝ) + 2) = -((d : ℝ) - 2) by ring]
            ring
        _ ≤ C * (((2 : ℝ) ^ ((d : ℝ) - 2) * (1 + ‖x‖) ^ (-((d : ℝ) - 2))) *
              (Real.log ‖x‖)⁻¹) := mul_le_mul_of_nonneg_left hstep1 hC
        _ ≤ C * (((2 : ℝ) ^ ((d : ℝ) - 2) * (1 + ‖x‖) ^ (-((d : ℝ) - 2))) *
              (3 * (LamR ‖x‖)⁻¹)) := mul_le_mul_of_nonneg_left hstep2 hC
        _ = (C * (3 * (2 : ℝ) ^ ((d : ℝ) - 2))) * Wt ((d : ℝ) - 2) 1 ‖x‖ := by
            unfold Wt
            rw [Real.rpow_neg_one]
            ring
        _ ≤ case3LogConst d C * Wt ((d : ℝ) - 2) 1 ‖x‖ := by
            refine mul_le_mul_of_nonneg_right ?_ hWt
            unfold case3LogConst
            linarith

/-! ## §3 The two convolutions -/

/-- **The first Case 3 convolution (strict regime).**  With `a = b = 2` and `â = b̂ = 1`, one
application of `conv_tsum_le` needs only `a + b = 4 < d` and gives

`|Σ' y, t y * t (x-y)| ≤ K² convConst d 2 2 1 1 · ⟨x⟩^(-(d-4)) (log⟨x⟩)^(-2)`

with `K = case3LogConst d C`.  The logarithmic exponent `2` — not `1` — is what makes the
subsequent marginal step legal, because that step needs `â + b̂ > 1`. -/
theorem convolution_two_case3 {t : (Fin d → ℤ) → ℝ} {C : ℝ} (hd : 4 < d) (hC : 0 ≤ C)
    (htnn : ∀ x, 0 ≤ t x) (ht0 : t 0 = 1)
    (ht : ∀ x ≠ 0, t x ≤ C * ‖x‖ ^ (-(d : ℝ) + 2) * (Real.log ‖x‖)⁻¹) (x : Fin d → ℤ) :
    Summable (fun y => t y * t (x - y)) ∧
      0 ≤ ∑' y, t y * t (x - y) ∧
      |∑' y, t y * t (x - y)| ≤
        case3LogConst d C * case3LogConst d C *
          (convConst d 2 2 1 1 * Wt ((d : ℝ) - 4) 2 ‖x‖) := by
  have hd2 : 2 < d := by omega
  have h4 : (2 : ℝ) + 2 < (d : ℝ) := by exact_mod_cast hd
  have hdom := abs_le_conv_wt_of_case3Raw hd2 hC htnn ht0 ht
  have hmain := CriticalLRPConv.conv_tsum_le (d := d) (show 1 ≤ d by omega)
    (show 0 < (2 : ℝ) by norm_num) (show 0 < (2 : ℝ) by norm_num) h4
    (show 0 ≤ (1 : ℝ) by norm_num) (show 0 ≤ (1 : ℝ) by norm_num)
    (case3LogConst_nonneg hC) (case3LogConst_nonneg hC) hdom hdom x
  refine ⟨hmain.1, tsum_nonneg (fun y => mul_nonneg (htnn _) (htnn _)), ?_⟩
  refine hmain.2.trans (le_of_eq ?_)
  rw [CriticalLRPConv.convTarget, CriticalLRPConv.convTargetR,
    show ((d : ℝ) - 2 - 2) = (d : ℝ) - 4 by ring,
    show (1 + 1 : ℝ) = 2 by norm_num]

/-- **The first Case 3 convolution, frozen logarithm.**  The same statement starting from the
domination in the paper's frozen convention `t x ≤ C ‖x‖^(-d+2) (log⟨x⟩)^(-1)`, with the
smaller conversion constant `case3LamConst d C` (no factor `3`). -/
theorem convolution_two_case3Lam {t : (Fin d → ℤ) → ℝ} {C : ℝ} (hd : 4 < d) (hC : 0 ≤ C)
    (htnn : ∀ x, 0 ≤ t x) (ht0 : t 0 = 1)
    (ht : ∀ x ≠ 0, t x ≤ C * ‖x‖ ^ (-(d : ℝ) + 2) * (LamR ‖x‖)⁻¹) (x : Fin d → ℤ) :
    Summable (fun y => t y * t (x - y)) ∧
      0 ≤ ∑' y, t y * t (x - y) ∧
      |∑' y, t y * t (x - y)| ≤
        case3LamConst d C * case3LamConst d C *
          (convConst d 2 2 1 1 * Wt ((d : ℝ) - 4) 2 ‖x‖) := by
  have hd2 : 2 < d := by omega
  have h4 : (2 : ℝ) + 2 < (d : ℝ) := by exact_mod_cast hd
  have hdom := abs_le_conv_wt_of_case3Lam hd2 hC htnn ht0 ht
  have hmain := CriticalLRPConv.conv_tsum_le (d := d) (show 1 ≤ d by omega)
    (show 0 < (2 : ℝ) by norm_num) (show 0 < (2 : ℝ) by norm_num) h4
    (show 0 ≤ (1 : ℝ) by norm_num) (show 0 ≤ (1 : ℝ) by norm_num)
    (case3LamConst_nonneg hC) (case3LamConst_nonneg hC) hdom hdom x
  refine ⟨hmain.1, tsum_nonneg (fun y => mul_nonneg (htnn _) (htnn _)), ?_⟩
  refine hmain.2.trans (le_of_eq ?_)
  rw [CriticalLRPConv.convTarget, CriticalLRPConv.convTargetR,
    show ((d : ℝ) - 2 - 2) = (d : ℝ) - 4 by ring,
    show (1 + 1 : ℝ) = 2 by norm_num]

/-- `margTarget 2 1` is the frozen profile `Wt 0 2`, i.e. `(log⟨x⟩)^(-2)`. -/
lemma margTarget_two_one {d : ℕ} (x : Fin d → ℤ) : margTarget 2 1 x = Wt 0 2 ‖x‖ := by
  unfold margTarget margTargetR
  rw [show (2 : ℝ) + 1 - 1 = 2 by norm_num]

/-- The frozen `d = 6` Case 3 target written out: `Wt 0 2 ‖x‖ = (log (2 + ‖x‖))^(-2)`. -/
lemma Wt_zero_two_eq {d : ℕ} (x : Fin d → ℤ) :
    Wt 0 2 ‖x‖ = (Real.log (2 + ‖x‖)) ^ (-2 : ℝ) := by
  unfold Wt LamR
  rw [show (1 : ℝ) + ‖x‖ = 1 + ‖x‖ by rfl, neg_zero, Real.rpow_zero, one_mul]

/-- **The Case 3 threefold convolution profile at `d = 6`.**  This is the source's second
(marginal) step: `a = 4`, `b = 2`, `â = 2`, `b̂ = 1`, so `a + b = 6 = d` and `â + b̂ = 3 > 1`.
The critical `c ↦ c - 1` loss turns the input exponent `-(2 + 1)` into the target exponent
`1 - 3 = -2`, i.e. square-logarithmic decay of the threefold convolution:

`|Σ' y, (Σ' a, t a * t (y-a)) * t (x-y)| ≤ K³ convConst 6 2 2 1 1 · margConst 6 4 2 2 1
   · (log⟨x⟩)^(-2)`.

Summability of the outer series is part of the conclusion; the inner series is summable by
`convolution_two_case3`. -/
theorem triple_convolution_case3 {t : (Fin 6 → ℤ) → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (htnn : ∀ x, 0 ≤ t x) (ht0 : t 0 = 1)
    (ht : ∀ x ≠ 0, t x ≤ C * ‖x‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖x‖)⁻¹) (x : Fin 6 → ℤ) :
    Summable (fun y => (∑' a, t a * t (y - a)) * t (x - y)) ∧
      |∑' y, (∑' a, t a * t (y - a)) * t (x - y)| ≤ case3Conv3Const C * Wt 0 2 ‖x‖ := by
  have hinner : ∀ z : Fin 6 → ℤ,
      |∑' a, t a * t (z - a)| ≤ case3Conv2Const 6 C * Wt ((6 : ℝ) - 4) 2 ‖z‖ := by
    intro z
    have h := (convolution_two_case3 (d := 6) (by norm_num) hC htnn ht0 ht z).2.2
    calc |∑' a, t a * t (z - a)|
        ≤ (case3LogConst 6 C * case3LogConst 6 C) *
            (convConst 6 2 2 1 1 * Wt ((6 : ℝ) - 4) 2 ‖z‖) := h
      _ = case3Conv2Const 6 C * Wt ((6 : ℝ) - 4) 2 ‖z‖ := by
          unfold case3Conv2Const
          ring
  have hmain := CriticalLRPConv.conv_tsum_le_marg (d := 6) (by norm_num)
    (a := 4) (b := 2) (ah := 2) (bh := 1)
    (show 0 < (4 : ℝ) by norm_num) (show 0 < (2 : ℝ) by norm_num)
    (show (4 : ℝ) + 2 = ((6 : ℕ) : ℝ) by norm_num)
    (show 0 ≤ (2 : ℝ) by norm_num) (show 0 ≤ (1 : ℝ) by norm_num)
    (show 1 < (2 : ℝ) + 1 by norm_num)
    (case3Conv2Const_nonneg (by norm_num) hC) (case3LogConst_nonneg hC)
    hinner (abs_le_conv_wt_of_case3Raw (d := 6) (by norm_num) hC htnn ht0 ht) x
  refine ⟨hmain.1, ?_⟩
  refine hmain.2.trans (le_of_eq ?_)
  rw [margTarget_two_one]
  unfold case3Conv3Const
  ring

/-! ## §4 The log bookkeeping, the explicit form, and the companion for `d > 6` -/

lemma LamR_ge_one_of_one_le_norm {x : Fin d → ℤ} (hx : (1 : ℝ) ≤ ‖x‖) :
    (1 : ℝ) ≤ LamR ‖x‖ := by
  have h3 : (3 : ℝ) ≤ 2 + ‖x‖ := by linarith
  have hlog : Real.log 3 ≤ Real.log (2 + ‖x‖) := Real.log_le_log (by norm_num) h3
  have h1 : (1 : ℝ) ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith
  exact le_trans h1 (by simpa only [LamR] using hlog)

/-- **The `c ↦ c - 1` bookkeeping is worth a full logarithm.**  A direct marginal step whose
inputs carried only one inverse logarithm each would have `â + b̂ = 1 + 1 = 2` and target
exponent `1 - 2 = -1`.  The strict first convolution delivers `â = 2`, hence `â + b̂ = 3` and a
target exponent `1 - 3 = -2`, which is the sharper profile off the origin. -/
lemma margTarget_two_one_le_one_one {x : Fin d → ℤ} (hx : x ≠ 0) :
    margTarget 2 1 x ≤ margTarget 1 1 x := by
  have honeR : (1 : ℝ) ≤ ‖x‖ := by
    have hone : (1 : ℕ) ≤ linfNorm x :=
      Nat.one_le_iff_ne_zero.mpr (fun h => hx (FiniteVolume.linfNorm_eq_zero_iff.mp h))
    rw [CriticalLRPConv.coe_norm_eq_linfNorm]
    exact_mod_cast hone
  have hL : (1 : ℝ) ≤ Real.log (2 + ‖x‖) := by
    have := LamR_ge_one_of_one_le_norm honeR
    simpa only [LamR] using this
  rw [margTarget_eq_explicit, margTarget_eq_explicit,
    show (1 : ℝ) - (2 + 1) = -2 by norm_num,
    show (1 : ℝ) - (1 + 1) = -1 by norm_num]
  exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)

/-- **The Case 3 threefold convolution profile, explicit logarithm.**  The `d = 6` bound of
`triple_convolution_case3` written with the target `(log (2 + ‖x‖))^(-2)` displayed.  It holds
at every `x`, including `x = 0`, where the profile equals `(log 2)^(-2) > 0`. -/
theorem triple_convolution_case3_log {t : (Fin 6 → ℤ) → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (htnn : ∀ x, 0 ≤ t x) (ht0 : t 0 = 1)
    (ht : ∀ x ≠ 0, t x ≤ C * ‖x‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖x‖)⁻¹) (x : Fin 6 → ℤ) :
    Summable (fun y => (∑' a, t a * t (y - a)) * t (x - y)) ∧
      |∑' y, (∑' a, t a * t (y - a)) * t (x - y)| ≤
        case3Conv3Const C * (Real.log (2 + ‖x‖)) ^ (-2 : ℝ) := by
  obtain ⟨hsum, hb⟩ := triple_convolution_case3 hC htnn ht0 ht x
  exact ⟨hsum, hb.trans (le_of_eq (congrArg (fun r => case3Conv3Const C * r)
    (Wt_zero_two_eq x)))⟩


lemma case3Conv3ConstHigh_nonneg {d : ℕ} (hd : 6 < d) {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ case3Conv3ConstHigh d C := by
  unfold case3Conv3ConstHigh
  have h6 : (4 : ℝ) + 2 < (d : ℝ) := by exact_mod_cast hd
  exact mul_nonneg (mul_nonneg (case3Conv2Const_nonneg (by omega) hC)
    (case3LogConst_nonneg hC))
    (SrcNormConv.convConst_nonneg (by omega) (by norm_num) (by norm_num) h6
      (by norm_num) (by norm_num))

/-- **The Case 3 profile above the critical dimension.**  For `d > 6` the second convolution is
again strict (`a + b = 6 < d`), so the same input yields power decay `⟨x⟩^(-(d-6))` with three
inverse logarithms.  This is the Case 3 counterpart of the `d > 6` Case 2 profile; the `d = 6`
statement above is the genuinely critical one. -/
theorem triple_convolution_case3_highdim {d : ℕ} (hd : 6 < d) {t : (Fin d → ℤ) → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (htnn : ∀ x, 0 ≤ t x) (ht0 : t 0 = 1)
    (ht : ∀ x ≠ 0, t x ≤ C * ‖x‖ ^ (-(d : ℝ) + 2) * (Real.log ‖x‖)⁻¹) (x : Fin d → ℤ) :
    Summable (fun y => (∑' a, t a * t (y - a)) * t (x - y)) ∧
      |∑' y, (∑' a, t a * t (y - a)) * t (x - y)| ≤
        case3Conv3ConstHigh d C * Wt ((d : ℝ) - 6) 3 ‖x‖ := by
  have hinner : ∀ z : Fin d → ℤ,
      |∑' a, t a * t (z - a)| ≤ case3Conv2Const d C * Wt ((d : ℝ) - 4) 2 ‖z‖ := by
    intro z
    have h := (convolution_two_case3 (d := d) (by omega) hC htnn ht0 ht z).2.2
    calc |∑' a, t a * t (z - a)|
        ≤ (case3LogConst d C * case3LogConst d C) *
            (convConst d 2 2 1 1 * Wt ((d : ℝ) - 4) 2 ‖z‖) := h
      _ = case3Conv2Const d C * Wt ((d : ℝ) - 4) 2 ‖z‖ := by
          unfold case3Conv2Const
          ring
  have h6 : (4 : ℝ) + 2 < (d : ℝ) := by exact_mod_cast hd
  have hmain := CriticalLRPConv.conv_tsum_le (d := d) (show 1 ≤ d by omega)
    (a := 4) (b := 2) (ah := 2) (bh := 1)
    (show 0 < (4 : ℝ) by norm_num) (show 0 < (2 : ℝ) by norm_num) h6
    (show 0 ≤ (2 : ℝ) by norm_num) (show 0 ≤ (1 : ℝ) by norm_num)
    (case3Conv2Const_nonneg (by omega) hC) (case3LogConst_nonneg hC)
    hinner (abs_le_conv_wt_of_case3Raw (by omega) hC htnn ht0 ht) x
  refine ⟨hmain.1, ?_⟩
  refine hmain.2.trans (le_of_eq ?_)
  rw [CriticalLRPConv.convTarget, CriticalLRPConv.convTargetR,
    show ((d : ℝ) - 4 - 2) = (d : ℝ) - 6 by ring,
    show (2 + 1 : ℝ) = 3 by norm_num]
  unfold case3Conv3ConstHigh
  ring


lemma case3Conv3ConstLam_nonneg {C : ℝ} (hC : 0 ≤ C) : 0 ≤ case3Conv3ConstLam C := by
  unfold case3Conv3ConstLam case3LamConv2Const
  have h4 : (2 : ℝ) + 2 < ((6 : ℕ) : ℝ) := by norm_num
  have hc : 0 ≤ convConst 6 2 2 1 1 :=
    SrcNormConv.convConst_nonneg (by norm_num) (by norm_num) (by norm_num) h4
      (by norm_num) (by norm_num)
  have hK := case3LamConst_nonneg (d := 6) hC
  have hm : 0 ≤ margConst 6 4 2 2 1 :=
    margConst_nonneg (d := 6) (a := 4) (b := 2) (ah := 2) (bh := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hK hK) hc) hK) hm

/-- **The Case 3 threefold profile at `d = 6`, frozen logarithm.**  The same end-to-end chain
started from the domination `t x ≤ C ‖x‖^(-d+2) (log⟨x⟩)^(-1)`, with the smaller conversion
constant and the same square-logarithmic target. -/
theorem triple_convolution_case3Lam {t : (Fin 6 → ℤ) → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (htnn : ∀ x, 0 ≤ t x) (ht0 : t 0 = 1)
    (ht : ∀ x ≠ 0, t x ≤ C * ‖x‖ ^ (-(6 : ℝ) + 2) * (LamR ‖x‖)⁻¹) (x : Fin 6 → ℤ) :
    Summable (fun y => (∑' a, t a * t (y - a)) * t (x - y)) ∧
      |∑' y, (∑' a, t a * t (y - a)) * t (x - y)| ≤ case3Conv3ConstLam C * Wt 0 2 ‖x‖ := by
  have hinner : ∀ z : Fin 6 → ℤ,
      |∑' a, t a * t (z - a)| ≤ case3LamConv2Const 6 C * Wt ((6 : ℝ) - 4) 2 ‖z‖ := by
    intro z
    have h := (convolution_two_case3Lam (d := 6) (by norm_num) hC htnn ht0 ht z).2.2
    calc |∑' a, t a * t (z - a)|
        ≤ (case3LamConst 6 C * case3LamConst 6 C) *
            (convConst 6 2 2 1 1 * Wt ((6 : ℝ) - 4) 2 ‖z‖) := h
      _ = case3LamConv2Const 6 C * Wt ((6 : ℝ) - 4) 2 ‖z‖ := by
          unfold case3LamConv2Const
          ring
  have hmain := CriticalLRPConv.conv_tsum_le_marg (d := 6) (by norm_num)
    (a := 4) (b := 2) (ah := 2) (bh := 1)
    (show 0 < (4 : ℝ) by norm_num) (show 0 < (2 : ℝ) by norm_num)
    (show (4 : ℝ) + 2 = ((6 : ℕ) : ℝ) by norm_num)
    (show 0 ≤ (2 : ℝ) by norm_num) (show 0 ≤ (1 : ℝ) by norm_num)
    (show 1 < (2 : ℝ) + 1 by norm_num)
    (by
      unfold case3LamConv2Const
      have h4 : (2 : ℝ) + 2 < ((6 : ℕ) : ℝ) := by norm_num
      exact mul_nonneg (mul_nonneg (case3LamConst_nonneg hC) (case3LamConst_nonneg hC))
        (SrcNormConv.convConst_nonneg (by norm_num) (by norm_num) (by norm_num) h4
          (by norm_num) (by norm_num)))
    (case3LamConst_nonneg hC)
    hinner (abs_le_conv_wt_of_case3Lam (d := 6) (by norm_num) hC htnn ht0 ht) x
  refine ⟨hmain.1, ?_⟩
  refine hmain.2.trans (le_of_eq ?_)
  rw [margTarget_two_one]
  unfold case3Conv3ConstLam
  ring

/-! ## §5 The profile-level interface and the source-shaped (`t ≤ 1`) input -/

/-- **The first convolution from a `Wt` domination alone.**  This is the profile-level form of
`convolution_two_case3`: every input variant below is an instance. -/
theorem convolution_two_of_wt_bound {t : (Fin d → ℤ) → ℝ} {Cf : ℝ} (hd : 4 < d) (hCf : 0 ≤ Cf)
    (hbd : ∀ x, |t x| ≤ Cf * Wt ((d : ℝ) - 2) 1 ‖x‖) (x : Fin d → ℤ) :
    Summable (fun y => t y * t (x - y)) ∧
      |∑' y, t y * t (x - y)| ≤
        Cf * Cf * (convConst d 2 2 1 1 * Wt ((d : ℝ) - 4) 2 ‖x‖) := by
  have h4 : (2 : ℝ) + 2 < (d : ℝ) := by exact_mod_cast hd
  have hmain := CriticalLRPConv.conv_tsum_le (d := d) (show 1 ≤ d by omega)
    (show 0 < (2 : ℝ) by norm_num) (show 0 < (2 : ℝ) by norm_num) h4
    (show 0 ≤ (1 : ℝ) by norm_num) (show 0 ≤ (1 : ℝ) by norm_num) hCf hCf hbd hbd x
  refine ⟨hmain.1, hmain.2.trans (le_of_eq ?_)⟩
  rw [CriticalLRPConv.convTarget, CriticalLRPConv.convTargetR,
    show ((d : ℝ) - 2 - 2) = (d : ℝ) - 4 by ring,
    show (1 + 1 : ℝ) = 2 by norm_num]

/-- **The `d = 6` threefold profile from a `Wt` domination alone.**  The marginal step
(`a = 4`, `b = 2`, `â = 2`, `b̂ = 1`) applied to the output of `convolution_two_of_wt_bound`. -/
theorem triple_convolution_of_wt_bound {t : (Fin 6 → ℤ) → ℝ} {Cf : ℝ} (hCf : 0 ≤ Cf)
    (hbd : ∀ x, |t x| ≤ Cf * Wt ((6 : ℝ) - 2) 1 ‖x‖) (x : Fin 6 → ℤ) :
    Summable (fun y => (∑' a, t a * t (y - a)) * t (x - y)) ∧
      |∑' y, (∑' a, t a * t (y - a)) * t (x - y)| ≤
        Cf * Cf * convConst 6 2 2 1 1 * Cf * (margConst 6 4 2 2 1 * Wt 0 2 ‖x‖) := by
  have hinner : ∀ z : Fin 6 → ℤ,
      |∑' a, t a * t (z - a)| ≤ (Cf * Cf * convConst 6 2 2 1 1) * Wt ((6 : ℝ) - 4) 2 ‖z‖ := by
    intro z
    have h := (convolution_two_of_wt_bound (d := 6) (by norm_num) hCf hbd z).2
    calc |∑' a, t a * t (z - a)|
        ≤ Cf * Cf * (convConst 6 2 2 1 1 * Wt ((6 : ℝ) - 4) 2 ‖z‖) := h
      _ = (Cf * Cf * convConst 6 2 2 1 1) * Wt ((6 : ℝ) - 4) 2 ‖z‖ := by ring
  have h4 : (2 : ℝ) + 2 < ((6 : ℕ) : ℝ) := by norm_num
  have hmain := CriticalLRPConv.conv_tsum_le_marg (d := 6) (by norm_num)
    (a := 4) (b := 2) (ah := 2) (bh := 1)
    (show 0 < (4 : ℝ) by norm_num) (show 0 < (2 : ℝ) by norm_num)
    (show (4 : ℝ) + 2 = ((6 : ℕ) : ℝ) by norm_num)
    (show 0 ≤ (2 : ℝ) by norm_num) (show 0 ≤ (1 : ℝ) by norm_num)
    (show 1 < (2 : ℝ) + 1 by norm_num)
    (mul_nonneg (mul_nonneg hCf hCf)
      (SrcNormConv.convConst_nonneg (by norm_num) (by norm_num) (by norm_num) h4
        (by norm_num) (by norm_num)))
    hCf hinner hbd x
  refine ⟨hmain.1, ?_⟩
  refine hmain.2.trans (le_of_eq ?_)
  rw [margTarget_two_one]


lemma case3ShellConst_nonneg {C : ℝ} (hC : 0 ≤ C) : 0 ≤ case3ShellConst d C := by
  unfold case3ShellConst
  have h1 : (0 : ℝ) ≤ C * (3 * (2 : ℝ) ^ ((d : ℝ) - 2)) :=
    mul_nonneg hC (mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _))
  have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ ((d : ℝ) - 2) * Real.log 3 :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.log_pos (by norm_num)).le
  have h3 : C * (3 * (2 : ℝ) ^ ((d : ℝ) - 2)) ≤
      max (C * (3 * (2 : ℝ) ^ ((d : ℝ) - 2))) ((2 : ℝ) ^ ((d : ℝ) - 2) * Real.log 3) :=
    le_max_left _ _
  linarith

/-- **Case 3 profile conversion for the source-shaped input.**  The hypotheses are the ones an
actual two-point function satisfies: `t` is real, nonnegative, at most one, and obeys the Case 3
decay only for `‖x‖ ≥ 2`.  No value of `t` at the origin is assumed: `t ≤ 1` covers it, together
with `Wt (d-2) 1 0 = (log 2)^(-1) > 1`.  This avoids the accidental strength of the literal
`(log ‖x‖)^(-1)` at the single radius `‖x‖ = 1`.  The price is a constant covering the unit
shell, `2^(d-2) log 3`, absorbed in `case3ShellConst`. -/
theorem abs_le_conv_wt_of_case3Shell (hd : 2 < d) {t : (Fin d → ℤ) → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (htnn : ∀ x, 0 ≤ t x) (hbound : ∀ x, t x ≤ 1)
    (ht : ∀ x, 2 ≤ ‖x‖ → t x ≤ C * ‖x‖ ^ (-(d : ℝ) + 2) * (Real.log ‖x‖)⁻¹)
    (x : Fin d → ℤ) :
    |t x| ≤ case3ShellConst d C * Wt ((d : ℝ) - 2) 1 ‖x‖ := by
  rw [abs_of_nonneg (htnn x)]
  have hK : 0 ≤ case3ShellConst d C := case3ShellConst_nonneg hC
  have hWt : 0 ≤ Wt ((d : ℝ) - 2) 1 ‖x‖ := Wt_nonneg (norm_nonneg x)
  have hd2 : (0 : ℝ) ≤ (d : ℝ) - 2 := by
    have : (2 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    linarith
  have hK1 : (1 : ℝ) ≤ case3ShellConst d C := by
    unfold case3ShellConst
    have h1 : (0 : ℝ) ≤ C * (3 * (2 : ℝ) ^ ((d : ℝ) - 2)) :=
      mul_nonneg hC (mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _))
    have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ ((d : ℝ) - 2) * Real.log 3 :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.log_pos (by norm_num)).le
    have h3 := le_max_left (C * (3 * (2 : ℝ) ^ ((d : ℝ) - 2)))
      ((2 : ℝ) ^ ((d : ℝ) - 2) * Real.log 3)
    linarith
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  rcases eq_or_ne x 0 with hx | hx
  · -- the origin: `t 0 ≤ 1` and `Wt … 0 = (log 2)^(-1) ≥ 1`
    subst hx
    have hW0 : Wt ((d : ℝ) - 2) 1 (0 : ℝ) = (Real.log 2)⁻¹ := by
      unfold Wt LamR
      rw [show (1 : ℝ) + 0 = 1 by norm_num, Real.one_rpow, one_mul, Real.rpow_neg_one]
      norm_num
    have hinv : (1 : ℝ) ≤ (Real.log 2)⁻¹ := (one_le_inv₀ hlog2pos).mpr hlog2le
    have hfin : (1 : ℝ) ≤ case3ShellConst d C * Wt ((d : ℝ) - 2) 1 (0 : ℝ) := by
      rw [hW0]
      calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
        _ ≤ case3ShellConst d C * (Real.log 2)⁻¹ := mul_le_mul hK1 hinv (by norm_num) hK
    have hnorm0 : ‖(0 : Fin d → ℤ)‖ = 0 := norm_zero
    simpa [hnorm0] using (le_trans (hbound 0) hfin)
  · have honeR : (1 : ℝ) ≤ ‖x‖ := by
      have hone : (1 : ℕ) ≤ linfNorm x :=
        Nat.one_le_iff_ne_zero.mpr (fun h => hx (FiniteVolume.linfNorm_eq_zero_iff.mp h))
      rw [CriticalLRPConv.coe_norm_eq_linfNorm]
      exact_mod_cast hone
    by_cases hsmall : ‖x‖ = 1
    · -- the unit shell: `t x ≤ 1` and `Wt (d-2) 1 1 = 2^(-(d-2)) (log 3)^(-1)`
      have hW1 : Wt ((d : ℝ) - 2) 1 (1 : ℝ) =
          (2 : ℝ) ^ (-((d : ℝ) - 2)) * (Real.log 3)⁻¹ := by
        unfold Wt LamR
        rw [show (1 : ℝ) + 1 = 2 by norm_num, show (2 : ℝ) + 1 = 3 by norm_num,
          Real.rpow_neg_one]
      have hK2 : (2 : ℝ) ^ ((d : ℝ) - 2) * Real.log 3 ≤ case3ShellConst d C := by
        unfold case3ShellConst
        have := le_max_right (C * (3 * (2 : ℝ) ^ ((d : ℝ) - 2)))
          ((2 : ℝ) ^ ((d : ℝ) - 2) * Real.log 3)
        linarith
      have hpos1 : (0 : ℝ) < (2 : ℝ) ^ ((d : ℝ) - 2) := Real.rpow_pos_of_pos (by norm_num) _
      have hpos2 : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
      have hpos3 : (0 : ℝ) < (2 : ℝ) ^ (-((d : ℝ) - 2)) :=
        Real.rpow_pos_of_pos (by norm_num) _
      have hlog3 : (0 : ℝ) < (Real.log 3)⁻¹ := inv_pos.mpr hpos2
      have hone : (1 : ℝ) ≤ case3ShellConst d C *
          ((2 : ℝ) ^ (-((d : ℝ) - 2)) * (Real.log 3)⁻¹) := by
        calc (1 : ℝ) ≤ ((2 : ℝ) ^ ((d : ℝ) - 2) * Real.log 3) *
              ((2 : ℝ) ^ (-((d : ℝ) - 2)) * (Real.log 3)⁻¹) := by
              rw [show ((2 : ℝ) ^ ((d : ℝ) - 2) * Real.log 3) *
                    ((2 : ℝ) ^ (-((d : ℝ) - 2)) * (Real.log 3)⁻¹) =
                  ((2 : ℝ) ^ ((d : ℝ) - 2) * (2 : ℝ) ^ (-((d : ℝ) - 2))) *
                    (Real.log 3 * (Real.log 3)⁻¹) by ring]
              rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
                mul_inv_cancel₀ (ne_of_gt hpos2)]
              norm_num
          _ ≤ case3ShellConst d C *
              ((2 : ℝ) ^ (-((d : ℝ) - 2)) * (Real.log 3)⁻¹) := by
              refine mul_le_mul_of_nonneg_right hK2 ?_
              exact mul_nonneg hpos3.le hlog3.le
      have hx1 : t x ≤ 1 := hbound x
      have : t x ≤ case3ShellConst d C * Wt ((d : ℝ) - 2) 1 (1 : ℝ) := by
        rw [hW1]
        exact hx1.trans hone
      simpa [hsmall] using this
    · -- the genuine decay region
      have h2 : (2 : ℝ) ≤ ‖x‖ := by
        have hlin1 : (1 : ℕ) ≤ linfNorm x :=
          Nat.one_le_iff_ne_zero.mpr (fun h => hx (FiniteVolume.linfNorm_eq_zero_iff.mp h))
        have hlinne : linfNorm x ≠ 1 := by
          intro h
          apply hsmall
          rw [CriticalLRPConv.coe_norm_eq_linfNorm, h]
          norm_num
        have hlin2 : (2 : ℕ) ≤ linfNorm x := by omega
        rw [CriticalLRPConv.coe_norm_eq_linfNorm]
        exact_mod_cast hlin2
      have hpow := norm_rpow_neg_le_const_mul (e := (d : ℝ) - 2) hd2 hx
      have hlog := log_inv_le_three_mul_LamR_inv h2
      have hlogpos : 0 ≤ (Real.log ‖x‖)⁻¹ := by
        have : (0 : ℝ) < Real.log ‖x‖ := Real.log_pos (by linarith)
        exact inv_nonneg.mpr this.le
      have hstep1 : ‖x‖ ^ (-((d : ℝ) - 2)) * (Real.log ‖x‖)⁻¹ ≤
          ((2 : ℝ) ^ ((d : ℝ) - 2) * (1 + ‖x‖) ^ (-((d : ℝ) - 2))) *
            (Real.log ‖x‖)⁻¹ :=
        mul_le_mul_of_nonneg_right hpow hlogpos
      have hstep2 : ((2 : ℝ) ^ ((d : ℝ) - 2) * (1 + ‖x‖) ^ (-((d : ℝ) - 2))) *
            (Real.log ‖x‖)⁻¹ ≤
          ((2 : ℝ) ^ ((d : ℝ) - 2) * (1 + ‖x‖) ^ (-((d : ℝ) - 2))) *
            (3 * (LamR ‖x‖)⁻¹) := by
        refine mul_le_mul_of_nonneg_left hlog ?_
        exact mul_nonneg (Real.rpow_pos_of_pos (by norm_num) _).le
          (Real.rpow_pos_of_pos (by linarith [norm_nonneg x]) _).le
      have hKge : C * (3 * (2 : ℝ) ^ ((d : ℝ) - 2)) ≤ case3ShellConst d C := by
        unfold case3ShellConst
        have := le_max_left (C * (3 * (2 : ℝ) ^ ((d : ℝ) - 2)))
          ((2 : ℝ) ^ ((d : ℝ) - 2) * Real.log 3)
        linarith
      calc t x ≤ C * ‖x‖ ^ (-(d : ℝ) + 2) * (Real.log ‖x‖)⁻¹ := ht x h2
        _ = C * (‖x‖ ^ (-((d : ℝ) - 2)) * (Real.log ‖x‖)⁻¹) := by
            rw [show (-(d : ℝ) + 2) = -((d : ℝ) - 2) by ring]
            ring
        _ ≤ C * (((2 : ℝ) ^ ((d : ℝ) - 2) * (1 + ‖x‖) ^ (-((d : ℝ) - 2))) *
              (Real.log ‖x‖)⁻¹) := mul_le_mul_of_nonneg_left hstep1 hC
        _ ≤ C * (((2 : ℝ) ^ ((d : ℝ) - 2) * (1 + ‖x‖) ^ (-((d : ℝ) - 2))) *
              (3 * (LamR ‖x‖)⁻¹)) := mul_le_mul_of_nonneg_left hstep2 hC
        _ = (C * (3 * (2 : ℝ) ^ ((d : ℝ) - 2))) * Wt ((d : ℝ) - 2) 1 ‖x‖ := by
            unfold Wt
            rw [Real.rpow_neg_one]
            ring
        _ ≤ case3ShellConst d C * Wt ((d : ℝ) - 2) 1 ‖x‖ :=
            mul_le_mul_of_nonneg_right hKge hWt


lemma case3Conv3ConstShell_nonneg {C : ℝ} (hC : 0 ≤ C) : 0 ≤ case3Conv3ConstShell C := by
  unfold case3Conv3ConstShell
  have h4 : (2 : ℝ) + 2 < ((6 : ℕ) : ℝ) := by norm_num
  have hK := case3ShellConst_nonneg (d := 6) hC
  have hc : 0 ≤ convConst 6 2 2 1 1 :=
    SrcNormConv.convConst_nonneg (by norm_num) (by norm_num) (by norm_num) h4
      (by norm_num) (by norm_num)
  have hm : 0 ≤ margConst 6 4 2 2 1 :=
    margConst_nonneg (d := 6) (a := 4) (b := 2) (ah := 2) (bh := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hK hK) hc) hK) hm

/-- **The Case 3 threefold profile for the source-shaped input at `d = 6`.**  This is the
end-to-end statement for `t` real, nonnegative, `t ≤ 1`, with the Case 3 decay assumed only for
`‖x‖ ≥ 2`.  No value at the origin is needed: `t ≤ 1` already covers it.  The witness
`case3Shell_hypotheses_inhabited` additionally satisfies the source normalisation `t 0 = 1`. -/
theorem triple_convolution_case3Shell {t : (Fin 6 → ℤ) → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (htnn : ∀ x, 0 ≤ t x) (hbound : ∀ x, t x ≤ 1)
    (ht : ∀ x, 2 ≤ ‖x‖ → t x ≤ C * ‖x‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖x‖)⁻¹)
    (x : Fin 6 → ℤ) :
    Summable (fun y => (∑' a, t a * t (y - a)) * t (x - y)) ∧
      |∑' y, (∑' a, t a * t (y - a)) * t (x - y)| ≤ case3Conv3ConstShell C * Wt 0 2 ‖x‖ := by
  obtain ⟨hsum, hb⟩ := triple_convolution_of_wt_bound (Cf := case3ShellConst 6 C)
    (case3ShellConst_nonneg hC)
    (abs_le_conv_wt_of_case3Shell (d := 6) (by norm_num) hC htnn hbound ht) x
  exact ⟨hsum, hb.trans (le_of_eq (by unfold case3Conv3ConstShell; ring))⟩

/-! ## §6 The hypothesis set is inhabited -/

/-- **A concrete input satisfying the source-shaped Case 3 hypotheses at `d = 6`.**  Taking
`t x = log 2 · Wt 4 1 ‖x‖` off the unit shell and `t x = 0` on it gives a real, nonnegative,
`≤ 1` function with `t 0 = 1` which obeys the literal Case 3 decay for `‖x‖ ≥ 2` with
`C = 1`.  The `t 0 = 1` conjunct is asserted and proved (from `‖0‖ = 0`, `Wt 4 1 0 = (log 2)^(-1)`
and `log 2 · (log 2)^(-1) = 1`), not only obtained in passing.  The forced vanishing on the
unit shell uses Lean's `(log ‖x‖)^(-1)`, which vanishes there. The source-shaped
`t ≤ 1` formulation avoids making this a modelling assumption. This shows the hypothesis set
of the Case 3 theorems is not empty. -/
theorem case3Shell_hypotheses_inhabited :
    ∃ (t : (Fin 6 → ℤ) → ℝ) (C : ℝ), 0 ≤ C ∧ (∀ x, 0 ≤ t x) ∧ (∀ x, t x ≤ 1) ∧
      t 0 = 1 ∧
      ∀ x, 2 ≤ ‖x‖ → t x ≤ C * ‖x‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖x‖)⁻¹ := by
  classical
  refine ⟨fun x => if ‖x‖ = 1 then 0 else Real.log 2 * Wt (4 : ℝ) 1 ‖x‖, 1, by norm_num,
    ?_, ?_, ?_, ?_⟩
  · intro x
    dsimp only
    by_cases h : ‖x‖ = 1
    · simp [h]
    · rw [if_neg h]
      exact mul_nonneg (Real.log_pos (by norm_num)).le (Wt_nonneg (norm_nonneg x))
  · intro x
    dsimp only
    by_cases h : ‖x‖ = 1
    · simp [h]
    · rw [if_neg h]
      have hW0 : Wt (4 : ℝ) 1 (0 : ℝ) = (Real.log 2)⁻¹ := by
        unfold Wt LamR
        rw [show (1 : ℝ) + 0 = 1 by norm_num, Real.one_rpow, one_mul, Real.rpow_neg_one]
        norm_num
      have hle : Wt (4 : ℝ) 1 ‖x‖ ≤ Wt (4 : ℝ) 1 (0 : ℝ) := by
        have hbase : (1 : ℝ) + 0 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
        have hbase0 : (0 : ℝ) < 1 + 0 := by norm_num
        have hpow : (1 + ‖x‖) ^ (-4 : ℝ) ≤ ((1 : ℝ) + 0) ^ (-4 : ℝ) :=
          Real.rpow_le_rpow_of_nonpos hbase0 hbase (by norm_num)
        have hlogle : Real.log (2 + 0) ≤ Real.log (2 + ‖x‖) :=
          Real.log_le_log (by norm_num) (by linarith [norm_nonneg x])
        have hlogpos : (0 : ℝ) < Real.log (2 + 0) := Real.log_pos (by norm_num)
        have hlogpos' : (0 : ℝ) < Real.log (2 + ‖x‖) := by linarith
        have hinv : (Real.log (2 + ‖x‖))⁻¹ ≤ (Real.log (2 + 0))⁻¹ := by
          rw [inv_eq_one_div, inv_eq_one_div]
          exact one_div_le_one_div_of_le hlogpos hlogle
        have h1 : Wt (4 : ℝ) 1 ‖x‖ = (1 + ‖x‖) ^ (-4 : ℝ) * (Real.log (2 + ‖x‖))⁻¹ := by
          unfold Wt LamR
          rw [Real.rpow_neg_one]
        have h2 : Wt (4 : ℝ) 1 (0 : ℝ) = (1 + 0) ^ (-4 : ℝ) * (Real.log (2 + 0))⁻¹ := by
          unfold Wt LamR
          rw [Real.rpow_neg_one]
        rw [h1, h2]
        exact mul_le_mul hpow hinv (inv_nonneg.mpr hlogpos'.le)
          (Real.rpow_nonneg (by positivity) _)
      have hone : Real.log 2 * (Real.log 2)⁻¹ = 1 :=
        mul_inv_cancel₀ (ne_of_gt (Real.log_pos (by norm_num)))
      calc Real.log 2 * Wt (4 : ℝ) 1 ‖x‖ ≤ Real.log 2 * Wt (4 : ℝ) 1 (0 : ℝ) :=
            mul_le_mul_of_nonneg_left hle (Real.log_pos (by norm_num)).le
        _ = 1 := by rw [hW0, hone]
  · -- `t 0 = 1`: the origin is off the unit shell, and `Wt 4 1 0 = (log 2)^(-1)`
    dsimp only
    have hW0 : Wt (4 : ℝ) 1 (0 : ℝ) = (Real.log 2)⁻¹ := by
      unfold Wt LamR
      rw [show (1 : ℝ) + 0 = 1 by norm_num, Real.one_rpow, one_mul, Real.rpow_neg_one]
      norm_num
    have hnorm0 : ‖(0 : Fin 6 → ℤ)‖ = 0 := norm_zero
    rw [hnorm0, if_neg (by norm_num : ¬ ((0 : ℝ) = 1)), hW0]
    exact mul_inv_cancel₀ (ne_of_gt (Real.log_pos (by norm_num)))
  · intro x hx
    dsimp only
    have hr : (0 : ℝ) < ‖x‖ := by linarith
    have hne : ‖x‖ ≠ 1 := by linarith
    have hlr : 0 < Real.log ‖x‖ := Real.log_pos (by linarith)
    have hlog2le : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      linarith
    have hpow : (1 + ‖x‖) ^ (-4 : ℝ) ≤ ‖x‖ ^ (-4 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hr (by linarith) (by norm_num)
    have hlogle : Real.log ‖x‖ ≤ Real.log (2 + ‖x‖) := Real.log_le_log hr (by linarith)
    have hlog2pos : (0 : ℝ) < Real.log (2 + ‖x‖) := by linarith
    have hlog : (Real.log (2 + ‖x‖))⁻¹ ≤ (Real.log ‖x‖)⁻¹ := by
      rw [inv_eq_one_div, inv_eq_one_div]
      exact one_div_le_one_div_of_le hlr hlogle
    have hWt : Wt (4 : ℝ) 1 ‖x‖ ≤ ‖x‖ ^ (-4 : ℝ) * (Real.log ‖x‖)⁻¹ := by
      have h1 : Wt (4 : ℝ) 1 ‖x‖ = (1 + ‖x‖) ^ (-4 : ℝ) * (Real.log (2 + ‖x‖))⁻¹ := by
        unfold Wt LamR
        rw [Real.rpow_neg_one]
      rw [h1]
      exact mul_le_mul hpow hlog (inv_nonneg.mpr hlog2pos.le)
        (Real.rpow_nonneg (by linarith) _)
    have hstep : Real.log 2 * Wt (4 : ℝ) 1 ‖x‖ ≤
        Real.log 2 * (‖x‖ ^ (-4 : ℝ) * (Real.log ‖x‖)⁻¹) :=
      mul_le_mul_of_nonneg_left hWt (Real.log_pos (by norm_num)).le
    have hnonneg : (0 : ℝ) ≤ ‖x‖ ^ (-4 : ℝ) * (Real.log ‖x‖)⁻¹ :=
      mul_nonneg (Real.rpow_nonneg (by linarith) _) (inv_nonneg.mpr hlr.le)
    have hstep2 : Real.log 2 * (‖x‖ ^ (-4 : ℝ) * (Real.log ‖x‖)⁻¹) ≤
        1 * (‖x‖ ^ (-4 : ℝ) * (Real.log ‖x‖)⁻¹) :=
      mul_le_mul_of_nonneg_right hlog2le hnonneg
    rw [if_neg hne]
    calc Real.log 2 * Wt (4 : ℝ) 1 ‖x‖
        ≤ 1 * (‖x‖ ^ (-4 : ℝ) * (Real.log ‖x‖)⁻¹) := le_trans hstep hstep2
      _ = 1 * ‖x‖ ^ (-(6 : ℝ) + 2) * (Real.log ‖x‖)⁻¹ := by
          rw [show (-(6 : ℝ) + 2) = (-4 : ℝ) by norm_num]
          ring

/-! ## Axiom audit -/

set_option linter.hashCommand false

#print axioms PercLib.CriticalLRP.Orchestration.HD.Case3.norm_rpow_neg_le_const_mul
#print axioms PercLib.CriticalLRP.Orchestration.HD.Case3.log_inv_le_three_mul_LamR_inv
#print axioms PercLib.CriticalLRP.Orchestration.HD.Case3.abs_le_conv_wt_of_case3Lam
#print axioms PercLib.CriticalLRP.Orchestration.HD.Case3.abs_le_conv_wt_of_case3Raw
#print axioms PercLib.CriticalLRP.Orchestration.HD.Case3.convolution_two_case3
#print axioms PercLib.CriticalLRP.Orchestration.HD.Case3.convolution_two_case3Lam
#print axioms PercLib.CriticalLRP.Orchestration.HD.Case3.margTarget_two_one
#print axioms PercLib.CriticalLRP.Orchestration.HD.Case3.triple_convolution_case3
#print axioms PercLib.CriticalLRP.Orchestration.HD.Case3.LamR_ge_one_of_one_le_norm
#print axioms PercLib.CriticalLRP.Orchestration.HD.Case3.margTarget_two_one_le_one_one
#print axioms PercLib.CriticalLRP.Orchestration.HD.Case3.triple_convolution_case3_log
#print axioms PercLib.CriticalLRP.Orchestration.HD.Case3.triple_convolution_case3_highdim
#print axioms PercLib.CriticalLRP.Orchestration.HD.Case3.case3Conv3ConstLam_nonneg
#print axioms PercLib.CriticalLRP.Orchestration.HD.Case3.triple_convolution_case3Lam
#print axioms PercLib.CriticalLRP.Orchestration.HD.Case3.abs_le_conv_wt_of_case3Shell
#print axioms PercLib.CriticalLRP.Orchestration.HD.Case3.convolution_two_of_wt_bound
#print axioms PercLib.CriticalLRP.Orchestration.HD.Case3.triple_convolution_of_wt_bound
#print axioms PercLib.CriticalLRP.Orchestration.HD.Case3.case3Conv3ConstShell_nonneg
#print axioms PercLib.CriticalLRP.Orchestration.HD.Case3.triple_convolution_case3Shell
#print axioms PercLib.CriticalLRP.Orchestration.HD.Case3.case3Shell_hypotheses_inhabited

end PercLib.CriticalLRP.Orchestration.HD.Case3
