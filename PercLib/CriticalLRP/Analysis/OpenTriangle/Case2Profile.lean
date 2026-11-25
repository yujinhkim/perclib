/-
Case 2 open-triangle development: profile conversion and the first convolution.
-/
module

public import PercLib.CriticalLRP.Analysis.LatticeConvolution.ConvAssembly.Main
public import PercLib.CriticalLRP.Analysis.LatticeConvolution.SrcNormConv.Transfer

/-!
# The first Case 2 convolution

This file handles only the real-valued profile step.  It does not identify an open triangle.
-/

set_option autoImplicit false
set_option linter.hashCommand false

@[expose] public section

namespace PercLib.CriticalLRP.Orchestration.HD

open CriticalLRPConv

variable {d : ℕ}

/-- The declared Case 2 two-point domination, at a real-valued nonnegative radial input with
value one at zero, implies domination by the generic `Wt (d - 2) 0` kernel.  The explicit
`C ≥ 1` covers the excluded origin in the source hypothesis, and `d > 2` fixes the sign. -/
theorem abs_le_conv_wt_of_case2 (hd : 2 < d) {t : (Fin d → ℤ) → ℝ} {C : ℝ} (hC : 1 ≤ C)
    (htnn : ∀ x, 0 ≤ t x) (ht0 : t 0 = 1)
    (ht : ∀ x ≠ 0, t x ≤ C * ‖x‖ ^ (-(d : ℝ) + 2)) (x : Fin d → ℤ) :
    |t x| ≤ (C * (2 : ℝ) ^ ((d : ℝ) - 2)) * Wt ((d : ℝ) - 2) 0 ‖x‖ := by
  rw [abs_of_nonneg (htnn x)]
  have hd2 : (2 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hexp : 0 ≤ (d : ℝ) - 2 := by linarith
  by_cases hx : x = 0
  · subst x
    have hfac : 1 ≤ (2 : ℝ) ^ ((d : ℝ) - 2) := Real.one_le_rpow (by norm_num) hexp
    have hC0 : 0 ≤ C := by linarith
    have hscaled : 1 ≤ C * (2 : ℝ) ^ ((d : ℝ) - 2) := by
      calc 1 = 1 * 1 := by ring
        _ ≤ C * (2 : ℝ) ^ ((d : ℝ) - 2) := mul_le_mul hC hfac (by positivity) hC0
    simpa [ht0, Wt, LamR_def] using hscaled
  · have hC0 : 0 ≤ C := by linarith
    have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hone : (1 : ℕ) ≤ FiniteVolume.linfNorm x :=
      Nat.one_le_iff_ne_zero.mpr (fun h => hx (FiniteVolume.linfNorm_eq_zero_iff.mp h))
    have honeR : (1 : ℝ) ≤ ‖x‖ := by
      rw [CriticalLRPConv.coe_norm_eq_linfNorm]
      exact_mod_cast hone
    have htwo : 1 + ‖x‖ ≤ 2 * ‖x‖ := by linarith
    have hpow : (2 * ‖x‖) ^ (-((d : ℝ) - 2)) ≤ (1 + ‖x‖) ^ (-((d : ℝ) - 2)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) htwo (by linarith)
    have hmul : (2 * ‖x‖) ^ (-((d : ℝ) - 2))
        = (2 : ℝ) ^ (-((d : ℝ) - 2)) * ‖x‖ ^ (-((d : ℝ) - 2)) :=
      Real.mul_rpow (by norm_num) (norm_nonneg x)
    have hfac : (0 : ℝ) < (2 : ℝ) ^ ((d : ℝ) - 2) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hcancel : (2 : ℝ) ^ (-((d : ℝ) - 2)) * (2 : ℝ) ^ ((d : ℝ) - 2) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      simp
    have hraw : ‖x‖ ^ (-((d : ℝ) - 2)) ≤
        (2 : ℝ) ^ ((d : ℝ) - 2) * (1 + ‖x‖) ^ (-((d : ℝ) - 2)) := by
      calc ‖x‖ ^ (-((d : ℝ) - 2)) = 1 * ‖x‖ ^ (-((d : ℝ) - 2)) := (one_mul _).symm
        _ = ((2 : ℝ) ^ (-((d : ℝ) - 2)) * (2 : ℝ) ^ ((d : ℝ) - 2)) *
            ‖x‖ ^ (-((d : ℝ) - 2)) := by rw [hcancel]
        _ = (2 : ℝ) ^ ((d : ℝ) - 2) * ((2 : ℝ) ^ (-((d : ℝ) - 2)) *
            ‖x‖ ^ (-((d : ℝ) - 2))) := by ring
        _ ≤ (2 : ℝ) ^ ((d : ℝ) - 2) * (1 + ‖x‖) ^ (-((d : ℝ) - 2)) :=
          mul_le_mul_of_nonneg_left (by rw [← hmul]; exact hpow) hfac.le
    calc
      t x ≤ C * ‖x‖ ^ (-(d : ℝ) + 2) := ht x hx
      _ = C * ‖x‖ ^ (-((d : ℝ) - 2)) := by congr 3; ring
      _ ≤ C * ((2 : ℝ) ^ ((d : ℝ) - 2) * (1 + ‖x‖) ^ (-((d : ℝ) - 2))) :=
        mul_le_mul_of_nonneg_left hraw hC0
      _ = (C * (2 : ℝ) ^ ((d : ℝ) - 2)) * Wt ((d : ℝ) - 2) 0 ‖x‖ := by
        rw [Wt_zero_log]
        ring

/-- One application of the strict convolution assembly at `a = b = 2` and zero logarithmic
exponents.  The input requires `d > 6`, although the first convolution needs only `d > 4`.
Summability is returned, and the absolute-value conclusion is simplified using nonnegativity. -/
theorem convolution_two_case2 {t : (Fin d → ℤ) → ℝ} {C : ℝ} (hd : 6 < d)
    (hC : 1 ≤ C) (htnn : ∀ x, 0 ≤ t x) (ht0 : t 0 = 1)
    (ht : ∀ x ≠ 0, t x ≤ C * ‖x‖ ^ (-(d : ℝ) + 2)) (x : Fin d → ℤ) :
    Summable (fun y => t y * t (x - y)) ∧
      0 ≤ ∑' y, t y * t (x - y) ∧
      |∑' y, t y * t (x - y)| ≤
        (C * (2 : ℝ) ^ ((d : ℝ) - 2)) * (C * (2 : ℝ) ^ ((d : ℝ) - 2)) *
          (convConst d 2 2 0 0 * Wt ((d : ℝ) - 4) 0 ‖x‖) := by
  have hd4 : (2 : ℝ) + 2 < (d : ℝ) := by exact_mod_cast (show 4 < d by omega)
  have hmain := CriticalLRPConv.conv_tsum_le (d := d) (show 1 ≤ d by omega)
    (show 0 < (2 : ℝ) by norm_num) (show 0 < (2 : ℝ) by norm_num) hd4
    (show 0 ≤ (0 : ℝ) by norm_num) (show 0 ≤ (0 : ℝ) by norm_num)
    (show 0 ≤ C * (2 : ℝ) ^ ((d : ℝ) - 2) by positivity)
    (show 0 ≤ C * (2 : ℝ) ^ ((d : ℝ) - 2) by positivity)
    (abs_le_conv_wt_of_case2 (by omega) hC htnn ht0 ht)
    (abs_le_conv_wt_of_case2 (by omega) hC htnn ht0 ht) x
  refine ⟨hmain.1, tsum_nonneg (fun y => mul_nonneg (htnn _) (htnn _)), ?_⟩
  simpa only [CriticalLRPConv.convTarget, CriticalLRPConv.convTargetR, zero_add,
    show ((d : ℝ) - 2 - 2) = (d : ℝ) - 4 by ring] using hmain.2

/-- The second application yields the threefold Case 2 profile.  This is a statement about an
abstract real radial input and its double convolution, not yet an identification with `nabla`. -/
theorem triple_convolution_case2 {t : (Fin d → ℤ) → ℝ} {C : ℝ} (hd : 6 < d)
    (hC : 1 ≤ C) (htnn : ∀ x, 0 ≤ t x) (ht0 : t 0 = 1)
    (ht : ∀ x ≠ 0, t x ≤ C * ‖x‖ ^ (-(d : ℝ) + 2)) (x : Fin d → ℤ) :
    Summable (fun y => (∑' a, t a * t (y - a)) * t (x - y)) ∧
      |∑' y, (∑' a, t a * t (y - a)) * t (x - y)| ≤
        ((C * (2 : ℝ) ^ ((d : ℝ) - 2)) * (C * (2 : ℝ) ^ ((d : ℝ) - 2)) *
          convConst d 2 2 0 0) * (C * (2 : ℝ) ^ ((d : ℝ) - 2)) *
          (convConst d 4 2 0 0 * Wt ((d : ℝ) - 6) 0 ‖x‖) := by
  have hd4 : (2 : ℝ) + 2 < (d : ℝ) := by exact_mod_cast (show 4 < d by omega)
  have hCc : 0 ≤ CriticalLRPConv.convConst d 2 2 0 0 :=
    SrcNormConv.convConst_nonneg (show 1 ≤ d by omega)
      (show 0 < (2 : ℝ) by norm_num) (show 0 < (2 : ℝ) by norm_num) hd4
      (show 0 ≤ (0 : ℝ) by norm_num) (show 0 ≤ (0 : ℝ) by norm_num)
  have hfactor : 0 ≤ (C * (2 : ℝ) ^ ((d : ℝ) - 2)) *
      (C * (2 : ℝ) ^ ((d : ℝ) - 2)) * CriticalLRPConv.convConst d 2 2 0 0 :=
    mul_nonneg (by positivity) hCc
  have hinner : ∀ z : (Fin d → ℤ),
      |∑' a, t a * t (z - a)| ≤
        ((C * (2 : ℝ) ^ ((d : ℝ) - 2)) * (C * (2 : ℝ) ^ ((d : ℝ) - 2)) *
          CriticalLRPConv.convConst d 2 2 0 0) * Wt ((d : ℝ) - 4) 0 ‖z‖ := by
    intro z
    simpa only [mul_assoc] using (convolution_two_case2 hd hC htnn ht0 ht z).2.2
  have hd6 : (4 : ℝ) + 2 < (d : ℝ) := by exact_mod_cast hd
  have hmain := CriticalLRPConv.conv_tsum_le (d := d) (show 1 ≤ d by omega)
    (show 0 < (4 : ℝ) by norm_num) (show 0 < (2 : ℝ) by norm_num) hd6
    (show 0 ≤ (0 : ℝ) by norm_num) (show 0 ≤ (0 : ℝ) by norm_num)
    hfactor (show 0 ≤ C * (2 : ℝ) ^ ((d : ℝ) - 2) by positivity)
    hinner (abs_le_conv_wt_of_case2 (by omega) hC htnn ht0 ht) x
  simpa only [CriticalLRPConv.convTarget, CriticalLRPConv.convTargetR, zero_add,
    show ((d : ℝ) - 4 - 2) = (d : ℝ) - 6 by ring, mul_assoc] using hmain

#print axioms PercLib.CriticalLRP.Orchestration.HD.abs_le_conv_wt_of_case2
#print axioms PercLib.CriticalLRP.Orchestration.HD.convolution_two_case2
#print axioms PercLib.CriticalLRP.Orchestration.HD.triple_convolution_case2

end HD

end Orchestration

end CriticalLRP

end PercLib
