/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
-/
module

public import PercLib.CriticalLRP.Analysis.LatticeConvolution.SrcNormConv.Main

/-!
# Cross-check by transfer from the frozen sup-norm assembly

A second, independent route to the strict source-norm convolution bound: instead of
re-deriving the three regions (as in `Regions.lean`), transport the domination hypotheses
into the supremum norm with the landed `Wt_srcNorm_le`, apply the frozen `conv_tsum_le`, and
transport the target profile back with `Wt_linfNorm_le_srcNorm`.  The two routes yield the
same statement with different explicit constants, which is the point: the frozen strict
assembly is legitimately reusable, not merely re-proved.
-/

set_option autoImplicit false

@[expose] public section

namespace SrcNormConv

open PercLib.CriticalLRP.Orchestration
open CriticalLRPConv
open PercLib.CriticalLRP.FiniteVolume (linfNorm)

variable {d : ℕ}

/-- `2 ^ x` is nonnegative for every real exponent. -/
theorem two_rpow_nonneg (x : ℝ) : (0 : ℝ) ≤ (2 : ℝ) ^ x :=
  Real.rpow_nonneg (by norm_num) x

/-- The upper logarithmic comparison constant is positive. -/
theorem srcLogConstUpper_pos (S : SourceNormData d) : 0 < srcLogConstUpper S := by
  have hC : (0 : ℝ) < srcUpperConst S := srcUpperConst_pos S
  have h1 : (0 : ℝ) < Real.log (2 + srcUpperConst S) := Real.log_pos (by linarith)
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h3 : (0 : ℝ) < Real.log (2 + srcUpperConst S) / Real.log 2 := div_pos h1 h2
  simp only [srcLogConstUpper]
  linarith

/-! ## §1 The reverse weight comparison, sup norm versus source norm -/

/-- **The target-side weight comparison.**  The sup-norm weight at `y` is bounded by the
source-norm weight at `y` up to the upper norm-comparison constant; this is the direction
needed to bring a sup-norm conclusion back to `S.ρ`. -/
theorem Wt_linfNorm_le_srcNorm (S : SourceNormData d) {e c : ℝ} (he : 0 ≤ e) (hc : 0 ≤ c)
    (y : Fin d → ℤ) :
    Wt e c (linfNorm y : ℝ) ≤
      srcUpperConst S ^ e * srcLogConstUpper S ^ c * Wt e c (S.ρ (toVec y)) := by
  have hC : (0 : ℝ) < srcUpperConst S := srcUpperConst_pos S
  have hle : S.ρ (toVec y) / srcUpperConst S ≤ (linfNorm y : ℝ) := by
    rw [div_le_iff₀ hC]
    calc S.ρ (toVec y) ≤ srcUpperConst S * (linfNorm y : ℝ) := srcNorm_le_upper_linfNorm S y
      _ = (linfNorm y : ℝ) * srcUpperConst S := by ring
  have hr : (0 : ℝ) ≤ S.ρ (toVec y) / srcUpperConst S :=
    div_nonneg (src_nonneg S _) hC.le
  have h1 : Wt e c (linfNorm y : ℝ) ≤ Wt e c (S.ρ (toVec y) / srcUpperConst S) :=
    Wt_antitone he hc hr hle
  have h2 := Wt_div_srcUpper_le (S := S) (e := e) (c := c) (S₀ := S.ρ (toVec y)) he hc
    (src_nonneg S _)
  exact h1.trans h2

/-! ## §2 The explicit transfer constant -/

/-- The constant produced by the transfer route: the hypothesis side pays
`srcLowerUnit^{-(d-a)} srcLogConst^{â}`, the target side pays
`srcUpperConst^{d-a-b} srcLogConstUpper^{â+b̂}`. -/
noncomputable def srcTransferConst (S : SourceNormData d) (a b ah bh : ℝ) : ℝ :=
  (srcLowerUnit S ^ (-((d : ℝ) - a)) * srcLogConst S ^ ah) *
    (srcLowerUnit S ^ (-((d : ℝ) - b)) * srcLogConst S ^ bh) *
    (srcUpperConst S ^ ((d : ℝ) - a - b) * srcLogConstUpper S ^ (ah + bh))

/-! ## §3 Nonnegativity of the frozen region-summed constant -/

/-- The frozen total region constant is nonnegative. -/
theorem convConst_nonneg {a b ah bh : ℝ} (hd : 1 ≤ d) (ha : 0 < a) (hb : 0 < b)
    (hab : a + b < (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh) :
    0 ≤ CriticalLRPConv.convConst d a b ah bh := by
  have had : a ≤ (d : ℝ) := by linarith
  have hbd : b ≤ (d : ℝ) := by linarith
  have hγ : 0 < (d : ℝ) - a - b := by linarith
  have h1 : 0 ≤ CriticalLRPConv.convReg1Const d a b ah bh := by
    rw [CriticalLRPConv.convReg1Const]
    exact mul_nonneg (mul_nonneg (two_rpow_nonneg _) (two_rpow_nonneg _))
      (CriticalLRPConv.ballShellConst_nonneg ha.le had hah)
  have h2 : 0 ≤ CriticalLRPConv.convReg2Const d a b ah bh := by
    rw [CriticalLRPConv.convReg2Const]
    exact mul_nonneg (mul_nonneg (two_rpow_nonneg _) (two_rpow_nonneg _))
      (CriticalLRPConv.ballShellConst_nonneg hb.le hbd hbh)
  have h3 : 0 ≤ CriticalLRPConv.convReg3Const d a b ah bh := by
    rw [CriticalLRPConv.convReg3Const]
    have ht : 0 < CriticalLRPConv.tailShellConst d ((d : ℝ) - a - b) :=
      CriticalLRPConv.tailShellConst_pos hd hγ
    exact mul_nonneg (mul_nonneg (two_rpow_nonneg _) (two_rpow_nonneg _))
      (mul_nonneg (by norm_num) (mul_nonneg (two_rpow_nonneg _) ht.le))
  rw [CriticalLRPConv.convConst]
  exact add_nonneg (add_nonneg h1 h2) h3

/-! ## §4 The transferred statement -/

/-- **Strict convolution assembly in the source norm, by transfer.**  The same conclusion as
`conv_tsum_le_srcNorm`, obtained from the frozen sup-norm assembly through the two weight
comparisons of `NormShell` instead of the region re-derivation of `Regions.lean`. -/
theorem conv_tsum_le_srcNorm_via_sup (S : SourceNormData d) (hd : 1 ≤ d) {a b ah bh : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b < (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh)
    {f g : (Fin d → ℤ) → ℝ} {Cf Cg : ℝ} (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hf : ∀ y, |f y| ≤ Cf * Wt ((d : ℝ) - a) ah (S.ρ (toVec y)))
    (hg : ∀ y, |g y| ≤ Cg * Wt ((d : ℝ) - b) bh (S.ρ (toVec y))) (x : Fin d → ℤ) :
    Summable (fun y => f y * g (x - y)) ∧
      |∑' y, f y * g (x - y)| ≤
        Cf * Cg * (srcTransferConst (d := d) S a b ah bh *
          (CriticalLRPConv.convConst d a b ah bh *
            Wt ((d : ℝ) - a - b) (ah + bh) (S.ρ (toVec x)))) := by
  have hea : (0 : ℝ) ≤ (d : ℝ) - a := by linarith
  have heb : (0 : ℝ) ≤ (d : ℝ) - b := by linarith
  have heab : (0 : ℝ) ≤ (d : ℝ) - a - b := by linarith
  set L1 : ℝ := srcLowerUnit S ^ (-((d : ℝ) - a)) * srcLogConst S ^ ah with hL1
  set L2 : ℝ := srcLowerUnit S ^ (-((d : ℝ) - b)) * srcLogConst S ^ bh with hL2
  set K3 : ℝ := srcUpperConst S ^ ((d : ℝ) - a - b) * srcLogConstUpper S ^ (ah + bh) with hK3
  have hL1nn : 0 ≤ L1 := by
    rw [hL1]
    exact mul_nonneg (Real.rpow_nonneg (srcLowerUnit_pos S hd).le _)
      (Real.rpow_nonneg (srcLogConst_pos S hd).le _)
  have hL2nn : 0 ≤ L2 := by
    rw [hL2]
    exact mul_nonneg (Real.rpow_nonneg (srcLowerUnit_pos S hd).le _)
      (Real.rpow_nonneg (srcLogConst_pos S hd).le _)
  have hK3nn : 0 ≤ K3 := by
    rw [hK3]
    exact mul_nonneg (Real.rpow_nonneg (srcUpperConst_pos S).le _)
      (Real.rpow_nonneg (srcLogConstUpper_pos S).le _)
  have hf' : ∀ y, |f y| ≤ (Cf * L1) * Wt ((d : ℝ) - a) ah ‖y‖ := by
    intro y
    rw [coe_norm_eq_linfNorm]
    refine (hf y).trans ?_
    have h := Wt_srcNorm_le S hd hea hah y
    calc Cf * Wt ((d : ℝ) - a) ah (S.ρ (toVec y))
        ≤ Cf * (L1 * Wt ((d : ℝ) - a) ah (linfNorm y : ℝ)) := by
          rw [hL1]
          exact mul_le_mul_of_nonneg_left h hCf
      _ = (Cf * L1) * Wt ((d : ℝ) - a) ah (linfNorm y : ℝ) := by ring
  have hg' : ∀ y, |g y| ≤ (Cg * L2) * Wt ((d : ℝ) - b) bh ‖y‖ := by
    intro y
    rw [coe_norm_eq_linfNorm]
    refine (hg y).trans ?_
    have h := Wt_srcNorm_le S hd heb hbh y
    calc Cg * Wt ((d : ℝ) - b) bh (S.ρ (toVec y))
        ≤ Cg * (L2 * Wt ((d : ℝ) - b) bh (linfNorm y : ℝ)) := by
          rw [hL2]
          exact mul_le_mul_of_nonneg_left h hCg
      _ = (Cg * L2) * Wt ((d : ℝ) - b) bh (linfNorm y : ℝ) := by ring
  obtain ⟨hsumm, hbound⟩ := CriticalLRPConv.conv_tsum_le (d := d) hd ha hb hab hah hbh
    (mul_nonneg hCf hL1nn) (mul_nonneg hCg hL2nn) hf' hg' x
  refine ⟨hsumm, ?_⟩
  have hgoal : CriticalLRPConv.convTarget a b ah bh x =
      Wt ((d : ℝ) - a - b) (ah + bh) (linfNorm x : ℝ) := by
    simp only [CriticalLRPConv.convTarget, CriticalLRPConv.convTargetR]
    rw [coe_norm_eq_linfNorm]
  have hW3 : CriticalLRPConv.convTarget a b ah bh x ≤
      K3 * Wt ((d : ℝ) - a - b) (ah + bh) (S.ρ (toVec x)) := by
    rw [hgoal, hK3]
    exact Wt_linfNorm_le_srcNorm (S := S) (e := (d : ℝ) - a - b) (c := ah + bh)
      heab (by linarith) x
  have hCnn : 0 ≤ CriticalLRPConv.convConst d a b ah bh :=
    convConst_nonneg hd ha hb hab hah hbh
  have hstep : CriticalLRPConv.convConst d a b ah bh *
        CriticalLRPConv.convTarget a b ah bh x ≤
      CriticalLRPConv.convConst d a b ah bh *
        (K3 * Wt ((d : ℝ) - a - b) (ah + bh) (S.ρ (toVec x))) :=
    mul_le_mul_of_nonneg_left hW3 hCnn
  calc |∑' y, f y * g (x - y)|
      ≤ (Cf * L1) * (Cg * L2) *
          (CriticalLRPConv.convConst d a b ah bh *
            CriticalLRPConv.convTarget a b ah bh x) := hbound
    _ ≤ (Cf * L1) * (Cg * L2) *
          (CriticalLRPConv.convConst d a b ah bh *
            (K3 * Wt ((d : ℝ) - a - b) (ah + bh) (S.ρ (toVec x)))) := by
        refine mul_le_mul_of_nonneg_left hstep ?_
        exact mul_nonneg (mul_nonneg hCf hL1nn) (mul_nonneg hCg hL2nn)
    _ = Cf * Cg * (srcTransferConst (d := d) S a b ah bh *
          (CriticalLRPConv.convConst d a b ah bh *
            Wt ((d : ℝ) - a - b) (ah + bh) (S.ρ (toVec x)))) := by
        rw [srcTransferConst, hL1, hL2, hK3]
        ring

end SrcNormConv

/-! ## §5 Axiom audit -/

set_option linter.hashCommand false

#print axioms SrcNormConv.two_rpow_nonneg
#print axioms SrcNormConv.srcLogConstUpper_pos
#print axioms SrcNormConv.Wt_linfNorm_le_srcNorm
#print axioms SrcNormConv.convConst_nonneg
#print axioms SrcNormConv.conv_tsum_le_srcNorm_via_sup
