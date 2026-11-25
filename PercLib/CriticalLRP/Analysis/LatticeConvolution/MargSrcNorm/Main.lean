/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
-/
module

public import PercLib.CriticalLRP.Analysis.LatticeConvolution.MargSrcNorm.Defs

/-!
# The marginal (`a + b = d`) convolution estimate in an arbitrary normalized source norm

This file transfers the frozen marginal assembly `CriticalLRPConv.conv_tsum_le_marg`
(`MargConv.Main`) from the lattice supremum norm to an arbitrary normalized
`SourceNormData S`, in the same way that `SrcNormConv.Transfer` transfers the strict-regime
assembly `CriticalLRPConv.conv_tsum_le`.

For `a, b > 0`, `a + b = d`, `â, b̂ ≥ 0`, `â + b̂ > 1` and `f`, `g` dominated by the
source-norm kernels `Wt (d-a) â (S.ρ ·)`, `Wt (d-b) b̂ (S.ρ ·)`, the series
`Σ' y, f y * g (x - y)` is summable and

`|Σ' y, f y * g (x - y)| ≤ Cf Cg (srcMargConst S a b â b̂) · Wt 0 (â+b̂-1) (S.ρ x)`,

i.e. bounded by the pure logarithmic profile `(log (2 + S.ρ x))^{1-(â+b̂)}` with an explicit
constant depending on `S` and the marginal parameters only.

The three ingredients are: (i) `1 ≤ d` follows from `a, b > 0` and `a + b = d`, so no
dimension hypothesis is needed; (ii) the hypothesis-side transfer
`Wt e c (S.ρ y) ≤ srcLowerUnit^{-e} srcLogConst^c · Wt e c ‖y‖` (`Wt_srcNorm_le`) with
`0 ≤ d - a`, `0 ≤ d - b`; (iii) the target-side transfer
`Wt 0 c ‖x‖ ≤ srcLogConstUpper^c · Wt 0 c (S.ρ x)` (`Wt_linfNorm_le_srcNorm`) with
`c = â + b̂ - 1 ≥ 0`, where the power factor `srcUpperConst^0` drops out. The exponent
`â + b̂ - 1` is preserved exactly: no pure-log `c` is introduced.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

namespace SrcNormConv

open PercLib.CriticalLRP.Orchestration
open CriticalLRPConv
open PercLib.CriticalLRP.FiniteVolume (linfNorm)

variable {d : ℕ}

/-! ## §0 Dimension, target profile and constant bookkeeping -/

/-- **Dimension positivity.**  In the marginal regime `a + b = d` with `a, b > 0` the
dimension is positive, so `1 ≤ d` need not be assumed separately. -/
theorem one_le_of_add_eq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = (d : ℝ)) :
    1 ≤ d := by
  have h0 : (0 : ℝ) < (d : ℝ) := by rw [← hab]; linarith
  have h1 : 0 < d := by exact_mod_cast h0
  omega

/-- The marginal target profile in the source norm is positive. -/
theorem srcMargTarget_pos (S : SourceNormData d) (ah bh : ℝ) (x : Fin d → ℤ) :
    0 < srcMargTarget S ah bh x :=
  Wt_pos (src_nonneg S (toVec x))

/-- The marginal target profile in the source norm is nonnegative. -/
theorem srcMargTarget_nonneg (S : SourceNormData d) (ah bh : ℝ) (x : Fin d → ℤ) :
    0 ≤ srcMargTarget S ah bh x :=
  (srcMargTarget_pos S ah bh x).le

/-- The marginal target profile is the pure logarithmic profile `Λ(S.ρ x)^{1-(â+b̂)}`. -/
theorem srcMargTarget_eq_explicit (S : SourceNormData d) (ah bh : ℝ) (x : Fin d → ℤ) :
    srcMargTarget S ah bh x = Real.log (2 + S.ρ (toVec x)) ^ (1 - (ah + bh)) := by
  unfold srcMargTarget Wt LamR
  have h0 : (1 + S.ρ (toVec x)) ^ (-(0 : ℝ)) = 1 := by simp
  rw [h0, one_mul]
  congr 1
  ring

/-- The two writings of the marginal target profile agree: `S.ρ (toVec x)` is the model
distance `S.dist 0 x`. -/
theorem srcMargTarget_eq_dist (S : SourceNormData d) (ah bh : ℝ) (x : Fin d → ℤ) :
    srcMargTarget S ah bh x = srcMargTargetDist S ah bh x := by
  rw [srcMargTarget, srcMargTargetDist, ← dist_zero_eq_srcNorm]

/-- The target profile written with `S.dist 0 x` is positive. -/
theorem srcMargTargetDist_pos (S : SourceNormData d) (ah bh : ℝ) (x : Fin d → ℤ) :
    0 < srcMargTargetDist S ah bh x := by
  rw [← srcMargTarget_eq_dist]
  exact srcMargTarget_pos S ah bh x

/-- A positive base raised to a real power is nonnegative. -/
theorem srcLowerUnit_rpow_nonneg (S : SourceNormData d) (hd : 1 ≤ d) (e : ℝ) :
    0 ≤ srcLowerUnit S ^ e :=
  Real.rpow_nonneg (srcLowerUnit_pos S hd).le e

/-- The hypothesis-side logarithmic constant is positive in positive dimension. -/
theorem srcLogConst_rpow_nonneg (S : SourceNormData d) (hd : 1 ≤ d) (e : ℝ) :
    0 ≤ srcLogConst S ^ e :=
  Real.rpow_nonneg (srcLogConst_pos S hd).le e

/-- The target-side logarithmic constant raised to a real power is nonnegative. -/
theorem srcLogConstUpper_rpow_nonneg (S : SourceNormData d) (e : ℝ) :
    0 ≤ srcLogConstUpper S ^ e :=
  Real.rpow_nonneg (srcLogConstUpper_pos S).le e

/-- **The transfer constant of the marginal assembly is nonnegative.** -/
theorem srcMargTransferConst_nonneg (S : SourceNormData d) (hd : 1 ≤ d) (a b ah bh : ℝ) :
    0 ≤ srcMargTransferConst S a b ah bh := by
  rw [srcMargTransferConst]
  refine mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) (mul_nonneg ?_ ?_)) ?_
  · exact srcLowerUnit_rpow_nonneg S hd _
  · exact srcLogConst_rpow_nonneg S hd _
  · exact srcLowerUnit_rpow_nonneg S hd _
  · exact srcLogConst_rpow_nonneg S hd _
  · exact srcLogConstUpper_rpow_nonneg S _

/-- **The transfer constant of the marginal assembly is positive.** -/
theorem srcMargTransferConst_pos (S : SourceNormData d) (hd : 1 ≤ d) (a b ah bh : ℝ) :
    0 < srcMargTransferConst S a b ah bh := by
  rw [srcMargTransferConst]
  refine mul_pos (mul_pos (mul_pos ?_ ?_) (mul_pos ?_ ?_)) ?_
  · exact Real.rpow_pos_of_pos (srcLowerUnit_pos S hd) _
  · exact Real.rpow_pos_of_pos (srcLogConst_pos S hd) _
  · exact Real.rpow_pos_of_pos (srcLowerUnit_pos S hd) _
  · exact Real.rpow_pos_of_pos (srcLogConst_pos S hd) _
  · exact Real.rpow_pos_of_pos (srcLogConstUpper_pos S) _

/-- **The assembled marginal constant is nonnegative.** -/
theorem srcMargConst_nonneg (S : SourceNormData d) (hd : 1 ≤ d) {a b ah bh : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh)
    (hS : 1 < ah + bh) :
    0 ≤ srcMargConst S a b ah bh :=
  mul_nonneg (srcMargTransferConst_nonneg S hd a b ah bh)
    (margConst_nonneg' hd ha hb hab hah hbh hS)

/-! ## §1 The two weight-transfer steps -/

/-- **Hypothesis-side transfer.**  The source-norm weight at `y` is at most the sup-norm
weight at `y` times `srcLowerUnit^{-e} srcLogConst^c`; this is `Wt_srcNorm_le` with the
product regrouped for use on the domination hypotheses. -/
theorem Wt_src_le_mul_linf (S : SourceNormData d) (hd : 1 ≤ d) {e c : ℝ} (he : 0 ≤ e)
    (hc : 0 ≤ c) (y : Fin d → ℤ) :
    Wt e c (S.ρ (toVec y)) ≤
      (srcLowerUnit S ^ (-e) * srcLogConst S ^ c) * Wt e c (linfNorm y : ℝ) :=
  Wt_srcNorm_le S hd he hc y

/-- **Target-side transfer.**  The sup-norm marginal target at `x` is at most
`srcLogConstUpper^{â+b̂-1}` times the source-norm marginal target at `x`; the power factor
`srcUpperConst^0` of `Wt_linfNorm_le_srcNorm` is `1` and drops out exactly. -/
theorem margTarget_le_srcMargTarget (S : SourceNormData d) {ah bh : ℝ}
    (hc : 0 ≤ ah + bh - 1) (x : Fin d → ℤ) :
    margTarget ah bh x ≤ srcLogConstUpper S ^ (ah + bh - 1) * srcMargTarget S ah bh x := by
  have hx : margTarget ah bh x = Wt 0 (ah + bh - 1) (linfNorm x : ℝ) := by
    rw [margTarget, margTargetR, coe_norm_eq_linfNorm]
  rw [hx, srcMargTarget]
  have h := Wt_linfNorm_le_srcNorm (S := S) (e := 0) (c := ah + bh - 1) le_rfl hc x
  rwa [Real.rpow_zero, one_mul] at h

/-! ## §2 The source-norm majorant is summable and bounded -/

/-- **Summability and bound for the source-norm marginal majorant.**  Obtained by applying
the frozen assembly `conv_tsum_le_marg` to the two source-norm kernels themselves; both
conclusions come out of the same application. -/
theorem srcConvMajorant_marg_bounds (S : SourceNormData d) {a b ah bh : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh)
    (hS : 1 < ah + bh) (x : Fin d → ℤ) :
    Summable (fun y => srcConvMajorant S a b ah bh x y) ∧
      (∑' y, srcConvMajorant S a b ah bh x y ≤
        srcMargConst S a b ah bh * srcMargTarget S ah bh x) := by
  have hd : 1 ≤ d := one_le_of_add_eq ha hb hab
  have hea : (0 : ℝ) ≤ (d : ℝ) - a := by linarith
  have heb : (0 : ℝ) ≤ (d : ℝ) - b := by linarith
  have hc1 : (0 : ℝ) ≤ ah + bh - 1 := by linarith
  set L1 : ℝ := srcLowerUnit S ^ (-((d : ℝ) - a)) * srcLogConst S ^ ah with hL1
  set L2 : ℝ := srcLowerUnit S ^ (-((d : ℝ) - b)) * srcLogConst S ^ bh with hL2
  have hL1nn : 0 ≤ L1 := by
    rw [hL1]
    exact mul_nonneg (srcLowerUnit_rpow_nonneg S hd _) (srcLogConst_rpow_nonneg S hd _)
  have hL2nn : 0 ≤ L2 := by
    rw [hL2]
    exact mul_nonneg (srcLowerUnit_rpow_nonneg S hd _) (srcLogConst_rpow_nonneg S hd _)
  have hf : ∀ y, |Wt ((d : ℝ) - a) ah (S.ρ (toVec y))| ≤
      L1 * Wt ((d : ℝ) - a) ah ‖y‖ := by
    intro y
    rw [abs_of_nonneg (Wt_nonneg (src_nonneg S _)), coe_norm_eq_linfNorm, hL1]
    exact Wt_src_le_mul_linf S hd hea hah y
  have hg : ∀ y, |Wt ((d : ℝ) - b) bh (S.ρ (toVec y))| ≤
      L2 * Wt ((d : ℝ) - b) bh ‖y‖ := by
    intro y
    rw [abs_of_nonneg (Wt_nonneg (src_nonneg S _)), coe_norm_eq_linfNorm, hL2]
    exact Wt_src_le_mul_linf S hd heb hbh y
  obtain ⟨hsumm, hbound⟩ :=
    conv_tsum_le_marg (d := d) hd ha hb hab hah hbh hS hL1nn hL2nn hf hg x
  have hsumm' : Summable (fun y => srcConvMajorant S a b ah bh x y) := by
    simpa only [srcConvMajorant, srcRadius] using hsumm
  refine ⟨hsumm', ?_⟩
  have hnonneg : 0 ≤ ∑' y, Wt ((d : ℝ) - a) ah (S.ρ (toVec y)) *
      Wt ((d : ℝ) - b) bh (S.ρ (toVec (x - y))) :=
    tsum_nonneg (fun y => mul_nonneg (Wt_nonneg (src_nonneg S _))
      (Wt_nonneg (src_nonneg S _)))
  have htsum : (∑' y, srcConvMajorant S a b ah bh x y) =
      ∑' y, Wt ((d : ℝ) - a) ah (S.ρ (toVec y)) *
        Wt ((d : ℝ) - b) bh (S.ρ (toVec (x - y))) :=
    tsum_congr (fun y => rfl)
  have htgt : margConst d a b ah bh * margTarget ah bh x ≤
      margConst d a b ah bh * (srcLogConstUpper S ^ (ah + bh - 1) * srcMargTarget S ah bh x) :=
    mul_le_mul_of_nonneg_left (margTarget_le_srcMargTarget (S := S) hc1 x)
      (margConst_nonneg' (d := d) hd ha hb hab hah hbh hS)
  calc ∑' y, srcConvMajorant S a b ah bh x y
      = ∑' y, Wt ((d : ℝ) - a) ah (S.ρ (toVec y)) *
          Wt ((d : ℝ) - b) bh (S.ρ (toVec (x - y))) := htsum
    _ = |∑' y, Wt ((d : ℝ) - a) ah (S.ρ (toVec y)) *
          Wt ((d : ℝ) - b) bh (S.ρ (toVec (x - y)))| := (abs_of_nonneg hnonneg).symm
    _ ≤ L1 * L2 * (margConst d a b ah bh * margTarget ah bh x) := hbound
    _ ≤ L1 * L2 *
          (margConst d a b ah bh * (srcLogConstUpper S ^ (ah + bh - 1) *
            srcMargTarget S ah bh x)) :=
        mul_le_mul_of_nonneg_left htgt (mul_nonneg hL1nn hL2nn)
    _ = srcMargConst S a b ah bh * srcMargTarget S ah bh x := by
        rw [srcMargConst, srcMargTransferConst, hL1, hL2]
        ring

/-- **Summability of the source-norm marginal majorant.** -/
theorem summable_srcConvMajorant_marg (S : SourceNormData d) {a b ah bh : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh)
    (hS : 1 < ah + bh) (x : Fin d → ℤ) :
    Summable (fun y => srcConvMajorant S a b ah bh x y) :=
  (srcConvMajorant_marg_bounds S ha hb hab hah hbh hS x).1

/-- **The `tsum` of the source-norm marginal majorant.** -/
theorem tsum_srcConvMajorant_le_marg (S : SourceNormData d) {a b ah bh : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh)
    (hS : 1 < ah + bh) (x : Fin d → ℤ) :
    ∑' y, srcConvMajorant S a b ah bh x y ≤
      srcMargConst S a b ah bh * srcMargTarget S ah bh x :=
  (srcConvMajorant_marg_bounds S ha hb hab hah hbh hS x).2

/-! ## §3 The marginal convolution assembly in the source norm -/

/-- **Marginal convolution assembly in an arbitrary normalized source norm.**  If `f` and `g`
are dominated by the source-norm kernels `Wt (d-a) â (S.ρ ·)` and `Wt (d-b) b̂ (S.ρ ·)` with
`a, b > 0`, `a + b = d`, `â, b̂ ≥ 0` and `1 < â + b̂`, then the convolution
`Σ' y, f y * g (x - y)` is summable and bounded by
`Cf Cg (srcMargConst S a b â b̂) Wt 0 (â+b̂-1) (S.ρ x)`, i.e. by the pure logarithmic profile
`(log (2 + S.ρ x))^{1-(â+b̂)}` with a constant independent of `x`, `f` and `g`.  No dimension
hypothesis is needed: `1 ≤ d` follows from `a, b > 0` and `a + b = d`. -/
theorem conv_tsum_le_marg_srcNorm (S : SourceNormData d) {a b ah bh : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh)
    (hS : 1 < ah + bh) {f g : (Fin d → ℤ) → ℝ} {Cf Cg : ℝ} (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hf : ∀ y, |f y| ≤ Cf * Wt ((d : ℝ) - a) ah (S.ρ (toVec y)))
    (hg : ∀ y, |g y| ≤ Cg * Wt ((d : ℝ) - b) bh (S.ρ (toVec y))) (x : Fin d → ℤ) :
    Summable (fun y => f y * g (x - y)) ∧
      |∑' y, f y * g (x - y)| ≤
        Cf * Cg * (srcMargConst S a b ah bh * srcMargTarget S ah bh x) := by
  have hmaj := summable_srcConvMajorant_marg S ha hb hab hah hbh hS x
  have hle : ∀ y, |f y * g (x - y)| ≤ Cf * Cg * srcConvMajorant S a b ah bh x y := by
    intro y
    rw [abs_mul]
    have h1 : |f y| ≤ Cf * Wt ((d : ℝ) - a) ah (S.ρ (toVec y)) := hf y
    have h2 : |g (x - y)| ≤ Cg * Wt ((d : ℝ) - b) bh (S.ρ (toVec (x - y))) := hg (x - y)
    have hW1 : (0 : ℝ) ≤ Wt ((d : ℝ) - a) ah (S.ρ (toVec y)) :=
      Wt_nonneg (src_nonneg S _)
    calc |f y| * |g (x - y)|
        ≤ (Cf * Wt ((d : ℝ) - a) ah (S.ρ (toVec y))) *
            (Cg * Wt ((d : ℝ) - b) bh (S.ρ (toVec (x - y)))) :=
          mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hCf hW1)
      _ = Cf * Cg * srcConvMajorant S a b ah bh x y := by
          simp only [srcConvMajorant, srcRadius]
          ring
  have hle' : ∀ y, ‖f y * g (x - y)‖ ≤ Cf * Cg * srcConvMajorant S a b ah bh x y := by
    intro y
    rw [Real.norm_eq_abs]
    exact hle y
  have hsumm : Summable (fun y => f y * g (x - y)) :=
    Summable.of_norm_bounded (hmaj.mul_left (Cf * Cg)) hle'
  refine ⟨hsumm, ?_⟩
  have hb1 : |∑' y, f y * g (x - y)| ≤ ∑' y, ‖f y * g (x - y)‖ := by
    rw [← Real.norm_eq_abs]
    exact norm_tsum_le_tsum_norm hsumm.norm
  have hb2 : ∑' y, ‖f y * g (x - y)‖ ≤
      Cf * Cg * (srcMargConst S a b ah bh * srcMargTarget S ah bh x) := by
    have hstep := Summable.tsum_le_tsum hle' hsumm.norm (hmaj.mul_left (Cf * Cg))
    calc ∑' y, ‖f y * g (x - y)‖ ≤ ∑' y, Cf * Cg * srcConvMajorant S a b ah bh x y := hstep
      _ = Cf * Cg * ∑' y, srcConvMajorant S a b ah bh x y := tsum_mul_left
      _ ≤ Cf * Cg * (srcMargConst S a b ah bh * srcMargTarget S ah bh x) :=
          mul_le_mul_of_nonneg_left
            (tsum_srcConvMajorant_le_marg S ha hb hab hah hbh hS x) (mul_nonneg hCf hCg)
  exact hb1.trans hb2

/-- **Summability alone**, as a standalone consequence of the marginal source-norm assembly. -/
theorem summable_conv_marg_srcNorm (S : SourceNormData d) {a b ah bh : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh)
    (hS : 1 < ah + bh) {f g : (Fin d → ℤ) → ℝ} {Cf Cg : ℝ} (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hf : ∀ y, |f y| ≤ Cf * Wt ((d : ℝ) - a) ah (S.ρ (toVec y)))
    (hg : ∀ y, |g y| ≤ Cg * Wt ((d : ℝ) - b) bh (S.ρ (toVec y))) (x : Fin d → ℤ) :
    Summable (fun y => f y * g (x - y)) :=
  (conv_tsum_le_marg_srcNorm S ha hb hab hah hbh hS hCf hCg hf hg x).1

/-! ## §4 The explicit constant, the `S.dist` form and the logarithmic profile -/

/-- **The same bound with the transfer and assembly constants separated.**  This is the
explicit constant of the transfer: `srcMargTransferConst S a b â b̂ · margConst d a b â b̂`,
where the first factor depends only on `S` and the exponents and the second only on the
frozen sup-norm assembly. -/
theorem conv_tsum_le_marg_srcNorm_expanded (S : SourceNormData d) {a b ah bh : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh)
    (hS : 1 < ah + bh) {f g : (Fin d → ℤ) → ℝ} {Cf Cg : ℝ} (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hf : ∀ y, |f y| ≤ Cf * Wt ((d : ℝ) - a) ah (S.ρ (toVec y)))
    (hg : ∀ y, |g y| ≤ Cg * Wt ((d : ℝ) - b) bh (S.ρ (toVec y))) (x : Fin d → ℤ) :
    Summable (fun y => f y * g (x - y)) ∧
      |∑' y, f y * g (x - y)| ≤
        Cf * Cg * (srcMargTransferConst S a b ah bh *
          (margConst d a b ah bh * srcMargTarget S ah bh x)) := by
  obtain ⟨hsumm, hbound⟩ :=
    conv_tsum_le_marg_srcNorm S ha hb hab hah hbh hS hCf hCg hf hg x
  refine ⟨hsumm, ?_⟩
  rw [srcMargConst] at hbound
  calc |∑' y, f y * g (x - y)|
      ≤ Cf * Cg * ((srcMargTransferConst S a b ah bh * margConst d a b ah bh) *
          srcMargTarget S ah bh x) := hbound
    _ = Cf * Cg * (srcMargTransferConst S a b ah bh *
          (margConst d a b ah bh * srcMargTarget S ah bh x)) := by ring

/-- **The bound in the paper's normalisation**: the target profile is written out as
`(log (2 + S.ρ x))^{1-(â+b̂)}`, with the exponent `1 - (â + b̂)` preserved. -/
theorem conv_tsum_le_marg_srcNorm_log (S : SourceNormData d) {a b ah bh : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh)
    (hS : 1 < ah + bh) {f g : (Fin d → ℤ) → ℝ} {Cf Cg : ℝ} (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hf : ∀ y, |f y| ≤ Cf * Wt ((d : ℝ) - a) ah (S.ρ (toVec y)))
    (hg : ∀ y, |g y| ≤ Cg * Wt ((d : ℝ) - b) bh (S.ρ (toVec y))) (x : Fin d → ℤ) :
    Summable (fun y => f y * g (x - y)) ∧
      |∑' y, f y * g (x - y)| ≤
        Cf * Cg * (srcMargConst S a b ah bh *
          Real.log (2 + S.ρ (toVec x)) ^ (1 - (ah + bh))) := by
  obtain ⟨hsumm, hbound⟩ :=
    conv_tsum_le_marg_srcNorm S ha hb hab hah hbh hS hCf hCg hf hg x
  refine ⟨hsumm, ?_⟩
  rw [← srcMargTarget_eq_explicit]
  exact hbound

/-- **The marginal assembly stated with the model source distance `S.dist 0 ·`.**  Every
source norm is written as the normalized source distance of the model data, and the target
profile is `Wt 0 (â+b̂-1) (S.dist 0 x)`. -/
theorem conv_tsum_le_marg_srcDist (S : SourceNormData d) {a b ah bh : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh)
    (hS : 1 < ah + bh) {f g : (Fin d → ℤ) → ℝ} {Cf Cg : ℝ} (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hf : ∀ y, |f y| ≤ Cf * Wt ((d : ℝ) - a) ah (S.dist 0 y))
    (hg : ∀ y, |g y| ≤ Cg * Wt ((d : ℝ) - b) bh (S.dist 0 y)) (x : Fin d → ℤ) :
    Summable (fun y => f y * g (x - y)) ∧
      |∑' y, f y * g (x - y)| ≤
        Cf * Cg * (srcMargConst S a b ah bh * srcMargTargetDist S ah bh x) := by
  have hf' : ∀ y, |f y| ≤ Cf * Wt ((d : ℝ) - a) ah (S.ρ (toVec y)) := by
    intro y
    rw [← dist_zero_eq_srcNorm]
    exact hf y
  have hg' : ∀ y, |g y| ≤ Cg * Wt ((d : ℝ) - b) bh (S.ρ (toVec y)) := by
    intro y
    rw [← dist_zero_eq_srcNorm]
    exact hg y
  obtain ⟨hsumm, hbound⟩ :=
    conv_tsum_le_marg_srcNorm S ha hb hab hah hbh hS hCf hCg hf' hg' x
  refine ⟨hsumm, ?_⟩
  rw [← srcMargTarget_eq_dist]
  exact hbound

/-- **Non-vacuity of the marginal source-norm assembly.**  The two model kernels themselves
satisfy the domination hypotheses with `Cf = Cg = 1`, so the assembly applies to a genuine
nonzero pair. -/
theorem conv_kernel_le_marg_srcDist (S : SourceNormData d) {a b ah bh : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh)
    (hS : 1 < ah + bh) (x : Fin d → ℤ) :
    Summable (fun y => Wt ((d : ℝ) - a) ah (S.dist 0 y) *
        Wt ((d : ℝ) - b) bh (S.dist 0 (x - y))) ∧
      |∑' y, Wt ((d : ℝ) - a) ah (S.dist 0 y) *
          Wt ((d : ℝ) - b) bh (S.dist 0 (x - y))| ≤
        srcMargConst S a b ah bh * srcMargTargetDist S ah bh x := by
  have hf : ∀ y, |Wt ((d : ℝ) - a) ah (S.dist 0 y)| ≤
      1 * Wt ((d : ℝ) - a) ah (S.dist 0 y) := by
    intro y
    rw [abs_of_nonneg (Wt_nonneg (srcDist_nonneg S y)), one_mul]
  have hg : ∀ y, |Wt ((d : ℝ) - b) bh (S.dist 0 y)| ≤
      1 * Wt ((d : ℝ) - b) bh (S.dist 0 y) := by
    intro y
    rw [abs_of_nonneg (Wt_nonneg (srcDist_nonneg S y)), one_mul]
  simpa using conv_tsum_le_marg_srcDist S ha hb hab hah hbh hS zero_le_one zero_le_one
    hf hg x

/-! ## §5 An outer source-level factor

The bound is multiplied by an arbitrary weight `Wt (-e) ê (S.ρ x) = (1+S.ρ x)^e Λ(S.ρ x)^{-ê}`;
this is the form in which the marginal estimate is used when the outer factor is a source-level
decay rather than part of the convolution estimate itself. -/

/-- **Marginal assembly with an outer source-level factor.**  Multiplying the marginal bound
by `(1 + S.ρ x)^e Λ(S.ρ x)^{-ê}` gives `Wt (-e) (ê + (â+b̂-1)) (S.ρ x)` on the right; there
is no further analytic content. -/
theorem conv_tsum_le_marg_srcNorm_sourced (S : SourceNormData d) {a b ah bh e eh : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh)
    (hS : 1 < ah + bh) {f g : (Fin d → ℤ) → ℝ} {Cf Cg : ℝ} (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hf : ∀ y, |f y| ≤ Cf * Wt ((d : ℝ) - a) ah (S.ρ (toVec y)))
    (hg : ∀ y, |g y| ≤ Cg * Wt ((d : ℝ) - b) bh (S.ρ (toVec y))) (x : Fin d → ℤ) :
    Wt (-e) eh (S.ρ (toVec x)) * |∑' y, f y * g (x - y)| ≤
      Cf * Cg * srcMargConst S a b ah bh *
        Wt (-e) (eh + (ah + bh - 1)) (S.ρ (toVec x)) := by
  have hmain := (conv_tsum_le_marg_srcNorm S ha hb hab hah hbh hS hCf hCg hf hg x).2
  have hfac : (0 : ℝ) ≤ Wt (-e) eh (S.ρ (toVec x)) := Wt_nonneg (src_nonneg S _)
  have hLam : (0 : ℝ) < LamR (S.ρ (toVec x)) := LamR_pos (src_nonneg S _)
  have hcomb : Wt (-e) eh (S.ρ (toVec x)) * Wt 0 (ah + bh - 1) (S.ρ (toVec x)) =
      Wt (-e) (eh + (ah + bh - 1)) (S.ρ (toVec x)) := by
    simp only [Wt, neg_neg, neg_zero, Real.rpow_zero, one_mul]
    rw [mul_assoc, ← Real.rpow_add hLam]
    change (1 + S.ρ (toVec x)) ^ e * LamR (S.ρ (toVec x)) ^ (-eh + -(ah + bh - 1)) =
      (1 + S.ρ (toVec x)) ^ e * LamR (S.ρ (toVec x)) ^ (-(eh + (ah + bh - 1)))
    rw [show -eh + -(ah + bh - 1) = -(eh + (ah + bh - 1)) by ring]
  calc Wt (-e) eh (S.ρ (toVec x)) * |∑' y, f y * g (x - y)|
      ≤ Wt (-e) eh (S.ρ (toVec x)) *
          (Cf * Cg * (srcMargConst S a b ah bh * srcMargTarget S ah bh x)) :=
        mul_le_mul_of_nonneg_left hmain hfac
    _ = Cf * Cg * srcMargConst S a b ah bh *
          (Wt (-e) eh (S.ρ (toVec x)) * Wt 0 (ah + bh - 1) (S.ρ (toVec x))) := by
        rw [srcMargTarget]
        ring
    _ = Cf * Cg * srcMargConst S a b ah bh *
          Wt (-e) (eh + (ah + bh - 1)) (S.ρ (toVec x)) := by rw [hcomb]

end SrcNormConv

/-! ## §6 Axiom audit -/

set_option linter.hashCommand false

#print axioms SrcNormConv.one_le_of_add_eq
#print axioms SrcNormConv.srcMargTarget_pos
#print axioms SrcNormConv.srcMargTarget_nonneg
#print axioms SrcNormConv.srcMargTargetDist_pos
#print axioms SrcNormConv.srcLowerUnit_rpow_nonneg
#print axioms SrcNormConv.srcLogConst_rpow_nonneg
#print axioms SrcNormConv.srcLogConstUpper_rpow_nonneg
#print axioms SrcNormConv.srcMargTarget_eq_explicit
#print axioms SrcNormConv.srcMargTarget_eq_dist
#print axioms SrcNormConv.srcMargTransferConst_nonneg
#print axioms SrcNormConv.srcMargTransferConst_pos
#print axioms SrcNormConv.srcMargConst_nonneg
#print axioms SrcNormConv.Wt_src_le_mul_linf
#print axioms SrcNormConv.margTarget_le_srcMargTarget
#print axioms SrcNormConv.srcConvMajorant_marg_bounds
#print axioms SrcNormConv.summable_srcConvMajorant_marg
#print axioms SrcNormConv.tsum_srcConvMajorant_le_marg
#print axioms SrcNormConv.conv_tsum_le_marg_srcNorm
#print axioms SrcNormConv.summable_conv_marg_srcNorm
#print axioms SrcNormConv.conv_tsum_le_marg_srcNorm_expanded
#print axioms SrcNormConv.conv_tsum_le_marg_srcNorm_log
#print axioms SrcNormConv.conv_tsum_le_marg_srcDist
#print axioms SrcNormConv.conv_kernel_le_marg_srcDist
#print axioms SrcNormConv.conv_tsum_le_marg_srcNorm_sourced
