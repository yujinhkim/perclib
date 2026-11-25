/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
-/
module

public import PercLib.CriticalLRP.Analysis.LatticeConvolution.SrcNormConv.Regions

/-!
# The strict convolution assembly in an arbitrary normalized source norm

Finite-set majorant bound, summability of the majorant, the `tsum` bound, and the signed
two-point convolution estimate

`|Σ' y, f y * g (x - y)| ≤ Cf Cg (srcConvConst S a b â b̂) ⟨S.ρ x⟩^{-(d-a-b)} Λ(S.ρ x)^{-(â+b̂)}`

for `a, b > 0`, `a + b < d`, dominated by the source-norm kernels
`Wt (d-a) â (S.ρ ·)` and `Wt (d-b) b̂ (S.ρ ·)`.
-/

set_option autoImplicit false

@[expose] public section

namespace SrcNormConv

open PercLib.CriticalLRP.Orchestration
open CriticalLRPConv

variable {d : ℕ}

/-! ## §1 The finite-set majorant bound -/

/-- **The finite-set majorant bound in the source norm.**  For every finite set `F` of lattice
points the product majorant is bounded by the region-summed source-norm constant times the
target profile. -/
theorem sum_srcConvMajorant_le (S : SourceNormData d) (hd : 1 ≤ d) {a b ah bh : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b < (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh)
    (x : Fin d → ℤ) (F : Finset (Fin d → ℤ)) :
    ∑ y ∈ F, srcConvMajorant S a b ah bh x y ≤
      srcConvConst (d := d) S a b ah bh * srcConvTarget S a b ah bh x := by
  classical
  have hsplit1 := Finset.sum_filter_add_sum_filter_not F (fun y => srcConvReg1 S x y)
    (fun y => srcConvMajorant S a b ah bh x y)
  have hsplit2 := Finset.sum_filter_add_sum_filter_not (F.filter (fun y => ¬ srcConvReg1 S x y))
    (fun y => srcConvReg2 S x y) (fun y => srcConvMajorant S a b ah bh x y)
  have h1 := sum_srcConvReg1_le S hd ha hb hab hah hbh x (F.filter (fun y => srcConvReg1 S x y))
    (fun y hy => (Finset.mem_filter.mp hy).2)
  have h2 := sum_srcConvReg2_le S hd ha hb hab hah hbh x
    ((F.filter (fun y => ¬ srcConvReg1 S x y)).filter (fun y => srcConvReg2 S x y))
    (fun y hy => (Finset.mem_filter.mp hy).2)
  have h3 := sum_srcConvReg3_le S hd ha hb hab hah hbh x
    ((F.filter (fun y => ¬ srcConvReg1 S x y)).filter (fun y => ¬ srcConvReg2 S x y))
    (fun y hy => (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).2)
    (fun y hy => (Finset.mem_filter.mp hy).2)
  have hEq : ∑ y ∈ F, srcConvMajorant S a b ah bh x y =
      (∑ y ∈ F.filter (fun y => srcConvReg1 S x y), srcConvMajorant S a b ah bh x y) +
      ((∑ y ∈ (F.filter (fun y => ¬ srcConvReg1 S x y)).filter (fun y => srcConvReg2 S x y),
            srcConvMajorant S a b ah bh x y) +
       (∑ y ∈ (F.filter (fun y => ¬ srcConvReg1 S x y)).filter (fun y => ¬ srcConvReg2 S x y),
            srcConvMajorant S a b ah bh x y)) := by
    rw [← hsplit1, ← hsplit2]
  rw [hEq]
  refine (add_le_add h1 (add_le_add h2 h3)).trans (le_of_eq ?_)
  rw [srcConvConst]
  ring

/-! ## §2 Summability of the majorant and the `tsum` bound -/

/-- **Summability of the source-norm product majorant.** -/
theorem summable_srcConvMajorant (S : SourceNormData d) (hd : 1 ≤ d) {a b ah bh : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b < (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh)
    (x : Fin d → ℤ) :
    Summable (fun y => srcConvMajorant S a b ah bh x y) := by
  refine summable_of_sum_le
    (c := srcConvConst (d := d) S a b ah bh * srcConvTarget S a b ah bh x)
    (fun y => ?_) (fun u => ?_)
  · exact mul_nonneg (Wt_nonneg (src_nonneg S _)) (Wt_nonneg (src_nonneg S _))
  · exact sum_srcConvMajorant_le S hd ha hb hab hah hbh x u

/-- **The `tsum` majorant bound in the source norm.** -/
theorem tsum_srcConvMajorant_le (S : SourceNormData d) (hd : 1 ≤ d) {a b ah bh : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b < (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh)
    (x : Fin d → ℤ) :
    ∑' y, srcConvMajorant S a b ah bh x y ≤
      srcConvConst (d := d) S a b ah bh * srcConvTarget S a b ah bh x :=
  Summable.tsum_le_of_sum_le (summable_srcConvMajorant S hd ha hb hab hah hbh x)
    (fun u => sum_srcConvMajorant_le S hd ha hb hab hah hbh x u)

/-! ## §3 The signed convolution assembly in the source norm -/

/-- **Strict convolution assembly in an arbitrary normalized source norm.**  If the signed
functions `f` and `g` are dominated by the source-norm kernels `Wt (d-a) â (S.ρ ·)` and
`Wt (d-b) b̂ (S.ρ ·)` with `a, b > 0` and `a + b < d`, then the convolution
`Σ' y, f y * g (x - y)` is summable and bounded by

`Cf Cg (srcConvConst S a b â b̂) ⟨S.ρ x⟩^{-(d-a-b)} Λ(S.ρ x)^{-(â+b̂)}`

with a constant `srcConvConst` that depends on `S` only through `srcCountConst`,
`srcLowerUnit`, `srcUpperConst` and `srcTailConstPureLog`. -/
theorem conv_tsum_le_srcNorm (S : SourceNormData d) (hd : 1 ≤ d) {a b ah bh : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b < (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh)
    {f g : (Fin d → ℤ) → ℝ} {Cf Cg : ℝ} (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hf : ∀ y, |f y| ≤ Cf * Wt ((d : ℝ) - a) ah (S.ρ (toVec y)))
    (hg : ∀ y, |g y| ≤ Cg * Wt ((d : ℝ) - b) bh (S.ρ (toVec y))) (x : Fin d → ℤ) :
    Summable (fun y => f y * g (x - y)) ∧
      |∑' y, f y * g (x - y)| ≤
        Cf * Cg * (srcConvConst (d := d) S a b ah bh * srcConvTarget S a b ah bh x) := by
  have hmaj := summable_srcConvMajorant S hd ha hb hab hah hbh x
  have hle : ∀ y, |f y * g (x - y)| ≤ Cf * Cg * srcConvMajorant S a b ah bh x y := by
    intro y
    rw [abs_mul]
    have h1 : |f y| ≤ Cf * Wt ((d : ℝ) - a) ah (S.ρ (toVec y)) := hf y
    have h2 : |g (x - y)| ≤ Cg * Wt ((d : ℝ) - b) bh (S.ρ (toVec (x - y))) := hg (x - y)
    have hW1 : (0 : ℝ) ≤ Wt ((d : ℝ) - a) ah (S.ρ (toVec y)) := Wt_nonneg (src_nonneg S _)
    calc |f y| * |g (x - y)|
        ≤ (Cf * Wt ((d : ℝ) - a) ah (S.ρ (toVec y))) *
            (Cg * Wt ((d : ℝ) - b) bh (S.ρ (toVec (x - y)))) :=
          mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hCf hW1)
      _ = Cf * Cg * srcConvMajorant S a b ah bh x y := by
          rw [srcConvMajorant_eq]
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
      Cf * Cg * (srcConvConst (d := d) S a b ah bh * srcConvTarget S a b ah bh x) := by
    have hstep := Summable.tsum_le_tsum hle' hsumm.norm (hmaj.mul_left (Cf * Cg))
    calc ∑' y, ‖f y * g (x - y)‖
        ≤ ∑' y, Cf * Cg * srcConvMajorant S a b ah bh x y := hstep
      _ = Cf * Cg * ∑' y, srcConvMajorant S a b ah bh x y := tsum_mul_left
      _ ≤ Cf * Cg * (srcConvConst (d := d) S a b ah bh * srcConvTarget S a b ah bh x) :=
          mul_le_mul_of_nonneg_left
            (tsum_srcConvMajorant_le S hd ha hb hab hah hbh x) (mul_nonneg hCf hCg)
  exact hb1.trans hb2

/-! ## §3' Nonnegativity of the assembled constant -/

/-- The `A1` region constant is nonnegative. -/
theorem srcConvReg1Const_nonneg (S : SourceNormData d) {a b ah bh : ℝ} (hd : 1 ≤ d)
    (hab : a + b < (d : ℝ)) (hb : 0 < b) (hah : 0 ≤ ah) :
    0 ≤ srcConvReg1Const (d := d) S a b ah bh := by
  have haD : a ≤ (d : ℝ) := by linarith
  rw [srcConvReg1Const]
  refine mul_nonneg (Real.rpow_nonneg (by norm_num) _) (mul_nonneg ?_
    (Real.rpow_nonneg (by norm_num) _))
  exact srcBallShellConst_nonneg S hd haD hah

/-- The `A2` region constant is nonnegative. -/
theorem srcConvReg2Const_nonneg (S : SourceNormData d) {a b ah bh : ℝ} (hd : 1 ≤ d)
    (hab : a + b < (d : ℝ)) (ha : 0 < a) (hbh : 0 ≤ bh) :
    0 ≤ srcConvReg2Const (d := d) S a b ah bh := by
  have hbD : b ≤ (d : ℝ) := by linarith
  rw [srcConvReg2Const]
  refine mul_nonneg (Real.rpow_nonneg (by norm_num) _) (mul_nonneg ?_
    (Real.rpow_nonneg (by norm_num) _))
  exact srcBallShellConst_nonneg S hd hbD hbh

/-- The `A3` region constant of one far half is nonnegative. -/
theorem srcConvReg3aConst_nonneg (S : SourceNormData d) {a b ah bh : ℝ} (hd : 1 ≤ d)
    (hab : a + b < (d : ℝ)) (_hah : 0 ≤ ah) (_hbh : 0 ≤ bh) :
    0 ≤ srcConvReg3aConst (d := d) S a b ah bh := by
  have hγ : 0 < (d : ℝ) - a - b := by linarith
  rw [srcConvReg3aConst]
  refine mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (Real.rpow_nonneg (by norm_num) _)) (mul_nonneg (Real.rpow_nonneg (by norm_num) _) ?_)
  exact srcPowTailConst_nonneg S hd hγ

/-- The `A3` region constant is nonnegative. -/
theorem srcConvReg3Const_nonneg (S : SourceNormData d) {a b ah bh : ℝ} (hd : 1 ≤ d)
    (hab : a + b < (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh) :
    0 ≤ srcConvReg3Const (d := d) S a b ah bh := by
  rw [srcConvReg3Const]
  exact add_nonneg (srcConvReg3aConst_nonneg S hd hab hah hbh)
    (srcConvReg3aConst_nonneg S hd hab hah hbh)

/-- **The assembled source-norm constant is nonnegative.**  Hence the convolution bound of
`conv_tsum_le_srcNorm` has a nonnegative right-hand side. -/
theorem srcConvConst_nonneg (S : SourceNormData d) {a b ah bh : ℝ} (hd : 1 ≤ d)
    (ha : 0 < a) (hb : 0 < b) (hab : a + b < (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh) :
    0 ≤ srcConvConst (d := d) S a b ah bh := by
  rw [srcConvConst]
  exact add_nonneg (add_nonneg (srcConvReg1Const_nonneg S hd hab hb hah)
    (srcConvReg2Const_nonneg S hd hab ha hbh)) (srcConvReg3Const_nonneg S hd hab hah hbh)

/-- The target profile is nonnegative. -/
theorem srcConvTarget_nonneg (S : SourceNormData d) (a b ah bh : ℝ) (x : Fin d → ℤ) :
    0 ≤ srcConvTarget S a b ah bh x :=
  Wt_nonneg (src_nonneg S _)

/-! ## §3'' The source-distance form `S.dist 0 ·` -/

/-- **Strict convolution assembly stated with the source distance `S.dist 0`.**  This is
`conv_tsum_le_srcNorm` with every source norm written as the normalized source distance
`S.dist 0 y = S.ρ (toVec y)` of the model data. -/
theorem conv_tsum_le_srcDist (S : SourceNormData d) (hd : 1 ≤ d) {a b ah bh : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b < (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh)
    {f g : (Fin d → ℤ) → ℝ} {Cf Cg : ℝ} (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hf : ∀ y, |f y| ≤ Cf * Wt ((d : ℝ) - a) ah (S.dist 0 y))
    (hg : ∀ y, |g y| ≤ Cg * Wt ((d : ℝ) - b) bh (S.dist 0 y)) (x : Fin d → ℤ) :
    Summable (fun y => f y * g (x - y)) ∧
      |∑' y, f y * g (x - y)| ≤
        Cf * Cg * (srcConvConst (d := d) S a b ah bh *
          Wt ((d : ℝ) - a - b) (ah + bh) (S.dist 0 x)) := by
  have hf' : ∀ y, |f y| ≤ Cf * Wt ((d : ℝ) - a) ah (S.ρ (toVec y)) := by
    intro y
    rw [← dist_zero_eq_srcNorm]
    exact hf y
  have hg' : ∀ y, |g y| ≤ Cg * Wt ((d : ℝ) - b) bh (S.ρ (toVec y)) := by
    intro y
    rw [← dist_zero_eq_srcNorm]
    exact hg y
  obtain ⟨hsumm, hbound⟩ :=
    conv_tsum_le_srcNorm S hd ha hb hab hah hbh hCf hCg hf' hg' x
  refine ⟨hsumm, ?_⟩
  rw [srcConvTarget_eq, ← dist_zero_eq_srcNorm] at hbound
  exact hbound

/-! ## §3d A non-vacuous instance: the model kernel convolved with itself -/

/-- The source distance from the origin is nonnegative. -/
theorem srcDist_nonneg (S : SourceNormData d) (y : Fin d → ℤ) : 0 ≤ S.dist 0 y := by
  rw [← srcRadius_eq_dist]
  exact srcRadius_nonneg S y

/-- **Non-vacuity of the assembly.**  The two model kernels themselves satisfy the domination
hypotheses with constants `Cf = Cg = 1`, so the source-norm assembly applies to a genuine
nonzero pair and yields the finite `tsum` bound. -/
theorem conv_modelKernel_le_srcDist (S : SourceNormData d) (hd : 1 ≤ d) {a b ah bh : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b < (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh)
    (x : Fin d → ℤ) :
    Summable (fun y => Wt ((d : ℝ) - a) ah (S.dist 0 y) *
        Wt ((d : ℝ) - b) bh (S.dist 0 (x - y))) ∧
      |∑' y, Wt ((d : ℝ) - a) ah (S.dist 0 y) *
          Wt ((d : ℝ) - b) bh (S.dist 0 (x - y))| ≤
        1 * 1 * (srcConvConst (d := d) S a b ah bh *
          Wt ((d : ℝ) - a - b) (ah + bh) (S.dist 0 x)) := by
  have hW : ∀ (e c : ℝ), 0 ≤ Wt e c (S.dist 0 x) := by
    intro e c
    exact Wt_nonneg (srcDist_nonneg S x)
  have hf : ∀ y, |Wt ((d : ℝ) - a) ah (S.dist 0 y)| ≤
      1 * Wt ((d : ℝ) - a) ah (S.dist 0 y) := by
    intro y
    have hnn : (0 : ℝ) ≤ Wt ((d : ℝ) - a) ah (S.dist 0 y) :=
      Wt_nonneg (srcDist_nonneg S y)
    rw [abs_of_nonneg hnn, one_mul]
  have hg : ∀ y, |Wt ((d : ℝ) - b) bh (S.dist 0 y)| ≤
      1 * Wt ((d : ℝ) - b) bh (S.dist 0 y) := by
    intro y
    have hnn : (0 : ℝ) ≤ Wt ((d : ℝ) - b) bh (S.dist 0 y) :=
      Wt_nonneg (srcDist_nonneg S y)
    rw [abs_of_nonneg hnn, one_mul]
  exact conv_tsum_le_srcDist S hd ha hb hab hah hbh zero_le_one zero_le_one hf hg x

end SrcNormConv

/-! ## §4 Axiom audit -/

set_option linter.hashCommand false

#print axioms SrcNormConv.Wt_antitone
#print axioms SrcNormConv.Wt_mul_same
#print axioms SrcNormConv.srcBallShellConst_nonneg
#print axioms SrcNormConv.srcPowTailConst_nonneg
#print axioms SrcNormConv.srcBallShell_sum_le
#print axioms SrcNormConv.srcPowTail_sum_le
#print axioms SrcNormConv.srcPowTail_sum_le_sub
#print axioms SrcNormConv.toVec_add
#print axioms SrcNormConv.srcNorm_halve_le_sub
#print axioms SrcNormConv.srcNorm_halve_le_of_sub_le
#print axioms SrcNormConv.reg1_arith
#print axioms SrcNormConv.reg2_arith
#print axioms SrcNormConv.reg3_arith
#print axioms SrcNormConv.sum_srcConvReg1_le
#print axioms SrcNormConv.sum_srcConvReg2_le
#print axioms SrcNormConv.sum_srcConvReg3a_le
#print axioms SrcNormConv.sum_srcConvReg3b_le
#print axioms SrcNormConv.sum_srcConvReg3_le
#print axioms SrcNormConv.sum_srcConvMajorant_le
#print axioms SrcNormConv.summable_srcConvMajorant
#print axioms SrcNormConv.tsum_srcConvMajorant_le
#print axioms SrcNormConv.conv_tsum_le_srcNorm
#print axioms SrcNormConv.srcConvReg1Const_nonneg
#print axioms SrcNormConv.srcConvReg2Const_nonneg
#print axioms SrcNormConv.srcConvReg3aConst_nonneg
#print axioms SrcNormConv.srcConvReg3Const_nonneg
#print axioms SrcNormConv.srcConvConst_nonneg
#print axioms SrcNormConv.srcConvTarget_nonneg
#print axioms SrcNormConv.conv_tsum_le_srcDist
#print axioms SrcNormConv.srcDist_nonneg
#print axioms SrcNormConv.conv_modelKernel_le_srcDist
