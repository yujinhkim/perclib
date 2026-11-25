module

public import PercLib.CriticalLRP.Analysis.LatticeConvolution.ConvAssembly.Regions

/-!
# Generic convolution assembly (`a + b < d`): summability and the full bound
-/

set_option autoImplicit false

@[expose] public section

namespace CriticalLRPConv

/-! ## §10 The finite-set convolution majorant bound -/

/-- **The finite-set convolution majorant bound.**  For every finite set `F` of lattice points
the product weight is bounded by the region-summed constant times the target profile. -/
theorem sum_convMajorant_le {d : ℕ} (hd : 1 ≤ d) {a b ah bh : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b < (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh) (x : Fin d → ℤ)
    (F : Finset (Fin d → ℤ)) :
    ∑ y ∈ F, convMajorant a b ah bh x y ≤ convConst d a b ah bh * convTarget a b ah bh x := by
  classical
  have hsplit1 := Finset.sum_filter_add_sum_filter_not F (fun y => convReg1 x y)
    (fun y => convMajorant a b ah bh x y)
  have hsplit2 := Finset.sum_filter_add_sum_filter_not (F.filter (fun y => ¬ convReg1 x y))
    (fun y => convReg2 x y) (fun y => convMajorant a b ah bh x y)
  have h1 := sum_convReg1_le ha hb hab hah hbh x (F.filter (fun y => convReg1 x y))
    (fun y hy => (Finset.mem_filter.mp hy).2)
  have h2 := sum_convReg2_le ha hb hab hah hbh x
    ((F.filter (fun y => ¬ convReg1 x y)).filter (fun y => convReg2 x y))
    (fun y hy => (Finset.mem_filter.mp hy).2)
  have h3 := sum_convReg3_le hd ha hb hab hah hbh x
    ((F.filter (fun y => ¬ convReg1 x y)).filter (fun y => ¬ convReg2 x y))
    (fun y hy => (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).2)
    (fun y hy => (Finset.mem_filter.mp hy).2)
  have hEq : ∑ y ∈ F, convMajorant a b ah bh x y =
      (∑ y ∈ F.filter (fun y => convReg1 x y), convMajorant a b ah bh x y) +
      ((∑ y ∈ (F.filter (fun y => ¬ convReg1 x y)).filter (fun y => convReg2 x y),
            convMajorant a b ah bh x y) +
       (∑ y ∈ (F.filter (fun y => ¬ convReg1 x y)).filter (fun y => ¬ convReg2 x y),
            convMajorant a b ah bh x y)) := by
    rw [← hsplit1, ← hsplit2]
  rw [hEq]
  refine (add_le_add h1 (add_le_add h2 h3)).trans (le_of_eq ?_)
  rw [convConst, convTarget_eq]
  ring

/-! ## §11 Summability of the majorant and the `tsum` bound -/

/-- **Summability of the product majorant.** -/
theorem summable_convMajorant {d : ℕ} (hd : 1 ≤ d) {a b ah bh : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b < (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh) (x : Fin d → ℤ) :
    Summable (fun y => convMajorant a b ah bh x y) := by
  refine summable_of_sum_le (c := convConst d a b ah bh * convTarget a b ah bh x)
    (fun y => ?_) (fun u => ?_)
  · exact mul_nonneg (Wt_nonneg (norm_nonneg y)) (Wt_nonneg (norm_nonneg _))
  · exact sum_convMajorant_le hd ha hb hab hah hbh x u

/-- **The `tsum` convolution majorant bound.** -/
theorem tsum_convMajorant_le {d : ℕ} (hd : 1 ≤ d) {a b ah bh : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b < (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh) (x : Fin d → ℤ) :
    ∑' y, convMajorant a b ah bh x y ≤ convConst d a b ah bh * convTarget a b ah bh x :=
  Summable.tsum_le_of_sum_le (summable_convMajorant hd ha hb hab hah hbh x)
    (fun u => sum_convMajorant_le hd ha hb hab hah hbh x u)

/-! ## §12 The generic convolution assembly -/

/-- **Generic convolution assembly for `a + b < d`.**  If `f` and `g` are dominated by the radial
kernels `Wt (d-a) â` and `Wt (d-b) b̂` with `a, b > 0`, `a + b < d`, then the convolution
`Σ' y, f y * g (x - y)` is summable and bounded by
`Cf Cg C ⟨x⟩^{-(d-a-b)} (log⟨x⟩)^{-(â+b̂)}` with a constant `C` uniform in `x`. -/
theorem conv_tsum_le {d : ℕ} (hd : 1 ≤ d) {a b ah bh : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b < (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh)
    {f g : (Fin d → ℤ) → ℝ} {Cf Cg : ℝ} (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hf : ∀ y, |f y| ≤ Cf * Wt ((d : ℝ) - a) ah ‖y‖)
    (hg : ∀ y, |g y| ≤ Cg * Wt ((d : ℝ) - b) bh ‖y‖) (x : Fin d → ℤ) :
    Summable (fun y => f y * g (x - y)) ∧
      |∑' y, f y * g (x - y)| ≤
        Cf * Cg * (convConst d a b ah bh * convTarget a b ah bh x) := by
  have hmaj := summable_convMajorant hd ha hb hab hah hbh x
  have hle : ∀ y, ‖f y * g (x - y)‖ ≤ Cf * Cg * convMajorant a b ah bh x y := by
    intro y
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |f y| ≤ Cf * Wt ((d : ℝ) - a) ah ‖y‖ := hf y
    have h2 : |g (x - y)| ≤ Cg * Wt ((d : ℝ) - b) bh ‖(x - y : Fin d → ℤ)‖ := hg (x - y)
    have hW1 : (0 : ℝ) ≤ Wt ((d : ℝ) - a) ah ‖y‖ := Wt_nonneg (norm_nonneg y)
    calc |f y| * |g (x - y)|
        ≤ (Cf * Wt ((d : ℝ) - a) ah ‖y‖) *
            (Cg * Wt ((d : ℝ) - b) bh ‖(x - y : Fin d → ℤ)‖) :=
          mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hCf hW1)
      _ = Cf * Cg * convMajorant a b ah bh x y := by
          rw [convMajorant]
          ring
  have hsumm : Summable (fun y => f y * g (x - y)) :=
    Summable.of_norm_bounded (hmaj.mul_left (Cf * Cg)) hle
  refine ⟨hsumm, ?_⟩
  have hb1 : |∑' y, f y * g (x - y)| ≤ ∑' y, ‖f y * g (x - y)‖ := by
    rw [← Real.norm_eq_abs]
    exact norm_tsum_le_tsum_norm hsumm.norm
  have hb2 : ∑' y, ‖f y * g (x - y)‖ ≤
      Cf * Cg * (convConst d a b ah bh * convTarget a b ah bh x) := by
    have hstep := Summable.tsum_le_tsum hle hsumm.norm (hmaj.mul_left (Cf * Cg))
    calc ∑' y, ‖f y * g (x - y)‖ ≤ ∑' y, Cf * Cg * convMajorant a b ah bh x y := hstep
      _ = Cf * Cg * ∑' y, convMajorant a b ah bh x y := tsum_mul_left
      _ ≤ Cf * Cg * (convConst d a b ah bh * convTarget a b ah bh x) :=
          mul_le_mul_of_nonneg_left (tsum_convMajorant_le hd ha hb hab hah hbh x)
            (mul_nonneg hCf hCg)
  exact hb1.trans hb2

end CriticalLRPConv

/-! ## §13 Axiom audit -/

set_option linter.hashCommand false

#print axioms CriticalLRPConv.coe_norm_eq_linfNorm
#print axioms CriticalLRPConv.LamR_halve
#print axioms CriticalLRPConv.LamR_rpow_halve_le
#print axioms CriticalLRPConv.LamR_rpow_freeze
#print axioms CriticalLRPConv.one_add_halve_rpow_le
#print axioms CriticalLRPConv.one_add_rpow_freeze
#print axioms CriticalLRPConv.Wt_freeze_halve
#print axioms CriticalLRPConv.ball_profile_halve
#print axioms CriticalLRPConv.ballShellConst_nonneg
#print axioms CriticalLRPConv.norm_half_le_norm_sub
#print axioms CriticalLRPConv.ball_shell_bound_centred
#print axioms CriticalLRPConv.sum_Wt_tail_le_norm
#print axioms CriticalLRPConv.sum_convReg1_le
#print axioms CriticalLRPConv.norm_half_le_norm_of_sub_le
#print axioms CriticalLRPConv.sum_convReg2_le
#print axioms CriticalLRPConv.Wt_zero_log
#print axioms CriticalLRPConv.one_add_halve_rpow_le_neg
#print axioms CriticalLRPConv.sum_pow_tail_le
#print axioms CriticalLRPConv.sum_pow_tail_le_sub
#print axioms CriticalLRPConv.sum_convReg3a_le
#print axioms CriticalLRPConv.sum_convReg3b_le
#print axioms CriticalLRPConv.sum_convReg3_le
#print axioms CriticalLRPConv.sum_convMajorant_le
#print axioms CriticalLRPConv.summable_convMajorant
#print axioms CriticalLRPConv.tsum_convMajorant_le
#print axioms CriticalLRPConv.conv_tsum_le
