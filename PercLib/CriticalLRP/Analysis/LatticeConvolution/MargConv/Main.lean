module

public import PercLib.CriticalLRP.Analysis.LatticeConvolution.MargConv.Regions
public import PercLib.CriticalLRP.Analysis.LatticeConvolution.ConvAssembly.PaperForm
public import PercLib.CriticalLRP.Analysis.LatticeConvolution.WeightLp

/-!
# The marginal (`a + b = d`) convolution assembly

Assembly of the three region bounds of `MargConv.Regions` into the marginal convolution
estimate: for signed `f, g` dominated by `Cf · Wt (d-a) â` and `Cg · Wt (d-b) b̂` with
`a, b > 0`, `a + b = d` and `â + b̂ > 1`, the series `Σ' y, f y * g (x-y)` is summable and

`|Σ' y, f y * g (x-y)| ≤ Cf Cg C (log (2 + ‖x‖))^{-(â+b̂)+1}`

with `C = margConst d a b â b̂` independent of `x`, `f` and `g`.

The exponent `-(â+b̂)+1` is sharp for this method: the `A3` region only converges
logarithmically, and `sum_Wt_tail_le_pureLog` shows that `Λ^{-(â+b̂)}` is *not* attainable.
-/

set_option autoImplicit false

@[expose] public section

namespace CriticalLRPConv

open PercLib.CriticalLRP.FiniteVolume (linfNorm)

/-! ## §1 The finite-set convolution majorant bound -/

/-- **The finite-set marginal convolution majorant bound.**  For every finite set `F` of lattice
points the product weight is bounded by the region-summed constant times the marginal target
profile. -/
theorem sum_convMajorant_le_marg {d : ℕ} (hd : 1 ≤ d) {a b ah bh : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh) (hS : 1 < ah + bh)
    (x : Fin d → ℤ) (F : Finset (Fin d → ℤ)) :
    ∑ y ∈ F, convMajorant a b ah bh x y ≤ margConst d a b ah bh * margTarget ah bh x := by
  classical
  have hsplit1 := Finset.sum_filter_add_sum_filter_not F (fun y => convReg1 x y)
    (fun y => convMajorant a b ah bh x y)
  have hsplit2 := Finset.sum_filter_add_sum_filter_not (F.filter (fun y => ¬ convReg1 x y))
    (fun y => convReg2 x y) (fun y => convMajorant a b ah bh x y)
  have h1 := sum_convReg1_le_marg (d := d) ha hb hab hah hbh x (F.filter (fun y => convReg1 x y))
    (fun y hy => (Finset.mem_filter.mp hy).2)
  have h2 := sum_convReg2_le_marg (d := d) ha hb hab hah hbh x
    ((F.filter (fun y => ¬ convReg1 x y)).filter (fun y => convReg2 x y))
    (fun y hy => (Finset.mem_filter.mp hy).2)
  have h3 := sum_convReg3_le_marg (d := d) hd ha hb hab hah hbh hS x
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
  rw [margConst]
  ring

/-! ## §2 Summability of the majorant and the `tsum` bound -/

/-- **Summability of the marginal product majorant.** -/
theorem summable_convMajorant_marg {d : ℕ} (hd : 1 ≤ d) {a b ah bh : ℝ} (ha : 0 < a)
    (hb : 0 < b) (hab : a + b = (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh) (hS : 1 < ah + bh)
    (x : Fin d → ℤ) : Summable (fun y => convMajorant a b ah bh x y) := by
  refine summable_of_sum_le (c := margConst d a b ah bh * margTarget ah bh x)
    (fun y => ?_) (fun u => ?_)
  · exact mul_nonneg (Wt_nonneg (norm_nonneg y)) (Wt_nonneg (norm_nonneg _))
  · exact sum_convMajorant_le_marg hd ha hb hab hah hbh hS x u

/-- **The `tsum` of the marginal product majorant.** -/
theorem tsum_convMajorant_le_marg {d : ℕ} (hd : 1 ≤ d) {a b ah bh : ℝ} (ha : 0 < a)
    (hb : 0 < b) (hab : a + b = (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh) (hS : 1 < ah + bh)
    (x : Fin d → ℤ) :
    ∑' y, convMajorant a b ah bh x y ≤ margConst d a b ah bh * margTarget ah bh x :=
  Summable.tsum_le_of_sum_le (summable_convMajorant_marg hd ha hb hab hah hbh hS x)
    (fun u => sum_convMajorant_le_marg hd ha hb hab hah hbh hS x u)

/-! ## §3 The marginal convolution assembly for signed functions -/

/-- **Marginal convolution assembly (`a + b = d`).**  If `f` and `g` are dominated by the
radial kernels `Wt (d-a) â` and `Wt (d-b) b̂` with `a, b > 0`, `a + b = d` and `â, b̂ ≥ 0`,
`1 < â + b̂`, then the convolution `Σ' y, f y * g (x - y)` is summable and bounded by
`Cf Cg C (log (2 + ‖x‖))^{-(â+b̂)+1}` with a constant `C` uniform in `x`. -/
theorem conv_tsum_le_marg {d : ℕ} (hd : 1 ≤ d) {a b ah bh : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh) (hS : 1 < ah + bh)
    {f g : (Fin d → ℤ) → ℝ} {Cf Cg : ℝ} (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hf : ∀ y, |f y| ≤ Cf * Wt ((d : ℝ) - a) ah ‖y‖)
    (hg : ∀ y, |g y| ≤ Cg * Wt ((d : ℝ) - b) bh ‖y‖) (x : Fin d → ℤ) :
    Summable (fun y => f y * g (x - y)) ∧
      |∑' y, f y * g (x - y)| ≤
        Cf * Cg * (margConst d a b ah bh * margTarget ah bh x) := by
  have hmaj := summable_convMajorant_marg hd ha hb hab hah hbh hS x
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
      Cf * Cg * (margConst d a b ah bh * margTarget ah bh x) := by
    have hstep := Summable.tsum_le_tsum hle hsumm.norm (hmaj.mul_left (Cf * Cg))
    calc ∑' y, ‖f y * g (x - y)‖ ≤ ∑' y, Cf * Cg * convMajorant a b ah bh x y := hstep
      _ = Cf * Cg * ∑' y, convMajorant a b ah bh x y := tsum_mul_left
      _ ≤ Cf * Cg * (margConst d a b ah bh * margTarget ah bh x) :=
          mul_le_mul_of_nonneg_left (tsum_convMajorant_le_marg hd ha hb hab hah hbh hS x)
            (mul_nonneg hCf hCg)
  exact hb1.trans hb2

/-! ## §4 The paper's normalisation -/

/-- **The marginal convolution estimate in the paper's normalisation.**  The bound reads
`Cf Cg C (log (2 + ‖x‖))^{-(â+b̂)+1}`, i.e. `… (log⟨x⟩)^{1-(â+b̂)}`. -/
theorem conv_tsum_le_marg_explicit {d : ℕ} (hd : 1 ≤ d) {a b ah bh : ℝ} (ha : 0 < a)
    (hb : 0 < b) (hab : a + b = (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh) (hS : 1 < ah + bh)
    {f g : (Fin d → ℤ) → ℝ} {Cf Cg : ℝ} (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hf : ∀ y, |f y| ≤ Cf * ((1 + ‖y‖) ^ (-((d : ℝ) - a)) * (Real.log (2 + ‖y‖)) ^ (-ah)))
    (hg : ∀ y, |g y| ≤ Cg * ((1 + ‖y‖) ^ (-((d : ℝ) - b)) * (Real.log (2 + ‖y‖)) ^ (-bh)))
    (x : Fin d → ℤ) :
    Summable (fun y => f y * g (x - y)) ∧
      |∑' y, f y * g (x - y)| ≤ (Cf * Cg * margConst d a b ah bh) *
        (Real.log (2 + ‖x‖)) ^ (-(ah + bh) + 1) := by
  have hmain := conv_tsum_le_marg hd ha hb hab hah hbh hS hCf hCg
    (f := f) (g := g) (fun y => by simpa [Wt_eq_explicit] using hf y)
    (fun y => by simpa [Wt_eq_explicit] using hg y) x
  refine ⟨hmain.1, hmain.2.trans (le_of_eq ?_)⟩
  rw [margTarget_eq_explicit]
  have hexp : 1 - (ah + bh) = -(ah + bh) + 1 := by ring
  rw [hexp]
  ring

/-- **The marginal assembly for the radial kernels themselves.** -/
theorem tsum_kernel_le_marg {d : ℕ} (hd : 1 ≤ d) {a b ah bh : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh) (hS : 1 < ah + bh)
    (x : Fin d → ℤ) :
    ∑' y, Wt ((d : ℝ) - a) ah ‖y‖ * Wt ((d : ℝ) - b) bh ‖(x - y : Fin d → ℤ)‖ ≤
      margConst d a b ah bh * margTarget ah bh x :=
  tsum_convMajorant_le_marg hd ha hb hab hah hbh hS x

/-! ## §5 Nonnegativity of the assembled constant -/

/-- The assembled constant of the marginal estimate is nonnegative. -/
theorem margConst_nonneg' {d : ℕ} (hd : 1 ≤ d) {a b ah bh : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh) (hS : 1 < ah + bh) :
    0 ≤ margConst d a b ah bh :=
  margConst_nonneg hd ha hb hab hah hbh hS

/-! ## §6 The marginal exponent threshold is sharp -/

/-- **The model majorant at the origin is the marginal weight.**  With `a + b = d`,
`convMajorant a b â b̂ 0 y = Wt d (â+b̂) ‖y‖`: the two power factors add up to `d` exactly. -/
lemma convMajorant_zero {d : ℕ} {a b ah bh : ℝ} (hab : a + b = (d : ℝ)) (y : Fin d → ℤ) :
    convMajorant a b ah bh (0 : Fin d → ℤ) y = Wt (d : ℝ) (ah + bh) ‖y‖ := by
  have hneg : ‖((0 : Fin d → ℤ) - y)‖ = ‖y‖ := by
    rw [zero_sub, norm_neg]
  have hy0 : (0 : ℝ) ≤ ‖y‖ := norm_nonneg y
  have hbase : (0 : ℝ) < 1 + ‖y‖ := by linarith
  have e1 : (1 + ‖y‖) ^ (-((d : ℝ) - a)) * (1 + ‖y‖) ^ (-((d : ℝ) - b)) =
      (1 + ‖y‖) ^ (-(d : ℝ)) := by
    rw [← Real.rpow_add hbase]
    congr 1
    linarith
  have e2 : LamR ‖y‖ ^ (-ah) * LamR ‖y‖ ^ (-bh) = LamR ‖y‖ ^ (-(ah + bh)) := by
    rw [← Real.rpow_add (LamR_pos hy0)]
    congr 1
    ring
  have hmain : convMajorant a b ah bh (0 : Fin d → ℤ) y =
      ((1 + ‖y‖) ^ (-((d : ℝ) - a)) * LamR ‖y‖ ^ (-ah)) *
        ((1 + ‖y‖) ^ (-((d : ℝ) - b)) * LamR ‖y‖ ^ (-bh)) := by
    simp only [convMajorant, Wt, hneg]
  calc convMajorant a b ah bh (0 : Fin d → ℤ) y
      = ((1 + ‖y‖) ^ (-((d : ℝ) - a)) * LamR ‖y‖ ^ (-ah)) *
          ((1 + ‖y‖) ^ (-((d : ℝ) - b)) * LamR ‖y‖ ^ (-bh)) := hmain
    _ = Wt (d : ℝ) (ah + bh) ‖y‖ := by
        rw [Wt, ← e1, ← e2]
        ring

/-- **The threshold `â + b̂ > 1` is necessary.**  In the marginal case `a + b = d` the product
majorant at `x = 0` is the pure marginal weight `Wt d (â+b̂)`, which is *not* summable when
`â + b̂ ≤ 1` (`CriticalLRPConv.not_summable_Wt_marginal`).  So the marginal assembly cannot be
run with the strict-case exponent `-(â+b̂)`, and `â + b̂ > 1` is not a technical convenience:
for `â + b̂ ≤ 1` the `A3` region diverges. -/
theorem not_summable_convMajorant_marg {d : ℕ} (hd : 0 < d) {a b ah bh : ℝ} (_ha : 0 < a)
    (_hb : 0 < b) (hab : a + b = (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh) (hc : ah + bh ≤ 1) :
    ¬ Summable (fun y => convMajorant a b ah bh (0 : Fin d → ℤ) y) := by
  intro hS
  have hW : Summable (fun y : Fin d → ℤ => Wt (d : ℝ) (ah + bh) (↑(linfNorm y) : ℝ)) := by
    refine hS.congr (fun y => ?_)
    rw [convMajorant_zero hab, coe_norm_eq_linfNorm]
  exact not_summable_Wt_marginal hd (by linarith) hc hW

/-! ## §7 Further specialisations -/

/-- **Marginal convolution assembly without a dimension hypothesis.**  The bound `1 ≤ d` is a
consequence of `a, b > 0` and `a + b = d`, so it need not be assumed. -/
theorem conv_tsum_le_marg' {d : ℕ} {a b ah bh : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b = (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh) (hS : 1 < ah + bh)
    {f g : (Fin d → ℤ) → ℝ} {Cf Cg : ℝ} (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hf : ∀ y, |f y| ≤ Cf * Wt ((d : ℝ) - a) ah ‖y‖)
    (hg : ∀ y, |g y| ≤ Cg * Wt ((d : ℝ) - b) bh ‖y‖) (x : Fin d → ℤ) :
    Summable (fun y => f y * g (x - y)) ∧
      |∑' y, f y * g (x - y)| ≤
        Cf * Cg * (margConst d a b ah bh * margTarget ah bh x) := by
  have h0 : (0 : ℝ) < (d : ℝ) := by linarith
  have hd0 : 0 < d := by exact_mod_cast h0
  exact conv_tsum_le_marg (by omega) ha hb hab hah hbh hS hCf hCg hf hg x

/-- **The marginal estimate with a source-level outer factor.**  Multiplying the assembly bound
by any `⟨x⟩^e Λ(x)^{-ê}` gives `⟨x⟩^e Λ(x)^{1-(â+b̂)-ê}`; there is no further analytic
content, only the correspondence with how the marginal convolution estimate is used in the
source. -/
theorem conv_tsum_le_marg_sourced {d : ℕ} (hd : 1 ≤ d) {a b ah bh e eh : ℝ} (ha : 0 < a)
    (hb : 0 < b) (hab : a + b = (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh) (hS : 1 < ah + bh)
    {f g : (Fin d → ℤ) → ℝ} {Cf Cg : ℝ} (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hf : ∀ y, |f y| ≤ Cf * Wt ((d : ℝ) - a) ah ‖y‖)
    (hg : ∀ y, |g y| ≤ Cg * Wt ((d : ℝ) - b) bh ‖y‖) (x : Fin d → ℤ) :
    (1 + ‖x‖) ^ e * LamR ‖x‖ ^ (-eh) * |∑' y, f y * g (x - y)| ≤
      Cf * Cg * margConst d a b ah bh *
        ((1 + ‖x‖) ^ e * LamR ‖x‖ ^ (1 - (ah + bh) - eh)) := by
  have hmain := (conv_tsum_le_marg hd ha hb hab hah hbh hS hCf hCg hf hg x).2
  have hx : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
  have hfac : (0 : ℝ) ≤ (1 + ‖x‖) ^ e * LamR ‖x‖ ^ (-eh) :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _)
      (Real.rpow_nonneg (LamR_nonneg hx) _)
  have hLam : (0 : ℝ) < LamR ‖x‖ := LamR_pos hx
  have hcomb : LamR ‖x‖ ^ (-eh) * LamR ‖x‖ ^ (1 - (ah + bh)) =
      LamR ‖x‖ ^ (1 - (ah + bh) - eh) := by
    rw [← Real.rpow_add hLam]
    congr 1
    ring
  calc (1 + ‖x‖) ^ e * LamR ‖x‖ ^ (-eh) * |∑' y, f y * g (x - y)|
      ≤ (1 + ‖x‖) ^ e * LamR ‖x‖ ^ (-eh) *
          (Cf * Cg * (margConst d a b ah bh * margTarget ah bh x)) :=
        mul_le_mul_of_nonneg_left hmain hfac
    _ = Cf * Cg * margConst d a b ah bh *
          ((1 + ‖x‖) ^ e * (LamR ‖x‖ ^ (-eh) * LamR ‖x‖ ^ (1 - (ah + bh)))) := by
        rw [margTarget_eq_explicit, LamR_def]
        ring
    _ = Cf * Cg * margConst d a b ah bh *
          ((1 + ‖x‖) ^ e * LamR ‖x‖ ^ (1 - (ah + bh) - eh)) := by rw [hcomb]

/-- **Complete characterisation at the origin.**  In the marginal case the model majorant at
`x = 0` is summable **iff** `â + b̂ > 1`: the `A3` region is exactly at the threshold of the
sharp power–log summability criterion of `WeightLp`. -/
theorem summable_convMajorant_zero_iff {d : ℕ} (hd : 0 < d) {a b ah bh : ℝ} (_ha : 0 < a)
    (_hb : 0 < b) (hab : a + b = (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh) :
    Summable (fun y => convMajorant a b ah bh (0 : Fin d → ℤ) y) ↔ 1 < ah + bh := by
  constructor
  · intro hS
    by_contra hcon
    exact not_summable_convMajorant_marg hd _ha _hb hab hah hbh (not_lt.mp hcon) hS
  · intro hc
    have hW : Summable (fun y : Fin d → ℤ => Wt (d : ℝ) (ah + bh) (↑(linfNorm y) : ℝ)) :=
      summable_Wt_marginal hd hc
    refine hW.congr (fun y => ?_)
    rw [convMajorant_zero hab, coe_norm_eq_linfNorm]

end CriticalLRPConv

/-! ## Axiom audit -/

set_option linter.hashCommand false

#print axioms CriticalLRPConv.sum_convMajorant_le_marg
#print axioms CriticalLRPConv.summable_convMajorant_marg
#print axioms CriticalLRPConv.tsum_convMajorant_le_marg
#print axioms CriticalLRPConv.conv_tsum_le_marg
#print axioms CriticalLRPConv.conv_tsum_le_marg_explicit
#print axioms CriticalLRPConv.tsum_kernel_le_marg
#print axioms CriticalLRPConv.margConst_nonneg'
#print axioms CriticalLRPConv.convMajorant_zero
#print axioms CriticalLRPConv.not_summable_convMajorant_marg
#print axioms CriticalLRPConv.conv_tsum_le_marg'
#print axioms CriticalLRPConv.conv_tsum_le_marg_sourced
#print axioms CriticalLRPConv.summable_convMajorant_zero_iff
