module

public import PercLib.CriticalLRP.Analysis.LatticeConvolution.ConvAssembly.Main

/-!
# Generic convolution assembly: the paper's normalisation

The statement of `conv_tsum_le` rewritten with `Wt` unfolded, so that the bound reads exactly
`Cf Cg C ⟨x⟩^{-d+a+b} (log ⟨x⟩)^{-(â+b̂)}` with `⟨x⟩ = 1 + ‖x‖` and `log ⟨x⟩ = log (2 + ‖x‖)`.
This is the `a + b < d` convolution estimate of the `A1`/`A2`/`A3` split of Lemma I.4.3.
-/

set_option autoImplicit false

@[expose] public section

namespace CriticalLRPConv

/-- `Wt` written out: `⟨r⟩^{-e} (log ⟨r⟩)^{-c}`. -/
lemma Wt_eq_explicit {e c r : ℝ} :
    Wt e c r = (1 + r) ^ (-e) * (Real.log (2 + r)) ^ (-c) := rfl

/-- **Generic convolution assembly in the paper's normalisation.** -/
theorem conv_tsum_le_explicit {d : ℕ} (hd : 1 ≤ d) {a b ah bh : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b < (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh)
    {f g : (Fin d → ℤ) → ℝ} {Cf Cg : ℝ} (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hf : ∀ y, |f y| ≤ Cf * ((1 + ‖y‖) ^ (-((d : ℝ) - a)) * (Real.log (2 + ‖y‖)) ^ (-ah)))
    (hg : ∀ y, |g y| ≤ Cg * ((1 + ‖y‖) ^ (-((d : ℝ) - b)) * (Real.log (2 + ‖y‖)) ^ (-bh)))
    (x : Fin d → ℤ) :
    Summable (fun y => f y * g (x - y)) ∧
      |∑' y, f y * g (x - y)| ≤ (Cf * Cg * convConst d a b ah bh) *
        ((1 + ‖x‖) ^ (-(d : ℝ) + a + b) * (Real.log (2 + ‖x‖)) ^ (-(ah + bh))) := by
  have hmain := conv_tsum_le hd ha hb hab hah hbh hCf hCg (f := f) (g := g) hf hg x
  refine ⟨hmain.1, hmain.2.trans (le_of_eq ?_)⟩
  rw [convTarget, convTargetR, Wt, LamR]
  have h1 : (1 + ‖x‖) ^ (-((d : ℝ) - a - b)) = (1 + ‖x‖) ^ (-(d : ℝ) + a + b) := by
    congr 1
    ring
  rw [h1]
  ring

/-- **The pure kernel form**: the radial kernels themselves satisfy the convolution bound. -/
theorem tsum_kernel_le {d : ℕ} (hd : 1 ≤ d) {a b ah bh : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b < (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh) (x : Fin d → ℤ) :
    ∑' y, Wt ((d : ℝ) - a) ah ‖y‖ * Wt ((d : ℝ) - b) bh ‖(x - y : Fin d → ℤ)‖ ≤
      convConst d a b ah bh * convTarget a b ah bh x :=
  tsum_convMajorant_le hd ha hb hab hah hbh x

/-- The convolution of the radial kernels is summable. -/
theorem summable_kernel {d : ℕ} (hd : 1 ≤ d) {a b ah bh : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b < (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh) (x : Fin d → ℤ) :
    Summable (fun y => Wt ((d : ℝ) - a) ah ‖y‖ * Wt ((d : ℝ) - b) bh ‖(x - y : Fin d → ℤ)‖) :=
  summable_convMajorant hd ha hb hab hah hbh x

/-- **Generic convolution assembly without a dimension hypothesis.**  The bound `1 ≤ d` is a
consequence of `a, b > 0` and `a + b < d`, so it does not have to be assumed. -/
theorem conv_tsum_le' {d : ℕ} {a b ah bh : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b < (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh)
    {f g : (Fin d → ℤ) → ℝ} {Cf Cg : ℝ} (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hf : ∀ y, |f y| ≤ Cf * Wt ((d : ℝ) - a) ah ‖y‖)
    (hg : ∀ y, |g y| ≤ Cg * Wt ((d : ℝ) - b) bh ‖y‖) (x : Fin d → ℤ) :
    Summable (fun y => f y * g (x - y)) ∧
      |∑' y, f y * g (x - y)| ≤
        Cf * Cg * (convConst d a b ah bh * convTarget a b ah bh x) := by
  have h0 : (0 : ℝ) < (d : ℝ) := by linarith
  have hd0 : 0 < d := by exact_mod_cast h0
  exact conv_tsum_le (by omega) ha hb hab hah hbh hCf hCg hf hg x

/-- **The pure power case** (`â = b̂ = 0`): no logarithmic factor in either kernel. -/
theorem conv_tsum_le_power {d : ℕ} (hd : 1 ≤ d) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hab : a + b < (d : ℝ))
    {f g : (Fin d → ℤ) → ℝ} {Cf Cg : ℝ} (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hf : ∀ y, |f y| ≤ Cf * (1 + ‖y‖) ^ (-((d : ℝ) - a)))
    (hg : ∀ y, |g y| ≤ Cg * (1 + ‖y‖) ^ (-((d : ℝ) - b))) (x : Fin d → ℤ) :
    Summable (fun y => f y * g (x - y)) ∧
      |∑' y, f y * g (x - y)| ≤
        Cf * Cg * (convConst d a b 0 0 * (1 + ‖x‖) ^ (-((d : ℝ) - a - b))) := by
  have h := conv_tsum_le hd ha hb hab (le_refl (0:ℝ)) (le_refl (0:ℝ)) hCf hCg
    (f := f) (g := g) (fun y => by simpa [Wt] using hf y)
    (fun y => by simpa [Wt] using hg y) x
  refine ⟨h.1, h.2.trans (le_of_eq ?_)⟩
  rw [convTarget, convTargetR, Wt]
  simp only [add_zero, neg_zero, Real.rpow_zero, mul_one]

/-- **The convolution estimate with a source-level outer factor.**  Multiplying the assembly
bound by any `⟨x⟩^e (log⟨x⟩)^{-ê}` gives the displayed contribution
`⟨x⟩^{e-(d-a-b)} (log⟨x⟩)^{-(â+b̂+ê)}`.  There is no further analytic content here, but the
statement records the correspondence with the paper's use of (I.4.12) in Lean rather than
verbally. -/
theorem conv_tsum_le_sourced {d : ℕ} (hd : 1 ≤ d) {a b ah bh e eh : ℝ} (ha : 0 < a)
    (hb : 0 < b) (hab : a + b < (d : ℝ)) (hah : 0 ≤ ah) (hbh : 0 ≤ bh)
    {f g : (Fin d → ℤ) → ℝ} {Cf Cg : ℝ} (hCf : 0 ≤ Cf) (hCg : 0 ≤ Cg)
    (hf : ∀ y, |f y| ≤ Cf * Wt ((d : ℝ) - a) ah ‖y‖)
    (hg : ∀ y, |g y| ≤ Cg * Wt ((d : ℝ) - b) bh ‖y‖) (x : Fin d → ℤ) :
    (1 + ‖x‖) ^ e * LamR ‖x‖ ^ (-eh) * |∑' y, f y * g (x - y)| ≤
      Cf * Cg * convConst d a b ah bh *
        ((1 + ‖x‖) ^ (e - ((d : ℝ) - a - b)) * LamR ‖x‖ ^ (-(ah + bh + eh))) := by
  have hmain := (conv_tsum_le hd ha hb hab hah hbh hCf hCg hf hg x).2
  have hfac : (0 : ℝ) ≤ (1 + ‖x‖) ^ e * LamR ‖x‖ ^ (-eh) :=
    mul_nonneg (Real.rpow_nonneg (by linarith [norm_nonneg x]) _)
      (Real.rpow_nonneg (LamR_nonneg (norm_nonneg x)) _)
  have hbase : (0 : ℝ) < 1 + ‖x‖ := by linarith [norm_nonneg x]
  have hLam : (0 : ℝ) < LamR ‖x‖ := LamR_pos (norm_nonneg x)
  have e1 : (1 + ‖x‖) ^ e * (1 + ‖x‖) ^ (-((d : ℝ) - a - b)) =
      (1 + ‖x‖) ^ (e - ((d : ℝ) - a - b)) := by
    rw [← Real.rpow_add hbase]
    congr 1
  have e2 : LamR ‖x‖ ^ (-eh) * LamR ‖x‖ ^ (-(ah + bh)) = LamR ‖x‖ ^ (-(ah + bh + eh)) := by
    rw [← Real.rpow_add hLam]
    congr 1
    ring
  calc (1 + ‖x‖) ^ e * LamR ‖x‖ ^ (-eh) * |∑' y, f y * g (x - y)|
      ≤ (1 + ‖x‖) ^ e * LamR ‖x‖ ^ (-eh) *
          (Cf * Cg * (convConst d a b ah bh * convTarget a b ah bh x)) :=
        mul_le_mul_of_nonneg_left hmain hfac
    _ = (1 + ‖x‖) ^ e * LamR ‖x‖ ^ (-eh) *
          (Cf * Cg * (convConst d a b ah bh *
            ((1 + ‖x‖) ^ (-((d : ℝ) - a - b)) * LamR ‖x‖ ^ (-(ah + bh))))) := by
        rw [convTarget, convTargetR, Wt]
    _ = Cf * Cg * convConst d a b ah bh *
          (((1 + ‖x‖) ^ e * (1 + ‖x‖) ^ (-((d : ℝ) - a - b))) *
            (LamR ‖x‖ ^ (-eh) * LamR ‖x‖ ^ (-(ah + bh)))) := by ring
    _ = Cf * Cg * convConst d a b ah bh *
          ((1 + ‖x‖) ^ (e - ((d : ℝ) - a - b)) * LamR ‖x‖ ^ (-(ah + bh + eh))) := by
        rw [e1, e2]

end CriticalLRPConv

/-! ## Axiom audit -/

set_option linter.hashCommand false

#print axioms CriticalLRPConv.Wt_eq_explicit
#print axioms CriticalLRPConv.conv_tsum_le_explicit
#print axioms CriticalLRPConv.tsum_kernel_le
#print axioms CriticalLRPConv.summable_kernel
#print axioms CriticalLRPConv.conv_tsum_le'
#print axioms CriticalLRPConv.conv_tsum_le_power
#print axioms CriticalLRPConv.conv_tsum_le_sourced
