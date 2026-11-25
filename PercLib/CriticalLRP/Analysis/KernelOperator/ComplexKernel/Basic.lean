/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

The complex Schur kernel operator on complex `ℓ²`: construction, norm bound, and agreement
with the real kernel operator on real-valued vectors.

Swarm `smwtxo95t`, member `m1`, direction (D) "concrete complex kernel operator".

`Operator.lean`/`LpOperator.lean` build `kernelCLM h : lp (V, ℝ) 2 →L[ℝ] lp (V, ℝ) 2` from a
`SchurKernel κ A`.  Here the same column-sum argument is run over `ℂ`: the complex kernel
series of an `ℓ²` function is summable, its squared `ℓ²` mass is at most `A² ‖f‖²` (via the
real Schur bound applied to `‖f‖`), and the resulting `ℂ`-linear map is a genuine bounded
operator `kernelCLMℂ h` of norm at most `A`.  Its values on real-valued `ℓ²` functions are
those of the real operator, which is the extension property consumed downstream by the
realification bridge of `CFC.lean`.
-/
module

public import PercLib.CriticalLRP.Analysis.KernelOperator.LpOperator
public import PercLib.CriticalLRP.Analysis.KernelOperator.CFC.Defs
public import PercLib.CriticalLRP.Analysis.KernelOperator.ComplexKernel.Defs

/-!
# The complex Schur kernel operator

Everything here is conditional on the same `SchurKernel κ A` hypothesis as the real operator;
no critical-norm input and no positivity is assumed.
-/

@[expose] public section

noncomputable section

open scoped ENNReal NNReal lp

namespace PercLib.CriticalLRP.KernelOperator

variable {V : Type*} {κ : V → V → ℝ} {A : ℝ}

/-! ### The `ℓ²` mass of a complex `ℓ²` function -/

/-- A complex `ℓ²` function has summable squared norm. -/
theorem summable_norm_sq_of_memℓp (f : lp (fun _ : V => ℂ) 2) :
    Summable fun y => ‖(f : V → ℂ) y‖ ^ 2 := by
  have h := (lp.memℓp f).summable (p := 2) (by norm_num : 0 < ((2 : ℝ≥0∞)).toReal)
  have h2 : ((2 : ℝ≥0∞)).toReal = 2 := by norm_num
  rw [h2] at h
  simpa only [Real.rpow_two] using h

/-! ### Row summability -/

/-- **Rows against complex `ℓ²` data are summable.**  The row of the kernel is summable
against `‖f‖` by the real Schur lemma, hence against the complex series by comparison of
norms. -/
theorem summable_row_mul_complex (h : SchurKernel κ A) {f : V → ℂ}
    (hfs : Summable fun y => ‖f y‖ ^ 2) (x : V) :
    Summable fun y => (κ x y : ℂ) * f y := by
  have hdom : Summable fun y => κ x y * ‖f y‖ := by
    refine (schur_summable_row_mul_abs h (g := fun y => ‖f y‖) hfs x).congr fun y => ?_
    rw [abs_of_nonneg (norm_nonneg _)]
  refine Summable.of_norm ?_
  refine hdom.congr fun y => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h.nonneg x y)]

/-- **The triangle step**: the norm of the complex kernel series is at most the real kernel
series of the norm. -/
theorem norm_kernelApplyℂ_le_kernelApply_norm (h : SchurKernel κ A) {f : V → ℂ}
    (hfs : Summable fun y => ‖f y‖ ^ 2) (x : V) :
    ‖kernelApplyℂ κ f x‖ ≤ kernelApply κ (fun y => ‖f y‖) x := by
  have hnorm : Summable fun y => ‖(κ x y : ℂ) * f y‖ :=
    (summable_row_mul_complex h hfs x).norm
  have h1 : ‖∑' y, (κ x y : ℂ) * f y‖ ≤ ∑' y, ‖(κ x y : ℂ) * f y‖ :=
    norm_tsum_le_tsum_norm hnorm
  have h2 : (∑' y, ‖(κ x y : ℂ) * f y‖) = ∑' y, κ x y * ‖f y‖ := by
    refine tsum_congr fun y => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h.nonneg x y)]
  rw [h2] at h1
  simpa only [kernelApply, kernelApplyℂ] using h1

/-! ### The Schur bound on complex `ℓ²` -/

/-- **The complex Schur bound**: the kernel series of a complex `ℓ²` function is square
summable with squared mass at most `A²` times the squared mass of the input.  The proof
compares with the real nonnegative Schur bound at `‖f‖`, so no new Cauchy–Schwarz argument
is needed. -/
theorem tsum_sq_kernelApplyℂ_le (h : SchurKernel κ A) (f : lp (fun _ : V => ℂ) 2) :
    Summable (fun x => ‖kernelApplyℂ κ (f : V → ℂ) x‖ ^ 2) ∧
      ∑' x, ‖kernelApplyℂ κ (f : V → ℂ) x‖ ^ 2
        ≤ A ^ 2 * ∑' y, ‖(f : V → ℂ) y‖ ^ 2 := by
  have hfs : Summable fun y => ‖(f : V → ℂ) y‖ ^ 2 := summable_norm_sq_of_memℓp f
  obtain ⟨hsq, hle⟩ := schur_tsum_sq_kernelApply_le_of_nonneg h
    (f := fun y => ‖(f : V → ℂ) y‖) (fun y => norm_nonneg _) hfs
  have hpt : ∀ x, ‖kernelApplyℂ κ (f : V → ℂ) x‖ ^ 2
      ≤ kernelApply κ (fun y => ‖(f : V → ℂ) y‖) x ^ 2 := by
    intro x
    have h1 := norm_kernelApplyℂ_le_kernelApply_norm h hfs x
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  refine ⟨Summable.of_nonneg_of_le (fun x => sq_nonneg _) hpt hsq, ?_⟩
  exact le_trans (Summable.tsum_le_tsum hpt
    (Summable.of_nonneg_of_le (fun x => sq_nonneg _) hpt hsq) hsq) hle

/-- **The complex kernel series of an `ℓ²` function is again in `ℓ²`.** -/
theorem memℓp_kernelApplyℂ (h : SchurKernel κ A) (f : lp (fun _ : V => ℂ) 2) :
    Memℓp (fun x => kernelApplyℂ κ (f : V → ℂ) x) 2 := by
  refine memℓp_gen ?_
  have hb := (tsum_sq_kernelApplyℂ_le h f).1
  have h2 : ((2 : ℝ≥0∞)).toReal = 2 := by norm_num
  simpa only [h2, Real.rpow_two] using hb

/-! ### The operator on complex `ℓ²` -/

/-- The complex kernel operator as a self-map of complex `ℓ²`. -/
noncomputable def kernelLpℂ (h : SchurKernel κ A) (f : lp (fun _ : V => ℂ) 2) :
    lp (fun _ : V => ℂ) 2 :=
  ⟨fun x => kernelApplyℂ κ (f : V → ℂ) x, memℓp_kernelApplyℂ h f⟩

@[simp]
theorem kernelLpℂ_apply (h : SchurKernel κ A) (f : lp (fun _ : V => ℂ) 2) (x : V) :
    (kernelLpℂ h f : V → ℂ) x = kernelApplyℂ κ (f : V → ℂ) x := rfl

theorem kernelLpℂ_add (h : SchurKernel κ A) (f g : lp (fun _ : V => ℂ) 2) :
    kernelLpℂ h (f + g) = kernelLpℂ h f + kernelLpℂ h g := by
  refine lp.ext ?_
  funext x
  have hf : Summable fun y => ‖(f : V → ℂ) y‖ ^ 2 := summable_norm_sq_of_memℓp f
  have hg : Summable fun y => ‖(g : V → ℂ) y‖ ^ 2 := summable_norm_sq_of_memℓp g
  have h1 : Summable fun y => (κ x y : ℂ) * (f : V → ℂ) y := summable_row_mul_complex h hf x
  have h2 : Summable fun y => (κ x y : ℂ) * (g : V → ℂ) y := summable_row_mul_complex h hg x
  simp only [kernelLpℂ, lp.coeFn_add, Pi.add_apply, kernelApplyℂ]
  rw [show (∑' y, (κ x y : ℂ) * ((f : V → ℂ) y + (g : V → ℂ) y))
      = ∑' y, ((κ x y : ℂ) * (f : V → ℂ) y + (κ x y : ℂ) * (g : V → ℂ) y) from
    tsum_congr fun y => by ring]
  rw [Summable.tsum_add h1 h2]

theorem kernelLpℂ_smul (h : SchurKernel κ A) (c : ℂ) (f : lp (fun _ : V => ℂ) 2) :
    kernelLpℂ h (c • f) = c • kernelLpℂ h f := by
  refine lp.ext ?_
  funext x
  have hf : Summable fun y => ‖(f : V → ℂ) y‖ ^ 2 := summable_norm_sq_of_memℓp f
  have hsum : Summable fun y => (κ x y : ℂ) * (f : V → ℂ) y := summable_row_mul_complex h hf x
  simp only [kernelLpℂ, lp.coeFn_smul, Pi.smul_apply, kernelApplyℂ, smul_eq_mul]
  rw [← tsum_mul_left]
  exact tsum_congr fun y => by ring

/-- The complex Schur kernel operator as a `ℂ`-linear map on complex `ℓ²`. -/
noncomputable def kernelLinearMapℂ (h : SchurKernel κ A) :
    lp (fun _ : V => ℂ) 2 →ₗ[ℂ] lp (fun _ : V => ℂ) 2 where
  toFun := kernelLpℂ h
  map_add' := kernelLpℂ_add h
  map_smul' := kernelLpℂ_smul h

@[simp]
theorem kernelLinearMapℂ_apply (h : SchurKernel κ A) (f : lp (fun _ : V => ℂ) 2) :
    kernelLinearMapℂ h f = kernelLpℂ h f := rfl

/-! ### The operator norm bound -/

theorem kernelLpℂ_norm_sq (h : SchurKernel κ A) (f : lp (fun _ : V => ℂ) 2) :
    ‖kernelLpℂ h f‖ ^ 2 = ∑' x, ‖kernelApplyℂ κ (f : V → ℂ) x‖ ^ 2 := by
  have h2 : ((2 : ℝ≥0∞)).toReal = 2 := by norm_num
  rw [← Real.rpow_two, ← h2,
    lp.norm_rpow_eq_tsum (p := 2) (by norm_num : 0 < ((2 : ℝ≥0∞)).toReal) (kernelLpℂ h f)]
  refine tsum_congr fun x => ?_
  rw [kernelLpℂ_apply, h2, Real.rpow_two]

theorem lp_norm_sq_complex (f : lp (fun _ : V => ℂ) 2) :
    ‖f‖ ^ 2 = ∑' y, ‖(f : V → ℂ) y‖ ^ 2 := by
  have h2 : ((2 : ℝ≥0∞)).toReal = 2 := by norm_num
  rw [← Real.rpow_two, ← h2,
    lp.norm_rpow_eq_tsum (p := 2) (by norm_num : 0 < ((2 : ℝ≥0∞)).toReal) f]
  refine tsum_congr fun y => ?_
  rw [h2, Real.rpow_two]

/-- **The operator norm bound**: `‖T_κ f‖ ≤ A ‖f‖` on complex `ℓ²`. -/
theorem kernelLpℂ_norm_le (h : SchurKernel κ A) (f : lp (fun _ : V => ℂ) 2) :
    ‖kernelLpℂ h f‖ ≤ A * ‖f‖ := by
  have hb := tsum_sq_kernelApplyℂ_le h f
  have hsq : ‖kernelLpℂ h f‖ ^ 2 ≤ (A * ‖f‖) ^ 2 := by
    rw [kernelLpℂ_norm_sq h f, mul_pow, lp_norm_sq_complex f]
    exact hb.2
  have h1 : 0 ≤ ‖kernelLpℂ h f‖ := norm_nonneg _
  have h2 : 0 ≤ A * ‖f‖ := mul_nonneg h.A_nonneg (norm_nonneg _)
  exact (pow_le_pow_iff_left₀ h1 h2 (by norm_num : (2 : ℕ) ≠ 0)).mp hsq

/-- **The complex Schur kernel operator as a genuine bounded `ℂ`-linear map on complex
`ℓ²`.** -/
noncomputable def kernelCLMℂ (h : SchurKernel κ A) :
    lp (fun _ : V => ℂ) 2 →L[ℂ] lp (fun _ : V => ℂ) 2 :=
  (kernelLinearMapℂ h).mkContinuous A (kernelLpℂ_norm_le h)

@[simp]
theorem kernelCLMℂ_apply (h : SchurKernel κ A) (f : lp (fun _ : V => ℂ) 2) :
    kernelCLMℂ h f = kernelLpℂ h f := rfl

/-- **The operator norm of the complex kernel operator is at most `A`.** -/
theorem kernelCLMℂ_norm_le (h : SchurKernel κ A) : ‖kernelCLMℂ h‖ ≤ A :=
  LinearMap.mkContinuous_norm_le _ h.A_nonneg (kernelLpℂ_norm_le h)

/-- The kernel formula for the complex bounded operator. -/
theorem kernelCLMℂ_apply_eq_tsum (h : SchurKernel κ A) (f : lp (fun _ : V => ℂ) 2)
    (x : V) : (kernelCLMℂ h f : V → ℂ) x = ∑' y, (κ x y : ℂ) * (f : V → ℂ) y := rfl

/-! ### Agreement with the real kernel operator -/

/-- **The complex kernel series of a real-valued function is the complexification of the real
kernel series.** -/
theorem kernelApplyℂ_ofReal (g : V → ℝ) (x : V) :
    kernelApplyℂ κ (fun y => (g y : ℂ)) x = ((kernelApply κ g x : ℝ) : ℂ) := by
  rw [kernelApplyℂ, kernelApply, Complex.ofReal_tsum]
  exact tsum_congr fun y => by push_cast; ring

/-- **The complex operator extends the real one.**  On real-valued `ℓ²` functions the complex
kernel operator coincides with `kernelCLM h`. -/
theorem kernelLpℂ_ofRealLp (h : SchurKernel κ A) (a : lp (fun _ : V => ℝ) 2) :
    kernelLpℂ h (Realification.ofRealLp a) = Realification.ofRealLp (kernelLp h a) := by
  refine lp.ext ?_
  funext x
  exact kernelApplyℂ_ofReal (κ := κ) (a : V → ℝ) x

/-- **The extension property for the bounded operators.** -/
theorem kernelCLMℂ_ofRealLp (h : SchurKernel κ A) (a : lp (fun _ : V => ℝ) 2) :
    kernelCLMℂ h (Realification.ofRealLp a) = Realification.ofRealLp (kernelCLM h a) :=
  kernelLpℂ_ofRealLp h a

end PercLib.CriticalLRP.KernelOperator

set_option linter.hashCommand false

/-! ### Axiom audit -/
#print axioms PercLib.CriticalLRP.KernelOperator.summable_norm_sq_of_memℓp
#print axioms PercLib.CriticalLRP.KernelOperator.summable_row_mul_complex
#print axioms PercLib.CriticalLRP.KernelOperator.norm_kernelApplyℂ_le_kernelApply_norm
#print axioms PercLib.CriticalLRP.KernelOperator.tsum_sq_kernelApplyℂ_le
#print axioms PercLib.CriticalLRP.KernelOperator.memℓp_kernelApplyℂ
#print axioms PercLib.CriticalLRP.KernelOperator.kernelLpℂ
#print axioms PercLib.CriticalLRP.KernelOperator.kernelLpℂ_add
#print axioms PercLib.CriticalLRP.KernelOperator.kernelLpℂ_smul
#print axioms PercLib.CriticalLRP.KernelOperator.kernelLinearMapℂ
#print axioms PercLib.CriticalLRP.KernelOperator.kernelLpℂ_norm_sq
#print axioms PercLib.CriticalLRP.KernelOperator.lp_norm_sq_complex
#print axioms PercLib.CriticalLRP.KernelOperator.kernelLpℂ_norm_le
#print axioms PercLib.CriticalLRP.KernelOperator.kernelCLMℂ
#print axioms PercLib.CriticalLRP.KernelOperator.kernelCLMℂ_norm_le
#print axioms PercLib.CriticalLRP.KernelOperator.kernelApplyℂ_ofReal
#print axioms PercLib.CriticalLRP.KernelOperator.kernelLpℂ_ofRealLp
#print axioms PercLib.CriticalLRP.KernelOperator.kernelCLMℂ_ofRealLp
