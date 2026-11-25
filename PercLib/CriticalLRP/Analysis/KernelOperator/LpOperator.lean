
module

public import PercLib.CriticalLRP.Analysis.KernelOperator.Operator

/-!
The Schur kernel operator as a genuine bounded linear map on real `ℓ²`.

Swarm `smwttizjk`, member `m2`, direction D6A.

`KernelOperator/Operator.lean` proves the Schur *numeric* bound: the lattice series
`kernelApply κ f` is square summable with `∑ ‖T f‖² ≤ A² ∑ ‖f‖²`.  This file packages that as an
actual `ContinuousLinearMap` on `lp (fun _ => ℝ) 2` (Mathlib's real `ℓ²`), with

* operator norm at most `A`,
* the kernel formula `(T f) x = ∑'_y κ x y * f y` on the nose,
* and, using `kernelApply_comp_eq`, the square of `T` acting by the composed kernel
  `kernelComp κ κ`,

so the `ℓ²` operator is available as an operator and not only as an estimate.  The composition
hypothesis `SchurKernel (kernelComp κ κ) (A * A)` needed for the third power is not assumed
here: it is derived in `Candidate/D6A/SchurComp.lean`.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal lp

namespace PercLib.CriticalLRP.KernelOperator

variable {V : Type*} {κ : V → V → ℝ} {A : ℝ}

/-! ### Row summability and `Memℓp` -/

/-- **Rows against an `ℓ²` function are summable.**  Absolute convergence of the row series
`∑_y κ x y f y`, which is what makes the pointwise formula additive and homogeneous. -/
theorem summable_row_mul (h : SchurKernel κ A) {f : V → ℝ} (hfs : Summable fun y => f y ^ 2)
    (x : V) : Summable fun y => κ x y * f y := by
  have hnorm : Summable fun y => κ x y * |f y| := schur_summable_row_mul_abs h hfs x
  refine Summable.of_norm ?_
  exact hnorm.congr fun y => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (h.nonneg x y)]

/-- An element of `ℓ²` is square summable as a plain real sequence. -/
theorem summable_sq_of_memℓp (f : lp (fun _ : V => ℝ) 2) :
    Summable fun y => (f : V → ℝ) y ^ 2 := by
  have h := (lp.memℓp f).summable (p := 2) (by norm_num : 0 < ((2 : ℝ≥0∞)).toReal)
  simpa [Real.norm_eq_abs, sq_abs] using h

/-- **The kernel series of an `ℓ²` function is again in `ℓ²`.** -/
theorem memℓp_kernelApply (h : SchurKernel κ A) (f : lp (fun _ : V => ℝ) 2) :
    Memℓp (fun x => kernelApply κ (f : V → ℝ) x) 2 := by
  refine memℓp_gen ?_
  have hb := (schur_tsum_sq_kernelApply_le h (f : V → ℝ) (summable_sq_of_memℓp f)).1
  refine hb.congr fun x => ?_
  have h2 : ((2 : ℝ≥0∞)).toReal = 2 := by norm_num
  rw [h2, Real.rpow_two]
  simp only [Real.norm_eq_abs, sq_abs]

/-! ### The operator as a function on `ℓ²` -/

/-- The kernel operator as a self-map of real `ℓ²`. -/
noncomputable def kernelLp (h : SchurKernel κ A) (f : lp (fun _ : V => ℝ) 2) :
    lp (fun _ : V => ℝ) 2 :=
  ⟨fun x => kernelApply κ (f : V → ℝ) x, memℓp_kernelApply h f⟩

@[simp]
theorem kernelLp_coe (h : SchurKernel κ A) (f : lp (fun _ : V => ℝ) 2) :
    (kernelLp h f : V → ℝ) = fun x => kernelApply κ (f : V → ℝ) x := rfl

@[simp]
theorem kernelLp_apply (h : SchurKernel κ A) (f : lp (fun _ : V => ℝ) 2) (x : V) :
    (kernelLp h f : V → ℝ) x = kernelApply κ (f : V → ℝ) x := rfl

theorem kernelLp_add (h : SchurKernel κ A) (f g : lp (fun _ : V => ℝ) 2) :
    kernelLp h (f + g) = kernelLp h f + kernelLp h g := by
  refine lp.ext ?_
  funext x
  have hf := summable_sq_of_memℓp f
  have hg := summable_sq_of_memℓp g
  simp only [kernelLp_apply, lp.coeFn_add, Pi.add_apply, kernelApply, mul_add]
  rw [Summable.tsum_add (summable_row_mul h hf x) (summable_row_mul h hg x)]

theorem kernelLp_smul (h : SchurKernel κ A) (c : ℝ) (f : lp (fun _ : V => ℝ) 2) :
    kernelLp h (c • f) = c • kernelLp h f := by
  refine lp.ext ?_
  funext x
  have hcf : Summable fun y => (c * (f : V → ℝ) y) ^ 2 := by
    have h2s : Summable fun y => c ^ 2 * (f : V → ℝ) y ^ 2 :=
      (summable_sq_of_memℓp f).mul_left _
    exact h2s.congr fun y => by rw [mul_pow]
  simp only [kernelLp_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, kernelApply]
  rw [← tsum_mul_left]
  exact tsum_congr fun y => by ring

/-- The Schur kernel operator as an `ℝ`-linear map on real `ℓ²`. -/
noncomputable def kernelLinearMap (h : SchurKernel κ A) :
    lp (fun _ : V => ℝ) 2 →ₗ[ℝ] lp (fun _ : V => ℝ) 2 where
  toFun := kernelLp h
  map_add' := kernelLp_add h
  map_smul' := kernelLp_smul h

@[simp]
theorem kernelLinearMap_apply (h : SchurKernel κ A) (f : lp (fun _ : V => ℝ) 2) :
    kernelLinearMap h f = kernelLp h f := rfl

/-! ### The operator norm bound -/

theorem kernelLp_norm_sq (h : SchurKernel κ A) (f : lp (fun _ : V => ℝ) 2) :
    ‖kernelLp h f‖ ^ 2 = ∑' x, kernelApply κ (f : V → ℝ) x ^ 2 := by
  have h2 : ((2 : ℝ≥0∞)).toReal = 2 := by norm_num
  rw [← Real.rpow_two, ← h2,
    lp.norm_rpow_eq_tsum (p := 2) (by norm_num : 0 < ((2 : ℝ≥0∞)).toReal) (kernelLp h f)]
  refine tsum_congr fun x => ?_
  rw [kernelLp_apply, h2, Real.rpow_two]
  simp only [Real.norm_eq_abs, sq_abs]

theorem lp_norm_sq (f : lp (fun _ : V => ℝ) 2) :
    ‖f‖ ^ 2 = ∑' y, (f : V → ℝ) y ^ 2 := by
  have h2 : ((2 : ℝ≥0∞)).toReal = 2 := by norm_num
  rw [← Real.rpow_two, ← h2,
    lp.norm_rpow_eq_tsum (p := 2) (by norm_num : 0 < ((2 : ℝ≥0∞)).toReal) f]
  refine tsum_congr fun y => ?_
  rw [h2, Real.rpow_two]
  simp only [Real.norm_eq_abs, sq_abs]

/-- **The operator norm bound**: `‖T_κ f‖ ≤ A ‖f‖`. -/
theorem kernelLp_norm_le (h : SchurKernel κ A) (f : lp (fun _ : V => ℝ) 2) :
    ‖kernelLp h f‖ ≤ A * ‖f‖ := by
  have hb := schur_tsum_sq_kernelApply_le h (f : V → ℝ) (summable_sq_of_memℓp f)
  have hsq : ‖kernelLp h f‖ ^ 2 ≤ (A * ‖f‖) ^ 2 := by
    rw [kernelLp_norm_sq h f, mul_pow, lp_norm_sq f]
    exact hb.2
  have h1 : 0 ≤ ‖kernelLp h f‖ := norm_nonneg _
  have h2 : 0 ≤ A * ‖f‖ := mul_nonneg h.A_nonneg (norm_nonneg _)
  exact (pow_le_pow_iff_left₀ h1 h2 (by norm_num : (2 : ℕ) ≠ 0)).mp hsq

/-- **The Schur kernel operator as a genuine bounded linear map on real `ℓ²`.** -/
noncomputable def kernelCLM (h : SchurKernel κ A) :
    lp (fun _ : V => ℝ) 2 →L[ℝ] lp (fun _ : V => ℝ) 2 :=
  (kernelLinearMap h).mkContinuous A (kernelLp_norm_le h)

@[simp]
theorem kernelCLM_apply (h : SchurKernel κ A) (f : lp (fun _ : V => ℝ) 2) :
    kernelCLM h f = kernelLp h f := rfl

/-- **The operator norm of the kernel operator is at most `A`.** -/
theorem kernelCLM_norm_le (h : SchurKernel κ A) : ‖kernelCLM h‖ ≤ A :=
  LinearMap.mkContinuous_norm_le _ h.A_nonneg (kernelLp_norm_le h)

/-- **The kernel formula for the bounded operator.** -/
theorem kernelCLM_apply_eq_tsum (h : SchurKernel κ A) (f : lp (fun _ : V => ℝ) 2) (x : V) :
    (kernelCLM h f : V → ℝ) x = ∑' y, κ x y * (f : V → ℝ) y := rfl

/-- **The square of the bounded operator acts by the composed kernel.**  Pointwise form of
`T_κ ∘ T_κ = T_{κ * κ}`; the composed kernel is a Schur kernel by `schurKernel_kernelComp`,
so this is the operator-level version of the O1 identity. -/
theorem kernelCLM_comp_apply (h : SchurKernel κ A) (f : lp (fun _ : V => ℝ) 2) (x : V) :
    (kernelCLM h (kernelCLM h f) : V → ℝ) x
      = ∑' z, kernelComp κ κ x z * (f : V → ℝ) z :=
  kernelApply_comp_eq h (summable_sq_of_memℓp f) x

/-- **Packaging statement.**  A Schur kernel gives a genuine bounded `ℝ`-linear operator on real
`ℓ²` of norm at most `A`, with the kernel formula, and whose square acts by `kernelComp κ κ`. -/
theorem exists_kernelCLM (h : SchurKernel κ A) :
    ∃ T : lp (fun _ : V => ℝ) 2 →L[ℝ] lp (fun _ : V => ℝ) 2,
      ‖T‖ ≤ A ∧
        (∀ (f : lp (fun _ : V => ℝ) 2) (x : V), (T f : V → ℝ) x = ∑' y, κ x y * (f : V → ℝ) y) ∧
        (∀ (f : lp (fun _ : V => ℝ) 2) (x : V),
          (T (T f) : V → ℝ) x = ∑' z, kernelComp κ κ x z * (f : V → ℝ) z) :=
  ⟨kernelCLM h, kernelCLM_norm_le h, kernelCLM_apply_eq_tsum h, kernelCLM_comp_apply h⟩

end PercLib.CriticalLRP.KernelOperator
