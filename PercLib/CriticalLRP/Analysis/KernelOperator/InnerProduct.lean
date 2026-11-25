module

public import PercLib.CriticalLRP.Analysis.KernelOperator.LpOperator

/-!
The Schur kernel operator on real `ℓ²` is self-adjoint.

Swarm `smwttizjk`, member `m2`, direction D6A.

`Candidate/D6A/LpOperator.lean` packages the kernel action as a bounded linear map `kernelCLM`.
Here the bilinear form is computed: for two `ℓ²` functions the double family
`(x, y) ↦ κ x y f y g x` is *absolutely* summable with total bound `A ‖f‖ ‖g‖` (Cauchy–Schwarz in
`x` against the Schur bound in `y`), which gives

`⟪T f, g⟫ = ∑_y f y (T g) y = ⟪f, T g⟫`,

so a symmetric Schur kernel gives a self-adjoint bounded operator.  This is the real (not
complex) Fubini step, and it is where the symmetry of `κ` is actually used analytically.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal lp

namespace PercLib.CriticalLRP.KernelOperator

variable {V : Type*} {κ : V → V → ℝ} {A : ℝ}

/-! ### The Schur bound for the absolute row sums -/

/-- **The square of the absolute kernel series is bounded by `A² ‖f‖²`.** -/
theorem tsum_sq_kernelApply_abs_le (h : SchurKernel κ A) (f : lp (fun _ : V => ℝ) 2) :
    ∑' x, kernelApply κ (fun y => |(f : V → ℝ) y|) x ^ 2 ≤ A ^ 2 * ‖f‖ ^ 2 := by
  have habs : Summable fun y => |(f : V → ℝ) y| ^ 2 := by
    simpa [sq_abs] using summable_sq_of_memℓp f
  have hb := (schur_tsum_sq_kernelApply_le h (fun y => |(f : V → ℝ) y|) habs).2
  refine le_trans hb (le_of_eq ?_)
  rw [lp_norm_sq f]
  congr 1
  exact tsum_congr fun y => by rw [sq_abs]

/-! ### Absolute summability of the double family -/

/-- **The absolute double family of a symmetric Schur kernel against two `ℓ²` functions is
summable**, with total bound `A ‖f‖ ‖g‖`.  This is the Fubini input for the bilinear form. -/
theorem summable_kernel_abs_mul (h : SchurKernel κ A) (f g : lp (fun _ : V => ℝ) 2) :
    Summable fun p : V × V => κ p.1 p.2 * |(f : V → ℝ) p.2| * |(g : V → ℝ) p.1| := by
  classical
  have habs : Summable fun y => |(f : V → ℝ) y| ^ 2 := by
    simpa [sq_abs] using summable_sq_of_memℓp f
  have hU : Summable fun x => kernelApply κ (fun y => |(f : V → ℝ) y|) x ^ 2 :=
    (schur_tsum_sq_kernelApply_le h (fun y => |(f : V → ℝ) y|) habs).1
  have hUle : ∑' x, kernelApply κ (fun y => |(f : V → ℝ) y|) x ^ 2 ≤ A ^ 2 * ‖f‖ ^ 2 :=
    tsum_sq_kernelApply_abs_le h f
  refine summable_of_sum_le (c := A * ‖f‖ * ‖g‖)
    (fun p => mul_nonneg (mul_nonneg (h.nonneg p.1 p.2) (abs_nonneg _)) (abs_nonneg _))
    fun u => ?_
  have hsub : u ⊆ u.image Prod.fst ×ˢ u.image Prod.snd := by
    intro p hp
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩
  have hnn : ∀ p : V × V, 0 ≤ κ p.1 p.2 * |(f : V → ℝ) p.2| * |(g : V → ℝ) p.1| := fun p =>
    mul_nonneg (mul_nonneg (h.nonneg p.1 p.2) (abs_nonneg _)) (abs_nonneg _)
  have h1 : ∑ p ∈ u, κ p.1 p.2 * |(f : V → ℝ) p.2| * |(g : V → ℝ) p.1|
      ≤ ∑ p ∈ u.image Prod.fst ×ˢ u.image Prod.snd,
          κ p.1 p.2 * |(f : V → ℝ) p.2| * |(g : V → ℝ) p.1| :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ => hnn p
  have h2 : ∑ p ∈ u.image Prod.fst ×ˢ u.image Prod.snd,
        κ p.1 p.2 * |(f : V → ℝ) p.2| * |(g : V → ℝ) p.1|
      = ∑ x ∈ u.image Prod.fst,
          |(g : V → ℝ) x| * (∑ y ∈ u.image Prod.snd, κ x y * |(f : V → ℝ) y|) := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  have h3 : ∑ x ∈ u.image Prod.fst,
        |(g : V → ℝ) x| * (∑ y ∈ u.image Prod.snd, κ x y * |(f : V → ℝ) y|)
      ≤ ∑ x ∈ u.image Prod.fst,
          |(g : V → ℝ) x| * kernelApply κ (fun y => |(f : V → ℝ) y|) x := by
    refine Finset.sum_le_sum fun x _ => ?_
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    exact (summable_row_mul h habs x).sum_le_tsum _
      (fun y _ => mul_nonneg (h.nonneg x y) (abs_nonneg _))
  have h4 : ∑ x ∈ u.image Prod.fst,
        |(g : V → ℝ) x| * kernelApply κ (fun y => |(f : V → ℝ) y|) x
      ≤ Real.sqrt (∑ x ∈ u.image Prod.fst, (g : V → ℝ) x ^ 2)
        * Real.sqrt (∑ x ∈ u.image Prod.fst,
            kernelApply κ (fun y => |(f : V → ℝ) y|) x ^ 2) := by
    have hCS := Finset.sum_mul_sq_le_sq_mul_sq (u.image Prod.fst)
      (fun x => |(g : V → ℝ) x|) (fun x => kernelApply κ (fun y => |(f : V → ℝ) y|) x)
    have hCS' : (∑ x ∈ u.image Prod.fst,
          |(g : V → ℝ) x| * kernelApply κ (fun y => |(f : V → ℝ) y|) x) ^ 2
        ≤ (∑ x ∈ u.image Prod.fst, (g : V → ℝ) x ^ 2)
          * ∑ x ∈ u.image Prod.fst, kernelApply κ (fun y => |(f : V → ℝ) y|) x ^ 2 := by
      refine le_trans hCS (le_of_eq ?_)
      rw [Finset.sum_congr rfl (fun x _ => sq_abs ((g : V → ℝ) x))]
    have := Real.le_sqrt_of_sq_le hCS'
    rwa [Real.sqrt_mul (Finset.sum_nonneg fun x _ => sq_nonneg _)] at this
  have h5 : Real.sqrt (∑ x ∈ u.image Prod.fst, (g : V → ℝ) x ^ 2) ≤ ‖g‖ := by
    have hle : (∑ x ∈ u.image Prod.fst, (g : V → ℝ) x ^ 2) ≤ ‖g‖ ^ 2 := by
      rw [lp_norm_sq g]
      exact (summable_sq_of_memℓp g).sum_le_tsum _ (fun i _ => sq_nonneg _)
    calc Real.sqrt (∑ x ∈ u.image Prod.fst, (g : V → ℝ) x ^ 2) ≤ Real.sqrt (‖g‖ ^ 2) :=
          Real.sqrt_le_sqrt hle
      _ = ‖g‖ := Real.sqrt_sq (norm_nonneg _)
  have h6 : Real.sqrt (∑ x ∈ u.image Prod.fst,
        kernelApply κ (fun y => |(f : V → ℝ) y|) x ^ 2) ≤ A * ‖f‖ := by
    have hle : (∑ x ∈ u.image Prod.fst,
        kernelApply κ (fun y => |(f : V → ℝ) y|) x ^ 2) ≤ A ^ 2 * ‖f‖ ^ 2 :=
      le_trans (hU.sum_le_tsum _ (fun i _ => sq_nonneg _)) hUle
    calc Real.sqrt (∑ x ∈ u.image Prod.fst,
          kernelApply κ (fun y => |(f : V → ℝ) y|) x ^ 2)
        ≤ Real.sqrt (A ^ 2 * ‖f‖ ^ 2) := Real.sqrt_le_sqrt hle
      _ = A * ‖f‖ := by
          rw [show A ^ 2 * ‖f‖ ^ 2 = (A * ‖f‖) ^ 2 by ring, Real.sqrt_sq]
          exact mul_nonneg h.A_nonneg (norm_nonneg _)
  have hbound : Real.sqrt (∑ x ∈ u.image Prod.fst, (g : V → ℝ) x ^ 2)
      * Real.sqrt (∑ x ∈ u.image Prod.fst,
          kernelApply κ (fun y => |(f : V → ℝ) y|) x ^ 2) ≤ ‖g‖ * (A * ‖f‖) :=
    mul_le_mul h5 h6 (Real.sqrt_nonneg _) (norm_nonneg _)
  calc ∑ p ∈ u, κ p.1 p.2 * |(f : V → ℝ) p.2| * |(g : V → ℝ) p.1|
      ≤ ∑ p ∈ u.image Prod.fst ×ˢ u.image Prod.snd,
          κ p.1 p.2 * |(f : V → ℝ) p.2| * |(g : V → ℝ) p.1| := h1
    _ = ∑ x ∈ u.image Prod.fst,
          |(g : V → ℝ) x| * (∑ y ∈ u.image Prod.snd, κ x y * |(f : V → ℝ) y|) := h2
    _ ≤ ∑ x ∈ u.image Prod.fst,
          |(g : V → ℝ) x| * kernelApply κ (fun y => |(f : V → ℝ) y|) x := h3
    _ ≤ Real.sqrt (∑ x ∈ u.image Prod.fst, (g : V → ℝ) x ^ 2)
        * Real.sqrt (∑ x ∈ u.image Prod.fst,
            kernelApply κ (fun y => |(f : V → ℝ) y|) x ^ 2) := h4
    _ ≤ ‖g‖ * (A * ‖f‖) := hbound
    _ = A * ‖f‖ * ‖g‖ := by ring

/-- **The signed double family is summable.** -/
theorem summable_kernel_mul (h : SchurKernel κ A) (f g : lp (fun _ : V => ℝ) 2) :
    Summable fun p : V × V => κ p.1 p.2 * (f : V → ℝ) p.2 * (g : V → ℝ) p.1 := by
  refine Summable.of_norm_bounded (summable_kernel_abs_mul h f g) fun p => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (h.nonneg p.1 p.2)]

/-! ### The bilinear form -/

/-- The real inner product as a product, in the orientation this Mathlib uses. -/
theorem real_inner_eq_mul (a b : ℝ) : inner ℝ a b = b * a := by
  rw [RCLike.inner_apply]
  simp

/-- **The bilinear form, computed once and for all**: `⟪T f, g⟫ = ∑_y f y · (T g) y`, written
with the column sums `∑_x κ x y g x`. -/
theorem inner_kernelCLM_eq (h : SchurKernel κ A) (f g : lp (fun _ : V => ℝ) 2) :
    inner ℝ (kernelCLM h f) g
      = ∑' y, (f : V → ℝ) y * ∑' x, κ x y * (g : V → ℝ) x := by
  have hS := summable_kernel_mul h f g
  rw [lp.inner_eq_tsum]
  have h1 : ∀ x, inner ℝ (kernelCLM h f x) (g x)
      = ∑' y, κ x y * (f : V → ℝ) y * (g : V → ℝ) x := by
    intro x
    rw [real_inner_eq_mul, kernelCLM_apply_eq_tsum, ← tsum_mul_left]
    exact tsum_congr fun y => by ring
  rw [tsum_congr h1]
  have hcomm : ∑' y, ∑' x, κ x y * (f : V → ℝ) y * (g : V → ℝ) x
      = ∑' x, ∑' y, κ x y * (f : V → ℝ) y * (g : V → ℝ) x :=
    Summable.tsum_comm (f := fun x y => κ x y * (f : V → ℝ) y * (g : V → ℝ) x) hS
  rw [← hcomm]
  refine tsum_congr fun y => ?_
  rw [show (∑' x, κ x y * (f : V → ℝ) y * (g : V → ℝ) x)
      = ∑' x, (f : V → ℝ) y * (κ x y * (g : V → ℝ) x) from
    tsum_congr fun x => by ring]
  rw [tsum_mul_left]

/-- **The operator is self-adjoint**: `⟪T f, g⟫ = ⟪f, T g⟫` for two `ℓ²` functions. -/
theorem inner_kernelCLM_comm (h : SchurKernel κ A) (f g : lp (fun _ : V => ℝ) 2) :
    inner ℝ (kernelCLM h f) g = inner ℝ f (kernelCLM h g) := by
  rw [inner_kernelCLM_eq h f g, lp.inner_eq_tsum]
  refine tsum_congr fun y => ?_
  rw [real_inner_eq_mul, kernelCLM_apply_eq_tsum, mul_comm]
  congr 1
  exact tsum_congr fun x => by rw [h.symm y x]

/-- **A symmetric Schur kernel gives a self-adjoint bounded operator on real `ℓ²`.** -/
theorem kernelCLM_adjoint_eq (h : SchurKernel κ A) :
    ContinuousLinearMap.adjoint (kernelCLM h) = kernelCLM h := by
  refine ContinuousLinearMap.ext fun f => ?_
  refine ext_inner_left ℝ fun g => ?_
  rw [real_inner_comm, ContinuousLinearMap.adjoint_inner_left, real_inner_comm]
  exact inner_kernelCLM_comm h g f

end PercLib.CriticalLRP.KernelOperator
