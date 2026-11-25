/-
Positive semidefiniteness of the composed and cube kernels, and of their quadratic forms.

Swarm `smwtxo95t`, member `m6`, direction (E).

`KernelOperator/Composition.lean` identifies the square and the cube of the bounded kernel operator
with the operators of `kernelComp κ κ` and `kernelCube κ`.  Composing that with the quadratic-form
identity of `Positivity/Basic.lean` gives the lattice-sum form of the `T²` and `T³` forms,
hence:

* `kernelComp_isPSDKernel` : the two-step kernel is positive semidefinite on every finite
  vertex set, from the Schur hypothesis alone (no positivity of `κ`: `⟪T²f, f⟫ = ‖T f‖²`),
* `kernelCube_isPSDKernel` : the three-step kernel is positive semidefinite once `κ` is.

The finite-block statements are reduced to the bounded-operator ones by testing on the
finitely-supported vector `1_s · v`, which is an element of `ℓ²`; the lattice sum then collapses to
a finite block sum by `tsum_eq_sum`.
-/
module

public import PercLib.CriticalLRP.Analysis.KernelOperator.CutoffPositivity.Cutoff
public import PercLib.CriticalLRP.Analysis.KernelOperator.Composition

/-!
# Composed and cube kernels: quadratic forms and finite-block positivity
-/

@[expose] public section

noncomputable section

open scoped ENNReal NNReal lp

namespace PercLib.CriticalLRP.CutoffPositivity

open PercLib.CriticalLRP.KernelOperator
open PercLib.CriticalLRP.Orchestration

variable {V : Type*} {κ : V → V → ℝ} {A : ℝ}

/-! ### The `T²` and `T³` quadratic forms as lattice sums -/

/-- **The square of the bounded operator acts by the two-step kernel** (pointwise form, with the
Schur hypothesis on the two-step kernel discharged). -/
theorem kernelCLM_sq_apply_eq (h : SchurKernel κ A) (f : lp (fun _ : V => ℝ) 2) (x : V) :
    (kernelCLM h (kernelCLM h f) : V → ℝ) x
      = (kernelCLM (schurKernel_kernelComp h) f : V → ℝ) x := by
  rw [← kernelCLM_comp_self_eq h, ContinuousLinearMap.comp_apply]

/-- **The square of the bounded operator acts by the three-fold iterated kernel**, pointwise. -/
theorem kernelCLM_cube_apply_eq (h : SchurKernel κ A) (f : lp (fun _ : V => ℝ) 2) (x : V) :
    (kernelCLM h (kernelCLM h (kernelCLM h f)) : V → ℝ) x
      = (kernelCLM (schurKernel_kernelCube h) f : V → ℝ) x :=
  kernelCLM_three_apply_eq h f x

/-- **The `T²` quadratic form is the lattice sum of the two-step kernel.** -/
theorem inner_sq_eq_kernelForm (h : SchurKernel κ A) (f : lp (fun _ : V => ℝ) 2) :
    inner ℝ ((kernelCLM h ^ 2) f) f
      = ∑' p : V × V, kernelComp κ κ p.1 p.2 * (f : V → ℝ) p.1 * (f : V → ℝ) p.2 := by
  have h2 : (kernelCLM h ^ 2) f = kernelCLM h (kernelCLM h f) := by
    simp only [pow_succ, pow_zero, one_mul, mul_apply_eq_comp]
  rw [h2]
  have hpt : kernelCLM h (kernelCLM h f) = kernelCLM (schurKernel_kernelComp h) f := by
    refine lp.ext ?_
    funext x
    exact kernelCLM_sq_apply_eq h f x
  rw [hpt, inner_kernelCLM_eq_kernelForm (schurKernel_kernelComp h) f]
  rfl

/-- **The `T³` quadratic form is the lattice sum of the cube kernel.** -/
theorem inner_cube_eq_kernelForm (h : SchurKernel κ A) (f : lp (fun _ : V => ℝ) 2) :
    inner ℝ ((kernelCLM h ^ 3) f) f
      = ∑' p : V × V, kernelCube κ p.1 p.2 * (f : V → ℝ) p.1 * (f : V → ℝ) p.2 := by
  have h3 : (kernelCLM h ^ 3) f = kernelCLM h (kernelCLM h (kernelCLM h f)) := by
    simp only [pow_succ, pow_zero, one_mul, mul_apply_eq_comp]
  rw [h3]
  have hpt : kernelCLM h (kernelCLM h (kernelCLM h f))
      = kernelCLM (schurKernel_kernelCube h) f := by
    refine lp.ext ?_
    funext x
    exact kernelCLM_cube_apply_eq h f x
  rw [hpt, inner_kernelCLM_eq_kernelForm (schurKernel_kernelCube h) f]
  rfl

/-! ### From `ℓ²` forms to finite blocks -/

/-- A function vanishing off a finite set is in `ℓ²`. -/
theorem memℓp_two_of_forall_notMem_eq_zero {g : V → ℝ} {s : Finset V}
    (hg : ∀ x ∉ s, g x = 0) : Memℓp g 2 := by
  refine memℓp_gen ?_
  have h2 : ((2 : ℝ≥0∞)).toReal = 2 := by norm_num
  rw [h2]
  refine summable_of_ne_finset_zero (s := s) fun b hb => ?_
  rw [hg b hb]
  simp

/-- **The lattice sum of a kernel form of a finitely supported function is its finite block
sum.** -/
theorem tsum_kernelForm_eq_sum {g : V → ℝ} {s : Finset V} (hg : ∀ x ∉ s, g x = 0)
    (κ' : V → V → ℝ) :
    ∑' p : V × V, κ' p.1 p.2 * g p.1 * g p.2
      = ∑ x ∈ s, ∑ y ∈ s, κ' x y * g x * g y := by
  rw [tsum_eq_sum (s := s ×ˢ s) (fun p hp => ?_), Finset.sum_product]
  simp only [Finset.mem_product, not_and_or] at hp
  rcases hp with hl | hr
  · rw [hg p.1 hl]; ring
  · rw [hg p.2 hr]; ring

/-! ### Positive semidefiniteness of the two-step and three-step kernels -/

/-- **The two-step kernel is positive semidefinite on every finite vertex set**, from the Schur
hypothesis alone: `⟪T² f, f⟫ = ‖T f‖² ≥ 0`, so no positivity of `κ` is needed. -/
theorem kernelComp_isPSDKernel (h : SchurKernel κ A) : IsPSDKernel (kernelComp κ κ) := by
  classical
  intro s v
  set g : V → ℝ := fun x => if x ∈ s then v x else 0 with hgdef
  have hg : ∀ x ∉ s, g x = 0 := by intro x hx; simp [hgdef, hx]
  have hgs : ∀ x ∈ s, g x = v x := by intro x hx; simp [hgdef, hx]
  let f : lp (fun _ : V => ℝ) 2 := ⟨g, memℓp_two_of_forall_notMem_eq_zero hg⟩
  have hf : (f : V → ℝ) = g := rfl
  have hkey : ∑' p : V × V, kernelComp κ κ p.1 p.2 * (f : V → ℝ) p.1 * (f : V → ℝ) p.2
      = ∑ x ∈ s, ∑ y ∈ s, kernelComp κ κ x y * v x * v y := by
    rw [hf, tsum_kernelForm_eq_sum hg]
    exact Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => by
      rw [hgs x hx, hgs y hy]
  rw [← hkey, ← inner_sq_eq_kernelForm h f]
  have h2 : (kernelCLM h ^ 2) f = kernelCLM h (kernelCLM h f) := by
    simp only [pow_succ, pow_zero, one_mul, mul_apply_eq_comp]
  rw [h2]
  have hstep : inner ℝ (kernelCLM h (kernelCLM h f)) f
      = inner ℝ (kernelCLM h f) (kernelCLM h f) := by
    rw [← ContinuousLinearMap.adjoint_inner_right (kernelCLM h) (kernelCLM h f) f,
      kernelCLM_adjoint h]
  rw [hstep]
  exact real_inner_self_nonneg

/-- **The three-step kernel is positive semidefinite on every finite vertex set** whenever `κ` is:
`⟪T³ f, f⟫ = ⟪T (T f), T f⟫ ≥ 0`. -/
theorem kernelCube_isPSDKernel (h : SchurKernel κ A) (hpsd : IsPSDKernel κ) :
    IsPSDKernel (kernelCube κ) := by
  classical
  intro s v
  set g : V → ℝ := fun x => if x ∈ s then v x else 0 with hgdef
  have hg : ∀ x ∉ s, g x = 0 := by intro x hx; simp [hgdef, hx]
  have hgs : ∀ x ∈ s, g x = v x := by intro x hx; simp [hgdef, hx]
  let f : lp (fun _ : V => ℝ) 2 := ⟨g, memℓp_two_of_forall_notMem_eq_zero hg⟩
  have hf : (f : V → ℝ) = g := rfl
  have hkey : ∑' p : V × V, kernelCube κ p.1 p.2 * (f : V → ℝ) p.1 * (f : V → ℝ) p.2
      = ∑ x ∈ s, ∑ y ∈ s, kernelCube κ x y * v x * v y := by
    rw [hf, tsum_kernelForm_eq_sum hg]
    exact Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => by
      rw [hgs x hx, hgs y hy]
  rw [← hkey, ← inner_cube_eq_kernelForm h f]
  exact kernelCLM_cube_form_nonneg h hpsd f

/-! ### The cutoff instances -/

/-- **The two-step cutoff connection kernel is positive semidefinite** at finite first cutoff
moment. -/
theorem cutKernel_comp_isPSDKernel (M : SourceModelData) (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) :
    IsPSDKernel (kernelComp (cutKernel M r) (cutKernel M r)) :=
  kernelComp_isPSDKernel (cutTwoPoint_schurKernel M r hχ)

/-- **The three-step cutoff connection kernel is positive semidefinite** at finite first cutoff
moment. -/
theorem cutKernel_cube_isPSDKernel (M : SourceModelData) (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) :
    IsPSDKernel (kernelCube (cutKernel M r)) :=
  kernelCube_isPSDKernel (cutTwoPoint_schurKernel M r hχ) (cutKernel_isPSDKernel M r)

end PercLib.CriticalLRP.CutoffPositivity
