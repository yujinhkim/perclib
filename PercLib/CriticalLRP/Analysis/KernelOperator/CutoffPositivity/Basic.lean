/-
The Schur kernel operator of a positive semidefinite kernel has a nonnegative quadratic form.

Swarm `smwtxo95t`, member `m6`, direction (E).

`KernelOperator/InnerProduct.lean` computes the bilinear form of `kernelCLM` as the lattice sum of
the kernel double family.  Here the *quadratic* form is shown nonnegative when the kernel is
positive semidefinite on finite vertex sets (`IsPSDKernel`), which is the only form in which the
model's `posSemidef_tau` is available.  The passage from finite blocks to the full lattice sum is
not an interchange of two limits: the block sums `∑_{u × u}` are a subnet of the partial sums of an
*absolutely* summable family, so nonnegativity is preserved by `le_of_tendsto`.
-/
module

public import PercLib.CriticalLRP.Analysis.KernelOperator.CutoffPositivity.Defs

/-!
# Quadratic-form positivity of a positive-semidefinite Schur kernel operator

`kernelCLM_quadForm_nonneg` and its cubic-form consequence, from `IsPSDKernel` on finite blocks.
-/

@[expose] public section

noncomputable section

open scoped ENNReal NNReal lp

namespace PercLib.CriticalLRP.CutoffPositivity

open PercLib.CriticalLRP.KernelOperator
open Filter

variable {V : Type*} {κ : V → V → ℝ} {A : ℝ}

/-! ### The quadratic form as a lattice sum over `V × V` -/

/-- **The kernel double family is summable** for an `ℓ²` vector and a Schur kernel. -/
theorem summable_kernelForm (h : SchurKernel κ A) (f : lp (fun _ : V => ℝ) 2) :
    Summable (kernelForm κ f) :=
  (summable_kernel_mul h f f).congr fun p => by
    simp only [kernelForm]
    ring

/-- **The quadratic form is the lattice sum of the kernel double family**:
`⟪T_κ f, f⟫ = ∑'_{(x,y)} κ x y (f x)(f y)`.  Symmetry of `κ` is used to put the row-first
iterated sum produced by `inner_kernelCLM_eq` into coordinate order. -/
theorem inner_kernelCLM_eq_kernelForm (h : SchurKernel κ A) (f : lp (fun _ : V => ℝ) 2) :
    inner ℝ (kernelCLM h f) f = ∑' p : V × V, kernelForm κ f p := by
  have hS := summable_kernelForm h f
  rw [inner_kernelCLM_eq h f f]
  have hstep : ∀ y : V, (f : V → ℝ) y * ∑' x, κ x y * (f : V → ℝ) x
      = ∑' x, kernelForm κ f (x, y) := by
    intro y
    rw [← tsum_mul_left]
    exact tsum_congr fun x => by simp only [kernelForm]; ring
  rw [tsum_congr hstep,
    Summable.tsum_comm (f := fun x y : V => kernelForm κ f (x, y)) hS]
  exact (hS.tsum_prod).symm

/-! ### Cofinality of the square blocks, and positivity on them -/

/-- **The square blocks `u × u` are cofinal** among the finite subsets of `V × V`: every finite
`s ⊆ V × V` is contained in `u × u` for `u ⊇ π₁ s ∪ π₂ s`.  This is what lets the block sums be a
subnet of the partial sums of an unconditionally summable family. -/
theorem tendsto_finset_prod_sq_atTop :
    Tendsto (fun u : Finset V => u ×ˢ u) atTop (atTop : Filter (Finset (V × V))) := by
  classical
  rw [tendsto_atTop]
  intro s
  filter_upwards [eventually_ge_atTop (s.image Prod.fst ∪ s.image Prod.snd)] with u hu
  intro p hp
  simp only [Finset.mem_product]
  exact ⟨hu (Finset.mem_union_left _ (Finset.mem_image_of_mem Prod.fst hp)),
    hu (Finset.mem_union_right _ (Finset.mem_image_of_mem Prod.snd hp))⟩

/-! ### Positivity on finite blocks, and the passage to the lattice sum -/

/-- **The block sums of the kernel form are nonnegative** at a positive semidefinite kernel. -/
theorem kernelForm_block_nonneg (hpsd : IsPSDKernel κ) (f : lp (fun _ : V => ℝ) 2)
    (u : Finset V) : 0 ≤ ∑ p ∈ u ×ˢ u, kernelForm κ f p := by
  rw [Finset.sum_product]
  simpa only [kernelForm] using hpsd u (f : V → ℝ)

/-- **Quadratic-form nonnegativity of the Schur kernel operator.**  A nonnegative symmetric Schur
kernel which is positive semidefinite on every finite vertex set defines a bounded operator on
`ℓ²(V; ℝ)` with `0 ≤ ⟪T f, f⟫` for every `f`.

The block sums `∑_{p ∈ u × u}` are partial sums of the absolutely summable family `kernelForm κ f`
along the image of `Finset V ↦ Finset V × Finset V` under `Filter.map`, so their nonnegativity
passes to the limit; no uniform per-`y` majorant and no interchange of two separate limits is
used. -/
theorem kernelCLM_quadForm_nonneg (h : SchurKernel κ A) (hpsd : IsPSDKernel κ) :
    QuadFormNonneg (kernelCLM h) := by
  intro f
  rw [inner_kernelCLM_eq_kernelForm h f]
  have hS := summable_kernelForm h f
  have hlim : Tendsto (fun s : Finset (V × V) => ∑ p ∈ s, kernelForm κ f p) atTop
      (nhds (∑' p, kernelForm κ f p)) := hS.hasSum
  have hcomp : Tendsto (fun u : Finset V => ∑ p ∈ u ×ˢ u, kernelForm κ f p) atTop
      (nhds (∑' p, kernelForm κ f p)) :=
    hlim.comp (tendsto_finset_prod_sq_atTop (V := V))
  exact ge_of_tendsto' hcomp fun u => kernelForm_block_nonneg hpsd f u

/-- **The bounded operator is self-adjoint** (restatement of `kernelCLM_adjoint_eq` in the
positivity package, so that the cubic-form statement below needs only this file). -/
theorem kernelCLM_adjoint (h : SchurKernel κ A) :
    ContinuousLinearMap.adjoint (kernelCLM h) = kernelCLM h :=
  kernelCLM_adjoint_eq h

/-- **The cubic form of a positive semidefinite Schur operator is nonnegative**:
`0 ≤ ⟪(T ^ 3) f, f⟫`.  This uses self-adjointness, the operator identity
`⟪T x, y⟫ = ⟪x, (adjoint T) y⟫`, and quadratic-form positivity at the vector `T f`; it is the real
counterpart of `CFC.ContinuousLinearMap.re_inner_cube_nonneg` and is the real-side input of the
Gram identity in `Realification.exists_sqrt_cube_real_operator`. -/
theorem kernelCLM_cube_form_nonneg (h : SchurKernel κ A) (hpsd : IsPSDKernel κ)
    (f : lp (fun _ : V => ℝ) 2) :
    0 ≤ inner ℝ ((kernelCLM h ^ 3) f) f := by
  have hpos := kernelCLM_quadForm_nonneg h hpsd
  have hadj := kernelCLM_adjoint h
  have hcomp : ((kernelCLM h ^ 3) f) = kernelCLM h (kernelCLM h (kernelCLM h f)) := by
    simp only [pow_succ, pow_zero, one_mul, mul_apply_eq_comp]
  rw [hcomp]
  have hstep : inner ℝ (kernelCLM h (kernelCLM h (kernelCLM h f))) f
      = inner ℝ (kernelCLM h (kernelCLM h f)) (kernelCLM h f) := by
    rw [← ContinuousLinearMap.adjoint_inner_right (kernelCLM h) (kernelCLM h (kernelCLM h f)) f,
      hadj]
  rw [hstep]
  exact hpos (kernelCLM h f)

end PercLib.CriticalLRP.CutoffPositivity
