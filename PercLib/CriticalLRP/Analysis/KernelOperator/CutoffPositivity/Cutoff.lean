/-
Quadratic-form positivity of the cutoff two-point operator at a finite first cutoff moment.

Swarm `smwtxo95t`, member `m6`, direction (E).

`Analysis/Cutoff/PSD.lean` proves that the range-truncated two-point matrix is positive
semidefinite on every finite vertex set (`cutTwoPoint_posSemidef`, from the production
Gram decomposition), and `KernelOperator/Model.lean` proves that finite first cutoff moment
`M.cutMassAt r 0 ≠ ⊤` makes the truncated two-point matrix a Schur kernel with constant
`(M.cutMassAt r 0).toReal`.  This file combines the two with `kernelCLM_quadForm_nonneg`:

* `cutKernel_isPSDKernel` : `IsPSDKernel (cutKernel M r)` at *every* radius (no moment hypothesis),
* `cutKernelCLM_quadForm_nonneg` : `0 ≤ ⟪T f, f⟫` for the bounded cutoff operator at finite first
  moment,
* `cutKernelCLM_cube_form_nonneg` : `0 ≤ ⟪(T ^ 3) f, f⟫`,
* `exists_sqrt_cube_cutKernelCLM` : the CFC square root of `Tℂ ^ 3` at the cutoff, with the complex
  extension kept as an explicit hypothesis.

Nothing here infers finiteness of the cutoff moment at any radius other than the one where it is
hypothetical, and no criticality, Schur bound at the critical kernel, or Kozma-type identity is
asserted.
-/
module

public import PercLib.CriticalLRP.Analysis.KernelOperator.CutoffPositivity.Basic
public import PercLib.CriticalLRP.Analysis.KernelOperator.CFC

/-!
# Cutoff two-point operator: quadratic and cubic forms

`IsPSDKernel (cutKernel M r)` from the finite-matrix positivity at the truncated law, the quadratic
and cubic forms of `cutKernelCLM` at finite first cutoff moment, and the conditional CFC square
root of its cube.
-/

@[expose] public section

noncomputable section

open scoped ENNReal NNReal lp InnerProduct

namespace PercLib.CriticalLRP.CutoffPositivity

open PercLib.CriticalLRP.KernelOperator
open PercLib.CriticalLRP.Orchestration

/-! ### The truncated two-point matrix is positive semidefinite on every finite vertex set -/

/-- **The truncated two-point kernel is positive semidefinite as a kernel**: every finite quadratic
form `∑_{x ∈ s} ∑_{y ∈ s} κ x y v x v y` is nonnegative.  Transferred from
`SourceModelData.cutTwoPoint_posSemidef`, the finite-matrix statement obtained from the production
cluster Gram decomposition.  No summability or moment hypothesis is used. -/
theorem cutKernel_isPSDKernel (M : SourceModelData) (r : ℝ) :
    IsPSDKernel (cutKernel M r) := by
  classical
  intro s v
  have h := M.cutTwoPoint_posSemidef r (f := fun i : s => (i : M.V))
  have hnn : 0 ≤ dotProduct (fun i : s => star (v i.val))
      (Matrix.mulVec (Matrix.of fun i j : s => M.cutTwoPoint r i.val j.val)
        (fun i : s => v i.val)) :=
    h.dotProduct_mulVec_nonneg (fun i : s => v i.val)
  have hEq : dotProduct (fun i : s => star (v i.val))
      (Matrix.mulVec (Matrix.of fun i j : s => M.cutTwoPoint r i.val j.val)
        (fun i : s => v i.val))
      = ∑ x ∈ s, ∑ y ∈ s, cutKernel M r x y * v x * v y := by
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, star_trivial, cutKernel]
    rw [← Finset.sum_coe_sort s
      (fun x : M.V => ∑ y ∈ s, M.cutTwoPoint r x y * v x * v y)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_coe_sort s (fun y : M.V => M.cutTwoPoint r i.val y * v i.val * v y),
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  exact le_of_le_of_eq hnn hEq

/-! ### The cutoff operator and its quadratic form -/

/-- **The cutoff two-point operator has a nonnegative quadratic form at finite first cutoff
moment.**  Both numerical inputs are hypotheses of this statement and nothing is inferred beyond
the actual radius: `hχ` is finiteness of the first cutoff moment at `r` (boundedness of the
operator) and `cutKernel_isPSDKernel` is the finite-matrix positivity at the same truncated law. -/
theorem cutKernelCLM_quadForm_nonneg (M : SourceModelData) (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) :
    QuadFormNonneg (cutKernelCLM M r hχ) :=
  kernelCLM_quadForm_nonneg (cutTwoPoint_schurKernel M r hχ) (cutKernel_isPSDKernel M r)

/-- **The cubic form of the cutoff operator is nonnegative**: `0 ≤ ⟪(T ^ 3) f, f⟫` at finite first
cutoff moment.  This is the real-side positivity consumed by the Gram identity of the CFC square
root of `T ^ 3`. -/
theorem cutKernelCLM_cube_form_nonneg (M : SourceModelData) (r : ℝ)
    (hχ : M.cutMassAt r 0 ≠ ⊤) (f : lp (fun _ : M.V => ℝ) 2) :
    0 ≤ inner ℝ ((cutKernelCLM M r hχ ^ 3) f) f :=
  kernelCLM_cube_form_nonneg (cutTwoPoint_schurKernel M r hχ) (cutKernel_isPSDKernel M r) f

/-- **The cutoff operator is self-adjoint**, from symmetry of the truncated two-point function. -/
theorem cutKernelCLM_adjoint (M : SourceModelData) (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) :
    ContinuousLinearMap.adjoint (cutKernelCLM M r hχ) = cutKernelCLM M r hχ :=
  kernelCLM_adjoint (cutTwoPoint_schurKernel M r hχ)

/-- **The operator norm of the cutoff two-point operator is at most the first cutoff moment.**
This is the Schur bound that the finite-moment hypothesis `hχ` supplies; it is the `A = χ(r)` case
of `kernelCLM_norm_le`. -/
theorem cutKernelCLM_norm_le (M : SourceModelData) (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) :
    ‖cutKernelCLM M r hχ‖ ≤ (M.cutMassAt r 0).toReal :=
  kernelCLM_norm_le (cutTwoPoint_schurKernel M r hχ)

/-! ### Downstream: the CFC square root of the cube, conditionally on a complex extension -/

/-- **The CFC square root of the cutoff cube.**  At finite first cutoff moment, with a
complex-linear operator `Tℂ` on `ℓ²(V; ℂ)` extending the real cutoff operator and self-adjoint,
`S = CFC.sqrt (Tℂ ^ 3)` is a nonnegative self-adjoint square root of `Tℂ ^ 3`, and its Gram form on
real vectors is the real cubic form `⟪T ^ 3 a, a⟫_ℝ`.

The complex extension is an explicit hypothesis: this snapshot has no real CFC, so complexification
cannot be constructed here.  No criticality and no identification with a Kozma operator is
asserted. -/
theorem exists_sqrt_cube_cutKernelCLM (M : SourceModelData) (r : ℝ)
    (hχ : M.cutMassAt r 0 ≠ ⊤)
    (Tℂ : lp (fun _ : M.V => ℂ) 2 →L[ℂ] lp (fun _ : M.V => ℂ) 2)
    (hT : ∀ a, Tℂ (Realification.ofRealLp a) = Realification.ofRealLp (cutKernelCLM M r hχ a))
    (hsa : IsSelfAdjoint Tℂ) :
    ∃ S : lp (fun _ : M.V => ℂ) 2 →L[ℂ] lp (fun _ : M.V => ℂ) 2,
      0 ≤ S ∧ S† = S ∧ S† * S = Tℂ ^ 3 ∧
        ∀ a, inner ℝ ((cutKernelCLM M r hχ ^ 3) a) a
          = RCLike.re (inner ℂ (S (Realification.ofRealLp a))
              (S (Realification.ofRealLp a))) :=
  Realification.exists_sqrt_cube_real_operator (cutKernelCLM M r hχ) Tℂ hT hsa
    (cutKernelCLM_quadForm_nonneg M r hχ)

end PercLib.CriticalLRP.CutoffPositivity
