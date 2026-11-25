/-
Quadratic-form positivity of the Schur kernel operator, and the cutoff two-point instance.

Swarm `smwtxo95t`, member `m6`, direction (E).

This is the *definition* layer: the predicate "the real quadratic form of a bounded operator on
`ℓ²(V; ℝ)` is nonnegative", the cutoff two-point operator as a bounded `ℝ`-linear map at a finite
first cutoff moment, and the kernel double family whose lattice sum is the quadratic form.  No
theorem is stated here.
-/
module

public import PercLib.CriticalLRP.Analysis.KernelOperator.InnerProduct
public import PercLib.CriticalLRP.Analysis.KernelOperator.CutoffComp
public import PercLib.CriticalLRP.Analysis.Cutoff.PSD

/-!
# Definitions: quadratic-form nonnegativity and the cutoff two-point operator

The predicate `QuadFormNonneg`, the kernel double family `kernelForm`, and the bounded cutoff
two-point operator `cutKernelCLM` at a finite first cutoff moment.  No theorem here.
-/

@[expose] public section

noncomputable section

open scoped ENNReal NNReal lp

namespace PercLib.CriticalLRP.CutoffPositivity

open PercLib.CriticalLRP.KernelOperator
open PercLib.CriticalLRP.Orchestration

variable {V : Type*}

/-- **Quadratic-form nonnegativity** of a real bounded operator on `ℓ²(V; ℝ)`: every value of the
quadratic form `f ↦ ⟪T f, f⟫` is nonnegative.  This is the real form of the Loewner-order
condition `0 ≤ T`, kept as an explicit predicate because the campaign only has positivity data on
the real side. -/
def QuadFormNonneg (T : lp (fun _ : V => ℝ) 2 →L[ℝ] lp (fun _ : V => ℝ) 2) : Prop :=
  ∀ f : lp (fun _ : V => ℝ) 2, 0 ≤ inner ℝ (T f) f

/-- The **double family of a kernel** against a fixed `ℓ²` vector: its lattice sum over
`V × V` is the quadratic form of the kernel operator (`inner_kernelCLM_eq_kernelForm`). -/
noncomputable def kernelForm (κ : V → V → ℝ) (f : lp (fun _ : V => ℝ) 2) (p : V × V) : ℝ :=
  κ p.1 p.2 * (f : V → ℝ) p.1 * (f : V → ℝ) p.2

/-- **The range-truncated two-point operator**, as a genuine bounded `ℝ`-linear operator on
`ℓ²(V; ℝ)`, at the actual cutoff law.  The only hypothesis is finiteness of the first cutoff
moment `M.cutMassAt r 0`, which is what makes every row of the truncated two-point matrix
summable with a uniform bound. -/
noncomputable def cutKernelCLM (M : SourceModelData) (r : ℝ) (hχ : M.cutMassAt r 0 ≠ ⊤) :
    lp (fun _ : M.V => ℝ) 2 →L[ℝ] lp (fun _ : M.V => ℝ) 2 :=
  kernelCLM (cutTwoPoint_schurKernel M r hχ)

end PercLib.CriticalLRP.CutoffPositivity
