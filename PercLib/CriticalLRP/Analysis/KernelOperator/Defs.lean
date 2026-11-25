/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.

Candidate definition layer for the `ℓ²` operator of the two-point kernel.

Swarm `smwtrtcqs`, member `m1`, direction D6 (actual two-point operator / triangle
identification).  This is a *candidate* `Defs.lean`: it is not imported by the package and
asserts no theorem.

The mathematical object is the linear operator attached to a kernel `κ : V → V → ℝ` by
`(T_κ f)(x) = ∑'_y κ x y * f y`, together with the two structural predicates it needs
(symmetric nonnegative kernel with a uniform row-sum bound; positive semidefinite kernel on
finite quadratic forms) and the kernel composition whose iterate gives the matrix powers.
-/
module

public import Mathlib

@[expose] public section

noncomputable section

open scoped ENNReal NNReal

namespace PercLib.CriticalLRP.KernelOperator

variable {V : Type*}

/-- The action of the kernel `κ` on a function `f`, written as a lattice series:
`(kernelApply κ f) x = ∑'_y κ x y * f y`.  No convergence is asserted by the definition; the
theorems below supply it. -/
noncomputable def kernelApply (κ : V → V → ℝ) (f : V → ℝ) (x : V) : ℝ :=
  ∑' y, κ x y * f y

/-- **The Schur hypothesis on a kernel**: nonnegative, symmetric, and with a uniform bound `A`
on its row sums.  This is exactly the hypothesis under which the Schur test bounds the operator
`kernelApply κ` on `ℓ²`. -/
structure SchurKernel (κ : V → V → ℝ) (A : ℝ) : Prop where
  /-- All entries are nonnegative. -/
  nonneg : ∀ x y, 0 ≤ κ x y
  /-- The kernel is symmetric. -/
  symm : ∀ x y, κ x y = κ y x
  /-- The row constant is nonnegative. -/
  nonneg_A : 0 ≤ A
  /-- Every row is summable. -/
  row_summable : ∀ x, Summable (κ x)
  /-- Every row sums to at most `A`. -/
  row_le : ∀ x, ∑' y, κ x y ≤ A

/-- A kernel is positive semidefinite when every finite quadratic form it defines is
nonnegative.  Restricting to finite vertex sets is what makes this a property of the kernel
alone (no summability), and it is the form in which the model's `posSemidef_tau` is available. -/
def IsPSDKernel (κ : V → V → ℝ) : Prop :=
  ∀ (s : Finset V) (v : V → ℝ), 0 ≤ ∑ x ∈ s, ∑ y ∈ s, κ x y * v x * v y

/-- Composition of kernels: `(kernelComp κ κ') x y = ∑'_z κ x z * κ' z y`.  The `n`-fold
iterate of `kernelComp κ` with itself is the `n`-th matrix power of `κ`. -/
noncomputable def kernelComp (κ κ' : V → V → ℝ) (x y : V) : ℝ :=
  ∑' z, κ x z * κ' z y

/-- The kernel of the third matrix power `κ³`. -/
noncomputable def kernelCube (κ : V → V → ℝ) (x y : V) : ℝ :=
  kernelComp κ (kernelComp κ κ) x y

/-- A function is finitely supported when its support is a finite set. -/
abbrev FinitelySupported (f : V → ℝ) : Prop := (Function.support f).Finite

end PercLib.CriticalLRP.KernelOperator
