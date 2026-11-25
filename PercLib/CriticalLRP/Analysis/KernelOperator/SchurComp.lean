
module

public import PercLib.CriticalLRP.Analysis.KernelOperator.Operator

/-!
Closure of the Schur hypothesis under composition of kernels.

Swarm `smwttizjk`, member `m2`, direction D6A.

`KernelOperator/Operator.lean` identifies the third iterate of the kernel operator with the
cube kernel only under the *extra* hypothesis `h2 : SchurKernel (kernelComp κ κ) (A * A)`.
That hypothesis is not an independent input: it follows from `SchurKernel κ A` alone, because
the composed kernel `kernelComp κ κ` again has nonnegative entries with every row sum bounded
by `A * A`.  This file discharges it, so `h2` is no longer retained anywhere.

The proof is the elementary row bound
`∑_y ∑_z κ x z κ z y = ∑_z κ x z (∑_y κ z y) ≤ ∑_z κ x z · A ≤ A · A`,
which needs the interchange of the two nonnegative lattice series (Fubini for nonnegative
sums, `summable_prod_of_nonneg` / `Summable.tsum_comm`), not symmetry and not `h2`.
-/

@[expose] public section

noncomputable section

open scoped ENNReal NNReal

namespace PercLib.CriticalLRP.KernelOperator

variable {V : Type*} {κ κ₁ κ₂ : V → V → ℝ} {A A₁ A₂ : ℝ}

/-! ### The two-kernel row bound -/

/-- **The composed double family is summable.**  Only row information is used: the row of `κ₁`
at `x` is nonnegative and summable with sum at most `A₁`, and every row of `κ₂` is nonnegative,
summable and bounded by `A₂`.  The total bound is `A₁ * A₂`, obtained by summing the finite
series `κ₁ x` against a bound of `A₂` on one row of `κ₂`.

No symmetry of either kernel is used, and no summability of `κ₂` as a two-variable family. -/
theorem summable_uncurry_comp_of_rows {κ₁ κ₂ : V → V → ℝ} {A₁ A₂ : ℝ} (x : V)
    (hn₁ : ∀ y, 0 ≤ κ₁ x y) (hs₁ : Summable (κ₁ x)) (hle₁ : (∑' y, κ₁ x y) ≤ A₁)
    (hn₂ : ∀ z y, 0 ≤ κ₂ z y) (hs₂ : ∀ z, Summable (κ₂ z))
    (hle₂ : ∀ z, (∑' y, κ₂ z y) ≤ A₂) (hA₂ : 0 ≤ A₂) :
    Summable (Function.uncurry fun z y => κ₁ x z * κ₂ z y) := by
  classical
  have hfins : ∀ u : Finset V, ∑ y ∈ u, κ₁ x y ≤ A₁ := by
    intro u
    have h1 : ∑ y ∈ u, κ₁ x y ≤ ∑' y, κ₁ x y := hs₁.sum_le_tsum u (fun i _ => hn₁ i)
    linarith
  refine summable_of_sum_le (c := A₁ * A₂)
    (fun p => mul_nonneg (hn₁ p.1) (hn₂ p.1 p.2)) fun u => ?_
  have hsub : u ⊆ u.image Prod.fst ×ˢ u.image Prod.snd := by
    intro p hp
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩
  have h1 : ∑ p ∈ u, κ₁ x p.1 * κ₂ p.1 p.2
      ≤ ∑ p ∈ u.image Prod.fst ×ˢ u.image Prod.snd, κ₁ x p.1 * κ₂ p.1 p.2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ =>
      mul_nonneg (hn₁ p.1) (hn₂ p.1 p.2)
  have h2 : ∑ p ∈ u.image Prod.fst ×ˢ u.image Prod.snd, κ₁ x p.1 * κ₂ p.1 p.2
      = ∑ z ∈ u.image Prod.fst, κ₁ x z * (∑ y ∈ u.image Prod.snd, κ₂ z y) := by
    rw [Finset.sum_product]
    exact Finset.sum_congr rfl fun z _ => by rw [Finset.mul_sum]
  have h3 : ∑ z ∈ u.image Prod.fst, κ₁ x z * (∑ y ∈ u.image Prod.snd, κ₂ z y)
      ≤ ∑ z ∈ u.image Prod.fst, κ₁ x z * A₂ := by
    refine Finset.sum_le_sum fun z _ => ?_
    refine mul_le_mul_of_nonneg_left ?_ (hn₁ z)
    calc ∑ y ∈ u.image Prod.snd, κ₂ z y ≤ ∑' y, κ₂ z y :=
          (hs₂ z).sum_le_tsum _ (fun i _ => hn₂ z i)
      _ ≤ A₂ := hle₂ z
  have h4 : ∑ z ∈ u.image Prod.fst, κ₁ x z * A₂ = (∑ z ∈ u.image Prod.fst, κ₁ x z) * A₂ :=
    (Finset.sum_mul _ _ _).symm
  have h5 : (∑ z ∈ u.image Prod.fst, κ₁ x z) * A₂ ≤ A₁ * A₂ :=
    mul_le_mul_of_nonneg_right (hfins _) hA₂
  calc ∑ p ∈ u, κ₁ x p.1 * κ₂ p.1 p.2
      ≤ ∑ p ∈ u.image Prod.fst ×ˢ u.image Prod.snd, κ₁ x p.1 * κ₂ p.1 p.2 := h1
    _ = ∑ z ∈ u.image Prod.fst, κ₁ x z * (∑ y ∈ u.image Prod.snd, κ₂ z y) := h2
    _ ≤ ∑ z ∈ u.image Prod.fst, κ₁ x z * A₂ := h3
    _ = (∑ z ∈ u.image Prod.fst, κ₁ x z) * A₂ := h4
    _ ≤ A₁ * A₂ := h5

/-! ### Row bounds for the composed kernel -/

/-- **Row summability of the composed kernel**, from row bounds alone. -/
theorem summable_comp_row_of_rows {κ₁ κ₂ : V → V → ℝ} {A₁ A₂ : ℝ} (x : V)
    (hn₁ : ∀ y, 0 ≤ κ₁ x y) (hs₁ : Summable (κ₁ x)) (hle₁ : (∑' y, κ₁ x y) ≤ A₁)
    (hn₂ : ∀ z y, 0 ≤ κ₂ z y) (hs₂ : ∀ z, Summable (κ₂ z))
    (hle₂ : ∀ z, (∑' y, κ₂ z y) ≤ A₂) (hA₂ : 0 ≤ A₂) :
    Summable fun y => kernelComp κ₁ κ₂ x y := by
  have hS := summable_uncurry_comp_of_rows (κ₁ := κ₁) (κ₂ := κ₂) (A₁ := A₁) (A₂ := A₂)
    x hn₁ hs₁ hle₁ hn₂ hs₂ hle₂ hA₂
  have hsym : Summable (fun p : V × V => κ₁ x p.2 * κ₂ p.2 p.1) := hS.prod_symm
  exact ((summable_prod_of_nonneg (f := fun p : V × V => κ₁ x p.2 * κ₂ p.2 p.1)
    fun p => mul_nonneg (hn₁ p.2) (hn₂ p.2 p.1)).mp hsym).2

/-- **The row sum of the composed kernel is at most `A₁ * A₂`.** -/
theorem tsum_comp_row_le_of_rows {κ₁ κ₂ : V → V → ℝ} {A₁ A₂ : ℝ} (x : V)
    (hn₁ : ∀ y, 0 ≤ κ₁ x y) (hs₁ : Summable (κ₁ x)) (hle₁ : (∑' y, κ₁ x y) ≤ A₁)
    (hn₂ : ∀ z y, 0 ≤ κ₂ z y) (hs₂ : ∀ z, Summable (κ₂ z))
    (hle₂ : ∀ z, (∑' y, κ₂ z y) ≤ A₂) (hA₂ : 0 ≤ A₂) :
    ∑' y, kernelComp κ₁ κ₂ x y ≤ A₁ * A₂ := by
  have hS := summable_uncurry_comp_of_rows (κ₁ := κ₁) (κ₂ := κ₂) (A₁ := A₁) (A₂ := A₂)
    x hn₁ hs₁ hle₁ hn₂ hs₂ hle₂ hA₂
  have hrow : Summable fun z => ∑' y, κ₁ x z * κ₂ z y :=
    ((summable_prod_of_nonneg (f := Function.uncurry fun z y => κ₁ x z * κ₂ z y)
      fun p => mul_nonneg (hn₁ p.1) (hn₂ p.1 p.2)).mp hS).2
  have hcomm : ∑' y, ∑' z, κ₁ x z * κ₂ z y = ∑' z, ∑' y, κ₁ x z * κ₂ z y :=
    Summable.tsum_comm (f := fun z y => κ₁ x z * κ₂ z y) hS
  have hstep : ∀ z, (∑' y, κ₁ x z * κ₂ z y) = κ₁ x z * (∑' y, κ₂ z y) := by
    intro z
    exact tsum_mul_left
  have hmajor : ∑' z, κ₁ x z * (∑' y, κ₂ z y) ≤ ∑' z, κ₁ x z * A₂ := by
    have hcmp : ∀ z, κ₁ x z * (∑' y, κ₂ z y) ≤ κ₁ x z * A₂ := fun z =>
      mul_le_mul_of_nonneg_left (hle₂ z) (hn₁ z)
    have hsumA : Summable fun z => κ₁ x z * A₂ := hs₁.mul_right A₂
    have hsumB : Summable fun z => κ₁ x z * (∑' y, κ₂ z y) :=
      Summable.of_nonneg_of_le (fun z => mul_nonneg (hn₁ z) (tsum_nonneg (hn₂ z))) hcmp hsumA
    exact Summable.tsum_le_tsum hcmp hsumB hsumA
  calc ∑' y, kernelComp κ₁ κ₂ x y
      = ∑' y, ∑' z, κ₁ x z * κ₂ z y := rfl
    _ = ∑' z, ∑' y, κ₁ x z * κ₂ z y := hcomm
    _ = ∑' z, κ₁ x z * (∑' y, κ₂ z y) := tsum_congr hstep
    _ ≤ ∑' z, κ₁ x z * A₂ := hmajor
    _ = (∑' z, κ₁ x z) * A₂ := tsum_mul_right
    _ ≤ A₁ * A₂ := mul_le_mul_of_nonneg_right hle₁ hA₂

/-! ### Symmetry of the composed kernel -/

/-- **Composition with two symmetric kernels is adjoint-transpose.**  The identity
`∑_z κ₁ x z κ₂ z y = ∑_z κ₂ y z κ₁ z x` is a termwise rewrite using the two symmetries: both
sides have summand `κ₁ z x · κ₂ y z` (up to commutativity), so no interchange is needed. -/
theorem kernelComp_swap_of_symm {κ₁ κ₂ : V → V → ℝ}
    (h₁ : ∀ x y, κ₁ x y = κ₁ y x) (h₂ : ∀ x y, κ₂ x y = κ₂ y x) (x y : V) :
    kernelComp κ₁ κ₂ x y = kernelComp κ₂ κ₁ y x := by
  rw [kernelComp, kernelComp]
  exact tsum_congr fun z => by rw [h₁ x z, h₂ z y, mul_comm]

/-- **The composed kernel of a symmetric kernel is symmetric.** -/
theorem kernelComp_symm {κ : V → V → ℝ} (h : ∀ x y, κ x y = κ y x) (x y : V) :
    kernelComp κ κ x y = kernelComp κ κ y x :=
  kernelComp_swap_of_symm h h x y

/-! ### The Schur closure theorems -/

/-- **`SchurKernel` is closed under composition with itself**: the two-fold kernel again has
nonnegative entries, is symmetric, and has every row sum bounded by `A * A`.  This is exactly
the hypothesis `h2` that `kernelApply_three_eq` previously had to assume. -/
theorem schurKernel_kernelComp (h : SchurKernel κ A) : SchurKernel (kernelComp κ κ) (A * A) where
  nonneg := fun x y => tsum_nonneg fun z => mul_nonneg (h.nonneg x z) (h.nonneg z y)
  symm := kernelComp_symm h.symm
  nonneg_A := mul_nonneg h.A_nonneg h.A_nonneg
  row_summable := fun x =>
    summable_comp_row_of_rows (κ₁ := κ) (κ₂ := κ) (A₁ := A) (A₂ := A) x
      (fun y => h.nonneg x y) (h.row_summable x) (h.row_le x)
      (fun z y => h.nonneg z y) h.row_summable h.row_le h.A_nonneg
  row_le := fun x =>
    tsum_comp_row_le_of_rows (κ₁ := κ) (κ₂ := κ) (A₁ := A) (A₂ := A) x
      (fun y => h.nonneg x y) (h.row_summable x) (h.row_le x)
      (fun z y => h.nonneg z y) h.row_summable h.row_le h.A_nonneg

/-! ### The cube kernel is again a Schur kernel -/

/-- **The cube kernel is a Schur kernel with constant `A * (A * A)`.**  Immediate from the
two-kernel row bound with `κ₁ = κ` and `κ₂ = kernelComp κ κ`, whose rows are bounded by
`A * A` by `schurKernel_kernelComp`; symmetry is the transpose identity
`kernelComp_swap_of_symm` combined with associativity `kernelComp_assoc`. -/
theorem schurKernel_kernelCube (h : SchurKernel κ A) :
    SchurKernel (kernelCube κ) (A * (A * A)) where
  nonneg := fun x y =>
    tsum_nonneg fun z => mul_nonneg (h.nonneg x z)
      (tsum_nonneg fun w => mul_nonneg (h.nonneg z w) (h.nonneg w y))
  symm := fun x y =>
    (kernelComp_swap_of_symm (κ₁ := κ) (κ₂ := kernelComp κ κ) h.symm
      (kernelComp_symm h.symm) x y).trans (kernelComp_assoc h y x)
  nonneg_A := mul_nonneg h.A_nonneg (mul_nonneg h.A_nonneg h.A_nonneg)
  row_summable := fun x =>
    summable_comp_row_of_rows (κ₁ := κ) (κ₂ := kernelComp κ κ) (A₁ := A) (A₂ := A * A) x
      (fun y => h.nonneg x y) (h.row_summable x) (h.row_le x)
      (fun z y => (schurKernel_kernelComp h).nonneg z y)
      (schurKernel_kernelComp h).row_summable (schurKernel_kernelComp h).row_le
      (mul_nonneg h.A_nonneg h.A_nonneg)
  row_le := fun x =>
    tsum_comp_row_le_of_rows (κ₁ := κ) (κ₂ := kernelComp κ κ) (A₁ := A) (A₂ := A * A) x
      (fun y => h.nonneg x y) (h.row_summable x) (h.row_le x)
      (fun z y => (schurKernel_kernelComp h).nonneg z y)
      (schurKernel_kernelComp h).row_summable (schurKernel_kernelComp h).row_le
      (mul_nonneg h.A_nonneg h.A_nonneg)

/-- **The third iterate of the kernel operator has the cube kernel, unconditionally.**  The
Schur hypothesis `h2` on the two-fold kernel that `kernelApply_three_eq` carries is discharged
by `schurKernel_kernelComp`, so the conclusion only assumes `SchurKernel κ A`. -/
theorem kernelApply_three_eq_of_schurKernel (h : SchurKernel κ A) {g : V → ℝ}
    (hgs : Summable fun z => g z ^ 2) (x : V) :
    kernelApply κ (kernelApply κ (kernelApply κ g)) x = ∑' z, kernelCube κ x z * g z :=
  kernelApply_three_eq h (schurKernel_kernelComp h) hgs x

/-- **The cube kernel operator is the third iterate.**  This is the operator-level form of
`kernelApply_three_eq_of_schurKernel`: the three-fold iterate of `kernelApply κ` is the kernel
operator of `kernelCube κ`, with no side hypothesis on the two-fold kernel. -/
theorem kernelApply_cube_eq (h : SchurKernel κ A) {g : V → ℝ}
    (hgs : Summable fun z => g z ^ 2) (x : V) :
    kernelApply (kernelCube κ) g x = kernelApply κ (kernelApply κ (kernelApply κ g)) x :=
  (kernelApply_three_eq_of_schurKernel h hgs x).symm

/-- **The cube operator is bounded on `ℓ²` with norm at most `A * (A * A)`.**  The Schur bound
applied to the cube kernel, whose Schur hypothesis is now derived from `SchurKernel κ A`. -/
theorem kernelCube_tsum_sq_le (h : SchurKernel κ A) (g : V → ℝ)
    (hgs : Summable fun y => g y ^ 2) :
    Summable (fun x => kernelApply (kernelCube κ) g x ^ 2) ∧
      ∑' x, kernelApply (kernelCube κ) g x ^ 2
        ≤ A * (A * A) * (A * (A * A)) * ∑' y, g y ^ 2 := by
  have hcube := schur_tsum_sq_kernelApply_le (schurKernel_kernelCube h) g hgs
  refine ⟨hcube.1, le_trans hcube.2 (le_of_eq ?_)⟩
  rw [mul_pow]
  ring

end PercLib.CriticalLRP.KernelOperator
