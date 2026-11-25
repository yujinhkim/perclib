/-
The Schur test for the kernel operator on `ℓ²`, at the level of lattice series.

Swarm `smwtrtcqs`, member `m1`, direction D6.  The hypotheses are collected in
`SchurKernel`: a nonnegative symmetric kernel whose rows are summable with a uniform bound `A`.
Under them, `kernelApply κ` maps `ℓ²` to `ℓ²` with norm at most `A`, is self-adjoint, and is
positive when the kernel is positive semidefinite.
-/
module

public import Mathlib
public import PercLib.CriticalLRP.Analysis.KernelOperator.Defs

@[expose] public section

noncomputable section

open scoped ENNReal NNReal

namespace PercLib.CriticalLRP.KernelOperator

variable {V : Type*}

/-! ### Weighted Cauchy–Schwarz for lattice series -/

/-- **Weighted Cauchy–Schwarz.** For nonnegative `a`, `b` with `∑ a` and `∑ a b²` convergent,
`(∑ a b)² ≤ (∑ a)(∑ a b²)`.  This is Cauchy–Schwarz for the vectors `√a` and `√a · b`. -/
theorem sq_tsum_mul_le {a b : V → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hsa : Summable a) (hsab : Summable fun i => a i * b i ^ 2) :
    (∑' i, a i * b i) ^ 2 ≤ (∑' i, a i) * ∑' i, a i * b i ^ 2 := by
  have hf : ∀ i, 0 ≤ Real.sqrt (a i) := fun i => Real.sqrt_nonneg _
  have hg : ∀ i, 0 ≤ Real.sqrt (a i) * b i := fun i => mul_nonneg (hf i) (hb i)
  have hsf : Summable fun i => Real.sqrt (a i) ^ (2 : ℝ) := by
    refine hsa.congr fun i => ?_
    rw [Real.rpow_two, Real.sq_sqrt (ha i)]
  have hsg : Summable fun i => (Real.sqrt (a i) * b i) ^ (2 : ℝ) := by
    refine hsab.congr fun i => ?_
    rw [Real.rpow_two, mul_pow, Real.sq_sqrt (ha i)]
  have hmain := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg (f := fun i => Real.sqrt (a i))
    (g := fun i => Real.sqrt (a i) * b i) (p := 2) (q := 2)
    (by norm_num [Real.holderConjugate_iff]) hf hg hsf hsg
  have hlhs : (∑' i, Real.sqrt (a i) * (Real.sqrt (a i) * b i)) = ∑' i, a i * b i := by
    refine tsum_congr fun i => ?_
    rw [← mul_assoc, Real.mul_self_sqrt (ha i)]
  rw [hlhs] at hmain
  have hAs : (∑' i, Real.sqrt (a i) ^ (2 : ℝ)) = ∑' i, a i := by
    refine tsum_congr fun i => ?_
    rw [Real.rpow_two, Real.sq_sqrt (ha i)]
  have hBs : (∑' i, (Real.sqrt (a i) * b i) ^ (2 : ℝ)) = ∑' i, a i * b i ^ 2 := by
    refine tsum_congr fun i => ?_
    rw [Real.rpow_two, mul_pow, Real.sq_sqrt (ha i)]
  rw [hAs, hBs] at hmain
  have hA0 : 0 ≤ ∑' i, a i := tsum_nonneg ha
  have hB0 : 0 ≤ ∑' i, a i * b i ^ 2 :=
    tsum_nonneg fun i => mul_nonneg (ha i) (sq_nonneg _)
  have hprod : ((∑' i, a i) ^ (1 / 2 : ℝ) * (∑' i, a i * b i ^ 2) ^ (1 / 2 : ℝ)) ^ 2
      = (∑' i, a i) * ∑' i, a i * b i ^ 2 := by
    rw [mul_pow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sq_sqrt hA0,
      Real.sq_sqrt hB0]
  calc (∑' i, a i * b i) ^ 2
      ≤ ((∑' i, a i) ^ (1 / 2 : ℝ) * (∑' i, a i * b i ^ 2) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (tsum_nonneg fun i => mul_nonneg (ha i) (hb i)) hmain 2
    _ = (∑' i, a i) * ∑' i, a i * b i ^ 2 := hprod

/-! ### The Schur kernel: rows, row bounds, and weighted rows -/

section Schur

variable {κ : V → V → ℝ} {A : ℝ}

theorem SchurKernel.A_nonneg (h : SchurKernel κ A) : 0 ≤ A := h.nonneg_A

/-- Finite partial sums of a row are bounded by the row constant. -/
theorem SchurKernel.row_finset_le (h : SchurKernel κ A) (x : V) (u : Finset V) :
    ∑ y ∈ u, κ x y ≤ A := by
  have h1 : ∑ y ∈ u, κ x y ≤ ∑' y, κ x y :=
    (h.row_summable x).sum_le_tsum u (fun i _ => h.nonneg x i)
  linarith [h.row_le x]

/-- A single square is at most the `ℓ²` mass. -/
theorem sq_le_tsum_sq {f : V → ℝ} (hf : Summable fun y => f y ^ 2) (y : V) :
    f y ^ 2 ≤ ∑' y, f y ^ 2 := by
  have h1 : ∑ i ∈ ({y} : Finset V), f i ^ 2 ≤ ∑' i, f i ^ 2 :=
    hf.sum_le_tsum {y} (fun i _ => sq_nonneg (f i))
  simpa using h1

/-- **Weighted rows are summable.** -/
theorem schur_summable_row_mul_sq (h : SchurKernel κ A) {f : V → ℝ}
    (hf : Summable fun y => f y ^ 2) (x : V) :
    Summable fun y => κ x y * f y ^ 2 := by
  have hB : 0 ≤ ∑' y, f y ^ 2 := tsum_nonneg fun y => sq_nonneg (f y)
  refine summable_of_sum_le (c := (∑' y, f y ^ 2) * A)
    (fun y => mul_nonneg (h.nonneg x y) (sq_nonneg (f y))) fun u => ?_
  have h1 : ∑ y ∈ u, κ x y * f y ^ 2 ≤ ∑ y ∈ u, κ x y * (∑' y, f y ^ 2) :=
    Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (sq_le_tsum_sq hf y) (h.nonneg x y)
  have h2 : ∑ y ∈ u, κ x y * (∑' y, f y ^ 2) = (∑' y, f y ^ 2) * ∑ y ∈ u, κ x y := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => mul_comm _ _
  have h3 : (∑' y, f y ^ 2) * ∑ y ∈ u, κ x y ≤ (∑' y, f y ^ 2) * A :=
    mul_le_mul_of_nonneg_left (h.row_finset_le x u) hB
  linarith

/-- **The weighted row sum is at most `A` times the `ℓ²` mass.** -/
theorem schur_tsum_row_mul_sq_le (h : SchurKernel κ A) {f : V → ℝ}
    (hf : Summable fun y => f y ^ 2) (x : V) :
    ∑' y, κ x y * f y ^ 2 ≤ A * ∑' y, f y ^ 2 := by
  have hB : 0 ≤ ∑' y, f y ^ 2 := tsum_nonneg fun y => sq_nonneg (f y)
  have hdom : Summable fun y => (∑' y, f y ^ 2) * κ x y := (h.row_summable x).mul_left _
  have hpt : ∀ y, κ x y * f y ^ 2 ≤ (∑' y, f y ^ 2) * κ x y := by
    intro y
    calc κ x y * f y ^ 2 ≤ κ x y * (∑' y, f y ^ 2) :=
          mul_le_mul_of_nonneg_left (sq_le_tsum_sq hf y) (h.nonneg x y)
      _ = (∑' y, f y ^ 2) * κ x y := mul_comm _ _
  calc ∑' y, κ x y * f y ^ 2
      ≤ ∑' y, (∑' y, f y ^ 2) * κ x y :=
        Summable.tsum_le_tsum hpt (schur_summable_row_mul_sq h hf x) hdom
    _ = (∑' y, f y ^ 2) * ∑' y, κ x y := tsum_mul_left
    _ ≤ (∑' y, f y ^ 2) * A := mul_le_mul_of_nonneg_left (h.row_le x) hB
    _ = A * ∑' y, f y ^ 2 := mul_comm _ _

/-- **Pointwise Cauchy–Schwarz at one vertex**: for nonnegative `f`, the square of the kernel
series is controlled by the row constant times the weighted row. -/
theorem schur_sq_kernelApply_le (h : SchurKernel κ A) {f : V → ℝ} (hf : ∀ y, 0 ≤ f y)
    (hfs : Summable fun y => f y ^ 2) (x : V) :
    kernelApply κ f x ^ 2 ≤ A * ∑' y, κ x y * f y ^ 2 := by
  have hCS := sq_tsum_mul_le (a := κ x) (b := f) (fun y => h.nonneg x y) hf
    (h.row_summable x) (schur_summable_row_mul_sq h hfs x)
  have hnn : 0 ≤ ∑' y, κ x y * f y ^ 2 :=
    tsum_nonneg fun y => mul_nonneg (h.nonneg x y) (sq_nonneg _)
  calc kernelApply κ f x ^ 2 = (∑' y, κ x y * f y) ^ 2 := rfl
    _ ≤ (∑' y, κ x y) * (∑' y, κ x y * f y ^ 2) := hCS
    _ ≤ A * (∑' y, κ x y * f y ^ 2) := mul_le_mul_of_nonneg_right (h.row_le x) hnn

/-! ### Summability of the double family (Fubini input) -/

/-- **The weighted double row family is summable.**  The bound is the product of the row
constant and the `ℓ²` mass; symmetry is used to turn the sum over a column into a row. -/
theorem schur_summable_uncurry (h : SchurKernel κ A) {f : V → ℝ}
    (hfs : Summable fun y => f y ^ 2) :
    Summable (Function.uncurry fun x y => κ x y * f y ^ 2) := by
  classical
  have hB : 0 ≤ ∑' y, f y ^ 2 := tsum_nonneg fun y => sq_nonneg (f y)
  have hA : 0 ≤ A := h.A_nonneg
  refine summable_of_sum_le (c := A * ∑' y, f y ^ 2)
    (fun p => mul_nonneg (h.nonneg p.1 p.2) (sq_nonneg _)) fun u => ?_
  have hsub : u ⊆ u.image Prod.fst ×ˢ u.image Prod.snd := by
    intro p hp
    rw [Finset.mem_product]
    exact ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩
  have hstep1 : ∑ p ∈ u, κ p.1 p.2 * f p.2 ^ 2
      ≤ ∑ p ∈ u.image Prod.fst ×ˢ u.image Prod.snd, κ p.1 p.2 * f p.2 ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun p _ _ =>
      mul_nonneg (h.nonneg p.1 p.2) (sq_nonneg _)
  have hstep2 : ∑ p ∈ u.image Prod.fst ×ˢ u.image Prod.snd, κ p.1 p.2 * f p.2 ^ 2
      = ∑ y ∈ u.image Prod.snd, (∑ x ∈ u.image Prod.fst, κ x y) * f y ^ 2 := by
    rw [Finset.sum_product, Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_mul]
  have hstep3 : ∑ y ∈ u.image Prod.snd, (∑ x ∈ u.image Prod.fst, κ x y) * f y ^ 2
      ≤ ∑ y ∈ u.image Prod.snd, A * f y ^ 2 := by
    refine Finset.sum_le_sum fun y _ => ?_
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    calc ∑ x ∈ u.image Prod.fst, κ x y = ∑ x ∈ u.image Prod.fst, κ y x :=
          Finset.sum_congr rfl fun x _ => h.symm x y
      _ ≤ A := h.row_finset_le y _
  have hstep4 : ∑ y ∈ u.image Prod.snd, A * f y ^ 2 ≤ A * ∑' y, f y ^ 2 := by
    have hs : ∑ y ∈ u.image Prod.snd, f y ^ 2 ≤ ∑' y, f y ^ 2 :=
      hfs.sum_le_tsum _ (fun i _ => sq_nonneg _)
    calc ∑ y ∈ u.image Prod.snd, A * f y ^ 2
        = A * ∑ y ∈ u.image Prod.snd, f y ^ 2 := (Finset.mul_sum _ _ _).symm
      _ ≤ A * ∑' y, f y ^ 2 := mul_le_mul_of_nonneg_left hs hA
  calc ∑ p ∈ u, κ p.1 p.2 * f p.2 ^ 2
      ≤ ∑ p ∈ u.image Prod.fst ×ˢ u.image Prod.snd, κ p.1 p.2 * f p.2 ^ 2 := hstep1
    _ = ∑ y ∈ u.image Prod.snd, (∑ x ∈ u.image Prod.fst, κ x y) * f y ^ 2 := hstep2
    _ ≤ ∑ y ∈ u.image Prod.snd, A * f y ^ 2 := hstep3
    _ ≤ A * ∑' y, f y ^ 2 := hstep4

end Schur

end PercLib.CriticalLRP.KernelOperator
