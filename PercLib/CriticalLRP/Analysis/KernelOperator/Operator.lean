/-
The kernel operator on `ℓ²`: norm bound, translation invariance, positivity, and the
identification of its third power with the triple kernel sum.

Swarm `smwtrtcqs`, member `m1`, direction D6.
-/
module

public import Mathlib
public import PercLib.CriticalLRP.Analysis.KernelOperator.Schur

@[expose] public section

noncomputable section

open scoped ENNReal NNReal


namespace PercLib.CriticalLRP.KernelOperator

variable {V : Type*}
variable {κ : V → V → ℝ} {A : ℝ}

/-! ### The `ℓ²` bound -/

/-- Bound on a single kernel series, for arbitrary (signed) `f`. -/
theorem abs_kernelApply_le (h : SchurKernel κ A) {f : V → ℝ}
    (hfs : Summable fun y => f y ^ 2) (x : V) :
    |kernelApply κ f x| ≤ A * Real.sqrt (∑' y, f y ^ 2) := by
  have habs : Summable fun y => |f y| ^ 2 := by simpa [sq_abs] using hfs
  have hrow : Summable fun y => κ x y * |f y| ^ 2 := schur_summable_row_mul_sq h habs x
  have hsum : Summable fun y => κ x y * |f y| := by
    have hdom : Summable fun y => (1 / 2) * (κ x y + κ x y * |f y| ^ 2) :=
      ((h.row_summable x).add hrow).mul_left (1 / 2)
    exact Summable.of_nonneg_of_le (fun y => mul_nonneg (h.nonneg x y) (abs_nonneg _))
      (fun y => by nlinarith [h.nonneg x y, sq_nonneg (|f y| - 1)]) hdom
  have habsrow : (∑' y, ‖κ x y * f y‖) = ∑' y, κ x y * |f y| := by
    refine tsum_congr fun y => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (h.nonneg x y)]
  have hnorm : Summable fun y => ‖κ x y * f y‖ := by
    refine hsum.congr fun y => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (h.nonneg x y)]
  have h1 : |kernelApply κ f x| ≤ ∑' y, κ x y * |f y| := by
    have h := norm_tsum_le_tsum_norm hnorm
    rw [habsrow, Real.norm_eq_abs] at h
    simpa only [kernelApply] using h
  have h2 : (∑' y, κ x y * |f y|) ^ 2 ≤ A * (A * ∑' y, f y ^ 2) := by
    have hcs := sq_tsum_mul_le (a := κ x) (b := fun y => |f y|) (fun y => h.nonneg x y)
      (fun y => abs_nonneg _) (h.row_summable x) hrow
    have hb : (∑' y, κ x y * |f y| ^ 2) ≤ A * ∑' y, f y ^ 2 := by
      refine le_trans (schur_tsum_row_mul_sq_le h habs x) ?_
      refine le_of_eq ?_
      congr 1
      exact tsum_congr fun y => by rw [sq_abs]
    have hrowle : (∑' y, κ x y) ≤ A := h.row_le x
    have hnn : 0 ≤ ∑' y, κ x y * |f y| ^ 2 :=
      tsum_nonneg fun y => mul_nonneg (h.nonneg x y) (sq_nonneg _)
    calc (∑' y, κ x y * |f y|) ^ 2 ≤ (∑' y, κ x y) * (∑' y, κ x y * |f y| ^ 2) := hcs
      _ ≤ A * (A * ∑' y, f y ^ 2) :=
          mul_le_mul hrowle hb hnn h.A_nonneg
  have hAB : 0 ≤ A * ∑' y, f y ^ 2 :=
    mul_nonneg h.A_nonneg (tsum_nonneg fun y => sq_nonneg _)
  have hnnrow : 0 ≤ ∑' y, κ x y * |f y| :=
    tsum_nonneg fun y => mul_nonneg (h.nonneg x y) (abs_nonneg _)
  calc |kernelApply κ f x| ≤ ∑' y, κ x y * |f y| := h1
    _ ≤ Real.sqrt (A * (A * ∑' y, f y ^ 2)) := by
        rw [← Real.sqrt_sq hnnrow]
        exact Real.sqrt_le_sqrt h2
    _ = A * Real.sqrt (∑' y, f y ^ 2) := by
        rw [show A * (A * ∑' y, f y ^ 2) = A ^ 2 * ∑' y, f y ^ 2 by ring,
          Real.sqrt_mul (sq_nonneg A), Real.sqrt_sq h.A_nonneg]


/-- **Triangle step**: the absolute value of the kernel series is at most the series of the
absolute values. -/
theorem abs_kernelApply_le_kernelApply_abs (h : SchurKernel κ A) {f : V → ℝ}
    (hfs : Summable fun y => f y ^ 2) (x : V) :
    |kernelApply κ f x| ≤ kernelApply κ (fun y => |f y|) x := by
  have habs : Summable fun y => |f y| ^ 2 := by simpa [sq_abs] using hfs
  have hrow : Summable fun y => κ x y * |f y| ^ 2 := schur_summable_row_mul_sq h habs x
  have hsum : Summable fun y => κ x y * |f y| := by
    have hdom : Summable fun y => (1 / 2) * (κ x y + κ x y * |f y| ^ 2) :=
      ((h.row_summable x).add hrow).mul_left (1 / 2)
    exact Summable.of_nonneg_of_le (fun y => mul_nonneg (h.nonneg x y) (abs_nonneg _))
      (fun y => by nlinarith [h.nonneg x y, sq_nonneg (|f y| - 1)]) hdom
  have habsrow : (∑' y, ‖κ x y * f y‖) = ∑' y, κ x y * |f y| := by
    refine tsum_congr fun y => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (h.nonneg x y)]
  have hnorm : Summable fun y => ‖κ x y * f y‖ := by
    refine hsum.congr fun y => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (h.nonneg x y)]
  have h := norm_tsum_le_tsum_norm hnorm
  rw [habsrow, Real.norm_eq_abs] at h
  simpa only [kernelApply] using h

/-! ### The `ℓ²` bound -/

/-- **The Schur bound, nonnegative case**: for `f ≥ 0` in `ℓ²`, the kernel series is in `ℓ²`
with squared norm at most `A²` times the squared norm of `f`. -/
theorem schur_tsum_sq_kernelApply_le_of_nonneg (h : SchurKernel κ A) {f : V → ℝ}
    (hf : ∀ y, 0 ≤ f y) (hfs : Summable fun y => f y ^ 2) :
    Summable (fun x => kernelApply κ f x ^ 2) ∧
      ∑' x, kernelApply κ f x ^ 2 ≤ A ^ 2 * ∑' y, f y ^ 2 := by
  have hU := schur_summable_uncurry h hfs
  have hiter : Summable fun x => ∑' y, κ x y * f y ^ 2 :=
    ((summable_prod_of_nonneg (f := Function.uncurry fun x y => κ x y * f y ^ 2)
      (fun p => mul_nonneg (h.nonneg p.1 p.2) (sq_nonneg _))).mp hU).2
  have hpt : ∀ x, kernelApply κ f x ^ 2 ≤ A * ∑' y, κ x y * f y ^ 2 :=
    fun x => schur_sq_kernelApply_le h hf hfs x
  have hAsum : Summable fun x => A * ∑' y, κ x y * f y ^ 2 := hiter.mul_left A
  have hsq : Summable fun x => kernelApply κ f x ^ 2 :=
    Summable.of_nonneg_of_le (fun x => sq_nonneg _) hpt hAsum
  refine ⟨hsq, ?_⟩
  have step1 : ∑' x, kernelApply κ f x ^ 2 ≤ ∑' x, A * ∑' y, κ x y * f y ^ 2 :=
    Summable.tsum_le_tsum hpt hsq hAsum
  have step2 : ∑' x, A * ∑' y, κ x y * f y ^ 2
      = A * ∑' y, ∑' x, κ x y * f y ^ 2 := by
    rw [tsum_mul_left, Summable.tsum_comm hU]
  have step3 : ∀ y, ∑' x, κ x y * f y ^ 2 = (∑' x, κ x y) * f y ^ 2 := by
    intro y
    rw [tsum_mul_right]
  have hcolrow : ∀ y, (∑' x, κ x y) ≤ A := by
    intro y
    have hs : (∑' x, κ x y) = ∑' x, κ y x := tsum_congr fun x => h.symm x y
    rw [hs]
    exact h.row_le y
  have hcol : ∀ y, (∑' x, κ x y) * f y ^ 2 ≤ A * f y ^ 2 :=
    fun y => mul_le_mul_of_nonneg_right (hcolrow y) (sq_nonneg _)
  have hsA : Summable fun y => A * f y ^ 2 := hfs.mul_left A
  have hsB : Summable fun y => (∑' x, κ x y) * f y ^ 2 :=
    Summable.of_nonneg_of_le
      (fun y => mul_nonneg (tsum_nonneg fun x => h.nonneg x y) (sq_nonneg _)) hcol hsA
  have step4 : ∑' y, (∑' x, κ x y) * f y ^ 2 ≤ A * ∑' y, f y ^ 2 := by
    refine le_trans (Summable.tsum_le_tsum hcol hsB hsA) ?_
    rw [tsum_mul_left]
  calc ∑' x, kernelApply κ f x ^ 2
      ≤ ∑' x, A * ∑' y, κ x y * f y ^ 2 := step1
    _ = A * ∑' y, ∑' x, κ x y * f y ^ 2 := step2
    _ = A * ∑' y, (∑' x, κ x y) * f y ^ 2 := by rw [tsum_congr step3]
    _ ≤ A * (A * ∑' y, f y ^ 2) := mul_le_mul_of_nonneg_left step4 h.A_nonneg
    _ = A ^ 2 * ∑' y, f y ^ 2 := by ring

/-- **The Schur bound on `ℓ²`**: the kernel operator maps `ℓ²` into `ℓ²` with norm at most the
row constant `A`.  This is the boundedness statement; the hypotheses are `SchurKernel`, in
particular a uniform row-sum bound, not merely finiteness of the diagonal. -/
theorem schur_tsum_sq_kernelApply_le (h : SchurKernel κ A) (f : V → ℝ)
    (hfs : Summable fun y => f y ^ 2) :
    Summable (fun x => kernelApply κ f x ^ 2) ∧
      ∑' x, kernelApply κ f x ^ 2 ≤ A ^ 2 * ∑' y, f y ^ 2 := by
  have habs : Summable fun y => |f y| ^ 2 := by simpa [sq_abs] using hfs
  obtain ⟨hsq, hle⟩ := schur_tsum_sq_kernelApply_le_of_nonneg h (f := fun y => |f y|)
    (fun y => abs_nonneg _) habs
  have hpt : ∀ x, kernelApply κ f x ^ 2 ≤ kernelApply κ (fun y => |f y|) x ^ 2 := by
    intro x
    have h1 := abs_kernelApply_le_kernelApply_abs h hfs x
    have h2 : |kernelApply κ f x| ^ 2 ≤ kernelApply κ (fun y => |f y|) x ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) h1 2
    simpa [sq_abs] using h2
  have hsq' : Summable fun x => kernelApply κ f x ^ 2 :=
    Summable.of_nonneg_of_le (fun x => sq_nonneg _) hpt hsq
  refine ⟨hsq', ?_⟩
  refine le_trans (Summable.tsum_le_tsum hpt hsq' hsq) ?_
  refine le_trans hle (le_of_eq ?_)
  congr 1
  exact tsum_congr fun y => sq_abs (f y)


/-! ### Composing the operator with itself: the triple kernel sum -/

/-- Columns are square-summable: each entry is at most `A`, and columns have the row bound by
symmetry. -/
theorem schur_summable_col_sq (h : SchurKernel κ A) (y : V) :
    Summable fun z => κ z y ^ 2 := by
  have hA : 0 ≤ A := h.A_nonneg
  have hcolsum : Summable fun z => κ z y := by
    have hs : (fun z => κ z y) = fun z => κ y z := funext fun z => h.symm z y
    rw [hs]
    exact h.row_summable y
  have hcolle : (∑' z, κ z y) ≤ A := by
    have hs : (∑' z, κ z y) = ∑' z, κ y z := tsum_congr fun z => h.symm z y
    rw [hs]
    exact h.row_le y
  have hpt : ∀ z, κ z y ^ 2 ≤ A * κ z y := by
    intro z
    have h1 : κ z y ≤ A := le_trans (Summable.le_tsum hcolsum z (fun i _ => h.nonneg i y)) hcolle
    nlinarith [h.nonneg z y]
  exact Summable.of_nonneg_of_le (fun z => sq_nonneg _) hpt (hcolsum.mul_left A)

/-- Rows against `|g|` are summable. -/
theorem schur_summable_row_mul_abs (h : SchurKernel κ A) {g : V → ℝ}
    (hgs : Summable fun z => g z ^ 2) (y : V) : Summable fun z => κ y z * |g z| := by
  have habs : Summable fun z => |g z| ^ 2 := by simpa [sq_abs] using hgs
  have hrow : Summable fun z => κ y z * |g z| ^ 2 := schur_summable_row_mul_sq h habs y
  have hdom : Summable fun z => (1 / 2) * (κ y z + κ y z * |g z| ^ 2) :=
    ((h.row_summable y).add hrow).mul_left (1 / 2)
  exact Summable.of_nonneg_of_le (fun z => mul_nonneg (h.nonneg y z) (abs_nonneg _))
    (fun z => by nlinarith [h.nonneg y z, sq_nonneg (|g z| - 1)]) hdom

/-- The row series of a nonnegative function is bounded by `A` times its `ℓ²` norm. -/
theorem row_tsum_mul_le (h : SchurKernel κ A) {g : V → ℝ} (_hg : ∀ z, 0 ≤ g z)
    (hgs : Summable fun z => g z ^ 2) (y : V) :
    ∑' z, κ y z * g z ≤ A * Real.sqrt (∑' z, g z ^ 2) :=
  le_trans (le_abs_self _) (abs_kernelApply_le h hgs y)

/-- **Summability of the composed double family.** -/
theorem schur_summable_uncurry_comp (h : SchurKernel κ A) {g : V → ℝ}
    (hgs : Summable fun z => g z ^ 2) (x : V) :
    Summable (Function.uncurry fun y z => κ x y * (κ y z * g z)) := by
  classical
  have habs : Summable fun z => |g z| ^ 2 := by simpa [sq_abs] using hgs
  have hA : 0 ≤ A := h.A_nonneg
  have hrowb : ∀ y, ∑' z, κ y z * |g z| ≤ A * Real.sqrt (∑' z, |g z| ^ 2) :=
    fun y => row_tsum_mul_le h (fun z => abs_nonneg _) habs y
  have hG : Summable (fun p : V × V => κ x p.1 * (κ p.1 p.2 * |g p.2|)) := by
    refine summable_of_sum_le (c := A * (A * Real.sqrt (∑' z, |g z| ^ 2)))
      (fun p => mul_nonneg (h.nonneg x p.1) (mul_nonneg (h.nonneg p.1 p.2) (abs_nonneg _)))
      fun u => ?_
    have hsub : u ⊆ u.image Prod.fst ×ˢ u.image Prod.snd := by
      intro p hp
      rw [Finset.mem_product]
      exact ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩
    have h1 : ∑ p ∈ u, κ x p.1 * (κ p.1 p.2 * |g p.2|)
        ≤ ∑ p ∈ u.image Prod.fst ×ˢ u.image Prod.snd,
            κ x p.1 * (κ p.1 p.2 * |g p.2|) :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (f := fun p : V × V => κ x p.1 * (κ p.1 p.2 * |g p.2|)) hsub
        fun p _ _ => mul_nonneg (h.nonneg x p.1)
          (mul_nonneg (h.nonneg p.1 p.2) (abs_nonneg _))
    have h2 : ∑ p ∈ u.image Prod.fst ×ˢ u.image Prod.snd,
          κ x p.1 * (κ p.1 p.2 * |g p.2|)
        = ∑ y ∈ u.image Prod.fst,
            κ x y * (∑ z ∈ u.image Prod.snd, κ y z * |g z|) := by
      rw [Finset.sum_product]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.mul_sum]
    have h3 : ∑ y ∈ u.image Prod.fst,
          κ x y * (∑ z ∈ u.image Prod.snd, κ y z * |g z|)
        ≤ ∑ y ∈ u.image Prod.fst,
            κ x y * (A * Real.sqrt (∑' z, |g z| ^ 2)) := by
      refine Finset.sum_le_sum fun y _ => ?_
      refine mul_le_mul_of_nonneg_left ?_ (h.nonneg x y)
      calc ∑ z ∈ u.image Prod.snd, κ y z * |g z| ≤ ∑' z, κ y z * |g z| :=
            (schur_summable_row_mul_abs h hgs y).sum_le_tsum _
              (fun i _ => mul_nonneg (h.nonneg y i) (abs_nonneg _))
        _ ≤ A * Real.sqrt (∑' z, |g z| ^ 2) := hrowb y
    have h4 : ∑ y ∈ u.image Prod.fst, κ x y * (A * Real.sqrt (∑' z, |g z| ^ 2))
        ≤ A * (A * Real.sqrt (∑' z, |g z| ^ 2)) := by
      have hs : ∑ y ∈ u.image Prod.fst, κ x y ≤ A := h.row_finset_le x _
      have hc : 0 ≤ A * Real.sqrt (∑' z, |g z| ^ 2) :=
        mul_nonneg hA (Real.sqrt_nonneg _)
      calc ∑ y ∈ u.image Prod.fst, κ x y * (A * Real.sqrt (∑' z, |g z| ^ 2))
          = (∑ y ∈ u.image Prod.fst, κ x y) * (A * Real.sqrt (∑' z, |g z| ^ 2)) :=
            (Finset.sum_mul _ _ _).symm
        _ ≤ A * (A * Real.sqrt (∑' z, |g z| ^ 2)) :=
            mul_le_mul_of_nonneg_right hs hc
    calc ∑ p ∈ u, κ x p.1 * (κ p.1 p.2 * |g p.2|)
        ≤ ∑ p ∈ u.image Prod.fst ×ˢ u.image Prod.snd,
            κ x p.1 * (κ p.1 p.2 * |g p.2|) := h1
      _ = ∑ y ∈ u.image Prod.fst,
            κ x y * (∑ z ∈ u.image Prod.snd, κ y z * |g z|) := h2
      _ ≤ ∑ y ∈ u.image Prod.fst,
            κ x y * (A * Real.sqrt (∑' z, |g z| ^ 2)) := h3
      _ ≤ A * (A * Real.sqrt (∑' z, |g z| ^ 2)) := h4
  refine Summable.of_norm_bounded hG fun p => ?_
  change |κ x p.1 * (κ p.1 p.2 * g p.2)| ≤ κ x p.1 * (κ p.1 p.2 * |g p.2|)
  rw [abs_mul, abs_mul, abs_of_nonneg (h.nonneg x p.1), abs_of_nonneg (h.nonneg p.1 p.2)]

/-- **`T_κ` composed with itself acts by the two-fold kernel sum.** -/
theorem kernelApply_comp_eq (h : SchurKernel κ A) {g : V → ℝ}
    (hgs : Summable fun z => g z ^ 2) (x : V) :
    kernelApply κ (kernelApply κ g) x = ∑' z, kernelComp κ κ x z * g z := by
  have hsum := schur_summable_uncurry_comp h hgs x
  have step1 : kernelApply κ (kernelApply κ g) x
      = ∑' y, ∑' z, κ x y * (κ y z * g z) := by
    rw [kernelApply]
    refine tsum_congr fun y => ?_
    rw [kernelApply, tsum_mul_left]
  rw [step1, ← Summable.tsum_comm (f := fun y z => κ x y * (κ y z * g z)) hsum]
  refine tsum_congr fun z => ?_
  rw [kernelComp, ← tsum_mul_right]
  exact tsum_congr fun y => by ring

/-! ### Associativity of kernel composition and the cube -/

/-- **Associativity of kernel composition** for Schur kernels. -/
theorem kernelComp_assoc (h : SchurKernel κ A) (x y : V) :
    kernelComp (kernelComp κ κ) κ x y = kernelComp κ (kernelComp κ κ) x y := by
  have hB : Summable (Function.uncurry fun u v => κ x u * (κ u v * κ v y)) := by
    have := schur_summable_uncurry_comp (A := A) h (g := fun v => κ v y)
      (hgs := schur_summable_col_sq h y) x
    simpa only [mul_comm] using this
  calc kernelComp (kernelComp κ κ) κ x y
      = ∑' v, ∑' u, κ x u * (κ u v * κ v y) := by
        rw [kernelComp]
        refine tsum_congr fun v => ?_
        rw [kernelComp, ← tsum_mul_right]
        exact tsum_congr fun u => by ring
    _ = ∑' u, ∑' v, κ x u * (κ u v * κ v y) := Summable.tsum_comm hB
    _ = kernelComp κ (kernelComp κ κ) x y := by
        rw [kernelComp]
        refine tsum_congr fun u => ?_
        rw [kernelComp, tsum_mul_left]


/-! ### Translation invariance and positivity -/

/-- **Translation invariance.**  A kernel invariant under the translations of an additive group
gives an operator commuting with the translation operators on functions. -/
theorem kernelApply_shift [AddGroup V]
    (hκ : ∀ (a x y : V), κ (x + a) (y + a) = κ x y) (f : V → ℝ) (a x : V) :
    kernelApply κ (fun y => f (y + a)) x = kernelApply κ f (x + a) := by
  rw [kernelApply, kernelApply]
  have h1 : (∑' y, κ x y * f (y + a)) = ∑' z, κ x (z - a) * f z := by
    have h := Equiv.tsum_eq (Equiv.addRight a) (fun z => κ x (z - a) * f z)
    simpa [sub_add_cancel] using h
  rw [h1]
  refine tsum_congr fun z => ?_
  rw [← hκ a x (z - a), sub_add_cancel]

/-- **Positivity of the quadratic form.**  If the kernel is positive semidefinite on finite
vertex sets, the operator's quadratic form is nonnegative on finitely supported functions. -/
theorem kernelApply_quadratic_nonneg (hpsd : IsPSDKernel κ)
    {f : V → ℝ} (hf : FinitelySupported f) :
    0 ≤ ∑' x, f x * kernelApply κ f x := by
  classical
  have hfin : (Function.support f).Finite := hf
  set s := hfin.toFinset with hsdef
  have hmem : ∀ x, x ∈ s ↔ f x ≠ 0 := by
    intro x
    rw [hsdef, Set.Finite.mem_toFinset]
    exact Iff.rfl
  have hzero : ∀ x ∉ s, f x * kernelApply κ f x = 0 := by
    intro x hx
    have hfx : f x = 0 := by
      by_contra hc
      exact hx ((hmem x).mpr hc)
    simp [hfx]
  have hinner : ∀ x, kernelApply κ f x = ∑ y ∈ s, κ x y * f y := by
    intro x
    rw [kernelApply, tsum_eq_sum (s := s) (fun y hy => by
      have hfy : f y = 0 := by
        by_contra hc
        exact hy ((hmem y).mpr hc)
      simp [hfy])]
  rw [tsum_eq_sum (s := s) hzero]
  have hstep : ∀ x ∈ s, f x * kernelApply κ f x
      = ∑ y ∈ s, κ x y * f x * f y := by
    intro x _
    rw [hinner x, Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [Finset.sum_congr rfl hstep]
  exact hpsd s f


/-- **Summability of a mixed composed double family**: only the row of `κ₁` at `x` is needed,
while `κ₂` must be a Schur kernel (to bound the rows against `|g|`). -/
theorem schur_summable_uncurry_comp_row {κ₁ κ₂ : V → V → ℝ} {A₁ A₂ : ℝ} (x : V)
    (hn₁ : ∀ y, 0 ≤ κ₁ x y) (hrow₁ : Summable (κ₁ x)) (hle₁ : (∑' y, κ₁ x y) ≤ A₁)
    (h₂ : SchurKernel κ₂ A₂) {g : V → ℝ} (hgs : Summable fun z => g z ^ 2) :
    Summable (Function.uncurry fun y z => κ₁ x y * (κ₂ y z * g z)) := by
  classical
  have habs : Summable fun z => |g z| ^ 2 := by simpa [sq_abs] using hgs
  have hA : 0 ≤ A₁ := le_trans (tsum_nonneg hn₁) hle₁
  have hrowb : ∀ y, ∑' z, κ₂ y z * |g z| ≤ A₂ * Real.sqrt (∑' z, |g z| ^ 2) :=
    fun y => row_tsum_mul_le h₂ (fun z => abs_nonneg _) habs y
  have hfins : ∀ u : Finset V, ∑ y ∈ u, κ₁ x y ≤ A₁ := by
    intro u
    have h1 : ∑ y ∈ u, κ₁ x y ≤ ∑' y, κ₁ x y :=
      hrow₁.sum_le_tsum u (fun i _ => hn₁ i)
    linarith
  have hG : Summable (fun p : V × V => κ₁ x p.1 * (κ₂ p.1 p.2 * |g p.2|)) := by
    refine summable_of_sum_le (c := A₁ * (A₂ * Real.sqrt (∑' z, |g z| ^ 2)))
      (fun p => mul_nonneg (hn₁ p.1) (mul_nonneg (h₂.nonneg p.1 p.2) (abs_nonneg _)))
      fun u => ?_
    have hsub : u ⊆ u.image Prod.fst ×ˢ u.image Prod.snd := by
      intro p hp
      rw [Finset.mem_product]
      exact ⟨Finset.mem_image_of_mem _ hp, Finset.mem_image_of_mem _ hp⟩
    have h1 : ∑ p ∈ u, κ₁ x p.1 * (κ₂ p.1 p.2 * |g p.2|)
        ≤ ∑ p ∈ u.image Prod.fst ×ˢ u.image Prod.snd,
            κ₁ x p.1 * (κ₂ p.1 p.2 * |g p.2|) :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (f := fun p : V × V => κ₁ x p.1 * (κ₂ p.1 p.2 * |g p.2|)) hsub
        fun p _ _ => mul_nonneg (hn₁ p.1)
          (mul_nonneg (h₂.nonneg p.1 p.2) (abs_nonneg _))
    have h2 : ∑ p ∈ u.image Prod.fst ×ˢ u.image Prod.snd,
          κ₁ x p.1 * (κ₂ p.1 p.2 * |g p.2|)
        = ∑ y ∈ u.image Prod.fst,
            κ₁ x y * (∑ z ∈ u.image Prod.snd, κ₂ y z * |g z|) := by
      rw [Finset.sum_product]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.mul_sum]
    have h3 : ∑ y ∈ u.image Prod.fst,
          κ₁ x y * (∑ z ∈ u.image Prod.snd, κ₂ y z * |g z|)
        ≤ ∑ y ∈ u.image Prod.fst, κ₁ x y * (A₂ * Real.sqrt (∑' z, |g z| ^ 2)) := by
      refine Finset.sum_le_sum fun y _ => ?_
      refine mul_le_mul_of_nonneg_left ?_ (hn₁ y)
      calc ∑ z ∈ u.image Prod.snd, κ₂ y z * |g z| ≤ ∑' z, κ₂ y z * |g z| :=
            (schur_summable_row_mul_abs h₂ hgs y).sum_le_tsum _
              (fun i _ => mul_nonneg (h₂.nonneg y i) (abs_nonneg _))
        _ ≤ A₂ * Real.sqrt (∑' z, |g z| ^ 2) := hrowb y
    have h4 : ∑ y ∈ u.image Prod.fst, κ₁ x y * (A₂ * Real.sqrt (∑' z, |g z| ^ 2))
        ≤ A₁ * (A₂ * Real.sqrt (∑' z, |g z| ^ 2)) := by
      have hs : ∑ y ∈ u.image Prod.fst, κ₁ x y ≤ A₁ := hfins _
      have hc : 0 ≤ A₂ * Real.sqrt (∑' z, |g z| ^ 2) :=
        mul_nonneg h₂.A_nonneg (Real.sqrt_nonneg _)
      calc ∑ y ∈ u.image Prod.fst, κ₁ x y * (A₂ * Real.sqrt (∑' z, |g z| ^ 2))
          = (∑ y ∈ u.image Prod.fst, κ₁ x y) * (A₂ * Real.sqrt (∑' z, |g z| ^ 2)) :=
            (Finset.sum_mul _ _ _).symm
        _ ≤ A₁ * (A₂ * Real.sqrt (∑' z, |g z| ^ 2)) :=
            mul_le_mul_of_nonneg_right hs hc
    calc ∑ p ∈ u, κ₁ x p.1 * (κ₂ p.1 p.2 * |g p.2|)
        ≤ ∑ p ∈ u.image Prod.fst ×ˢ u.image Prod.snd,
            κ₁ x p.1 * (κ₂ p.1 p.2 * |g p.2|) := h1
      _ = ∑ y ∈ u.image Prod.fst,
            κ₁ x y * (∑ z ∈ u.image Prod.snd, κ₂ y z * |g z|) := h2
      _ ≤ ∑ y ∈ u.image Prod.fst, κ₁ x y * (A₂ * Real.sqrt (∑' z, |g z| ^ 2)) := h3
      _ ≤ A₁ * (A₂ * Real.sqrt (∑' z, |g z| ^ 2)) := h4
  refine Summable.of_norm_bounded hG fun p => ?_
  change |κ₁ x p.1 * (κ₂ p.1 p.2 * g p.2)| ≤ κ₁ x p.1 * (κ₂ p.1 p.2 * |g p.2|)
  rw [abs_mul, abs_mul, abs_of_nonneg (hn₁ p.1), abs_of_nonneg (h₂.nonneg p.1 p.2)]

/-- **The third power of the operator acts by the cube kernel.**  Given the Schur bound for the
two-fold kernel (used only through its row at `x`), the third iterate of `kernelApply κ` has
kernel `kernelCube κ`, i.e. the triple sum `∑_u ∑_v κ x u κ u v κ v y` that the model's
`openTriangle` is. -/
theorem kernelApply_three_eq (h : SchurKernel κ A)
    (h2 : SchurKernel (kernelComp κ κ) (A * A))
    {g : V → ℝ} (hgs : Summable fun z => g z ^ 2) (x : V) :
    kernelApply κ (kernelApply κ (kernelApply κ g)) x = ∑' z, kernelCube κ x z * g z := by
  have hTg : Summable fun z => kernelApply κ g z ^ 2 :=
    (schur_tsum_sq_kernelApply_le h g hgs).1
  rw [kernelApply_comp_eq h hTg x]
  have hnn : ∀ y, 0 ≤ kernelComp κ κ x y :=
    fun y => tsum_nonneg fun z => mul_nonneg (h.nonneg x z) (h.nonneg z y)
  have hmix := schur_summable_uncurry_comp_row (κ₁ := kernelComp κ κ) (κ₂ := κ)
    (A₁ := A * A) (A₂ := A) x hnn (h2.row_summable x) (h2.row_le x) h hgs
  have hstep : ∀ z, kernelComp κ κ x z * kernelApply κ g z
      = ∑' w, kernelComp κ κ x z * (κ z w * g w) := by
    intro z
    rw [kernelApply, tsum_mul_left]
  rw [tsum_congr hstep, ← Summable.tsum_comm
    (f := fun z w => kernelComp κ κ x z * (κ z w * g w)) hmix]
  refine tsum_congr fun w => ?_
  rw [kernelCube, ← kernelComp_assoc h x w, kernelComp, ← tsum_mul_right]
  exact tsum_congr fun z => by ring

end PercLib.CriticalLRP.KernelOperator
