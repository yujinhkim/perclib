/- Integrated from independently rebuilt Ultramath work, base revision 4140ac56119d2cd80995f91886669efe004839d5.
Scratch source: ../../.ultramath/smwqozn0q/m1/Finite.lean ; imports migrated only.
-/

module

/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
The truncated matrix power of the connection kernel is a genuine matrix power, and powers of a
positive semidefinite matrix satisfy the Cauchy--Schwarz entry bound.
-/
public import PercLib.CriticalLRP.Analysis.KernelPower.Defs

/-!
# Finite submatrices: `KpowF` is a matrix power, and PSD powers are diagonally maximal

* `KpowF_eq_matpow`: for `x, y ∈ S`, `KpowF K S n x y` is the `(x,y)` entry of the `n`-th
  power of the principal submatrix of `K` on `S`.
* `matrix_pow_entry_sq_le`: for a positive semidefinite matrix `A`, `(A ^ n) i j ^ 2 ≤
  (A ^ n) i i * (A ^ n) j j`.  This is the Cauchy--Schwarz bound for the positive
  semidefinite matrix `A ^ n`; it holds whether or not `A ^ n` is diagonally constant.
* `KpowF_sq_le`: the same bound for the truncated kernel power.
-/

@[expose] public section

noncomputable section

open scoped ENNReal Matrix

attribute [local instance] Classical.propDecidable

namespace PercLib.CriticalLRP.KernelPower

variable {V : Type*}

/-! ### `KpowF` is a matrix power -/

theorem KpowF_eq_matpow (K : V → V → ℝ) (S : Finset V) (n : ℕ) (x y : V) (hx : x ∈ S)
    (hy : y ∈ S) :
    KpowF K S n x y = ((Matrix.of fun i j : S => K (i : V) (j : V)) ^ n) ⟨x, hx⟩ ⟨y, hy⟩ := by
  classical
  induction n generalizing x y with
  | zero =>
    rw [KpowF_zero, pow_zero, Matrix.one_apply]
    by_cases h : x = y
    · subst h; simp [delta_self]
    · rw [delta_of_ne h]
      simp [h]
  | succ n ih =>
    rw [KpowF_succ, pow_succ, Matrix.mul_apply, ← Finset.sum_coe_sort S]
    refine Finset.sum_congr rfl fun u => ?_
    rw [ih x (u : V) hx u.2, Matrix.of_apply]
    simp

/-! ### Powers of positive semidefinite matrices -/

/-- The entries of a Hermitian matrix are symmetric. -/
theorem isHermitian_apply {ι : Type*} {A : Matrix ι ι ℝ} (h : A.IsHermitian) (i j : ι) :
    A j i = A i j := by
  have h' : Aᴴ = A := h
  have := congrFun (congrFun h' i) j
  simpa [Matrix.conjTranspose_apply] using this

/-- **Cauchy--Schwarz for the entries of a positive semidefinite matrix**:
`A i j ^ 2 ≤ A i i * A j j`. -/
theorem posSemidef_entry_sq_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (i j : ι) : A i j ^ 2 ≤ A i i * A j j := by
  have hB : (A.submatrix ![i, j] ![i, j]).PosSemidef := hA.submatrix _
  have hdet : 0 ≤ (A.submatrix ![i, j] ![i, j]).det := hB.det_nonneg
  have hsym : A j i = A i j := isHermitian_apply hA.isHermitian i j
  rw [Matrix.det_fin_two] at hdet
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hdet
  rw [hsym] at hdet
  nlinarith

/-- **Cauchy--Schwarz for the entries of a power of a positive semidefinite matrix.** -/
theorem matrix_pow_entry_sq_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (n : ℕ) (i j : ι) :
    (A ^ n) i j ^ 2 ≤ (A ^ n) i i * (A ^ n) j j :=
  posSemidef_entry_sq_le (hA.pow n) i j

/-! ### The truncated kernel power -/

/-- **Cauchy--Schwarz for the truncated kernel power.**  If every finite principal submatrix of
the kernel `K` is positive semidefinite, then for `x, y ∈ S` the truncated `n`-fold power
satisfies `KpowF K S n x y ^ 2 ≤ KpowF K S n x x * KpowF K S n y y`. -/
theorem KpowF_sq_le (K : V → V → ℝ)
    (hK : ∀ S : Finset V, (Matrix.of fun i j : S => K (i : V) (j : V)).PosSemidef)
    (S : Finset V) (n : ℕ) (x y : V) (hx : x ∈ S) (hy : y ∈ S) :
    KpowF K S n x y ^ 2 ≤ KpowF K S n x x * KpowF K S n y y := by
  classical
  rw [KpowF_eq_matpow K S n x y hx hy, KpowF_eq_matpow K S n x x hx hx,
    KpowF_eq_matpow K S n y y hy hy]
  exact matrix_pow_entry_sq_le (hK S) n ⟨x, hx⟩ ⟨y, hy⟩

end PercLib.CriticalLRP.KernelPower
