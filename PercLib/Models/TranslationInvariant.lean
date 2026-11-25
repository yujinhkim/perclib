/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for P-7 (issue 41), written on 2026-11-14, from pinned mathlib's `Sym2.lift`,
`Equiv.tsum_eq` and ENNReal sums, and the P-5 and P-6 theorems. No upstream code is copied.
-/
module

public import PercLib.Percolation.Bond.Intensity

/-! # Translation-invariant kernels on additive groups, and `ℤ^d`

On an additive group `G`, a pair intensity is translation invariant when
`J s(x,y) = k (y - x)` for a displacement kernel `k`. Such a `J` exists exactly when `k`
is even, because pairs are unordered (`exists_sym2_kernel`). The off-diagonal row of `J`
at every vertex is `∑'_{z ≠ 0} k z` (`rowSum_eq_of_translationInvariant`), so P-5 and
P-6 apply with `M` any bound on `∑' z, k z`.

`ℤ^d` is `Fin d → ℤ`. The compiled witness at the end uses the nearest-neighbour kernel
along one coordinate axis; it is nonzero, its row sum is two, and at `β = 1/4` the
susceptibility is at most two at every vertex and both thresholds are at least `1/2`.

The kernel `k` is a hypothesis-bound function, so this file adds no definition.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal
open Classical
open PercLib.Percolation.Bond

namespace PercLib.Models

variable {G : Type*} [AddGroup G]

/-- Every even displacement kernel is the kernel of a pair intensity on unordered
pairs. -/
theorem exists_sym2_kernel (k : G → ℝ≥0) (hk : ∀ z, k (-z) = k z) :
    ∃ J : Sym2 G → ℝ≥0, ∀ x y, J s(x,y) = k (y - x) :=
  ⟨Sym2.lift ⟨fun x y => k (y - x), fun x y => by
      show k (y - x) = k (x - y)
      rw [← hk, neg_sub]⟩,
    fun x y => Sym2.lift_mk _ x y⟩

/-- A translation-invariant pair intensity has the same off-diagonal row at every vertex:
the sum of the kernel away from zero. -/
theorem rowSum_eq_of_translationInvariant (J : Sym2 G → ℝ≥0) (k : G → ℝ≥0)
    (hJ : ∀ x y, J s(x,y) = k (y - x)) (v : G) :
    (∑' w, if w = v then 0 else (J s(v,w) : ℝ≥0∞)) =
      ∑' z, if z = 0 then 0 else (k z : ℝ≥0∞) := by
  rw [← (Equiv.addRight v).tsum_eq]
  refine tsum_congr fun z => ?_
  simp [hJ]

/-- The off-diagonal row of a translation-invariant pair intensity is at most the total
mass of its kernel. -/
theorem rowSum_le_tsum_of_translationInvariant (J : Sym2 G → ℝ≥0) (k : G → ℝ≥0)
    (hJ : ∀ x y, J s(x,y) = k (y - x)) (v : G) :
    (∑' w, if w = v then 0 else (J s(v,w) : ℝ≥0∞)) ≤ ∑' z, (k z : ℝ≥0∞) := by
  rw [rowSum_eq_of_translationInvariant J k hJ v]
  exact ENNReal.tsum_le_tsum fun z => by split_ifs <;> simp

/-- **P-5 for translation-invariant profiles.** If `q s(x,y) = p (y - x)` and the
off-diagonal mass of `p` is at most `m < 1`, then `chi q x ≤ (1 - m)⁻¹`. -/
theorem chi_le_of_translationInvariant [Countable G] (q : Sym2 G → unitInterval)
    (p : G → unitInterval) (hq : ∀ x y, q s(x,y) = p (y - x)) (m : ℝ≥0∞)
    (hp : (∑' z, if z = 0 then 0 else (unitInterval.toNNReal (p z) : ℝ≥0∞)) ≤ m)
    (hm : m < 1) (x : G) : chi q x ≤ (1 - m)⁻¹ :=
  chi_le_inv_one_sub_of_rowSum q m (fun v =>
    (rowSum_eq_of_translationInvariant (fun e => unitInterval.toNNReal (q e))
      (fun z => unitInterval.toNNReal (p z))
      (fun x y => congrArg unitInterval.toNNReal (hq x y)) v).le.trans hp) hm x

/-- **P-6 for translation-invariant intensities: susceptibility.** -/
theorem chi_intensity_le_of_translationInvariant [Countable G] (J : Sym2 G → ℝ≥0)
    (k : G → ℝ≥0) (hJ : ∀ x y, J s(x,y) = k (y - x)) (M : ℝ≥0)
    (hk : ∑' z, (k z : ℝ≥0∞) ≤ M) (β : ℝ≥0) (hβ : (β : ℝ≥0∞) * M < 1) (x : G) :
    chi (intensityProfile J β) x ≤ (1 - (β : ℝ≥0∞) * M)⁻¹ :=
  chi_intensity_le J M (fun v => (rowSum_le_tsum_of_translationInvariant J k hJ v).trans hk)
    β hβ x

/-- **P-6 for translation-invariant intensities: global threshold.** -/
theorem inv_le_globalCriticalIntensity_of_translationInvariant [Countable G]
    (J : Sym2 G → ℝ≥0) (k : G → ℝ≥0) (hJ : ∀ x y, J s(x,y) = k (y - x)) (M : ℝ≥0)
    (hk : ∑' z, (k z : ℝ≥0∞) ≤ M) :
    (M : ℝ≥0∞)⁻¹ ≤ globalCriticalIntensity J :=
  inv_le_globalCriticalIntensity J M fun v =>
    (rowSum_le_tsum_of_translationInvariant J k hJ v).trans hk

/-- **P-6 for translation-invariant intensities: root threshold.** -/
theorem inv_le_rootCriticalIntensity_of_translationInvariant [Countable G]
    (J : Sym2 G → ℝ≥0) (k : G → ℝ≥0) (hJ : ∀ x y, J s(x,y) = k (y - x)) (M : ℝ≥0)
    (hk : ∑' z, (k z : ℝ≥0∞) ≤ M) (x : G) :
    (M : ℝ≥0∞)⁻¹ ≤ rootCriticalIntensity J x :=
  inv_le_rootCriticalIntensity J M (fun v =>
    (rowSum_le_tsum_of_translationInvariant J k hJ v).trans hk) x

/-! ### A two-point kernel -/

omit [AddGroup G] in
/-- A point mass sums to one. -/
theorem tsum_coe_ite_eq_one [DecidableEq G] (b : G) :
    (∑' z, (((if z = b then 1 else 0 : ℝ≥0)) : ℝ≥0∞)) = 1 := by
  rw [show (fun z => (((if z = b then 1 else 0 : ℝ≥0)) : ℝ≥0∞)) =
      fun z => if z = b then 1 else 0 from funext fun z => by split_ifs <;> simp]
  exact tsum_ite_eq b 1

/-- The kernel with unit mass at `a` and at `-a` has total mass two. -/
theorem tsum_twoPointKernel [DecidableEq G] (a : G) :
    (∑' z, ((((if z = a then 1 else 0) + (if z = -a then 1 else 0) : ℝ≥0)) : ℝ≥0∞)) = 2 := by
  simp_rw [ENNReal.coe_add]
  rw [ENNReal.tsum_add, tsum_coe_ite_eq_one a, tsum_coe_ite_eq_one (-a)]
  exact one_add_one_eq_two

/-- The kernel with unit mass at `a` and at `-a` is even. -/
theorem twoPointKernel_neg [DecidableEq G] (a z : G) :
    ((if -z = a then 1 else 0) + (if -z = -a then 1 else 0) : ℝ≥0) =
      (if z = a then 1 else 0) + (if z = -a then 1 else 0) := by
  rw [add_comm]
  congr 1 <;> simp [neg_eq_iff_eq_neg]

end PercLib.Models

/-! ### Non-vacuity on `ℤ^d` -/
section Witnesses

open PercLib.Models

/-- On `ℤ^d`, `d ≥ 1`, the nearest-neighbour kernel along the axis `i` gives a nonzero
translation-invariant intensity. At `β = 1/4` its susceptibility is at most two at every
vertex, and both thresholds are at least `1/2`. -/
example (d : ℕ) (i : Fin d) (x : Fin d → ℤ) :
    ∃ J : Sym2 (Fin d → ℤ) → ℝ≥0, J ≠ 0 ∧
      chi (intensityProfile J (1 / 4)) x ≤
        (1 - ((1 / 4 : ℝ≥0) : ℝ≥0∞) * ((2 : ℝ≥0) : ℝ≥0∞))⁻¹ ∧
      ((2 : ℝ≥0) : ℝ≥0∞)⁻¹ ≤ globalCriticalIntensity J ∧
      ((2 : ℝ≥0) : ℝ≥0∞)⁻¹ ≤ rootCriticalIntensity J x := by
  set a : Fin d → ℤ := Pi.single i 1
  set k : (Fin d → ℤ) → ℝ≥0 := fun z => (if z = a then 1 else 0) + (if z = -a then 1 else 0)
  obtain ⟨J, hJ⟩ := exists_sym2_kernel k (twoPointKernel_neg a)
  have hk : ∑' z, (k z : ℝ≥0∞) ≤ ((2 : ℝ≥0) : ℝ≥0∞) :=
    (tsum_twoPointKernel a).le.trans (by simp)
  refine ⟨J, ?_, chi_intensity_le_of_translationInvariant J k hJ 2 hk (1 / 4) ?_ x,
    inv_le_globalCriticalIntensity_of_translationInvariant J k hJ 2 hk,
    inv_le_rootCriticalIntensity_of_translationInvariant J k hJ 2 hk x⟩
  · intro h
    have h0 := congrFun h s(0, a)
    rw [hJ] at h0
    simp [k] at h0
  · rw [← ENNReal.coe_mul, ENNReal.coe_lt_one_iff]
    norm_num

end Witnesses
