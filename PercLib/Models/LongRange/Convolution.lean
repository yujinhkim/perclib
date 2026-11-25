/-
Copyright (c) 2026 PercLib contributors. Released under Apache 2.0.
New doubling-kernel convolution estimate using the triangle inequality and
nonnegative series. No upstream proof is copied; summability is an explicit
hypothesis, not an assertion about power-law convergence at exponent zero.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Normed.Group.Int
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum

@[expose] public section
noncomputable section
open scoped ENNReal NNReal Classical
namespace PercLib.Models

/-- A doubling kernel has convolution bounded by twice its doubling constant times
its mass. No symmetry of the kernel or of the gauge is needed. -/
theorem tsum_mul_le_of_doubling {G : Type*} [AddCommGroup G] (ρ : G → ℝ≥0)
    (htri : ∀ u v, ρ (u + v) ≤ ρ u + ρ v)
    (k : G → ℝ≥0∞) (hk0 : k 0 = 0) {D M : ℝ≥0∞}
    (hD : ∀ u w, u ≠ 0 → w ≠ 0 → ρ w ≤ 2 * ρ u → k u ≤ D * k w)
    (hM : ∑' z, k z ≤ M) {x y : G} (hxy : x ≠ y) :
    ∑' z, k (z - x) * k (y - z) ≤ 2 * D * M * k (y - x) := by
  have hw : y - x ≠ 0 := sub_ne_zero.mpr hxy.symm
  have hpoint (z : G) : k (z-x) * k (y-z) ≤
      D * k (y-x) * (k (y-z) + k (z-x)) := by
    by_cases hz : z = x
    · subst z; simp [hk0]
    by_cases hz' : y = z
    · subst z; simp [hk0]
    have htriangle : ρ (y-x) ≤ ρ (z-x) + ρ (y-z) := by
      convert htri (z-x) (y-z) using 1
      abel
    by_cases h : ρ (y-x) ≤ 2 * ρ (z-x)
    · calc
        _ ≤ (D * k (y-x)) * k (y-z) := by gcongr; exact hD _ _ (sub_ne_zero.mpr hz) hw h
        _ ≤ _ := by gcongr; exact le_add_right le_rfl
    · have h' : ρ (y-x) ≤ 2 * ρ (y-z) := by
        have h1 : (ρ (y-x) : ℝ) ≤ ρ (z-x) + ρ (y-z) := htriangle
        have h2 : ¬ (ρ (y-x) : ℝ) ≤ 2 * ρ (z-x) := h
        change (ρ (y-x) : ℝ) ≤ 2 * ρ (y-z)
        linarith
      calc
        _ ≤ k (z-x) * (D * k (y-x)) := by gcongr; exact hD _ _ (sub_ne_zero.mpr hz') hw h'
        _ = D * k (y-x) * k (z-x) := by ac_rfl
        _ ≤ _ := by gcongr; exact le_add_left le_rfl
  have hs1 : (∑' z, k (z-x)) = ∑' z, k z := (Equiv.subRight x).tsum_eq k
  have hs2 : (∑' z, k (y-z)) = ∑' z, k z := (Equiv.subLeft y).tsum_eq k
  calc
    _ ≤ ∑' z, D * k (y-x) * (k (y-z) + k (z-x)) := ENNReal.tsum_le_tsum hpoint
    _ = D * k (y-x) * ((∑' z, k z) + ∑' z, k z) := by
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_add, hs1, hs2]
    _ ≤ D * k (y-x) * (M+M) := by gcongr
    _ = _ := by rw [← two_mul]; ac_rfl

/-- Negative powers of a norm obey the uniform doubling bound 2^s. -/
theorem nnnorm_rpow_neg_le_of_le_twice {G : Type*} [NormedAddCommGroup G]
    {s : ℝ} (hs : 0 ≤ s) {u w : G} (hw : w ≠ 0) (h : ‖w‖₊ ≤ 2 * ‖u‖₊) :
    ‖u‖₊ ^ (-s) ≤ (2:ℝ≥0) ^ s * ‖w‖₊ ^ (-s) := by
  have hp : 0 < ‖w‖₊ := nnnorm_pos.mpr hw
  have hb : (2:ℝ≥0)^s * (2 * ‖u‖₊)^(-s) ≤ (2:ℝ≥0)^s * ‖w‖₊^(-s) := by
    gcongr 1
    exact NNReal.rpow_le_rpow_of_nonpos hp h (neg_nonpos.mpr hs)
  rw [NNReal.mul_rpow, ← mul_assoc, ← NNReal.rpow_add (by norm_num),
    add_neg_cancel, NNReal.rpow_zero, one_mul] at hb
  exact hb

/-- The origin-deleted power kernel satisfies doubling, including exponent zero. -/
theorem powerKernel_doubling {G : Type*} [NormedAddCommGroup G]
    {s : ℝ} (hs : 0 ≤ s) {u w : G} (hu : u ≠ 0) (hw : w ≠ 0)
    (h : ‖w‖₊ ≤ 2 * ‖u‖₊) :
    (if u = 0 then 0 else (‖u‖₊ ^ (-s) : ℝ≥0∞)) ≤
      (((2:ℝ≥0)^s : ℝ≥0) : ℝ≥0∞) *
        (if w = 0 then 0 else (‖w‖₊ ^ (-s) : ℝ≥0∞)) := by
  simp only [hu, hw, ↓reduceIte]
  rw [← ENNReal.coe_rpow_of_ne_zero ((nnnorm_pos.mpr hu).ne'),
    ← ENNReal.coe_rpow_of_ne_zero ((nnnorm_pos.mpr hw).ne'), ← ENNReal.coe_mul,
    ENNReal.coe_le_coe]
  exact nnnorm_rpow_neg_le_of_le_twice hs hw h

/-- Power-law convolution on any normed abelian group, under its explicit mass bound. -/
theorem tsum_powerKernel_mul_le {G : Type*} [NormedAddCommGroup G]
    {s : ℝ} (hs : 0 ≤ s) {M : ℝ≥0∞}
    (hM : ∑' z : G, (if z = 0 then 0 else (‖z‖₊ ^ (-s) : ℝ≥0∞)) ≤ M)
    {x y : G} (hxy : x ≠ y) :
    ∑' z, (if z-x = 0 then 0 else (‖z-x‖₊ ^ (-s) : ℝ≥0∞)) *
      (if y-z = 0 then 0 else (‖y-z‖₊ ^ (-s) : ℝ≥0∞)) ≤
      2 * (((2:ℝ≥0)^s : ℝ≥0) : ℝ≥0∞) * M * (‖y-x‖₊ ^ (-s) : ℝ≥0∞) := by
  simpa only [ite_eq_left rfl, ite_eq_right (sub_ne_zero.mpr hxy.symm)] using
    tsum_mul_le_of_doubling (fun z : G => ‖z‖₊) nnnorm_add_le
      (fun z => if z = 0 then 0 else (‖z‖₊ ^ (-s) : ℝ≥0∞)) (by simp)
      (fun _ _ hu hw h => powerKernel_doubling hs hu hw h) hM hxy

/-- On Z^d the norm is the supremum norm, and the doubling constant is 2^(d+α).
Summability is deliberately a hypothesis, so α=0 and d=0 remain sound. -/
theorem tsum_lattice_powerKernel_mul_le (d : ℕ) {α : ℝ} (hα : 0 ≤ α) {M : ℝ≥0∞}
    (hM : ∑' z : Fin d → ℤ,
      (if z = 0 then 0 else (‖z‖₊ ^ (-(d+α)) : ℝ≥0∞)) ≤ M)
    {x y : Fin d → ℤ} (hxy : x ≠ y) :
    ∑' z, (if z-x = 0 then 0 else (‖z-x‖₊ ^ (-(d+α)) : ℝ≥0∞)) *
      (if y-z = 0 then 0 else (‖y-z‖₊ ^ (-(d+α)) : ℝ≥0∞)) ≤
      2 * (((2:ℝ≥0)^(d+α) : ℝ≥0) : ℝ≥0∞) * M * (‖y-x‖₊ ^ (-(d+α)) : ℝ≥0∞) :=
  by
  have hm : (∑' z : Fin d → ℤ,
      (if z = 0 then 0 else (‖z‖₊ ^ (-((d:ℝ)+α)) : ℝ≥0∞))) ≤ M := by
    convert hM using 1
  convert tsum_powerKernel_mul_le (s := (d:ℝ)+α) (M := M) (by positivity) (by
    convert hm using 1
    apply tsum_congr
    intro z
    split_ifs <;> rfl) hxy using 1
  apply tsum_congr
  intro z
  split_ifs <;> rfl

-- A zero kernel works with zero mass, even on an uncountable ambient group.
example {G : Type*} [NormedAddCommGroup G] {x y : G} (_hxy : x ≠ y) :
    ∑' _z : G, (0:ℝ≥0∞) * 0 ≤ 2 * 0 * 0 * 0 := by simp

-- The power-law doubling hypothesis is genuinely realized at d=1, α=1.
example {u w : Fin 1 → ℤ} (hu : u ≠ 0) (hw : w ≠ 0) (h : ‖w‖₊ ≤ 2 * ‖u‖₊) :
    (if u = 0 then 0 else (‖u‖₊ ^ (-2:ℝ) : ℝ≥0∞)) ≤
      (4:ℝ≥0∞) * (if w = 0 then 0 else (‖w‖₊ ^ (-2:ℝ) : ℝ≥0∞)) := by
  convert powerKernel_doubling (s := 2) (by norm_num) hu hw h using 1 <;> norm_num

-- The inverse-square profile on Z has finite mass and the x=0, y=1 bound is finite.
example : ∃ M : ℝ≥0∞, M < ⊤ ∧
    (∑' z : ℤ, (if z = 0 then 0 else (‖z‖₊ ^ (-2:ℝ) : ℝ≥0∞)) *
      (if 1-z = 0 then 0 else (‖1-z‖₊ ^ (-2:ℝ) : ℝ≥0∞))) ≤ 8 * M := by
  have hs : Summable (fun z : ℤ => ‖z‖₊ ^ (-2:ℝ)) := by
    rw [← NNReal.summable_coe]
    simpa only [NNReal.coe_rpow, coe_nnnorm, Int.norm_eq_abs] using
      (Real.summable_abs_int_rpow (b := 2) (by norm_num))
  have he (z : ℤ) : (if z = 0 then 0 else (‖z‖₊ ^ (-2:ℝ) : ℝ≥0∞)) =
      ((‖z‖₊ ^ (-2:ℝ) : ℝ≥0) : ℝ≥0∞) := by
    by_cases hz : z = 0
    · subst z; norm_num
    · simp only [hz, ↓reduceIte,
        ENNReal.coe_rpow_of_ne_zero (nnnorm_pos.mpr hz).ne']
  let M : ℝ≥0∞ := ∑' z : ℤ, (if z = 0 then 0 else (‖z‖₊ ^ (-2:ℝ) : ℝ≥0∞))
  have hM : M < ⊤ := by
    simp only [M, he]
    exact lt_top_iff_ne_top.mpr (ENNReal.tsum_coe_ne_top_iff_summable.mpr hs)
  refine ⟨M,hM,?_⟩
  have hb := tsum_powerKernel_mul_le (s := 2) (by norm_num) (M := M)
    (x := (0:ℤ)) (y := 1) (by
      convert le_refl M using 1
      dsimp [M]
      apply tsum_congr
      intro z
      split_ifs <;> rfl) (by norm_num)
  norm_num at hb ⊢
  exact hb

end PercLib.Models
