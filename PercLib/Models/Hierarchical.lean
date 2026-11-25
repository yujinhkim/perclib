/-
Copyright (c) 2026 PercLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
New proofs for P-7 (issue 41), written on 2026-11-14, from pinned mathlib's finitely
supported functions, `ZMod` cardinality and ENNReal geometric series, and the P-6 and
translation-invariant theorems. No upstream code is copied.
-/
module

public import PercLib.Models.TranslationInvariant
public import Mathlib.Data.Finsupp.Encodable
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # The hierarchical lattice with a radial kernel

The hierarchical lattice of dimension `d` and scale `L` is the countable additive group
`ℕ →₀ (Fin d → ZMod L)` of finitely supported sequences: the finite-support direct sum,
not the full product. The level of a displacement `z` is `z.support.sup Nat.succ`: zero
for `z = 0`, and one more than the largest index of its support otherwise. A kernel is
radial when it depends on the displacement only through its level.

* `tsum_ball_le`: the ball of level `n` (support below `n`) has at most `L^(d n)` points;
  it injects into `Fin n → (Fin d → ZMod L)`.
* `tsum_radial_le`: for every `f`, `∑' z, f (level z) ≤ ∑' n, L^(d n) f n`.
* `tsum_geometricRadial_le`: the infinite-range kernel `C r^(level z)` with
  `2 L^d r ≤ 1` has total mass at most `2 C`. With `r = L^(-(d+α))` this is the radial
  family `C L^(-(d+α) n)` for `L^α ≥ 2`.
* `chi_intensity_le_hierarchical` and the threshold bounds: P-6 for every pair intensity
  with that kernel.

The bound uses the ball count `L^(d n)` for the shell of level `n`, which suffices for
summability; the exact shell count `L^(d n) - L^(d (n-1))` is not needed and not proved
here.
-/

@[expose] public section
noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal
open Classical
open PercLib.Percolation.Bond

namespace PercLib.Models

variable {d L : ℕ} [NeZero L]

/-- The ball of level `n` of the hierarchical lattice has at most `L^(d n)` points. -/
theorem tsum_ball_le (n : ℕ) :
    (∑' z : ℕ →₀ (Fin d → ZMod L), if ∀ b ∈ z.support, b < n then (1 : ℝ≥0∞) else 0) ≤
      (((L ^ d) ^ n : ℕ) : ℝ≥0∞) := by
  have hS := tsum_subtype {z : ℕ →₀ (Fin d → ZMod L) | ∀ b ∈ z.support, b < n}
    (fun _ => (1 : ℝ≥0∞))
  have he : (∑' z : ℕ →₀ (Fin d → ZMod L),
      if ∀ b ∈ z.support, b < n then (1 : ℝ≥0∞) else 0) =
      ∑' z : ℕ →₀ (Fin d → ZMod L),
        {z : ℕ →₀ (Fin d → ZMod L) | ∀ b ∈ z.support, b < n}.indicator
          (fun _ => (1 : ℝ≥0∞)) z := by
    refine tsum_congr fun z => ?_
    rw [Set.indicator_apply]
    by_cases h : ∀ b ∈ z.support, b < n
    · rw [ite_eq_left h,
        ite_eq_left (show z ∈ {z : ℕ →₀ (Fin d → ZMod L) | ∀ b ∈ z.support, b < n} from h)]
    · rw [ite_eq_right h,
        ite_eq_right (show z ∉ {z : ℕ →₀ (Fin d → ZMod L) | ∀ b ∈ z.support, b < n} from h)]
  rw [he, ← hS]
  have hinj : Function.Injective
      (fun (z : {z : ℕ →₀ (Fin d → ZMod L) | ∀ b ∈ z.support, b < n}) (i : Fin n) =>
        z.1 i) := by
    rintro ⟨z, hz⟩ ⟨z', hz'⟩ h
    apply Subtype.ext
    ext a : 1
    by_cases ha : a < n
    · exact congrFun h ⟨a, ha⟩
    · have h1 : z a = 0 := by
        by_contra h0
        exact ha (hz a (Finsupp.mem_support_iff.2 h0))
      have h2 : z' a = 0 := by
        by_contra h0
        exact ha (hz' a (Finsupp.mem_support_iff.2 h0))
      rw [h1, h2]
  calc ∑' _ : {z : ℕ →₀ (Fin d → ZMod L) | ∀ b ∈ z.support, b < n}, (1 : ℝ≥0∞)
      ≤ ∑' _ : Fin n → Fin d → ZMod L, (1 : ℝ≥0∞) :=
        ENNReal.tsum_comp_le_tsum_of_injective hinj (fun _ => 1)
    _ = (((L ^ d) ^ n : ℕ) : ℝ≥0∞) := by
        simp [tsum_fintype, ZMod.card]

/-- A radial sum over the hierarchical lattice is at most the sum over levels weighted by
the size of the ball of that level. -/
theorem tsum_radial_le (f : ℕ → ℝ≥0∞) :
    ∑' z : ℕ →₀ (Fin d → ZMod L), f (z.support.sup Nat.succ) ≤
      ∑' n, (((L ^ d) ^ n : ℕ) : ℝ≥0∞) * f n := by
  calc ∑' z : ℕ →₀ (Fin d → ZMod L), f (z.support.sup Nat.succ)
      = ∑' z : ℕ →₀ (Fin d → ZMod L), ∑' n : ℕ,
          if n = z.support.sup Nat.succ then f n else 0 :=
        tsum_congr fun z => (tsum_ite_eq _ _).symm
    _ = ∑' n : ℕ, ∑' z : ℕ →₀ (Fin d → ZMod L),
          if n = z.support.sup Nat.succ then f n else 0 :=
        ENNReal.tsum_comm
    _ ≤ ∑' n : ℕ, ∑' z : ℕ →₀ (Fin d → ZMod L),
          f n * (if ∀ b ∈ z.support, b < n then (1 : ℝ≥0∞) else 0) := by
        refine ENNReal.tsum_le_tsum fun n => ENNReal.tsum_le_tsum fun z => ?_
        by_cases h1 : n = z.support.sup Nat.succ
        · have h2 : ∀ b ∈ z.support, b < n := fun b hb =>
            h1 ▸ Nat.lt_of_succ_le (Finset.le_sup (f := Nat.succ) hb)
          exact le_of_eq (by rw [ite_eq_left h1, ite_eq_left h2, mul_one])
        · rw [ite_eq_right h1]
          exact zero_le
    _ = ∑' n : ℕ, f n * ∑' z : ℕ →₀ (Fin d → ZMod L),
          (if ∀ b ∈ z.support, b < n then (1 : ℝ≥0∞) else 0) :=
        tsum_congr fun n => ENNReal.tsum_mul_left
    _ ≤ ∑' n : ℕ, f n * (((L ^ d) ^ n : ℕ) : ℝ≥0∞) :=
        ENNReal.tsum_le_tsum fun n => by
          gcongr
          exact tsum_ball_le n
    _ = ∑' n, (((L ^ d) ^ n : ℕ) : ℝ≥0∞) * f n :=
        tsum_congr fun n => mul_comm _ _

/-- The infinite-range radial kernel `C r^(level z)` with `2 L^d r ≤ 1` has total mass at
most `2 C`. -/
theorem tsum_geometricRadial_le (C r : ℝ≥0) (hr : (L : ℝ≥0) ^ d * r * 2 ≤ 1) :
    ∑' z : ℕ →₀ (Fin d → ZMod L), ((C * r ^ (z.support.sup Nat.succ) : ℝ≥0) : ℝ≥0∞) ≤
      ((2 * C : ℝ≥0) : ℝ≥0∞) := by
  have hr' : (L : ℝ≥0∞) ^ d * r ≤ 2⁻¹ := by
    apply ENNReal.le_inv_iff_mul_le.2
    have h := ENNReal.coe_le_coe.2 hr
    push_cast at h
    exact h
  calc ∑' z : ℕ →₀ (Fin d → ZMod L), ((C * r ^ (z.support.sup Nat.succ) : ℝ≥0) : ℝ≥0∞)
      ≤ ∑' n, (((L ^ d) ^ n : ℕ) : ℝ≥0∞) * ((C * r ^ n : ℝ≥0) : ℝ≥0∞) :=
        tsum_radial_le (fun n => ((C * r ^ n : ℝ≥0) : ℝ≥0∞))
    _ = ∑' n, (C : ℝ≥0∞) * ((L : ℝ≥0∞) ^ d * r) ^ n := by
        refine tsum_congr fun n => ?_
        push_cast
        ring
    _ ≤ ∑' n, (C : ℝ≥0∞) * 2⁻¹ ^ n :=
        ENNReal.tsum_le_tsum fun n => by
          gcongr
    _ = ((2 * C : ℝ≥0) : ℝ≥0∞) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
        push_cast
        ring

omit [NeZero L] in
/-- The radial kernel `C r^(level z)` is even, so it is the kernel of a pair intensity. -/
theorem exists_hierarchical_kernel (C r : ℝ≥0) :
    ∃ J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0,
      ∀ x y, J s(x,y) = C * r ^ ((y - x).support.sup Nat.succ) :=
  exists_sym2_kernel (fun z : ℕ →₀ (Fin d → ZMod L) => C * r ^ (z.support.sup Nat.succ))
    fun z => by
    simp only [Finsupp.support_neg]

/-- **P-6 on the hierarchical lattice: susceptibility.** -/
theorem chi_intensity_le_hierarchical (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0)
    (C r : ℝ≥0) (hJ : ∀ x y, J s(x,y) = C * r ^ ((y - x).support.sup Nat.succ))
    (hr : (L : ℝ≥0) ^ d * r * 2 ≤ 1) (β : ℝ≥0)
    (hβ : (β : ℝ≥0∞) * ((2 * C : ℝ≥0) : ℝ≥0∞) < 1) (x : ℕ →₀ (Fin d → ZMod L)) :
    chi (intensityProfile J β) x ≤ (1 - (β : ℝ≥0∞) * ((2 * C : ℝ≥0) : ℝ≥0∞))⁻¹ :=
  chi_intensity_le_of_translationInvariant J (fun z => C * r ^ (z.support.sup Nat.succ)) hJ
    (2 * C) (tsum_geometricRadial_le C r hr) β hβ x

/-- **P-6 on the hierarchical lattice: global threshold.** -/
theorem inv_le_globalCriticalIntensity_hierarchical
    (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0) (C r : ℝ≥0)
    (hJ : ∀ x y, J s(x,y) = C * r ^ ((y - x).support.sup Nat.succ))
    (hr : (L : ℝ≥0) ^ d * r * 2 ≤ 1) :
    (((2 * C : ℝ≥0)) : ℝ≥0∞)⁻¹ ≤ globalCriticalIntensity J :=
  inv_le_globalCriticalIntensity_of_translationInvariant J
    (fun z => C * r ^ (z.support.sup Nat.succ)) hJ (2 * C) (tsum_geometricRadial_le C r hr)

/-- **P-6 on the hierarchical lattice: root threshold.** -/
theorem inv_le_rootCriticalIntensity_hierarchical
    (J : Sym2 (ℕ →₀ (Fin d → ZMod L)) → ℝ≥0) (C r : ℝ≥0)
    (hJ : ∀ x y, J s(x,y) = C * r ^ ((y - x).support.sup Nat.succ))
    (hr : (L : ℝ≥0) ^ d * r * 2 ≤ 1) (x : ℕ →₀ (Fin d → ZMod L)) :
    (((2 * C : ℝ≥0)) : ℝ≥0∞)⁻¹ ≤ rootCriticalIntensity J x :=
  inv_le_rootCriticalIntensity_of_translationInvariant J
    (fun z => C * r ^ (z.support.sup Nat.succ)) hJ (2 * C) (tsum_geometricRadial_le C r hr) x

end PercLib.Models

/-! ### Non-vacuity -/
section Witnesses

open PercLib.Models

/-- `d = 1`, `L = 2`: the radial kernel `4^(-level)`, that is `C L^(-(d+α) n)` with
`C = 1` and `α = 1`. It is positive at every displacement, so its range is infinite. A
pair intensity with this kernel is nonzero; at `β = 1/8` its susceptibility is at most
`(1 - 1/8 · 2)⁻¹`, and both thresholds are at least `1/2`. -/
example (x : ℕ →₀ (Fin 1 → ZMod 2)) :
    ∃ J : Sym2 (ℕ →₀ (Fin 1 → ZMod 2)) → ℝ≥0, J ≠ 0 ∧
      chi (intensityProfile J (1 / 8)) x ≤
        (1 - ((1 / 8 : ℝ≥0) : ℝ≥0∞) * ((2 * 1 : ℝ≥0) : ℝ≥0∞))⁻¹ ∧
      ((2 * 1 : ℝ≥0) : ℝ≥0∞)⁻¹ ≤ globalCriticalIntensity J ∧
      ((2 * 1 : ℝ≥0) : ℝ≥0∞)⁻¹ ≤ rootCriticalIntensity J x := by
  obtain ⟨J, hJ⟩ := exists_hierarchical_kernel (d := 1) (L := 2) 1 (1 / 4)
  have hr : ((2 : ℕ) : ℝ≥0) ^ 1 * (1 / 4) * 2 ≤ 1 := by norm_num
  refine ⟨J, ?_, chi_intensity_le_hierarchical J 1 (1 / 4) hJ hr (1 / 8) ?_ x,
    inv_le_globalCriticalIntensity_hierarchical J 1 (1 / 4) hJ hr,
    inv_le_rootCriticalIntensity_hierarchical J 1 (1 / 4) hJ hr x⟩
  · intro h
    have h0 := congrFun h s(0, Finsupp.single 0 (fun _ => 1))
    rw [hJ] at h0
    simp at h0
  · rw [← ENNReal.coe_mul, ENNReal.coe_lt_one_iff]
    norm_num

end Witnesses
