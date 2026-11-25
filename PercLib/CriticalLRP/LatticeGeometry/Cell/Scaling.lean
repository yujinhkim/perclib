/-
# Scaling of normalized rho-balls

The unit-volume convention of Definition I.1.3 turns Haar scaling into the
volume identity used in the proof of Lemma I.4.6. No lattice-counting claim is
made in this file.
-/
module

public import PercLib.CriticalLRP.LatticeGeometry.Cell.Packing
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

set_option autoImplicit false

@[expose] public section

namespace PercLib.CriticalLRP.LatticeGeometry

open MeasureTheory

open scoped ENNReal Pointwise

variable {d : ℕ}

/-- A positive radius scales the unit rho-ball by that radius. -/
theorem rhoBall_pos_eq_smul {ρ : (Fin d → ℝ) → ℝ}
    (h_hom : ∀ (c : ℝ) (x : Fin d → ℝ), ρ (c • x) = |c| * ρ x)
    {r : ℝ} (hr : 0 < r) :
    rhoBall ρ r = r • rhoBall ρ 1 := by
  ext x
  constructor
  · intro hx
    refine ⟨r⁻¹ • x, ?_, ?_⟩
    · change ρ (r⁻¹ • x) ≤ 1
      rw [h_hom, abs_inv, abs_of_pos hr]
      have hx' : ρ x ≤ r := hx
      calc
        r⁻¹ * ρ x ≤ r⁻¹ * r := mul_le_mul_of_nonneg_left hx' (inv_nonneg.mpr hr.le)
        _ = 1 := inv_mul_cancel₀ hr.ne'
    · change r • (r⁻¹ • x) = x
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  · rintro ⟨y, hy, rfl⟩
    change ρ (r • y) ≤ r
    rw [h_hom, abs_of_pos hr]
    have hy' : ρ y ≤ 1 := hy
    simpa using mul_le_mul_of_nonneg_left hy' hr.le

/-- Under the paper's unit-volume normalization, the volume of a rho-ball of
positive radius `r` is `r ^ d`. -/
theorem volume_rhoBall {ρ : (Fin d → ℝ) → ℝ}
    (h_hom : ∀ (c : ℝ) (x : Fin d → ℝ), ρ (c • x) = |c| * ρ x)
    (hunit : volume (rhoBall ρ 1) = 1) {r : ℝ} (hr : 0 < r) :
    volume (rhoBall ρ r) = ENNReal.ofReal (r ^ d) := by
  rw [rhoBall_pos_eq_smul h_hom hr, Measure.addHaar_smul_of_nonneg volume hr.le, hunit,
    mul_one]
  simp [Module.finrank_fintype_fun_eq_card]

/-- The normalized counting sandwich as an inequality between real numbers.
The condition `C < r` is used only to apply positive-radius Haar scaling to
both the inner and outer balls. -/
theorem ncard_integer_centers_sandwich_real {ρ : (Fin d → ℝ) → ℝ}
    (h_add : ∀ x y, ρ (x + y) ≤ ρ x + ρ y) (h_neg : ∀ x, ρ (-x) = ρ x)
    {C r : ℝ} (hC : ∀ y : Fin d → ℝ, (∀ j, 0 ≤ y j ∧ y j < 1) → ρ y ≤ C)
    (h_hom : ∀ (c : ℝ) (x : Fin d → ℝ), ρ (c • x) = |c| * ρ x)
    (hunit : volume (rhoBall ρ 1) = 1) (hC0 : 0 ≤ C) (hrC : C < r) :
    (r - C) ^ d ≤ (Set.ncard {z : Fin d → ℤ | ρ (fun j => (z j : ℝ)) ≤ r} : ℝ) ∧
      (Set.ncard {z : Fin d → ℤ | ρ (fun j => (z j : ℝ)) ≤ r} : ℝ) ≤ (r + C) ^ d := by
  have hr : 0 < r := hC0.trans_lt hrC
  have hout : 0 < r + C := add_pos_of_pos_of_nonneg hr hC0
  have hfin : volume {x : Fin d → ℝ | ρ x ≤ r + C} ≠ ∞ := by
    change volume (rhoBall ρ (r + C)) ≠ ∞
    rw [volume_rhoBall h_hom hunit hout]
    exact ENNReal.ofReal_ne_top
  have hs := ncard_integer_centers_sandwich (d := d) (ρ := ρ) (C := C) (r := r)
    h_add h_neg hC hfin
  change volume (rhoBall ρ (r - C)) ≤ _ ∧ _ ≤ volume (rhoBall ρ (r + C)) at hs
  rw [volume_rhoBall h_hom hunit (sub_pos.mpr hrC), volume_rhoBall h_hom hunit hout] at hs
  constructor
  · exact ENNReal.ofReal_le_natCast.mp hs.1
  · have hu := (ENNReal.le_ofReal_iff_toReal_le (ENNReal.natCast_ne_top _)
      (pow_nonneg (add_nonneg hr.le hC0) d)).mp hs.2
    simpa using hu

/-- A normalized rho-ball count differs from `r ^ d` by at most the explicitly
computable width of the inner/outer power sandwich. -/
theorem abs_ncard_integer_centers_sub_pow_le {ρ : (Fin d → ℝ) → ℝ}
    (h_add : ∀ x y, ρ (x + y) ≤ ρ x + ρ y) (h_neg : ∀ x, ρ (-x) = ρ x)
    {C r : ℝ} (hC : ∀ y : Fin d → ℝ, (∀ j, 0 ≤ y j ∧ y j < 1) → ρ y ≤ C)
    (h_hom : ∀ (c : ℝ) (x : Fin d → ℝ), ρ (c • x) = |c| * ρ x)
    (hunit : volume (rhoBall ρ 1) = 1) (hC0 : 0 ≤ C) (hrC : C < r) :
    |(Set.ncard {z : Fin d → ℤ | ρ (fun j => (z j : ℝ)) ≤ r} : ℝ) - r ^ d| ≤
      (r + C) ^ d - (r - C) ^ d := by
  have hr : 0 < r := hC0.trans_lt hrC
  have hs := ncard_integer_centers_sandwich_real (d := d) (ρ := ρ) (C := C) (r := r)
    h_add h_neg hC h_hom hunit hC0 hrC
  have hlo : (r - C) ^ d ≤ r ^ d := by
    apply pow_le_pow_left₀ (sub_nonneg.mpr hrC.le) (by linarith) d
  have hhi : r ^ d ≤ (r + C) ^ d := by
    apply pow_le_pow_left₀ hr.le (by linarith) d
  rw [abs_sub_le_iff]
  constructor <;> linarith [hs.1, hs.2]

end PercLib.CriticalLRP.LatticeGeometry
