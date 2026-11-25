/-
# Asymptotic assembly for the normalized lattice count

This file turns the finite counting sandwich into an `IsBigO` statement. The
power-difference estimate itself is proved separately in `Cell.Remainder`;
the assembly helper below also exposes it as a premise for modular reuse.
-/
module

public import PercLib.CriticalLRP.LatticeGeometry.Cell.Constants
public import PercLib.CriticalLRP.LatticeGeometry.Cell.Remainder

set_option autoImplicit false

@[expose] public section

namespace PercLib.CriticalLRP.LatticeGeometry

open Filter MeasureTheory

open scoped Asymptotics ENNReal Topology

variable {d : ℕ}

/-- Assemble the normalized lattice count from the explicit sandwich-error
remainder. This helper isolates the last analytic input needed for I.4.6. -/
theorem ncard_integer_centers_sub_pow_isBigO_of_remainder
    {ρ : (Fin d → ℝ) → ℝ}
    (h_add : ∀ x y, ρ (x + y) ≤ ρ x + ρ y) (h_neg : ∀ x, ρ (-x) = ρ x)
    {C : ℝ} (hC : ∀ y : Fin d → ℝ, (∀ j, 0 ≤ y j ∧ y j < 1) → ρ y ≤ C)
    (h_hom : ∀ (c : ℝ) (x : Fin d → ℝ), ρ (c • x) = |c| * ρ x)
    (hunit : volume (rhoBall ρ 1) = 1) (hC0 : 0 ≤ C)
    (hO : (fun r : ℝ => (r + C) ^ d - (r - C) ^ d) =O[atTop]
      (fun r => r ^ (d - 1))) :
    (fun r : ℝ =>
      (Set.ncard {z : Fin d → ℤ | ρ (fun j => (z j : ℝ)) ≤ r} : ℝ) - r ^ d) =O[atTop]
      (fun r => r ^ (d - 1)) := by
  obtain ⟨K, hK⟩ := hO.bound
  apply Asymptotics.IsBigO.of_bound K
  filter_upwards [eventually_gt_atTop C, hK] with r hrC hKr
  have habs := abs_ncard_integer_centers_sub_pow_le (d := d) (ρ := ρ) (C := C) (r := r)
    h_add h_neg hC h_hom hunit hC0 hrC
  have hD : 0 ≤ (r + C) ^ d - (r - C) ^ d := (abs_nonneg _).trans habs
  calc
    ‖(Set.ncard {z : Fin d → ℤ | ρ (fun j => (z j : ℝ)) ≤ r} : ℝ) - r ^ d‖ =
        |(Set.ncard {z : Fin d → ℤ | ρ (fun j => (z j : ℝ)) ≤ r} : ℝ) - r ^ d| :=
      Real.norm_eq_abs _
    _ ≤ (r + C) ^ d - (r - C) ^ d := habs
    _ ≤ ‖(r + C) ^ d - (r - C) ^ d‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg hD]
    _ ≤ K * ‖r ^ (d - 1)‖ := hKr

/-- The normalized lattice count has the `r ^ d ± O(r ^ (d - 1))` expansion.
This version exposes the finite cube bound `C` used by the tiling argument. -/
theorem ncard_integer_centers_sub_pow_isBigO {ρ : (Fin d → ℝ) → ℝ}
    (h_add : ∀ x y, ρ (x + y) ≤ ρ x + ρ y) (h_neg : ∀ x, ρ (-x) = ρ x)
    {C : ℝ} (hC : ∀ y : Fin d → ℝ, (∀ j, 0 ≤ y j ∧ y j < 1) → ρ y ≤ C)
    (h_hom : ∀ (c : ℝ) (x : Fin d → ℝ), ρ (c • x) = |c| * ρ x)
    (hunit : volume (rhoBall ρ 1) = 1) (hC0 : 0 ≤ C) :
    (fun r : ℝ =>
      (Set.ncard {z : Fin d → ℤ | ρ (fun j => (z j : ℝ)) ≤ r} : ℝ) - r ^ d) =O[atTop]
      (fun r => r ^ (d - 1)) :=
  ncard_integer_centers_sub_pow_isBigO_of_remainder h_add h_neg hC h_hom hunit hC0
    (isBigO_add_sub_pow hC0)

/-- **Lemma I.4.6.** For a normalized norm-like function on real coordinate
space, the number of integer points of rho-length at most `r` differs from
`r ^ d` by `O(r ^ (d - 1))`. The unit-volume premise is the source convention,
not an assertion that every norm is already normalized. -/
theorem lemma_I_4_6 {ρ : (Fin d → ℝ) → ℝ}
    (h_add : ∀ x y, ρ (x + y) ≤ ρ x + ρ y) (h_neg : ∀ x, ρ (-x) = ρ x)
    (h_cont : Continuous ρ)
    (h_hom : ∀ (c : ℝ) (x : Fin d → ℝ), ρ (c • x) = |c| * ρ x)
    (hunit : volume (rhoBall ρ 1) = 1) :
    (fun r : ℝ =>
      (Set.ncard {z : Fin d → ℤ | ρ (fun j => (z j : ℝ)) ≤ r} : ℝ) - r ^ d) =O[atTop]
      (fun r => r ^ (d - 1)) := by
  obtain ⟨C, hC⟩ := exists_unitCube_upper_bound ρ h_cont
  have hρ0 : ρ 0 = 0 := by
    have h := h_hom (0 : ℝ) 0
    simpa using h
  have hC0 : 0 ≤ C := by
    have h := hC 0 (fun j => by simp)
    rw [hρ0] at h
    exact h
  exact ncard_integer_centers_sub_pow_isBigO h_add h_neg hC h_hom hunit hC0

/-- The same expansion for the norm carried by real coordinate space, with
the source's unit-volume normalization as its only analytical premise. -/
theorem lemma_I_4_6_norm
    (hunit : volume (rhoBall (fun x : Fin d → ℝ => ‖x‖) 1) = 1) :
    (fun r : ℝ =>
      (Set.ncard {z : Fin d → ℤ | ‖fun j => (z j : ℝ)‖ ≤ r} : ℝ) - r ^ d) =O[atTop]
      (fun r => r ^ (d - 1)) := by
  apply lemma_I_4_6 (ρ := fun x : Fin d → ℝ => ‖x‖) (hunit := hunit)
  · exact fun x y => norm_add_le x y
  · exact norm_neg
  · exact continuous_norm
  · intro c x
    simp only [norm_smul, Real.norm_eq_abs]

/-- The standing normalization `|B_r| ∼ r ^ d` in positive dimension. This is
obtained from `lemma_I_4_6` by dividing its error bound by `r ^ d`. -/
theorem lemma_I_4_6_isEquivalent (hd : 1 ≤ d) {ρ : (Fin d → ℝ) → ℝ}
    (h_add : ∀ x y, ρ (x + y) ≤ ρ x + ρ y) (h_neg : ∀ x, ρ (-x) = ρ x)
    (h_cont : Continuous ρ)
    (h_hom : ∀ (c : ℝ) (x : Fin d → ℝ), ρ (c • x) = |c| * ρ x)
    (hunit : volume (rhoBall ρ 1) = 1) :
    (fun r : ℝ => (Set.ncard {z : Fin d → ℤ | ρ (fun j => (z j : ℝ)) ≤ r} : ℝ)) ~[atTop]
      (fun r => r ^ d) := by
  let N : ℝ → ℝ := fun r =>
    (Set.ncard {z : Fin d → ℤ | ρ (fun j => (z j : ℝ)) ≤ r} : ℝ)
  change N ~[atTop] (fun r => r ^ d)
  have hO : (fun r => N r - r ^ d) =O[atTop] (fun r => r ^ (d - 1)) :=
    lemma_I_4_6 h_add h_neg h_cont h_hom hunit
  obtain ⟨K, hK⟩ := hO.bound
  have hM : Tendsto (fun r : ℝ => max K 1 * (1 / r)) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero (𝕜 := ℝ)).const_mul (max K 1)
    simpa [one_div] using h
  have hrel : Tendsto (fun r : ℝ => (N r - r ^ d) / r ^ d) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hM
    filter_upwards [hK, eventually_ge_atTop (1 : ℝ)] with r hKr hr
    have hrpos : 0 < r := zero_lt_one.trans_le hr
    have hrem : |N r - r ^ d| ≤ max K 1 * r ^ (d - 1) := by
      calc
        |N r - r ^ d| = ‖N r - r ^ d‖ := (Real.norm_eq_abs _).symm
        _ ≤ K * ‖r ^ (d - 1)‖ := hKr
        _ ≤ max K 1 * ‖r ^ (d - 1)‖ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
        _ = max K 1 * r ^ (d - 1) := by
          rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hrpos.le _)]
    have hpd : 0 < r ^ d := pow_pos hrpos d
    have hsplit : r ^ (d - 1) / r ^ d = 1 / r := by
      rw [div_eq_div_iff (by positivity) (ne_of_gt hrpos), ← pow_succ, Nat.sub_add_cancel hd]
      ring
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hpd]
    calc
      |N r - r ^ d| / r ^ d ≤ (max K 1 * r ^ (d - 1)) / r ^ d :=
        div_le_div_of_nonneg_right hrem hpd.le
      _ = max K 1 * (1 / r) := by rw [mul_div_assoc, hsplit]
  refine (Asymptotics.isLittleO_iff_tendsto' ?_).mpr hrel
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with r hr hz
  exact (pow_ne_zero d (by linarith : r ≠ 0) hz).elim

end PercLib.CriticalLRP.LatticeGeometry
