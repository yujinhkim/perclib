/-
# Rescaling a genuine norm to unit volume

Positive definiteness supplies norm equivalence, hence finite ball volumes.
Continuity supplies a non-empty strict ball, hence positive unit-ball volume.
The Haar scaling identity then produces the normalization assumed by the paper.
-/
module

public import PercLib.CriticalLRP.LatticeGeometry.Cell.Example

set_option autoImplicit false

@[expose] public section

namespace PercLib.CriticalLRP.LatticeGeometry

open Filter MeasureTheory

open scoped ENNReal Pointwise Topology

variable {d : ℕ}

/-- Absolute homogeneity forces `rho 0 = 0`. -/
theorem rho_zero_of_abs_hom {ρ : (Fin d → ℝ) → ℝ}
    (h_hom : ∀ (c : ℝ) (x : Fin d → ℝ), ρ (c • x) = |c| * ρ x) : ρ 0 = 0 := by
  simpa using h_hom 0 (0 : Fin d → ℝ)

/-- Absolute homogeneity at `-1` gives evenness. -/
theorem rho_neg_of_abs_hom {ρ : (Fin d → ℝ) → ℝ}
    (h_hom : ∀ (c : ℝ) (x : Fin d → ℝ), ρ (c • x) = |c| * ρ x) (x : Fin d → ℝ) :
    ρ (-x) = ρ x := by
  simpa using h_hom (-1) x

/-- A subadditive absolutely homogeneous function is nonnegative. -/
theorem rho_nonneg_of_abs_hom {ρ : (Fin d → ℝ) → ℝ}
    (h_add : ∀ x y, ρ (x + y) ≤ ρ x + ρ y)
    (h_hom : ∀ (c : ℝ) (x : Fin d → ℝ), ρ (c • x) = |c| * ρ x) (x : Fin d → ℝ) :
    0 ≤ ρ x := by
  have h := h_add x (-x)
  rw [add_neg_cancel, rho_neg_of_abs_hom h_hom, rho_zero_of_abs_hom h_hom] at h
  linarith

/-- Positive definiteness and continuity give norm equivalence with the
canonical supremum norm. -/
theorem exists_pos_mul_norm_le_of_pos_def {ρ : (Fin d → ℝ) → ℝ}
    (h_add : ∀ x y, ρ (x + y) ≤ ρ x + ρ y) (h_cont : Continuous ρ)
    (h_hom : ∀ (c : ℝ) (x : Fin d → ℝ), ρ (c • x) = |c| * ρ x)
    (h_pos : ∀ x, ρ x = 0 → x = 0) (hd : 0 < d) :
    ∃ m : ℝ, 0 < m ∧ ∀ x : Fin d → ℝ, m * ‖x‖ ≤ ρ x := by
  have hnonneg := rho_nonneg_of_abs_hom (d := d) h_add h_hom
  have hne : (Metric.sphere (0 : Fin d → ℝ) 1).Nonempty := by
    refine ⟨Pi.single ⟨0, hd⟩ (1 : ℝ), ?_⟩
    rw [Metric.mem_sphere, dist_zero_right, Pi.norm_single]
    norm_num
  obtain ⟨x₀, hx₀, hmin⟩ := (isCompact_sphere (0 : Fin d → ℝ) 1).exists_isMinOn hne
    h_cont.continuousOn
  have hx₀ne : x₀ ≠ 0 := by
    intro h
    rw [h] at hx₀
    simp at hx₀
  have hmpos : 0 < ρ x₀ :=
    lt_of_le_of_ne (hnonneg x₀) (fun h => hx₀ne (h_pos x₀ h.symm))
  refine ⟨ρ x₀, hmpos, fun x => ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp [rho_zero_of_abs_hom h_hom]
  · have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hu : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : Fin d → ℝ) 1 := by
      rw [Metric.mem_sphere, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs,
        abs_of_pos hxn]
      field_simp
    have hle := hmin hu
    have hscaled : ρ (‖x‖ • (‖x‖⁻¹ • x)) = ‖x‖ * ρ (‖x‖⁻¹ • x) := by
      rw [h_hom, abs_of_pos hxn]
    rw [smul_smul, mul_inv_cancel₀ hxn.ne', one_smul] at hscaled
    rw [hscaled, mul_comm (ρ x₀) ‖x‖]
    exact mul_le_mul_of_nonneg_left hle hxn.le

/-- Every rho-ball of a positive-definite norm-like function has finite
Lebesgue volume. -/
theorem volume_rhoBall_ne_top_of_pos_def {ρ : (Fin d → ℝ) → ℝ}
    (h_add : ∀ x y, ρ (x + y) ≤ ρ x + ρ y) (h_cont : Continuous ρ)
    (h_hom : ∀ (c : ℝ) (x : Fin d → ℝ), ρ (c • x) = |c| * ρ x)
    (h_pos : ∀ x, ρ x = 0 → x = 0) (hd : 0 < d) (R : ℝ) :
    volume (rhoBall ρ R) ≠ ∞ := by
  obtain ⟨m, hmpos, hmle⟩ := exists_pos_mul_norm_le_of_pos_def h_add h_cont h_hom h_pos hd
  have hsub : rhoBall ρ R ⊆ Metric.closedBall 0 (max 0 (R / m)) := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 : m * ‖x‖ ≤ R := le_trans (hmle x) hx
    have h2 : ‖x‖ ≤ R / m := by
      rw [le_div_iff₀ hmpos]
      linarith
    exact h2.trans (le_max_right _ _)
  have hfin : volume (Metric.closedBall (0 : Fin d → ℝ) (max 0 (R / m))) ≠ ∞ := by
    rw [Real.volume_pi_closedBall _ (le_max_left 0 _)]
    exact ENNReal.ofReal_ne_top
  exact ne_top_of_le_ne_top hfin (measure_mono hsub)

/-- The unit ball of a genuine norm has strictly positive Lebesgue measure. -/
theorem volume_rhoBall_one_pos_of_pos_def {ρ : (Fin d → ℝ) → ℝ}
    (h_add : ∀ x y, ρ (x + y) ≤ ρ x + ρ y) (h_cont : Continuous ρ)
    (h_hom : ∀ (c : ℝ) (x : Fin d → ℝ), ρ (c • x) = |c| * ρ x)
    (h_pos : ∀ x, ρ x = 0 → x = 0) (hd : 0 < d) :
    0 < volume (rhoBall ρ 1) := by
  let x : Fin d → ℝ := Pi.single ⟨0, hd⟩ (1 : ℝ)
  have hx : x ≠ 0 := by
    intro h
    have hc := congrFun h ⟨0, hd⟩
    simp [x] at hc
  have hxρ : 0 < ρ x :=
    lt_of_le_of_ne (rho_nonneg_of_abs_hom h_add h_hom x) (fun h => hx (h_pos x h.symm))
  have hw : (2 * ρ x)⁻¹ • x ∈ {y : Fin d → ℝ | ρ y < 1} := by
    change ρ ((2 * ρ x)⁻¹ • x) < 1
    rw [h_hom, abs_of_pos (by positivity : 0 < (2 * ρ x)⁻¹)]
    have heq : (2 * ρ x)⁻¹ * ρ x = 1 / 2 := by field_simp [hxρ.ne']
    rw [heq]
    norm_num
  have hopen : IsOpen {y : Fin d → ℝ | ρ y < 1} := isOpen_lt h_cont continuous_const
  have hpos : 0 < volume {y : Fin d → ℝ | ρ y < 1} := hopen.measure_pos volume ⟨_, hw⟩
  have hsub : {y : Fin d → ℝ | ρ y < 1} ⊆ rhoBall ρ 1 := by
    intro y hy
    change ρ y < 1 at hy
    exact hy.le
  exact lt_of_lt_of_le hpos (measure_mono hsub)

/-- For `V > 0` and positive dimension there is a positive `b` with
`b ^ d = 1 / V`. -/
theorem exists_pos_pow_eq_inv {V : ℝ} (hV : 0 < V) {d : ℕ} (hd : 0 < d) :
    ∃ b : ℝ, 0 < b ∧ b ^ d = 1 / V := by
  refine ⟨(1 / V) ^ ((d : ℝ)⁻¹), Real.rpow_pos_of_pos (by positivity) _, ?_⟩
  rw [← Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ 1 / V) ((d : ℝ)⁻¹) d,
    inv_mul_cancel₀ (by exact_mod_cast hd.ne'), Real.rpow_one]

/-- A positive finite unit-ball volume can be rescaled to one. -/
theorem exists_normalized_smul {ρ : (Fin d → ℝ) → ℝ}
    (h_hom : ∀ (c : ℝ) (x : Fin d → ℝ), ρ (c • x) = |c| * ρ x)
    (hd : 0 < d) (hV : 0 < (volume (rhoBall ρ 1)).toReal) :
    ∃ a : ℝ, 0 < a ∧ volume {x : Fin d → ℝ | a * ρ x ≤ 1} = 1 := by
  have hfin : volume (rhoBall ρ 1) ≠ ∞ := by
    intro h
    rw [h, ENNReal.toReal_top] at hV
    exact lt_irrefl 0 hV
  have h0 : volume (rhoBall ρ 1) ≠ 0 := by
    intro h
    rw [h, ENNReal.toReal_zero] at hV
    exact lt_irrefl 0 hV
  obtain ⟨b, hb0, hbd⟩ := exists_pos_pow_eq_inv hV hd
  refine ⟨b⁻¹, inv_pos.mpr hb0, ?_⟩
  have hset : {x : Fin d → ℝ | b⁻¹ * ρ x ≤ 1} = rhoBall ρ b := by
    ext x
    change b⁻¹ * ρ x ≤ 1 ↔ ρ x ≤ b
    constructor
    · intro h
      have h' := mul_le_mul_of_nonneg_left h hb0.le
      rwa [← mul_assoc, mul_inv_cancel₀ hb0.ne', one_mul, mul_one] at h'
    · intro h
      have h' := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hb0.le)
      rwa [inv_mul_cancel₀ hb0.ne'] at h'
  rw [hset, rhoBall_pos_eq_smul h_hom hb0, Measure.addHaar_smul_of_nonneg volume hb0.le]
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, hbd, one_div,
    ENNReal.ofReal_inv_of_pos hV, ENNReal.ofReal_toReal hfin]
  exact ENNReal.inv_mul_cancel h0 hfin

/-- **The paper's normalization is achieved by rescaling.** A genuine norm on
real coordinate space has a positive multiple whose unit ball has volume one. -/
theorem exists_normalized_unitBall {ρ : (Fin d → ℝ) → ℝ}
    (h_add : ∀ x y, ρ (x + y) ≤ ρ x + ρ y) (h_cont : Continuous ρ)
    (h_hom : ∀ (c : ℝ) (x : Fin d → ℝ), ρ (c • x) = |c| * ρ x)
    (h_pos : ∀ x, ρ x = 0 → x = 0) (hd : 0 < d) :
    ∃ a : ℝ, 0 < a ∧ volume (rhoBall (fun x => a * ρ x) 1) = 1 := by
  have hfin := volume_rhoBall_ne_top_of_pos_def (ρ := ρ) h_add h_cont h_hom h_pos hd 1
  have hpos : 0 < (volume (rhoBall ρ 1)).toReal :=
    ENNReal.toReal_pos (ne_of_gt (volume_rhoBall_one_pos_of_pos_def h_add h_cont h_hom h_pos hd))
      hfin
  simpa only [rhoBall] using exists_normalized_smul (ρ := ρ) h_hom hd hpos

/-- **Arbitrary-norm form of Lemma I.4.6.** For every positive-definite normlike
function, some positive scalar multiple satisfies the source normalization and
has the expected lattice-count remainder. -/
theorem lemma_I_4_6_after_normalization {ρ : (Fin d → ℝ) → ℝ}
    (h_add : ∀ x y, ρ (x + y) ≤ ρ x + ρ y) (h_cont : Continuous ρ)
    (h_hom : ∀ (c : ℝ) (x : Fin d → ℝ), ρ (c • x) = |c| * ρ x)
    (h_pos : ∀ x, ρ x = 0 → x = 0) (hd : 0 < d) :
    ∃ a : ℝ, 0 < a ∧ volume (rhoBall (fun x => a * ρ x) 1) = 1 ∧
      (fun r : ℝ =>
        (Set.ncard {z : Fin d → ℤ | a * ρ (fun j => (z j : ℝ)) ≤ r} : ℝ) - r ^ d) =O[atTop]
        (fun r => r ^ (d - 1)) := by
  obtain ⟨a, ha, hunit⟩ := exists_normalized_unitBall h_add h_cont h_hom h_pos hd
  refine ⟨a, ha, hunit, ?_⟩
  apply lemma_I_4_6 (ρ := fun x : Fin d → ℝ => a * ρ x)
  · intro x y
    calc
      a * ρ (x + y) ≤ a * (ρ x + ρ y) := mul_le_mul_of_nonneg_left (h_add x y) ha.le
      _ = a * ρ x + a * ρ y := by rw [mul_add]
  · intro x
    exact congrArg (fun t : ℝ => a * t) (rho_neg_of_abs_hom h_hom x)
  · exact continuous_const.mul h_cont
  · intro c x
    rw [h_hom]
    ring
  · exact hunit

end PercLib.CriticalLRP.LatticeGeometry
